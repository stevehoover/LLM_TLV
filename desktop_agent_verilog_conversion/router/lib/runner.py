"""The task loop: one task at a time, cheap provider first with escalation,
fev.sh as the only gate, judge and acceptance checks after every pass."""

import os
import re
import time

from . import accounting, config, edits, state
from .accounting import cache_str, print_summary, track
from .config import ACCEPT_GLOB, EDIT_FORMAT, JUDGE_ON, MODEL_NAME, PROVIDERS
from .edits import apply_files, extract_justification, is_no_change, restore
from .fev import enrich_feedback, run_fev, run_in_module
from .judge import accept_count, acceptance_ok, distinct_ok, judge, write_judge_record
from .prompts import build_user
from .providers import call_with_retry, run_agent_worker
from .workspace import (log_attempt_exchange, log_unparsed, revert,
                        set_status_fields, snap, snapshot_module)

# Tasks that are deterministic scripts run directly, costing no API call.
SCRIPT_TASKS = {"No Tabs": "./scripts/no_tabs.py 2>&1"}


def main():
    ORDER = config.load_order()
    done_tasks, inflight = state.load(config.MDIR)

    for tname, tfile in ORDER:
        if tname in done_tasks:
            print(f"##### TASK: {tname} (previously completed: {done_tasks[tname]}, skip)")
            accounting.stats.append((tname, done_tasks[tname] + " (prior)"))
            continue
        task = open(tfile).read()
        hint_path = os.path.join(os.environ.get("MM_HINTS", os.path.join(config.ROUTER_DIR, "hints")),
                                 re.sub(r"[^A-Za-z0-9]+", "_", tname) + ".txt")
        hinted = os.path.exists(hint_path)
        if hinted:
            task += "\n\n# Guidance from the user (after prior failed attempts)\n\n" + open(hint_path).read()
        print(f"\n##### TASK: {tname} [{time.strftime('%H:%M:%S')}]" + (" (with user guidance)" if hinted else ""))
        set_status_fields(task=tname)
        done = False
        used = None
        feedback = None
        burned = inflight.get("used", {}) if inflight.get("task") == tname else {}
        if burned:
            print(f"  (resuming mid-task: already burned {burned}, continuing with the next provider)")
        inflight = {"task": tname, "used": dict(burned)}
        state.save(done_tasks, inflight)
        accept_base = accept_count()
        task_before = snap("wip.tlv")
        sr_apply_fails = 0
        if tname in SCRIPT_TASKS:
            set_status_fields(model="script")
            sout = run_in_module(SCRIPT_TASKS[tname])
            ok, out = run_fev()
            print(f"  [script] {SCRIPT_TASKS[tname]} fev={'PASS' if ok else 'FAIL'}")
            if ok:
                done_tasks[tname] = "script"
                inflight = {}
                state.save(done_tasks, inflight)
                accounting.stats.append((tname, "script"))
                continue
            print("  [script] failed, handing to LLM with feedback")
            feedback = sout + "\n" + out
            revert()
        for pidx, (provider, tries) in enumerate(PROVIDERS):
            start = burned.get(provider, 0) + 1
            for a in range(start, tries + 1):
                inflight["used"][provider] = a
                state.save(done_tasks, inflight)
                if provider == "agent":
                    print(f"  [agent #{a}] running Claude Code worker ...", flush=True)
                    before_snap = snapshot_module()
                    report, wall = run_agent_worker(task, feedback)
                    after_snap = snapshot_module()
                    touched_harness = [f for f in config.HARNESS_FILES
                                       if before_snap.get(f) != after_snap.get(f)]
                    if touched_harness:
                        restore({f: before_snap.get(f) for f in touched_harness})
                        print(f"  [agent #{a}] RESTORED harness files it touched: {touched_harness}")
                    changed = sorted(f for f in set(before_snap) | set(after_snap)
                                     if f not in config.HARNESS_FILES and f != "attempts.jsonl"
                                     and before_snap.get(f) != after_snap.get(f))
                    originals = {f: before_snap.get(f) for f in changed}
                    log_attempt_exchange(tname, "agent", a, feedback, report, 0.0)
                    accounting.agent_wall[0] += wall
                    if not changed:
                        nc_just = extract_justification(report)
                        print(f"  [agent #{a}] no design files changed (wall {wall:.0f}s) -> judged as NO_CHANGE")
                        if ACCEPT_GLOB and accept_count() <= accept_base:
                            feedback = (f"NO_CHANGE is not acceptable for this task: it explicitly requires "
                                        f"creating new files matching '{ACCEPT_GLOB}', and none exist yet. "
                                        f"Create the required files.")
                            continue
                        if JUDGE_ON:
                            jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                    justification=nc_just, nochange=True)
                            print(f"  [judge:no-change] {'PASS' if jp else 'FAIL'} (${jc:.4f})"
                                  + ("" if jp else f": {jreason[:150]}"))
                            if not jp:
                                feedback = ("You made no edits, but a separate reviewing agent judged that "
                                            "this task DOES require work on this code. Its reason:\n\n"
                                            + jreason + "\n\nDo the required work by editing the files.")
                                continue
                        done = True; used = "agent (no-change)"; break
                    files = changed
                    set_status_fields(model=MODEL_NAME["agent"],
                                      cache={"in": 0, "out": 0, "cache_read": 0, "cache_write": 0})
                    ok, out = run_fev()
                    print(f"  [agent #{a}] files={files} fev={'PASS' if ok else 'FAIL'} (wall {wall:.0f}s)")
                    if ok:
                        if acceptance_ok(accept_base) and distinct_ok():
                            if JUDGE_ON:
                                if "wip.tlv" in files:
                                    jp, jreason, jc = judge(tname, task, task_before, snap("wip.tlv"),
                                                            justification=extract_justification(report))
                                else:
                                    # Design credit without touching wip.tlv (audit Aug 25 dodge
                                    # gap): judge whether leaving the design unchanged is the
                                    # correct outcome for this task.
                                    jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                            justification=extract_justification(report), nochange=True)
                                write_judge_record(tname, jp, jreason, jc)
                                print(f"  [judge] {'PASS' if jp else 'FAIL'} (${jc:.4f})" + ("" if jp else f": {jreason[:150]}"))
                                if not jp:
                                    feedback = ("FEV passed (behavior is preserved), but a separate reviewing agent "
                                                "judged the task goal NOT achieved. Its reason:\n\n" + jreason +
                                                "\n\nComplete the remaining refactoring from the current state of the files.")
                                    continue
                            done = True; used = "agent"; break
                        if not acceptance_ok(accept_base):
                            print(f"  [agent #{a}] fev PASS but required outputs missing ({ACCEPT_GLOB}), rejected")
                            feedback = (f"FEV passed, but the task's required outputs are missing: no new files "
                                        f"matching '{ACCEPT_GLOB}' were created. The task explicitly requires "
                                        f"creating one per parameter set. Create them now.")
                        else:
                            print(f"  [agent #{a}] fev PASS but all per-config designs are IDENTICAL, rejected")
                            feedback = ("FEV passed, but all generated per-configuration designs (wip_*.sv) are "
                                        "byte-identical, so the alternate configuration does not actually change "
                                        "elaboration and the check is vacuous. Likely cause: a hardcoded m5 "
                                        "var(...) in wip.tlv overrides the per-config m5 definition. Restructure "
                                        "so the configuration genuinely affects the design, then re-verify.")
                        continue
                    feedback = enrich_feedback(out)
                    restore(originals)
                    revert()
                    continue
                print(f"  [{provider} #{a}] calling API ...", flush=True)
                resp, u = call_with_retry(provider, build_user(task, feedback))
                c = track(provider, u)
                print(f"    ({cache_str(u)})")
                log_attempt_exchange(tname, provider, a, feedback, resp, c)
                if is_no_change(resp):
                    nc_just = extract_justification(resp)
                    if nc_just:
                        feedback = ((feedback + "\n\n") if feedback else "") + \
                            "The previous model replied NO_CHANGE with this justification:\n" + nc_just
                    if ACCEPT_GLOB and accept_count() <= accept_base:
                        print(f"  [{provider} #{a}] NO_CHANGE REJECTED (missing required output {ACCEPT_GLOB})")
                        feedback = (f"NO_CHANGE is not acceptable for this task: it explicitly requires "
                                    f"creating new files matching '{ACCEPT_GLOB}', and none exist yet. "
                                    f"Create the required files.")
                        continue
                    if pidx + 1 < len(PROVIDERS):
                        checker = PROVIDERS[pidx + 1][0]
                        print(f"  [{provider} #{a}] NO_CHANGE (${c:.4f}) -> cross-check by {checker}")
                        vresp, vu = call_with_retry(checker, build_user(task, feedback))
                        vc = track(checker, vu)
                        if is_no_change(vresp):
                            print(f"  [{checker} verify] agrees NO_CHANGE (${vc:.4f})")
                            # Every NO_CHANGE outcome goes through the judge:
                            # workers never referee their own intent.
                            if JUDGE_ON:
                                jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                        justification=nc_just, nochange=True)
                                print(f"  [judge:no-change] {'PASS' if jp else 'FAIL'} (${jc:.4f})"
                                      + ("" if jp else f": {jreason[:150]}"))
                                if not jp:
                                    feedback = ("Both models proposed NO_CHANGE, but a separate reviewing "
                                                "agent judged that this task DOES require work on this code. "
                                                "Its reason:\n\n" + jreason + "\n\nDo the required work.")
                                    continue
                            done = True; used = f"{provider}+{checker} (no-change agreed)"; break
                        vfiles, vorig = apply_files(vresp)
                        if vfiles and not any(config.DESIGN_FILES_RE.match(f) for f in vfiles):
                            # "Disagreed" but touched no design file: an empty
                            # overrule, treated as agreeing NO_CHANGE.
                            restore(vorig)
                            print(f"  [{checker} verify] only touched non-design files {vfiles}, treated as agreeing NO_CHANGE (${vc:.4f})")
                            if JUDGE_ON:
                                jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                        justification=nc_just, nochange=True)
                                print(f"  [judge:no-change] {'PASS' if jp else 'FAIL'} (${jc:.4f})"
                                      + ("" if jp else f": {jreason[:150]}"))
                                if not jp:
                                    feedback = ("Both models proposed NO_CHANGE, but a separate reviewing "
                                                "agent judged that this task DOES require work on this code. "
                                                "Its reason:\n\n" + jreason + "\n\nDo the required work.")
                                    continue
                            done = True; used = f"{provider}+{checker} (no-change agreed)"; break
                        if vfiles:
                            set_status_fields(model=MODEL_NAME[checker], cache=vu)
                            ok, out = run_fev()
                            print(f"  [{checker} verify] DISAGREES, files={vfiles} fev={'PASS' if ok else 'FAIL'} (${vc:.4f})")
                            if ok:
                                if JUDGE_ON:
                                    if "wip.tlv" in vfiles:
                                        jp, jreason, jc = judge(tname, task, task_before, snap("wip.tlv"),
                                                                justification=extract_justification(vresp))
                                    else:
                                        # Design credit without touching wip.tlv (audit Aug 25 dodge
                                        # gap): judge whether leaving the design unchanged is the
                                        # correct outcome for this task.
                                        jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                                justification=extract_justification(vresp), nochange=True)
                                    write_judge_record(tname, jp, jreason, jc)
                                    print(f"  [judge] {'PASS' if jp else 'FAIL'} (${jc:.4f})" + ("" if jp else f": {jreason[:150]}"))
                                    if not jp:
                                        feedback = ("FEV passed, but a separate reviewing agent judged the task goal "
                                                    "NOT achieved. Its reason:\n\n" + jreason +
                                                    "\n\nComplete the remaining refactoring from the current state of the files.")
                                        continue
                                done = True; used = f"{checker} (overruled no-change)"; break
                            feedback = enrich_feedback(out)
                            restore(vorig)
                            revert()
                            continue
                        log_unparsed(tname, f"{checker} verify", vresp)
                        print(f"  [{checker} verify] reply not parseable (logged), provisionally accepting NO_CHANGE")
                        if JUDGE_ON:
                            jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                    justification=nc_just, nochange=True)
                            print(f"  [judge:no-change] {'PASS' if jp else 'FAIL'} (${jc:.4f})"
                                  + ("" if jp else f": {jreason[:150]}"))
                            if not jp:
                                feedback = ("A NO_CHANGE claim was judged incorrect by the reviewing agent. "
                                            "Its reason:\n\n" + jreason + "\n\nDo the required work.")
                                continue
                        done = True; used = provider + " (no-change unverified)"; break
                    else:
                        print(f"  [{provider} #{a}] NO_CHANGE (${c:.4f})")
                        if JUDGE_ON:
                            jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                    justification=nc_just, nochange=True)
                            print(f"  [judge:no-change] {'PASS' if jp else 'FAIL'} (${jc:.4f})"
                                  + ("" if jp else f": {jreason[:150]}"))
                            if not jp:
                                feedback = ("A NO_CHANGE claim was judged incorrect by the reviewing agent. "
                                            "Its reason:\n\n" + jreason + "\n\nDo the required work.")
                                continue
                        done = True; used = provider + " (no-change)"; break
                files, originals = apply_files(resp)
                if not files:
                    log_unparsed(tname, f"{provider} #{a}", resp)
                    print(f"  [{provider} #{a}] reply not parseable (logged), retry")
                    feedback = edits.APPLY_ERROR or "Your reply did not follow the ===FILE:===/===END=== format."
                    # Hard fallback for search/replace (agreed with Steve, Aug 18): the
                    # dots path fails soft to a full-file request, sr previously kept
                    # retrying blocks forever. After two failed applies, blocks are
                    # banned for the rest of the task.
                    if EDIT_FORMAT == "sr" and "earch/replace" in feedback:
                        sr_apply_fails += 1
                        if sr_apply_fails >= 2:
                            feedback += ("\n\nSearch/replace blocks have now failed to apply "
                                         f"{sr_apply_fails} times on this task. Do NOT send any more "
                                         "search/replace blocks: reply with the COMPLETE updated file "
                                         "contents inside the ===FILE:===/===END=== block.")
                    continue
                sr_apply_fails = 0
                set_status_fields(model=MODEL_NAME[provider], cache=u)
                ok, out = run_fev()
                print(f"  [{provider} #{a}] files={files} fev={'PASS' if ok else 'FAIL'} (${c:.4f})")
                if ok:
                    if acceptance_ok(accept_base) and distinct_ok():
                        if JUDGE_ON:
                            if "wip.tlv" in files:
                                jp, jreason, jc = judge(tname, task, task_before, snap("wip.tlv"),
                                                        justification=extract_justification(resp))
                            else:
                                # Design credit without touching wip.tlv (audit Aug 25 dodge
                                # gap): judge whether leaving the design unchanged is the
                                # correct outcome for this task.
                                jp, jreason, jc = judge(tname, task, task_before, task_before,
                                                        justification=extract_justification(resp), nochange=True)
                            write_judge_record(tname, jp, jreason, jc)
                            print(f"  [judge] {'PASS' if jp else 'FAIL'} (${jc:.4f})" + ("" if jp else f": {jreason[:150]}"))
                            if not jp:
                                feedback = ("FEV passed (behavior is preserved), but a separate reviewing agent "
                                            "judged the task goal NOT achieved. Its reason:\n\n" + jreason +
                                            "\n\nComplete the remaining refactoring from the current state of the files.")
                                continue
                        done = True; used = provider; break
                    if not acceptance_ok(accept_base):
                        print(f"  [{provider} #{a}] fev PASS but required outputs missing ({ACCEPT_GLOB}), rejected")
                        feedback = (f"FEV passed, but the task's required outputs are missing: no new files "
                                    f"matching '{ACCEPT_GLOB}' were created. The task explicitly requires "
                                    f"creating one per parameter set. Create them now.")
                    else:
                        print(f"  [{provider} #{a}] fev PASS but all per-config designs are IDENTICAL, rejected")
                        feedback = ("FEV passed, but all generated per-configuration designs (wip_*.sv) are "
                                    "byte-identical, so the alternate configuration does not actually change "
                                    "elaboration and the check is vacuous. Likely cause: a hardcoded m5 "
                                    "var(...) in wip.tlv overrides the per-config m5 definition. Restructure "
                                    "so the configuration genuinely affects the design, then re-verify.")
                    continue
                feedback = enrich_feedback(out)
                restore(originals)
                revert()
            if done:
                break
        accounting.stats.append((tname, used if done else "FAILED"))
        if done:
            done_tasks[tname] = used
            inflight = {}
            state.save(done_tasks, inflight)
        if not done:
            print(f"  !!! TASK FAILED, attempt budget exhausted, stopping here")
            inflight = {}
            state.save(done_tasks, inflight)
            break

    print_summary()
