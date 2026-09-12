"""Oversight judge and post-FEV acceptance checks.

FEV only proves behavior is unchanged, not that the refactoring GOAL was
achieved (e.g. an if left untouched inside \\SV_plus still passes FEV). A
SEPARATE LLM call answers only pass/fail on intent; it has no incentive to
declare success on the worker's behalf. FAIL routes the reason back through
the same retry path as a FEV failure, then judges again. MM_JUDGE=0
disables; MM_CHECKS adds per-task criteria files.
"""

import glob as _glob
import json
import os
import re

from . import config
from .accounting import track
from .config import ACCEPT_DISTINCT, ACCEPT_GLOB, MODEL_NAME
from .providers import call_with_retry

JUDGE_SYSTEM = (
    "You are a strict, skeptical hardware-refactoring reviewer. Formal equivalence "
    "checking has ALREADY proven the code's behavior is unchanged; that is not your "
    "question. Your only question is whether the stated refactoring goal was actually "
    "achieved in the resulting code. Refactoring agents sometimes dodge: leaving "
    "constructs untouched inside \\SV_plus blocks, renaming without restructuring, or "
    "declaring work done that was not performed. If the goal was to eliminate or convert "
    "a construct and it survives anywhere, including inside \\SV_plus, the verdict is "
    "FAIL, with one exception: the agent may supply a technical justification for "
    "residual incompleteness, and you may PASS if and only if that justification is "
    "specific to the exact surviving constructs and technically sound (a real tool "
    "limitation or a construct with no equivalent), not a vague effort claim. "
    "Reply with exactly:\nVERDICT: PASS\nor\nVERDICT: FAIL\nREASON: <short paragraph "
    "pointing at the specific lines or constructs showing the goal was not met>"
)


# The verdict goes into its OWN file in the checkpoint fev.sh just
# recorded: status.json belongs to the agent/harness, judge.json is written
# only by the router, and the Console renders it like any checkpoint file.
# The judge runs AFTER recording, so it writes into the newest history dir.
def write_judge_record(tname, passed, reason, cost_usd):
    hist = os.path.join(config.MDIR, "history")
    try:
        nums = sorted([d for d in os.listdir(hist) if d.isdigit()], key=int)
    except OSError:
        return
    if not nums:
        return
    with open(os.path.join(hist, nums[-1], "judge.json"), "w") as f:
        json.dump({"verdict": "PASS" if passed else "FAIL", "reason": reason,
                   "cost_usd": round(cost_usd, 4), "model": MODEL_NAME["claude"],
                   "task": tname}, f, indent=1)


def judge(tname, task, before, after, justification=None, nochange=False):
    check_path = os.path.join(os.environ.get("MM_CHECKS", os.path.join(config.ROUTER_DIR, "checks")),
                              re.sub(r"[^A-Za-z0-9]+", "_", tname) + ".txt")
    u = "# Refactoring task that was performed\n\n" + task + "\n"
    if os.path.exists(check_path):
        u += "\n# Specific acceptance criteria for this task\n\n" + open(check_path).read() + "\n"
    if nochange:
        u += "\n===FILE: wip.tlv (proposed UNCHANGED)===\n" + before + "\n===END===\n"
        u += ("\nThe worker agents concluded this task requires NO change to this code, and a "
              "second model cross-checked and agreed. There is deliberately no diff to review; "
              "do not fail merely because the files are identical. Judge whether no-change is "
              "the CORRECT outcome: PASS if the task's goal is already satisfied in this code "
              "or genuinely does not apply to it; FAIL if the task still requires work here.\n")
    else:
        u += "\n===FILE: wip.tlv BEFORE the task===\n" + before + "\n===END===\n"
        u += "\n===FILE: wip.tlv AFTER the task===\n" + after + "\n===END===\n"
    if justification:
        u += ("\n# The refactoring agent's justification for any remaining incompleteness\n\n"
              + justification + "\n\nAccept this only if it is specific and technically sound "
              "for the exact constructs left unconverted; reject vague effort claims.\n")
    u += "\nWas the refactoring goal achieved?"
    resp, ju = call_with_retry("claude", (u, ""), system=JUDGE_SYSTEM)
    jc = track("claude", ju)
    passed = bool(re.search(r"VERDICT:\s*PASS", resp))
    m = re.search(r"REASON:\s*(.+)", resp, re.S)
    reason = m.group(1).strip()[:2000] if m else resp.strip()[:2000]
    return passed, reason, jc


def accept_count():
    return len(_glob.glob(os.path.join(config.MDIR, ACCEPT_GLOB))) if ACCEPT_GLOB else 0


def acceptance_ok(baseline):
    return (not ACCEPT_GLOB) or accept_count() > baseline


def distinct_ok():
    if not ACCEPT_DISTINCT:
        return True
    svs = sorted(_glob.glob(os.path.join(config.MDIR, "wip_*.sv")))
    if len(svs) < 2:
        return True
    bodies = [open(p).read() for p in svs]
    return any(b != bodies[0] for b in bodies[1:])
