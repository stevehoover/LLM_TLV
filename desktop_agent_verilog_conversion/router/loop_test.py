#!/usr/bin/env python3
"""Self-contained tests for the judge context and the retry loop, driven
with fake providers so nothing leaves the machine. Each case sets up a
throwaway module dir, monkeypatches the provider call, and inspects the
prompt or the attempts.jsonl record the router wrote.

Run: python3 loop_test.py   (no pytest; prints "N/N cases passed", exit 1 on fail)
"""
import contextlib
import io
import json
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

os.environ["MM_DEEPSEEK_KEY_FILE"] = "/nonexistent/deepseek_key"
os.environ["MM_ANTHROPIC_KEY_FILE"] = "/nonexistent/anthropic_key"
os.environ["MM_PROVIDERS"] = "deepseek:2"
os.environ["MM_JUDGE"] = "0"
os.environ.pop("MM_ORDER", None)
os.environ.pop("MM_COMMON_GUIDE", None)

from lib import accounting, config, judge, runner, workspace

CASES = []


def case(name):
    def deco(fn):
        CASES.append((name, fn))
        return fn
    return deco


EQY_BODY = "[gold]\nread_verilog -sv gold.sv\nprep -top serv_immdec_p2\n"


@case("judge: prompt includes every changed file, not only wip.tlv")
def _():
    with tempfile.TemporaryDirectory() as mdir:
        config.init(mdir)
        with open(os.path.join(mdir, "wip.tlv"), "w") as f:
            f.write("m4_TLV_version 1d\n")
        with open(os.path.join(mdir, "fev_full_p2.eqy"), "w") as f:
            f.write(EQY_BODY)
        seen = {}

        def fake_call(provider, user, tries=8, system=None):
            seen["prompt"] = user[0]
            return "VERDICT: PASS", {"in": 0, "out": 0, "cache_read": 0, "cache_write": 0}

        judge.call_with_retry = fake_call
        judge.track = lambda provider, u: 0.0
        passed, reason, cost = judge.judge("T", "task text", "before", "after",
                                           changed=["wip.tlv", "fev_full_p2.eqy"])
        p = seen["prompt"]
        assert passed is True
        assert "===FILE: fev_full_p2.eqy AFTER the task===\n" + EQY_BODY in p, p
        assert p.count("===FILE: wip.tlv") == 2, p
        assert "# Other files the worker changed in this attempt" in p, p


@case("judge: no extra block when only wip.tlv changed")
def _():
    with tempfile.TemporaryDirectory() as mdir:
        config.init(mdir)
        seen = {}

        def fake_call(provider, user, tries=8, system=None):
            seen["prompt"] = user[0]
            return "VERDICT: FAIL\nREASON: nope", {"in": 0, "out": 0, "cache_read": 0, "cache_write": 0}

        judge.call_with_retry = fake_call
        judge.track = lambda provider, u: 0.0
        passed, reason, cost = judge.judge("T", "task text", "before", "after", changed=["wip.tlv"])
        assert passed is False and reason == "nope"
        assert "Other files the worker changed" not in seen["prompt"]


TRUNC_REPLY = "===FILE: wip.tlv===\nm4_TLV_version 1d\n\\SV\n   module x(\n"
TRUNC_USAGE = {"in": 100, "out": 8000, "cache_read": 0, "cache_write": 0, "stop": "max_tokens"}
FULL_USAGE = {"in": 100, "out": 10, "cache_read": 0, "cache_write": 0, "stop": "end_turn"}


@case("loop: truncated reply skips apply, feeds targeted feedback, logs stop reason")
def _():
    with tempfile.TemporaryDirectory() as mdir:
        config.init(mdir)
        with open(os.path.join(mdir, "wip.tlv"), "w") as f:
            f.write("m4_TLV_version 1d\n")
        with open(os.path.join(mdir, "task_a.txt"), "w") as f:
            f.write("Do the thing.\n")
        with open(os.path.join(mdir, "order.json"), "w") as f:
            f.write('[["Task A", "task_a.txt"]]\n')
        os.environ["MM_ORDER"] = os.path.join(mdir, "order.json")
        replies = [(TRUNC_REPLY, dict(TRUNC_USAGE)), ("NO_CHANGE", dict(FULL_USAGE))]
        prompts = []

        def fake_call(provider, user, tries=8, system=None):
            prompts.append(user)
            return replies.pop(0)

        def no_apply(text):
            raise AssertionError("apply_files was called on a truncated reply")

        def no_fev():
            raise AssertionError("run_fev was called on a truncated reply")

        runner.call_with_retry = fake_call
        runner.apply_files = no_apply
        runner.run_fev = no_fev
        with contextlib.redirect_stdout(io.StringIO()):
            runner.main()
        assert not replies, "second attempt never ran"
        fb = prompts[1][2]
        assert "cut off by the output token limit after 8000 tokens" in fb, fb
        assert "stop reason: max_tokens" in fb, fb
        assert '"..." omission lines' in fb, fb
        assert "send it in full, with no commentary" in fb, fb
        recs = [json.loads(l) for l in open(os.path.join(mdir, "attempts.jsonl"))]
        assert [r["stop_reason"] for r in recs] == ["max_tokens", "end_turn"], recs
        assert "cut off by the output token limit" in recs[1]["feedback_in"], recs[1]
        assert accounting.stats[-1] == ("Task A", "deepseek (no-change)"), accounting.stats


def main():
    fails = 0
    for name, fn in CASES:
        try:
            fn()
            print(f"  ok   {name}")
        except Exception as e:
            fails += 1
            print(f"  FAIL {name}: {type(e).__name__}: {e}")
    print(f"{len(CASES) - fails}/{len(CASES)} cases passed")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
