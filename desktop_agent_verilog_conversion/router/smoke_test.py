#!/usr/bin/env python3
"""Smoke test: import every router module, check the default configuration
resolves inside this repo, and run preflight against a deliberately broken
environment, expecting a graceful PREFLIGHT FAILED report naming each
missing piece. Makes no network calls and costs nothing.

Run: python3 smoke_test.py
"""
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

os.environ["MM_DEEPSEEK_KEY_FILE"] = "/nonexistent/deepseek_key"
os.environ["MM_ANTHROPIC_KEY_FILE"] = "/nonexistent/anthropic_key"
os.environ["MM_DOCKER_IMAGE"] = "mm-router-smoke-no-such-image:none"
os.environ["MM_AGENT_CMD"] = "/nonexistent/claude"
os.environ["MM_PROVIDERS"] = "deepseek:1,agent:1"
os.environ.pop("MM_ORDER", None)
os.environ.pop("MM_COMMON_GUIDE", None)

from lib import (accounting, config, edits, fev, judge, preflight, prompts,
                 providers, runner, state, workspace)

failures = []


def check(ok, what):
    if not ok:
        failures.append(what)


check(config.REPO_DIR == os.path.dirname(os.path.dirname(HERE)),
      f"REPO_DIR resolved to {config.REPO_DIR}, expected the LLM_TLV checkout root")
check(config.LLMTLV_DIR == config.REPO_DIR,
      f"default MM_LLMTLV_DIR is {config.LLMTLV_DIR}, expected {config.REPO_DIR}")

order = config.load_order()
check(len(order) == 27, f"default order.json lists {len(order)} tasks, expected 27")
check(all(os.path.isfile(path) for _, path in order),
      "a task file named in the default order.json does not exist")

check(prompts.COMMON.startswith("# TL-Verilog language reference"),
      "COMMON guide did not compose from guide_preamble.md + shared "
      "instructions/desktop_agent_instructions.md + guide_appendix.md")
check("NOTE ON YOUR ROLE IN THIS FLOW" in prompts.COMMON,
      "COMMON guide is missing the router-role preamble")

with tempfile.TemporaryDirectory() as mdir:
    config.init(mdir)
    try:
        preflight.preflight()
        failures.append("preflight passed against a fake environment; it must fail")
    except SystemExit as e:
        msg = str(e)
        for want in ("PREFLIGHT FAILED",
                     "API key file for deepseek",
                     "API key file for claude",
                     "scripts/fev.sh",
                     "docker",
                     "agent worker command not found"):
            check(want in msg, f"preflight report is missing: {want!r}\nreport was:\n{msg}")

for line in failures:
    print("FAIL:", line)
if failures:
    print("smoke test FAILED")
    sys.exit(1)
print("smoke test passed (11 modules imported, preflight reported the broken environment)")
