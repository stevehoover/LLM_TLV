#!/usr/bin/env python3
"""Per-task LLM router for the Verilog -> TL-Verilog conversion flow.

Runs the task list one task at a time. Each task is attempted by a cheap
provider first (deepseek), escalating to a stronger one (claude) on failure.
Every attempt is a fresh stateless API call; fev.sh (formal equivalence
checking) is the only gate that advances a task. Key mechanisms:

  - Prompt caching: each call is (common guide, task+files, feedback), with
    cache breakpoints after the first two parts, so retries hit cache.
  - Oversight judge: after FEV passes, a separate skeptical LLM call checks
    whether the task's REFACTORING GOAL was achieved (FEV only proves
    behavior is unchanged). FAIL feeds back into the retry loop.
  - NO_CHANGE cross-check: a NO_CHANGE claim is confirmed by the next
    provider and then judged; workers never referee their own intent.
  - Edit formats (MM_EDIT_FORMAT): "dots" (whole file with "..." omission
    lines, applied by diff alignment, ambiguity fails soft to a full-file
    request) or "sr" (aider-style search/replace blocks, exact-once match,
    hard fallback to full file after repeated apply failures).
  - Acceptance checks: MM_ACCEPT_GLOB (required new files), and
    MM_ACCEPT_DISTINCT=1 (per-config designs must actually differ).
  - attempts.jsonl: every worker attempt's feedback-in and full reply are
    recorded so the exact exchange is inspectable after the fact.
  - Agent worker mode: provider "agent" in MM_PROVIDERS runs Claude Code
    headless in the module dir; it edits design files directly with file
    tools only (no shell), harness files are snapshotted and force-restored
    if touched, and fev.sh/judge gate exactly as for API workers.
  - Preflight: key files, docker image, fev.sh, and the agent CLI are
    checked up front with clear errors before any paid call.
  - Resume: e6_state.json tracks completed tasks and the in-flight attempt
    budget; rerunning the router continues where it stopped.

Usage:
  MM_PROVIDERS="deepseek:2,claude:2" python3 router.py <module_dir>

See README.md in this directory for the full environment reference and
lib/ for the implementation, split by concern.
"""

import os
import sys

if len(sys.argv) < 2 or not os.path.isdir(sys.argv[1]):
    sys.exit("usage: router.py <module_dir>   (module_dir must exist and contain wip.tlv, fev.eqy, scripts/fev.sh)")

from lib import config

config.init(sys.argv[1])

from lib import preflight, runner

if __name__ == "__main__":
    preflight.preflight()
    runner.main()
