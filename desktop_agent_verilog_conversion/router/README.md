# Per-task LLM router for Verilog -> TL-Verilog conversion

A programmatic driver for the conversion flow in this repo: one stateless
API call per attempt, a cheap model first with escalation, and formal
equivalence checking as the only gate. It ran the serv_rf_ram conversion for
$1.62 and both serv_immdec A/B runs (about $10 each with every failed round
included). Per the Sep 1 meeting this is the primary conversion workflow;
the desktop agent flow described in `../README.md` remains supported, and
both share the same task definitions, instructions, fev.sh harness, and
Docker toolchain image.

## What is shared with the desktop agent flow

- `../instructions/desktop_agent_instructions.md` is the core of the cached
  common guide sent to every worker. The router wraps it with
  `guide_preamble.md` (the worker's role in the routed flow) and
  `guide_appendix.md` (a condensed TL-Verilog reference) at startup, so
  instruction updates land in both flows without duplication.
- `../scripts/fev.sh` and the other scripts run inside the container through
  each module dir's `scripts/` link; the router never carries its own copy.
- The Docker toolchain image is built from
  `../conversion_setup/env/Dockerfile.fev` (or the full agent image from
  `Dockerfile` in the same directory).

New here: the routing loop itself (`router.py` + `lib/`), the per-task
prompt files (`tasks/`), per-task judge criteria (`checks/`), reference
hints from the serv_immdec runs (`hints_examples/`), and a `timeout` shim
(`toolshim/`) that widens fev.sh's SandPiper timeout for slower machines.

## Why it is cheap

1. Every attempt is a fresh call built as three blocks: the common guide
   (identical across all tasks and modules), the task + current files
   (identical across retries within a task), and the latest feedback. Cache
   breakpoints sit after the first two blocks, so retries are mostly cache
   reads. Retry attempts routinely hit 90%+ input cache.
2. deepseek attempts each task first; claude only sees tasks deepseek failed.
   On serv_rf_ram deepseek handled 21 of 45 checkpoints for about 7 cents.
3. The full shared instructions ride along in the cached prefix, so nothing
   is re-sent at full price.

## What keeps it honest

- fev.sh must print "All FEV runs successful" for a task to advance. No
  exceptions; the router never edits harness files, and models cannot either
  (HARNESS_FILES blocklist).
- An oversight judge (separate LLM call, skeptical system prompt) checks the
  refactoring INTENT after FEV passes; its FAIL reason feeds the retry loop.
- NO_CHANGE claims are cross-checked by the next provider, then judged.
- MM_ACCEPT_GLOB / MM_ACCEPT_DISTINCT block the observed work-dodging moves
  (no files created; per-config designs byte-identical).
- attempts.jsonl records every attempt's feedback-in and full reply.

## Setup

1. Key files (a file containing only the key):
   - `~/.secrets/deepseek_key` (or MM_DEEPSEEK_KEY_FILE)
   - `~/.secrets/anthropic_key` (or MM_ANTHROPIC_KEY_FILE); also used by the
     judge, so needed even when the worker is deepseek or the agent.
2. The toolchain docker image, from this repo:
   `cd desktop_agent_verilog_conversion/conversion_setup/env && docker build -f Dockerfile.fev -t mm-convert:latest .`
3. A checkout of the Verilog project with tlv/<module> work dirs (each work
   dir holds wip.tlv, fev.eqy, config.json, orig.sv, prepared.sv and a
   scripts/ link into this repo). MM_LLMTLV_DIR defaults to this repo, the
   one containing the router.

The router preflights all of this and fails fast with a clear message if a
key file, the docker image, fev.sh, or the agent CLI is missing.

## Run

Works from any directory; task paths resolve relative to the order file.

```
MM_SERV_DIR=/path/to/serv \
MM_PROVIDERS="deepseek:2,claude:6" \
python3 desktop_agent_verilog_conversion/router/router.py /path/to/serv/tlv/<module_dir>
```

Tests, both dependency-free:

```
python3 tests.py        # 34 parser cases for the edit formats
python3 smoke_test.py   # imports every module, exercises preflight
```

The router resumes: completed tasks and the in-flight attempt budget live in
`<module_dir>/e6_state.json`, so rerunning the same command continues where
it stopped (survives network drops and machine sleep; run it in tmux on a
server and your laptop is irrelevant).

## Structure

`router.py` is the entry point: argv check, config init, preflight, loop.
The implementation lives in `lib/`, one concern per module:

| Module | Role |
|---|---|
| lib/config.py | every MM_* knob and shared constant, read once at import; MDIR set from argv |
| lib/prompts.py | system prompts, the composed cached common guide, per-attempt prompt assembly |
| lib/providers.py | deepseek/claude API calls with caching and retry, plus the Claude Code agent worker |
| lib/edits.py | edit-format parsing and applying: dots omissions, search/replace blocks, NO_CHANGE, justifications |
| lib/fev.py | docker invocation of the shared fev.sh and SandPiper error-context enrichment |
| lib/judge.py | the oversight judge, judge.json records, and the acceptance checks |
| lib/workspace.py | module-dir file access, status.json, attempts.jsonl and unparsed-reply logging |
| lib/accounting.py | cost and cache tracking, spend caps, run summary |
| lib/state.py | e6_state.json load/save for resume |
| lib/preflight.py | fail-fast environment checks before any paid call |
| lib/runner.py | the task loop: provider escalation, NO_CHANGE cross-check, judge routing, resume bookkeeping |

## Environment reference

| Variable | Default | Meaning |
|---|---|---|
| MM_ORDER | router/tasks/order.json | task list, [name, task-file] pairs; task paths resolve relative to the order file |
| MM_PROVIDERS | deepseek:2,claude:2 | attempt budget per provider, in order |
| MM_EDIT_FORMAT | dots | dots (whole file with "..." omissions) or sr (search/replace blocks) |
| MM_JUDGE | 1 | oversight judge on/off |
| MM_CHECKS | router/checks | per-task judge criteria files |
| MM_HINTS | router/hints | per-task user guidance files, appended to the task prompt; filename = task name with every non-alphanumeric run replaced by `_`, plus `.txt` (e.g. `Non_vector_Signals.txt`) |
| MM_COMMON_GUIDE | (composed) | a single prebuilt guide file, replacing the default composition from the shared instructions |
| MM_ACCEPT_GLOB | (off) | glob whose match count must increase during the task |
| MM_ACCEPT_DISTINCT | (off) | 1 = per-config wip_*.sv must differ |
| MM_MAX_COST_DEEPSEEK / _CLAUDE | 2.0 / 5.0 | USD safety caps per run |
| MM_SERV_DIR | ./serv | docker mount for the Verilog project checkout |
| MM_LLMTLV_DIR | this repo | docker mount for the LLM_TLV checkout (fev.sh harness) |
| MM_TOOLSHIM_DIR | router/toolshim | docker mount for the timeout shim |
| MM_DOCKER_IMAGE / MM_DOCKER_USER | mm-convert:latest / (none) | toolchain container |
| MM_DEEPSEEK_KEY_FILE / MM_ANTHROPIC_KEY_FILE | ~/.secrets/... | API key file paths |
| MM_AGENT_CMD / MM_AGENT_MODEL | claude / sonnet | agent worker CLI and model |
| MM_AGENT_MAX_TURNS / MM_AGENT_TIMEOUT | 40 / 900 | agent worker limits |

## Agent worker mode

`MM_PROVIDERS="agent:2"` (or e.g. `"deepseek:2,agent:2"`) replaces the raw
API worker with Claude Code running headless in the module directory: the
agent edits the design files directly with file tools only (no shell), so
edit formats do not apply at all. Harness files are snapshotted before every
attempt and force-restored if touched, fev.sh and the judge gate exactly as
for API workers, and every attempt's report still lands in attempts.jsonl.
Requires the `claude` CLI installed and logged in (subscription usage, no
API cost for the worker; the judge still uses the anthropic key file).
This is the direction of issue #8: programmatic sequencing with an agentic
refactor step.

## Hints: the ratchet

When a task fails its whole attempt budget, the run stops. Write what you
learned into `hints/<Task_Name>.txt` (mine the previous conversion's history
for the verified pattern; verify fixes by hand through fev.sh before turning
them into a hint) and rerun; the hint is appended to the task prompt as user
guidance. `hints_examples/serv_immdec/` contains the full hint set that
carried both serv_immdec A/B runs to completion, as a reference for the
style: state why the attempts failed, give the verified pattern byte-exact,
and say explicitly what not to touch.

## Edit formats and the A/B result

Both formats are implemented (MM_EDIT_FORMAT). The serv_immdec A/B (same
module, tasks, models, hints) finished 24/24 on both, $9.93 for dots vs
$11.78 for sr, with the gap concentrated in one whole-file restructure task
that search/replace blocks could not express. dots is the default; sr fails
hard to a full-file requirement after two failed applies.
