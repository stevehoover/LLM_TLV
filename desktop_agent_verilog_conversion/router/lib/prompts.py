"""System prompts, the cached common guide, and per-attempt user prompts."""

import os

from . import config
from .workspace import context_files, snap

_FMT_DOTS = (
    "Only include files you change. For a file that already exists, you may shorten your "
    "output by replacing large UNCHANGED regions with a single line containing exactly "
    "... (three dots, no indentation). Include several unchanged context lines before and "
    "after each ... line so the omitted region maps unambiguously onto the original file, "
    "and preserve those context lines' exact indentation. Never place ... on or next to "
    "lines you are changing, and never use ... in a brand-new file. "
)
_FMT_SR = (
    "Only include files you change. For a file that already exists, instead of the full "
    "contents you may provide one or more search/replace edits inside the file block:\n"
    "<<<<<<< SEARCH\n<exact lines copied verbatim from the current file>\n=======\n"
    "<replacement lines>\n>>>>>>> REPLACE\n"
    "The SEARCH text must match the current file exactly (same whitespace) and exactly "
    "once; include enough surrounding lines to make it unique. Use multiple blocks for "
    "multiple edits, in top-to-bottom file order. A brand-new file must be written out "
    "in full with no search/replace blocks. "
)
SYSTEM = (
    "You are an expert digital-design refactoring agent converting Verilog to TL-Verilog "
    "in small, formally verified steps. You will be given one refactoring task and the "
    "current files. Reply with the updated contents of every file you change, "
    "using EXACTLY this format for each file (no markdown fences, no commentary):\n"
    "===FILE: <filename>===\n<file contents>\n===END===\n"
    + (_FMT_SR if config.EDIT_FORMAT == "sr" else _FMT_DOTS) +
    "If the task requires "
    "no change to this design, reply with exactly: NO_CHANGE\n"
    "A separate reviewing agent will verify that the task's goal was actually achieved; "
    "it cannot be talked into approving unfinished work. If part of the goal genuinely "
    "cannot be achieved for a specific technical reason (a tool limitation, a construct "
    "with no equivalent), say so explicitly by adding this block after your files:\n"
    "===JUSTIFICATION===\n<the specific technical reason, referencing the exact signals "
    "or constructs>\n===END===\n"
    "The reviewer weighs justifications on their technical merit; vague effort claims "
    "are rejected."
)

AGENT_PREAMBLE = (
    "You are a digital-design refactoring agent converting Verilog to TL-Verilog in "
    "small, formally verified steps. You are working directly in this module directory. "
    "Perform ONE refactoring task by editing the design files in place: wip.tlv, "
    "fev.eqy, fev_full*.eqy, config.json, tracker.md. Rules:\n"
    "- Do NOT run fev.sh, docker, or any command; the harness runs formal verification "
    "after you finish, and a separate reviewing agent checks that the task's goal was "
    "actually achieved. It cannot be talked into approving unfinished work.\n"
    "- Do NOT edit these harness files: status.json, e6_state.json, feved.tlv, "
    "fully_feved.tlv, orig.sv, prepared.sv, match_lines.eqy, attempts.jsonl.\n"
    "- If the task genuinely requires no change, edit nothing and end your reply with "
    "NO_CHANGE plus a ===JUSTIFICATION===/===END=== block naming the exact constructs "
    "and why; vague effort claims are rejected.\n"
    "- When your edits are complete, stop and summarize what you changed in 2-3 "
    "sentences.\n\n"
)

# The common guide is shared by EVERY task and module: it goes at the front
# of the prompt as a cache prefix that survives across tasks. Task+files
# change per task, so they come after; feedback changes per attempt, so last.
# It is composed from the repo's shared desktop agent instructions (the same
# file the desktop agent flow uses) wrapped in a router-role preamble and a
# TL-Verilog quick reference; MM_COMMON_GUIDE substitutes a single prebuilt
# file instead.
COMMON = ""
_cg = os.environ.get("MM_COMMON_GUIDE", "")
if _cg:
    if os.path.exists(_cg):
        COMMON = "# TL-Verilog language reference (common to all tasks)\n\n" + open(_cg).read() + "\n"
else:
    _parts = [os.path.join(config.ROUTER_DIR, "guide_preamble.md"),
              os.path.join(config.CONVERSION_DIR, "instructions", "desktop_agent_instructions.md"),
              os.path.join(config.ROUTER_DIR, "guide_appendix.md")]
    if all(os.path.exists(p) for p in _parts):
        COMMON = ("# TL-Verilog language reference (common to all tasks)\n\n"
                  + "".join(open(p).read() for p in _parts) + "\n")


def build_user(task, feedback=None):
    # Three parts: common (identical across tasks, cache breakpoint 1),
    # stable (task + files, identical across retries within a task, cache
    # breakpoint 2), and feedback (changes every attempt, so it goes last).
    u = "# Task\n\n" + task + "\n"
    for n in context_files():
        u += f"\n===FILE: {n}===\n" + snap(n) + "\n===END===\n"
    fb = ""
    if feedback:
        fb = ("\n# Previous attempt FAILED verification. Tool output:\n\n" + feedback[-3000:] +
              "\n\nFix the problem and reply with the complete corrected files. If the "
              "remaining constructs genuinely cannot be converted for a specific technical "
              "reason, it is acceptable to reply NO_CHANGE followed by a "
              "===JUSTIFICATION===/===END=== block naming the exact constructs and why; "
              "the reviewing agent will weigh it on its merits.")
    return COMMON, u, fb
