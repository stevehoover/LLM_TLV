"""Environment knobs, shared constants, and run configuration.

Everything the MM_* environment variables control is read here, once, at
import time. MDIR (the module work directory) comes from the command line
and is set by init(); modules that need it read config.MDIR at call time.
"""

import json
import os
import re

ROUTER_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONVERSION_DIR = os.path.dirname(ROUTER_DIR)
REPO_DIR = os.path.dirname(CONVERSION_DIR)

MDIR = None


def init(mdir):
    global MDIR
    MDIR = mdir


def load_order():
    order_path = os.environ.get("MM_ORDER", os.path.join(ROUTER_DIR, "tasks", "order.json"))
    order_dir = os.path.dirname(os.path.abspath(order_path))
    order = json.load(open(order_path))
    # Task-file paths in the order file are resolved relative to the order file
    # itself, so the router works from any CWD.
    return [[name, path if os.path.isabs(path) else os.path.join(order_dir, path)]
            for name, path in order]


MAX_COST = {
    "deepseek": float(os.environ.get("MM_MAX_COST_DEEPSEEK", "2.0")),
    "claude": float(os.environ.get("MM_MAX_COST_CLAUDE", "5.0")),
}
MODEL_NAME = {"deepseek": "deepseek-v4-flash", "claude": "claude-sonnet-4-6",
              "agent": "claude-code-agent"}

# Agent worker mode (issue #8 direction, Steve Aug 18: "just ask the agent to
# modify the file"): provider "agent" in MM_PROVIDERS invokes Claude Code
# headless in the module dir. The agent edits design files directly with
# file tools only (no shell), so edit formats do not apply; the harness still
# owns fev.sh, the judge, and all acceptance checks. Harness files are
# snapshotted and force-restored if the agent touches them.
AGENT_CMD = os.environ.get("MM_AGENT_CMD", "claude")
AGENT_MODEL = os.environ.get("MM_AGENT_MODEL", "sonnet")
AGENT_MAX_TURNS = int(os.environ.get("MM_AGENT_MAX_TURNS", "40"))
AGENT_TIMEOUT = int(os.environ.get("MM_AGENT_TIMEOUT", "900"))

# Edit formats for the A/B experiment: the "..." omission style vs the
# search/replace block style modern coding agents use. MM_EDIT_FORMAT=dots|sr.
EDIT_FORMAT = os.environ.get("MM_EDIT_FORMAT", "dots")

SERV_DIR = os.environ.get("MM_SERV_DIR", os.path.abspath("serv"))
# The LLM_TLV checkout mounted into the container is, by default, the repo
# this router lives in: the module dirs' scripts/ links and fev.sh come from
# the same tree.
LLMTLV_DIR = os.environ.get("MM_LLMTLV_DIR", REPO_DIR)
TOOLSHIM_DIR = os.environ.get("MM_TOOLSHIM_DIR", os.path.join(ROUTER_DIR, "toolshim"))
DOCKER_IMAGE = os.environ.get("MM_DOCKER_IMAGE", "mm-convert:latest")
DOCKER_USER = os.environ.get("MM_DOCKER_USER", "")

JUDGE_ON = os.environ.get("MM_JUDGE", "1") == "1"

# Acceptance criterion beyond FEV (blocks "dodge by creating no files"):
# MM_ACCEPT_GLOB names a glob whose match count must INCREASE during the task.
ACCEPT_GLOB = os.environ.get("MM_ACCEPT_GLOB", "")

# MM_ACCEPT_DISTINCT=1: per-config generated designs (wip_*.sv) must truly
# differ. Blocks the "vacuous config" dodge where a hardcoded var() in
# wip.tlv overrides the per-config m5 define, every config elaborates to the
# same design, and FEV passes meaninglessly.
ACCEPT_DISTINCT = os.environ.get("MM_ACCEPT_DISTINCT", "") == "1"

# Harness/fev.sh bookkeeping files the model must never write. Observed
# dodge: a model "overruled" a NO_CHANGE by editing status.json + tracker.md,
# touching no design file yet getting credited with work.
HARNESS_FILES = {"status.json", "e6_state.json", "feved.tlv", "fully_feved.tlv",
                 "match_lines.eqy", "orig.sv", "prepared.sv"}
DESIGN_FILES_RE = re.compile(r"^(wip\.tlv|fev.*\.eqy|config\.json)$")

PROVIDERS = [tuple(x.strip().split(":")) for x in os.environ.get("MM_PROVIDERS", "deepseek:2,claude:2").split(",") if x.strip()]
PROVIDERS = [(p, int(n)) for p, n in PROVIDERS]
