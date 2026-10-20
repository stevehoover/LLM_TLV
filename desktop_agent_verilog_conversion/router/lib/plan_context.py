"""Read-back of the design-level combining plan (plan.py collateral) for the
current module, and the prompt block that hands the decision to the worker.

The router runs per module work dir; the plan is one design-level file, so it
is found by walking up from the module dir (module dirs sit at
<design>/tlv/<module>), then falling back to the project checkout root.
MM_PLAN names a plan file or its directory explicitly. With no plan file the
lookup yields nothing and the prompt is unchanged.
"""

import json
import os

from . import config

HEADING = "# Hierarchy combining plan for this module"

PLAN_FILE = "combining_plan.json"

MEANING = {
    "module": ("Strategy `module` means this module stays a real module: it is not inlined "
               "into a parent and not turned into a macro."),
    "macro": ("Strategy `macro` means this module becomes a TL-Verilog macro, included and "
              "instantiated at each of its instantiation sites."),
    "inline": ("Strategy `inline` means this module is inlined into its parent as a TL-Verilog "
               "scope named after it, rather than surviving as a separate module or macro."),
}

_cache = {}


def plan_path():
    if config.PLAN:
        p = os.path.join(config.PLAN, PLAN_FILE) if os.path.isdir(config.PLAN) else config.PLAN
        return p if os.path.isfile(p) else None
    if not config.MDIR:
        return None
    d = os.path.abspath(config.MDIR)
    while True:
        p = os.path.join(d, PLAN_FILE)
        if os.path.isfile(p):
            return p
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    p = os.path.join(config.SERV_DIR, PLAN_FILE)
    return p if os.path.isfile(p) else None


def load():
    path = plan_path()
    if not path:
        return None
    if path not in _cache:
        try:
            _cache[path] = json.load(open(path))
        except Exception:
            _cache[path] = None
    return _cache[path]


def module_name():
    return os.path.basename(os.path.normpath(config.MDIR)) if config.MDIR else ""


def block(plan, name):
    entry = (plan.get("modules") or {}).get(name)
    if not isinstance(entry, dict):
        return ""
    strategy = entry.get("strategy", "")
    lines = [f"The combining strategy for this design was decided and accepted in the "
             f"design-level plan for top module `{plan.get('top', '')}`. The decision for this "
             f"module is below. Apply it as given; do not re-derive it or choose differently.",
             "",
             f"- module: `{name}`",
             f"- strategy: {strategy}",
             f"- instantiations: {entry.get('instantiations', 0)}",
             f"- reason: {entry.get('reason', '')}"]
    if entry.get("user_override"):
        lines.append("- this strategy was set by the user, overriding the proposal.")
    if name in (plan.get("synthesis_boundaries") or []):
        lines.append("- this module is a synthesis boundary and stays a real module.")
    if strategy in MEANING:
        lines += ["", MEANING[strategy]]
    return "\n".join(lines) + "\n"


def for_task(tname):
    if tname not in config.PLAN_TASKS:
        return ""
    plan = load()
    if not isinstance(plan, dict):
        return ""
    return block(plan, module_name())
