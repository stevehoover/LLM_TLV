#!/usr/bin/env python3
"""Test that the combining tasks consume the combining plan: builds a temp
design dir holding a fake combining_plan.json with a module work dir under it
(<design>/tlv/<module>), then checks the lookup, the injected prompt block for
a combining task, its absence for a non-combining task, and that removing the
plan file restores the exact prompt the router built before. Makes no network
calls and costs nothing.

Run: python3 plan_wire_test.py
"""
import json
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

os.environ["MM_DEEPSEEK_KEY_FILE"] = "/nonexistent/deepseek_key"
os.environ["MM_ANTHROPIC_KEY_FILE"] = "/nonexistent/anthropic_key"
os.environ.pop("MM_PLAN", None)
os.environ.pop("MM_PLAN_TASKS", None)
os.environ.pop("MM_HINTS", None)
os.environ.pop("MM_ORDER", None)

from lib import config, plan_context, prompts, runner

PLAN = {
    "top": "top",
    "modules": {
        "top": {"strategy": "module", "instantiations": 0,
                "reason": "conversion target (top)", "user_override": False},
        "child_a": {"strategy": "inline", "instantiations": 1,
                    "reason": "single use; inline as TLV scope /child_a", "user_override": False},
        "child_b": {"strategy": "macro", "instantiations": 2,
                    "reason": "instantiated 2 times; shared macro", "user_override": True},
    },
    "synthesis_boundaries": [],
}

COMBINING = "Combine Repeated Logic"
OTHER = "Reset and Clock"

failures = []


def check(ok, what):
    if not ok:
        failures.append(what)


def task_file(name):
    for tname, path in config.load_order():
        if tname == name:
            return path
    raise RuntimeError(f"task {name!r} not in the default order")


with tempfile.TemporaryDirectory() as design:
    mdir = os.path.join(design, "tlv", "child_b")
    os.makedirs(mdir)
    with open(os.path.join(mdir, "wip.tlv"), "w") as f:
        f.write("\\m5_TLV_version 1d: tl-x.org\n")
    plan_path = os.path.join(design, "combining_plan.json")
    with open(plan_path, "w") as f:
        json.dump(PLAN, f, indent=2)
    config.init(mdir)

    check(plan_context.plan_path() == plan_path,
          f"lookup found {plan_context.plan_path()}, expected {plan_path}")
    check(plan_context.module_name() == "child_b",
          f"module name resolved to {plan_context.module_name()!r}, expected 'child_b'")

    combining_file, other_file = task_file(COMBINING), task_file(OTHER)
    task, _, planned = runner.build_task(COMBINING, combining_file)
    _, u, _ = prompts.build_user(task)
    check(plan_context.HEADING in u, "plan heading missing from the combining task prompt")
    for want in ("strategy: macro", "instantiated 2 times; shared macro",
                 "do not re-derive it", "set by the user",
                 "becomes a TL-Verilog macro"):
        check(want in u, f"injected block is missing {want!r}")
    check(planned and planned in task, "build_task did not report the injected block")

    task_other, _, planned_other = runner.build_task(OTHER, other_file)
    _, u_other, _ = prompts.build_user(task_other)
    check(planned_other == "", "a non-combining task was given the plan")
    check(plan_context.HEADING not in u_other,
          "plan block leaked into a non-combining task prompt")
    check(task_other == open(other_file).read(),
          "a non-combining task prompt is not the bare task file")

    os.remove(plan_path)
    plan_context._cache.clear()
    task_bare, _, planned_bare = runner.build_task(COMBINING, combining_file)
    _, u_bare, _ = prompts.build_user(task_bare)
    _, u_today, _ = prompts.build_user(open(combining_file).read())
    check(planned_bare == "", "a missing plan file still produced an injected block")
    check(task_bare == open(combining_file).read(),
          "with no plan file the task text is not the bare task file")
    check(u_bare == u_today,
          "with no plan file the assembled prompt is not byte-identical to today's")

    config.PLAN = os.path.join(design, "elsewhere")
    os.mkdir(config.PLAN)
    with open(os.path.join(config.PLAN, "combining_plan.json"), "w") as f:
        json.dump(PLAN, f, indent=2)
    plan_context._cache.clear()
    check(plan_context.plan_path() == os.path.join(config.PLAN, "combining_plan.json"),
          "MM_PLAN override did not select the explicit plan directory")
    config.PLAN = ""

for line in failures:
    print("FAIL:", line)
if failures:
    print("plan wire test FAILED")
    sys.exit(1)
print("plan wire test passed (plan found, injected into the combining task only, "
      "prompt unchanged when absent)")
