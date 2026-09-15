#!/usr/bin/env python3
"""Test for the combining-plan pre-step: builds a tiny fake design (a top
instantiating child_a once and parameterized child_b twice), runs plan.py
mechanical-only and non-interactively, and checks the persisted plan.
Makes no network calls and costs nothing.

Run: python3 plan_test.py
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

TOP = """
module top (input clk, input [7:0] a, output [7:0] y);
   wire [7:0] w0, w1, w2;
   child_a u_a (.clk(clk), .d(a), .q(w0));
   child_b #(.W(8)) u_b0 (.clk(clk), .d(w0), .q(w1));
   child_b
     #(.W(8))
   u_b1
     (.clk(clk), .d(w1), .q(w2));
   assign y = w2;
endmodule
"""

CHILD_A = """
module child_a (input clk, input [7:0] d, output reg [7:0] q);
   // child_b mentioned in a comment must not count
   always @(posedge clk) q <= d;
endmodule
"""

CHILD_B = """
module child_b #(parameter W = 4) (input clk, input [W-1:0] d, output reg [W-1:0] q);
   always @(posedge clk) q <= ~d;
endmodule
"""

failures = []


def check(ok, what):
    if not ok:
        failures.append(what)


with tempfile.TemporaryDirectory() as d:
    os.mkdir(os.path.join(d, "rtl"))
    for name, text in [("top.v", TOP), ("child_a.v", CHILD_A), ("child_b.sv", CHILD_B)]:
        with open(os.path.join(d, "rtl", name), "w") as f:
            f.write(text)
    r = subprocess.run([sys.executable, os.path.join(HERE, "plan.py"), d, "--no-llm"],
                       stdin=subprocess.DEVNULL, capture_output=True, text=True)
    check(r.returncode == 0, f"plan.py exited {r.returncode}: {r.stderr}")
    check("non-interactive" in r.stdout, "non-interactive default-accept notice missing")
    plan_path = os.path.join(d, "combining_plan.json")
    check(os.path.isfile(plan_path), "combining_plan.json not written")
    check(os.path.isfile(os.path.join(d, "combining_plan.md")), "combining_plan.md not written")
    if os.path.isfile(plan_path):
        plan = json.load(open(plan_path))
        check(plan["top"] == "top", f"top resolved to {plan.get('top')}, expected top")
        mods = plan["modules"]
        check(set(mods) == {"top", "child_a", "child_b"},
              f"modules surveyed: {sorted(mods)}, expected top/child_a/child_b")
        for name, strategy, n in [("top", "module", 0), ("child_a", "inline", 1),
                                  ("child_b", "macro", 2)]:
            e = mods.get(name, {})
            check(e.get("strategy") == strategy,
                  f"{name}: strategy {e.get('strategy')}, expected {strategy}")
            check(e.get("instantiations") == n,
                  f"{name}: {e.get('instantiations')} instantiations, expected {n}")
            check(e.get("user_override") is False, f"{name}: user_override should be False")
        check(plan["synthesis_boundaries"] == [], "synthesis_boundaries should be empty")

for line in failures:
    print("FAIL:", line)
if failures:
    print("plan test FAILED")
    sys.exit(1)
print("plan test passed (fake design surveyed; top=module, child_a=inline, child_b=macro)")
