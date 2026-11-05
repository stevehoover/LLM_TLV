#!/usr/bin/env python3

# Self-contained tests for gen_match_lines.py's gate-reference resolution.
#
# Run: python3 gen_match_lines_test.py   (no pytest; prints "N/N cases passed",
# exit 1 on fail). Loads the script as a module; no yosys, sandpiper or
# design files are needed, the gate enumeration is given by hand.
#
# What is pinned down here: a gate reference resolves by the exact generated
# name rule only. A gate name that differs from the expected name just in
# case or underscores is refused, whether it is the only look-alike or one
# of several, and the failure names the expected form and every look-alike.

import importlib.util
import io
import os
import sys
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("gml", os.path.join(HERE, "gen_match_lines.py"))
gml = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gml)

PASSED = 0
FAILED = 0


# Record one test outcome.
def check(ok, what):
    # Args:
    #    ok: Whether the case held
    #    what: One-line description printed on failure
    #
    # Returns:
    #    None
    global PASSED, FAILED
    if ok:
        PASSED += 1
    else:
        FAILED += 1
        print("FAIL:", what)


# Build a gate-side signal dict of the shape side_signals returns, from names alone.
def sigs(*names, reg=False):
    # Args:
    #    names: Gate signal names, as enumerated by yosys
    #    reg: Whether each signal should count as holding state
    #
    # Returns:
    #    Dict mapping each name to a signal record with one bit
    return {n: {"bits": [i + 1], "regbits": [i + 1] if reg else [], "reg": reg, "port": False}
            for i, n in enumerate(names)}


# Resolve a reference against a gate enumeration, capturing anything printed.
def resolve(ref, gate_sigs):
    # Args:
    #    ref: The gate reference to resolve
    #    gate_sigs: The gate-side signal dict
    #
    # Returns:
    #    (resolved, printed, near) where resolved is gate_ref_exists' verdict,
    #    printed is whatever it wrote to stdout, and near is near_misses' list
    index = gml.gate_name_index(gate_sigs)
    buf = io.StringIO()
    with redirect_stdout(buf):
        ok = gml.gate_ref_exists(ref, gate_sigs, index, ({}, False))
    return ok, buf.getvalue(), gml.near_misses(ref, index)


# Run check() on a match section against hand-built enumerations, capturing its verdict.
def run_check(gold_sigs, gate_sigs, match_lines):
    # Args:
    #    gold_sigs: The gold-side signal dict
    #    gate_sigs: The gate-side signal dict
    #    match_lines: List of [match] section lines
    #
    # Returns:
    #    (exit_code, output) where exit_code is 0 on PASS and the SystemExit
    #    code otherwise
    buf = io.StringIO()
    code = 0
    with redirect_stdout(buf):
        try:
            gml.check("t.eqy", gold_sigs, gate_sigs, match_lines, ({}, False))
        except SystemExit as e:
            code = e.code
    return code, buf.getvalue()


# Exact rule: the documented mangling resolves, silently.
ok, out, near = resolve("/rf_ram_if|default<>0$rgnt", sigs("RfRamIf_DEFAULT_rgnt_a0", "RfRamIf_DEFAULT_rgnt_n1"))
check(ok and out == "", "scoped reference resolves by the exact rule with nothing printed")

ok, out, near = resolve("|default<>0$wtrig0_r", sigs("DEFAULT_wtrig0_r_a0"))
check(ok and out == "", "flat reference resolves by the exact rule with nothing printed")

# Exact match wins when a look-alike is also present: $a_b and $ab are two signals.
both = sigs("DEFAULT_a_b_a0", "DEFAULT_ab_a0")
ok, out, near = resolve("|default<>0$a_b", both)
check(ok and out == "", "$a_b resolves to DEFAULT_a_b when DEFAULT_ab also exists")
ok, out, near = resolve("|default<>0$ab", both)
check(ok and out == "", "$ab resolves to DEFAULT_ab when DEFAULT_a_b also exists")

# A unique look-alike is refused, and named: $rdata_0 must not pass as $rdata0.
ok, out, near = resolve("|default<>0$rdata_0", sigs("DEFAULT_rdata0_a0"))
check(not ok, "$rdata_0 does not resolve to the only near miss DEFAULT_rdata0")
check(out == "", "refusal of a unique near miss prints no NOTE from the resolver")
check(near == ["DEFAULT_rdata0"], f"unique near miss is reported by name, got {near}")

ok, out, near = resolve("|default<>0$a_b", sigs("DEFAULT_ab_a0"))
check(not ok and near == ["DEFAULT_ab"], f"$a_b is refused against DEFAULT_ab alone, got {ok} {near}")

# Two distinct scopes collide under squash: /rf_ram_if and /rfram_if. A
# reference to neither is refused and both are listed.
two = sigs("RfRamIf_DEFAULT_x_a0", "RframIf_DEFAULT_x_a0")
ok, out, near = resolve("/rf_ramif|default<>0$x", two)
check(not ok, "reference to a scope that exists only as two look-alikes is refused")
check(near == ["RfRamIf_DEFAULT_x", "RframIf_DEFAULT_x"], f"both colliding scopes are listed, got {near}")
ok, out, near = resolve("/rf_ram_if|default<>0$x", two)
check(ok, "the exact scope still resolves when a look-alike scope also exists")

# Stage suffix look-alike: $fooa0 is not $foo_a0.
ok, out, near = resolve("|default<>1$fooa0", sigs("DEFAULT_foo_a0_a1"))
check(not ok and near == ["DEFAULT_foo_a0"], f"$fooa0 is refused against DEFAULT_foo_a0, got {ok} {near}")

# Generate-local shape: the L<n>_ prefixes are stripped for the exact rule
# only; a squash-only look-alike through that shape is still refused.
gen = sigs("L1_Sort_Level[level].L2_a_num_a1")
ok, out, near = resolve("/sort/level$a_num", gen)
check(ok, "generate-block name resolves by the exact rule after L-prefix stripping")
ok, out, near = resolve("/sort$level_a_num", gen)
check(not ok and near == ["Sort_Level_a_num"], f"squash-only look-alike through the generate shape is refused, got {ok} {near}")

# Nothing close: refused with an empty near-miss list.
ok, out, near = resolve("|default<>0$zzz", sigs("DEFAULT_rgnt_a0"))
check(not ok and near == [], "unrelated reference is refused with no near misses")

# Plain Verilog references are unaffected.
ok, out, near = resolve("memory[0]", sigs("memory[0]"))
check(ok and near == [], "plain Verilog reference resolves as before")

# End to end through check(): an exact section passes...
gold = sigs("rf_ram_if.rgnt", "rf_ram_if.rdata0", reg=True)
gate = sigs("RfRamIf_DEFAULT_rgnt_a0", "RfRamIf_DEFAULT_rdata0_a0", reg=True)
code, out = run_check(gold, gate, ["gold-match rf_ram_if.rgnt /rf_ram_if|default<>0$rgnt",
                                   "gold-match rf_ram_if.rdata0 /rf_ram_if|default<>0$rdata0"])
check(code == 0 and "PASS" in out and "NOTE" not in out, f"exact match section passes, got {code}: {out}")

# ...a unique near miss fails and the report carries both names...
code, out = run_check(gold, gate, ["gold-match rf_ram_if.rgnt /rf_ram_if|default<>0$rgnt",
                                   "gold-match rf_ram_if.rdata0 /rf_ram_if|default<>0$rdata_0"])
check(code == 1, f"unique near miss fails the check, got {code}")
check("RfRamIf_DEFAULT_rdata_0[_a<n>]" in out and "['RfRamIf_DEFAULT_rdata0']" in out,
      f"failure names the expected form and the near miss: {out}")
check("gold register 'rf_ram_if.rdata0'" not in out, "the refused line is still counted as the gold register's match line")

# ...and an ambiguous near miss fails listing every candidate.
gold2 = sigs("u.x", reg=True)
gate2 = sigs("RfRamIf_DEFAULT_x_a0", "RframIf_DEFAULT_x_a0", reg=True)
code, out = run_check(gold2, gate2, ["gold-match u.x /rf_ramif|default<>0$x"])
check(code == 1 and "['RfRamIf_DEFAULT_x', 'RframIf_DEFAULT_x']" in out,
      f"ambiguous near miss fails listing both candidates: {out}")

total = PASSED + FAILED
print(f"{PASSED}/{total} cases passed")
sys.exit(1 if FAILED else 0)
