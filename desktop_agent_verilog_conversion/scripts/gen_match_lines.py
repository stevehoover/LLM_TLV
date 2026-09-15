#!/usr/bin/env python3

# Mechanical enumeration and cross-check of fev*.eqy match lines.
#
# Usage: ./gen_match_lines.py --emit <fev*.eqy>
#        ./gen_match_lines.py --check <fev*.eqy>
# Run from the module work directory (alongside wip.tlv, prepared.sv, config.json).
#
# Both modes replay the .eqy file's [gold]/[gate] read commands and [script]
# transforms through yosys (the same view eqy matches on) and enumerate the
# named wires and registers on each side. Name-identical pairs need no match
# line.
#
# --emit prints a proposed [match] section: gold-only names are paired to
#   gate-only names by a conservative base-name heuristic where the pairing
#   is unambiguous, and listed as UNRESOLVED otherwise.
#
# --check compares the match lines present in the .eqy file against the
#   enumeration and exits 1 listing every disagreement:
#   - match lines whose gold name does not exist in the gold enumeration
#   - gate references (TL-Verilog or Verilog syntax) that map to no signal
#     in the gate enumeration
#   - gold registers with no name-identical gate partner and no match line
#     (state that would make FEV fail or pass vacuously)
#   Exit 2 means the check itself could not run (missing tool, elaboration
#   failure); callers should treat that as "no verdict", not as disagreement.
#
# The gate side is regenerated from wip.tlv with sandpiper-saas (mirroring
# fev.sh) into a temporary directory so the check reflects the current
# source. When sandpiper-saas is unavailable, the on-disk generated Verilog
# is used as-is.

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

DFF_TYPES = re.compile(r'^\$(dff|dffe|adff|adffe|aldff|aldffe|sdff|sdffe|sdffce|dffsr|dffsre|dlatch|adlatch|dlatchsr|ff)$')


def parse_eqy(path):
    sections = {"gold": [], "gate": [], "script": [], "match": []}
    cur = None
    for raw in open(path):
        s = raw.strip()
        if s.startswith('['):
            cur = re.match(r'\[(\w+)', s).group(1)
            continue
        if not s or s.startswith('#'):
            continue
        if cur in sections:
            sections[cur].append(s)
    return sections


def top_module(script):
    for s in script:
        m = re.search(r'hierarchy\s.*-top\s+(\S+)', s)
        if m:
            return m.group(1)
    print("ERROR: no 'hierarchy -top <top>' command in the [script] section.")
    sys.exit(2)


def m5_config_args(suffix):
    try:
        with open('config.json') as f:
            config_json = json.load(f)
    except Exception:
        return ""
    M5_configs = config_json.get('M5_configs', {})
    if not suffix:
        suffix = config_json.get('default_config', "")
    if suffix == "":
        return ""
    args = M5_configs.get(suffix)
    if args is None:
        print(f"ERROR: M5 configuration '{suffix}' not found in config.json's M5_configs.")
        sys.exit(2)
    return args


def regen_gate(gate_lines, tmpdir):
    for i, s in enumerate(gate_lines):
        m = re.search(r'read_verilog.*\s(wip_?(\S*)\.sv)\b', s)
        if not m:
            continue
        sv_name, suffix = m.group(1), m.group(2)
        if shutil.which("sandpiper-saas") is None:
            if os.path.exists(sv_name):
                print(f"NOTE: sandpiper-saas not available; using on-disk {sv_name}.")
                return gate_lines
            print(f"ERROR: sandpiper-saas not available and {sv_name} does not exist.")
            sys.exit(2)
        out_path = os.path.join(tmpdir, sv_name)
        cmd = ["sandpiper-saas", "-i", "wip.tlv", "-o", sv_name, "--outdir", tmpdir,
               "--inlineGen", "--noline", "--iArgs"] + m5_config_args(suffix).split()
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0 and not os.path.exists(out_path):
            time.sleep(15)
            r = subprocess.run(cmd, capture_output=True, text=True)
        if not os.path.exists(out_path):
            if r.returncode == 0:
                shutil.copy("wip.tlv", out_path)
            else:
                print(f"ERROR: SandPiper failed regenerating {sv_name} from wip.tlv:")
                print(r.stdout + r.stderr)
                sys.exit(2)
        return gate_lines[:i] + [s.replace(sv_name, out_path)] + gate_lines[i + 1:]
    return gate_lines


def enumerate_side(read_lines, script, tag, tmpdir):
    if shutil.which("yosys") is None:
        print("ERROR: yosys not found in PATH.")
        sys.exit(2)
    json_path = os.path.join(tmpdir, tag + ".json")
    ys_path = os.path.join(tmpdir, tag + ".ys")
    with open(ys_path, "w") as f:
        f.write("\n".join(read_lines + script + ["write_json " + json_path]) + "\n")
    r = subprocess.run(["yosys", "-q", "-s", ys_path], capture_output=True, text=True)
    if r.returncode != 0:
        print(f"ERROR: yosys failed elaborating the {tag} side:")
        print(r.stdout + r.stderr)
        sys.exit(2)
    with open(json_path) as f:
        return json.load(f)


def side_signals(design, top, tag):
    mod = design.get("modules", {}).get(top)
    if mod is None:
        print(f"ERROR: module '{top}' not found on the {tag} side after elaboration.")
        sys.exit(2)
    reg_bits = set()
    for cell in mod.get("cells", {}).values():
        if DFF_TYPES.match(cell.get("type", "")):
            for b in cell.get("connections", {}).get("Q", []):
                if isinstance(b, int):
                    reg_bits.add(b)
    ports = set(mod.get("ports", {}))
    sigs = {}
    for name, net in mod.get("netnames", {}).items():
        if net.get("hide_name") or name.startswith("$"):
            continue
        bits = [b for b in net.get("bits", []) if isinstance(b, int)]
        sigs[name] = {"bits": bits,
                      "regbits": [b for b in bits if b in reg_bits],
                      "reg": any(b in reg_bits for b in bits),
                      "port": name in ports}
    return sigs


def tlv_stem(ref):
    if not re.search(r'[|$]', ref):
        return None
    toks = re.findall(r'([|/$])([A-Za-z_][A-Za-z0-9_]*)', ref)
    if not toks or toks[-1][0] != '$':
        return None
    return "_".join(t[1] for t in toks)


def gate_ref_exists(ref, gate_sigs):
    stem = tlv_stem(ref)
    if stem is None:
        return ref.lstrip('*') in gate_sigs
    rx = re.compile(re.escape(stem) + r"(_[an]\d+)?$", re.IGNORECASE)
    return any(rx.fullmatch(n) for n in gate_sigs)


def gate_base(name):
    parts = re.sub(r'_[an]\d+$', '', name).split('_')
    while len(parts) > 1 and parts[0].isupper():
        parts.pop(0)
    return "_".join(parts)


def match_pairs(match_lines):
    pairs = []
    for s in match_lines:
        parts = s.split(None, 2)
        if len(parts) == 3 and parts[0] == "gold-match":
            pairs.append((parts[1], parts[2].strip()))
    return pairs


def emit(top, gold_sigs, gate_sigs):
    gold_only = sorted(n for n, v in gold_sigs.items() if not v["port"] and n not in gate_sigs)
    gate_only = sorted(n for n, v in gate_sigs.items() if not v["port"] and n not in gold_sigs)
    by_base = {}
    for n in gate_only:
        by_base.setdefault(gate_base(n), []).append(n)
    gold_base_count = {}
    for n in gold_only:
        b = n.rsplit(".", 1)[-1]
        gold_base_count[b] = gold_base_count.get(b, 0) + 1
    print(f"[match {top}]")
    unresolved = []
    for n in gold_only:
        b = n.rsplit(".", 1)[-1]
        cands = by_base.get(b, [])
        if len(cands) > 1:
            aligned = [c for c in cands if re.search(r'_a\d+$', c)]
            if len(aligned) == 1:
                cands = aligned
        if len(cands) == 1 and gold_base_count[b] == 1:
            print(f"gold-match {n} {cands[0]}")
        else:
            unresolved.append(n)
    if unresolved:
        print()
        print("# UNRESOLVED (no unique gate candidate; resolve by hand):")
        for n in unresolved:
            print(f"#   {n}")


def check(eqy_file, gold_sigs, gate_sigs, match_lines):
    pairs = match_pairs(match_lines)
    matched_gold = {g for g, _ in pairs}
    problems = []
    for g, gate_ref in pairs:
        if g not in gold_sigs:
            problems.append(f"gold name not in the gold design: 'gold-match {g} {gate_ref}'")
        if not gate_ref_exists(gate_ref, gate_sigs):
            stem = tlv_stem(gate_ref)
            hint = f" (no gate signal matches '{stem}[_a<n>]')" if stem else ""
            problems.append(f"gate reference maps to no gate signal: 'gold-match {g} {gate_ref}'{hint}")
    covered = set()
    for n, v in gold_sigs.items():
        if v["port"] or n in gate_sigs or n in matched_gold:
            covered.update(v["bits"])
    for n, v in sorted(gold_sigs.items()):
        if v["port"] or n in gate_sigs or n in matched_gold:
            continue
        if v["reg"] and any(b not in covered for b in v["regbits"]):
            problems.append(f"gold register '{n}' has no name-identical gate partner and no match line")
    if problems:
        print(f"MATCH CROSS-CHECK FAILED for {eqy_file} ({len(problems)} problem(s)):")
        for p in problems:
            print(f"  - {p}")
        print("The match section disagrees with the mechanical enumeration of the two designs.")
        print("Fix the match lines (or the design) before FEV is run.")
        sys.exit(1)
    print(f"match cross-check PASS: {eqy_file} "
          f"({len(pairs)} match lines, {len(gold_sigs)} gold signals, {len(gate_sigs)} gate signals)")


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in ("--emit", "--check"):
        print("Usage: ./gen_match_lines.py (--emit|--check) <fev*.eqy>")
        sys.exit(1)
    mode, eqy_file = sys.argv[1], sys.argv[2]
    if not os.path.isfile(eqy_file):
        print(f"ERROR: {eqy_file} not found.")
        sys.exit(2)
    sections = parse_eqy(eqy_file)
    top = top_module(sections["script"])
    with tempfile.TemporaryDirectory() as tmpdir:
        gate_lines = regen_gate(sections["gate"], tmpdir)
        gold_sigs = side_signals(enumerate_side(sections["gold"], sections["script"], "gold", tmpdir), top, "gold")
        gate_sigs = side_signals(enumerate_side(gate_lines, sections["script"], "gate", tmpdir), top, "gate")
    if mode == "--emit":
        emit(top, gold_sigs, gate_sigs)
    else:
        check(eqy_file, gold_sigs, gate_sigs, sections["match"])


if __name__ == "__main__":
    main()
