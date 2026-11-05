#!/usr/bin/env python3

# Report which of a module's Verilog parameters the FEV configurations actually vary.
#
# Usage: ./config_coverage.py [--warn-only] <module-dir>
#
# Reads the parameters declared by <module-dir>/orig.sv (name and default), the M5 configurations
# in config.json, and the `chparam -set NAME VALUE` lines of every fev_full*.eqy, and prints, per
# parameter, the values the FEV configurations exercise and whether any of them differs from the
# default. A parameter whose default is computed from other parameters (B = W-1) is reported as
# derived and is never counted as unvaried.
#
# This is advisory: some parameters are legitimately fixed for a conversion. fev.sh runs it with
# --warn-only, which prints only the WARNING lines, and does not fail on it.
#
# Exit status: 0 when every non-derived parameter is varied by at least one configuration (or the
# module has no parameters); 1 when at least one parameter is never changed from its default (the
# WARNING lines name them); 2 when <module-dir> has no orig.sv.

import json
import os
import re
import sys

TYPE_WORDS = ("integer", "int", "logic", "bit", "reg", "wire", "signed", "unsigned", "real", "string",
              "time", "longint", "shortint", "byte")


# Strip // and /* */ comments from Verilog text.
def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


# Scan a parameter default value starting at text[i], up to a top-level ',' ';' or ')'.
# Returns (value, index of the terminator).
def scan_value(text, i):
    depth = 0
    start = i
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                break
            depth -= 1
        elif c in ",;" and depth == 0:
            break
        i += 1
    return text[start:i].strip(), i


# Parse the overridable parameters of orig.sv. Returns an ordered list of (name, default).
# localparam declarations are skipped, since chparam cannot set them.
def parse_parameters(sv_text):
    text = strip_comments(sv_text)
    params = []
    head_re = re.compile(r"(?<![\w$])parameter\b")
    decl_re = re.compile(r"\s*(?:(?:" + "|".join(TYPE_WORDS) + r")\s+)*(?:\[[^\]]*\]\s*)*(\w+)\s*=")
    pos = 0
    while True:
        m = head_re.search(text, pos)
        if not m:
            break
        pos = m.end()
        while True:
            d = decl_re.match(text, pos)
            if not d:
                break
            value, end = scan_value(text, d.end())
            params.append((d.group(1), value))
            pos = end
            # "parameter A = 1, B = 2" continues after a comma unless a keyword follows.
            if end < len(text) and text[end] == "," and \
                    not re.match(r"\s*(parameter|localparam|input|output|inout)\b", text[end + 1:]):
                pos = end + 1
                continue
            break
    return params


# Normalize a parameter value for comparison: strip quotes, evaluate Verilog sized/based
# literals to an int, else return the trimmed text.
def normalize(value):
    v = value.strip()
    if len(v) >= 2 and v[0] == '"' and v[-1] == '"':
        return v[1:-1]
    m = re.fullmatch(r"(\d*)'([sS]?)([bBoOdDhH])([0-9a-fA-F_xXzZ?]+)", v)
    if m:
        base = {"b": 2, "o": 8, "d": 10, "h": 16}[m.group(3).lower()]
        try:
            return int(m.group(4).replace("_", ""), base)
        except ValueError:
            return v
    if re.fullmatch(r"-?\d+", v):
        return int(v)
    return v


# Read the configuration name and chparam settings of one .eqy file.
# Returns (config_name, {param: value}).
def parse_eqy(path):
    name = "default"
    settings = {}
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if s.startswith("#"):
                continue
            m = re.search(r"\bread_verilog\b.*\swip_?(\S*)\.sv", s)
            if m and m.group(1):
                name = m.group(1)
            if s.startswith("chparam"):
                for pm in re.finditer(r"-set\s+(\w+)\s+(\"[^\"]*\"|\S+)", s):
                    settings[pm.group(1)] = pm.group(2)
    return name, settings


def main():
    argv = sys.argv[1:]
    warn_only = "--warn-only" in argv
    argv = [a for a in argv if a != "--warn-only"]
    if len(argv) != 1:
        print("Usage: ./config_coverage.py [--warn-only] <module-dir>")
        return 2
    mdir = argv[0]
    orig = os.path.join(mdir, "orig.sv")
    if not os.path.isfile(orig):
        print(f"WARNING: config coverage: {orig} not found; cannot check parameter coverage.")
        return 2
    with open(orig, "r", encoding="utf-8", errors="replace") as f:
        params = parse_parameters(f.read())
    names = [p for p, _ in params]

    m5_configs = {}
    cfg = os.path.join(mdir, "config.json")
    if os.path.isfile(cfg):
        try:
            with open(cfg) as f:
                m5_configs = json.load(f).get("M5_configs", {}) or {}
        except (OSError, ValueError):
            m5_configs = {}

    # Each configuration is labeled by its file name suffix (fev_full_W_4.eqy is "W_4"); the
    # M5 configuration it reads (wip_<name>.sv) is shown alongside when there is one.
    eqys = []
    for fn in sorted(os.listdir(mdir)):
        m = re.fullmatch(r"fev_full_?(.*)\.eqy", fn)
        if m:
            label = m.group(1) or "default"
            m5name, settings = parse_eqy(os.path.join(mdir, fn))
            if m5name != "default" and m5name != label:
                label = f"{label}, M5 {m5name}"
            eqys.append((fn, label, settings))

    rows = []
    unvaried = []
    for name, default in params:
        derived = sorted(o for o in names if o != name and re.search(r"(?<![\w$])" + re.escape(o) + r"(?![\w])", default))
        seen = []
        varied = False
        for fn, cname, settings in eqys:
            if name in settings:
                seen.append(f"{settings[name]} ({cname})")
                if normalize(settings[name]) != normalize(default):
                    varied = True
        if derived:
            status = "derived from " + ", ".join(derived)
        elif varied:
            status = "yes"
        else:
            status = "NO"
            unvaried.append((name, default))
        rows.append((name, default, ", ".join(seen) if seen else "(never set)", status))

    if not warn_only:
        top = os.path.basename(os.path.abspath(mdir))
        print(f"Parameter coverage for {top}: orig.sv parameters vs. chparam in fev_full*.eqy")
        if m5_configs:
            for k, v in m5_configs.items():
                print(f"  M5 config {k}: {v}")
        if not params:
            print("  orig.sv declares no parameters.")
        else:
            w0 = max(len("parameter"), max(len(r[0]) for r in rows))
            w1 = max(len("default"), max(len(r[1]) for r in rows))
            w2 = max(len("values exercised"), max(len(r[2]) for r in rows))
            print(f"  {'parameter':<{w0}}  {'default':<{w1}}  {'values exercised':<{w2}}  varied")
            for r in rows:
                print(f"  {r[0]:<{w0}}  {r[1]:<{w1}}  {r[2]:<{w2}}  {r[3]}")
        print(f"  FEV configurations: " + (", ".join(f"{fn} [{cname}]" for fn, cname, _ in eqys) or "none"))
    for name, default in unvaried:
        print(f"WARNING: config coverage: parameter {name} (default {default}) is never changed from its default by "
              f"any FEV configuration (no fev_full*.eqy sets it with chparam). If {name} is meant to stay fixed, say "
              f"so in tracker.md; otherwise add a fev_full_<config>.eqy with \"chparam -set {name} <value>\".")
    return 1 if unvaried else 0


if __name__ == "__main__":
    sys.exit(main())
