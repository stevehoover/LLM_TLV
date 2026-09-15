#!/usr/bin/env python3
"""Hierarchy combining plan: the design-level pre-step run once before any
module conversion. Surveys every Verilog module in a design, proposes a
per-module combining strategy, takes the user's feedback, and persists the
plan as collateral (combining_plan.json + combining_plan.md) that the
combining tasks consult.

Strategies:
  module - stays a real module (the conversion target, or a synthesis block)
  macro  - becomes a TLV macro, included at each instantiation site
  inline - single-use structural module, inlined as a TLV scope /<name>

Mechanical facts (instantiation counts, parameter differences across sites)
set the defaults; an optional LLM pass adds a generic-vs-structural judgment
per module and may upgrade an inline to a macro; the user overrides anything
interactively. Non-interactive runs (EOF / no tty) accept the defaults.

Usage:
  python3 plan.py <design_dir> [top_module] [--no-llm] [--out <dir>]
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

STRATEGIES = ("module", "macro", "inline")


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def skip_parens(text, i):
    depth = 0
    while i < len(text):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return i


def find_instances(body, names):
    found = []
    for name in names:
        for m in re.finditer(r"\b%s\b" % re.escape(name), body):
            i, params = m.end(), ""
            while i < len(body) and body[i].isspace():
                i += 1
            if i < len(body) and body[i] == "#":
                i += 1
                while i < len(body) and body[i].isspace():
                    i += 1
                if i >= len(body) or body[i] != "(":
                    continue
                j = skip_parens(body, i)
                params = " ".join(body[i:j].split())
                i = j
                while i < len(body) and body[i].isspace():
                    i += 1
            inst = re.match(r"[A-Za-z_]\w*", body[i:])
            if not inst:
                continue
            i += inst.end()
            while i < len(body) and body[i].isspace():
                i += 1
            if i < len(body) and body[i] == "[":
                j = body.find("]", i)
                if j < 0:
                    continue
                i = j + 1
                while i < len(body) and body[i].isspace():
                    i += 1
            if i < len(body) and body[i] == "(":
                found.append((name, params))
    return found


def survey(design_dir):
    files = []
    for root, _, fnames in os.walk(design_dir):
        files += [os.path.join(root, f) for f in sorted(fnames)
                  if f.endswith((".v", ".sv")) and not f.startswith("wip")]
    modules = {}
    for path in sorted(files):
        text = strip_comments(open(path).read())
        for m in re.finditer(r"\bmodule\s+([A-Za-z_]\w*)(.*?)\bendmodule\b", text, re.S):
            name, body = m.group(1), m.group(2)
            modules[name] = {
                "file": os.path.relpath(path, design_dir),
                "lines": body.count("\n") + 1,
                "params": re.findall(r"\bparameter\b[^=,;()]*?([A-Za-z_]\w*)\s*=", body),
                "body": body,
            }
    edges, sites = {}, {}
    for name, info in modules.items():
        for child, params in find_instances(info["body"], [n for n in modules if n != name]):
            edges.setdefault(name, []).append(child)
            sites.setdefault(child, []).append(params)
    counts = {name: len(sites.get(name, [])) for name in modules}
    return modules, edges, counts, sites


def reachable(edges, root):
    seen, todo = set(), [root]
    while todo:
        n = todo.pop()
        if n not in seen:
            seen.add(n)
            todo += edges.get(n, [])
    return seen


def pick_top(modules, edges, counts):
    roots = [n for n in modules if counts[n] == 0] or list(modules)
    return max(sorted(roots), key=lambda n: len(reachable(edges, n)))


def propose(modules, counts, sites, top):
    plan = {"top": top, "modules": {}, "synthesis_boundaries": []}
    for name in sorted(modules):
        n = counts[name]
        if name == top:
            strategy, reason = "module", "conversion target (top)"
        elif n == 0:
            strategy, reason = "module", "not instantiated (separate root); kept a module"
        elif n >= 2 and len(set(sites[name])) > 1:
            strategy, reason = "macro", f"instantiated {n} times with differing parameters; macro with config knobs"
        elif n >= 2:
            strategy, reason = "macro", f"instantiated {n} times; shared macro"
        else:
            strategy, reason = "inline", f"single use; inline as TLV scope /{name}"
        plan["modules"][name] = {"strategy": strategy, "instantiations": n,
                                 "reason": reason, "user_override": False}
    return plan


def llm_annotate(plan, modules):
    from lib import providers
    keyfiles = {"deepseek": os.path.expanduser(os.environ.get("MM_DEEPSEEK_KEY_FILE", "~/.secrets/deepseek_key")),
                "claude": os.path.expanduser(os.environ.get("MM_ANTHROPIC_KEY_FILE", "~/.secrets/anthropic_key"))}
    system = ("You are a hardware design analyst. For each Verilog module listed, judge in one "
              "line whether it is a GENERIC reusable component (a RAM, FIFO, arbiter - worth "
              "keeping as a reusable macro) or STRUCTURAL organization of this one design "
              "(worth inlining). Reply with exactly one line per module, format:\n"
              "<module>|generic or structural|<one-line reason>|keep or macro\n"
              "'macro' in the last field means the module is generic enough that it should "
              "be a macro even if instantiated only once; otherwise 'keep'.")
    prompt = "Design survey:\n"
    for name, e in plan["modules"].items():
        info = modules[name]
        head = "\n".join(info["body"].splitlines()[:40])
        prompt += (f"\n== {name} (file {info['file']}, {info['lines']} lines, "
                   f"instantiated {e['instantiations']}x, params {info['params'] or 'none'}, "
                   f"proposed {e['strategy']}) ==\n{head}\n")
    reply = None
    for prov in ("deepseek", "claude"):
        if not os.path.exists(keyfiles[prov]):
            continue
        try:
            reply, _ = providers.call_with_retry(prov, prompt, tries=2, system=system)
            break
        except Exception as e:
            print(f"  ({prov} LLM pass failed: {e})")
    if not reply:
        print("  (no LLM provider available; mechanical proposal only)")
        return
    for line in reply.splitlines():
        parts = [p.strip() for p in line.split("|")]
        if len(parts) != 4 or parts[0] not in plan["modules"]:
            continue
        e = plan["modules"][parts[0]]
        e["reason"] += f" | LLM: {parts[1]} - {parts[2]}"
        if parts[3] == "macro" and e["strategy"] == "inline":
            e["strategy"] = "macro"
            e["reason"] += " (upgraded inline -> macro)"


def table(plan):
    rows = [("module", "inst", "lines", "strategy", "reason")]
    for name, e in plan["modules"].items():
        rows.append((name, str(e["instantiations"]), str(e["lines"]),
                     e["strategy"] + (" *" if e["user_override"] else ""), e["reason"]))
    w = [max(len(r[i]) for r in rows) for i in range(4)]
    return "\n".join("  ".join(c.ljust(w[i]) for i, c in enumerate(r[:4])) + "  " + r[4]
                     for r in rows)


def interact(plan):
    if not sys.stdin.isatty():
        print("\n(non-interactive: defaults accepted)")
        return
    print("\nAccept with an empty line. Override with <module>=module|macro|inline."
          "\nMark synthesis-boundary modules with: synth <module> [<module>...]"
          "\n(none is the right default for small designs).")
    while True:
        try:
            line = input("plan> ").strip()
        except EOFError:
            break
        if line in ("", "accept", "y"):
            break
        if line.startswith("synth"):
            for name in line.split()[1:]:
                if name in plan["modules"]:
                    plan["synthesis_boundaries"].append(name)
                    plan["modules"][name].update(strategy="module", user_override=True,
                                                 reason="synthesis boundary (user)")
                else:
                    print(f"  no module named {name}")
            continue
        m = re.match(r"(\w+)\s*=\s*(\w+)$", line)
        if m and m.group(1) in plan["modules"] and m.group(2) in STRATEGIES:
            plan["modules"][m.group(1)].update(strategy=m.group(2), user_override=True)
            plan["modules"][m.group(1)]["reason"] += " (user override)"
        else:
            print("  ? use <module>=module|macro|inline, 'synth <module>', or empty line to accept")
    print("\n" + table(plan))


def write_outputs(plan, out_dir):
    for e in plan["modules"].values():
        e.pop("lines", None)
    with open(os.path.join(out_dir, "combining_plan.json"), "w") as f:
        json.dump(plan, f, indent=2)
        f.write("\n")
    md = [f"# Hierarchy combining plan", "", f"Top module: `{plan['top']}`", "",
          "| module | instantiations | strategy | reason |", "|---|---|---|---|"]
    for name, e in plan["modules"].items():
        star = " **(user override)**" if e["user_override"] else ""
        md.append(f"| {name} | {e['instantiations']} | {e['strategy']}{star} | {e['reason']} |")
    md += ["", "Synthesis boundaries: " +
           (", ".join(plan["synthesis_boundaries"]) or "none"), ""]
    with open(os.path.join(out_dir, "combining_plan.md"), "w") as f:
        f.write("\n".join(md))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("design_dir")
    ap.add_argument("top_module", nargs="?")
    ap.add_argument("--no-llm", action="store_true")
    ap.add_argument("--out")
    args = ap.parse_args()
    modules, edges, counts, sites = survey(args.design_dir)
    if not modules:
        sys.exit(f"no Verilog modules found under {args.design_dir}")
    top = args.top_module or pick_top(modules, edges, counts)
    if top not in modules:
        sys.exit(f"top module {top} not found; defined: {', '.join(sorted(modules))}")
    plan = propose(modules, counts, sites, top)
    for name, e in plan["modules"].items():
        e["lines"] = modules[name]["lines"]
    if not args.no_llm:
        llm_annotate(plan, modules)
    print(f"Design: {args.design_dir}  top: {top}  "
          f"({len(modules)} modules)\n\n" + table(plan))
    interact(plan)
    out_dir = args.out or args.design_dir
    os.makedirs(out_dir, exist_ok=True)
    write_outputs(plan, out_dir)
    print(f"\nwrote {os.path.join(out_dir, 'combining_plan.json')} and combining_plan.md")


if __name__ == "__main__":
    main()
