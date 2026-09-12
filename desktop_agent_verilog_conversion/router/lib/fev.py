"""Formal equivalence checking: docker invocation of the shared fev.sh
harness, plus feedback enrichment from SandPiper-generated Verilog."""

import os
import re
import subprocess

from . import config


def run_in_module(cmd, timeout=3600):
    argv = ["docker", "run", "--rm"]
    if config.DOCKER_USER:
        argv += ["-u", config.DOCKER_USER]
    argv += ["-v", config.SERV_DIR + ":/workspace/proj:rw",
        "-v", config.LLMTLV_DIR + ":/home/steve/repos/LLM_TLV:ro",
        "-v", config.TOOLSHIM_DIR + ":/toolshim:ro",
        "-w", "/workspace/proj/tlv/" + os.path.basename(config.MDIR),
        "--entrypoint", "bash", config.DOCKER_IMAGE, "-lc",
        "export PATH=/toolshim:/opt/oss-cad-suite/bin:$PATH; " + cmd]
    r = subprocess.run(argv, capture_output=True, text=True, timeout=timeout)
    return r.stdout + r.stderr


def run_fev():
    out = run_in_module("./scripts/fev.sh 2>&1")
    return "All FEV runs successful" in out, out


def enrich_feedback(out):
    m = re.search(r"wip\.sv:(\d+): ERROR", out)
    p = os.path.join(config.MDIR, "wip.sv")
    if m and os.path.exists(p):
        ln = int(m.group(1))
        lines = open(p).read().splitlines()
        lo, hi = max(0, ln - 8), min(len(lines), ln + 8)
        excerpt = "\n".join(f"{i+1}: {lines[i]}" for i in range(lo, hi))
        out += ("\n\n# The Verilog that SandPiper GENERATED from your wip.tlv, around the error line:\n"
                + excerpt +
                "\n\nCompare this generated Verilog against your TLV source to see how your TLV was interpreted.")
    return out
