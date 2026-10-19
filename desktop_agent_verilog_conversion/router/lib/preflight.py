"""Preflight (audit Aug 25): fail fast with clear messages instead of
burning retries or paid calls against a broken environment."""

import os
import subprocess
import sys

from . import config
from .config import AGENT_CMD, DOCKER_IMAGE, JUDGE_ON, PROVIDERS
from .fev import run_in_module

FEV_TOOLS = ("sandpiper-saas", "eqy", "sby", "yosys", "jq")
LINK_TARGET = "/home/steve/repos/LLM_TLV/desktop_agent_verilog_conversion/scripts"


def container_check():
    cmd = ("[ -f ./scripts/fev.sh ] && [ -x ./scripts/fev.sh ] || echo MISSING:fev.sh; "
           "for t in " + " ".join(FEV_TOOLS) + "; do command -v $t >/dev/null || echo MISSING:$t; done; "
           "echo CHECK_DONE")
    out = run_in_module(cmd, timeout=60)
    if "CHECK_DONE" not in out:
        return [f"container check in {DOCKER_IMAGE} did not run: {out.strip()[-500:]}"]
    errs = []
    for line in out.splitlines():
        if line == "MISSING:fev.sh":
            errs.append(f"scripts/fev.sh does not resolve inside the container (the scripts link in {config.MDIR} "
                        f"probably points to a host path or one level too high; point it at the LLM_TLV mount, {LINK_TARGET})")
        elif line.startswith("MISSING:"):
            errs.append(f"{line[8:]} not found inside {DOCKER_IMAGE}")
    return errs


def preflight():
    errs = []
    used = {p for p, _ in PROVIDERS}
    keyfiles = {"deepseek": os.path.expanduser(os.environ.get("MM_DEEPSEEK_KEY_FILE", "~/.secrets/deepseek_key"))}
    if JUDGE_ON or "claude" in used:
        keyfiles["claude"] = os.path.expanduser(os.environ.get("MM_ANTHROPIC_KEY_FILE", "~/.secrets/anthropic_key"))
    for prov, kf in keyfiles.items():
        if prov in used or (prov == "claude" and JUDGE_ON):
            if not os.path.isfile(kf):
                errs.append(f"API key file for {prov} not found: {kf}")
    host_ok = os.path.isfile(os.path.join(config.MDIR, "scripts", "fev.sh")) or os.path.islink(os.path.join(config.MDIR, "scripts"))
    if not host_ok:
        errs.append(f"no scripts/fev.sh under {config.MDIR} (is this a conversion work dir?)")
    try:
        r = subprocess.run(["docker", "image", "inspect", DOCKER_IMAGE],
                           capture_output=True, text=True, timeout=30)
        if r.returncode != 0:
            errs.append(f"docker image {DOCKER_IMAGE} not found "
                        "(build it from desktop_agent_verilog_conversion/conversion_setup/env/Dockerfile.fev)")
        else:
            errs += [e for e in container_check() if host_ok or "scripts/fev.sh" not in e]
    except FileNotFoundError:
        errs.append("docker not found on PATH")
    except Exception as e:
        errs.append(f"docker preflight failed: {e}")
    if "agent" in used:
        try:
            subprocess.run([AGENT_CMD, "--version"], capture_output=True, timeout=30)
        except FileNotFoundError:
            errs.append(f"agent worker command not found: {AGENT_CMD} (install Claude Code)")
    if errs:
        sys.exit("PREFLIGHT FAILED:\n  - " + "\n  - ".join(errs))
