"""Preflight (audit Aug 25): fail fast with clear messages instead of
burning retries or paid calls against a broken environment."""

import os
import subprocess
import sys

from . import config
from .config import AGENT_CMD, DOCKER_IMAGE, JUDGE_ON, PROVIDERS


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
    if not os.path.isfile(os.path.join(config.MDIR, "scripts", "fev.sh")) and not os.path.islink(os.path.join(config.MDIR, "scripts")):
        errs.append(f"no scripts/fev.sh under {config.MDIR} (is this a conversion work dir?)")
    try:
        r = subprocess.run(["docker", "image", "inspect", DOCKER_IMAGE],
                           capture_output=True, text=True, timeout=30)
        if r.returncode != 0:
            errs.append(f"docker image {DOCKER_IMAGE} not found "
                        "(build it from desktop_agent_verilog_conversion/conversion_setup/env/Dockerfile.fev)")
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
