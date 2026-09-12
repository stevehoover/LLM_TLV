"""Module-directory file access, status.json, and attempt logging."""

import json
import os
import time

from . import config


def snap(name):
    return open(os.path.join(config.MDIR, name)).read() if os.path.exists(os.path.join(config.MDIR, name)) else ""


def set_status_fields(**fields):
    p = os.path.join(config.MDIR, "status.json")
    try:
        d = json.load(open(p))
    except Exception:
        d = {"task": "", "fev.sh": "none", "fev_cnt": 0, "llm": ""}
    d.update(fields)
    with open(p, "w") as f:
        json.dump(d, f, indent=2)


def context_files():
    names = ["wip.tlv", "fev.eqy", "fev_full.eqy", "config.json", "tracker.md"]
    for f in sorted(os.listdir(config.MDIR)):
        if f.startswith("fev_full_") and f.endswith(".eqy"):
            names.append(f)
    return [n for n in names if os.path.exists(os.path.join(config.MDIR, n))]


def snapshot_module():
    snap = {}
    for f in os.listdir(config.MDIR):
        p = os.path.join(config.MDIR, f)
        if os.path.isfile(p):
            try:
                snap[f] = open(p, encoding="utf-8", errors="replace").read()
            except OSError:
                pass
    return snap


def revert():
    body = snap("feved.tlv")
    if body:
        with open(os.path.join(config.MDIR, "wip.tlv"), "w") as f:
            f.write(body)


def log_unparsed(tname, tag, resp):
    with open(os.path.join(config.MDIR, "unparsed_replies.log"), "a") as lf:
        lf.write(f"\n===== {tname} [{tag}] {time.strftime('%H:%M:%S')} =====\n{resp}\n")


# Per-attempt exchange capture (agreed with Steve, meeting Aug 18): every worker
# attempt's full reply plus the feedback it was given, one JSON line each, so
# the Console can show the exact exchange after the fact. Conversations are
# otherwise stateless and unrecoverable.
def log_attempt_exchange(tname, provider, n, feedback_in, reply, cost):
    rec = {"ts": time.strftime("%Y-%m-%d %H:%M:%S"), "task": tname,
           "provider": provider, "attempt": n,
           "feedback_in": feedback_in or "", "reply": reply, "cost_usd": round(cost, 4)}
    with open(os.path.join(config.MDIR, "attempts.jsonl"), "a") as f:
        f.write(json.dumps(rec) + "\n")
