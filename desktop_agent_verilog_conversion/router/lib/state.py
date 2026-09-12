"""Resume state: completed tasks and the in-flight attempt budget live in
<module_dir>/e6_state.json, so rerunning the router continues where it
stopped."""

import json
import os

STATE = None


def load(mdir):
    global STATE
    STATE = os.path.join(mdir, "e6_state.json")
    _raw_state = json.load(open(STATE)) if os.path.exists(STATE) else {}
    if "done" in _raw_state:
        done_tasks = _raw_state["done"]
        inflight = _raw_state.get("inflight") or {}
    else:
        done_tasks = _raw_state
        inflight = {}
    return done_tasks, inflight


def save(done_tasks, inflight):
    json.dump({"done": done_tasks, "inflight": inflight}, open(STATE, "w"), indent=1)
