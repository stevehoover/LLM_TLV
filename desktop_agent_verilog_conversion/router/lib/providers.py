"""Worker invocation: the deepseek and claude API calls (with prompt caching
and network retry) and the Claude Code agent worker subprocess."""

import json
import os
import subprocess
import time
import urllib.request

from . import config
from .prompts import AGENT_PREAMBLE, SYSTEM


def call_with_retry(provider, user, tries=8, system=None):
    for k in range(tries):
        try:
            return call(provider, user, system=system)
        except Exception as e:
            wait = min(60, 15 * (k + 1))
            print(f"    (network error {type(e).__name__}, retry {k+1}/{tries} in {wait}s)", flush=True)
            time.sleep(wait)
    raise RuntimeError("network retries exhausted")


def call(provider, user, system=None):
    # user is (common, stable, fb) from build_user, (stable, fb) from the
    # judge path, or a bare string. Common goes first so both providers can
    # cache the cross-task prefix.
    if isinstance(user, tuple):
        common, stable, fb = user if len(user) == 3 else ("", user[0], user[1])
    else:
        common, stable, fb = "", user, ""
    system = system or SYSTEM
    if provider == "deepseek":
        key = open(os.path.expanduser(os.environ.get("MM_DEEPSEEK_KEY_FILE", "~/.secrets/deepseek_key"))).read().strip()
        req = urllib.request.Request("https://api.deepseek.com/chat/completions",
            data=json.dumps({"model": config.MODEL_NAME["deepseek"],
                "messages": [{"role": "system", "content": system}, {"role": "user", "content": common + stable + fb}],
                "max_tokens": 16000, "temperature": 0.2}).encode(),
            headers={"Content-Type": "application/json",
                     "Authorization": "Bearer " + key})
        d = json.load(urllib.request.urlopen(req, timeout=300))
        u = d.get("usage", {})
        usage = {"in": u.get("prompt_cache_miss_tokens", u.get("prompt_tokens", 0)),
                 "out": u.get("completion_tokens", 0),
                 "cache_read": u.get("prompt_cache_hit_tokens", 0),
                 "cache_write": 0}
        msg = d["choices"][0]["message"]
        content = msg.get("content") or ""
        if not content:
            # deepseek v4 can burn its whole budget on reasoning -> empty content
            print(f"    (deepseek empty content, finish_reason={d['choices'][0].get('finish_reason')})", flush=True)
            content = msg.get("reasoning_content") or ""
        return content, usage
    else:
        key = open(os.path.expanduser(os.environ.get("MM_ANTHROPIC_KEY_FILE", "~/.secrets/anthropic_key"))).read().strip()
        content = []
        if common:
            content.append({"type": "text", "text": common, "cache_control": {"type": "ephemeral"}})
        content.append({"type": "text", "text": stable, "cache_control": {"type": "ephemeral"}})
        if fb:
            content.append({"type": "text", "text": fb})
        req = urllib.request.Request("https://api.anthropic.com/v1/messages",
            data=json.dumps({"model": config.MODEL_NAME["claude"], "max_tokens": 8000, "system": system,
                "messages": [{"role": "user", "content": content}]}).encode(),
            headers={"Content-Type": "application/json", "x-api-key": key,
                     "anthropic-version": "2023-06-01"})
        d = json.load(urllib.request.urlopen(req, timeout=300))
        u = d.get("usage", {})
        usage = {"in": u.get("input_tokens", 0), "out": u.get("output_tokens", 0),
                 "cache_read": u.get("cache_read_input_tokens", 0),
                 "cache_write": u.get("cache_creation_input_tokens", 0)}
        return d["content"][0]["text"], usage


def run_agent_worker(task_text, feedback):
    prompt = AGENT_PREAMBLE + "# Task\n\n" + task_text + "\n"
    if feedback:
        prompt += ("\n# Previous attempt FAILED verification. Tool output:\n\n"
                   + feedback[-3000:] + "\n\nFix the problem by editing the files.\n")
    env = dict(os.environ)
    env.pop("ANTHROPIC_API_KEY", None)
    argv = [config.AGENT_CMD, "-p", "--model", config.AGENT_MODEL,
            "--max-turns", str(config.AGENT_MAX_TURNS),
            "--permission-mode", "acceptEdits",
            "--allowedTools", "Read,Edit,Write,Grep,Glob"]
    t_start = time.time()
    try:
        r = subprocess.run(argv, input=prompt, capture_output=True, text=True,
                           timeout=config.AGENT_TIMEOUT, cwd=config.MDIR, env=env)
        report = (r.stdout or "") + (("\n[stderr] " + r.stderr) if r.returncode != 0 and r.stderr else "")
    except subprocess.TimeoutExpired:
        report = f"[agent timed out after {config.AGENT_TIMEOUT}s]"
    return report.strip(), time.time() - t_start
