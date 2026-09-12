"""Cost and cache-usage tracking, per-provider spend caps, run summary."""

import sys
import time

from .config import MAX_COST

cost = {"deepseek": 0.0, "claude": 0.0}
cache_totals = {"read": 0, "write": 0, "in": 0}


def track(provider, u):
    # Cache pricing per the official price sheets: anthropic cache write is
    # 1.25x input and cache read 0.1x input; deepseek cache hit ~0.1x miss.
    if provider == "deepseek":
        c = (u["in"]*0.14 + u["cache_read"]*0.014 + u["out"]*0.28)/1e6
    else:
        c = (u["in"]*3.0 + u["cache_write"]*3.75 + u["cache_read"]*0.30 + u["out"]*15.0)/1e6
    cost[provider] += c
    cache_totals["read"] += u["cache_read"]
    cache_totals["write"] += u["cache_write"]
    cache_totals["in"] += u["in"]
    if cost[provider] > MAX_COST[provider]:
        print(f"!!! COST CAP: {provider} ${cost[provider]:.2f} > ${MAX_COST[provider]:.2f}, stopping safely")
        print_summary()
        sys.exit(2)
    return c


def cache_str(u):
    return f"cache r{u['cache_read']}/w{u['cache_write']}/u{u['in']}"


stats = []
t0 = time.time()
agent_wall = [0.0]


def print_summary():
    print("\n===== RUN SUMMARY =====")
    for t, u in stats:
        print(f"  {u:36} {t}")
    print(f"cost: deepseek ${cost['deepseek']:.4f} + claude ${cost['claude']:.4f} = ${cost['deepseek']+cost['claude']:.4f}")
    tot = cache_totals["read"] + cache_totals["in"]
    pct = 100.0 * cache_totals["read"] / tot if tot else 0.0
    print(f"cache: read {cache_totals['read']} / write {cache_totals['write']} / uncached {cache_totals['in']} (hit {pct:.0f}%)")
    print(f"wall clock: {(time.time()-t0)/60:.1f} min")
    if agent_wall[0]:
        print(f"agent worker wall: {agent_wall[0]/60:.1f} min (subscription, no API cost)")
