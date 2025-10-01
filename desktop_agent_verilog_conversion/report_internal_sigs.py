#!/usr/bin/env python3

# Usage: python3 report_internal_sigs.py <eqy_output_directory>

import json, sys, os
from pathlib import Path

def load_json(path: str):
    with open(path, "r") as f:
        return json.load(f)

def get_internal(d: dict, keys: list[str]) -> dict:
    for k in keys:
        v = d.get(k)
        if isinstance(v, dict):
            internal = v.get("internal", {})
            if isinstance(internal, dict):
                return internal
    return {}

def report_partition_internal_signals(partition_json_path: str, signal_name: str):
    """Report internal signals for a given partition JSON file"""
    try:
        obj = load_json(partition_json_path)
        gold_internal = get_internal(obj, ["gold_module", "gold_model"])
        gate_internal = get_internal(obj, ["gate_module", "gate_model"])

        print(f"\n=== Internal signals for {signal_name} ===")
        print("Gold internal:")
        for name in sorted(gold_internal.keys()):
            print(f"  {name}")

        print("\nGate internal:")
        for name in sorted(gate_internal.keys()):
            print(f"  {name}")
        print()
    except Exception as e:
        print(f"Error processing {partition_json_path}: {e}", file=sys.stderr)

def main():
    if len(sys.argv) != 2 or sys.argv[1] in ["-h", "--help"]:
        print(f"usage: {sys.argv[0]} <eqy_output_directory>", file=sys.stderr)
        print("", file=sys.stderr)
        print("Reports internal signals for any EQY strategies that did not PASS.", file=sys.stderr)
        print("Scans strategies/*/sby_seq/status files and reports internal signals", file=sys.stderr)
        print("from the corresponding partitions/*.json files.", file=sys.stderr)
        sys.exit(1)

    eqy_dir = Path(sys.argv[1])
    if not eqy_dir.is_dir():
        print(f"Error: {eqy_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    strategies_dir = eqy_dir / "strategies"
    partitions_dir = eqy_dir / "partitions"
    
    if not strategies_dir.exists():
        print(f"Error: strategies directory not found in {eqy_dir}", file=sys.stderr)
        sys.exit(1)
    
    if not partitions_dir.exists():
        print(f"Error: partitions directory not found in {eqy_dir}", file=sys.stderr)
        sys.exit(1)

    failed_signals = []
    
    # Scan all strategies for non-PASS status
    for strategy_dir in strategies_dir.iterdir():
        if strategy_dir.is_dir():
            status_file = strategy_dir / "sby_seq" / "status"
            if status_file.exists():
                try:
                    with open(status_file, "r") as f:
                        status = f.read().strip()
                    if status != "PASS":
                        signal_name = strategy_dir.name
                        failed_signals.append((signal_name, status))
                except Exception as e:
                    print(f"Error reading {status_file}: {e}", file=sys.stderr)

    if not failed_signals:
        print("All strategies passed - no internal signals to report")
        return

    print(f"Found {len(failed_signals)} non-passing strategies:")
    for signal_name, status in failed_signals:
        print(f"  {signal_name}: {status}")

    # Report internal signals for each non-passing strategy
    for signal_name, status in failed_signals:
        partition_json = partitions_dir / f"{signal_name}.json"
        if partition_json.exists():
            report_partition_internal_signals(str(partition_json), signal_name)
        else:
            print(f"Warning: partition JSON file not found for {signal_name}", file=sys.stderr)

if __name__ == "__main__":
    main()
