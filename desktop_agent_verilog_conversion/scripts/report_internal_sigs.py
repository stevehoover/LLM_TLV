#!/usr/bin/env python3

# Usage: python3 report_internal_sigs.py <eqy_output_directory>
# Reports internal and unused signals for non-passing EQY partitions

import json, sys, os
from pathlib import Path

def load_json(path: str):
    with open(path, "r") as f:
        return json.load(f)

def get_signals(d: dict, keys: list[str], signal_type: str) -> dict:
    """Extract signals of specified type ('internal' or 'unused') from module data"""
    for k in keys:
        v = d.get(k)
        if isinstance(v, dict):
            signals = v.get(signal_type, {})
            if isinstance(signals, dict):
                return signals
    return {}

def report_partition_internal_signals(partition_json_path: str, signal_name: str):
    """Report internal and unused signals for a given partition JSON file"""
    try:
        obj = load_json(partition_json_path)
        gold_internal = get_signals(obj, ["gold_module", "gold_model"], "internal")
        gate_internal = get_signals(obj, ["gate_module", "gate_model"], "internal")
        gold_unused = get_signals(obj, ["gold_module", "gold_model"], "unused")
        gate_unused = get_signals(obj, ["gate_module", "gate_model"], "unused")

        print(f"\n=== Internal signals for {signal_name} ===")
        print("Gold internal:")
        for name in sorted(gold_internal.keys()):
            print(f"  {name}")

        print("\nGate internal:")
        for name in sorted(gate_internal.keys()):
            print(f"  {name}")

        print(f"\n=== Unused signals for {signal_name} ===")
        print("Gold unused:")
        for name in sorted(gold_unused.keys()):
            print(f"  {name}")

        print("\nGate unused:")
        for name in sorted(gate_unused.keys()):
            print(f"  {name}")
        print()
    except Exception as e:
        print(f"Error processing {partition_json_path}: {e}", file=sys.stderr)

def main():
    if len(sys.argv) != 2 or sys.argv[1] in ["-h", "--help"]:
        print(f"usage: {sys.argv[0]} <eqy_output_directory>", file=sys.stderr)
        print("", file=sys.stderr)
        print("Reports internal and unused signals for any EQY strategies that did not PASS.", file=sys.stderr)
        print("Scans strategies/*/sby_seq/status files and reports internal and unused signals", file=sys.stderr)
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

    failed_partitions = []
    unfinished = 0
    
    # Scan all partitions in strategies/sby_seq/status for non-PASS status
    for partition_dir in strategies_dir.iterdir():
        if partition_dir.is_dir():
            status_file = partition_dir / "sby_seq" / "status"
            if status_file.exists():
                try:
                    with open(status_file, "r") as f:
                        status = f.read().strip()
                    if status != "PASS":
                        signal_name = partition_dir.name
                        failed_partitions.append((signal_name, status))
                except Exception as e:
                    print(f"Error reading {status_file}: {e}", file=sys.stderr)
            else:
                unfinished += 1

    if not failed_partitions:
        if unfinished:
            print(f"No failing partitions, but {unfinished} partitions have no status yet (EQY stopped early, e.g. on a timeout).")
        else:
            print("All partitions passed!")
        return

    print(f"Found {len(failed_partitions)} non-passing partitions:")
    for signal_name, status in failed_partitions:
        print(f"  {signal_name}: {status}")

    # Report internal signals for each non-passing partition
    for signal_name, status in failed_partitions:
        partition_json = partitions_dir / f"{signal_name}.json"
        if partition_json.exists():
            report_partition_internal_signals(str(partition_json), signal_name)
        else:
            print(f"Warning: partition JSON file not found for {signal_name}", file=sys.stderr)

    print("Signals reported above are Verilog signals. Some may be generated from TL-Verilog.")
    print("Address mismatches by editing *.eqy. Use TL-Verilog pipesignal names rather than generated names.")

if __name__ == "__main__":
    main()
