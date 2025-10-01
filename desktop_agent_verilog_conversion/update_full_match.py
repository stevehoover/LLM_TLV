#!/usr/bin/env python3

# Update fev_full*.eqy to incorporate wip changes (after successful incremental FEV).
# Apply WIP <tmp-dir>/match_lines.eqy (extracted from fev.eqy) to fev_full*.eqy
# (using TLV names), and produce <tmp-dir>/fev_full*.eqy (using Verilog names).
# This approach is used to generate Verilog names specific to wip.tlv, since TLV changes vs. feved.tlv
# can (in rare circumstances) affect Verilog signal paths for unchanged pipesignals.


import re
import sys
import pathlib
import subprocess


print("Updating fev_full*.eqy to incorporate wip changes...")

# Process command line argument.
if len(sys.argv) != 2:
    print("Usage: ./update_full_match.py <temp-dir>")
    sys.exit(1)
TEMP_DIR = sys.argv[1]

MATCH_LINES_EQY = pathlib.Path('match_lines.eqy')
FEV_FULL_ALT_EQY_GLOB = 'fev_full*.eqy'
MATCH_SECTION_RE = re.compile(r'^\[match\b')

if not MATCH_LINES_EQY.exists():
    print(f"ERROR: {MATCH_LINES_EQY} not found.")
    sys.exit(1)

# Read match_lines.eqy into an array of {gold, gate}.
# match_lines.eqy contains lines like:
# gold-match <gold_signal> <gate_signal>
wip_match_pairs = []
with MATCH_LINES_EQY.open('r') as f:
    for line in f:
        line = line.strip()
        if line.startswith('gold-match '):
            parts = line.split()
            if len(parts) == 3:
                wip_match_pairs.append({'gold': parts[1], 'gate': parts[2]})
            else:
                print(f"WARNING: Ignoring malformed line in {MATCH_LINES_EQY}: {line}")
        else:
            print(f"WARNING: Ignoring malformed line in {MATCH_LINES_EQY}: {line}")

# All work is done in TEMP_DIR, and copied back to fev_full*.eqy only on success.

# For each fev_full*.eqy file:
# - for each line of fev_full*.eqy:
#   - write it to TEMP_DIR/fev_full*.eqy.upd, except:
# - if it is in the [match ...] section:
#   - it should contain a gold-match <gold> <gate>
#   - add it to an array of replacement pairs {gold, gate}
#   - add its array index to a dictionary indexed by <gate>
# - After reading and removing lines (encountering a blank line or EOF):
#   - for each pair in temp-dir/match/match_lines.eqy:
#     - look up the dictionary by its <gold> (matching <gate> from fev_full*.eqy) (or report a warning):
#     - update <gate> of the replacement pair
#   - write the updated replacement pairs to fev_full*.eqy.upd
# - On success, move fev_full*.eqy.upd to fev_full*.eqy
# - On failure, exit with fev_full*.eqy unchanged.

for fev_full_eqy in pathlib.Path('.').glob(FEV_FULL_ALT_EQY_GLOB):
    print(f"Processing {fev_full_eqy}")
    try:
        fev_full_eqy_upd = pathlib.Path(f'{TEMP_DIR}/{fev_full_eqy.name}')
        with fev_full_eqy.open('r') as fin, fev_full_eqy_upd.open('w') as fout:
            in_match_section = False
            full_match_pairs = []
            full_gate_to_index = {}

            for line in fin:
                if MATCH_SECTION_RE.match(line):
                    # Error if already found a match section.
                    if full_match_pairs:
                        raise Exception(f"ERROR: Multiple [match ...] sections found in {fev_full_eqy}")
                    in_match_section = True
                    fout.write(line)
                    continue

                if in_match_section:
                    if not line.strip():
                        # End of match section.
                        in_match_section = False

                        # Apply updates from wip_match_pairs to full_match_pairs.
                        for ml in wip_match_pairs:
                            print(f"Updating full match for gold '{ml['gold']}' to gate '{ml['gate']}'")
                            print(f"ml: {ml}")
                            wip_gate = ml['gate']
                            wip_gold = ml['gold']
                            if wip_gold in full_gate_to_index:
                                idx = full_gate_to_index[wip_gold]
                                full_match_pairs[idx]['gate'] = wip_gate
                            else:
                                print(f"WARNING: Unable to update {fev_full_eqy} for refactoring of '{wip_gold}' -> {wip_gate}.")

                        # Write updated match section lines.
                        for pair in full_match_pairs:
                            fout.write(f'gold-match {pair["gold"]} {pair["gate"]}\n')
                        fout.write(line)  # Write the blank line ending the section.
                        continue

                    # Inside match section, process line.
                    if line.startswith('gold-match '):
                        print(f"Processing line in match section: {line.strip()}")
                        parts = line.strip().split()
                        if len(parts) == 3:
                            gate = parts[2]
                            full_gate_to_index[gate] = len(full_match_pairs)
                            full_match_pairs.append({'gold': parts[1], 'gate': gate})
                        else:
                            print(f"WARNING: Ignoring malformed line in {fev_full_eqy}: {line.strip()}")
                    else:
                        print(f"WARNING: Ignoring malformed line in {fev_full_eqy}: {line.strip()}")
                else:
                    # Outside match section, just copy line.
                    fout.write(line)

            # Shouldn't end in a match section.
            if in_match_section:
                raise Exception(f"ERROR: Unexpected end of file in {fev_full_eqy}")

            # Moved to fev.sh for because it must be done in the same TEMP_DIR as incremental FEV.
            ## Generate <temp-dir>/fev_full*.eqy files from fev_full*.eqy and wip.tlv, updated to use Verilog names.
            #result = subprocess.run([f"{pathlib.Path(__file__).parent}/map_match_pipesignals.py", TEMP_DIR, str(fev_full_eqy)])
            #if result.returncode != 0:
            #  print(f"ERROR: map_match_pipesignals.py failed for {fev_full_eqy}")
            #  sys.exit(1)
    except Exception as e:
        print(f"ERROR: Exception processing {fev_full_eqy}: {e}")
        sys.exit(1)
# Success. Accept the change.
for fev_full_eqy in pathlib.Path('.').glob(FEV_FULL_ALT_EQY_GLOB):
    fev_full_eqy_upd = pathlib.Path(f'{TEMP_DIR}/{fev_full_eqy.name}')
    fev_full_eqy.unlink()
    fev_full_eqy_upd.rename(fev_full_eqy)
# All done with match_lines.eqy. Empty it, indicating completion of fev_full*.eqy updates.
MATCH_LINES_EQY.write_text('')
