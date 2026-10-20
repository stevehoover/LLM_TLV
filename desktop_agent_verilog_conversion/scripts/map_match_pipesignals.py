#!/usr/bin/env python3

# Map TL-Verilog pipesignal references to Verilog signal paths in a .eqy file, producing <tmp-dir>/<same>.eqy.
#
# Usage: python ./map_match_pipesignals.py <temp-dir> <eqy-file> [<match-file-name>]
#  <temp-dir>: a temporary working directory;
#  <eqy-file>: the .eqy file to process
#  <match-file-name>: optional (provided only for incremental FEV) a file name, e.g. match_lines.eqy, to which
#                     to write the original .eqy match section (in <temp-dir>)
#                     if provided, <temp-dir>/<eqy-file>.upd will be created with the match section removed.
#
# This script behaves differently for incremental FEV (when <match-file-name> is given) vs. full FEV (when it is not).
# Incremental FEV maps both gold and gate pipesignals, using feved.tlv and wip.tlv, respectively. Full FEV maps only
# gate pipesignals, using wip.tlv.
#
# This script:
# - Extracts the [match ...] sections from fev.eqy.
# - Creates `./<tmp-dir>/*_match.tlv` file(s) that append the match section contents to wip.tlv/feved.tlv in an
#   `\SV_plus` region. For incremental FEV, two files, `wip_match.tlv` and `feved_match.tlv` are created, containing wip
#   and feved pipesignal lists, respectively. For full FEV, the full match section is added in `fev*_match.tlv`.
# - Runs SandPiper on these `*_match.tlv` files to produce `*_match.sv`, which contains the mapped signal names.
#   (Note these files are not valid Verilog.)
# - For incremental FEV, writes the raw match section to `<tmp-dir>/<match-file-name>` (still with TLV pipesignal names)
# - For incremental FEV, writes `<tmp-dir>/<eqy-file>.upd` (`fev.eqy.upd`), which is <eqy-file> with the match section removed.
# - Updates the match sections in <eqy-file> to use the mapped signal names, writing the result to <tmp-dir>/<eqy-file>.
#
# Thus, we have the following intermediate files in <tmp-dir>:
#
# For incremental FEV:
# - `fev.eqy.upd`: `fev.eqy` with match section removed
# - `match_lines.eqy`: original match section from `fev.eqy`
# - `feved_match.tlv`: to map gold pipesignals
# - `wip_match.tlv`: to map gate pipesignals
# - `feved_match.sv`: mapped gold signals
# - `wip_match.sv`: mapped gate signals
#
# For full FEV:
# - `fev_full*_match.tlv`: to map gate pipesignals
# - `fev_full*_match.sv`: mapped gate signals
#
# For both:
# - `fev*.eqy`: updated to use mapped signal names

import re
import sys
import pathlib
import subprocess
import json

# Process command line arguments.
if len(sys.argv) < 3 or len(sys.argv) > 4:
    print("Usage: python ./map_match_pipesignals.py <temp-dir> <eqy-file> [<match-file-name>]")
    sys.exit(1)
TEMP_DIR = sys.argv[1]
EQY_FILE = sys.argv[2]
if len(sys.argv) > 3:
    MATCH_LINES_FILE = f"{TEMP_DIR}/{sys.argv[3]}"
    FEV_EQY_UPD = pathlib.Path(f'{TEMP_DIR}/{EQY_FILE}.upd')
else:
    MATCH_LINES_FILE = None
    FEV_EQY_UPD = None

FEV_EQY = pathlib.Path(EQY_FILE)
WIP_TLV = pathlib.Path('wip.tlv')
TMP_FEV_EQY = pathlib.Path(f'{TEMP_DIR}/{EQY_FILE}')
MATCH_SECTION_RE = re.compile(r'^\[match\b')

# Determine M5_CONFIG_STR from config.json (e.g. '--m5def cond_w_1 --m5def cond_reset_init').
# Extract the M5 configuration from FEV_EQY by looking for the .sv file name among the `read_verilog` commands.
eqy_text = FEV_EQY.read_text()
eqy_m5_config = "?"
for line in eqy_text.splitlines():
    m = re.search(r'\s*read_verilog.*\s+wip_?(\S*)\.sv', line)
    if m:
        eqy_m5_config = m.group(1)
        break
if eqy_m5_config == "?":
    print(f"ERROR: Could not determine M5 configuration used in {str(FEV_EQY)} from read_verilog commands.")
    print("       This needs to be addressed by the user.")
    sys.exit(1)
# Read `M5_configs` from `config.json`.
try:
    with open('config.json', 'r') as cjf:
        config_json = json.load(cjf)
    M5_configs = config_json.get('M5_configs', None)
except Exception as ex:
    print(f"Could not read M5 configuration from config.json: {ex}")
    M5_configs = {}
FMT_FLAT_SIGNALS = config_json.get('fmt_flat_signals', False) is True
# For wip.tlv (eqy_m5_config is ""), use "default_config" from the json. 
if not eqy_m5_config:
    eqy_m5_config = config_json.get('default_config', "")
# Get the M5 configuration string, or fail.
if eqy_m5_config == "":
    M5_CONFIG_STR = ""
else:
    M5_CONFIG_STR = M5_configs.get(eqy_m5_config, None)
if M5_CONFIG_STR is None:
    print(f"ERROR: Could not find M5 configuration '{eqy_m5_config}' in config.json's M5_configs.")
    print("       This needs to be addressed by the user.")
    sys.exit(1)



# Map TL-Verilog pipesignal references to Verilog signal paths by running SandPiper.
def map_pipesignals(match_lines: list[str], tlv_file: pathlib.Path, eqy_file: str, m5_config_str: str) -> list[str]:
    # Takes a block of text containing pipesignal references and converts them to Verilog signal paths.
    #
    # Args:
    #    match_lines: List of strings containing pipesignal references to map
    #    tlv_file: Path to the TL-Verilog file to use as the base for mapping
    #
    # Returns:
    #    List of strings with pipesignal references mapped to Verilog signal names
    
    # Generate unique file paths based on the TLV file name
    tlv_name = tlv_file.stem
    match_tlv = pathlib.Path(f'{TEMP_DIR}/{tlv_name}_match.tlv')
    match_sv_name = f'{tlv_name}_match.sv'
    match_sv = pathlib.Path(f'{TEMP_DIR}/{match_sv_name}')
    
    # Create match TLV file by appending match sections to the TLV file in a \SV_plus region
    match_tlv.parent.mkdir(exist_ok=True)
    with match_tlv.open('w') as f:
        f.write(tlv_file.read_text())
        f.write('\n\\SV_plus\n')
        f.write('[match]\n')
        f.writelines(match_lines)

    # Run SandPiper to produce the mapped Verilog file
    try:
        # Remove .sv first (though it should not exist)
        if match_sv.exists():
            match_sv.unlink()
        cmd = [
            'sandpiper-saas', '-i', str(match_tlv), '-o', match_sv_name,
            '--outdir', TEMP_DIR, '--inlineGen', '--noline', '--iArgs'
        ]
        if FMT_FLAT_SIGNALS:
            cmd.append('--fmtFlatSignals')
        # Append M5 configuration if provided.
        if m5_config_str:
            cmd.extend(m5_config_str.split())
        print(f"Running SandPiper...")  
        result = subprocess.run(cmd, check=True, capture_output=True, text=True)
        if not match_sv.exists():
            # Presumably the .tlv file was simply Verilog, and we must copy it.
            match_sv.write_text(match_tlv.read_text())
    except subprocess.CalledProcessError as e:
        print(f"ERROR: SandPiper failed to map TL-Verilog pipesignal paths to Verilog signal paths for the match section.")
        print(f"    Failing command (status ${e.returncode}): {' '.join(cmd)}")
        if e.stdout:
            print("SandPiper stdout:\n" + e.stdout)
        if e.stderr:
            print("SandPiper stderr:\n" + e.stderr)
        
        print("")
        print("This failure likely indicates a syntax issue with pipesignal references in the match")
        print(f"section of `{str(FEV_EQY)}`. Dangling signal warnings likely indicate")
        print("pipesignal references using the wrong path. Other SandPiper error messages are explained")
        print("in `sandpiper_messages.md`.")
        print("")
        print(f"{eqy_file} uses M5 configuration:")
        print(f"    {eqy_m5_config}")
        print("which may affect which signals exist.")
        print("")
        print("In case you need to dig deeper, details of the use of SandPiper for this mapping and the")
        print("intermediate files involved can be found in the header comments of this script (`map_match_pipesignals.py`).")
        sys.exit(1)

    # Read the generated SV file to extract the match section body, now mapped to Verilog
    return extract_match_sections(match_sv, None)


# Extract the [match ...] section from a file, writing an updated file without this section emptied if upd_path isn't None.
def extract_match_sections(file_path: pathlib.Path, upd_path: pathlib.Path) -> list[str]:
    match_lines = []
    in_match_section = False
    print(f"Extracting match sections from {file_path}")
    found_cnt = 0
    with file_path.open('r') as f:
        updf = upd_path.open('w') if upd_path else None
        for line in f:
            blank = not line.strip()
            # Write updated file if requested, excluding match section lines.
            if updf and (not in_match_section or blank):
                updf.write(line)
            
            if MATCH_SECTION_RE.match(line):
                in_match_section = True
                found_cnt += 1
            elif in_match_section:
                if blank:
                    in_match_section = False
                    if not updf:
                        # Nothing left to do.
                        break
                else:
                    match_lines.append(line.lstrip())
        if updf:
            updf.close()
    if found_cnt != 1:
        if found_cnt == 0:
            print(f"ERROR: No [match ...] section found in {file_path}.")
        else:
            print(f"ERROR: Multiple [match ...] sections found in {file_path}.")
        sys.exit(1)
    return match_lines


# Extract the [match ...] sections from FEV_EQY.
match_lines = extract_match_sections(FEV_EQY, FEV_EQY_UPD)


# Write match_lines to MATCH_LINES_FILE.
if MATCH_LINES_FILE:
    with pathlib.Path(MATCH_LINES_FILE).open('w') as f:
        f.writelines(match_lines)


# Map pipesignals in match_lines to Verilog signal names
if MATCH_LINES_FILE:
    # Incremental FEV: need to map gold and gate signals separately
    FEVED_TLV = pathlib.Path('feved.tlv')
    
    # Extract gold (left) and gate (right) signals from match lines
    gold_signals = []
    gate_signals = []
    for line in match_lines:
        if line.strip().startswith('gold-match '):
            parts = line.strip().split(None, 2)  # Split into at most 3 parts
            if len(parts) >= 3:
                gold_signals.append(f"{parts[1]}\n")
                gate_signals.append(f"{parts[2]}\n")
    
    # Map gold signals using feved.tlv and gate signals using wip.tlv
    mapped_gold_signals = map_pipesignals(gold_signals, FEVED_TLV, EQY_FILE, M5_CONFIG_STR) if gold_signals else []
    mapped_gate_signals = map_pipesignals(gate_signals, WIP_TLV, EQY_FILE, M5_CONFIG_STR) if gate_signals else []

    # Reconstruct match lines with mapped signals
    mapped_match_lines = []
    for i, line in enumerate(match_lines):
        if line.strip().startswith('gold-match ') and i < len(mapped_gold_signals) and i < len(mapped_gate_signals):
            # Use mapped signal names directly
            gold_mapped = mapped_gold_signals[i].strip()
            gate_mapped = mapped_gate_signals[i].strip()
            mapped_match_lines.append(f"gold-match {gold_mapped} {gate_mapped}\n")
        else:
            # Non-match line, keep as-is
            mapped_match_lines.append(line)
else:
    # Full FEV: map entire match section using wip.tlv only, with parameters
    mapped_match_lines = map_pipesignals(match_lines, WIP_TLV, EQY_FILE, M5_CONFIG_STR)


# Update the match sections in FEV_EQY to use the mapped signal names, writing to TMP_FEV_EQY.
with TMP_FEV_EQY.open('w') as out_f:
    with FEV_EQY.open('r') as in_f:
        in_match_section = False
        for line in in_f:
            if MATCH_SECTION_RE.match(line):
                in_match_section = True
                out_f.write(line)
                out_f.writelines(mapped_match_lines)
                continue
            if in_match_section:
                if not line.strip():
                    in_match_section = False
                    out_f.write('\n')
                continue
            out_f.write(line)
