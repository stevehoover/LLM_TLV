#!/usr/bin/env python3
import sys
if sys.version_info < (3, 12):
    print(f"Error: rename_sigs.py requires Python 3.12+. Current version: {sys.version}. Please upgrade.")
    sys.exit(1)

# Extract the match list from fev_full.eqy and apply the renaming to wip.tlv and copy
# the fev_full.eqy match section to the fev.eqy match section (which must be empty).

import re
import sys
import subprocess
import os
import argparse

def load_match_list(filename, all):
    match_list = []
    match_lines = []
    with open(filename, 'r') as f:
        in_match_section = False
        for line in f:
            line = line.strip()
            if line.startswith('gold-match'):
                in_match_section = True
                parts = line.split()
                if len(parts) >= 3:
                    original = parts[1]
                    replacement = parts[2]
                    # Extract only the final word characters.
                    original = re.search(r'(\w+)$', original).group(1)
                    replacement = re.search(r'(\w+)$', replacement).group(1)
                    if all or original != replacement:
                        match_list.append((original, replacement))
                        match_lines.append(line)
            elif in_match_section and line == '':
                break  # End of match section
    return [match_list, match_lines]

def validate_name(name):
    # Check if the name is a valid lower-case identifier name using the `test_identifier_name.sh` script.
    script_path = os.path.join(os.path.dirname(__file__), 'test_identifier_name.sh')
    result = subprocess.run([script_path, name], capture_output=True, text=True)
    return result.returncode

def main():
    usage = """\
rename_sigs.py [-n] [-f] name1 replacement1 [name2 replacement2 ...]
       rename_sigs.py -t name1 [name2 ...]
       rename_sigs.py [-n] [-f] [-a]
"""
    epilog = """\
Specifically:
- if no names are given, extracts the match list from fev_full.eqy's match section
- for names in `fev_full.eqy` with hierarchy, uses the final part (word chars only, e.g., after ".")
- verifies that replacement names comply with identifier rules
- verifies the names exist in `wip.tlv` and that replacements don't (unless -t)
- stops if any issues are found or if -n or -t are given
- applies the renaming to wip.tlv
- copies the fev_full.eqy match section (excluding one-to-one mappings, unless -a) to the
fev.eqy match section, or reports an error if this section is not empty.

Examples:
  Test whether full_fev.eqy names need changes:
    > rename_sigs.py -n -a
  Dry run using full_fev.eqy matches:
    > rename_sigs.py -n
  Test validity of specific names (no changes):
    > rename_sigs.py -t foo1 bar2 baz3
  Force apply explicit pairs:
    > rename_sigs.py -f foo bar he they
  Convert names to TL-Verilog:
    > rename_sigs.py foo '$foo' bar '$bar'
"""

    parser = argparse.ArgumentParser(
        description='Assists with pipesignal naming conventions and renaming of signals in wip.tlv.',
        usage=usage,
        epilog=epilog,
        formatter_class=argparse.RawTextHelpFormatter,
    )
    parser.add_argument('-n', '--dry-run', action='store_true', help='Perform a dry run without modifying wip.tlv.')
    parser.add_argument('-f', '--force', action='store_true', help='Force the renaming without checks.')
    parser.add_argument('-t', '--test', action='store_true', help='Test the names for validity without making changes.')
    parser.add_argument('-a', '--all', action='store_true', help='Test all match lines, even those that would not change anything.')
    parser.add_argument('names', nargs='*', help='A list of names (-t only) or name pairs (gold gate).')
    args = parser.parse_args()

    status = 0  # Exit status, 0=success, 1=warning, 2=error

    if not args.test and len(args.names) % 2 != 0:
        print("Error: Names must be provided in pairs of original and replacement.")
        sys.exit(1)

    eqy_update = (len(args.names) == 0)
    match_lines = []
    if eqy_update:
        [match_list, match_lines] = load_match_list('fev_full.eqy', args.all)
    else:
        args_per = 1 if args.test else 2
        match_list = [(args.names[i], args.names[i+args_per-1]) for i in range(0, len(args.names), args_per)]

    # Validate names
    rule_violated_mask = 0  # Or of return codes from validate_name.
    rule_messages = [
        "Rule 1: lower-case ASCII word chars only",
        "Rule 2: tokens (delimited by '_') must be a string of letters followed optionally by digits characters",
        "Rule 3: must begin with two letters"
    ]
    for original, replacement in match_list:
        if not re.match(r'^\w+$', original) and original != replacement:
            print(f"Warning: Original name '{original}' contains invalid characters.")
            status = 1
        # Strip "$" if present for validation.
        test_name = replacement.lstrip('$')
        returncode = validate_name(test_name)
        if returncode != 0:
            # Report the violated rules, corresponding to bits 0, 1, 2 (rules 1, 2, 3) of the return code.
            violated_rules = ""
            if returncode != 0:
                rule_violated_mask |= returncode
                if returncode & 1:
                    violated_rules += ", #1"
                if returncode & 2:
                    violated_rules += ", #2"
                if returncode & 4:
                    violated_rules += ", #3"
                print(f"Error: Replacement name '{replacement}' violates rules: {violated_rules[2:]}")

    if rule_violated_mask != 0:
        status = 1
        print("Violated rules above:")
        for i in range(3):
            if rule_violated_mask & (1 << i):
                print(f"  {rule_messages[i]}")
        print("")

    if args.test:
        if status == 0:
            print("All names are compliant.")
        sys.exit(status)

    # Read wip.tlv content
    with open('wip.tlv', 'r') as f:
        content = f.read()

    # Check existence and collisions (unless equal)
    for original, replacement in match_list:
        if re.search(r'\b' + re.escape(original) + r'\b', content) is None:
            print(f"Warning: Original name '{original}' does not exist in wip.tlv.")
            status = 1
        if (original != replacement) and re.search(r'\b' + re.escape(replacement) + r'\b', content):
            print(f"Warning: Replacement name '{replacement}' already exists in wip.tlv.")
            status = 1

    # Make sure `wip.tlv` contains no `gold-match` lines if replacing.
    if eqy_update and re.search(r'^\s*gold-match\s+', content, re.MULTILINE):
        print("Warning: wip.tlv contains 'gold-match' lines that would be replaced.")
        status = 1

    if args.dry_run:
        print(f"Dry run complete. {'No issues found.' if status == 0 else 'Issues must be resolved (or use -f).'}")
    else:
        if status != 0 and not args.force:
            print("Errors or warnings detected. No changes applied. (Repeat with -f to force renaming.)")
        else:
            # Update fev.eqy if needed
            if eqy_update:
                # Read fev.eqy and insert match_lines after the first [match ...] line
                with open('fev.eqy', 'r') as f:
                    fev_lines = f.readlines()
                new_lines = []
                inserted = False
                for line in fev_lines:
                    new_lines.append(line)
                    if not inserted and line.strip().startswith('[match'):
                        # Insert match_lines after this line
                        for match_line in match_lines:
                            new_lines.append(match_line + '\n')
                        inserted = True
                with open('fev.eqy', 'w') as f:
                    f.writelines(new_lines)
                if inserted:
                    print("fev.eqy updated with new match section.")
                else:
                    print("Warning: fev.eqy not updated. No [match ...] section found.")
            
            # Perform replacements in wip.tlv.
            for original, replacement in match_list:
                content = re.sub(r'\b' + re.escape(original) + r'\b', replacement, content)
            with open('wip.tlv', 'w') as f:
                f.write(content)
            print("Renaming complete. wip.tlv has been updated.")

    sys.exit(status)


if __name__ == '__main__':
    main()