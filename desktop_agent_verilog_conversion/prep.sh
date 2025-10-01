#!/bin/bash

# Usage: ./prep.sh <directory> <verilog-file> <module-name>

# Create and prepare the given directory for Verilog -> TL-Verilog code conversion
# as described in desktop_agent_instructions.md.

# Absolute path to the directory containing this script.
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_dir" || exit 1

DIR=$1
VERILOG_FILE=$2
MODULE_NAME=$3

# Fail if the directory already exists.
if [[ -d "$DIR" ]]; then
  echo "ERROR: Directory $DIR already exists."
  exit 1
fi

# Fail if the Verilog file does not exist.
if [[ ! -f "$VERILOG_FILE" ]]; then
  echo "ERROR: Verilog file $VERILOG_FILE not found."
  exit 1
fi

# Create the work directory and its temporary subdirectory.
mkdir -p "$DIR/tmp"

# Create a link back to the script directory.
ln -s "$script_dir" "$DIR/scripts"

# Copy the Verilog file to prepared.sv (also orig.sv, wip.sv, feved.sv).
cp "$VERILOG_FILE" "$DIR/orig.sv"
cp "$VERILOG_FILE" "$DIR/prepared.sv"
cp "$VERILOG_FILE" "$DIR/wip.tlv"
cp "$VERILOG_FILE" "$DIR/feved.tlv"

# Initialize status.md and tracker.md files.
touch "$DIR/tracker.md"
echo '{"task": "Preparation", "fev.sh": "none", "llm": ""}' > "$DIR/status.json"
sed "s|<ORIGINAL_FILE>|feved.sv|g; s|<MODIFIED_FILE>|wip.sv|g; s|<MODULE_NAME>|$MODULE_NAME|g" "./fev.eqy" > "$DIR/fev.eqy"
sed "s|<ORIGINAL_FILE>|prepared.sv|g; s|<MODIFIED_FILE>|wip.sv|g; s|<MODULE_NAME>|$MODULE_NAME|g" "./fev.eqy" > "$DIR/fev_full.eqy"

# Create config.json with top module name
cat > "$DIR/config.json" <<EOF
{
  "top": "$MODULE_NAME"
}
EOF
# Create a .gitignore to ignore tmp directory.
cat > "$DIR/.gitignore" <<EOF
tmp/
EOF

echo "Created the following files in $DIR:"
ls "$DIR"
echo "Your next steps are:"
echo " - update prepared.sv as discussed and copy it to wip.sv and feved.sv (if changed)."
echo " - create match_wip.eqy to map all signals (initially to themselves) and copy it to match_feved.eqy."
