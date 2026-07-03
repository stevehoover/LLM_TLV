#!/bin/bash

# Usage: ./prep.sh <directory> <verilog-file> <module-name>

# Create and prepare the given directory for Verilog -> TL-Verilog code conversion
# as described in instructions/desktop_agent_instructions.md.

# Absolute path to the directory containing this script.
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_dir" || exit 1

DIR=$1
VERILOG_FILE=$2
MODULE_NAME=$3

# DIR and VERILOG_FILE must be an absolute path.
if [[ "$DIR" != /* ]]; then
  echo "ERROR: Directory path $DIR must be absolute."
  exit 1
fi

if [[ "$VERILOG_FILE" != /* ]]; then
  echo "ERROR: Verilog file path $VERILOG_FILE must be absolute."
  exit 1
fi

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

# Portable relative symlink helper. `ln -sr` is GNU coreutils only; macOS BSD ln has no -r.
make_relative_symlink() {
  local target="$1"
  local link="$2"
  local rel
  rel=$(python3 -c "import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))" "$target" "$(dirname "$link")")
  ln -s "$rel" "$link"
}

# Create links back to the main directories.
make_relative_symlink "$script_dir" "$DIR/scripts"
make_relative_symlink "$script_dir/../fev" "$DIR/fev"
make_relative_symlink "$script_dir/../instructions" "$DIR/instructions"

# Copy the Verilog file to prepared.sv (also orig.sv, wip.sv, feved.sv).
cp "$VERILOG_FILE" "$DIR/orig.sv"
cp "$VERILOG_FILE" "$DIR/prepared.sv"
cp "$VERILOG_FILE" "$DIR/wip.tlv"
cp "$VERILOG_FILE" "$DIR/feved.tlv"
cp "$VERILOG_FILE" "$DIR/feved.sv"
chmod 400 "$DIR/feved.tlv"

# Initialize status.md, tracker.md, fev.eqy, and fev_full.eqy.
touch "$DIR/tracker.md"
echo '{"task": "Preparation", "fev.sh": "none", "fev_cnt": 0, "llm": ""}' > "$DIR/status.json"
sed "s|<ORIGINAL_FILE>|feved.sv|g; s|<MODIFIED_FILE>|wip.sv|g; s|<MODULE_NAME>|$MODULE_NAME|g" "$script_dir/../fev/fev.eqy" > "$DIR/fev.eqy"
sed "s|<ORIGINAL_FILE>|prepared.sv|g; s|<MODIFIED_FILE>|wip.sv|g; s|<MODULE_NAME>|$MODULE_NAME|g" "$script_dir/../fev/fev.eqy" > "$DIR/fev_full.eqy"

# Create config.json with top module name
cat > "$DIR/config.json" <<EOF
{
  "top": "$MODULE_NAME"
}
EOF
# Create a .gitignore to ignore tmp directory.
cat > "$DIR/.gitignore" <<EOF
tmp/
unsuccessful/
EOF

# Record the prepared baseline as the first history snapshot, so the conversion's
# starting point is captured even though no source code has changed yet.
( cd "$DIR" && "$script_dir/record_history.sh" > /dev/null )

echo "Created the following files in $DIR:"
ls "$DIR"
echo "Your next steps are:"
echo " - update prepared.sv as discussed and copy it to wip.sv and feved.sv (if changed)."
echo " - create match_wip.eqy to map all signals (initially to themselves) and copy it to match_feved.eqy."
