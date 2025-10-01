#!/bin/bash

# This script restores the working directory to the state captured in the give history directory.

# Usage: restore_from_history.sh <history-number>
# Run from a conversion directory containing /history/<history-number>
# E.g., ./scripts/restore_from_history.sh 2

set -euo pipefail

cnt=$1
HISTORY_NAME=$(printf "%03d" "$cnt")   # Append leading zeros.
HISTORY_DIR="history/${HISTORY_NAME}"

if [[ ! -d "$HISTORY_DIR" ]]; then
  echo "ERROR: History directory $HISTORY_DIR not found."
  exit 1
fi

# Copy the saved files back to the working directory in a state where rerunning fev.sh
# should produce the same results.
cp "$HISTORY_DIR/wip.tlv" "./wip.tlv"
cp "$HISTORY_DIR/feved.tlv" "./feved.tlv"
cp "$HISTORY_DIR/status.json" "./status.json"
shopt -s nullglob
for file in $HISTORY_DIR/fev*.eqy; do
  cp "$file" .
done
shopt -u nullglob

# Remove local files.
rm match_lines.eqy 2>/dev/null || true

# Delete history directories after and including the given one.
# Strip leading zeros from history directory number.
while [[ -d history/$(printf "%03d" "${cnt}") ]]; do
  echo "Removing history directory: history/$(printf "%03d" "${cnt}")"
  rm -rf history/$(printf "%03d" "${cnt}")
  cnt=$((cnt + 1))
done

# Run fev.sh to reproduce the results.
./scripts/fev.sh
