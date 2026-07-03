#!/bin/bash

# Snapshot the current conversion state into a history directory.
#
# Usage: ./record_history.sh [TARGET_HISTORY_DIR]
#   With a directory argument, that directory is used (fev.sh passes the one it
#   computed for the current refactoring step). With no argument, the next unused
#   history/NNN directory is created (get_task.py and prep.sh use this to record a
#   per-task or baseline snapshot).
#
# Run from a module conversion directory. Copies whatever artifacts are present so
# the checkpoint is self-contained; status.json is expected to already reflect the
# state being recorded.

set -uo pipefail

# Directory of this script (for get_task.py).
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

mkdir -p history
if [[ $# -ge 1 && -n "$1" ]]; then
  dir="$1"
  name="$(basename "$dir")"
else
  num=1
  while [[ -d history/$(printf "%03d" "$num") ]]; do
    num=$((num + 1))
  done
  name="$(printf "%03d" "$num")"
  dir="history/${name}"
fi

mkdir -p "${dir}"
rm -f history/latest
ln -s "${name}" history/latest
# These files are conversion-directory preconditions, so copy them unguarded.
cp config.json "${dir}"
cp wip.tlv "${dir}"
rm -f "${dir}/feved.tlv"
cp feved.tlv "${dir}"
cp fev.eqy "${dir}"
cp status.json "${dir}"
# tracker.md may legitimately be absent on an older module, so guard it.
[ -f tracker.md ] && cp tracker.md "${dir}"
"${script_dir}/get_task.py" current > "${dir}/task.md" 2>/dev/null || true
echo "${dir}"
