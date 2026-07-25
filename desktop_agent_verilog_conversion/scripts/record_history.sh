#!/bin/bash

# Snapshot the current conversion state into a history directory.
#
# Usage: ./record_history.sh <TARGET_HISTORY_DIR>
#   Records into the given directory; each caller computes the directory it wants.
#   fev.sh passes the directory it computed for the step (with its reuse logic),
#   get_task.py passes the next directory for a no-op task, and prep.sh passes the
#   baseline (001). This keeps the directory-numbering logic in the callers and out
#   of here, so the directory is scanned for at most once per call site.
#
# Run from a module conversion directory. Copies whatever artifacts are present so
# the checkpoint is self-contained; status.json is expected to already reflect the
# state being recorded.

set -uo pipefail

# Directory of this script (for get_task.py).
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ $# -lt 1 || -z "$1" ]]; then
  echo "ERROR: record_history.sh requires a target history directory (e.g. history/003)." >&2
  exit 1
fi
dir="$1"
name="$(basename "$dir")"

mkdir -p history
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
