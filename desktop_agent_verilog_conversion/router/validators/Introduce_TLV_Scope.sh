#!/bin/bash

# Pre-FEV gate for the Introduce TLV Scope task: cross-check every full-FEV
# match section against the mechanical enumeration before spending a FEV run.
# Exit 2 from the checker means it could not run (missing tool, elaboration
# failure); that is no verdict, so FEV proceeds as before.

# Usage: Introduce_TLV_Scope.sh <module-dir>

cd "${1:-.}" || exit 1
shopt -s nullglob

status=0
for f in fev_full.eqy fev_full_*.eqy; do
  ./scripts/gen_match_lines.py --check "$f"
  s=$?
  if [[ $s -eq 2 ]]; then
    echo "NOTE: cross-check unavailable for $f (checker exit 2); proceeding to FEV."
  elif [[ $s -ne 0 ]]; then
    status=1
  fi
done
exit $status
