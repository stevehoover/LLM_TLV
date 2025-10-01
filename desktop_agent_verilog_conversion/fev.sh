#!/bin/bash

# A supporting script for the instructions in desktop_agent_instructions.md.

# Usage: ./fev.sh
# Run from the directory containing the TLV file(s).

# This script involves three steps, performed atomically. This script is idempotent.
# Any of these three steps that have already been completed will be skipped until all
# have succeeded.
# All work is done in a temporary directory, and captured on success after each step.
# match_lines.eqy lists signal/pipesignal mappings from feved.sv to wip.sv and serves
# also as an indication of which steps have been completed.
#
# Steps are:
# - Incremental FEV:
#   - Run SandPiper on wip.tlv and feved.tlv
#   - Map pipesignal paths in fev.eqy [match ...] section to signal paths (using SandPiper)
#   - Run eqy with updated fev.eqy.
# - Update fev_full Matches
#   - Incorporating match_lines.eqy into fev_full*.eqy
# - Full FEV
#   - Map pipesignal paths in fev_full*.eqy [match ...] sections to signal paths (using SandPiper)
#   - Run eqy for fev_full*.eqy verifying wip.sv vs. prepared.sv for various parameter values.
#
# These update local files (match_lines.eqy, feved.tlv, and feved.sv) as follows:
# - Incremental FEV:
#   - match_lines.eqy is extracted from fev.eqy
#   - wip.tlv -> feved.tlv
#   - wip.sv -> feved.sv
#   - wip.tlv is made read-only
# - Update fev_full Matches:
#   - match_lines.eqy is emptied
# - Full FEV:
#   - wip.tlv is made writable again after passing fev_full.eqy (fev_full_*.eqy may still fail and
#     would need wip.tlv changes)
#   - match_lines.eqy is removed
#
# They update history/#/ with:
# - Incremental FEV: `wip.tlv`, `feved.tlv`, and `fev.eqy`, `status.json`
# - Update fev_full Matches: nothing
# - Full FEV:  `fev_full*.eqy` and `prepared.sv` (as a symlink), `status.json`

set -uo pipefail



####################
# Common Functions #
####################

# Update status.json to indicate failure. Preserve "task", and "llm" properties. Write "fev.sh" with, "$status: $msg".
# Return the give status.
# Usage example: update_status 1 "file not found" || exit $?
function update_status() {
  local status="$1"
  local msg="$2"
  jq --arg val "$status: $msg" \
     '.["fev.sh"] = $val' status.json > status.tmp.json && mv status.tmp.json status.json
  echo 'Updated the `fev.sh` property of `status.json`: '"$status: $msg"
  if [[ $status -ne 0 ]]; then
    echo "Try a smaller change, or, if you are having trouble making forward progress,"
    echo "reread the instructions in 'desktop_agent_instructions.md' for ideas and double-check your work."
  fi
  echo 'Remember to update the `llm` property of `status.json` and possibly `tracker.md` to reflect your progress.'
  return $status
}

# Run a tool command, logging output to TEMP_DIR and returning the given exit status or failure or 0 on success.
function run_tool() {
  local job="$1"
  local tool_cmd="$2"
  local fail_status="$3"
  local fail_msg="$4"
  local cmd="timeout 120s $tool_cmd > ${TEMP_DIR}/${job}.log 2>&1"
  echo "Running: $cmd"
  if ! eval "$cmd"; then
    # Output the log for diagnosis.
    #cat "${TEMP_DIR}/${job}.log"
    # Record failure status and message.
    echo "HERE"
    update_status "$fail_status" "$fail_msg"
    # Report error.
    echo "ERROR: $fail_msg"
    echo "   Failing command: $cmd"
    return $fail_status
  else
    echo "Successfully ran: $tool_cmd"
    return 0
  fi
}

# A variant of run_tool specialized for eqy commands, which also runs eqy_diag.py on failure.
# Takes <root> name of <root>.eqy file rather than a full command line.
function run_fev() {
  local job="$1"
  local fev_name="$2"
  local fail_status="$3"
  local fail_msg="$4"
  local fev_out_dir="${TEMP_DIR}/${fev_name}"
  local cmd="eqy -d ${fev_out_dir} ${TEMP_MATCH_DIR}/${fev_name}.eqy"
  run_tool "$job" "$cmd" "$fail_status" "$fail_msg"
  status=$?
  if [[ $status -ne 0 ]]; then
    if [[ -d ${fev_out_dir} ]]; then
      # TODO: Also report Warnings from the log about bad match lines.
      # Report internal signals for diagnosis.
      echo
      echo "EQY Failure Analysis:"
      echo
      echo "FAIL/UNKNOWN often results from unmatched state elements."
      echo "Proper matching can also help to isolate issues."
      echo "Reporting failure status and identifying internal (unmatched) signals."
      echo "EQY log can be found in: ${TEMP_DIR}/${job}.log"
      ${script_dir}/report_internal_sigs.py "${fev_out_dir}"
      echo
    else
      echo
      echo "FEV log for ${fev_name}.eqy:"
      echo
      cat "${TEMP_DIR}/${job}.log"
      echo
    fi

  fi
  return $status
}



#################
# Preconditions #
#################

for file in wip.tlv prepared.sv feved.tlv fev.eqy status.json; do
  if [[ ! -f "$file" ]]; then
    echo "ERROR: $file not found."
    update_status 1 "$file not found" || exit $?
  fi
done

# Make sure required commands are available.
for cmd in sandpiper-saas eqy jq; do
  if ! command -v "$cmd" &> /dev/null; then
    echo "ERROR: $cmd could not be found. Please ensure it is installed and in your PATH."
    update_status 1 "$cmd not found" || exit $?
  fi
done


#########
# Setup #
#########

# Directory of this script.
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Determine history directory
mkdir -p history
NEXT_HISTORY_NUM=1
while [[ -d history/$(printf "%03d" "${NEXT_HISTORY_NUM}") ]]; do
  NEXT_HISTORY_NUM=$((NEXT_HISTORY_NUM + 1))
done
PREV_HISTORY_NUM=$((NEXT_HISTORY_NUM - 1))
PREV_HISTORY_DIR=history/$(printf "%03d" "${PREV_HISTORY_NUM}")
# NEXT_HISTORY_DIR assigned later.

# See whether full FEV was completed previously.
if [[ -e match_lines.eqy ]]; then
  NEED_FULL_FEV=true
else
  NEED_FULL_FEV=false
fi
if [[ $NEED_FULL_FEV == true ]]; then
  # Source files should be unchanged since last FEV.
  if ! diff -q wip.tlv feved.tlv > /dev/null; then
    echo "Uh oh! Full FEV (vs. prepared.sv) was not completed previously, but wip.tlv has been updated."
    echo "If you made these changes to address failures with non-default parameters, no worries."
    echo "Otherwise, it is always best to resolve full FEV failures before proceeding. We'll test your"
    echo "new changes anyway. In case of failure, it is recommended to revert wip.tlv to feved.tlv and"
    echo "get full FEV passing. Reference 'full_fev_failed.md' for guidance."
    exit 1
    # Keep the old history, even though full FEV failed.
    NEED_FULL_FEV=false
  else
    echo "Running full FEV only (failed previously)."
    # Continue ongoing work in PREV_HISTORY_DIR, only running full FEV.
    NEXT_HISTORY_NUM=$PREV_HISTORY_NUM
  fi
fi
NEXT_HISTORY_NAME=$(printf "%03d" "${NEXT_HISTORY_NUM}")
NEXT_HISTORY_DIR=history/${NEXT_HISTORY_NAME}


# Create a local (visible to agent) temporary directory.
mkdir -p tmp
TEMP_NAME="$(cd tmp && mktemp -d XXXXX)"
TEMP_DIR="./tmp/${TEMP_NAME}"
echo "Verifying changes in: $TEMP_DIR"
TEMP_MATCH_DIR=${TEMP_DIR}/match
mkdir ${TEMP_MATCH_DIR}
rm -f ./tmp/latest
ln -s ${TEMP_NAME} ./tmp/latest



###################
# Incremental FEV #
###################

if [[ $NEED_FULL_FEV == false ]]; then
  # Attempt to run incremental FEV (vs. feved.sv).
  # Success updates history and creates match_lines.eqy for updating full FEV configs.

  # Run SandPiper on wip.tlv and (just to be certain) feved.tlv.
  for file in wip feved; do
    rm -f ${file}.sv
    run_tool "sandpiper_${file}" "sandpiper-saas -i ${file}.tlv -o ${file}.sv --inlineGen --iArgs" 2 "SandPiper failed on ${file}.tlv"
    status=$?
    if [[ $status -ne 0 ]]; then
      # Output the log.
      echo
      echo "SandPiper log for ${file}.tlv:"
      echo
      cat "${TEMP_DIR}/sandpiper_${file}.log"
      echo
      exit $status
    fi
    if [[ ! -f ${file}.sv ]]; then
      # If SandPiper returns 0 but the output file is missing, its presumably because the file
      # was not a TLV file so copy it to the output file.
      echo "SandPiper did not produce ${file}.sv; presuming ${file}.tlv is Verilog."
      cp ${file}.tlv ${file}.sv
    fi
  done


  # Map TL-Verilog pipesignal references in fev.eqy's match section to Verilog signal paths.
  # Produces in ${TEMP_MATCH_DIR}:
  # - match_lines.eqy
  # - fev.eqy (with Verilog names)
  # - fev.eqy.upd (with match section removed)
  ${script_dir}/map_match_pipesignals.py "${TEMP_MATCH_DIR}" fev.eqy match_lines.eqy
  if [[ $? -ne 0 ]]; then
    update_status 3 "Failed to map TLV pipesignals to Verilog in fev.eqy. (See work in ${TEMP_MATCH_DIR})" || exit $?
  fi


  # Run incremental FEV (vs. feved.sv)
  run_fev "incremental_fev" "fev" 3 "Incremental FEV failed" || exit $?

  # Incremental FEV succeeded. Record history, copy wip to feved, and copy match_lines.eqy (to incorporate into fev_full*.eqy) and updated fev.eqy.
  # Record history.
  mkdir -p ${NEXT_HISTORY_DIR}
  rm -f history/latest
  ln -s ../${NEXT_HISTORY_NAME} history/latest
  cp wip.tlv ${NEXT_HISTORY_DIR}
  cp feved.tlv ${NEXT_HISTORY_DIR}
  cp fev.eqy ${NEXT_HISTORY_DIR}
  cp status.json ${NEXT_HISTORY_DIR}
  echo "Incremental FEV succeeded. Updated feved.tlv and feved.sv."
  echo "Recorded wip.tlv in ${NEXT_HISTORY_DIR}"
  # Copy wip to feved
  cp wip.tlv feved.tlv
  cp wip.sv feved.sv
  # Make wip.tlv read-only to prevent changes until full FEV is done.
  chmod 400 wip.tlv
  # Copy match_lines.eqy and updated fev.eqy.
  cp ${TEMP_MATCH_DIR}/match_lines.eqy .
  cp -f ${TEMP_MATCH_DIR}/fev.eqy.upd fev.eqy

fi



###########################
# Update fev_full Matches #
###########################

# Apply match_lines.eqy to fev_full*.eqy.
# If this step fails, it has not modified any files and can be retried by a subsequent run.
# If it succeeds, it empties match_lines.eqy, indicating success for subsequent runs of `fev.sh`.
# If match_lines.eqy is missing or empty, this step is skipped.
if [[ -s match_lines.eqy ]]; then
  echo "Applying match_lines.eqy to fev_full*.eqy..."
  ${script_dir}/update_full_match.py "${TEMP_MATCH_DIR}"
  if [[ $? -ne 0 ]]; then
    update_status 4 "Failed to update fev_full*.eqy match section by applying match_lines.eqy." || exit $?
  fi
else
  echo "Skipping application of match_lines.eqy to fev_full*.eqy (not present or empty)."
fi



############
# Full FEV #
############

# Run full FEV (vs. prepared.sv) for all parameter sets (fev_full*.eqy, default first).
shopt -s nullglob
for fev_file in fev_full.eqy fev_full_*.eqy; do
  # Strip '.eqy'
  full_fev=${fev_file%.eqy}
  # Map TL-Verilog pipesignal references in fev_full*.eqy's match section to Verilog signal paths,
  # producing <temp-dir>/fev_full*.eqy files.
  ${script_dir}/map_match_pipesignals.py "${TEMP_MATCH_DIR}" "${fev_file}"
  if [[ $? -ne 0 ]]; then
    update_status 4 "Failed to map TLV pipesignals to Verilog in ${fev_file}. (See work in ${TEMP_MATCH_DIR})" || exit $?
  fi
  # Run full FEV
  if ! run_fev "$full_fev" "$full_fev" 4 "Full FEV (${full_fev}) failed"; then
    echo "See 'full_fev_failed.md' for guidance."
    exit $?
  fi
  # Make wip.tlv writable again (effective after fev_full.eqy run; others may need wip.tlv changes).
  chmod 600 wip.tlv
done
shopt -u nullglob

## Full FEV succeeded. Record history.
# Copy fev_full.eqy to history
cp fev_full*.eqy ${NEXT_HISTORY_DIR}/
cp -f status.json ${NEXT_HISTORY_DIR}/
ln -s ../../prepared.sv ${NEXT_HISTORY_DIR}/prepared.sv
# Remove match_lines.eqy as an indication of completion.
rm match_lines.eqy

# Success
echo "Refactoring step successful!"
update_status 0 "Refactoring step (not task) successful!"

