#!/bin/bash

# A supporting script for the instructions in instructions/desktop_agent_instructions.md.

# Usage: ./fev.sh
# Run from the directory containing the TLV file(s).

# This script involves four idempotent steps, performed atomically.
# Any of these four steps that have already been completed will be skipped or safely repeated
# until all have succeeded.
# All work is done in a temporary directory, and captured on success after each step.
# match_lines.eqy lists signal/pipesignal mappings for incremental FEV and serves
# also as an indication of which steps have been completed.
#
# Steps are:
# - SandPiper
#   - Run SandPiper on wip.tlv for all configurations, defining the Verilog files against which
#     FEV is run.
# - Incremental FEV:
#   - Map pipesignal paths in fev.eqy [match ...] section to signal paths (using SandPiper)
#   - Run eqy with updated fev.eqy.
# - Update fev_full Matches
#   - Incorporating match_lines.eqy into fev_full*.eqy
# - Full FEV
#   - Map pipesignal paths in fev_full*.eqy [match ...] sections to signal paths (using SandPiper)
#   - Run eqy for fev_full*.eqy, verifying wip*.sv vs. prepared.sv for various parameter values.
#
# These update local files (match_lines.eqy, feved.tlv, and *.sv) on success (or repeatably)
# as follows:
# - SandPiper:
#   - wip.tlv -> wip_*.sv (for all `config.json` M5_configs, or `wip.sv` if none)
#   - wip.sv (from SandPiper if no M5_configs, or as a symlink to the corresponding wip_*.sv)
# - Incremental FEV:
#   - match_lines.eqy is extracted from fev.eqy
#   - [DISABLED--PROBLEMATIC] wip.tlv is made read-only
#   - feved.tlv is updated from wip.tlv (and feved.sv from wip.sv)
# - Update fev_full Matches:
#   - match_lines.eqy is emptied
# - Full FEV:
#   - [DISABLED--PROBLEMATIC] wip.tlv is made writable again after passing fev_full.eqy (fev_full_*.eqy may still fail and
#     could need wip.tlv changes)
#   - match_lines.eqy is removed
#   - fully_feved.tlv is updated from wip.tlv (and all *.sv are copied in `full_sv/` for reference)
#
# They update history/#/ with:
# - SandPiper: nothing
# - Incremental FEV: `wip.tlv`, `feved.tlv`, and `fev.eqy`, `status.json`
# - Update fev_full Matches: nothing
# - Full FEV: `fev_full*.eqy` and `prepared.sv` (as a symlink), `status.json`

# TODO: This should be a Makefile (though that would run the risk of agent edits to intermediate files).

set -uo pipefail
shopt -s nullglob


# No arguments should be given.
if [[ $# -ne 0 ]]; then
  echo "Usage: $0"
  exit 1
fi


####################
# Common Functions #
####################

# Update status.json to indicate failure. Preserve "task", and "llm" properties. Write "fev.sh" with, "$status: $msg".
# Return the give status.
# Usage example: update_status 1 "file not found" || exit $?
function update_status() {
  local status="$1"
  local msg="$2"
  # Update status.json.
  jq --argjson s "$status" --arg msg "$msg" '
    .["fev.sh"] = ("\($s): " + $msg) |
    .fev_cnt = if $s == 0 then 0 else ((.fev_cnt // 0) + 1) end
  ' status.json > status.tmp.json && mv status.tmp.json status.json
  echo 'Updated the `fev.sh` and `fev_cnt` properties of `status.json`: '"$status: $msg"
  echo
  if [[ $status -ne 0 ]]; then
    echo "Try a smaller change, or, if you are having trouble making forward progress,"
    echo "reread the instructions in 'instructions/desktop_agent_instructions.md' for ideas and double-check your work."
  fi
  echo 'Remember to update the `llm` property of `status.json` and possibly `tracker.md` to reflect:'
  echo 'your progress, and continue the task.'
  return $status
}

# Write an interim (non-terminal) `fev.sh` status without bumping `fev_cnt`.
# Used to clear a stale failure at the start of a run, and to mark incremental
# forward progress before the terminal (success/failure) status is known.
function set_status() {
  local msg="$1"
  jq --arg msg "$msg" '.["fev.sh"] = $msg' status.json > status.tmp.json && mv status.tmp.json status.json
}

# Snapshot the current state into the history directory so each checkpoint is
# self-contained for review. Called after status.json reflects the outcome
# (success or failure) so the recorded status is meaningful, not a stale one.
# Copies whatever artifacts are present and is safe to call repeatedly for the
# same directory (success refreshes the directory recorded on incremental pass).
function record_history() {
  "${script_dir}/record_history.sh" "${NEXT_HISTORY_DIR}" > /dev/null
}

# Record a failure status, snapshot the history, and exit. Usage: fail <status> <msg>
function fail() {
  update_status "$1" "$2"
  record_history
  exit "$1"
}

# Snapshot the history and exit with the given status, for failures where run_tool
# already set the status. Usage: record_and_exit <status>
function record_and_exit() {
  record_history
  exit "$1"
}

# True if the previous history checkpoint recorded a passing (terminal) fev.sh
# status. Used to avoid reusing (overwriting) a directory that holds a recorded
# failure attempt.
function prev_is_pass() {
  local f="history/$(printf "%03d" "${PREV_HISTORY_NUM}")/status.json"
  [[ -f "$f" ]] && [[ "$(jq -r '.["fev.sh"] // ""' "$f" 2>/dev/null)" == 0:* ]]
}

# Run a tool command, logging output to TEMP_DIR and returning the given exit status or failure or 0 on success.
function run_tool() {
  local job="$1"
  local tool_cmd="$2"
  local fail_status="$3"
  local fail_msg="$4"
  local cmd="timeout 120s $tool_cmd > ${TEMP_DIR}/${job}.log 2>&1"
  echo "Running: $cmd"
  eval "$cmd"
  exit_code=$?
  if [[ $exit_code -ne 0 ]]; then
    if [[ $exit_code -eq 124 ]]; then
      $fail_msg="Timeout running: $tool_cmd"
    fi
    # Output the log for diagnosis.
    #cat "${TEMP_DIR}/${job}.log"
    # Record failure status and message.
    update_status "$fail_status" "$fail_msg"
    # Report error.
    echo
    echo "FATAL ERROR: $fail_msg"
    echo "   Failing command: $cmd"
    return $fail_status
  else
    echo
    #echo "Successfully ran: $tool_cmd"
    return 0
  fi
}

function run_sandpiper() {
  local file="wip"
  local config="$1"
  local config_m5def="$2"

  local config_suffix="$config"
  local config_desc="default"
  # If config is non-empty, prepend '_' to it.
  if [[ -n "$config_suffix" ]]; then
    config_suffix="_$config_suffix"
    config_desc="$config"
  fi
  local sv_file="${file}${config_suffix}.sv"
  rm -f ${sv_file}
  run_tool "sandpiper_${file}${config_suffix}" "sandpiper-saas -i ${file}.tlv -o ${sv_file} ${config_m5def} --inlineGen --noline --iArgs" 2 "SandPiper failed for ${file}.tlv -> ${sv_file}"
  status=$?
  if [[ $status -ne 0 ]]; then
    # Output the log.
    echo
    echo "SandPiper log for ${file}.tlv -> ${sv_file}:"
    echo
    cat "${TEMP_DIR}/sandpiper_${file}${config_suffix}.log"
    echo
    echo "More information on some SandPiper messages can be found in sandpiper_messages.md."
    echo
    record_and_exit $status
  fi
  if [[ ! -f ${sv_file} ]]; then
    # If SandPiper returns 0 but the output file is missing, its presumably because the file
    # was not a TLV file so copy it to the output file.
    echo "SandPiper did not produce ${sv_file}; presuming ${file}.tlv is Verilog."
    cp ${file}.tlv ${sv_file}
  fi
}


# A variant of run_tool specialized for eqy commands.
function run_fev() {
  local job="$1"
  local fev_name="$2"
  local fail_status="$3"
  local fail_msg="$4"
  local fev_out_dir="${TEMP_DIR}/${fev_name}"
  local cmd="time eqy -d ${fev_out_dir} ${TEMP_MATCH_DIR}/${fev_name}.eqy"
  run_tool "$job" "$cmd" "$fail_status" "$fail_msg"
  status=$?
  if [[ $status -ne 0 ]]; then
    if [[ -d ${fev_out_dir} && -d ${fev_out_dir}/strategies ]]; then
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
    if [[ $job != "incremental_fev" ]]; then
      echo "Fix FEV failures before further refactoring. See 'instructions/full_fev_failed.md' for guidance."
    fi
  fi
  return $status
}



#################
# Preconditions #
#################

for file in config.json wip.tlv prepared.sv feved.tlv fev.eqy status.json; do
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
if [[ NEXT_HISTORY_NUM -eq "1000" ]]; then
  echo "ERROR: Reached maximum history limit of 999."
  exit 1
fi
while [[ -d history/$(printf "%03d" "${NEXT_HISTORY_NUM}") ]]; do
  NEXT_HISTORY_NUM=$((NEXT_HISTORY_NUM + 1))
done
PREV_HISTORY_NUM=$((NEXT_HISTORY_NUM - 1))
# NEXT_HISTORY_DIR assigned later.

# See whether full FEV was completed previously.
if [[ -e match_lines.eqy ]]; then
  NEED_FULL_FEV=true
else
  NEED_FULL_FEV=false
fi
diff -q wip.tlv feved.tlv > /dev/null
diff_status=$?
if [[ $NEED_FULL_FEV == true ]]; then
  # Source files should be unchanged since last FEV.
  if [[ $diff_status -ne 0 ]]; then
    echo "Uh oh! Full FEV (vs. prepared.sv) was not completed previously, but wip.tlv has been updated."
    echo "If you made these changes to address failures with non-default parameters, no worries."
    echo "Otherwise, it is always best to resolve full FEV failures before proceeding. We'll test your"
    echo "new changes anyway. In case of failure, it is recommended to revert wip.tlv to feved.tlv and"
    echo "get full FEV passing. Reference 'instructions/full_fev_failed.md' for guidance."
    # Keep the old history, even though full FEV failed.
    NEED_FULL_FEV=false
  else
    echo "Running full FEV only (failed previously)."
    # Continue ongoing work in previous history directory, only running full FEV.
    NEXT_HISTORY_NUM=$PREV_HISTORY_NUM
  fi
elif [[ $diff_status -eq 0 && $NEXT_HISTORY_NUM -gt 1 ]] && prev_is_pass; then
  echo "wip.tlv is unchanged from previously passing (at least incremental) FEV. Reusing history/$(printf "%03d" "${PREV_HISTORY_NUM}"))."
  NEXT_HISTORY_NUM=$PREV_HISTORY_NUM
fi
NEXT_HISTORY_NAME=$(printf "%03d" "${NEXT_HISTORY_NUM}")
NEXT_HISTORY_DIR=history/${NEXT_HISTORY_NAME}

# Clear any stale fev.sh status from a prior attempt so a recorded checkpoint reflects
# this run, not a previous failure. fev_cnt is preserved for loop detection.
set_status "fev.sh running."


# Create, scrub, and initialize a local (visible to agent) temporary directory.
mkdir -p tmp

# Scrub the /tmp directory of directories older than 2 day and keep at most 5.
find ./tmp -mindepth 1 -maxdepth 1 -type d -mtime +2 -exec rm -rf {} +; \
ls -1dt ./tmp/*/ 2>/dev/null | tail -n +6 | xargs -r rm -rf

TEMP_NAME="$(cd tmp && mktemp -d XXXXX)"
TEMP_DIR="./tmp/${TEMP_NAME}"
echo "Verifying changes in: $TEMP_DIR"
TEMP_MATCH_DIR=${TEMP_DIR}/match
mkdir ${TEMP_MATCH_DIR}
rm -f ./tmp/latest
ln -s ${TEMP_NAME} ./tmp/latest


# wip.sv should exist if we NEED_FULL_FEV.
MISSING_SV=false
if [[ $NEED_FULL_FEV == true && ! -f wip.sv ]]; then
  echo "ERROR: Something went wrong. wip.sv is missing. Repeating SandPiper and incremental FEV."
  MISSING_SV=true
fi


if [[ $NEED_FULL_FEV == false || $MISSING_SV == true ]]; then
  # Attempt to run incremental FEV (vs. feved.sv).
  # Success updates history and creates match_lines.eqy for updating full FEV configs.


  #################
  # Run SandPiper #
  #################

  # Remove all wip*.sv files/links to ensure they are regenerated and to know which is the one generated by incremental FEV.
  rm -f wip*.sv

  # Run SandPiper on wip.tlv and feved.tlv for all configurations in `config.json`'s `configs` list,
  # or call run_sandpiper "" "" if none present.
  M5_configs=$(jq -r 'if has("M5_configs") then .M5_configs | to_entries[] | "\(.key):\(.value)" else empty end' config.json 2>/dev/null || true)
  if [[ -z "$M5_configs" ]]; then
    run_sandpiper "" ""
  else
    IFS=$'\n'
    for entry in $M5_configs; do
      key="${entry%%:*}"
      value="${entry#*:}"
      run_sandpiper "$key" "$value"
    done
    unset IFS

    # Create wip.sv as a symlink to the default configuration's wip_*.sv.
    ln -s wip_$(jq -r '.default_config' config.json 2>/dev/null || echo "").sv wip.sv
  fi



  ###################
  # Incremental FEV #
  ###################

  # Map TL-Verilog pipesignal references in fev.eqy's match section to Verilog signal paths.
  # Produces in ${TEMP_MATCH_DIR}:
  # - match_lines.eqy
  # - fev.eqy (with Verilog names)
  # - fev.eqy.upd (with match section removed)
  ${script_dir}/map_match_pipesignals.py "${TEMP_MATCH_DIR}" fev.eqy match_lines.eqy
  if [[ $? -ne 0 ]]; then
    fail 3 "Failed to map TLV pipesignals to Verilog in fev.eqy. (See work in ${TEMP_MATCH_DIR})"
  fi


  # Run incremental FEV (vs. feved.sv)
  run_fev "incremental_fev" "fev" 3 "Incremental FEV failed"
  incremental_status=$?
  if [[ $incremental_status -ne 0 ]]; then
    if [[ $diff_status -eq 0 ]]; then
      echo "Since wip.tlv is unchanged from feved.tlv, incremental FEV failure indicates a problem with the match list."
      if [[ $NEXT_HISTORY_NUM -gt 1 ]]; then
        echo "Since this is the initial FEV run, the match list *should* be empty. We have run into situations where a module"
        echo "fails to FEV against itself. At that time 'group *' seemed to blame, and it was squashing vectors to bits. Help the"
        echo "user to further isolate the issue and improve the process."
      fi
      echo "Please review and update the match list in fev.eqy (see 'improving_signal_matching.md' for guidance) before retrying."
    fi
    echo "Incremental FEV failed"
    # TODO: Need better instructions for the agent specific to incremental FEV failure.
    record_and_exit $incremental_status
  fi

  # Incremental FEV succeeded. Record forward progress, copy wip to feved, and copy
  # match_lines.eqy (to incorporate into fev_full*.eqy) and updated fev.eqy.

  # Mark incremental progress before recording so the checkpoint reflects this run
  # rather than a prior failure. The terminal status is set after full FEV below.
  set_status "Incremental FEV passed. Running full FEV."
  record_history
  echo "Incremental FEV succeeded. Updated feved.tlv and feved.sv."
  echo "Recorded wip.tlv in ${NEXT_HISTORY_DIR}"
  
  # Checkpoint (not in history/) wip to feved. Our policy is for feved.tlv to be read-only.
  # Remove before copying to avoid a permission issue if feved.tlv's owner changes.
  rm -f feved.tlv
  cp wip.tlv feved.tlv
  chmod -w feved.tlv
  # Copy wip.sv (which might be a symlink) to feved.sv (just for reference).
  cp wip.sv feved.sv


  # Make wip.tlv read-only to prevent changes until full FEV is done--this didn't work. GH Copilot makes changes that fail to save.
  #chmod -w wip.tlv
  # Copy match_lines.eqy and updated fev.eqy.
  cp ${TEMP_MATCH_DIR}/match_lines.eqy .
  cp ${TEMP_MATCH_DIR}/fev.eqy.upd fev.eqy

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
    fail 4 "Failed to update fev_full*.eqy match section by applying match_lines.eqy."
  fi
else
  echo "Skipping application of match_lines.eqy to fev_full*.eqy (not present or empty)."
fi



############
# Full FEV #
############

# Run full FEV (vs. prepared.sv) for all parameter sets (fev_full*.eqy, default first).
for fev_file in fev_full.eqy fev_full_*.eqy; do
  # Strip '.eqy'
  full_fev=${fev_file%.eqy}
  # Map TL-Verilog pipesignal references in fev_full*.eqy's match section to Verilog signal paths,
  # producing <temp-dir>/fev_full*.eqy files.
  ${script_dir}/map_match_pipesignals.py "${TEMP_MATCH_DIR}" "${fev_file}"
  if [[ $? -ne 0 ]]; then
    fail 4 "Failed to map TLV pipesignals to Verilog in ${fev_file}. (See work in ${TEMP_MATCH_DIR})"
  fi
  # Run full FEV
  run_fev "$full_fev" "$full_fev" 4 "Full FEV (${full_fev}) failed" || record_and_exit $?
  # Make wip.tlv writable again (effective after fev_full.eqy run; others may need wip.tlv changes).
  chmod +w wip.tlv   # (no longer made read-only earlier)
done

# Full FEV succeeded.

# Copy wip.tlv to fully_feved.tlv (read-only) as a record of the fully feved state.
rm -f fully_feved.tlv
cp wip.tlv fully_feved.tlv
chmod -w fully_feved.tlv
# Record history. Set the terminal success status first so the checkpoint records it.
if ! cmp -s config.json ${NEXT_HISTORY_DIR}/config.json; then
  echo "WARNING: config.json changed since incremental FEV. History may be inconsistent."
fi
update_status 0 "All FEV runs successful! History updated."
record_history
cp fev_full*.eqy ${NEXT_HISTORY_DIR}/
rm -f ${NEXT_HISTORY_DIR}/prepared.sv
ln -s ../../prepared.sv ${NEXT_HISTORY_DIR}/prepared.sv
# Remove match_lines.eqy as an indication of completion.
rm match_lines.eqy
if (( $PREV_HISTORY_NUM != $NEXT_HISTORY_NUM )); then
  echo "History recorded in ${NEXT_HISTORY_DIR}."
else
  echo "History updated in ${NEXT_HISTORY_DIR}."
fi

# Copy wip_*.sv into full_sv/.
mkdir -p full_sv
rm -f full_sv/wip*.sv
cp wip*.sv full_sv/

# Report success
echo
echo "All FEV runs successful!"

