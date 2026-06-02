#!/bin/bash
# Counter regression: builds counter.v + counter_tb.v with Verilator, runs the
# simulation, and compares the $monitor trace against a golden reference so that
# a behavioral mismatch (not just a compile error) fails the regression.
#
# Quiet on success; prints the build log location and trace diff on failure.
# Full logs: $LOG_DIR/{build.log,sim.log}.
set -u

PROJ=/workspace/proj
GOLDEN="$PROJ/tlv/regress/counter.golden"
LOG_DIR="$PROJ/tlv/regress/logs"
mkdir -p "$LOG_DIR"
cd "$PROJ"

fail() { echo "REGRESSION FAILED: $1"; exit 1; }

# --- Build -----------------------------------------------------------------
if ! verilator --binary -j 0 --top counter_tb counter.v counter_tb.v \
        -o sim_counter >"$LOG_DIR/build.log" 2>&1; then
    echo "--- build.log (tail) ---"; tail -20 "$LOG_DIR/build.log"
    fail "Verilator build error (see $LOG_DIR/build.log)"
fi

# --- Simulate --------------------------------------------------------------
./obj_dir/sim_counter >"$LOG_DIR/sim.log" 2>&1 \
    || fail "simulation crashed (see $LOG_DIR/sim.log)"

# Extract the trace lines the golden reference tracks.
grep -E '^t=' "$LOG_DIR/sim.log" > "$LOG_DIR/trace.txt"

# --- Golden compare --------------------------------------------------------
[ -f "$GOLDEN" ] || fail "missing golden file $GOLDEN"

if ! diff -u "$GOLDEN" "$LOG_DIR/trace.txt" > "$LOG_DIR/trace.diff"; then
    echo "--- trace does not match golden (expected < , got >) ---"
    cat "$LOG_DIR/trace.diff"
    fail "output mismatch vs $GOLDEN"
fi

echo "REGRESSION PASSED (trace matches golden, $(wc -l < "$GOLDEN") lines)"
