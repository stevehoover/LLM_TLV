#!/bin/bash

# Automated Verilog-to-TL-Verilog conversion launcher.
#
# Run this from the root of the Verilog project being converted.
#
# Usage:
#   <path-to>/convert.sh <module-name>
#
# Example:
#   /path/to/LLM_TLV/desktop_agent_verilog_conversion/convert.sh serv_ctrl

set -e

MODULE="$1"

if [ -z "$MODULE" ]; then
    echo "Usage: $0 <module-name>"
    exit 1
fi

PROJECT_ROOT="$(pwd)"

# Verify that this is a prepared conversion project.
if [ ! -f "$PROJECT_ROOT/tlv/env/docker-compose.yml" ]; then
    echo "Error: tlv/env/docker-compose.yml not found."
    echo "Run this script from the root of a project prepared for TL-Verilog conversion."
    exit 1
fi

# Verify that the requested module has been prepared.
if [ ! -f "$PROJECT_ROOT/tlv/$MODULE/orig.sv" ]; then
    echo "Error: tlv/$MODULE/orig.sv not found."
    echo "Prepare the module with prep.sh before running conversion."
    exit 1
fi

# Find the API key.
if [ -n "$ANTHROPIC_API_KEY" ]; then
    API_KEY="$ANTHROPIC_API_KEY"
elif [ -f "$HOME/.anthropic/key.txt" ]; then
    API_KEY="$(cat "$HOME/.anthropic/key.txt")"
else
    echo "Error: Anthropic API key not found."
    echo "Set ANTHROPIC_API_KEY or create ~/.anthropic/key.txt."
    exit 1
fi

echo "Starting conversion..."
echo "Project: $PROJECT_ROOT"
echo "Module:  $MODULE"
echo ""

cd "$PROJECT_ROOT/tlv/env"

docker compose run --rm \
    -e ANTHROPIC_API_KEY="$API_KEY" \
    claude-conversion \
    bash -lc "cd /workspace/proj && claude -p \"Follow the instructions in tlv/project_instructions/desktop_agent_instructions.md to convert $MODULE from Verilog to TL-Verilog.\""
