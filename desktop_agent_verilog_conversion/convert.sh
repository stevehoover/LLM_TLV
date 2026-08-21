#!/bin/bash

# Automated Verilog-to-TL-Verilog conversion launcher.
#
# Usage:
#   ./convert.sh <project-name> <module-name>
#
# Examples:
#   ./convert.sh stevehoover-serv serv_ctrl
#   ./convert.sh ibex ibex_csr
#   ./convert.sh Cores-VeeR-EL2 el2_prim_generic_buf

set -e

PROJECT="$1"
MODULE="$2"

if [ -z "$PROJECT" ] || [ -z "$MODULE" ]; then
    echo "Usage: ./convert.sh <project-name> <module-name>"
    echo ""
    echo "Examples:"
    echo "  ./convert.sh stevehoover-serv serv_ctrl"
    echo "  ./convert.sh ibex ibex_csr"
    echo "  ./convert.sh Cores-VeeR-EL2 el2_prim_generic_buf"
    exit 1
fi

PROJECT_ROOT="/workspace/proj/$PROJECT"

if [ ! -f "$HOME/.anthropic/key.txt" ]; then
    echo "Error: Anthropic API key not found at ~/.anthropic/key.txt"
    exit 1
fi

echo "Starting conversion..."
echo "Project: $PROJECT"
echo "Module:  $MODULE"
echo ""

cd "$HOME/gsoc/$PROJECT/tlv/env" 2>/dev/null || {
    echo "Error: could not find local project at:"
    echo "  $HOME/gsoc/$PROJECT/tlv/env"
    exit 1
}

docker compose run --rm \
    -e ANTHROPIC_API_KEY="$(cat "$HOME/.anthropic/key.txt")" \
    claude-conversion \
    bash -lc "
        cd $PROJECT_ROOT/tlv &&
        claude -p \"Follow the instructions in $PROJECT_ROOT/tlv/project_instructions/desktop_agent_instructions.md to convert $MODULE from Verilog to TL-Verilog.\"
    "
