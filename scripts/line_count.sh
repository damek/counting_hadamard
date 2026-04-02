#!/usr/bin/env bash
# Total line count for all active Lean source files.
cd "$(dirname "$0")/.." || exit 1
wc -l RequestProject/*.lean | tail -1
echo ""
wc -l RequestProject/*.lean
