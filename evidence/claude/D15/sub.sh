#!/bin/bash
# usage: sub.sh Module GB
cd "C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform"
C:/Users/seanl/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe -I -X utf8 scripts/claude/lanes.py submit "$1" "${2:-3}" 2>&1
