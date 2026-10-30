#!/bin/bash
# usage: errs.sh Module [ctx] [maxlines]  -> error blocks of the newest build log of Module
D="C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/logs"
N=$(echo $1 | tr . _)
L=$(ls -t "$D"/${N}-build-2*.log 2>/dev/null | head -1)
[ -z "$L" ] && L="$D/${N}-build.log"
echo "== $L"
grep -n "^error" -A${2:-18} "$L" | cut -c1-260 | head -${3:-120}
