#!/bin/bash
# usage: queue.sh <lanes> <budgetGB> <listfile>
LANES="$1"; B="$2"; LST="$3"
cd C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-shift
cat "$LST" | xargs -P "$LANES" -I{} bash -c 'sleep $((RANDOM % 20)); bash scripts/certgen-hybs/b.sh {} '"$B"
