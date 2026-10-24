#!/bin/bash
# usage: b.sh <Module> [BudgetGB]   (module name without the CatalanCore.Cert.SigmaHybS prefix unless it contains a dot)
M="$1"; B="${2:-3}"
case "$M" in *.*) FULL="$M";; *) FULL="CatalanCore.Cert.SigmaHybS.$M";; esac
LOGD="C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/shift-nonclean-2026-10-22/certlogs"
mkdir -p "$LOGD"
T0=$(date +%s)
for TRY in $(seq 1 40); do
powershell -NoProfile -ExecutionPolicy Bypass -File C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/tools/guard.ps1 -Kind lean -Dir C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-shift -BudgetGB $B -Exe C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/lean-runtime/lean-4.35.0-rc2-windows/bin/lake.exe -ArgString "build $FULL" > "$LOGD/build-$FULL.log" 2>&1
RC=$?
if [ "$RC" = "98" ] || [ "$RC" = "99" ]; then echo "retry $TRY (exit $RC)" >> "$LOGD/retries.txt"; sleep $((20 + RANDOM % 40)); continue; fi
break
done
echo "exit=$RC secs=$(( $(date +%s)-T0 ))" >> "$LOGD/build-$FULL.log"
echo "$FULL exit=$RC secs=$(( $(date +%s)-T0 ))" >> "$LOGD/_summary.txt"
