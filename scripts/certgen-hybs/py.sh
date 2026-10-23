#!/bin/bash
# usage: py.sh <logname> <budgetGB> <script args...>   (runs python through the guard, log in certlogs)
LOGN="$1"; B="$2"; shift 2
LOGD="C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/shift-nonclean-2026-10-22/certlogs"
powershell -NoProfile -ExecutionPolicy Bypass -File C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/tools/guard.ps1 -Kind python -Dir C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-shift/scripts/certgen-hybs -BudgetGB $B -Exe C:/Users/seanl/AppData/Local/Programs/Python/Python313/python.exe -ArgString "$*" > "$LOGD/py-$LOGN.log" 2>&1
echo "exit=$?" >> "$LOGD/py-$LOGN.log"
