#!/bin/bash
# usage: chain.sh Mod1 Mod2 ...  (stops at first failure); prints rc, wall (incl. queue), lean wall + peak GB
cd "C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform"
for m in "$@"; do
  s=$(date +%s)
  evidence/claude/D15/sub.sh "$m" ${GB:-3} > /tmp/chain_$m.out
  rc=$?
  e=$(date +%s)
  info=$(head -1 /tmp/chain_$m.out | C:/Users/seanl/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe -X utf8 -c "
import sys,json
try:
    j=json.loads(sys.stdin.read()); pk=max(j.get('lean_process_peak_working_sets_bytes',{'x':0}).values())/2**30
    print('build_wall=%.0fs peak_lean=%.2fGB tree_peak=%.2fGB'%(j['wrapper_wall_seconds'],pk,j['sampled_wrapper_tree_peak_bytes']/2**30))
except Exception as ex: print('noinfo',ex)")
  echo "$m rc=$rc total=$((e-s))s $info"
  if [ $rc -ne 0 ]; then
    evidence/claude/D15/errs.sh $m 25 70
    exit $rc
  fi
done
