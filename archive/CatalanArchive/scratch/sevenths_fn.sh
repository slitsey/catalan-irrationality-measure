PY=C:/Users/seanl/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe
sub(){ $PY -I -X utf8 scripts/claude/lanes.py submit $1 3 >> scratch/sevenths_build.log 2>&1; echo "== $1 rc $?" >> scratch/sevenths_build.log; }
