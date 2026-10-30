PY=C:/Users/seanl/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe
M=CatalanCore.Uniform.Bank.SeventhsContent
sub(){ $PY -I -X utf8 scripts/claude/lanes.py submit $1 3 >> scratch/sevenths_build.log 2>&1; echo "== $1 rc $?" >> scratch/sevenths_build.log; }
sub $M.AutoData.Head
for j in 1 2 3 4 5 6; do for k in 0 1 2; do echo $M.AutoData.U${j}P$k; done; done | xargs -P 3 -I{} bash -c "source scratch/sevenths_fn.sh; sub {}"
for j in 1 2 3 4 5 6; do echo $M.AutoData.U$j; done | xargs -P 3 -I{} bash -c "source scratch/sevenths_fn.sh; sub {}"
sub $M.AutoData
sub $M.Auto
sub $M.AutoMeasure
sub $M.Bound
