"""Full trial-A cover through the validated shared generator and guarded admission."""
from pathlib import Path
from types import SimpleNamespace
import importlib.util, json, sys, time
from concurrent.futures import ThreadPoolExecutor
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path.insert(0,str(HERE))
import admit
spec=importlib.util.spec_from_file_location('shared_cover',ROOT/'scripts/claude/bank/cover/cover.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
# Smaller independent cell and energy modules preserve the bank's 2.5 GB leaf limit.
c.BLK_TUBE=4;c.BLK_LINE=4;c.BLK_CAP=4;c.ROWS_PER_MOD=1
scratch=HERE/'decay-cover'
C=c.Ctx('Sev1','CatalanCore.Uniform.Bank.Sevenths.Cover',str(scratch))
a=SimpleNamespace(K=24,J=12,centre=None,slices=12,eslices=4,gb=2.5,
                  capmode='CP',cmd='gen',capfile=None)
def checkpoint(phase,**kw):
    (HERE/'decay-campaign.json').write_text(json.dumps(dict(phase=phase,time=time.time(),**kw),indent=2)+'\n')
    print(phase,kw,flush=True)
if not (HERE/'decay-generator-cleared.json').exists():
    checkpoint('held', reason='Await updated handoff confirming B6 generator reconciliation')
    raise SystemExit(0)
checkpoint('environment')
c.cmd_env(C)
if admit.ensure(C.mod+'.Env0'):raise SystemExit('environment failed')
checkpoint('generate')
c.cmd_gen(C,a)
checkpoint('emit')
c.cmd_emit(C,a)
mods=c.modules(C)
done=set()
while len(done)<len(mods):
    ready=[m for m,deps in mods.items() if m not in done and all(d in done for d in deps)]
    if not ready:raise RuntimeError('cyclic cover imports')
    def build(m):
        budget=8 if m.endswith(('.Check','.Decay')) else 2.5
        checkpoint('build',target=m,budget=budget,accepted=len(done),total=len(mods))
        if admit.ensure(m,budget=budget):raise SystemExit('cover module failed: '+m)
        return m
    with ThreadPoolExecutor(max_workers=3) as pool:
        done.update(pool.map(build,ready))
checkpoint('complete',accepted=len(done),total=len(mods))
