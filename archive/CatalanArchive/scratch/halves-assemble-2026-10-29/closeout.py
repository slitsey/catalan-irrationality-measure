"""Coordinator close-out of the halves (pi^2) cover and bound, 29 Oct.
Pieces (validated: T0-T4 and L contiguous on [0,1], cap contiguous on [-r0,0], 0 FAIL):
  gen_0.out (T0,T2,T4; Codex slice 0), gen_1.out (T1; Codex slice 1), gen_2.out (T3, L; fast mode),
  cap = scratch/halves-cpcap-2026-10-29/gen_0.out (split-rule CP), energy gen2_0/1.out, gen2G_0.out (rc 0).
Steps: emit (Dt must equal the receipt's D_lower) -> cover build (parallel 2) -> lift the HalvesContent.Bound hold
(Sean: build pi2_measure once LP2 and the prefix layer are settled; both are, at depth 8) -> Bound -> Audit.
Run from work/catalan-uniform."""
from pathlib import Path
import json, re, subprocess, sys, time, shutil
from fractions import Fraction
R = Path.cwd(); A = R/'scratch/halves-assemble-2026-10-29'; PY = sys.executable
CAP = R/'scratch/halves-cpcap-2026-10-29/gen_0.out'
REC = Path('C:/Users/seanl/Documents/Codex/2026-10-29/handoff-codex-2026-10-29-halves/exact-HALF.json')
COVER = 'CatalanCore.Uniform.Bank.Halves.Cover'; BOUND = 'CatalanCore.Uniform.Bank.HalvesContent.Bound'
LANES = R/'scripts/claude/lanes.py'; CV = R/'scripts/claude/bank/cover/cover.py'
HOLD = R/'../tools/lanes/hold.txt'
def event(phase, **kw):
    d = dict(time=time.strftime('%Y-%m-%d %H:%M:%S'), phase=phase, **kw)
    with (A/'closeout-events.jsonl').open('a', encoding='utf-8') as f: f.write(json.dumps(d)+'\n')
    print(json.dumps(d), flush=True)
def run(args, name, check=True):
    with (A/name).open('w', encoding='utf-8') as f:
        p = subprocess.run([str(x) for x in args], stdout=f, stderr=subprocess.STDOUT, cwd=R)
    t = (A/name).read_text(encoding='utf-8', errors='replace'); event(name, rc=p.returncode)
    if check and p.returncode: raise RuntimeError(name+' failed: '+t[-2000:])
    return t
try:
    mods = list((R/'CatalanCore/Uniform/Bank/Halves/Cover').glob('*.lean'))
    assert [m.name for m in mods] == ['Env0.lean'], 'Halves/Cover has more than Env0: '+str(mods)
    run([PY, '-I', '-X', 'utf8', CV, 'emit', 'Halves', '--mod', COVER, '--scratch', A, '--capfile', CAP], 'emit.log')
    q = json.loads((A/'emit_summary.json').read_text()); ex = json.loads(REC.read_text())
    assert Fraction(q['Dt']) == Fraction(ex['D_lower']), ('Dt mismatch', q['Dt'], ex['D_lower'])
    event('emitted', summary=q)
    t = run([PY, '-I', '-X', 'utf8', CV, 'build', 'Halves', '--mod', COVER, '--scratch', A, '--parallel', '2'], 'cover-build.log')
    assert not re.search(r'^FAIL ', t, re.M) and 'failed []' in t, t[-2000:]
    event('cover-built')
    h = HOLD.read_text(encoding='utf-8'); shutil.copy2(HOLD, str(HOLD)+'.bak-halves')
    new = ''.join(l for l in h.splitlines(True) if not l.startswith(BOUND+' '))
    new += '# 29 Oct ~17:35: '+BOUND+' lifted (Sean: build pi2_measure once LP2 and prefix are settled; both done at depth 8)\n'
    HOLD.write_text(new, encoding='utf-8'); event('hold-lifted')
    t = run([PY, '-I', '-X', 'utf8', LANES, 'submit', BOUND, '4'], 'bound-build.log', False)
    assert 'Build completed successfully' in t, 'Bound did not build: '+t[-3000:]
    event('bound-built')
    run([PY, '-I', '-X', 'utf8', LANES, 'run', 'HalvesAudit', '3', '--',
         'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/lean-runtime/lean-4.35.0-rc2-windows/bin/lake.exe',
         'env', 'lean', 'CatalanCore/Uniform/Bank/HalvesContent/Audit.lean'], 'audit.log')
    event('complete')
except Exception as e:
    event('stopped', error=str(e)); raise
