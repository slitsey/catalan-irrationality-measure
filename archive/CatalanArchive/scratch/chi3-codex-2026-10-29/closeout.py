"""Coordinator close-out of the chi_-3 decay regeneration (Codex plan of continue.py, 29 Oct), with:
- the slice-1 cap from the approved uniform-rate run (scratch/chi3-ucap-2026-10-29/gen_0.out) passed as --capfile
  (cover.py then ignores the two old cap cells left in gen_1.out);
- explicit receipt checks (Chi3Cdx0, Chi3UCap0, Chi3E0, Chi3G0 rc 0; Chi3Cdx1 stopped by Sean after its tube edges);
- cover leaves at parallel 2; final targets RankFinal (unchanged 13.7486 statement) and KContent.Bound (13.7046);
- the audit of continue.py.  Run from work/catalan-uniform."""
from pathlib import Path
import json, re, subprocess, sys, time, shutil
R = Path.cwd(); S = R/'scratch/chi3-codex-2026-10-29'; PY = sys.executable
CAP = R/'scratch/chi3-ucap-2026-10-29/gen_0.out'
COVER = 'CatalanCore.Uniform.Bank.Chi3.Cover'
TARGETS = ['CatalanCore.Uniform.Bank.Chi3Rank.RankFinal', 'CatalanCore.Uniform.Bank.Chi3.KContent.Bound']
LANES = R/'scripts/claude/lanes.py'; CV = R/'scripts/claude/bank/cover/cover.py'
def event(phase, **kw):
    d = dict(time=time.strftime('%Y-%m-%d %H:%M:%S'), phase=phase, **kw)
    with (S/'closeout-events.jsonl').open('a', encoding='utf-8') as f: f.write(json.dumps(d)+'\n')
    print(json.dumps(d), flush=True)
def run(args, name, check=True):
    with (S/name).open('w', encoding='utf-8') as f:
        p = subprocess.run([str(x) for x in args], stdout=f, stderr=subprocess.STDOUT, cwd=R)
    t = (S/name).read_text(encoding='utf-8', errors='replace'); event(name, rc=p.returncode)
    if check and p.returncode: raise RuntimeError(name+' failed: '+t[-2000:])
    return t
def imports(m):
    p = R/(m.replace('.', '/')+'.lean')
    if not p.exists(): return []
    return [x for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', p.read_text(encoding='utf-8-sig'), re.M)
            for x in line.split() if not x.startswith('--')]
def order(m):
    seen = set(); out = []
    def visit(x):
        if x in seen: return
        seen.add(x)
        for y in imports(x): visit(y)
        out.append(x)
    visit(m); return out
def receipt(label):
    best = None
    for p in (R/'../tools/lanes/done').glob('*.json'):
        j = json.loads(p.read_text(encoding='utf-8'))
        if j.get('target') == 'job.'+label and (best is None or p.stat().st_mtime > best[0]): best = (p.stat().st_mtime, j)
    return None if best is None else best[1]
try:
    event('validate')
    for n in ['gen_0.out', 'gen_1.out', 'gen2_0.out', 'gen2G_0.out']:
        p = S/n; assert p.exists() and p.stat().st_size, 'missing '+n
        assert not re.search(r'^(FAIL|.*error:)', p.read_text(encoding='utf-8'), re.M), 'bad '+n
    assert CAP.exists() and not re.search(r'^(FAIL|.*error:)', CAP.read_text(encoding='utf-8'), re.M), 'bad cap'
    for lab in ['Chi3Cdx0', 'Chi3UCap0', 'Chi3E0', 'Chi3G0']:
        j = receipt(lab); assert j is not None and j.get('rc') == 0, 'receipt '+lab
    src = R/'CatalanCore/Uniform/Bank/Chi3/Cover'; dst = R/'archive/CatalanArchive/CatalanCore/Uniform/Bank/Chi3/Cover'
    assert not dst.exists(), 'archive target exists'
    assert not subprocess.check_output(['git', 'status', '--porcelain', '--', str(src)], cwd=R).strip(), 'cover changed'
    dec = R/'CatalanCore/Uniform/Bank/Chi3New/Decay.lean'
    assert dec.read_bytes() == (S/'Decay.before.lean').read_bytes(), 'decay changed concurrently'
    dst.parent.mkdir(parents=True, exist_ok=True)
    run(['git', 'mv', src, dst], 'closeout-archive.log')
    src.mkdir(); shutil.copy2(dst/'Env0.lean', src/'Env0.lean')
    event('archived')
    run([PY, '-I', '-X', 'utf8', CV, 'emit', 'Chi3', '--mod', COVER, '--scratch', S, '--capfile', CAP], 'closeout-emit.log')
    q = json.loads((S/'emit_summary.json').read_text()); from fractions import Fraction
    assert Fraction(q['Dt']) == Fraction(4643511791526209475773, 10**21), q
    event('emitted', summary=q)
    t = run([PY, '-I', '-X', 'utf8', CV, 'build', 'Chi3', '--mod', COVER, '--scratch', S, '--parallel', '2'], 'closeout-cover-build.log')
    assert not re.search(r'^FAIL ', t, re.M) and 'failed []' in t, t[-2000:]
    event('cover-built')
    dec.write_text((S/'Decay.draft.lean').read_text(encoding='utf-8'), encoding='utf-8', newline='\n')
    event('decay-replaced')
    for TARGET in TARGETS:
        for attempt in range(10):
            t = run([PY, '-I', '-X', 'utf8', 'scripts/claude/run_guarded.py', TARGET, 'preflight', '3'], f'closeout-preflight-{attempt}.log', False)
            stale = set(re.findall(r'Building ([A-Za-z0-9_.]+)', t))
            assert not any(x in t for x in ['SigmaQuarter', 'SigmaThirds', 'QuarterContour', 'SigmaHybS']), 'retired frontier'
            stale.discard(TARGET)
            if not stale: break
            seq = [m for m in order(TARGET) if m in stale]
            assert seq, 'unparsed frontier: '+t[-2000:]
            for m in seq:
                assert m.startswith('CatalanCore.Uniform.Bank.Chi3'), 'unowned stale leaf '+m
                run([PY, '-I', '-X', 'utf8', LANES, 'submit', m, '2.5'], 'closeout-'+m.rsplit('.', 2)[-2]+'-'+m.rsplit('.', 1)[-1]+'.log')
        else: raise RuntimeError('stale frontier did not close for '+TARGET)
        t = run([PY, '-I', '-X', 'utf8', LANES, 'submit', TARGET, '4'], 'closeout-final-'+TARGET.rsplit('.', 1)[-1]+'.log')
        assert 'Build completed successfully' in t, 'missing own final success '+TARGET
        event('target-built', target=TARGET)
    run([PY, '-I', '-X', 'utf8', LANES, 'run', 'Chi3CdxAudit', '2.5', '--', PY, '-I', '-X', 'utf8',
         'scripts/claude/bank/cover/runlean.py', S/'audit.out', S/'audit.lean'], 'closeout-audit-driver.log')
    audit = (S/'audit.out').read_text(encoding='utf-8')
    assert 'Chi3 final audit completed' in audit and 'sorryAx' not in audit, audit[-2000:]
    for sym in ['chi3_decay', 'chi3_measure_L2_rank']:
        line = next(x for x in audit.splitlines() if sym in x and 'depends on axioms' in x)
        assert set(re.search(r'\[(.*?)\]', line).group(1).split(', ')) == {'propext', 'Classical.choice', 'Quot.sound'}, line
    graph = order(TARGETS[0]); (S/'closeout-import-closure.json').write_text(json.dumps(sorted(graph), indent=1))
    oldprefix = 'CatalanCore.Uniform.Bank.Chi3.'
    bad = [m for m in graph if any(m == oldprefix+x or m.startswith(oldprefix+x+'.') for x in ['Tube', 'Line', 'Cap', 'Energy', 'Check', 'Decay'])]
    event('complete', closure_modules=len(graph), old_cover_in_closure=bad)
except Exception as e:
    event('stopped', error=str(e)); raise
