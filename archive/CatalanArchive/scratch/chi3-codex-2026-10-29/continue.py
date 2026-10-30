from pathlib import Path
import ctypes as C,json,re,subprocess,sys,time,hashlib,shutil
R=Path.cwd(); S=R/'scratch/chi3-codex-2026-10-29'; PY=sys.executable
COVER='CatalanCore.Uniform.Bank.Chi3.Cover'; TARGET='CatalanCore.Uniform.Bank.Chi3Rank.RankFinal'
LANES=R/'scripts/claude/lanes.py'; CV=R/'scripts/claude/bank/cover/cover.py'
def event(phase,**kw):
    data=dict(time=time.strftime('%Y-%m-%d %H:%M:%S'),phase=phase,**kw)
    with (S/'events.jsonl').open('a',encoding='utf-8') as f: f.write(json.dumps(data)+'\n')
    print(json.dumps(data),flush=True)
def run(args,name,check=True):
    with (S/name).open('w',encoding='utf-8') as f:
        p=subprocess.run([str(x) for x in args],stdout=f,stderr=subprocess.STDOUT,cwd=R)
    t=(S/name).read_text(encoding='utf-8',errors='replace')
    event(name,rc=p.returncode)
    if check and p.returncode: raise RuntimeError(name+' failed: '+t[-2000:])
    return t
def imports(m):
    p=R/(m.replace('.','/')+'.lean')
    if not p.exists(): return []
    return [x for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',p.read_text(encoding='utf-8-sig'),re.M) for x in line.split() if not x.startswith('--')]
def order(m):
    seen=set(); out=[]
    def visit(x):
        if x in seen:return
        seen.add(x)
        for y in imports(x):visit(y)
        out.append(x)
    visit(m);return out
try:
    # Retain an OS process handle while waiting: PID reuse cannot complete the wrong producer.
    if len(sys.argv)>1:
        k=C.WinDLL('kernel32',use_last_error=True); k.OpenProcess.restype=C.c_void_p
        k.WaitForSingleObject.argtypes=[C.c_void_p,C.c_ulong]; k.CloseHandle.argtypes=[C.c_void_p]
        h=k.OpenProcess(0x100000,False,int(sys.argv[1]))
        if h:
            event('waiting-for-producer',pid=int(sys.argv[1]))
            while k.WaitForSingleObject(h,1000)==258:pass
            k.CloseHandle(h)
    event('validate-generator')
    expected=['gen_0.out','gen_1.out','gen2_0.out','gen2G_0.out']
    for n in expected:
        p=S/n; assert p.exists() and p.stat().st_size, 'missing output '+n
        t=p.read_text(encoding='utf-8'); assert not re.search(r'^(FAIL|.*error:)',t,re.M), 'bad output '+n
    done=[]
    for p in (R/'../tools/lanes/done').glob('*.json'):
        j=json.loads(p.read_text(encoding='utf-8')); cmd=' '.join(j.get('cmd',[]))
        if 'chi3-codex-2026-10-29' in cmd:done.append(j)
    assert len(done)==4 and all(j.get('rc')==0 for j in done), 'generator receipts missing or failed'
    (S/'generator-receipts.json').write_text(json.dumps(done,indent=1))
    src=R/'CatalanCore/Uniform/Bank/Chi3/Cover'; dst=R/'archive/CatalanArchive/CatalanCore/Uniform/Bank/Chi3/Cover'
    assert not dst.exists()
    assert not subprocess.check_output(['git','status','--porcelain','--',str(src)],cwd=R).strip(), 'cover changed since handoff'
    dst.parent.mkdir(parents=True,exist_ok=True)
    run(['git','mv',src,dst],'archive.log')
    src.mkdir(); shutil.copy2(dst/'Env0.lean',src/'Env0.lean')
    event('archived-regression')
    run([PY,'-I','-X','utf8',CV,'emit','Chi3','--mod',COVER,'--scratch',S],'emit.log')
    q=json.loads((S/'emit_summary.json').read_text()); from fractions import Fraction
    assert Fraction(q['Dt'])==Fraction(4643511791526209475773,10**21),q
    event('emitted',summary=q)
    t=run([PY,'-I','-X','utf8',CV,'build','Chi3','--mod',COVER,'--scratch',S,'--parallel','3'],'cover-build.log')
    assert not re.search(r'^FAIL ',t,re.M) and 'failed []' in t,t[-2000:]
    event('cover-accepted')
    p=R/'CatalanCore/Uniform/Bank/Chi3New/Decay.lean'
    assert p.read_bytes()==(S/'Decay.before.lean').read_bytes() or p.read_text(encoding='utf-8')==(S/'Decay.before.lean').read_text(encoding='utf-8'), 'decay changed concurrently'
    p.write_text((S/'Decay.draft.lean').read_text(encoding='utf-8'),encoding='utf-8',newline='\n')
    for attempt in range(10):
        t=run([PY,'-I','-X','utf8','scripts/claude/run_guarded.py',TARGET,'preflight','3'],f'final-preflight-{attempt}.log',False)
        stale=set(re.findall(r'Building ([A-Za-z0-9_.]+)',t))
        assert not any(x in t for x in ['SigmaQuarter','SigmaThirds','QuarterContour','SigmaHybS']), 'retired frontier'
        if not stale:break
        seq=[m for m in order(TARGET) if m in stale]
        assert seq, 'unparsed frontier: '+t[-2000:]
        for m in seq:
            assert m.startswith('CatalanCore.Uniform.Bank.Chi3'), 'unowned stale leaf '+m
            run([PY,'-I','-X','utf8',LANES,'submit',m,'2.5'],m.rsplit('.',2)[-2]+'-'+m.rsplit('.',1)[-1]+'.log')
    else: raise RuntimeError('stale frontier did not close')
    t=run([PY,'-I','-X','utf8',LANES,'submit',TARGET,'2.5'],'final-build.log')
    assert 'Build completed successfully' in t, 'missing own final success'
    run([PY,'-I','-X','utf8',LANES,'run','Chi3CdxAudit','2.5','--',PY,'-I','-X','utf8','scripts/claude/bank/cover/runlean.py',S/'audit.out',S/'audit.lean'],'audit-driver.log')
    audit=(S/'audit.out').read_text(encoding='utf-8'); assert 'Chi3 final audit completed' in audit and 'sorryAx' not in audit,audit
    for sym in ['chi3_decay','chi3_measure_L2_rank']:
        line=next(x for x in audit.splitlines() if sym in x and 'depends on axioms' in x)
        assert set(re.search(r'\[(.*?)\]',line).group(1).split(', '))=={'propext','Classical.choice','Quot.sound'},line
    graph=order(TARGET); (S/'new-import-closure.json').write_text(json.dumps(sorted(graph),indent=1))
    oldprefix='CatalanCore.Uniform.Bank.Chi3.'
    bad=[m for m in graph if any(m==oldprefix+x or m.startswith(oldprefix+x+'.') for x in ['Tube','Line','Cap','Energy','Check','Decay'])]
    assert not bad,bad
    event('complete',closure_modules=len(graph),axioms=['propext','Classical.choice','Quot.sound'])
except Exception as e:
    event('stopped',error=str(e)); raise
