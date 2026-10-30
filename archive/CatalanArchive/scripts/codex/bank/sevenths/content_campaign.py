"""Source-bound content qualification; every admission uses explicit guarded preflight."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib,json,sys,time,threading
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
sys.path.insert(0,str(HERE));import admit
LOGS=ROOT.parents[1]/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/logs'
OUT=HERE/'module-receipts';OUT.mkdir(exist_ok=True)
lock=threading.Lock();state={}
def full(m):return m if m.startswith('CatalanCore.') else 'CatalanCore.Uniform.Bank.Sevenths.'+m
def check(m):
    src=ROOT/(m.replace('.','/')+'.lean')
    if not src.exists():return None
    for p in sorted(LOGS.glob(m.replace('.','_')+'-build*.json'),key=lambda p:p.stat().st_mtime,reverse=True):
        r=json.loads(p.read_text(encoding='utf-8-sig'));log=Path(r['log'])
        if r.get('rc')!=0 or not log.exists():continue
        start=p.stat().st_mtime-r['wrapper_wall_seconds']
        if src.stat().st_mtime>start+1:continue
        t=log.read_text(encoding='utf-8');peaks=list(r.get('lean_process_peak_working_sets_bytes',{}).values())
        if 'Build completed successfully' not in t or 'sorryAx' in t or not peaks or max(peaks)>2.5*2**30:continue
        return dict(target=m,accepted=True,sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                    log=str(log),metadata=str(p),peak_lean_bytes=max(peaks),verified=time.time())
    return None
def save(m,r):
    with lock:
        state[m]=r
        (HERE/'content-campaign.json').write_text(json.dumps(dict(time=time.time(),modules=state),indent=2))
        print(m,r.get('accepted'),r.get('rc'),flush=True)
    tmp=OUT/(m.replace('.','_')+'.tmp');dst=tmp.with_suffix('.json')
    tmp.write_text(json.dumps(r,indent=2));tmp.replace(dst)
def build(short):
    m=full(short);r=check(m)
    if r:save(m,r);return True
    rc=admit.ensure(m)
    r=check(m) if rc==0 else None
    if not r:
        r=dict(target=m,accepted=False,rc=rc,time=time.time())
        logs=sorted(LOGS.glob(m.replace('.','_')+'-build*.log'),key=lambda p:p.stat().st_mtime)
        if logs:
            r['log']=str(logs[-1]);text=logs[-1].read_text(encoding='utf-8')
            r['errors']=[l for l in text.splitlines() if l.startswith('error:')][-16:]
    save(m,r);return r['accepted']
sequences=[
 ['TwoTerm','PoleData','LPWindows','CatalanCore.Uniform.Content.BankShared.LPPrice','LP','UF','UFWindow','CatalanCore.Uniform.Content.BankShared.UFPrice','UFPrice.C1P26'],
 ['CatalanCore.Uniform.Content.RankProducer.Balance','CatalanCore.Uniform.Content.RankProducer.BalancedGeometry','Band','RankFibre.C1S00','PrimeBound','RankUnits','RankLoads.C1','CatalanCore.Uniform.Content.RankProducer.RunCount','CatalanCore.Uniform.Content.RankProducer.RunFibres','RankCount.C1S00','RankFacts.C1S00','RankMatch.C1S00','RankSetup','CatalanCore.Uniform.Content.RankProducer.LineBound','RankFinish','RankPrice.C1S00'],
 ['CatalanCore.Uniform.Content.BankShared.LeastPrice','Price','CatalanCore.Uniform.Content.BankShared.PoleTropical','TropicalLevels','Tropical','Tail','CatalanCore.Uniform.Content.BankShared.CrudeLog','Budget','SawPrice','CatalanCore.Uniform.Content.BankShared.SawTemplate','Classes','Profile.Mass','Profile.Template','Profile.Limiting','Contour','Energy']]
def sequence(xs):
    for x in xs:
        if not build(x):return False
    return True
if __name__=='__main__':
    with ThreadPoolExecutor(max_workers=3) as pool:
        good=list(pool.map(sequence,sequences))
    print('CONTENT_QUALIFICATION_PASSED' if all(good) else 'CONTENT_QUALIFICATION_NEEDS_REPAIR',flush=True)
    raise SystemExit(0 if all(good) else 1)
