"""Bounded compact-trial reoptimisation; numerical proposals, never Lean premises."""
import os, sys, json, time, hashlib, traceback
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'): os.environ[k]='1'
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
SRC=ROOT/'outputs/Compatibility programme'
EVID=SRC/'lean-plan-2026-10-27/evidence/phase1/decay'
sys.path[:0]=[str(ROOT/'outputs/claude-2026-10-16/N-rho-trial/libs'),str(ROOT/'work/pylibs'),str(ROOT/'work/python-packages'),str(SRC/'scope-screen-2026-10-27')]
import scope_screen as H
from research_compiler import parse_context

def main(frame, budget):
    source=SRC/'scope-screen-2026-10-27/selected-candidates.json'
    row=next(r for r in json.loads(source.read_text())['hybrid'] if r['frame']==frame)
    destination=EVID/f'compact-{frame}-{budget}.json'
    if destination.exists():
        old=json.loads(destination.read_text())
        if old.get('status')=='ACCEPTED_F' and old.get('source_sha256')==hashlib.sha256(source.read_bytes()).hexdigest():
            print('REUSED',destination,flush=True); return
    t=time.monotonic(); cpu_start=time.process_time(); spec=row['spec']; context=parse_context(spec)
    # The same exact source/node geometry and its matched price are retained.
    backend=H.backend(context,False,'high')
    pars=spec['parameters']; ys=list(map(float,pars['contour']['heights'])); leans=list(map(float,pars['contour']['leans']))
    backend.CASES['compact']=dict(alpha=float(context.geometry.mass)-1,r0=float(pars['r0']),d=len(context.frame.poles),eps=.001,Lam=row['Lambda']['upper'],B0=row['mu'],a12=(.5,1),h=.4)
    # Mandatory polygon vertices are inserted by solve; these budgets refer to
    # upper-ray + real pieces before adding conjugates to a physical measure.
    if budget==12:
        rb=[0,.00005,.005,.5]; sb=[0,.001,.03]; lb=[.5,.7,.9,1.]
    elif budget==20:
        rb=[0,.000002,.00005,.001,.015,.08,.5]; sb=[0,.00005,.002,.03]; lb=[.5,.65,.8,.9,.97,1.]
    elif budget in (21,22):
        rb=[0,.000002,.00005,.001,.015,.08,.3,.5]; sb=[0,.00005,.002,.03]; lb=[.5,.65,.75,.85,.9,.94,.97,.99,1.]
    elif budget==23:
        rb=[0,.000002,.00005,.001,.015,.08,.3,.35,.4,.45,.5]; sb=[0,.00005,.002,.03]; lb=[.5,.65,.75,.85,.9,.94,.97,.985,.99,1.]
    else: raise ValueError(budget)
    degree=4 if budget in (22,23) else 3
    out=backend.solve('compact',ys,leans,raybr=rb,segbr=sb,linebr=lb,deg=degree,fixseg=-1,c0=False,B=row['mu']+.01,iters=3,nsamp=1200,fine=True,extra=True)
    scores=[float(context.geometry.degree_scale)*out[k]['c']/(out[k]['D']-row['Lambda']['upper']) if out[k]['D']>row['Lambda']['upper'] and out[k]['c']>0 else None for k in ('fine','indep')]
    accepted=out['status'] in ('Solved','AlmostSolved') and all(v is not None for v in scores)
    mu=max(scores) if accepted else None
    physical=sum(2 if p['kind']=='ray' else 1 for p in out['pieces'])
    import ctypes as C
    from ctypes import wintypes as W
    class Memory(C.Structure):
        _fields_=[('cb',W.DWORD),('faults',W.DWORD)]+[(n,C.c_size_t) for n in ('peak','working','peakpaged','paged','peaknonpaged','nonpaged','pagefile','peakpagefile','private')]
    metrics=Memory();metrics.cb=C.sizeof(metrics)
    C.windll.kernel32.GetCurrentProcess.restype=W.HANDLE
    C.windll.psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,C.POINTER(Memory),W.DWORD]
    assert C.windll.psapi.GetProcessMemoryInfo(C.windll.kernel32.GetCurrentProcess(),C.byref(metrics),metrics.cb)
    record=dict(worker_peak_working_set_bytes=metrics.peak,worker_private_bytes_at_finish=metrics.private,cpu_seconds=time.process_time()-cpu_start,status='ACCEPTED_F' if accepted else 'FAILED_F',label='F numerical proposal only',frame=frame,budget_label=budget,actual_basis_pieces=out['npieces'],physical_pieces=physical,degree=degree,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_spec=spec,matched_price=row['Lambda'],reference_mu=row['mu'],mu=mu,mu_loss=mu-row['mu'] if mu else None,negligible_loss_under_001=bool(mu and mu-row['mu']<.01),scores=scores,seconds=time.monotonic()-t,total_variation_F=H.total_variation(out['w'],degree),variation_upper_E=H.variation_bound(out['w'],degree),numerical=out,theorem_domain='full signed degree4 theorem remains required')
    tmp=destination.with_suffix('.tmp'); tmp.write_text(json.dumps(record,indent=2,allow_nan=False)+'\n'); tmp.replace(destination)
    print('COMPACT_RESULT '+json.dumps({k:v for k,v in record.items() if k not in ('numerical','source_spec','matched_price')}),flush=True)
if __name__=='__main__': main(sys.argv[1],int(sys.argv[2]))






