"""Directed Arb adaptive covers and operation-count cost estimates, not Lean proofs."""
from decay_common import *
import time,traceback,collections

def run(frame,variant):
    t=time.monotonic();ctx.prec=384;row=getrow(frame);f=Field(row,variant)
    destination=EVID/f'cover-{frame}-{variant}.json'
    if destination.exists() and json.loads(destination.read_text()).get('status')=='COMPLETE_E_COVER':
        print('REUSED',destination,flush=True);return
    covers={};counts={};attempts=0
    for kind in ('ray','line','seg'):
        breaks=f.breaks(kind);pending=[(a,b,0) for a,b in zip(breaks,breaks[1:])][::-1];accepted=[]
        while pending:
            lo,hi,depth=pending.pop();attempts+=1;bound=f.bound(kind,lo,hi)
            good=bound is not None and (bound[1]<A(f.targets[kind]) if kind=='seg' else bound[0]>A(f.targets[kind]))
            if not good:
                if depth>=56 or len(accepted)>20000 or time.monotonic()-t>900:
                    raise RuntimeError(f'bounded cover incomplete {kind} accepted={len(accepted)} depth={depth}')
                mid=(lo+hi)/2;pending.extend([(mid,hi,depth+1),(lo,mid,depth+1)]);continue
            lb,ub,rule,error=bound;accepted.append([str(lo),str(hi),rule,str(-upper_q(-lb)),str(upper_q(ub)),error])
            if len(accepted)%100==0:print('PROGRESS',frame,variant,kind,len(accepted),flush=True)
        # Recheck bounded adjacent unions. Every union receives a fresh bound;
        # no merge crosses a polygon corner/direction change.
        merged=[];i=0
        while i<len(accepted):
            best=i+1;selected=accepted[i];lo=Q(accepted[i][0])
            for end in range(i+2,min(len(accepted),i+8)+1):
                hi=Q(accepted[end-1][1])
                if kind=='ray' and any(lo<y<hi for y in f.ys):break
                attempts+=1;bound=f.bound(kind,lo,hi)
                good=bound is not None and (bound[1]<A(f.targets[kind]) if kind=='seg' else bound[0]>A(f.targets[kind]))
                if good:
                    lb,ub,rule,error=bound;best=end;selected=[str(lo),str(hi),rule,str(-upper_q(-lb)),str(upper_q(ub)),error]
            merged.append(selected);i=best
        assert Q(merged[0][0])==breaks[0] and Q(merged[-1][1])==breaks[-1]
        assert all(Q(a[1])==Q(b[0]) for a,b in zip(merged,merged[1:]))
        # Actual model replay at one interior point of every accepted merged cell.
        for lo,hi,rule,lb,ub,error in merged:
            value=f.evaluate(kind,(Q(lo)+Q(hi))/2);assert A(Q(lb))<=value and value<=A(Q(ub))
        covers[kind]=merged;counts[kind]=dict(raw=len(accepted),merged=len(merged),rules=dict(collections.Counter(r[2] for r in merged)))
        print('COVER',frame,variant,kind,counts[kind],flush=True)
    # Source/nu radius and signed absolute-moment tail check at y=8.
    R=max(float(abs(C(v))) for p in f.pieces+f.nu for v in p[:2])
    Vmoment=sum(abs(float(fac))*sum(abs(float(c))/(k+1) for k,c in enumerate(cs))*max(float(abs(C(a))),float(abs(C(b)))) for fac,ps in ((f.b,f.pieces),(Q(1),f.nu)) for a,b,cs in ps)
    tail_lower=(1-float(f.eps))*3.141592653589793*8-2*Vmoment/8
    assert 8>2*R and tail_lower>float(f.targets['ray'])
    n=len(f.pieces);total=sum(x['merged'] for x in counts.values())
    record=dict(status='COMPLETE_E_COVER',frame=frame,variant=variant,source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),label='Directed arithmetic cover; generic analytic/Lean soundness pending',pieces=n,density_degree=f.num['deg'],counts=counts,total_cells=total,attempts=attempts,seconds=time.monotonic()-t,targets={k:str(v) for k,v in f.targets.items()},tail_F_check=dict(radius=R,lower=tail_lower),kernel_model=dict(baseline_seconds_per_cell=43.7*(n/114)**2,total_seconds=total*43.7*(n/114)**2,scaling='C quadratic indexed-row projection from one Phase0 measurement; superseded by measured streaming checker when available'),covers=covers)
    tmp=destination.with_suffix('.tmp');tmp.write_text(json.dumps(record,indent=2)+'\n');tmp.replace(destination)
    print('COVER_COMPLETE '+json.dumps({k:v for k,v in record.items() if k!='covers'}),flush=True)
if __name__=='__main__':
    frame,variant=sys.argv[1:3]
    try:run(frame,variant)
    except Exception as error:
        (EVID/f'cover-{frame}-{variant}-failure.json').write_text(json.dumps(dict(status='INCOMPLETE',frame=frame,variant=variant,error=str(error),traceback=traceback.format_exc()),indent=2)+'\n');raise
