"""Per-family real accepted macro benchmarks and explicitly labelled baseline cost estimates."""
from decay_common import *
from decay_fast_cover import FastField,chooseFast
from decay_far import Cluster,choose,coefficients,bernstein,ORDER
from decay_emit import emit
import copy,statistics,time
ctx.prec=512
CASES={'chi3':('12','Chi3Final'),'thirds+':('12','ThirdsFinal'),'lambda+':('23','Lambda24Final'),'q5-a1':('22','FifthsFinal')}
def run(frame):
    started=time.monotonic();variant,label=CASES[frame];row=getrow(frame);f=Field(row,variant);tree=Cluster(f.pieces,list(range(len(f.pieces))))
    cover=json.loads((EVID/'fast-covers'/f'cover-{frame}-{variant}.json').read_text())
    distribution=[];candidates=[]
    for kind,rows in cover['covers'].items():
        for cell in rows:
            lo,hi=map(Q,cell[:2]);c=(lo+hi)/2;h=(hi-lo)/2;f.active=c
            far,near,error=chooseFast(tree,f.point(kind,c),h*sum(map(abs,f.direction(kind))),Q(1,10**10),tree.TV)
            estimate=4*len(near)+len(far)+10;distribution.append((kind,len(near),len(far),estimate))
            if 'logjet' in cell[2]:candidates.append((estimate,kind,lo,hi))
    _,kind,lo,hi=max(candidates);c=(lo+hi)/2;h=(hi-lo)/2;f.active=c;z=f.point(kind,c);direction=f.direction(kind)
    far,near,error=choose(tree,z,h*sum(map(abs,direction)),Q(1,10**10),tree.TV)
    nf=copy.copy(f);nf.pieces=[f.pieces[i]for i in near];co=S.point_jets(nf,kind,c,h,ORDER);tail=f.b*error
    for cluster in far:
        cs,er=coefficients(cluster,z,direction,h);co=[a+f.b*b for a,b in zip(co,cs)];tail+=f.b*er
    data=jets(nf,kind,c,h,ORDER);assert data is not None;tail+=upper_q(data[1]);bs=bernstein(co)
    lower=min(-upper_q(-ex.value())for ex in bs)-tail;upper=max(upper_q(ex.value())for ex in bs)+tail
    assert upper<f.targets[kind] if kind=='seg' else lower>f.targets[kind]
    for t in(Q(-1),Q(0),Q(1)):
        approximation=sum((ex.value()*A(t**j)for j,ex in enumerate(co)),arb(0));actual=f.evaluate(kind,c+t*h);assert abs(approximation-actual)<=A(tail)
    candidate=json.loads((EVID/f'compact-{frame}-{variant}.json').read_text())
    physical=len(f.pieces);basis=candidate['actual_basis_pieces'];ray=physical-basis;real=basis-ray;pairs=physical*(physical+1)//2;orbits=(pairs+real*(real+1)//2+ray)//2
    meta=dict(frame=frame,candidate_variant=variant,physical_pieces=physical,basis_pieces=basis,degree=f.num['deg'],full_cover_cells=cover['total_cells'],cover_counts=cover['counts'],chosen_real_macro=dict(kind=kind,lo=str(lo),hi=str(hi),near_pieces=len(near),far_clusters=len(far)),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),independent_direct_controls=3,uniform_error_upper_F=float(tail),source_spec=row['spec'],matched_price=row['Lambda'],candidate_mu_F=candidate['mu'],mu_loss_F=candidate['mu_loss'],symmetric_sigma_energy_blocks=orbits,total_sigma_pairs=pairs,operation_distribution=dict(mean_near=statistics.mean(x[1]for x in distribution),max_near=max(x[1]for x in distribution),mean_clusters=statistics.mean(x[2]for x in distribution),max_clusters=max(x[2]for x in distribution),mean_inputs_model=statistics.mean(x[3]for x in distribution),max_inputs_model=max(x[3]for x in distribution)),scope='Accepted directed arithmetic macro and finite full-cover count; final source/analytic Lean transfer remainsPhase2/3')
    emit(label,bs,meta,fast=True)
    (EVID/f'case-{frame}.json').write_text(json.dumps(meta,indent=2)+'\n');print('CASE_READY',frame,physical,cover['total_cells'],'near',len(near),'clusters',len(far),'seconds',time.monotonic()-started,flush=True)

def baseline_profile(frame):
    row=getrow(frame);f=Field(row);cover=json.loads((EVID/'fast-covers'/f'cover-{frame}-baseline.json').read_text());records=[];estimates={}
    for kind,rows in cover['covers'].items():
        indices=sorted({min(len(rows)-1,(j*len(rows))//16)for j in range(16)})
        factors=[]
        for i in indices:
            lo,hi=map(Q,rows[i][:2]);c=(lo+hi)/2;h=(hi-lo)/2;accepted=False
            for shrink in range(30):
                bound=f.bound(kind,c-h,c+h)
                accepted=bound is not None and(bound[1]<A(f.targets[kind])if kind=='seg'else bound[0]>A(f.targets[kind]))
                if accepted:break
                h/=2
            factor=2**shrink;factors.append(factor)
            records.append(dict(kind=kind,macro=i,accepted_local_probe=accepted,probe_center=str(c),original_half_width=str((hi-lo)/2),accepted_half_width=str(h),dyadic_subdivision_factor=factor))
        estimates[kind]=dict(compressed_macros=len(rows),sample_count=len(indices),mean_factor=statistics.mean(factors),median_factor=statistics.median(factors),max_sampled_factor=max(factors),estimated_original_cells=len(rows)*statistics.mean(factors))
    n=sum(x['estimated_original_cells']for x in estimates.values());pieces=len(f.pieces);cell=43.7*(pieces/114)**2
    record=dict(frame=frame,label='C local-width extrapolation, not a complete cover or global bound',physical_pieces=pieces,per_domain=estimates,estimated_full_original_cells=n,phase0_scaled_kernel_seconds_per_cell=cell,estimated_total_original_potential_kernel_seconds=n*cell,uncertainty='Profiles sample16accepted compressed macros per domain. Local accepted half-widths do not prove a uniform partition; estimates may vary strongly near endpoints. Previous900s original-cover work limits are reported separately, never as complete counts.',probes=records)
    (EVID/f'baseline-cost-{frame}.json').write_text(json.dumps(record,indent=2)+'\n');print('BASELINE_COST_ESTIMATE',frame,n,n*cell,flush=True)
if __name__=='__main__':
    if sys.argv[1]=='profile':baseline_profile(sys.argv[2])
    else:run(sys.argv[1])
