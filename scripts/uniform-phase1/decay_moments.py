"""Preserve exact source moments and validate one four-cell shared Taylor block."""
from decay_common import *
from decay_far import Cluster,choose,coefficients,bernstein,ORDER,L
from decay_emit import emit
import copy,time
ctx.prec=384;row=getrow('chi3');f=Field(row);c=(f.ys[1]+f.ys[2])/2;h=Q(1,250);f.active=c;z=f.point('ray',c);direction=f.direction('ray')
tree=Cluster(f.pieces,list(range(len(f.pieces))));far,near,error=choose(tree,z,h*sum(map(abs,direction)),Q(1,10**10),tree.TV)
clusters=[];checks=0
for cluster in far:
    expected=cluster.moments();independent=[(Q(0),Q(0))for _ in range(L+1)]
    for a,b,cs in cluster.ps:
        aa=S.sub(a,cluster.c);v=S.sub(b,a);power=[(Q(1),Q(0))]
        for k in range(L+1):
            value=(Q(0),Q(0))
            for j,pj in enumerate(power):
                for ell,coeff in enumerate(cs):value=S.za(value,S.zc(pj,coeff/Q(j+ell+1)))
            independent[k]=S.za(independent[k],value)
            nxt=[(Q(0),Q(0))for _ in range(len(power)+1)]
            for j,pj in enumerate(power):nxt[j]=S.za(nxt[j],S.zm(pj,aa));nxt[j+1]=S.za(nxt[j+1],S.zm(pj,v))
            power=nxt
    assert expected==independent;checks+=len(expected)
    clusters.append(dict(piece_indices=cluster.ids,center=list(map(str,cluster.c)),radius_L1=str(cluster.R),absolute_mass_upper=str(cluster.TV),moments=[list(map(str,m))for m in expected]))
nf=copy.copy(f);nf.pieces=[f.pieces[i]for i in near];co=S.point_jets(nf,'ray',c,h,ORDER);tail=f.b*error
for cluster in far:
    cs,er=coefficients(cluster,z,direction,h);co=[a+f.b*b for a,b in zip(co,cs)];tail+=f.b*er
nearData=jets(nf,'ray',c,h,ORDER);assert nearData is not None;tail+=upper_q(nearData[1]);bs=bernstein(co)
lower=min(-upper_q(-ex.value())for ex in bs)-tail
for t in(Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1)):
    approx=sum((ex.value()*A(t**j)for j,ex in enumerate(co)),arb(0));direct=f.evaluate('ray',c+t*h);assert abs(approx-direct)<=A(tail)
record=dict(status='EXACT_MOMENTS_AND_DIRECTED_BLOCK_CHECKED',source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),source_pieces=[dict(A=list(map(str,a)),B=list(map(str,b)),density=list(map(str,cs)))for a,b,cs in f.pieces],clusters=clusters,independent_moment_equalities=checks,near_indices=near,center=str(c),block_half_width=str(h),cells_per_block=4,cell_half_width='1/1000',error_upper=str(tail),error_upper_F=float(tail),lower=str(lower),target=str(f.targets['ray']),block_accepted=lower>f.targets['ray'],generic_analytic_soundness='Phase2 obligation; exact algebra and independent direct Arb controls only')
(EVID/'moments-and-shared-block.json').write_text(json.dumps(record,indent=2)+'\n');print('MOMENTS_BLOCK',checks,'block_accepted',record['block_accepted'],'error',float(tail),flush=True)
emit('Block',bs,dict(pieces=114,near_pieces=len(near),far_clusters=len(far),half_width=str(h),cells_per_block=4,block_accepted=record['block_accepted'],scope='real sharedTaylor macro arithmetic; analytic soundness remainsPhase2'))
