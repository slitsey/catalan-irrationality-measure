"""A real endpoint macro with a rational Bernstein/L1 log-modulus arithmetic check."""
from decay_common import *
from decay_fast_cover import chooseFast
from decay_far import Cluster,choose,coefficients,bernstein,ORDER
from decay_emit import emit
import copy
ctx.prec=512;row=getrow('chi3');f=Field(row,'12');cover=json.loads((EVID/'fast-covers/cover-chi3-12.json').read_text());tree=Cluster(f.pieces,list(range(len(f.pieces))));candidates=[]
for kind,rows in cover['covers'].items():
    for cell in rows:
        if not cell[2].startswith('endpoint'):continue
        lo,hi=map(Q,cell[:2]);c=(lo+hi)/2;h=(hi-lo)/2;f.active=c
        far,near,error=chooseFast(tree,f.point(kind,c),h*sum(map(abs,f.direction(kind))),Q(1,10**10),tree.TV)
        candidates.append((len(near)*4+len(far),kind,lo,hi))
_,kind,lo,hi=max(candidates);c=(lo+hi)/2;initialh=(hi-lo)/2
for subdivision in range(5):
    h=initialh/Q(2)**subdivision;f.active=c;z=f.point(kind,c);direction=f.direction(kind);delta=h*sum(map(abs,direction));assert 0<delta<=Q(1,4)
    far,near,err=choose(tree,z,delta,Q(1,10**10),tree.TV);point=S.Expr();modulus=S.Expr();tail=f.b*err;farco=[S.Expr()for _ in range(ORDER)]
    for factor,ps in((f.b,[f.pieces[i]for i in near]),(Q(-1),f.nu)):
        for a,b,cs in ps:
            point+=factor*S.potential((a,b,cs),z);deg=len(cs)-1
            bs=[sum((cs[k]*Q(comb(j,k),comb(deg,k))for k in range(j+1)),Q(0))for j in range(deg+1)]
            v=S.sub(b,a);F=max(map(abs,bs))/max(map(abs,v));L1=sum(map(abs,v));weight=abs(factor)*F*delta
            modulus+=S.Expr(14*weight,terms={('log',delta):-10*weight,('log',1+L1/(2*delta)):4*weight})
    if kind=='ray':
        point+=S.Expr(terms={('pi',Q(0)):(1-f.eps)*c});modulus+=S.Expr(terms={('pi',Q(0)):(1-f.eps)*h})
    for cluster in far:
        co,er=coefficients(cluster,z,direction,h);farco=[a+f.b*b for a,b in zip(farco,co)];tail+=f.b*er
    farbs=bernstein(farco);lower=min(-upper_q(-v.value())for v in farbs)+(-upper_q(-(point-modulus).value()))-tail
    upper=max(upper_q(v.value())for v in farbs)+upper_q((point+modulus).value())+tail
    good=upper<f.targets[kind]if kind=='seg'else lower>f.targets[kind]
    if good:break
assert good
for q in(Q(-1),Q(0),Q(1)):
    actual=f.evaluate(kind,c+q*h);assert A(lower)<=actual and actual<=A(upper)
meta=dict(frame='chi3',variant='12',rule='endpoint-log-modulus-plus-compressed-far-field',actual_cover_cell=dict(kind=kind,lo=str(lo),hi=str(hi)),chosen_half_width=str(h),subdivision_factor=2**subdivision,near_pieces=len(near),far_clusters=len(far),uniform_delta_L1=str(delta),lower=str(lower),upper=str(upper),target=str(f.targets[kind]),directed_accepted=True,independent_actual_point_controls=3,source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),scope='Actual endpoint macro. Rational Bernstein absolute density, source L1 lengths and log-modulus arithmetic; analytic modulus soundness remainsPhase2.')
emit('Endpoint',farbs+[point-modulus,point+modulus],meta,fast=True)
(EVID/'endpoint-model.json').write_text(json.dumps(meta,indent=2)+'\n');print('ENDPOINT_ACCEPTED',kind,'subdivision',2**subdivision,'near',len(near),'far',len(far),flush=True)
