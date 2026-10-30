"""E (directed Arb/rational) decay check of one hybrid spline trial (any alternating-geometry frame; frame enters only through alpha, d, gamma, Lambda).
usage: sev_exact.py TRIAL_TAG [ray_margin] [seg_margin] [line_margin]
Reuses: decay_common.Field (polygon potentials/jets), cell-reduction-v1 spline_energy / hybrid_endpoint bridges.
Nothing here is a kernel proof."""
import sys,json,time,collections,hashlib
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction as Q
from math import comb
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
sys.path[:0]=[str(ROOT/'work/catalan-uniform/scripts/uniform-phase1')]
from decay_common import *   # Field, arb, acb, ctx, jets, bernstein_range, potential, modulus, C, sub, norm2, A, upper_q, LEG
from spline_energy import mutual,nonnegative,self_energy
from hybrid_endpoint import smoothing_atom,finite_cap_bridge,ODD,nearest
ME=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/decay-cell-reduction-2026-10-28/d16/fewer')
tag=sys.argv[1]
mR=Q(sys.argv[2]) if len(sys.argv)>2 else Q(1,10**5)
mS=Q(sys.argv[3]) if len(sys.argv)>3 else Q(1,10**3)
mL=Q(sys.argv[4]) if len(sys.argv)>4 else Q(1,10**5)
sfx=sys.argv[5] if len(sys.argv)>5 else ''
ctx.prec=320
def lower(x):return -upper_q(-x)
T=json.loads((ME/f'trial-{tag}.json').read_text());meta=T['meta'];o=T['o']
alpha=Q(meta['alpha']);d=meta['d'];gamma=Q(int(meta['gamma']))
class SevField(Field):
    def __init__(self):
        self.alpha=alpha;self.b=1+alpha;self.eps=Q(1,1000)
        self.r0=Q(str(meta['r0']));self.ys=[Q(str(v)) for v in meta['ys']];self.leans=[Q(str(v)) for v in meta['ps']]
        self.vertices=[(-self.r0,Q(0))]
        for y,l in zip(self.ys,self.leans):
            x0,y0=self.vertices[-1];self.vertices.append((x0+l*(y-y0),y))
        self.nu=[((Q(0),Q(0)),(Q(1),Q(0)),[Q(1)]),((Q(1),Q(0)),(1+2*alpha,Q(0)),[alpha])]
        self.active=Q(0)
f=SevField();kw=meta['kw'];deg=o['deg']
# ---------- exact piece list (rational polygon, rational breakpoints) ----------
SB=[Q(str(v)) for v in kw['segbr']];LB=[Q(str(v)) for v in kw['linebr']];RB=[Q(str(v)) for v in kw['raybr']]
rb=sorted(set(RB)|{y for y in f.ys if 0<y<RB[-1]})
specs=[]   # (kind, lo, hi) parameter extents: seg/line in x, ray in y
for i in range(len(SB)-1):specs.append(('seg',-f.r0+SB[i],-f.r0+SB[i+1]))
if kw['fixseg']>=0:specs.append(('seg',-f.r0+SB[-1],Q(0)))
elif abs(SB[-1]-f.r0)>Q(1,10**12):specs.append(('seg',-f.r0+SB[-1],Q(0)))
for i in range(len(rb)-1):specs.append(('ray',rb[i],rb[i+1]))
for i in range(len(LB)-1):specs.append(('line',LB[i],LB[i+1]))
assert len(specs)==len(o['pieces'])==o['npieces'],(len(specs),len(o['pieces']))
for sp,pc in zip(specs,o['pieces']):
    assert pc['kind']==sp[0]
    lo_f=pc['A'][1] if sp[0]=='ray' else pc['A'][0];hi_f=pc['B'][1] if sp[0]=='ray' else pc['B'][0]
    assert abs(lo_f-float(sp[1]))<1e-12 and abs(hi_f-float(sp[2]))<1e-12,(sp,pc)
W=[Q(v) for v in o['w']]
def legendre_to_mono(w):
    return [sum((w[j]*(-1)**(j+k)*comb(j,k)*comb(j+k,k) for j in range(k,deg+1)),Q(0)) for k in range(deg+1)]
fam_last={};upper=[]   # upper-half-plane/real pieces in solver order
for i,(kind,lo,hi) in enumerate(specs):
    mono=legendre_to_mono(W[i*(deg+1):(i+1)*(deg+1)])
    if kind=='ray':
        cs=[nearest(v/2) for v in mono]
        a=f.point('ray',lo);b=f.point('ray',hi);fam=('ray',f.edge((lo+hi)/2))
    else:
        cs=[nearest(v) for v in mono]
        a=(lo,Q(0));b=(hi,Q(0));fam=(kind,0)
    L=hi-lo
    if kw['c0'] and fam in fam_last:
        end,dens=fam_last[fam]
        if end==lo:
            ch=dens*L-cs[0];cs[0]+=ch;cs[1]-=ch   # exact C0 inside one collinear family
    fam_last[fam]=(hi,sum(cs)/L)
    upper.append((kind,a,b,cs))
pieces=[]
for kind,a,b,cs in upper:
    pieces.append((a,b,list(cs)))
    if kind=='ray':pieces.append(((a[0],-a[1]),(b[0],-b[1]),list(cs)))
mass=sum((v/Q(k+1) for _,_,cs in pieces for k,v in enumerate(cs)),Q(0))
corr=6*(1-mass);pieces[-1][2][1]+=corr;pieces[-1][2][2]-=corr
mass=sum((v/Q(k+1) for _,_,cs in pieces for k,v in enumerate(cs)),Q(0));assert mass==1
f.pieces=pieces
pos=[nonnegative(cs) for _,_,cs in pieces]   # raises unless every piece certified nonnegative
print('rationalised: pieces',len(pieces),'mass',mass,'mass-correction',float(corr),'all Bernstein nonneg ok',flush=True)
key=lambda pc:(tuple(pc[0]),tuple(pc[1]),tuple(pc[2]))
S_=set(key(pc) for pc in pieces)
for pc in pieces:assert key(((pc[0][0],-pc[0][1]),(pc[1][0],-pc[1][1]),pc[2])) in S_   # conjugation invariance, exact
fine=o['fine']
f.targets=dict(ray=Q(str(fine['m']))-mR,line=Q(str(fine['gmin']))-mL,seg=Q(str(fine['m']))+mS)
print('targets',{k:float(v) for k,v in f.targets.items()},flush=True)
# ---------- directed potential covers ----------
t0=time.time();covers={};counts={};attempts=0
for kind in ('ray','line','seg'):
    breaks=f.breaks(kind);pending=[(a,b,0) for a,b in zip(breaks,breaks[1:])][::-1];accepted=[]
    while pending:
        lo,hi,depth=pending.pop();attempts+=1;bound=f.bound(kind,lo,hi)
        good=bound is not None and (bound[1]<A(f.targets[kind]) if kind=='seg' else bound[0]>A(f.targets[kind]))
        if not good:
            if depth>=56 or len(accepted)>40000 or time.time()-t0>3600:raise RuntimeError(f'cover incomplete {kind} {len(accepted)} depth {depth} at {float(lo)}')
            mid=(lo+hi)/2;pending.extend([(mid,hi,depth+1),(lo,mid,depth+1)]);continue
        lb,ub,rule,error=bound;accepted.append([str(lo),str(hi),rule,str(lower(lb)),str(upper_q(ub)),error])
    merged=[];i=0
    while i<len(accepted):
        best=i+1;sel=accepted[i];lo=Q(accepted[i][0])
        for end in range(i+2,min(len(accepted),i+8)+1):
            hi=Q(accepted[end-1][1])
            if kind=='ray' and any(lo<y<hi for y in f.ys):break
            attempts+=1;bound=f.bound(kind,lo,hi)
            good=bound is not None and (bound[1]<A(f.targets[kind]) if kind=='seg' else bound[0]>A(f.targets[kind]))
            if good:
                lb,ub,rule,error=bound;best=end;sel=[str(lo),str(hi),rule,str(lower(lb)),str(upper_q(ub)),error]
        merged.append(sel);i=best
    assert Q(merged[0][0])==breaks[0] and Q(merged[-1][1])==breaks[-1] and all(Q(a[1])==Q(b[0]) for a,b in zip(merged,merged[1:]))
    for lo,hi,rule,lb,ub,error in merged:   # independent midpoint replay of the model
        v=f.evaluate(kind,(Q(lo)+Q(hi))/2);assert A(Q(lb))<=v and v<=A(Q(ub))
    covers[kind]=merged;counts[kind]=dict(raw=len(accepted),merged=len(merged),rules=dict(collections.Counter(r[2] for r in merged)))
    print('COVER',kind,counts[kind],round(time.time()-t0,1),flush=True)
total_cells=sum(v['merged'] for v in counts.values())
# ---------- tail at y=8 (signed absolute-moment tail, directed) ----------
R=max(upper_q(abs(C(v))) for p in f.pieces+f.nu for v in p[:2])
mom=arb(0)
for fac,ps in ((f.b,f.pieces),(Q(1),f.nu)):
    for aa,bb,cs in ps:mom+=A(abs(fac)*sum(abs(v)/Q(k+1) for k,v in enumerate(cs)))*abs(C(aa)).max(abs(C(bb)))
Y=Q(8);tail_lower=A((1-f.eps)*Y)*arb.pi()-2*mom/A(Y);assert Y>=2*R and tail_lower>A(f.targets['ray'])
tail=dict(Y='8',R_upper=str(R),lower=str(lower(tail_lower)))
# ---------- strip, atoms, bridges ----------
Wd=Q(1,10**15)
strip=sum((A(f.b)*modulus(pc,A(Wd)) for pc in f.pieces),arb(0))+sum((modulus(pc,A(Wd)) for pc in f.nu),arb(0))+A(1-f.eps)*arb.pi()*A(Wd)
strip_loss=upper_q(strip);m=f.targets['ray']-strip_loss
losses=smoothing_atom(f);U_loss=Q(losses['total_U_loss'])
matom=m-f.b*U_loss;latom=f.targets['line']-f.b*U_loss
# ---------- energies (closed forms) ----------
I=arb(0);n=len(f.pieces)
for i in range(n):
    for j in range(i+1):
        v=mutual(f.pieces[i],f.pieces[j]);I+=v if i==j else 2*v
cap=((-f.r0,Q(0)),(Q(0),Q(0)),[f.r0])
cap_sigma=sum((mutual(cap,pc) for pc in f.pieces),arb(0));cap_nu=sum((mutual(cap,pc) for pc in f.nu),arb(0))
integral=A(f.b)*cap_sigma-cap_nu
Inu_pairs,_=self_energy(f.nu)
def F(L_):return A(L_*L_/2)*A(L_).log()-A(3*L_*L_/4) if L_ else arb(0)
a=alpha;ell=2*a
J=A(Q(3,2))+A(a*a)*(A(Q(3,2))-A(ell).log())-(F(1+ell)-F(1)-F(ell));assert (J-Inu_pairs).contains(0)
Iup=upper_q(I);Inulo=lower(J)
excess=sum(((Q(hi)-Q(lo))*max(Q(ub)-m,Q(0)) for lo,hi,_,_,ub,_ in covers['seg']),Q(0))
Sfull=d*(integral-A(f.r0*m+excess))     # d * lower bound of int min(g-m,0) over the cap
Slo=lower(Sfull)
Sunit,bridge=finite_cap_bridge(f,losses,Slo/d);Sfinal=d*Sunit
Iatom=Iup+Q(losses['energy_atom_loss'])
D=2*(f.b*matom+Sfinal)-f.b*f.b*Iatom+Inulo
c=2*(matom-latom)
I_F=fine['b2I']/float(f.b)**2
pr=meta['price'];log2c=Q(pr['log2']);ratM3=Q(pr['rational'])
LamM3=upper_q(A(ratM3)+A(log2c)*arb(2).log())      # exact Lambda = rational + coef*log 2; directed UPPER rational bound
LamP=LamM3
assert abs(float(LamM3)-(float(ratM3)+float(log2c)*0.6931471805599453))<1e-11
out=dict(evidence='E',kernel_checked=False,tag=tag,alpha=meta['alpha'],d=d,gamma=str(gamma),frame=meta['frame'],price=pr,
  trial=dict(layout=meta['layout'],B=meta['B'],pieces_basis=o['npieces'],pieces_physical=len(f.pieces),degree=deg,r0=str(f.r0),ys=list(map(str,f.ys)),leans=list(map(str,f.leans)),mass='1'),
  margins=dict(ray=str(mR),seg=str(mS),line=str(mL)),targets={k:str(v) for k,v in f.targets.items()},
  covers_counts=counts,total_potential_cells=total_cells,tail=tail,strip_loss_upper=str(strip_loss),
  m_cont=str(m),m_atom=str(matom),l_atom=str(latom),I_enclosure=I.str(30),I_upper=str(Iup),I_F=I_F,Inu_lower=str(Inulo),
  cap_g_integral=integral.str(30),cap_excess=str(excess),S_lower_unit=str(Sunit),S_final=str(Sfinal),atom=losses,cap_bridge=bridge,
  D_lower=str(D),D_lower_F=float(D),c_upper=str(c),c_upper_F=float(c),F_reference=dict(D=fine['D'],c=fine['c'],m=fine['m'],gmin=fine['gmin'],S=fine['S']),
  Lambda_upper=str(LamM3),Lambda_upper_F=float(LamM3),seconds=time.time()-t0)
for name,L_ in (('M3',LamM3),):
    eta=D-L_;out['eta_lower_'+name]=str(eta);out['eta_lower_'+name+'_F']=float(eta)
    out['mu_upper_'+name]=str(gamma*c/eta) if eta>0 else None;out['mu_upper_'+name+'_F']=float(gamma*c/eta) if eta>0 else None
out['certificate']=dict(pieces=[dict(A=list(map(str,a_)),B=list(map(str,b_)),coefficients=list(map(str,cs))) for a_,b_,cs in f.pieces])
out['covers']=covers
(ME/f'exact-{tag}{sfx}.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('covers','certificate','atom','cap_bridge','I_enclosure','cap_g_integral')},indent=1),flush=True)
