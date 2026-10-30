"""D16 screen: breakpoint-cell (Lemma 1 / bpOk) radii for any hybrid receipt, then lemma-aware cover count.
Model of bpOk: far pieces by Arb jets about p (radius S), incident pieces by exact closed-form series in s,
poly part by Bernstein lower bound, log part by sum |b_m| S^m |ln S|, plus both remainders.
usage: bp.py exact.json out.json"""
import sys,json,time,math
from pathlib import Path
from fractions import Fraction as Q
from math import comb
sys.path.insert(0,str(Path(__file__).parent))
from recover import *
NMAX=34
def padd(a,b):
    n=max(len(a),len(b));return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def pmul(a,b,N=NMAX):
    r=[0j]*min(len(a)+len(b)-1,N+1)
    for i,x in enumerate(a):
        if x==0:continue
        for j,y in enumerate(b):
            if i+j>N:break
            r[i+j]+=x*y
    return r
def ppow(a,k):
    r=[1+0j]
    for _ in range(k):r=pmul(r,a)
    return r
def pscale(a,c):return [c*x for x in a]
def cmplx(p):return complex(float(p[0]),float(p[1]))
def reverse_piece(P):
    A_,B_,cs=P;n=len(cs)
    new=[sum(cs[k]*comb(k,j)*(-1)**j for k in range(j,n)) for j in range(n)]
    return (B_,A_,new)
def inc_model(pieces,d,r_of_S):
    """pieces: list of (factor, (A,B,cs)) with A == p. returns polyA (real coeffs), polyLog (real coeffs)
    in s for z=p+s d (d complex), and function giving remainder bound for S."""
    pa=[0j];pl=[0j];remc=[]
    for fac,(A_,B_,cs) in pieces:
        u=complex(float(B_[0]-A_[0]),float(B_[1]-A_[1]));e=d/u;L=abs(u);loglen=math.log(L)
        W=[0j,e];Lm=complex(math.log(abs(-e)),math.atan2((-e).imag,(-e).real))
        L1=[0j]+[-(e**n)/n for n in range(1,NMAX+1)]  # -sum w^n/n as poly in s
        for k,a in enumerate(cs):
            a=float(a)
            if a==0:continue
            Wk1=ppow(W,k+1)
            t1=pmul([1+0j]+[0j]*0,L1);t1=padd(L1,pscale(pmul(Wk1,L1),-1))
            t2=pscale(Wk1,Lm)
            sm=[0j]
            for i in range(k+1):sm=padd(sm,pscale(ppow(W,k-i),1/(i+1)))
            tot=padd(padd(t1,t2),pscale(sm,-1))
            c=-float(fac)*a/(k+1)
            pa=padd(pa,pscale(tot,c))
            pa[0]+= -float(fac)*a*loglen/(k+1)
            pl=padd(pl,pscale(Wk1,c))
            remc.append((abs(float(fac)*a)/(k+1),abs(e)))
    def rem(S):
        tot=0.0
        for c,ae in remc:
            r=ae*S
            if r>=1:return float('inf')
            tot+=c*2*r**(NMAX+1)/((NMAX+1)*(1-r))
        return tot
    return [x.real for x in pa],[x.real for x in pl],rem
def bern_low(co,S):
    n=len(co)-1;c=[co[j]*S**j for j in range(n+1)]
    best=1e300
    for i in range(n+1):
        v=sum(c[j]*comb(i,j)/comb(n,j) for j in range(i+1))
        best=min(best,v)
    return best
class SubField(RField):
    def __init__(self,f,pieces,nu,dirvec):
        self.__dict__.update(f.__dict__);self.pieces=pieces;self.nu=nu;self.dirvec=dirvec
    def direction(self,kind):return self.dirvec
def same(a,b):return a[0]==b[0] and a[1]==b[1]
def radius_fn(f,kind,p,sigma,gapmax):
    """returns function ok(S)->margin (>=0 passes) and info"""
    pt=f.point(kind,p) if kind=='ray' else (p,Q(0))
    if kind=='ray':
        j=f.edge(p) if sigma>0 else sum(y<p for y in f.ys)
        dvec=(sigma*f.leans[j],Q(sigma))
    else:dvec=(Q(sigma),Q(0))
    d=complex(float(dvec[0]),float(dvec[1]))
    inc=[];far_s=[];far_n=[]
    for fac,ps,tgt in ((f.b,f.pieces,'s'),(Q(-1),f.nu,'n')):
        for P in ps:
            A_,B_,cs=P
            if same(A_,pt):inc.append((fac,P))
            elif same(B_,pt):inc.append((fac,reverse_piece(P)))
            else:(far_s if tgt=='s' else far_n).append(P)
    pa,pl,rem=inc_model(inc,d,None)
    sub=SubField(f,far_s,far_n,dvec);sub.active=p
    sgn=-1.0 if kind=='seg' else 1.0
    def margin(S,ret=False):
        S=float(S)
        if S>1/3:return -1e9
        Sq=Q(S).limit_denominator(10**12)
        try:
            jd=jets(sub,kind,p if kind=='ray' else p,Sq,8) if True else None
        except Exception as ex:return -1e9
        if jd is None:return -1e9
        co,rad=jd;co=[float(x.mid()) for x in co];rad=float(rad.upper())
        if kind=='ray' and sigma<0:co[1]-=2*float((1-f.eps))*math.pi
        tot=padd(co,pa) if False else [ (co[i] if i<len(co) else 0.0)+(pa[i] if i<len(pa) else 0.0) for i in range(max(len(co),len(pa)))]
        lg=sum(abs(pl[m])*S**m for m in range(1,len(pl)))*abs(math.log(S))
        if pl and abs(pl[0])>1e-12:return -1e9  # no log at order 0 expected
        r=rem(S)
        if kind=='seg':
            val=-bern_low([-x for x in tot],S)+lg+rad+r;m=float(f.targets[kind])-val
        else:
            val=bern_low(tot,S)-lg-rad-r;m=val-float(f.targets[kind])
        return m
    return margin
def max_radius(margin,gap):
    hi=min(gap,1/3)
    if margin(hi)>=0:return hi
    lo=hi*2**-60
    if margin(lo)<0:return 0.0
    # bisection on log scale
    a,b=math.log(lo),math.log(hi)
    for _ in range(40):
        m=(a+b)/2
        if margin(math.exp(m))>=0:a=m
        else:b=m
        if b-a<0.01:break
    return math.exp(a)
def contour_bps(f,kind):
    br=f.breaks(kind)
    if kind=='ray':br=[x for x in br]
    return br
def validate(f,kind,p,sigma,S):
    pass
if __name__=='__main__':
    ex=json.loads(Path(sys.argv[1]).read_text());f=RField(ex);out={};t0=time.time()
    for kind in ('line','seg','ray'):
        br=contour_bps(f,kind);res=[]
        for i,p in enumerate(br):
            for sigma in (1,-1):
                if sigma>0 and i==len(br)-1:continue
                if sigma<0 and i==0:continue
                if kind=='ray' and sigma>0 and p>=8:continue
                nb=br[i+1] if sigma>0 else br[i-1];gap=abs(float(nb-p))
                mg=radius_fn(f,kind,p,sigma,gap)
                s0=max_radius(mg,gap)
                res.append([str(p),sigma,s0,gap])
        out[kind]=res
        print(kind,len(res),'sides; mean frac %.3f'%(sum(min(1,r[2]/r[3]) for r in res)/len(res)),round(time.time()-t0),flush=True)
    Path(sys.argv[2]).write_text(json.dumps(out))
