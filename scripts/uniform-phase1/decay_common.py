"""Exact selected signed spline import shared by performance experiments."""
import os,sys,json,hashlib
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction as Q
from math import comb
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
SRC=ROOT/'outputs/Compatibility programme'; LEG=SRC/'analytic-decay-2026-10-25'
EVID=SRC/'lean-plan-2026-10-27/evidence/phase1/decay'
WORK=ROOT/'work/catalan-uniform'
sys.path[:0]=[str(ROOT/'work/pylibs'),str(LEG/'cell-reduction-v1'),str(LEG/'endpoints-v1')]
from flint import arb,acb,ctx
from high_order import jets,bernstein_range
from hybrid_cover import potential,modulus,C,sub,norm2
from g_trial_check import A,upper_q
import symbolic_bench as S
SOURCE=SRC/'scope-screen-2026-10-27/selected-candidates.json'
ROWS=json.loads(SOURCE.read_text())['hybrid']
def getrow(frame):return next(r for r in ROWS if r['frame']==frame)
class Field:
    def __init__(self,row,variant='baseline'):
        self.row=row;self.variant=variant;self.r0=Q(row['spec']['parameters']['r0'])
        self.alpha=Q(row['alpha']);self.b=1+self.alpha;self.eps=Q(1,1000)
        self.ys=list(map(Q,row['spec']['parameters']['contour']['heights']))
        self.leans=list(map(Q,row['spec']['parameters']['contour']['leans']))
        self.vertices=[(-self.r0,Q(0))]
        for y,l in zip(self.ys,self.leans):
            x0,y0=self.vertices[-1];self.vertices.append((x0+l*(y-y0),y))
        if variant=='baseline':num=row['numerical']
        else:num=json.loads((EVID/f'compact-{row["frame"]}-{variant}.json').read_text())['numerical']
        self.num=num;degree=num['deg'];self.pieces=[];self.massabs=[]
        for i,p in enumerate(num['pieces']):
            weights=[Q(v) for v in num['w'][i*(degree+1):(i+1)*(degree+1)]]
            cs=[sum((weights[j]*(-1)**(j+k)*comb(j,k)*comb(j+k,k) for j in range(k,degree+1)),Q(0)) for k in range(degree+1)]
            aa=tuple(Q(str(v)) for v in p['A']);bb=tuple(Q(str(v)) for v in p['B'])
            if p['kind']=='ray':
                cs=[v/2 for v in cs];self.pieces.append((aa,bb,cs));self.pieces.append(((aa[0],-aa[1]),(bb[0],-bb[1]),cs.copy()))
            else:self.pieces.append((aa,bb,cs))
        mass=sum((v/Q(k+1) for _,_,cs in self.pieces for k,v in enumerate(cs)),Q(0))
        correction=6*(1-mass);self.pieces[-1][2][1]+=correction;self.pieces[-1][2][2]-=correction
        assert sum((v/Q(k+1) for _,_,cs in self.pieces for k,v in enumerate(cs)),Q(0))==1
        self.nu=[((Q(0),Q(0)),(Q(1),Q(0)),[Q(1)]),((Q(1),Q(0)),(1+2*self.alpha,Q(0)),[self.alpha])]
        self.targets=dict(ray=Q(str(num['fine']['m']))-Q(1,100000),line=Q(str(num['fine']['gmin']))-Q(1,100000),seg=Q(str(num['fine']['m']))+Q(1,1000))
        self.active=Q(0)
    def edge(self,t):return sum(y<=t for y in self.ys)
    def point(self,kind,t):
        if kind!='ray':return(t,Q(0))
        j=self.edge(t);x,y=self.vertices[j];return(x+self.leans[j]*(t-y),t)
    def direction(self,kind):return(self.leans[self.edge(self.active)],Q(1)) if kind=='ray' else(Q(1),Q(0))
    def evaluate(self,kind,t):
        z=self.point(kind,t);value=sum((A(self.b)*potential(p,z) for p in self.pieces),arb(0))-sum((potential(p,z) for p in self.nu),arb(0))
        return value+A((1-self.eps)*t)*arb.pi() if kind=='ray' else value
    def bound(self,kind,lo,hi,n=8):
        c=(lo+hi)/2;h=(hi-lo)/2;self.active=c
        data=jets(self,kind,c,h,n)
        if data is not None:
            co,rad=data;br=bernstein_range(co,h);return br-rad,br+rad,'logjet'+str(n),float(rad)
        delta=A(h)*A(norm2(self.direction(kind))).sqrt()
        if not delta<=A(Q(1,4)):return None
        gc=self.evaluate(kind,c);err=arb(0)
        # Tight exact Bernstein absolute density majorants in the endpoint rule.
        for factor,ps in ((self.b,self.pieces),(Q(1),self.nu)):
            for aa,bb,cs in ps:
                deg=len(cs)-1;bern=[sum((cs[k]*Q(comb(j,k),comb(deg,k)) for k in range(j+1)),Q(0)) for j in range(deg+1)]
                F=max(map(abs,bern));length=abs(C(sub(bb,aa)))
                err+=A(abs(factor)*F)/length*delta*(14+10*abs(delta.log())+4*(1+length/(2*delta)).log())
        if kind=='ray':err+=A((1-self.eps)*h)*arb.pi()
        return gc-err,gc+err,'endpoint',float(err)
    def breaks(self,kind):
        if kind=='ray':return sorted({Q(0),Q(8),*self.ys,*[a[1] for a,b,cs in self.pieces if a[1]>=0],*[b[1] for a,b,cs in self.pieces if b[1]>=0]})
        low,high=(-self.r0,Q(0)) if kind=='seg' else(Q(0),Q(1))
        return sorted({low,high,*[a[0] for a,b,cs in self.pieces if a[1]==b[1]==0 and low<a[0]<high],*[b[0] for a,b,cs in self.pieces if a[1]==b[1]==0 and low<b[0]<high]})
