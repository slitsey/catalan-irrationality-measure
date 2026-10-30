"""D16 screen: far-field multipole cell (FarField.mpCellOk) coverage on the last ray, any hybrid receipt.
usage: mp.py exact.json out.json"""
import sys,json,math,time
from pathlib import Path
from math import comb
sys.path.insert(0,str(Path(__file__).parent))
from recover import *
def tb(a,k):
    t=0.0
    for i in range(k):t=(t+(i+1))/(1-a)
    return t
def nrm(z):return abs(z.real)+abs(z.imag)
class MP:
    def __init__(s,f,c,K,J):
        s.f=f;s.c=c;s.K=K;s.J=J
        P=[(float(f.b),p) for p in f.pieces]+[(-1.0,p) for p in f.nu]
        s.mu=[0j]*(K+1);s.R=0.0;s.Aabs=0.0
        for fac,(A_,B_,cs) in P:
            A0=complex(float(A_[0]),float(A_[1]))-c;D=complex(float(B_[0]-A_[0]),float(B_[1]-A_[1]))
            s.R=max(s.R,abs(A0),abs(A0+D))
            s.Aabs+=abs(fac)*sum(float(x)/(j+1) for j,x in enumerate(cs))
            for k in range(1,K+1):
                tot=0j
                for i in range(k+1):
                    co=comb(k,i)*A0**(k-i)*D**i
                    tot+=co*sum(float(x)/(j+i+1) for j,x in enumerate(cs))
                s.mu[k]+=fac*tot
        s.cpi=float(1-f.eps)*math.pi
    def g(s,z):  # model of g on the upper half plane (pure multipole), K terms
        u=z-s.c
        return s.cpi*z.imag+sum(s.mu[k]/(k*u**k) for k in range(1,s.K+1)).real
    def cell(s,zc,dd,h,W,m):
        u0=zc-s.c;rm=abs(u0)*(1-1e-9);rh=abs(dd)*h;vr=rh+W
        if vr>=rm:return -1e9
        a=vr/rm;r0=rm-vr
        if s.R>=r0:return -1e9
        w=1/u0;J=s.J;K=s.K
        S0=sum(s.mu[k+1]*w**(k+1)/(k+1) for k in range(J))
        S1=sum(s.mu[k+1]*w**(k+2) for k in range(J))
        lin=h*abs((S1*dd).real)+W*abs(S1.real)
        quad=a*a*sum(nrm(s.mu[k+1])/((k+1)*rm**(k+1))*tb(a,k+1) for k in range(J))
        tail=sum(nrm(s.mu[k+1])/((k+1)*r0**(k+1)) for k in range(J,K))
        rho=s.R/r0
        rem=s.Aabs*(rho**(K+1)/((K+1)*(1-rho)))
        y0=zc.imag-h*abs(dd.imag)
        return s.cpi*y0+S0.real-lin-quad-tail-rem-m
def last_edge(f):
    j=len(f.ys);return j,f.vertices[j],f.leans[j]
def far_cover(mp,f,m,W=1e-5,ntop=8.0,maxcells=6):
    j,(vx,vy),lean=last_edge(f);lean=float(lean);vx=float(vx);vy=float(vy)
    def pt(y):return complex(vx+lean*(y-vy),y)
    dd=complex(lean,1.0);cells=[];top=ntop
    for _ in range(maxcells):
        # largest h with cell [top-2h, top] feasible
        def ok(w):
            y1=top-w;yc=(top+y1)/2;return mp.cell(pt(yc),dd,w/2,W,m)>=0
        if not ok(1e-4):break
        lo,hi=1e-4,top-0.3
        if ok(hi):lo=hi
        else:
            for _ in range(40):
                mid=(lo+hi)/2
                if ok(mid):lo=mid
                else:hi=mid
        cells.append((top-lo,top));top=top-lo
    return cells
if __name__=='__main__':
    ex=json.loads(Path(sys.argv[1]).read_text());f=RField(ex);m=float(f.targets['ray']);out=[]
    mp0=MP(f,0.5,24,12)
    j,(vx,vy),lean=last_edge(f)
    yt=3.0;z=complex(float(vx+lean*(Q(yt)-vy)),yt)
    from flint import acb
    gv=f.evaluate('ray',Q(yt)).mid()
    print('check g(y=3):',float(gv),'multipole:',mp0.g(z),flush=True)
    best=None
    for c in (0.3,0.35,0.4,0.45,0.5,0.55,0.6):
      for K,J in ((24,12),(32,12),(32,16)):
        mp=MP(f,c,K,J);cells=far_cover(mp,f,m)
        yfar=cells[-1][0] if cells else 8.0
        out.append(dict(c=c,K=K,J=J,R=mp.R,Aabs=mp.Aabs,ncells=len(cells),yfar=yfar,cells=cells))
        print('c',c,'K',K,'J',J,'R %.3f'%mp.R,'cells',len(cells),'yfar %.4f'%yfar,[ (round(a,4)) for a,b in cells],flush=True)
    Path(sys.argv[2]).write_text(json.dumps(out))
