# Arb certificate for the HYBRID k_rho energy step.  Adapted from paper-lambda/scripts/arb/kcert.py (unchanged originals in orig/).
# Usage: python hcert.py sigma.json ALPHA mtarget gtarget tag nseg
#  node measure nu = Leb[0,1] + 1/2 Leb[1,1+L], L=2*alpha; b=1+alpha (number of free charges per r)
#  g(s) = b U^sigma_rho(s) - U^nu(s) + (1-eps) pi |Im s|
#  D_F  = 2( b m' + S_cert ) - b^2 I_rho(sigma) + I(nu);    c = 2 (m' - g_min)
import sys, os, json, time, math
if os.environ.get('PYLIBS'): sys.path.insert(0, os.environ['PYLIBS'])  # optional: directory holding python-flint, numpy
import numpy as np
import flint
from flint import arb
from fractions import Fraction as Fr
from multiprocessing import Pool
flint.ctx.prec=96
R0=arb(7)/50; EPS=arb(1)/1000; PI=arb.pi()
W=arb(1)/2**30
G={}
def init(fn,alpha):
    d=json.load(open(fn)); pd=d['pos_den']; md=d['mass_den']
    P=[]
    for X,Y,n in d['points']:
        x=arb(X)/pd; y=arb(Y)/pd; m=arb(n)/md
        P.append((x,y,m))
        if Y!=0: P.append((x,-y,m))
    G['P']=P; rr=Fr(d['rho']); G['rho2']=(arb(rr.numerator)/rr.denominator)**2
    G['Xf']=np.array([float(p[0]) for p in P]); G['Yf']=np.array([float(p[1]) for p in P])
    a=Fr(alpha); G['alpha']=a; G['b']=arb(1+a.numerator/a.denominator) if False else (arb(1)+arb(a.numerator)/a.denominator)
    G['L']=arb(2*a.numerator)/a.denominator
def amax(a,b): return a if a>=b else (b if b>=a else a.union(b).abs_upper())
def Usig_lo(xlo,xhi,ylo,yhi):
    rho2=G['rho2']; tot=arb(0)
    for X,Y,m in G['P']:
        dx=amax((xlo-X).abs_upper(),(xhi-X).abs_upper()); dy=amax((ylo-Y).abs_upper(),(yhi-Y).abs_upper())
        tot+=m*(dx*dx+dy*dy+rho2).log()
    return -tot/2
# ---- closed forms for the potential U^nu, nu = 1_[0,1] + (1/2) 1_[1,1+L]
def Phi(q,x,y):   # Re[(q-s)(log(q-s)-1)], s=x+iy, q>x  (so q-s has positive real part)
    a=q-x
    return a*((a*a+y*y).log()/2-1)-y*(y/a).atan()
def Unu_box(x,y):   # x<0 ball, y>=0 ball (rays): upper enclosure of U^nu
    v=-(Phi(arb(1),x,y)-Phi(arb(0),x,y))
    if G['L']!=0: v+=-(Phi(1+G['L'],x,y)-Phi(arb(1),x,y))/2
    return v
Gf=lambda x: (arb(0) if x==0 else x*abs(x).log())-x
def Unu_pt(t):   # real point t in [-oo,1+L]; exact formula (t arb)
    t=arb(t); out=arb(1)
    if t!=0: out-=t*abs(t).log()
    if (1-t)!=0: out-=(1-t)*abs(1-t).log()
    if G['L']!=0: out-=(Gf(1+G['L']-t)-Gf(1-t))/2
    return out
def dUnu(t):     # U^nu'(t) = 1/2 log|(1-t)(1+L-t)| - log|t|  on (0,1)
    t=arb(t); return ((1-t)*(1+G['L']-t)).log()/2-t.log()
def Unu_seg(b):  # U^nu increasing on (-oo,0] (U'>0 there, shown in note); value at right end is the sup
    return Unu_pt(b)
def Unu_line_up(a,b):  # upper bound for sup of U^nu on cell [a,b] within [0,1]  (U^nu concave on (0,1), U' decreasing)
    A=arb(a); B=arb(b)
    if a>=1: return Unu_pt(A)   # U^nu is decreasing on [1,oo): U'<0 there
    if b>0 and dUnu(B)>0: return Unu_pt(B)
    if a>0 and dUnu(A)<0: return Unu_pt(A)
    cands=[]
    if a>0:
        d=dUnu(A); d=d if d>0 else arb(0)
        cands.append(Unu_pt(A)+d*(B-A))
    if b<1:
        d=-dUnu(B); d=d if d>0 else arb(0)
        cands.append(Unu_pt(B)+d*(B-A))
    if not cands: return arb(2)   # unreachable in practice
    best=cands[0]
    for c in cands[1:]:
        if c.upper()<best.upper(): best=c
    return best
def down(v):  # float lower rounding of an arb lower bound
    f=float(v.lower()); return math.nextafter(f,-math.inf) if f==f else float('-inf')
def hull(a,b): return arb(a).union(arb(b))
def ray_cell(c):
    ua,ub=c
    xl=-R0-arb(ub)-W; xh=-R0-arb(ua)+W
    x=xl.union(xh); y=3*hull(ua,ub)
    g=G['b']*Usig_lo(xl,xh,3*arb(ua),3*arb(ub))-Unu_box(x,y)+(1-EPS)*PI*3*arb(ua)
    return down(g)
def seg_cell(c):
    a,b=c
    return down(G['b']*Usig_lo(arb(a),arb(b),arb(0),arb(0))-Unu_seg(arb(b)))
def line_cell(c):
    a,b=c
    return down(G['b']*Usig_lo(arb(a),arb(b),arb(0),arb(0))-Unu_line_up(a,b))
def work(job):
    kind,cells=job; f={'ray':ray_cell,'seg':seg_cell,'line':line_cell}[kind]
    return [f(c) for c in cells]
NW=6
def run(pool,kind,cells):
    ch=[cells[i::NW] for i in range(NW)]
    res=pool.map(work,[(kind,c) for c in ch])
    out=[None]*len(cells)
    for i in range(NW): out[i::NW]=res[i]
    return out
def adapt(pool,kind,cells,need,maxit=24):
    done=[]; todo=cells
    for it in range(maxit):
        if not todo: break
        lb=run(pool,kind,todo); nxt=[]
        for c,l in zip(todo,lb):
            if need(c,l): a,b=c; m=(a+b)/2; nxt+= [(a,m),(m,b)]
            else: done.append((c,l))
        todo=nxt
    for c in todo: done.append((c,float('-inf')))
    done.sort(); return [c for c,l in done],[l for c,l in done]
def Inu(L):  # closed form energy of nu (Arb)
    F=lambda x: arb(0) if x==0 else x*x/2*abs(x).log()-3*x*x/4
    I12=-(F(1+L)-F(arb(1))-F(L)+F(arb(0)))
    I22=arb(0) if L==0 else L*L*(arb(3)/2-L.log())
    return arb(3)/2+I12+I22/4
if __name__=='__main__':
    fn=sys.argv[1]; alpha=sys.argv[2]; mtarget=float(sys.argv[3]); gtarget=float(sys.argv[4]); tag=sys.argv[5]; ns=int(sys.argv[6])
    init(fn,alpha); t0=time.time()
    pool=Pool(NW,initializer=init,initargs=(fn,alpha))
    n0=3000; U0=Fr(3,2); rc=[(float(U0*i/n0),float(U0*(i+1)/n0)) for i in range(n0)]
    rc,rl=adapt(pool,'ray',rc,lambda c,l: l<mtarget)
    mprime=min(rl); print('ray cells',len(rc),"m' >=",repr(mprime),'time',time.time()-t0,flush=True)
    sc=[(-0.14+0.14*i/ns,-0.14+0.14*(i+1)/ns) for i in range(ns)]
    sl=run(pool,'seg',sc)
    # exact rational S_cert from the float cell data
    Sc=2*sum((Fr(b)-Fr(a))*min(Fr(l)-Fr(mprime),0) for (a,b),l in zip(sc,sl))
    print('seg cells',len(sc),'S_cert',float(Sc),'time',time.time()-t0,flush=True)
    nl=4000; lc=[(i/nl,(i+1)/nl) for i in range(nl)]
    ne=int(sys.argv[7]) if len(sys.argv)>7 else 0
    lc+=[(1+float(G['L'])*i/ne,1+float(G['L'])*(i+1)/ne) for i in range(ne)] if ne else []
    lc,ll=adapt(pool,'line',lc,lambda c,l: l<gtarget)
    gmin01=min(l for (a,bb),l in zip(lc,ll) if bb<=1.0); print('g_min on [0,1] >=',repr(gmin01)); gmin=min(ll); print('line cells',len(lc),'g_min >=',repr(gmin),'time',time.time()-t0,flush=True)
    P=G['P']; rho2=G['rho2']; I=arb(0)
    for i,(X,Y,m) in enumerate(P):
        acc=arb(0)
        for (X2,Y2,m2) in P: acc+=m2*((X-X2)**2+(Y-Y2)**2+rho2).log()
        I+=m*acc
    I=-I/2; print('I_rho(sigma)',I)
    b=G['b']; L=G['L']
    Rs=max(np.hypot(G['Xf'],G['Yf']))*1.0001; u=arb(3)/2; s10=arb(10).sqrt()
    # tail u>=3/2:  b*U^sig >= -b/2 log((|z|+Rs)^2+rho^2), |z|<=r0+W+u sqrt10;  U^nu <= -b log(|z|-1-L), |z|>=u sqrt10 - r0 - W
    tail=-b*(((R0+W+u*s10+arb(Rs))**2+rho2).log())/2+b*(u*s10-R0-W-1-L).log()+(1-EPS)*PI*3*u
    print('tail lower',tail.lower())
    mp=min(mprime,float(tail.lower()))
    I0=Inu(L)
    D=2*(b*arb(mp)+arb(Sc.numerator)/Sc.denominator)-b*b*I+I0
    c=2*(arb(mp)-arb(gmin))
    print('I(nu)',I0,' D_F cert >=',D.lower(),' c_cert <=',c.upper())
    json.dump(dict(ray=[[a,bb,l] for (a,bb),l in zip(rc,rl)],seg=[[a,bb,l] for (a,bb),l in zip(sc,sl)],line=[[a,bb,l] for (a,bb),l in zip(lc,ll)],
       mprime=mp,S=float(Sc),I=str(I),Inu=str(I0),gmin=gmin,D=str(D),c=str(c),alpha=alpha),open('hcells_%s.json'%tag,'w'))
    print('total time',time.time()-t0)
