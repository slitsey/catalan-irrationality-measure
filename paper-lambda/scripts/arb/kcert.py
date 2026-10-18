# Arb certificate for the k_rho point-mass sigma (sigma*.json): m', S_cert, I_rho(sigma), tail, g_min  ->  D_cert, c_cert, mu
import sys; sys.path.insert(0,'./pylibs')
import json, time, numpy as np
import flint
from flint import arb
from multiprocessing import Pool
flint.ctx.prec=96
R0=arb(7)/50; EPS=arb(1)/1000; PI=arb.pi()
W=arb(1)/2**30            # horizontal widening: covers delta_h in [-3/(8h),5/(8h)) for h >= 2^30
G={}
def init(fn):
    d=json.load(open(fn)); pd=d['pos_den']; md=d['mass_den']
    P=[]
    for X,Y,n in d['points']:
        x=arb(X)/pd; y=arb(Y)/pd; m=arb(n)/md
        P.append((x,y,m))
        if Y!=0: P.append((x,-y,m))
    G['P']=P; G['rho2']=(arb(1)/1024)**2
    G['Xf']=np.array([float(p[0]) for p in P]); G['Yf']=np.array([float(p[1]) for p in P]); G['Mf']=np.array([float(p[2]) for p in P])
def hull(a,b): return arb(a).union(arb(b))
def amax(a,b): return a if a>=b else (b if b>=a else a.union(b).abs_upper())
def Usig_lo(xlo,xhi,ylo,yhi):
    # lower bound of U_rho^sigma on the box: q_k <= max dx^2 + max dy^2 + rho^2 (exact corner maximum)
    rho2=G['rho2']; tot=arb(0)
    for X,Y,m in G['P']:
        dx=amax((xlo-X).abs_upper(),(xhi-X).abs_upper()); dy=amax((ylo-Y).abs_upper(),(yhi-Y).abs_upper())
        tot+=m*(dx*dx+dy*dy+rho2).log()
    return -tot/2
def Utau_seg(b):   # exact point value at real b<=0 (upper bound on cell [a,b] by monotonicity)
    if b==0: return arb(1)
    s=arb(b); return 1-s*(-s).log()-(1-s)*(1-s).log()
def Utau_line_up(a,b):
    def pt(t):
        if t==0 or t==1: return arb(1)
        t=arb(t); return 1-t*abs(t).log()-(1-t)*(1-t).log()
    if b<=0.5: return pt(b)
    if a>=0.5: return pt(a)
    return 1+arb(2).log()
def Utau_box(x,y):  # x<0, y>=0 balls
    z2=x*x+y*y; w2=(1-x)**2+y*y
    return 1-x*z2.log()/2-(1-x)*w2.log()/2-y*(y/(z2-x)).atan()
def ray_cell(c):
    ua,ub=c; u=hull(ua,ub)
    xl=-R0-arb(ub)-W; xh=-R0-arb(ua)+W
    x=xl.union(xh); y=3*u
    g=Usig_lo(xl,xh,3*arb(ua),3*arb(ub))-Utau_box(x,y)+(1-EPS)*PI*3*arb(ua)
    return g.lower()
def seg_cell(c):
    a,b=c; s=hull(a,b)
    return (Usig_lo(arb(a),arb(b),arb(0),arb(0))-Utau_seg(b)).lower()
def line_cell(c):
    a,b=c; t=hull(a,b)
    return (Usig_lo(arb(a),arb(b),arb(0),arb(0))-Utau_line_up(a,b)).lower()
def work(job):
    kind,cells=job; f={'ray':ray_cell,'seg':seg_cell,'line':line_cell}[kind]
    out=[float(f(c)) for c in cells]
    return [v if v==v else float('-inf') for v in out]
def run(pool,kind,cells):
    ch=[cells[i::3] for i in range(3)]
    res=pool.map(work,[(kind,c) for c in ch])
    out=[None]*len(cells)
    for i in range(3): out[i::3]=res[i]
    return out
def adapt(pool,kind,cells,need,maxit=30):
    # bisect cells whose certified lower bound fails need(cell,lb); returns final (cells,lbs)
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
if __name__=='__main__':
    fn=sys.argv[1]; mtarget=float(sys.argv[2]); gtarget=float(sys.argv[3]); tag=sys.argv[4]
    init(fn); t0=time.time()
    pool=Pool(3,initializer=init,initargs=(fn,))
    from fractions import Fraction as Fr
    U0=Fr(1,2)*3  # u in [0,3/2]; r = u*sqrt(10) <= 4.75
    n0=3000; rc=[(float(U0*i/n0),float(U0*(i+1)/n0)) for i in range(n0)]
    rc,rl=adapt(pool,'ray',rc,lambda c,l: l<mtarget)
    mprime=min(rl); print('ray cells',len(rc),'m\' >=',repr(mprime),'time',time.time()-t0,flush=True)
    ns=int(sys.argv[5]); sc=[(-0.14+0.14*i/ns,-0.14+0.14*(i+1)/ns) for i in range(ns)]
    # refine segment cells where the lower bound is below m' by much more than at its float-point value
    sl=run(pool,'seg',sc)
    Sc=2*sum((b-a)*min(l-mprime,0) for (a,b),l in zip(sc,sl))
    print('seg cells',len(sc),'S_cert',repr(Sc),'time',time.time()-t0,flush=True)
    nl=4000; lc=[(-1/64+(1+1/64)*i/nl,-1/64+(1+1/64)*(i+1)/nl) for i in range(nl)]
    lc,ll=adapt(pool,'line',lc,lambda c,l: l<gtarget)
    gmin=min(ll); print('line cells',len(lc),'g_min >=',repr(gmin),'time',time.time()-t0,flush=True)
    # I_rho(sigma) upper bound (exact finite sum)
    P=G['P']; rho2=G['rho2']; I=arb(0)
    for i,(X,Y,m) in enumerate(P):
        acc=arb(0)
        for (X2,Y2,m2) in P: acc+=m2*((X-X2)**2+(Y-Y2)**2+rho2).log()
        I+=m*acc
    I=-I/2; print('I_rho(sigma)',I)
    # tail u>=U0: g >= -1/2 log((r0+u sqrt10+Rs)^2+rho^2)+log(u sqrt10 - r0 - 1)+(1-eps) pi 3u, increasing in u
    Rs=max(np.hypot(G['Xf'],G['Yf']))*1.0001; u=arb(3)/2; s10=arb(10).sqrt()
    tail=-(((R0+u*s10+arb(Rs))**2+rho2).log())/2+(u*s10-R0-1).log()+(1-EPS)*PI*3*u
    print('tail lower',tail.lower())
    mp=min(mprime,float(tail.lower()))
    D=2*(arb(mp)+arb(Sc))-I+arb(3)/2; c=2*(arb(mp)-arb(gmin)); eta=D-arb(313)/105; mu=c*(4/(3*eta)+1)
    print('D_cert >=',D.lower(),' c_cert <=',c.upper(),' eta',eta,' mu <=',mu.upper())
    json.dump(dict(ray=[[a,b,l] for (a,b),l in zip(rc,rl)],seg=[[a,b,l] for (a,b),l in zip(sc,sl)],line=[[a,b,l] for (a,b),l in zip(lc,ll)],
       mprime=mp,S=Sc,I=str(I),gmin=gmin,D=str(D),c=str(c),mu=str(mu)),open('cells_%s.json'%tag,'w'))
    print('total time',time.time()-t0)
