"""Exact control: fibre-additive rank-layer price of the chi3 common-minor member (no deletion).
price = 2h - (#killed) - G, G = F + dimV*d - sum costs, V in {0, line(v), top}, all fibre additive."""
import sys
from fractions import Fraction as Q
from math import gcd
# p6Frame digamma data: (u,q,w): mu=1 -> (1,1); 1/3 -> (1,3); 1/2 -> (1,2); w = 1,2,-3 ; norm 36
POLES=[(1,1,Q(1,36)),(1,3,Q(2,36)),(1,2,Q(-3,36))]
def Lf(p,n):
    s=Q(0)
    for u,q,c in POLES:
        for k in range(n):
            d=q*k+u
            if d%p==0: s+=c*q*p/d
    return s
def Ef(p,n):
    s=Q(0)
    for u,q,c in POLES:
        for k in range(n):
            d=q*k+u
            if d%p==0: s+=c*q*q*p*p/Q(d*d)
    return s
def rref(M,nr,nc):
    M=[row[:] for row in M]; piv=[]; r=0
    for c in range(nc):
        pr=None
        for i in range(r,nr):
            if M[i][c]!=0: pr=i;break
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]
        inv=1/M[r][c]; M[r]=[x*inv for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==nr: break
    return M,piv
def rightker(M,nr,nc):
    R,piv=rref(M,nr,nc); free=[c for c in range(nc) if c not in piv]; out=[]
    for f in free:
        v=[Q(0)]*nc; v[f]=Q(1)
        for i,c in enumerate(piv): v[c]=-R[i][f]
        out.append(v)
    return out
def transpose(M,nr,nc): return [[M[i][j] for i in range(nr)] for j in range(nc)]
def omega(x,y): return x[0]*y[1]-x[1]*y[0]
def span_dim(vs):
    vs=[v for v in vs if v!=(0,0)]
    if not vs: return 0
    for v in vs[1:]:
        if omega(vs[0],v)!=0: return 2
    return 1
def proj(v):
    if v[0]!=0: return (Q(1),v[1]/v[0])
    return (Q(0),Q(1))
def analyse(r,m,p,delete=()):
    com=[c for c in range(r) if c not in delete]
    rows=com+[r+2*i for i in range(m)]; cols=com+[r+2*j+1 for j in range(m)]
    h=len(rows); assert len(cols)==h
    fr={};fc={}
    for n in rows: fr.setdefault(n%p,[]).append(n)
    for n in cols: fc.setdefault(n%p,[]).append(n)
    fibres=[]
    for x in set(fr)|set(fc):
        R=sorted(fr.get(x,[]));C=sorted(fc.get(x,[]))
        lr=[Lf(p,n) for n in R]; lc=[Lf(p,n) for n in C]
        K=[[ (-Ef(p,n) if n==nn else (lc[j]-lr[i])/Q(nn//p-n//p)) for j,nn in enumerate(C)] for i,n in enumerate(R)]
        # note common node: n==nn
        rk=len(rref(K,len(R),len(C))[1]) if R and C else 0
        # right kernel -> col loads; left kernel -> row loads
        rk_vecs=rightker(K,len(R),len(C)) if C else []
        lk_vecs=rightker(transpose(K,len(R),len(C)),len(C),len(R)) if R else []
        cl=[(sum(v),sum(a*b for a,b in zip(lc,v))) for v in rk_vecs]
        rl=[(sum(v),sum(a*b for a,b in zip(lr,v))) for v in lk_vecs]
        fibres.append(dict(x=x,R=R,C=C,rk=rk,cl=cl,rl=rl,K=K))
    return h,fibres
def price(h,fibres,V):
    # V: 'zero' | 'top' | ('line',v)
    killr=sum(len(f['rl']) for f in fibres); killc=sum(len(f['cl']) for f in fibres)
    ks=min(killr,killc)
    F=0;d=0;costs=0
    for f in fibres:
        cl,rl=f['cl'],f['rl']
        F+=sum(1 for v in cl if v==(0,0))   # NB basis choice: load-zero kernel vectors count (adapted basis assumed)
        if cl:
            d+=1
            sd=span_dim(cl)
            if V=='zero': c=0
            elif V=='top': c=2-sd
            else:
                v=V[1]; c=0 if (sd==2 or (sd==1 and omega(next(w for w in cl if w!=(0,0)),v)==0)) else 1
                if sd==0: c=1
            costs+=c
        if rl:
            sdr=span_dim(rl)  # rank of row loads ; rowAnn = {v: omega(x_i,v)=0}
            if V=='zero': c=0
            elif V=='top': c=sdr
            else:
                v=V[1]; c=0 if all(omega(w,v)==0 for w in rl) else 1
            costs+=c
    dimV={'zero':0,'top':2}.get(V,1) if V in('zero','top') else 1
    G=F+d*dimV-costs
    return 2*h-ks-max(G,0), dict(killr=killr,killc=killc,F=F,d=d,costs=costs,G=G)
def best(h,fibres):
    cands=['zero','top']
    dirs=set()
    for f in fibres:
        for v in f['cl']+f['rl']:
            if v!=(0,0): dirs.add(proj(v))
    cands+= [('line',v) for v in dirs]
    res=[(price(h,fibres,V),V) for V in cands]
    return min(res,key=lambda t:t[0][0])
if __name__=='__main__':
    r=int(sys.argv[1]); p=int(sys.argv[2]); m=r//4
    h,fib=analyse(r,m,p)
    (pr,info),V=best(h,fib)
    print('r',r,'m',m,'p',p,'theta',p/r,'h',h,'price',pr,'V',V,info,'trop-natural 2h-killed',2*h-info['killr'])
