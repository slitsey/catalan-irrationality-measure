"""Closed-form palettes and certificates for the chi3 fibres (H16)."""
import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Q
def wA(cls): return 1 if cls==1 else 2
def kA(cls,p): return (p-1)//3 if cls==1 else (2*p-1)//3
def kB(p): return (p-1)//2
def Lcl(cls,d,zA,zB):
    """Lf(x+p d) in terms of d and zone bits"""
    a=sum(Q(1,wA(cls)+3*m) for m in range(d+zA)); b=sum(Q(1,1+2*m) for m in range(d+zB)); c=sum(Q(1,1+m) for m in range(d))
    return Q(1,18)*3*a+Q(-1,12)*2*b+Q(1,36)*c
def Ecl(cls,d,zA,zB):
    a=sum(Q(1,(wA(cls)+3*m)**2) for m in range(d+zA)); b=sum(Q(1,(1+2*m)**2) for m in range(d+zB)); c=sum(Q(1,(1+m)**2) for m in range(d))
    return Q(1,18)*9*a+Q(-1,12)*4*b+Q(1,36)*c
# kinds: 0=C(common) 1=E(row) 2=O(col) 3=N(none)
def key_of(r,p,x):
    n1=x+p; n2=x+2*p; half=r+r//2
    def kind(n):
        if n<r: return 0
        if n<half: return 1 if n%2==0 else 2
        return 3
    return (kind(n1),kind(n2))
def palette(cls,k1,k2,zA,zB):
    R=[0]+([1] if k1 in(0,1) else [])+([2] if k2==1 else [])
    C=[0]+([1] if k1 in(0,2) else [])+([2] if k2==2 else [])
    ds=sorted(set(R+C))
    return R,C,{d:Lcl(cls,d,zA,zB) for d in ds},{d:Ecl(cls,d,zA,zB) for d in ds}
def Kmat(R,C,lf,ee):
    return [[(-ee[d] if d==e else (lf[e]-lf[d])/(e-d)) for e in C] for d in R]
def rref(M,nr,nc):
    M=[row[:] for row in M]; piv=[]; r=0
    for c in range(nc):
        pr=next((i for i in range(r,nr) if M[i][c]!=0),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; inv=1/M[r][c]; M[r]=[x*inv for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==nr: break
    return M,piv
def rightker(M,nr,nc):
    Rr,piv=rref(M,nr,nc); free=[c for c in range(nc) if c not in piv]; out=[]
    for f in free:
        v=[Q(0)]*nc; v[f]=Q(1)
        for i,c in enumerate(piv): v[c]=-Rr[i][f]
        out.append(v)
    return out
def inverse(M):
    n=len(M); A=[row[:]+[Q(int(i==j)) for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        pr=next(i for i in range(c,n) if A[i][c]!=0); A[c],A[pr]=A[pr],A[c]
        inv=1/A[c][c]; A[c]=[x*inv for x in A[c]]
        for i in range(n):
            if i!=c and A[i][c]!=0:
                f=A[i][c]; A[i]=[a-f*b for a,b in zip(A[i],A[c])]
    return [row[n:] for row in A]
def build_cert(cls,k1,k2,zA,zB):
    """returns dict with R,C,lf,ee,Lq,Lq',Pq,Pq' (3x3 dicts by digit), kr,kc, loads"""
    R,C,lf,ee=palette(cls,k1,k2,zA,zB)
    K=Kmat(R,C,lf,ee); nr,nc=len(R),len(C)
    rk=rightker(K,nr,nc)
    lk=rightker([[K[i][j] for i in range(nr)] for j in range(nc)],nc,nr)
    assert len(rk)<=1 and len(lk)<=1,(cls,k1,k2,zA,zB,len(rk),len(lk))
    # Lq: identity with pivot row replaced by left kernel vector y
    Lm=[[Q(int(i==j)) for j in range(nr)] for i in range(nr)]; kr=[]
    if lk:
        y=lk[0]; dk=next(i for i in range(nr) if y[i]!=0); Lm[dk]=y[:]; kr=[R[dk]]
    Pm=[[Q(int(i==j)) for j in range(nc)] for i in range(nc)]; kc=[]
    if rk:
        v=rk[0]; ek=next(i for i in range(nc) if v[i]!=0)
        for i in range(nc): Pm[i][ek]=v[i]
        kc=[C[ek]]
    Li=inverse(Lm); Pi=inverse(Pm)
    def emb(M,D): return {(D[i],D[j]):M[i][j] for i in range(len(D)) for j in range(len(D))}
    cert=dict(R=R,C=C,lf=lf,ee=ee,Lq=emb(Lm,R),Lq_=emb(Li,R),Pq=emb(Pm,C),Pq_=emb(Pi,C),kr=kr,kc=kc)
    # check
    for d in kr:
        for e in C: assert sum(Lm[R.index(d)][i]*K[i][j]*0 for i in range(nr) for j in range(nc))==0
    # loads
    cert['rload']={d:(sum(cert['Lq'][(d,f)] for f in R),sum(lf[f]*cert['Lq'][(d,f)] for f in R)) for d in kr}
    cert['cload']={e:(sum(cert['Pq'][(g,e)] for g in C),sum(lf[g]*cert['Pq'][(g,e)] for g in C)) for e in kc}
    return cert
def par(a,b): return a[0]*b[1]-a[1]*b[0]
def gain(cert,v):
    """v=None (V=0), 'top', or (v0,v1) line; returns (nkr, mcterm, mrterm) with gain = nkr + mc*[kc] - (dV-mr)*[kr]"""
    nkr=len(cert['kr']); 
    if v is None: return nkr
    if v=='top':
        # dV=2: mc=dim Ucol (<=1 since one kill), mr=dim(V cap Urow)=1 if rload nonzero else 2
        mc=sum(1 for e in cert['kc'] if cert['cload'][e]!=(0,0))
        mrterm=sum(2-(1 if cert['rload'][d]!=(0,0) else 2) for d in cert['kr'])
        return nkr+mc-mrterm
    mc=sum(1 for e in cert['kc'] if cert['cload'][e]!=(0,0) and par(cert['cload'][e],v)==0)
    mrterm=sum(1-(1 if par(cert['rload'][d],v)==0 else 0) for d in cert['kr'])
    return nkr+mc-mrterm
