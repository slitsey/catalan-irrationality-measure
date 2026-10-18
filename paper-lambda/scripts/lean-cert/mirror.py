import json, math, sys
from fractions import Fraction as F
from tables import *
D='./'
data=json.load(open(D+'cert_K300_data.json'))
sig=json.load(open(D+'sigma300.json'))
Z=2**40; P=2**64
# sigma list K=300: (X,Y,n) scaled X,Y by 2^40
pts=[]
for X,Y,n in sig['points']:
    pts.append((X<<16,Y<<16,n))
    if Y>0: pts.append((X<<16,-(Y<<16),n))
assert len(pts)==300 and sum(p[2] for p in pts)==2**32, (len(pts),sum(p[2] for p in pts))
def tu(i): return tup[i]
def tl(i): return tlo[i]
def logUpS(N):
    L=N.bit_length()-1
    i=((N<<8)>>L)-256
    e=(L-80)*(tup[256] if L>=80 else tlo[256])
    f0=256+i
    R=((N<<72)+(f0<<L)-1)//(f0<<L) - P
    return e+tup[i]+R
def logLoS(N):
    L=N.bit_length()-1
    i=((N<<8)>>L)-256
    e=(L-80)*(tlo[256] if L>=80 else tup[256])
    f1=257+i
    c=((f1<<(L+56))+N-1)//N
    return e+tlo[i+1]+P-c
PILO=F(314159265358979323846,10**20)
def box_lb(b, mp):
    xlo,xhi,ylo,yhi=b
    tot=0
    for X,Y,n in pts:
        dx=max(abs(xlo-X),abs(xhi-X)); dy=max(abs(ylo-Y),abs(yhi-Y))
        tot+=n*logUpS(dx*dx+dy*dy+2**60)
    Ls=F(-tot,2**97)
    a1=F(-xhi,Z); a2=F(-xlo,Z)
    L1=F(logUpS(xlo*xlo+yhi*yhi),P)
    A=F(1,2)*max(a1*L1,a2*L1)
    wl=(Z-xhi)**2+ylo*ylo
    l=F(logLoS(wl),P); c1=F(Z-xhi,Z); c2=F(Z-xlo,Z)
    B=-F(1,2)*min(c1*l,c2*l)
    den=xlo*xlo+yhi*yhi-xlo*Z
    vlo=F(ylo*Z,den)
    j=min(math.floor(vlo*256),JM)
    th=F(alo[j],P) + (0 if j==JM else (vlo-F(j,256))/(1+F(j+1,256)**2))
    C=-min(F(ylo,Z)*th,F(yhi,Z)*th)
    U=1+A+B+C
    return Ls-U+F(999,1000)*PILO*F(ylo,Z)
def mkbox(ua,ub):
    # ua,ub Fractions; snap u to 2^-40 grid outward (ua down, ub up)
    ua40=math.floor(ua*Z); ub40=-((-ub*Z)//1); ub40=math.ceil(ub*Z)
    W=F(1,2**30)
    xlo=math.floor((-F(7,50)-F(ub40,Z)-W)*Z); xhi=math.ceil((-F(7,50)-F(ua40,Z)+W)*Z)
    return (xlo,xhi,3*ua40,3*ub40)
if __name__=="__main__":
    import time
    cells=data['ray_cells']
    mp=F(197179,100000)
    N=int(sys.argv[1]); st=len(cells)//N
    ok=0;bad=[]
    t=time.time()
    for idx in range(0,len(cells),st):
        (a,b)=cells[idx]; b_=mkbox(F(*a),F(*b))
        lb=box_lb(b_,mp)
        if lb>=mp: ok+=1
        else: bad.append((idx,float(lb-mp)))
    print(ok,len(bad),bad[:20],time.time()-t)
