"""Exact (Fraction) emulation of the D15 far-field cell Boolean, chi3 data."""
import sys
sys.path.insert(0,'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank')
import gen_bank
from fractions import Fraction as Fr
from math import comb
d=gen_bank.derive('Chi3'); sc=d['sc']
Mq=sc['Mq']; eps=sc['eps']; mprime=sc['mprime']; W=sc['W']
class Q:  # gaussian rational
    __slots__=('r','i')
    def __init__(s,r=Fr(0),i=Fr(0)): s.r=Fr(r); s.i=Fr(i)
    def __add__(a,b): return Q(a.r+b.r,a.i+b.i)
    def __sub__(a,b): return Q(a.r-b.r,a.i-b.i)
    def __mul__(a,b): return Q(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
    def sm(a,q): return Q(a.r*q,a.i*q)
    def nsq(a): return a.r*a.r+a.i*a.i
    def inv(a): n=a.nsq(); return Q(a.r/n,-a.i/n)
    def __repr__(s): return f"({float(s.r):.6g}{float(s.i):+.6g}i)"
def pw(a,n):
    r=Q(1)
    for _ in range(n): r=r*a
    return r
# pieces: (w, A, B, coef list)
PS=[]
for s in d['segs']:
    PS.append((Mq,Q(s['ax'],s['ay']),Q(s['bx'],s['by']),[Fr(c) for c in s['coef']]))
RP=[(Fr(1),Fr(0),Fr(1)),(Fr(1,2),Fr(1),Fr(3,2))]
for (w,lo,hi) in RP+RP:
    PS.append((Fr(-1),Q(lo),Q(hi),[w*(hi-lo)/2]))
def mass(a): return sum(a[k]/(k+1) for k in range(len(a)))
def Tj(a,j): return sum(a[i]/(i+j+1) for i in range(len(a)))
def momP(P,c,k):
    w,A,B,a=P; u=A-c; V=B-A
    s=Q(0)
    for j in range(k+1):
        s=s+ (pw(u,k-j)*pw(V,j)).sm(comb(k,j)*Tj(a,j))
    return s
def moments(c,K):
    mu=[Q(0)]*(K+1)
    for P in PS:
        for k in range(1,K+1): mu[k]=mu[k]+momP(P,c,k).sm(P[0])
    return mu
def nonneg(a):  # crude: sample check
    return all(sum(a[k]*Fr(t,200)**k for k in range(len(a)))>=0 for t in range(201))
def absmass(a):
    return mass(a) if nonneg(a) else sum(abs(a[k])/(k+1) for k in range(len(a)))
Mtot=sum(P[0]*mass(P[3]) for P in PS)
Aabs=sum(abs(P[0])*absmass(P[3]) for P in PS)
def fsqrt_lo(x,den=10**6):  # rational lower sqrt
    import math
    n=int(math.isqrt(int(x*den*den))); return Fr(n,den)
def fsqrt_hi(x,den=10**6):
    import math
    n=int(math.isqrt(int(x*den*den)))+1; return Fr(n,den)
def cell(mu,c,R,K,J,Aabs,zc,dd,h,Wd,cpi,rm,rh,mp=mprime):
    """returns (value-m'), pieces"""
    u0=zc-c
    if not (rm*rm<=u0.nsq()): return None
    if not (dd.nsq()*h*h<=rh*rh): return None
    vr=rh+Wd
    if not vr<rm: return None
    a=vr/rm; r0=rm-vr
    if not R<r0: return None
    rho=R/r0
    w0=u0.inv()
    wp=[Q(1)]
    for k in range(J+2): wp.append(wp[-1]*w0)
    S0=Q(0);S1=Q(0)
    for k in range(1,J+1):
        S0=S0+(mu[k]*wp[k]).sm(Fr(1,k)); S1=S1+mu[k]*wp[k+1]
    lin=h*abs((S1*dd).r)+Wd*abs(S1.r)
    b=Fr(0); quad=Fr(0)
    for k in range(1,J+1):
        b=(b+k)/(1-a)
        quad+= (abs(mu[k].r)+abs(mu[k].i))/k * b / rm**k
    quad*=a*a
    tail=sum((abs(mu[k].r)+abs(mu[k].i))/(k*r0**k) for k in range(J+1,K+1))
    rem=Aabs*rho**(K+1)/((K+1)*(1-rho))
    y0=zc.i-h*abs(dd.i)
    val=cpi*y0+S0.r-lin-quad-tail-rem
    return val-mp, dict(lin=float(lin),quad=float(quad),tail=float(tail),rem=float(rem),S0=float(S0.r),y0=float(y0),cpi=float(cpi))
if __name__=='__main__':
    print('Mtot',Mtot,'Aabs',float(Aabs), 'mprime',float(mprime))
    for P in PS: 
        if not nonneg(P[3]): print('NONNEG FAIL',P[3])
