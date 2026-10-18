# generate packed tables for Lean: TUP, TLO (log(1+j/256), j=0..256), ALO (arctan(j/256) lower, j=0..JM)
from fractions import Fraction as F
import math
S=2**64; NT=25; NA=100; JM=208
def atanh_sum(x,n):
    return 2*sum(x**(2*k+1)/(2*k+1) for k in range(n))
def tail(x,n):
    return 2*x**(2*n+1)/((2*n+1)*(1-x*x))
tlo=[];tup=[]
for j in range(257):
    x=F(j,512+j); s=atanh_sum(x,NT); t=s+tail(x,NT)
    tlo.append(math.floor(s*S)); tup.append(math.ceil(t*S))
def asum(v,n): return sum(F((-1)**k)*v**(2*k+1)/(2*k+1) for k in range(n))
alo=[math.floor(asum(F(j,256),NA)*S) for j in range(JM+1)]
def pack(L): return sum(v<<(64*i) for i,v in enumerate(L))
if __name__=="__main__":
    assert all(0<=v<S for v in tlo+tup+alo)
    print(max(u-l for u,l in zip(tup,tlo)))
    print(math.log(2)*2**64-tlo[256], tup[256]-math.log(2)*2**64)
