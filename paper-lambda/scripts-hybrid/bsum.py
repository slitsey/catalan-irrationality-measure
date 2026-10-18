# check of Proposition hdual: sum over primes p>=5 of B(p) log p / r^2  (level 1 only), m=r/8
import math, sys
def sieve(n):
    b=bytearray([1])*(n+1); b[0]=b[1]=0
    for i in range(2,int(n**.5)+1):
        if b[i]: b[i*i::i]=bytearray(len(b[i*i::i]))
    return [i for i in range(n+1) if b[i]]
def B(q,r,m):
    N=r+2*m
    j=1 if q%4==3 else 3
    k=(j*q+1)//4
    n=min(r,k)
    dA=min(2*r, 2*(r-n)+2*min(n,max(r-q,0)))
    if q<2*m:
        d=min(m,q-m%q)  # q*||m/q|| computed below
        # q*||m/q|| = min(m mod q, q - m mod q)
        t=m%q; qn=min(t,q-t)
        return dA + m + (m-qn)
    if q<=r:
        U=max(k-r+q,0); L=min(U,2*m)
        return dA+min(2*m+L, m+L+U)
    if q<N: return dA+2*m+(N-q)
    if k<=r: return dA+2*m
    return dA+max(N-k,0)
for r in [1000,10000,100000,400000]:
    m=r//8
    ps=[p for p in sieve(4*(r+2*m)+10) if p>=5]
    tot=sum(B(p,r,m)*math.log(p) for p in ps)/r**2
    print(r, round(tot,4))
