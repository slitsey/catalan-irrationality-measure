import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from pal import *
from ctl import analyse,Lf,Ef
# verify closed form palette against brute-force for several (r,p)
import itertools
def isprime(n): return n>1 and all(n%k for k in range(2,int(n**.5)+1))
bad=0;cnt=0
for r in (120,240):
  for p in range(r//2,r*5//6+1):
    if not isprime(p) or p%6 not in(1,5): continue
    cls=p%6; m=r//4
    h,fib=analyse(r,m,p)
    for f in fib:
        x=f['x']; k1,k2=key_of(r,p,x)
        zA=int(x>kA(cls,p)); zB=int(x>kB(p))
        R,C,lf,ee=palette(cls,k1,k2,zA,zB)
        cnt+=1
        if [n//p for n in f['R']]!=R or [n//p for n in f['C']]!=C: bad+=1; print('digits',r,p,x); continue
        K=Kmat(R,C,lf,ee)
        if K!=f['K']: bad+=1; print('K',r,p,x,K,f['K'])
print('checked',cnt,'bad',bad)
