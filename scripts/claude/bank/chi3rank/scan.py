import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from ctl import *
def isprime(n):
    return n>1 and all(n%k for k in range(2,int(n**.5)+1))
LINES={1:[(Q(5,8),Q(2,3),Q(7,2),Q(-2)),(Q(2,3),Q(3,4),Q(5,2),Q(-1,2)),(Q(3,4),Q(5,6),Q(1),Q(3,2))],
       5:[(Q(1,2),Q(3,5),Q(5,2),Q(-1,2)),(Q(3,5),Q(5,8),Q(1),Q(2))]}
for r in [int(a) for a in sys.argv[1:]]:
    m=r//4
    for p in range(r//2,r*5//6+1):
        if not isprime(p) or p%6 not in (1,5) or p<7: continue
        t=p%6; th=Q(p,r)
        for lo,hi,a,b in LINES[t]:
            if lo<=th<=hi:
                h,fib=analyse(r,m,p)
                (pr,info),V=best(h,fib)
                print(r,p,t,float(th),'price',pr,'line',float(a*r+b*p),'delta',float(pr-(a*r+b*p)),V if isinstance(V,str) else V[1],flush=True)
