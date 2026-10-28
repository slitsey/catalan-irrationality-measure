import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from pal import *
from collections import Counter
def isprime(n): return n>1 and all(n%k for k in range(2,int(n**.5)+1))
CACHE={}
def cert(cls,k1,k2,zA,zB):
    k=(cls,k1,k2,zA,zB)
    if k not in CACHE: CACHE[k]=build_cert(*k)
    return CACHE[k]
WIN={1:[(Q(5,8),Q(2,3),Q(7,2),Q(-2)),(Q(2,3),Q(3,4),Q(5,2),Q(-1,2)),(Q(3,4),Q(5,6),Q(1),Q(3,2))],
     5:[(Q(1,2),Q(3,5),Q(5,2),Q(-1,2)),(Q(3,5),Q(5,8),Q(1),Q(2))]}
def keys_of(r,p):
    cls=p%6; kk=Counter()
    for x in range(p):
        k1,k2=key_of(r,p,x); kk[(cls,k1,k2,int(x>kA(cls,p)),int(x>kB(p)))]+=1
    return kk
def total(kk,v):
    return sum(n*gain(cert(*k),v) for k,n in kk.items())
if __name__=='__main__':
    for cls in (1,5):
      for lo,hi,a,b in WIN[cls]:
        for r in (480,960):
          ps=[p for p in range(int(lo*r)+1,int(hi*r)) if isprime(p) and p%6==cls]
          ps=ps[:: max(1,len(ps)//4)]
          for p in ps:
            kk=keys_of(r,p); h=r+r//4
            cands=[None,'top']
            for k in kk:
                c=cert(*k)
                for d in c['kr']:
                    L=c['rload'][d]
                    if L!=(0,0): cands.append((L[0],L[1]) if L[0]!=0 else L)
                for e in c['kc']:
                    L=c['cload'][e]
                    if L!=(0,0): cands.append(L)
            cands=list({(str(c) if not isinstance(c,tuple) else (c[1]/c[0] if c[0]!=0 else 'inf')) :c for c in cands}.values())
            res=sorted(((total(kk,v),v) for v in cands),key=lambda t:-t[0])
            best=res[0]
            price=2*h-best[0]
            print(cls,(str(lo),str(hi)),r,p,'best gain',best[0],'V',best[1] if not isinstance(best[1],tuple) else (best[1][1]/best[1][0] if best[1][0] else 'inf'),'price',price,'line',float(a*r+b*p),'d',float(price-(a*r+b*p)))
