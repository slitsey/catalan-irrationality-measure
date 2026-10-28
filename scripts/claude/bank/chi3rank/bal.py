import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from vsel import *
bad=0;tot=0
for cls in (1,5):
  for r in (480,484*1, 496, 600, 960):
    if r%4: continue
    for p in range(r//2,r*5//6+1):
        if not isprime(p) or p%6!=cls: continue
        kk=keys_of(r,p); nr=sum(n*len(cert(*k)['kr']) for k,n in kk.items()); nc=sum(n*len(cert(*k)['kc']) for k,n in kk.items())
        tot+=1
        if nr!=nc: bad+=1; print('unbalanced',r,p,nr,nc)
print(tot,bad)
