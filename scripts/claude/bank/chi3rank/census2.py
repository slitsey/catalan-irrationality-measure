import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from ctl import *
from collections import Counter
r=int(sys.argv[1]);p=int(sys.argv[2]);m=r//4
h,fib=analyse(r,m,p)
(pr,info),V=best(h,fib)
print('r',r,'p',p,'theta',p/r,'h',h,'price',pr,V,info)
cen2=Counter()
for f in fib:
    key=(tuple(n//p for n in f['R']),tuple(n//p for n in f['C']),tuple(map(tuple,f['K'])),tuple(f['cl']),tuple(f['rl']))
    cen2[key]+=1
for k,v in sorted(cen2.items(),key=lambda t:str(t[0])): print(k[0],k[1],[[str(x) for x in row] for row in k[2]],'cl',[(str(a),str(b)) for a,b in k[3]],'rl',[(str(a),str(b)) for a,b in k[4]],v)
