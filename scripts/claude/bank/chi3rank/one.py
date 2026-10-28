import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from vsel import *
r,p=int(sys.argv[1]),int(sys.argv[2]); cls=p%6
V={1:(Q(1),Q(1,78)),5:(Q(1),Q(46,2295))}[cls]
kk=keys_of(r,p)
print('a,b,c,kA,kB',r-p,3*r//2-p,3*r//2-2*p,kA(cls,p),kB(p))
for k,n in sorted(kk.items()):
    c=cert(*k); print(k[1:],n,'gain',gain(c,V),'kr',c['kr'],'kc',c['kc'],{d:(str(a),str(b)) for d,(a,b) in c['rload'].items()},{d:(str(a),str(b)) for d,(a,b) in c['cload'].items()})
