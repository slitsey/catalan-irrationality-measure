import sys; sys.path.insert(0,'.')
import genreal as g
from p6mirror import *
for gm in (F(-14419,10000), F(-14425,10000), F(-1445,1000)):
    g.GMIN=gm
    lc=g.adapt(-(g.Z//64),0,gm)+g.adapt(0,g.Z,gm)
    while len(lc)%128: 
        k=max(range(len(lc)),key=lambda i:lc[i][1]-lc[i][0]); a,b=lc.pop(k); m=(a+b)//2; lc[k:k]=[(a,m),(m,b)]
    tot=0;n=0
    for k in range(0,len(lc)//32,3):
        cells=lc[k*32:(k+1)*32]
        c=g.macro_choose_real(cells, lambda i,lb_,fl,u: lb_-u>=gm)
        tot+=c[0]; n+=len(cells)
    print(float(gm), len(lc), tot/n, flush=True)
