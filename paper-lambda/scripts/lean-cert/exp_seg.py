import sys, time
from mirror3 import *
mp=F(197179,100000); r0=F(7,50)
a0=math.floor(-r0*Z)
for wexp in (1e-4,5e-5,2e-5):
    step=int(wexp*Z); n=(-a0+step-1)//step
    cells=[(a0+i*step,min(a0+(i+1)*step,0)) for i in range(n)]
    M=32; S=F(0); cost=0; t=time.time(); worst=0
    for k in range(0,len(cells),M):
        cs=cells[k:k+M]
        c=macro_choose_real(cs,lambda i,lb,fl,u: lb>=fl-F(2,10**5))
        cost+=c[0]
        for (xl,xh),g in zip(cs,c[5]):
            S+=2*F(xh-xl,Z)*min(g-mp,0)
    print(wexp,"cells",len(cells),"S",float(S),"cost/cell",cost/len(cells),"t",time.time()-t,flush=True)
