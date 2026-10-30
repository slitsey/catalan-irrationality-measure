import sys,time,pickle; sys.path.insert(0,'evidence/claude/D15')
from emu import *
c=Q(Fr(1,2),0); R=Fr(1); K=24; J=12
t=time.time(); mu=moments(c,K); print('moments',time.time()-t)
V=gen_bank.derive('Chi3')['poly']['vertices']; sl=gen_bank.derive('Chi3')['poly']['tailSlope']; tmax=Fr(13943,2000)
P0=Q(V[-1][0],V[-1][1]); D=Q(-tmax,sl*tmax)
cpi=(1-eps)*Fr(31415926,10**7)   # piLo approx
print('P0',P0,'D',D)
def evalcell(ua,ub,J=J,K=K):
    um=(ua+ub)/2; h=(ub-ua)/2
    zc=P0+D.sm(um)
    u0=zc-c
    rm=fsqrt_lo(u0.nsq(),10**4); rh=fsqrt_hi(D.nsq()*h*h,10**4)
    return cell(mu,c,R,K,J,Aabs,zc,D,h,W,cpi,rm,rh)
for (ua,ub) in []:
    print(ua,ub,evalcell(ua,ub))
print('=== floats')
for J_ in (8,12,16):
  for (ua,ub) in [(Fr(0),Fr(1,16)),(Fr(0),Fr(3,32)),(Fr(1,16),Fr(1,8)),(Fr(1,8),Fr(1,4)),(Fr(1,4),Fr(1,2)),(Fr(1,2),Fr(1))]:
    r=evalcell(ua,ub,J=J_)
    print(J_,ua,ub,float(r[0]) if r else None)
