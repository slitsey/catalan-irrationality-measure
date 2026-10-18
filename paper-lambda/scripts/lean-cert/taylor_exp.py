import sys, numpy as np, pickle, os
from mirror import *
cells=data['ray_cells']
Z=2.0**40
mp=1.97179
boxes=[mkbox(F(*a),F(*b)) for a,b in cells]
B=np.array(boxes,dtype=np.float64)/Z   # xlo xhi ylo yhi
P=np.array([(p[0],p[1],p[2]) for p in pts],dtype=np.float64)
cx=P[:,0]/Z; cy=P[:,1]/Z; m=P[:,2]/2**32
rho2=2.0**-20
# float rest: everything but Ls ; compute via formulas (approximate)
import math
def rest(b):
    xlo,xhi,ylo,yhi=b
    L1=math.log(xlo**2+yhi**2)
    A=0.5*max(-xhi*L1,-xlo*L1)
    l=math.log((1-xhi)**2+ylo**2)
    Bq=-0.5*min((1-xhi)*l,(1-xlo)*l)
    v=ylo/(xlo**2+yhi**2-xlo); th=math.atan(v)
    C=-min(ylo*th,yhi*th)
    return 1+A+Bq+C-0.999*math.pi*ylo
R=np.array([rest(b) for b in B])
def Ls_corner(b,idx):
    dx=np.maximum(abs(b[0]-cx[idx]),abs(b[1]-cx[idx])); dy=np.maximum(abs(b[2]-cy[idx]),abs(b[3]-cy[idx]))
    return -0.5*np.sum(m[idx]*np.log(dx*dx+dy*dy+rho2))
allidx=np.arange(300)
base=np.array([Ls_corner(b,allidx)-R[i] for i,b in enumerate(B)])
print("cells",len(B),"base min",base.min(),"fail",(base<mp).sum())
def macro_eval(lo,hi,D):
    mb=B[lo:hi]
    x0=(mb[:,0].min()+mb[:,1].max())/2; y0=(mb[:,2].min()+mb[:,3].max())/2
    d=np.hypot(cx-x0,cy-y0)
    far=d>D; fi=np.where(far)[0]; ni=np.where(~far)[0]
    q0=(x0-cx[fi])**2+(y0-cy[fi])**2+rho2
    base_far=-0.5*np.sum(m[fi]*np.log(q0))
    gx=np.sum(m[fi]*(x0-cx[fi])/q0); gy=np.sum(m[fi]*(y0-cy[fi])/q0); H=np.sum(m[fi]/q0)
    lbs=[]
    for i in range(lo,hi):
        b=B[i]
        wx=[b[0]-x0,b[1]-x0]; wy=[b[2]-y0,b[3]-y0]
        lin=max(2*(gx*a+gy*c) for a in wx for c in wy)
        quad=H*max(a*a for a in wx)+0  # placeholder
        quad=H*(max(a*a for a in wx)+max(c*c for c in wy))
        far_lb=base_far-0.5*(lin+quad)
        lbs.append(far_lb+Ls_corner(b,ni)-R[i])
    return np.array(lbs),len(ni),len(fi)
for M in (8,16,32,64):
  for D in (0.01,0.02,0.04,0.08):
    tot_cost=0; fails=0; n=0
    step=max(1,len(B)//(60*M))   # sample macros
    for lo in range(0,len(B)-M,step*M):
        lbs,nn,nf=macro_eval(lo,lo+M,D)
        tot_cost+=nn*M+nf; n+=M
        fails+=(lbs<mp).sum()
    print(M,D,"cost/cell %.1f (base 300)"%(tot_cost/n),"fails",fails,"of",n,flush=True)
