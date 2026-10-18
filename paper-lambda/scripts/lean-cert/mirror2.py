# exact integer mirror of the Lean Taylor-macro signature bound (SigTaylor.lean)
import sys; sys.set_int_max_str_digits(0)
from mirror import *
spts=sorted(pts,key=lambda p:(p[0],p[1]))
KX=[p[0] for p in spts]
import bisect
def far_data(x0,y0,far):
    L=Ax=Ex=Ay=Ey=H=0
    for X,Y,n in far:
        dx=x0-X; dy=y0-Y
        q0=dx*dx+dy*dy+2**60
        lo=2**100//q0
        L+=n*logUpS(q0); Ax+=n*dx*lo; Ex+=n*abs(dx); Ay+=n*dy*lo; Ey+=n*abs(dy); H+=n*(lo+1)
    return (L,Ax,Ex,Ay,Ey,H)
def maxprod(gl,gh,a,b): return max(gl*a,gl*b,gh*a,gh*b)
def near_sum(box,near):
    xlo,xhi,ylo,yhi=box; t=0
    for X,Y,n in near:
        dx=max(abs(xlo-X),abs(xhi-X)); dy=max(abs(ylo-Y),abs(yhi-Y))
        t+=n*logUpS(dx*dx+dy*dy+2**60)
    return t
def sig_lb(x0,y0,i0,i1,fd,box):
    xlo,xhi,ylo,yhi=box
    L,Ax,Ex,Ay,Ey,H=fd
    ulo,uhi,vlo,vhi=xlo-x0,xhi-x0,ylo-y0,yhi-y0
    lin=2*(maxprod(Ax-Ex,Ax+Ex,ulo,uhi)+maxprod(Ay-Ey,Ay+Ey,vlo,vhi))
    quad=H*(max(ulo*ulo,uhi*uhi)+max(vlo*vlo,vhi*vhi))
    return F(-near_sum(box,spts[i0:i1]),2**97)-F(L,2**97)-F(lin+quad,2**133)
def ray_rest(b):   # = Ls - box_lb(Ls)  i.e. box_lb = Ls - rest
    xlo,xhi,ylo,yhi=b
    L1=F(logUpS(xlo*xlo+yhi*yhi),P)
    A=F(1,2)*max(F(-xhi,Z)*L1,F(-xlo,Z)*L1)
    wl=(Z-xhi)**2+ylo*ylo
    l=F(logLoS(wl),P); c1=F(Z-xhi,Z); c2=F(Z-xlo,Z)
    B=-F(1,2)*min(c1*l,c2*l)
    den=xlo*xlo+yhi*yhi-xlo*Z
    vlo=F(ylo*Z,den)
    j=min(math.floor(vlo*256),JM)
    th=F(alo[j],P)+(0 if j==JM else (vlo-F(j,256))/(1+F(j+1,256)**2))
    C=-min(F(ylo,Z)*th,F(yhi,Z)*th)
    return 1+A+B+C-F(999,1000)*PILO*F(ylo,Z)
DS=[0.004,0.008,0.016,0.03,0.06,0.12,0.25,10]
def window(x0,Dd):
    i0=bisect.bisect_left(KX,x0-int(Dd*Z)); i1=bisect.bisect_right(KX,x0+int(Dd*Z))
    return i0,i1
def macro_choose(boxes,rest,thr,costw=2.0):
    """boxes: list of int boxes; returns best (cost, x0,y0,i0,i1) passing rest-adjusted thr"""
    xs=min(b[0] for b in boxes); xe=max(b[1] for b in boxes); ys=min(b[2] for b in boxes); ye=max(b[3] for b in boxes)
    x0=(xs+xe)//2; y0=(ys+ye)//2
    rs=[rest(b) for b in boxes]
    for Dd in DS:
        i0,i1=window(x0,Dd)
        far=spts[:i0]+spts[i1:]
        fd=far_data(x0,y0,far)
        if all(sig_lb(x0,y0,i0,i1,fd,b)-r>=thr for b,r in zip(boxes,rs)):
            return (len(boxes)*(i1-i0)+costw*len(far), x0,y0,i0,i1)
    raise Exception("no D passes")
if __name__=="__main__":
    M=int(sys.argv[1]); N=int(sys.argv[2]); st=len(data['ray_cells'])//N
    mp=F(197179,100000)
    boxes_all=[mkbox(F(*a),F(*b)) for a,b in data['ray_cells']]
    tot=0;nb=0;import time;t=time.time()
    for lo in range(0,len(boxes_all)-M,st):
        bs=boxes_all[lo:lo+M]
        c=macro_choose(bs,ray_rest,mp)
        tot+=c[0]; nb+=len(bs)
    print("M",M,"cost per cell (term-units)",tot/nb,"time",time.time()-t)
