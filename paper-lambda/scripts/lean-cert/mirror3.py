import sys; sys.set_int_max_str_digits(0)
from mirror2 import *
from math import isqrt
def l_lo(N): return F(logLoS(N),2**65)
def l_up(N): return F(logUpS(N),2**65)
def ut_A(xlo,xhi):
    assert xhi<=0 and xlo>=-Z
    if xhi==0: F1=F(0)
    else:
        T1=-xhi; T2=-xlo; a=l_lo(T1*T1); b=l_up(T2*T2)
        F1=max(F(T1,Z)*a,F(T1,Z)*b,F(T2,Z)*a,F(T2,Z)*b)
    S1=F(Z-xhi,Z); Ll=l_lo((Z-xhi)**2)
    return 1+F1-S1*Ll
def tlogUB(t1,t2):
    if t1==0: return 2*F(isqrt(t2*Z)+1,Z)
    a=l_lo(t1*t1); b=l_up(t2*t2)
    return max(-F(t1,Z)*a,-F(t1,Z)*b,-F(t2,Z)*a,-F(t2,Z)*b)
def ut_B(xlo,xhi):
    assert 0<=xlo<=xhi<=Z
    return 1+tlogUB(xlo,xhi)+tlogUB(Z-xhi,Z-xlo)
def ut(xlo,xhi): return ut_A(xlo,xhi) if xhi<=0 else ut_B(xlo,xhi)
def full_sig(xlo,xhi):
    return F(-near_sum((xlo,xhi,0,0),spts),2**97)
def macro_choose_real(cells, thr_fn, DSL=DS):
    """cells: list of (xlo,xhi). thr_fn(i, utv, fullLB)->required min sigLB; returns best passing macro"""
    xs=min(c[0] for c in cells); xe=max(c[1] for c in cells)
    x0=(xs+xe)//2; y0=0
    box=lambda c:(c[0],c[1],0,0)
    uts=[ut(*c) for c in cells]
    fulls=[full_sig(*c) for c in cells]
    for Dd in DSL:
        i0,i1=window(x0,Dd)
        far=spts[:i0]+spts[i1:]
        fd=far_data(x0,y0,far)
        lbs=[sig_lb(x0,y0,i0,i1,fd,box(c)) for c in cells]
        if all(thr_fn(k,lbs[k],fulls[k],uts[k]) for k in range(len(cells))):
            return (len(cells)*(i1-i0)+2.0*len(far),x0,y0,i0,i1,[l-u for l,u in zip(lbs,uts)])
    raise Exception("none")
