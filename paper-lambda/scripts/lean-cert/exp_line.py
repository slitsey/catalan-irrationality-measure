import sys, time
from mirror3 import *
def lb(c): return full_sig(*c)-ut(*c)
lo=-(Z//64)
# uniform grid test
for w in (2**-12, 2**-14):
    step=int(w*Z); pts_=[lo]+[0]
    cells=[]
    x=lo
    while x<0: cells.append((x,min(x+step,0))); x+=step
    x=0
    while x<Z: cells.append((x,min(x+step,Z))); x+=step
    vals=[(float(lb(c)),c[0]/Z) for c in cells]
    m=min(vals); print(w,len(cells),"min",m)
def adapt(lo_,hi_,thr,maxw=2**-8):
    out=[]; stack=[(lo_,hi_)]
    while stack:
        a,b=stack.pop()
        if (b-a)<=int(maxw*Z) and lb((a,b))>=thr: out.append((a,b))
        else:
            if b-a<=1: raise Exception("too small")
            m=(a+b)//2; stack.append((m,b)); stack.append((a,m))
    return sorted(out)
for thr in (F(-14645,10000),F(-1465)/1000,F(-1466)/1000):
    t=time.time()
    c1=adapt(lo,0,thr); c2=adapt(0,Z,thr)
    print(float(thr),len(c1),len(c2),time.time()-t,flush=True)
