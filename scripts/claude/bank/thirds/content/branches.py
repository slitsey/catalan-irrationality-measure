"""Validate T-layer branch bounds (D1x, D2, D45, D6) of tableT against the profile T pieces (thirds, alpha=3/20)."""
import json, math, sys
from fractions import Fraction as F
sys.dont_write_bytecode=True
al=F(3,20)
prof=json.load(open('scripts/claude/bank/thirds/content/nouf-profile.json'))
def border(r):  # G310.borderSize at even r
    a=math.ceil(F(3,10)*r/2); b=math.ceil((F(3,10)*r-1)/2); return min(a,b)
def kq(p,e):
    t=1 if (p+e)%3==0 else 2
    return (t*p+e)//3
def sub(a,b): return max(a-b,0)
def D1x(r,m,p): return 2*r+2*m-min(m%p,p-m%p)
def D2sup(r,m,p,k):  # sup over feasible (u,L)
    if not (2*m<p<=r and k<=r): return None
    best=None
    for u in range(max(k+p-r,0),r+1):
        L=min(u,2*m)
        v=2*(r-u)+2*m+L
        best=v if best is None else max(best,v)
        if u>max(k+p-r,0)+3: break
    return best
def D45(r,m,p,k): return None if not (r<p and 2*m<=r) else sub(2*r,2*k)+2*m+sub(2*m,sub(p,r))
def D6(r,m,p,k): return None if not (r+2*m<=p and r<=k) else sub(2*m,sub(k,r))
def branch_vals(r,p,e):
    m=border(r); k=kq(p,e)
    out={}
    out['D1x']=D1x(r,m,p) if p%2==1 and p>2 else None
    out['D2']=D2sup(r,m,p,k)
    out['D45']=D45(r,m,p,k); out['D6']=D6(r,m,p,k)
    return out
def check(piece,e,cls,rs):
    s,t=F(piece['left']),F(piece['right']);A,B=map(F,piece['line'])
    ok={}
    for br in ('D1x','D2','D45','D6'):
        good=True;cnt=0
        for r in rs:
            for w in (F(1,50),F(1,3),F(1,2),F(2,3),F(49,50)):
                p=int((s+(t-s)*w)*r)
                # adjust to prime class: sample numbers p with p%6==cls, p>s r, p<=t r
                while p%6!=cls: p+=1
                if not (s*r<p<=t*r): continue
                v=branch_vals(r,p,e)[br]
                if v is None: good=False;break
                cnt+=1
                if v> A*r+B*p+2: good=False;break
            if not good:break
        ok[br]=good and cnt>0
    return ok
if __name__=='__main__':
    rs=[10**7+2,3*10**8+4,7*10**9+6]
    for root,cl in ((0,{1:1,5:2}),):
        pass
    # root1: kappa=1/3: (e=2,cls=1) -> j=1 ; root2: kappa=2/3: (e=2,cls=5)
    for e,cls,root in ((2,1,0),(2,5,1),(1,1,1),(1,5,0)):
        print('e',e,'cls',cls,'root',root+1)
        for k,pc in enumerate(prof['classes'][root]['pieces']):
            if pc['layer']=='T':
                print(' ',k,pc['left'],pc['right'],pc['line'],check(pc,e,cls,rs))
