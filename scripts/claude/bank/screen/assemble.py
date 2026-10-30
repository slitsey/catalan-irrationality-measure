"""Lemma-aware re-cover: per interval between consecutive breakpoints choose among {no bp, left bp, right bp, both}.
usage: assemble.py exact.json bp.json out.json"""
import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
from recover import *
def cnt(f,kind,L,H):
    if H<=L:return 0
    out=[];greedy_seg(f,kind,L,H,out);return len(out)
if __name__=='__main__':
    ex=json.loads(Path(sys.argv[1]).read_text());f=RField(ex);bp=json.loads(Path(sys.argv[2]).read_text());t0=time.time();res={}
    for kind in ('line','seg','ray'):
        s0={(Q(p),sg):r for p,sg,r,g in bp[kind]}
        brs=sorted(set(Q(p) for p,_,_,_ in bp[kind]))
        if kind=='ray':brs=[b for b in f.breaks('ray')]
        rows=[]
        for L,H in zip(brs,brs[1:]):
            gap=H-L;a=Q(s0.get((L,1),0.0)).limit_denominator(10**12) if (L,1) in s0 else Q(0);b=Q(s0.get((H,-1),0.0)).limit_denominator(10**12) if (H,-1) in s0 else Q(0)
            if a+b>=gap*Q(99,100) and a>0 and b>0:opts={'both':2,'none':cnt(f,kind,L,H)}
            else:
                opts={'none':cnt(f,kind,L,H)}
                if a>0:opts['left']=1+cnt(f,kind,L+a,H)
                if b>0:opts['right']=1+cnt(f,kind,L,H-b)
                if a>0 and b>0 and a+b<gap:opts['both']=2+cnt(f,kind,L+a,H-b)
            best=min(opts,key=opts.get)
            rows.append([str(L),str(H),opts,best,opts[best],opts['none']])
        res[kind]=rows
        print(kind,'plain-nocross',sum(r[5] for r in rows),'lemma',sum(r[4] for r in rows),round(time.time()-t0),flush=True)
    Path(sys.argv[3]).write_text(json.dumps(res))
