"""D16 screen: true greedy re-cover of a hybrid exact receipt with the SAME Field.bound rules.
usage: recover.py TAGFILE(exact json path) OUT.json [margin_scale]
Field is rebuilt from the receipt's final physical pieces (no QP). Counts per class (ray by edge, line, seg)."""
import sys,json,time,collections
from pathlib import Path
from fractions import Fraction as Q
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
sys.path[:0]=[str(ROOT/'work/catalan-uniform/scripts/uniform-phase1')]
from decay_common import *
ctx.prec=320
class RField(Field):
    def __init__(self,ex):
        tr=ex['trial'];self.alpha=Q(ex['alpha']);self.b=1+self.alpha;self.eps=Q(1,1000)
        self.r0=Q(tr['r0']);self.ys=[Q(v) for v in tr['ys']];self.leans=[Q(v) for v in tr['leans']]
        self.vertices=[(-self.r0,Q(0))]
        for y,l in zip(self.ys,self.leans):
            x0,y0=self.vertices[-1];self.vertices.append((x0+l*(y-y0),y))
        self.nu=[((Q(0),Q(0)),(Q(1),Q(0)),[Q(1)]),((Q(1),Q(0)),(1+2*self.alpha,Q(0)),[self.alpha])]
        self.pieces=[(tuple(Q(v) for v in p['A']),tuple(Q(v) for v in p['B']),[Q(v) for v in p['coefficients']]) for p in ex['certificate']['pieces']]
        self.targets={k:Q(v) for k,v in ex['targets'].items()};self.active=Q(0)
def good(f,kind,lo,hi):
    b=f.bound(kind,lo,hi)
    if b is None:return False
    return b[1]<A(f.targets[kind]) if kind=='seg' else b[0]>A(f.targets[kind])
def rat(x,den=10**14):
    return Q(round(x*den),den)
def greedy_seg(f,kind,L,H,out):
    a=L
    while a<H:
        if good(f,kind,a,H):out.append((a,H));return
        lo=Q(0);hi=H-a;w0=(H-a)/Q(2)**40
        if not good(f,kind,a,a+w0):
            # cannot even make a tiny cell: record fail
            out.append((a,a+w0,'FAIL'));a=a+w0;continue
        lw=w0
        # gallop
        while lw*2<hi and good(f,kind,a,a+lw*2):lw*=2
        hw=min(lw*2,hi)
        for _ in range(30):
            if hw/lw<Q(101,100):break
            mid=rat(float(lw)*0.5+float(hw)*0.5) if False else (lw+hw)/2
            mid=Q(round(mid*10**14),10**14) if mid>Q(1,10**9) else mid
            if good(f,kind,a,a+mid):lw=mid
            else:hw=mid
        out.append((a,a+lw));a=a+lw
def run(exfile,outfile):
    ex=json.loads(Path(exfile).read_text());f=RField(ex);t0=time.time();res={}
    for kind in ('ray','line','seg'):
        cells=[]
        if kind=='ray':
            corners=[Q(0)]+[y for y in f.ys if 0<y<8]+[Q(8)]
            for L,H in zip(corners,corners[1:]):greedy_seg(f,kind,L,H,cells)
        else:
            L,H=(-f.r0,Q(0)) if kind=='seg' else (Q(0),Q(1))
            greedy_seg(f,kind,L,H,cells)
        res[kind]=[[str(c[0]),str(c[1])]+list(c[2:]) for c in cells]
        print(kind,len(cells),'orig',ex['covers_counts'][kind]['merged'],round(time.time()-t0),flush=True)
    res['ys']=[str(y) for y in f.ys]
    Path(outfile).write_text(json.dumps(res))
if __name__=='__main__':run(sys.argv[1],sys.argv[2])
