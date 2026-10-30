"""usage: summary.py exact.json PREFIX_DIR/NAME   (reads NAME-rec / NAME-bp / NAME-asm / NAME-mp json: names rec-X.json etc.)
prints and writes NAME-sum.json"""
import sys,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
from recover import *
from assemble import cnt
def main(exfile,rec,bp,asm,mp,out):
    ex=json.loads(Path(exfile).read_text());f=RField(ex)
    base={k:v['merged'] for k,v in ex['covers_counts'].items()}
    R=json.loads(Path(rec).read_text());recn={k:len(R[k]) for k in ('ray','line','seg')}
    AS=json.loads(Path(asm).read_text());M=json.loads(Path(mp).read_text())
    lem={k:sum(r[4] for r in AS[k]) for k in ('ray','line','seg')}
    final={k:min(recn[k],lem[k]) for k in lem}
    # multipole on the last ray interval
    rows=AS['ray'];last=rows[-1];Lq=Q(last[0])
    head=sum(r[4] for r in rows[:-1])
    bpd={(Q(p),sg):s for p,sg,s,g in json.loads(Path(bp).read_text())['ray']}
    a=Q(bpd.get((Lq,1),0.0)).limit_denominator(10**12)
    best=(None,None)
    ycache={}
    def tail(yf):
        yf=Q(yf).limit_denominator(10**6)
        if yf<=Lq:return 0
        if yf in ycache:return ycache[yf]
        c0=cnt(f,'ray',Lq,yf);c1=1+cnt(f,'ray',Lq+a,yf) if a>0 else c0
        ycache[yf]=min(c0,c1);return ycache[yf]
    cand=[]
    for cfg in M:
        for n,(y0,y1) in enumerate(cfg['cells'],1):
            tot=head+tail(y0)+n+3
            cand.append((tot,n,cfg['c'],cfg['K'],cfg['J'],y0))
    cand.sort();tot,n,c,K,J,y0=cand[0]
    mpray=min(tot,final['ray'])
    final_mp=dict(final);final_mp['ray']=mpray
    sig=len(f.pieces)+2
    sec=lambda cells:cells*(0.35+0.45*sig)
    res=dict(base=base,base_total=sum(base.values()),rec=recn,rec_total=sum(recn.values()),lemma1=final,lemma1_total=sum(final.values()),
        mp=dict(ray=mpray,n=n,c=c,K=K,J=J,yfar=y0,lemma_ray_without_mp=final['ray']),final=final_mp,final_total=sum(final_mp.values()),
        sigma=sig,kernel_s_base=sec(sum(base.values())),kernel_s_final=sec(sum(final_mp.values())),
        mu_upper_M3_F=ex.get('mu_upper_M3_F'),pieces_physical=len(f.pieces))
    Path(out).write_text(json.dumps(res,indent=1));print(json.dumps(res))
if __name__=='__main__':main(*sys.argv[1:7])
