"""fewer-pieces trials for the sevenths a=1 frame at alpha=1/12 (same rational polygon as exact-check trial-A). usage: fewer7.py LAYOUT"""
import sys,json,math,time
sys.dont_write_bytecode=True
from pathlib import Path
sys.path.insert(0,'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/sevenths-decay-2026-10-27')
ME=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16\fewer')
import dec
exec(open(r'scripts\claude\bank\screen\fewer.py').read().split("tag,layout=")[0].split("LAY={")[0].split("from fractions")[0]) if False else None
src=open(r'scripts\claude\bank\screen\fewer.py').read()
LAY={}
exec("LAY={"+src.split("LAY={")[1].split("tag,layout=")[0].replace("from fractions import Fraction as Q","") ,globals())
layout=sys.argv[1]
OUTL=layout
alpha='1/12';r0=.1365;ys=[.0787,.2082];ps=[-.5042,-.3776,-.2706];B=3218.6
if len(sys.argv)>2:
    PJ=json.loads((ME/f'poly-A-{layout}.json').read_text());r0,ps,ys=PJ['r0'],PJ['ps'],PJ['ys'];OUTL=layout+'p'
s,c=dec.ctx(alpha);mod=dec.module(alpha,True);d=len(c.frame.poles)
rat_log2=('PLACEHOLDER')
prat,plog='RATPLACE','1/72'
import json as J
ex=J.load(open(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\sevenths-decay-2026-10-27\exact-check\exact-A.json'))
prat=ex['Lambda_M3'];plog='0'
from fractions import Fraction as Q
L=float(Q(prat))+float(Q(plog))*math.log(2)
lay=LAY[layout]
mod.CASES['d']=dict(alpha=float(c.geometry.mass)-1,r0=r0,d=d,eps=.001,Lam=L,B0=B,a12=(.5,1),h=.4)
KW=dict(deg=lay['deg'],fixseg=lay['fix'],c0=True);t0=time.time()
o=mod.solve('d',ys,ps,raybr=lay['RB'],segbr=lay['SB'],linebr=lay['LB'],B=B,iters=4,**KW,nsamp=1200,fine=True,extra=True)
assert o['status'] in ('Solved','AlmostSolved'),o['status']
ok=bool(o['density']['nonnegative_exact_bernstein'])
meta=dict(frame='sevenths',alpha=alpha,r0=r0,ys=ys,ps=ps,d=d,gamma=float(c.geometry.degree_scale),mass=float(c.geometry.mass),layout=OUTL,B=B,price=dict(rational=prat,log2=plog),kw=dict(raybr=lay['RB'],segbr=lay['SB'],linebr=lay['LB'],**KW))
json.dump(dict(meta=meta,o=o),open(ME/f'trial-A-{OUTL}.json','w'))
mu=max(o[k]['c']/(o[k]['D']-L) for k in('fine','indep'))
print('RESULT','A',OUTL,'npieces',o['npieces'],'D fine',o['fine']['D'],'indep',o['indep']['D'],'c',o['fine']['c'],'Lam',L,'mu',mu,'bern',ok,'secs',round(time.time()-t0),flush=True)
