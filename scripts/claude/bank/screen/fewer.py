"""D16 lever: re-optimise a bank's trial with fewer pieces (C0, nonneg) at the SAME rational polygon.
usage: fewer.py TAG(FIFTH|THIRD|CHI3|LAMB) LAYOUT -> writes d16/fewer/trial-TAG-LAYOUT.json, prints F D, c, mu."""
import sys,json,math,time
sys.dont_write_bytecode=True
from pathlib import Path
ME=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16\fewer');ME.mkdir(exist_ok=True)
REC=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\hybrid-exact-receipts-2026-10-27')
SS='C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/scope-screen-2026-10-27'
sys.path.insert(0,SS)
sys.path[:0]=['C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/python-packages','C:/Users/seanl/Documents/Codex/2026-10-21/users-seanl-documents-codex-2026-10/work/g729-pydeps','C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/pylibs']
from fractions import Fraction as Q
import scope_screen as H
from research_compiler import parse_context
LAY={
 'c3':dict(RB=[0,.04,.12,.22,.32,.42,.5],SB=[0,.0002,.002,.01,.03],LB=[.5,.6,.7,.8,.9,.96,1.],deg=3,fix=.03),
 'g1':dict(RB=[0,.06,.22,.5],SB=[0,.02],LB=[.5,.75,1.],deg=3,fix=.02),
 'g2':dict(RB=[0,.04,.12,.3,.5],SB=[0,.01,.03],LB=[.5,.7,.9,1.],deg=3,fix=.03),
 'g3':dict(RB=[0,.1,.22,.5],SB=[0,.002,.03],LB=[.5,.7,.85,1.],deg=3,fix=.03),
 'g4':dict(RB=[0,.06,.22,.5],SB=[0,.02],LB=[.5,.75,1.],deg=4,fix=.02),
 'g5':dict(RB=[0,.04,.12,.3,.5],SB=[0,.01,.03],LB=[.5,.7,.9,1.],deg=4,fix=.03),
 'g6':dict(RB=[0,.06,.22,.5],SB=[0,.003,.03],LB=[.5,.7,.85,1.],deg=3,fix=.03),
 'g7':dict(RB=[0,.06,.22,.42,.5],SB=[0,.0005,.01,.03],LB=[.5,.7,.9,1.],deg=3,fix=.03),
}

SHAPES={'s1':([0,.5],[0],[.5,1.]),'s2':([0,.5],[0,.02],[.5,1.]),'s3':([0,.5],[0,.02],[.5,.8,1.]),'s4':([0,.1,.5],[0,.02],[.5,.8,1.]),'s5':([0,.06,.22,.5],[0,.02],[.5,.8,1.]),'s6':([0,.5],[0,.02],[.5,.75,.9,1.]),'s7':([0,.5],[0,.005,.03],[.5,.8,1.]),'s8':([0,.3,.5],[0,.02],[.5,.8,1.])}
for k,(rb,sb,lb) in SHAPES.items():
    for dg in (3,4,5):
        LAY[f'{k}d{dg}']=dict(RB=rb,SB=sb,LB=lb,deg=dg,fix=sb[-1])
tag,layout=sys.argv[1:3]
m=json.loads((REC/f'trial-{tag}.json').read_text())['meta']
frame,alpha,r0,ps,ys,B=m['frame'],m['alpha'],m['r0'],m['ps'],m['ys'],m['B']
OUTL=layout
if len(sys.argv)>3:
    PJ=json.loads((ME/f'poly-{tag}-{layout}.json').read_text());r0,ps,ys=PJ['r0'],PJ['ps'],PJ['ys'];OUTL=layout+'p'
prat,plog=m['price']['rational'],m['price']['log2']
if frame.startswith('fifth-'):
    s=H.spec(frame,alpha,'alternating',r0,tuple(ps),tuple(ys));s['frame']['name']='q5-a'+frame.split('-')[-1]
else:s=H.spec(frame,alpha,'alternating',r0,tuple(ps),tuple(ys))
s['parameters']['spline_degree']=4;s['parameters']['nonnegative_density']=True
c=parse_context(s);L=float(Q(prat))+float(Q(plog))*math.log(2)
mod=H.backend(c,True,'high');lay=LAY[layout];d=len(c.frame.poles)
mod.CASES['d']=dict(alpha=float(c.geometry.mass)-1,r0=r0,d=d,eps=.001,Lam=L,B0=B,a12=(.5,1),h=.4)
KW=dict(deg=lay['deg'],fixseg=lay['fix'],c0=True)
t0=time.time()
o=mod.solve('d',ys,ps,raybr=lay['RB'],segbr=lay['SB'],linebr=lay['LB'],B=B,iters=4,**KW,nsamp=1200,fine=True,extra=True)
assert o['status'] in ('Solved','AlmostSolved'),o['status']
ok=bool(o['density']['nonnegative_exact_bernstein'])
meta=dict(frame=frame,alpha=alpha,r0=r0,ys=ys,ps=ps,d=d,gamma=float(c.geometry.degree_scale),mass=float(c.geometry.mass),poles=[[str(x),str(y)] for x,y in c.frame.poles],layout=OUTL,B=B,price=dict(rational=prat,log2=plog),selector=s['selector'],kw=dict(raybr=lay['RB'],segbr=lay['SB'],linebr=lay['LB'],**KW))
json.dump(dict(meta=meta,o=o),open(ME/f'trial-{tag}-{OUTL}.json','w'))
mu=max(o[k]['c']/(o[k]['D']-L) for k in('fine','indep'))
print('RESULT',tag,OUTL,'npieces',o['npieces'],'D fine',o['fine']['D'],'indep',o['indep']['D'],'c',o['fine']['c'],'Lam',L,'mu',mu,'bern',ok,'secs',round(time.time()-t0),flush=True)
