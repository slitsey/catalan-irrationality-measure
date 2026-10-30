"""Nelder-Mead polygon re-optimisation for a fewer-piece layout (F). usage: polyopt.py TAG LAYOUT NEVAL"""
import sys,json,math,time
sys.dont_write_bytecode=True
from pathlib import Path
src=open(r'scripts\claude\bank\screen\fewer.py').read()
head=src.split("tag,layout=sys.argv[1:3]")[0]
exec(head)
tag,layout,NEV=sys.argv[1],sys.argv[2],int(sys.argv[3])
import numpy as np
from scipy.optimize import minimize
if tag=='A':
    sys.path.insert(0,'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/sevenths-decay-2026-10-27')
    import dec
    m=dict(r0=.1365,ys=[.0787,.2082],ps=[-.5042,-.3776,-.2706],B=3218.6)
    s,c=dec.ctx('1/12');mod=dec.module('1/12',True);d=len(c.frame.poles);L=3.640175392747;alpha_f=float(c.geometry.mass)-1
else:
    m=json.loads((REC/f'trial-{tag}.json').read_text())['meta']
    frame,alpha=m['frame'],m['alpha'];prat,plog=m['price']['rational'],m['price']['log2']
    r0=m['r0']
    if frame.startswith('fifth-'):
        s=H.spec(frame,alpha,'alternating',r0,tuple(m['ps']),tuple(m['ys']));s['frame']['name']='q5-a'+frame.split('-')[-1]
    else:s=H.spec(frame,alpha,'alternating',r0,tuple(m['ps']),tuple(m['ys']))
    s['parameters']['spline_degree']=4;s['parameters']['nonnegative_density']=True
    c=parse_context(s);L=float(Q(prat))+float(Q(plog))*math.log(2);mod=H.backend(c,True,'high');d=len(c.frame.poles);alpha_f=float(c.geometry.mass)-1
lay=LAY[layout];KW=dict(deg=lay['deg'],fixseg=lay['fix'],c0=True)
n=len(m['ps']);x0=np.array([m['r0']]+list(m['ps'])+list(m['ys']))
B=m['B'];best=[None,1e9];cnt=[0]
def unpack(x):return x[0],list(x[1:1+n]),list(x[1+n:])
def f(x):
    r0,ps,ys=unpack(x)
    if r0<=0.02 or any(b<=a for a,b in zip([0]+ys,ys)) or ys[0]<=0 or ps[-1]<-1.0 or any(p>-0.02 for p in ps) or ys[-1]>0.75:return 1e3
    mod.CASES['d']=dict(alpha=alpha_f,r0=r0,d=d,eps=.001,Lam=L,B0=B,a12=(.5,1),h=.4)
    try:
        o=mod.solve('d',ys,ps,raybr=lay['RB'],segbr=lay['SB'],linebr=lay['LB'],B=B,iters=1,**KW,nsamp=800,fine=True,extra=True)
        if o['status'] not in ('Solved','AlmostSolved') or not o['density']['nonnegative_exact_bernstein']:return 1e3
        D=min(o['fine']['D'],o['indep']['D']);v=-D
    except Exception as e:return 1e3
    cnt[0]+=1
    if v<best[1]:best[0]=x.copy();best[1]=v;print('eval',cnt[0],'D',-v,flush=True)
    return v
t0=time.time()
step=np.array([0.004]+[0.02]*n+[0.01]*(n-1))
sim=[x0]+[x0+np.eye(len(x0))[i]*step[i] for i in range(len(x0))]
res=minimize(f,x0,method='Nelder-Mead',options=dict(maxfev=NEV,initial_simplex=np.array(sim),xatol=1e-5,fatol=1e-9))
x=best[0];r0,ps,ys=unpack(x)
rd=lambda v:round(float(v),5)
out=dict(tag=tag,layout=layout,r0=rd(r0),ps=[rd(p) for p in ps],ys=[rd(y) for y in ys],D=-best[1],secs=time.time()-t0,evals=cnt[0])
Path(ME/f'poly-{tag}-{layout}.json').write_text(json.dumps(out));print('POLY',json.dumps(out),flush=True)
