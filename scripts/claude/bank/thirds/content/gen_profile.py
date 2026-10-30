from pathlib import Path
from fractions import Fraction as Q
import json,sys
sys.dont_write_bytecode=True
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
P=R.parents[1]/'outputs/Compatibility programme'
sys.path.insert(0,str(P/'hybrid-alpha-2026-10-27'))
import _paths
sys.path.insert(0,str(P/'q4-mechanisms-uniform-2026-10-27'))
import newprice as N,m3
D=json.loads((P/'bank-specs-2026-10-28/rank-thirds.json').read_text())
al=Q(3,20);left=2*al;right=Q(39,10);hi3=min(right,1+4*al)
res=[]
for case in D['cases']:
 ka=Q(case['pole_cut'])
 rank=[(Q(v['left']),Q(v['right']),N.Line(Q(v['line'][0]),Q(v['line'][1]))) for c in case['cells'] for v in c['price_pieces']]
 cuts={al,left,right,hi3}|{x for x in N.breakpoints(al,ka) if left<x<right}|{x for x in N.g_kinks(al,ka) if left<x<right}
 cuts|={x for u,v,f in rank for x in (u,v)}
 fine=set(cuts)
 for u,v in zip(sorted(cuts),sorted(cuts)[1:]):
  if u<hi3:fine|=m3.kinks(al,ka,u,min(v,hi3))
 fine=sorted(x for x in fine if al<=x<=right);pieces=[]
 for u,v in zip(fine,fine[1:]):
  mid=(u+v)/2
  T=N.Line(2+3*al,Q(-1)) if mid<left else N.trop_line(u,v,al,ka)
  ls=[('T',T)]
  if mid>=left:
   rline=next(f for a,b,f in rank if a<mid<b);ls.append(('R',rline))
   g=N.g_line(mid,al,ka)
   if 1<mid and ka*mid<1 and (1+ka)*mid<1+2*al:g=N.Line(Q(0),Q(0))
   ls.append(('LP',N.Line(T.intercept-g.intercept,T.slope-g.slope)))
  if mid<hi3:ls.extend(('M3D',f) for f in m3.P3_lines(al,ka,u,v))
  sub={u,v}
  for _,f in ls:
   for _,g in ls:
    if f.slope!=g.slope:
     x=(g.intercept-f.intercept)/(f.slope-g.slope)
     if u<x<v:sub.add(x)
  for a,b in zip(sorted(sub),sorted(sub)[1:]):
   tag,f=min(ls,key=lambda tf:tf[1]((a+b)/2))
   assert f(a)>=0 and f(b)>=0
   if pieces and pieces[-1]['line']==[str(f.intercept),str(f.slope)] and pieces[-1]['right']==str(a) and pieces[-1]['layer']==tag:
    pieces[-1]['right']=str(b)
   else:pieces.append(dict(left=str(a),right=str(b),line=[str(f.intercept),str(f.slope)],layer=tag))
 mass=sum((Q(v['line'][0])*(Q(v['right'])-Q(v['left']))+Q(v['line'][1])*(Q(v['right'])**2-Q(v['left'])**2)/2 for v in pieces),Q(0))
 res.append(dict(root=case['root_index'],pieces=pieces,mass=str(mass)))
prefix=4*al+2*al**2-((2+3*al)*al-Q(3,2)*al**2)
A=prefix+sum((Q(c['mass']) for c in res),Q(0))/2
expected=Q(json.loads((P/'bank-specs-2026-10-28/replay-thirds.json').read_text())['noUF']['rational'])
assert A==expected,(A,expected)
out=dict(prefix_rational=str(prefix),prefix_log2=str(2*al**2),lambda_rational=str(A),classes=res,noUF=True,lean_supplier_proved=False)
(R/'scripts/claude/bank/thirds/content/nouf-profile.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print('No-UF profile reproduced exactly; pieces:',[len(c['pieces']) for c in res])
