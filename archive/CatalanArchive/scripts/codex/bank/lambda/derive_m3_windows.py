"""Exact leading M3 gap witnesses for the finite no-UF profile, not Lean acceptance."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';P=S/'nouf-profile.json';D=json.loads(P.read_text());rows=[]
def endpoints(j,t,n0,n1,n3):
 k=j*t/4
 A=max(n0*t,n1*t+k,1+n3*t,1,Q(6,5)-t)
 B=min((n0+1)*t,(n1+1)*t+k,1+(n3+1)*t,Q(6,5),1+t)
 return A,B
for case in D['classes']:
 j=case['root']
 for ci,c in enumerate(case['pieces']):
  if c['layer']!='M3D':continue
  lo,hi=Q(c['left']),Q(c['right']);a,b=map(Q,c['line']);mid=(lo+hi)/2
  cand=[]
  for n0 in range(int(Q(6,5)/lo)+1):
   for n1 in range(int(Q(6,5)/lo)+1):
    n3=0
    margins=[]
    for t in (lo,hi):
     A,B=endpoints(j,t,n0,n1,n3);margins.append(B-A-(Q(11,5)-a-b*t))
    if min(margins)>=0:
     A,B=endpoints(j,mid,n0,n1,n3);cand.append((B-A,n0,n1,n3,margins))
  assert cand,(j,ci,c)
  width,n0,n1,n3,margins=max(cand)
  rows.append({'root':j,'piece':ci,'left':c['left'],'right':c['right'],'line':c['line'],'gaps':[n0,n1,n3],'endpoint_margins':list(map(str,margins))})
result={'profile_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'lean_acceptance':False,'witnesses':rows}
(S/'m3-profile-witnesses.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print('Exact M3 gap witnesses:',len(rows))