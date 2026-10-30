"""Exact source partition for rank portions of the no-UF envelope."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';spec=R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-lambda.json';D=json.loads(spec.read_text());P=json.loads((S/'nouf-profile.json').read_text());rows=[]
for prof in P['classes']:
 j=prof['root'];case=next(x for x in D['cases'] if x['prime_class']==j)
 for pi,piece in enumerate(prof['pieces']):
  if piece['layer']!='R':continue
  lo,hi=Q(piece['left']),Q(piece['right']);target=list(map(Q,piece['line']));cuts={lo,hi}
  for c in case['cells']:
   for pc in c['price_pieces']:
    cuts|={x for x in map(Q,[pc['left'],pc['right']]) if lo<x<hi}
  cuts=sorted(cuts);children=[]
  for l,u in zip(cuts,cuts[1:]):
   mid=(l+u)/2;candidates=[]
   for ci,c in enumerate(case['cells']):
    if not Q(c['left'])<=l<u<=Q(c['right']):continue
    vs=list(dict.fromkeys(tuple(pc['V']) for pc in c['price_pieces'] if isinstance(pc['V'],list)))
    for pc in c['price_pieces']:
     if not Q(pc['left'])<=mid<=Q(pc['right']):continue
     line=list(map(Q,pc['line']));margins=[target[0]+target[1]*x-line[0]-line[1]*x for x in [l,u]]
     if min(margins)<0:continue
     name=f'C{j}S{ci:02}'
     suffix=f'_V{vs.index(tuple(pc["V"]))}_member' if isinstance(pc['V'],list) else '_raw_member'
     if not isinstance(pc['V'],list):assert list(map(Q,c['raw']))==line
     candidates.append({'left':str(l),'right':str(u),'cell':name,'theorem':name+suffix,'line':pc['line'],'margins':list(map(str,margins))})
   assert candidates,(j,pi,l,u)
   children.append(candidates[0])
  rows.append({'root':j,'piece':pi,'left':piece['left'],'right':piece['right'],'line':piece['line'],'providers':children})
result={'rank_sha256':hashlib.sha256(spec.read_bytes()).hexdigest(),'lean_acceptance':False,'pieces':rows}
(S/'rank-profile-providers.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print('Partitioned',len(rows),'rank profile pieces into',sum(len(x['providers']) for x in rows),'physical providers')