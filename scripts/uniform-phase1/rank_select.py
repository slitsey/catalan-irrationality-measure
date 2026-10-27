from rank_integer import *
from glob import glob
rows=[]
for p in OUT.glob('point-lines-???-???.json'):
 a=json.loads(p.read_text());assert not a['problems'];rows+=a['rows']
a=json.loads((BASE/'complete31/final-audit-2026-10-26/final-audit-result.json').read_text())
chosen=[];missing=[];uncovered=[]
for cell in a['rows']:
 cand=[z for z in rows if z['leaf']==cell['leaf_id']]
 if not cand:uncovered.append(cell['leaf_id']);continue
 for pc in cell['pieces']:
  u,v=map(Q,pc['interval']);c=Q(pc['line']['intercept']);s=Q(pc['line']['slope'])
  if c+s*u==0 and c+s*v==0:
   chosen.append({'leaf':cell['leaf_id'],'interval':pc['interval'],'zero':True});continue
  good=[z for z in cand if Q(z['intercept'])+Q(z['slope'])*u>=c+s*u and Q(z['intercept'])+Q(z['slope'])*v>=c+s*v]
  if not good:missing.append({'leaf':cell['leaf_id'],'piece':pc,'available':[{k:z[k] for k in ['side','intercept','slope','d']} for z in cand]})
  else:
   z=min(good,key=lambda z:(z['n']*z['d'],z['d']));chosen.append({'leaf':cell['leaf_id'],'interval':pc['interval'],'source_side':z['side'],'line':pc['line'],'witness_line':{'intercept':z['intercept'],'slope':z['slope']},'n':z['n'],'d':z['d']})
(OUT/'piece-witness-selection.json').write_text(json.dumps({'chosen':chosen,'missing':missing,'input_rows':len(rows),'uncovered_cells':uncovered},indent=2)+'\n')
print('UNCOVERED',uncovered);print('SELECTION',len(chosen),'missing',len(missing),'unique_packets',len({(z['leaf'],z.get('source_side')) for z in chosen if not z.get('zero')}))
for z in missing[:3]:print(z)

