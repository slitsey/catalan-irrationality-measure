from pathlib import Path
import json,hashlib
from fractions import Fraction as Q
r=Path('.').resolve();p=r.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-lambda.json';d=json.loads(p.read_text());counts=[];pieces=0
for case in d['cases']:
 for ci,c in enumerate(case['cells']):
  rs=cs=[Q(0),Q(0)];rs=[Q(0),Q(0)];cs=[Q(0),Q(0)]
  for run in c['runs']:
   t=case['types'][run['type_id']];assert len(t['killed_rows'])<=1 and len(t['killed_columns'])<=1
   for loads in [t['row_loads'],t['column_loads']]:assert all(any(Q(x) for x in v) for v in loads)
   n=[Q(run['count'][k]) for k in ['intercept','slope']]
   for k in range(2):rs[k]+=len(t['killed_rows'])*n[k];cs[k]+=len(t['killed_columns'])*n[k]
  assert rs==cs==list(map(Q,c['balanced_kills']))
  assert [Q(11,5)-rs[0],-rs[1]]==list(map(Q,c['raw']))
  row={'cell':f'C{case["prime_class"]}S{ci:02}','balanced_kills':list(map(str,rs)),'pieces':[]}
  for pc in c['price_pieces']:
   v=pc['V'];weights=[];match=[Q(0),Q(0)]
   if isinstance(v,list):
    v=list(map(Q,v))
    for run in c['runs']:
     t=case['types'][run['type_id']];w=sum(Q(z[0])*v[1]-Q(z[1])*v[0]==0 for z in t['row_loads']+t['column_loads']);weights.append(w)
     for k,key in enumerate(['intercept','slope']):match[k]+=w*Q(run['count'][key])
    gain=[match[k]-rs[k] for k in range(2)]
   elif v=='zero':gain=[Q(0),Q(0)]
   elif v=='top':gain=[cs[k]-rs[k] for k in range(2)]
   else:raise ValueError(v)
   assert gain==list(map(Q,pc['gain']))
   assert [Q(c['raw'][k])-gain[k] for k in range(2)]==list(map(Q,pc['line']))
   row['pieces'].append({'left':pc['left'],'right':pc['right'],'V':pc['V'],'match_weights':weights,'matched_count':list(map(str,match)),'gain':list(map(str,gain))});pieces+=1
  counts.append(row)
out={'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cells_checked':len(counts),'pieces_checked':pieces,'lean_acceptance':False,'scope':'Exact leading affine row/column balance and selected zero/full/line gain arithmetic; does not prove physical count errors or rank supplier.','cells':counts}
(r/'scripts/codex/bank/lambda/rank-accounting.json').write_text(json.dumps(out,indent=2),encoding='utf-8');print('Verified leading affine balance and selected line accounting:',len(counts),'cells',pieces,'pieces')
