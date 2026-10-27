"""Bounded streaming inventory of lower source packets; no upper minor replay."""
from pathlib import Path
import json,re,time
from rank_integer import lower,BASE,OUT
start=time.monotonic();rows=[];problems=[]
for folder in sorted((BASE/'complete30/production').glob('D58-L*')):
 for path in [folder/'left.json',folder/'right.json']+sorted(folder.glob('k*.json')):
  if not path.exists() or not(path.stem in ('left','right') or re.fullmatch(r'k\d+_\d+',path.stem)):continue
  try:
   w=lower(path);v=w.get('V',[]);d=len(v);n=len(v[0]) if d else 0
   source=(BASE/f'complete29/production/{folder.name}/{path.name}') if path.stem in ('left','right') else path.with_name(path.stem+'-normal.json')
   s=json.loads(source.read_text())
   assert not d or n==s['dimension']
   rows.append({'leaf':folder.name,'side':path.stem,'n':s['dimension'],'d':d,'maps':len(s['active_maps']),'entries':sum(len(x['matrix'])*s['dimension'] for x in s['active_maps']),'leading_weights':s.get('leading_weight_certificates'),'interval':s['interval'],'knot':s['knot']})
  except Exception as e:problems.append({'path':str(path),'error':repr(e)})
 if len(rows)%25<3:print('INVENTORY',folder.name,len(rows),'problems',len(problems),flush=True)
 (OUT/'rank-packet-inventory.json').write_text(json.dumps({'rows':rows,'problems':problems,'elapsed':time.monotonic()-start},indent=2)+'\n')
print('INVENTORY_COMPLETED',len(rows),'problems',len(problems),'max_n',max((r['n'] for r in rows),default=0),'max_d',max((r['d'] for r in rows),default=0),flush=True)
