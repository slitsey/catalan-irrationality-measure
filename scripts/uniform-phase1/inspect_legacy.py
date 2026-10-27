from rank_integer import *
for name in ['complete15/square-chain-certificate.json','complete15/actual-square-compact-certificate.json','complete14/supported-gap-rank-certificate.json','complete30/production-high-x-whole-cell.json']:
 p=BASE/name
 if not p.exists():print('MISSING',name);continue
 x=json.loads(p.read_text(),parse_int=str);print(name,list(x))
 for k,v in x.items():
  if any(a in k.lower() for a in ['lower','witness','basis','vector','source','profile','point','rank']):
   text=str(v);print(k,text if len(text)<500 else '<'+str(len(text))+' chars>')
