from rank_integer import *
for leaf in ['D58-L0000','D58-L0002','D58-L0203']:
 p=BASE/f'complete30/production/{leaf}/whole-cell.json'
 w=json.loads(p.read_text(),parse_int=str)
 print(leaf,'WHOLE_KEYS',list(w))
 for k,v in w.items():
  if k not in ['required_integer_units','pieces','knot_maxima','knot_packet_sha256']:
   text=str(v)
   if len(text)<1500:print(k,text)
 p=BASE/f'complete29/production/{leaf}/left.json'
 s=json.loads(p.read_text(),parse_int=str)
 print('SOURCE',s['knot'],s['leading_central'],'dimension',s['dimension'],'active',len(s['active_maps']),'weightcerts',len(s['leading_weight_certificates']),'dropped',len(s['dropped_zero_weight_maps']))
 print('W_CERT_0',s['leading_weight_certificates'][:1]);print('MAXIMUM',s['maximum'])

