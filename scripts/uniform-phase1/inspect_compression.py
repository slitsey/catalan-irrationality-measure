from rank_integer import *
for leaf in ['D58-L0108','D58-L0002','D58-L0203']:
 p=BASE/f'complete29/production/{leaf}/compression.json';x=json.loads(p.read_text(),parse_int=str)
 x=x['compression'];print(leaf,'COMP_KEYS',list(x))
 for k,v in x.items():
  if any(z in k.lower() for z in ['centr','degree','bound','width','dim','interval']):
   z=str(v);print(k,z if len(z)<1500 else ('<'+str(len(z))+' chars>'))

