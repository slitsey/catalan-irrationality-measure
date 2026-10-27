"""Actual lower-subspace affine profiles, including maps zero at a sampled knot."""
from rank_integer import *
import re,time

def rank_small(a):
 a=[row[:] for row in a];m=len(a);d=len(a[0]) if m else 0;i=0
 for j in range(d):
  k=next((k for k in range(i,m) if a[k][j]),None)
  if k is None:continue
  a[i],a[k]=a[k],a[i];q=a[i][j];a[i]=[x/q for x in a[i]]
  for k in range(i+1,m):
   q=a[k][j]
   if q:a[k]=[x-q*y for x,y in zip(a[k],a[i])]
  i+=1
 return i

def point_line(leaf,side):
 path=BASE/f'complete30/production/{leaf}/{side}.json';w=lower(path);vs=w['V'];d=len(vs)
 source=(BASE/f'complete29/production/{leaf}/{side}.json') if side in ('left','right') else path.with_name(side+'-normal.json')
 s=json.loads(source.read_text());n=s['dimension'];v=trans(mat(vs)) if d else [[] for _ in range(n)]
 assert rank_small(v)==d
 maps=sorted(s['active_maps']+s['dropped_zero_weight_maps'],key=lambda z:int(z['compressed_map_index']))
 ranks={int(z['compressed_map_index']):rank_small(mul(mat(z['matrix']),v,d)) if d else 0 for z in maps}
 comp=json.loads((BASE/f'complete29/production/{leaf}/compression.json').read_text())['compression']
 central=comp['central_coefficient'];assert set(central)<={'N','hp','1'}
 def central_at(x):return Q(central.get('N',0))+Q(central.get('hp',0))*x/2
 l,r=map(Q,s['interval']);knot=Q(s['knot']);assert central_at(knot)==Q(s['leading_central'])
 vl=central_at(l)*d;vr=central_at(r)*d;vk=central_at(knot)*d
 assert set(ranks)=={int(z['map']) for z in s['leading_weight_certificates']}
 for z in s['leading_weight_certificates']:
  rk=ranks[int(z['map'])];vl-=Q(z['at_left'])*rk;vr-=Q(z['at_right'])*rk;vk-=Q(z['at_knot'])*rk
 assert vk==Q(w['value'])/Q(s['integer_weight_scale']),(leaf,side,vk,w['value'],s['integer_weight_scale'])
 slope=(vr-vl)/(r-l);intercept=vl-slope*l
 return {'leaf':leaf,'side':side,'n':n,'d':d,'intercept':str(intercept),'slope':str(slope),'point':str(knot),'value':str(vk),'ranks':ranks,'maps':len(maps)}

if __name__=='__main__':
 lo,hi=map(int,sys.argv[1:] or ['0','10']);rows=[];problems=[];start=time.monotonic()
 for k in range(lo,hi):
  leaf=f'D58-L{k:04}';folder=BASE/f'complete30/production/{leaf}'
  for path in [folder/'left.json',folder/'right.json']+sorted(folder.glob('k*.json')):
   if not path.exists() or not(path.stem in ('left','right') or re.fullmatch(r'k\d+_\d+',path.stem)):continue
   try:rows.append(point_line(leaf,path.stem))
   except Exception as e:problems.append({'leaf':leaf,'side':path.stem,'error':repr(e)})
  (OUT/f'point-lines-{lo:03}-{hi:03}.json').write_text(json.dumps({'rows':rows,'problems':problems,'elapsed':time.monotonic()-start},indent=2)+'\n')
  print('PROFILE',leaf,len(rows),'problems',len(problems),flush=True)
 print('PROFILES_COMPLETED',lo,hi,'rows',len(rows),'problems',len(problems),flush=True)


