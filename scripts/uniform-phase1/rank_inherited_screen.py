from rank_integer import *
import hashlib
sys.path.insert(0,str(P/'work/pylibs'))
import flint
flint.ctx.threads=1
cat=json.loads((BASE/'complete31/accepted-subspace-proposals.json').read_text())+json.loads((P/'outputs/Compatibility programme/scope-screen-2026-10-27/g-extra-proposals.json').read_text())
for leaf,interval,desired in [('D58-L0108',('4','150/37'),('-8','2')),('D58-L0109',('69/17','53/13'),('-14','7/2'))]:
 s=json.loads((BASE/f'complete29/production/{leaf}/right.json').read_text());comp=json.loads((BASE/f'complete29/production/{leaf}/compression.json').read_text())['compression'];n=s['dimension'];names=s['coordinate_names']
 maps=sorted(s['active_maps']+s['dropped_zero_weight_maps'],key=lambda z:int(z['compressed_map_index']));bm=[flint.fmpq_mat(mp['matrix']) for mp in maps]
 l,r=map(Q,s['interval']);u,v=map(Q,interval);ic,sl=map(Q,desired)
 cc=comp['central_coefficient'];central=lambda x:Q(cc.get('N',0))+(Q(cc.get('hp',0))/2+Q(cc.get('p',0)))*x
 wc={int(z['map']):z for z in s['leading_weight_certificates']}
 def weights(x):return [Q(wc[int(mp['compressed_map_index'])]['at_left'])+(Q(wc[int(mp['compressed_map_index'])]['at_right'])-Q(wc[int(mp['compressed_map_index'])]['at_left']))*(x-l)/(r-l) for mp in maps]
 wu,wv=weights(u),weights(v);candidates=[];seen=set()
 for z in cat:
  old=z.get('coordinate_names');V=z['V']
  if V and len(V[0])==n:candidates.append((z['source'],V))
  if old and len(set(names)&set(old))/max(len(names),len(old))>=.6:
   idx={a:i for i,a in enumerate(old)};candidates.append((z['source']+' mapped',[[row[idx[a]] if a in idx else '0' for a in names] for row in V]))
 accepted=[]
 for tag,V in candidates:
  sig=hashlib.sha256(json.dumps(V).encode()).hexdigest()
  if sig in seen:continue
  seen.add(sig);M=flint.fmpq_mat(V);R,d=M.rref()
  if not d:continue
  V=[[str(R[i,j]) for j in range(n)] for i in range(d)];M=flint.fmpq_mat(V).transpose();rs=[(B*M).rank() for B in bm]
  eu=central(u)*d-sum((a*b for a,b in zip(wu,rs)),Q(0));ev=central(v)*d-sum((a*b for a,b in zip(wv,rs)),Q(0))
  if eu>=ic+sl*u and ev>=ic+sl*v:
   accepted.append({'source':tag,'n':n,'d':d,'V':V,'ranks':rs,'values':[str(eu),str(ev)]});print('LOWER_CANDIDATE_PASS',leaf,'d',d,'source',tag,flush=True);break
 (OUT/f'{leaf}-inherited-direct-proposal.json').write_text(json.dumps({'leaf':leaf,'tested':len(seen),'accepted':accepted,'scope':'exact rational lower proposals only; Lean source matrix checks still required'},indent=2)+'\n')
 print('SCREEN_DONE',leaf,'tested',len(seen),'accepted',len(accepted),flush=True)
