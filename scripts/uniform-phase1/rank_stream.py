"""Streaming, row-cleared integer lower certificates. No upper-minor discovery."""
from rank_integer import *
import math

def run_stream(leaf,side):
 source=BASE/f'complete29/production/{leaf}/{side}.json'
 if side not in ('left','right'):source=BASE/f'complete30/production/{leaf}/{side}-normal.json'
 s=json.loads(source.read_text());w=lower(BASE/f'complete30/production/{leaf}/{side}.json')
 n=s['dimension'];d=len(w['V']);v=trans(mat(w['V'])) if d else [[] for _ in range(n)]
 ds=[lcm(*(v[i][j].denominator for i in range(n))) for j in range(d)]
 vi=[[int(v[i][j]*ds[j]) for j in range(d)] for i in range(n)]
 L=left_inv(mat(vi)) if d else [];scale=denom(L);li=scaled(L,scale)
 name=leaf.replace('D58-L','L')+'_'+side.replace('-','_');ns='CatalanMeasure.GenD.Uniform.Bank.StreamRank.'+name
 lines=['module','public import CatalanCore.Uniform.Content.RowCertificate','public import CatalanMeasure.CellCert.RawInts','@[expose] public section','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 50','set_option maxRecDepth 100000',f'namespace {ns}','open Matrix CatalanCore.Uniform.Content','def tapes (m : Nat) (xs : List (List Int)) : Fin m → List Int := fun i => xs.getD i.val []']
 def tape(name,a,m,width):
  lines.append(f'def {name} : Fin {m} → List Int := tapes {m} [\n'+',\n'.join('raw_ints% ['+', '.join(map(str,row))+']' for row in a)+']')
  lines.append(f'theorem {name}_length : ∀ i, ({name} i).length={width} := by decide +kernel')
 tape('Vt',trans(vi),d,n);tape('Lt',li,d,n)
 lines +=[f'def V : Matrix (Fin {n}) (Fin {d}) Int := fromColumns Vt',f'def L : Matrix (Fin {d}) (Fin {n}) Int := fromRows Lt',f'def basisScale : Int := (raw_ints% [{scale}]).getD 0 0','theorem basis_dots : ∀ i j, streamDot (Lt i) (Vt j)=if i=j then basisScale else 0 := by decide +kernel','theorem basis_check : L*V=basisScale • 1 := stream_left_inverse Lt Vt Lt_length Vt_length basisScale basis_dots',f'theorem basis_rank (K : Type*) [Field K] (hs : (basisScale : K)≠0) : (castMatrix K V).rank={d} := integral_basis_rank K V L basisScale basis_check hs']
 rec=[]
 for j,(mp,c) in enumerate(zip(s['active_maps'],w['restriction_certificates'])):
  b=mat(mp['matrix']);r=c['rank'];m=len(b);cc=mat(c['coordinates']);tt=mat(c['basis'])
  td=[[x*ds[k] for k,x in enumerate(row)] for row in tt]
  t=denom(td);ks=[lcm(denom([br]),denom([cr])) for br,cr in zip(b,cc)]
  bi=[scaled([br],k*t)[0] for br,k in zip(b,ks)];ci=[scaled([cr],k)[0] for cr,k in zip(cc,ks)];ti=scaled(td,t)
  assert mul(bi,vi,d)==mul(ci,ti,d)
  tape(f'Bt{j}',bi,m,n);tape(f'Ct{j}',ci,m,r);tape(f'Tt{j}',trans(ti) if r else [[] for _ in range(d)],d,r)
  lines +=[f'def B{j} : Matrix (Fin {m}) (Fin {n}) Int := fromRows Bt{j}',f'def C{j} : Matrix (Fin {m}) (Fin {r}) Int := fromRows Ct{j}',f'def T{j} : Matrix (Fin {r}) (Fin {d}) Int := fromColumns Tt{j}',f'theorem map{j}_dots : ∀ i j, streamDot (Bt{j} i) (Vt j)=streamDot (Ct{j} i) (Tt{j} j) := by decide +kernel',f'theorem map{j}_check : B{j}*V=C{j}*T{j} := stream_factorization Bt{j} Vt Ct{j} Tt{j} Bt{j}_length Vt_length Ct{j}_length Tt{j}_length map{j}_dots',f'theorem map{j}_rank (K : Type*) [Field K] : (castMatrix K B{j}*castMatrix K V).rank≤{r} := integral_image_rank_le K B{j} V C{j} T{j} map{j}_check']
  rec.append({'index':j,'rank':r,'rows':m,'row_scales':[str(k*t) for k in ks],'max_scale_bits':max((int(k*t).bit_length() for k in ks),default=0)})
 lines +=['#print axioms basis_rank',f'end {ns}']
 out=WORK/f'CatalanMeasure/GenD/Uniform/Bank/StreamRank/{name}.lean';out.parent.mkdir(parents=True,exist_ok=True);out.write_text('\n\n'.join(lines)+'\n',encoding='utf-8')
 receipt={'leaf':leaf,'side':side,'n':n,'d':d,'basis_scale_bits':scale.bit_length(),'maps':rec,'bytes':out.stat().st_size,'status':'PASS exact independent row-cleared integer identities; source semantics separate'}
 (OUT/f'{name}-stream-mirror.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print({k:v for k,v in receipt.items() if k!='maps'},flush=True)
if __name__=='__main__':run_stream(*(sys.argv[1:] or ['D58-L0203','right']))
