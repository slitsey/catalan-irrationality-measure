"""Full original-source rank certificates with symbolic row scales and exceptions."""
from rank_integer import *

def factor_small(bv,d):
 a=[row[:] for row in bv];m=len(a);i=0;piv=[]
 for j in range(d):
  k=next((k for k in range(i,m) if a[k][j]),None)
  if k is None:continue
  a[i],a[k]=a[k],a[i];q=a[i][j];a[i]=[x/q for x in a[i]]
  for k in range(m):
   if k!=i and a[k][j]:
    q=a[k][j];a[k]=[x-q*y for x,y in zip(a[k],a[i])]
  piv.append(j);i+=1
 T=a[:i];C=[[row[j] for j in piv] for row in bv]
 assert mul(C,T,d)==bv
 return {'rank':i,'coordinates':C,'basis':T}

def run_source(leaf,side):
 path=BASE/f'complete30/production/{leaf}/{side}.json';w=lower(path)
 sp=BASE/f'complete29/production/{leaf}/{side}.json' if side in ('left','right') else path.with_name(side+'-normal.json')
 s=json.loads(sp.read_text());n=s['dimension'];d=len(w['V']);v=trans(mat(w['V'])) if d else [[] for _ in range(n)]
 ds=[lcm(*(v[i][j].denominator for i in range(n))) for j in range(d)]
 vi=[[int(v[i][j]*ds[j]) for j in range(d)] for i in range(n)]
 L=left_inv(mat(vi)) if d else [];scale=denom(L);li=scaled(L,scale)
 known={int(mp['compressed_map_index']):c for mp,c in zip(s['active_maps'],w['restriction_certificates'])}
 maps=sorted(s['active_maps']+s['dropped_zero_weight_maps'],key=lambda z:int(z['compressed_map_index']))
 name=leaf.replace('D58-L','L')+'_'+side.replace('-','_');ns='CatalanMeasure.GenD.Uniform.Bank.SourceRank.'+name
 lines=['module','public import CatalanCore.Uniform.Content.ScaledStreamCertificate','public import CatalanCore.Uniform.Content.ExceptionCertificate','public import CatalanMeasure.CellCert.RawInts','@[expose] public section','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 50','set_option maxRecDepth 100000',f'namespace {ns}','open Matrix CatalanCore.Uniform.Content','def tapes (m : Nat) (xs : List (List Int)) : Fin m → List Int := fun i => xs.getD i.val []']
 def tape(name,a,m,width):
  lines.append(f'def {name} : Fin {m} → List Int := tapes {m} [\n'+',\n'.join('raw_ints% ['+', '.join(map(str,row))+']' for row in a)+']')
  lines.append(f'theorem {name}_length : ∀ i, ({name} i).length={width} := by decide +kernel')
 def scalars(name,a,m):lines.append(f'def {name} : Fin {m} → Int := fun i => (raw_ints% ['+', '.join(map(str,a))+']).getD i.val 1')
 tape('Vt',trans(vi),d,n);tape('Lt',li,d,n)
 lines +=[f'def V : Matrix (Fin {n}) (Fin {d}) Int := fromColumns Vt',f'def L : Matrix (Fin {d}) (Fin {n}) Int := fromRows Lt',f'def basisScale : Int := (raw_ints% [{scale}]).getD 0 0','theorem basis_dots : ∀ i j, streamDot (Lt i) (Vt j)=if i=j then basisScale else 0 := by decide +kernel','theorem basis_check : L*V=basisScale • 1 := stream_left_inverse Lt Vt Lt_length Vt_length basisScale basis_dots',f'theorem basis_rank (K : Type*) [Field K] (hs : (basisScale : K)≠0) : (castMatrix K V).rank={d} := integral_basis_rank K V L basisScale basis_check hs']
 lines += ['theorem basisScale_pos : (0 : Int)<basisScale := by decide +kernel']
 rec=[]
 for j,mp in enumerate(maps):
  b=mat(mp['matrix']);m=len(b);bv=mul(b,v,d);c=known.get(int(mp['compressed_map_index']))
  if c is None:c=factor_small(bv,d)
  r=c['rank'];cc=mat(c['coordinates']);tt=mat(c['basis']);assert mul(cc,tt,d)==bv
  td=[[x*ds[k] for k,x in enumerate(row)] for row in tt];t=denom(td)
  db=[denom([br]) for br in b];ks=[lcm(z,denom([cr])) for z,cr in zip(db,cc)]
  br=[scaled([row],z)[0] for row,z in zip(b,db)];ss=[k*t//z for k,z in zip(ks,db)]
  ci=[scaled([row],k)[0] for row,k in zip(cc,ks)];ti=scaled(td,t)
  assert [[ss[i]*x for x in row] for i,row in enumerate(mul(br,vi,d))]==mul(ci,ti,d)
  nums=[[x.numerator for x in row] for row in b];dens=[[x.denominator for x in row] for row in b]
  tape(f'Bt{j}',br,m,n);tape(f'Ct{j}',ci,m,r);tape(f'Tt{j}',trans(ti) if r else [[] for _ in range(d)],d,r)
  tape(f'Nt{j}',nums,m,n);tape(f'Dt{j}',dens,m,n);scalars(f'D{j}',db,m);scalars(f'S{j}',ss,m)
  lines +=[f'def B{j} : Matrix (Fin {m}) (Fin {n}) Int := scaledRows S{j} Bt{j}',f'def C{j} : Matrix (Fin {m}) (Fin {r}) Int := fromRows Ct{j}',f'def T{j} : Matrix (Fin {r}) (Fin {d}) Int := fromColumns Tt{j}',f'theorem map{j}_dots : ∀ i j, S{j} i*streamDot (Bt{j} i) (Vt j)=streamDot (Ct{j} i) (Tt{j} j) := by decide +kernel',f'theorem map{j}_check : B{j}*V=C{j}*T{j} := stream_scaled_factorization S{j} Bt{j} Vt Ct{j} Tt{j} Bt{j}_length Vt_length Ct{j}_length Tt{j}_length map{j}_dots',f'theorem map{j}_normalization : ∀ i, rowNormalization (D{j} i) (Nt{j} i) (Dt{j} i) (Bt{j} i)=true := by decide +kernel',f'def exception{j} : Int := exceptionInteger basisScale (fun i => D{j} i*S{j} i) (fun i (k : Fin {n}) => (Dt{j} i).getD k.val 0)',f'theorem source{j}_rank (K : Type*) [Field K] (h : (exception{j} : K)≠0) : ((sourceFractions K Nt{j} Dt{j} : Matrix (Fin {m}) (Fin {n}) K)*castMatrix K V).rank≤{r} := by\n  have hu := exception_units K basisScale (fun i => D{j} i*S{j} i) (fun i (k : Fin {n}) => (Dt{j} i).getD k.val 0) h\n  have hds : ∀ i, (D{j} i : K)≠0 ∧ (S{j} i : K)≠0 := by\n    intro i\n    simpa only [Int.cast_mul,mul_ne_zero_iff] using hu.2.1 i\n  exact source_scaled_rank_le K Nt{j} Dt{j} Bt{j} D{j} S{j} V C{j} T{j} map{j}_normalization hu.2.2 (fun i => (hds i).1) (fun i => (hds i).2) map{j}_check']
  lines += [f'theorem exception{j}_rows_pos : ∀ i, (0 : Int)<D{j} i*S{j} i := by decide +kernel',f'theorem exception{j}_den_pos : ∀ i (k : Fin {n}), (0 : Int)<(Dt{j} i).getD k.val 0 := by decide +kernel',f'theorem exception{j}_pos : (0 : Int)<exception{j} := exceptionInteger_pos basisScale (fun i => D{j} i*S{j} i) (fun i (k : Fin {n}) => (Dt{j} i).getD k.val 0) basisScale_pos exception{j}_rows_pos exception{j}_den_pos']
  rec.append({'index':j,'compressed_map_index':mp['compressed_map_index'],'rank':r,'rows':m,'new_zero_knot_factor':int(mp['compressed_map_index']) not in known})
 lines+=['#print axioms basis_rank']+[f'#print axioms source{j}_rank' for j in range(len(maps))]+[f'end {ns}']
 out=WORK/f'CatalanMeasure/GenD/Uniform/Bank/SourceRank/{name}.lean';out.parent.mkdir(parents=True,exist_ok=True);out.write_text('\n\n'.join(lines)+'\n',encoding='utf-8')
 receipt={'leaf':leaf,'side':side,'n':n,'d':d,'maps':rec,'bytes':out.stat().st_size,'status':'PASS exact full original-source integer identities, field reduction still requires own Lean completion'}
 (OUT/f'{name}-source-mirror.json').write_text(json.dumps(receipt,indent=2)+'\n');print({k:v for k,v in receipt.items() if k!='maps'},flush=True)
if __name__=='__main__':run_source(*(sys.argv[1:] or ['D58-L0002','left']))

