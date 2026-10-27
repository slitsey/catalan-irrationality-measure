"""Integer-cleared lower witness: exact kernel checks, no determinant discovery."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json,sys
P=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
BASE=P/'outputs/Compatibility programme/thin-windows-2026-10-24'
OUT=P/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank'
WORK=P/'work/catalan-uniform'

def lower(path):
 parts=[];active=False;depth=0;quoted=False;escape=False
 with path.open(encoding='utf-8') as f:
  for line in f:
   if not active:
    if '"lower": {' not in line:continue
    active=True;line=line[line.index('{'):]
   parts.append(line)
   for ch in line:
    if quoted:
     if escape:escape=False
     elif ch=='\\':escape=True
     elif ch=='"':quoted=False
    elif ch=='"':quoted=True
    elif ch=='{':depth+=1
    elif ch=='}':depth-=1
   if depth==0:return json.loads(''.join(parts).rstrip().rstrip(','))
 raise ValueError(path)
def trans(a):return [list(x) for x in zip(*a)]
def mat(a):return [[Q(x) for x in row] for row in a]
def mul(a,b,ncols=None):
 cols=trans(b) if b else [[] for _ in range(ncols or 0)]
 return [[sum((x*y for x,y in zip(row,col)),Q(0)) for col in cols] for row in a]
def denom(a):return lcm(*(x.denominator for row in a for x in row))
def scaled(a,k):return [[int(x*k) for x in row] for row in a]
def inv(a):
 n=len(a); m=[row[:]+[Q(i==j) for j in range(n)] for i,row in enumerate(a)]
 for j in range(n):
  k=next(k for k in range(j,n) if m[k][j]);m[j],m[k]=m[k],m[j]
  q=m[j][j];m[j]=[x/q for x in m[j]]
  for k in range(n):
   if k!=j:
    q=m[k][j];m[k]=[x-q*y for x,y in zip(m[k],m[j])]
 return [row[n:] for row in m]
def left_inv(v):
 n=len(v);d=len(v[0]) if n else 0
 a=trans(v);piv=[];i=0
 for j in range(n):
  k=next((k for k in range(i,d) if a[k][j]),None)
  if k is None:continue
  a[i],a[k]=a[k],a[i];q=a[i][j];a[i]=[x/q for x in a[i]]
  for k in range(i+1,d):
   q=a[k][j];a[k]=[x-q*y for x,y in zip(a[k],a[i])]
  piv.append(j);i+=1
  if i==d:break
 assert i==d
 t=inv([v[j] for j in piv]);out=[[Q(0)]*n for _ in range(d)]
 for i in range(d):
  for k,j in enumerate(piv):out[i][j]=t[i][k]
 return out

def run(leaf,side):
 source=BASE/f'complete29/production/{leaf}/{side}.json'
 if side not in ('left','right'):source=BASE/f'complete30/production/{leaf}/{side}-normal.json'
 s=json.loads(source.read_text()); w=lower(BASE/f'complete30/production/{leaf}/{side}.json')
 v=trans(mat(w['V'])); n=len(v);d=len(v[0]);ds=[lcm(*(v[i][j].denominator for i in range(n))) for j in range(d)]
 vi=[[int(v[i][j]*ds[j]) for j in range(d)] for i in range(n)]
 L=left_inv(mat(vi));scale=denom(L);li=scaled(L,scale)
 assert mul(li,vi)==[[scale*int(i==j) for j in range(d)] for i in range(d)]
 name=leaf.replace('D58-L','L')+'_'+side.replace('-','_'); ns='CatalanMeasure.GenD.Uniform.Bank.Rank.'+name
 lines=['module','public import CatalanCore.Uniform.Content.RankCertificate','public import CatalanMeasure.CellCert.RawInts','@[expose] public section','set_option Elab.async false','set_option profiler true','set_option maxRecDepth 100000',f'namespace {ns}','open Matrix CatalanCore.Uniform.Content','def intMat (m n : Nat) (xs : List Int) : Matrix (Fin m) (Fin n) Int :=\n  fun i j => xs.getD (i.val*n+j.val) 0']
 def emit(name,a,m,r):
  lines.append(f'def {name} : Matrix (Fin {m}) (Fin {r}) Int := intMat {m} {r} (raw_ints% ['+', '.join(str(x) for row in a for x in row)+'])')
 emit('V',vi,n,d);emit('L',li,d,n)
 lines +=[f'def basisScale : Int := {scale}', 'theorem basis_check : L*V=basisScale • 1 := by decide +kernel',f'theorem basis_rank (K : Type*) [Field K] (hs : (basisScale : K)≠0) : (castMatrix K V).rank={d} := integral_basis_rank K V L basisScale basis_check hs']
 rec=[]
 for j,(mp,c) in enumerate(zip(s['active_maps'],w['restriction_certificates'])):
  b=mat(mp['matrix']);r=c['rank'];m=len(b);cc=mat(c['coordinates']);tt=mat(c['basis'])
  td=[[x*ds[k] for k,x in enumerate(row)] for row in tt]
  k=lcm(denom(b),denom(cc));t=denom(td);bi=scaled(b,k*t);ci=scaled(cc,k);ti=scaled(td,t)
  assert mul(bi,vi,d)==mul(ci,ti,d)
  emit(f'B{j}',bi,m,n);emit(f'C{j}',ci,m,r);emit(f'T{j}',ti,r,d)
  lines +=[f'def mapScale{j} : Int := {k*t}',f'theorem map{j}_check : B{j}*V=C{j}*T{j} := by decide +kernel',f'theorem map{j}_rank (K : Type*) [Field K] : (castMatrix K B{j}*castMatrix K V).rank≤{r} := integral_image_rank_le K B{j} V C{j} T{j} map{j}_check']
  rec.append({'index':j,'rank':r,'rows':m,'scale':str(k*t)})
 lines +=['#print axioms basis_rank',f'end {ns}']
 out=WORK/f'CatalanMeasure/GenD/Uniform/Bank/Rank/{name}.lean';out.parent.mkdir(parents=True,exist_ok=True);out.write_text('\n\n'.join(lines)+'\n',encoding='utf-8')
 rr={'leaf':leaf,'side':side,'n':n,'d':d,'basisScale':str(scale),'maps':rec,'status':'PASS exact independent integer identities; source semantics separate'}
 (OUT/f'{name}-integer-mirror.json').write_text(json.dumps(rr,indent=2)+'\n');print(rr,flush=True)
if __name__=='__main__':run(*(sys.argv[1:] or ['D58-L0203','right']))

