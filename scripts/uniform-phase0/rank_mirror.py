"""Exact independent Fraction replay and Lean emitter for D58-L0203/right.
No imported campaign arithmetic, floating point, solver or expected-rank premise.
"""
from fractions import Fraction as F
from pathlib import Path
import json, hashlib
ROOT=Path(__file__).resolve().parents[2]
BASE=Path('C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/thin-windows-2026-10-24')
src=BASE/'complete29/production/D58-L0203/right.json'
wit=BASE/'complete30/production/D58-L0203/right.json'
s=json.loads(src.read_text()); w=json.loads(wit.read_text())
def matrix(a): return [[F(x) for x in r] for r in a]
def trans(a): return list(map(list,zip(*a)))
def mul(a,b):
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in trans(b)] for row in a]
def rank(a):
    a=[r[:] for r in a]; i=0
    if not a:return 0
    for j in range(len(a[0])):
        k=next((k for k in range(i,len(a)) if a[k][j]),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i]; z=a[i][j]; a[i]=[x/z for x in a[i]]
        for k in range(len(a)):
            if k!=i:
                z=a[k][j]; a[k]=[x-z*y for x,y in zip(a[k],a[i])]
        i+=1
        if i==len(a):break
    return i
V=trans(matrix(w['lower']['V'])); assert rank(V)==3
lines=['module','public import Mathlib.LinearAlgebra.Matrix.Rank','public import CatalanMeasure.CellCert.RawInts','@[expose] public section','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 0','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace CatalanMeasure.GenD.Uniform.PilotRank','open Matrix', '''
/-! Real D58 source-cell pilot: D58-L0203, right endpoint x=26.
The rank certificates concern the exported rational source maps. Physical-prefix
transport, source coverage and reduction away from exceptional primes remain
separate obligations; this file does not claim a content or measure theorem. -/

def ratMat (m n : Nat) (nums dens : List Int) : Matrix (Fin m) (Fin n) Rat :=
  fun i j => (nums.getD (i.val * n + j.val) 0 : Rat) /
    (dens.getD (i.val * n + j.val) 1 : Rat)

theorem rank_le_of_factorization {m n r : Nat}
    (A : Matrix (Fin m) (Fin n) Rat)
    (C : Matrix (Fin m) (Fin r) Rat) (T : Matrix (Fin r) (Fin n) Rat)
    (h : A = C * T) : A.rank <= r := by
  rw [h]
  exact (Matrix.rank_mul_le_left C T).trans (Matrix.rank_le_width C)
''']
def emit(name,a,m,n):
    vals=[x for row in a for x in row]
    ns=', '.join(str(x.numerator) for x in vals)
    ds=', '.join(str(x.denominator) for x in vals)
    lines.append(f'def {name} : Matrix (Fin {m}) (Fin {n}) Rat :=\n  ratMat {m} {n} (raw_ints% [{ns}]) (raw_ints% [{ds}])\n')
emit('V',V,20,3)
L=[[F(int(i==j)) for j in range(20)] for i in range(3)]
emit('leftInverse',L,3,20)
lines+=['theorem basis_check : leftInverse * V = 1 := by decide +kernel', '''theorem basis_rank : V.rank = 3 := by
  apply le_antisymm (Matrix.rank_le_width V)
  have h := Matrix.rank_mul_le_right leftInverse V
  rw [basis_check, Matrix.rank_one, Fintype.card_fin] at h
  exact h
''']
rows=[]; weightedsum=0
for k,(mp,c) in enumerate(zip(s['active_maps'],w['lower']['restriction_certificates'])):
    B=matrix(mp['matrix']); r=c['rank']; m=len(B)
    C=matrix(c['coordinates']); T=matrix(c['basis']); BV=mul(B,V)
    got=rank(BV); assert got==r
    if r: assert BV==mul(C,T)
    else: assert all(not x for row in BV for x in row)
    emit(f'B{k}',B,m,20);emit(f'C{k}',C,m,r);emit(f'T{k}',T,r,3)
    lines.append(f'theorem factor{k} : B{k} * V = C{k} * T{k} := by decide +kernel\n')
    lines.append(f'theorem image_rank{k} : (B{k} * V).rank <= {r} :=\n  rank_le_of_factorization _ C{k} T{k} factor{k}\n')
    rows.append({'index':k,'compressed_map_index':mp['compressed_map_index'],'rows':m,'rank':got,'weight':mp['weight']})
    weightedsum+=int(mp['weight'])*got
# central coefficient at this point is p/N=26, giving 26*3-sum(weight*rank)=1.
assert 26*rank(V)-weightedsum==1
lines+=['theorem euler_arithmetic : (26 : Int) * 3 - (13*1 + 17*0 + 9*0 + 3*2 + 13*1 + 7*0 + 18*2 + 4*2 + 1*1 + 3*0) = 1 := by decide +kernel','end CatalanMeasure.GenD.Uniform.PilotRank']
lines.insert(-1, '''
/-- Semantic certificate pack: a genuine three-dimensional subspace and image rank bounds. -/
theorem certificate_pack : V.rank = 3 ∧
    (B0 * V).rank ≤ 1 ∧ (B1 * V).rank ≤ 0 ∧ (B2 * V).rank ≤ 0 ∧
    (B3 * V).rank ≤ 2 ∧ (B4 * V).rank ≤ 1 ∧ (B5 * V).rank ≤ 0 ∧
    (B6 * V).rank ≤ 2 ∧ (B7 * V).rank ≤ 2 ∧ (B8 * V).rank ≤ 1 ∧
    (B9 * V).rank ≤ 0 :=
  ⟨basis_rank, image_rank0, image_rank1, image_rank2, image_rank3,
    image_rank4, image_rank5, image_rank6, image_rank7, image_rank8, image_rank9⟩

#print axioms basis_rank
#print axioms certificate_pack
''')
out=ROOT/'CatalanMeasure/GenD/Uniform/PilotRank.lean';out.parent.mkdir(parents=True,exist_ok=True)
out.write_text('\n'.join(lines)+'\n',encoding='utf-8')
receipt={'source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'witness':str(wit),'witness_sha256':hashlib.sha256(wit.read_bytes()).hexdigest(),'basis_rank':rank(V),'maps':rows,'weighted_image_rank_sum':weightedsum,'euler_at_x26':1,'status':'independent exact Fraction replay passed','lean_file':str(out),'lean_lines':len(out.read_text().splitlines())}
(ROOT/'scripts/uniform-phase0/rank-mirror.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
print('RANK_MIRROR_COMPLETED')
