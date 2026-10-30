"""Prepare canonical generic geometry and q7 physical source realization (no builds)."""
from pathlib import Path
import hashlib, json, re
R=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
B=R/'CatalanCore/Uniform/Bank/Sevenths'
G=R/'CatalanCore/Uniform/Content/RankProducer'
S=R/'scripts/codex/bank/sevenths'
L=R/'CatalanCore/Uniform/Bank/Lambda'
sources={}
def read(path):
    s=path.read_text(encoding='utf-8-sig')
    sources[str(path.relative_to(R))]=hashlib.sha256(s.encode()).hexdigest()
    return s
def put(path,text):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(text,encoding='utf-8')
# Extract the existing fully generic common-minor node/realization lemmas to the canonical module.
s=read(R/'CatalanCore/Uniform/Bank/Chi3Rank/Fibre.lean')
s=s.replace('import CatalanCore.Uniform.Bank.Chi3Rank.Pair2',
            'import CatalanCore.Uniform.Content.RankProducer.Cert\nimport CatalanCore.Uniform.Content.Member.Transfer')
s=s.replace('CatalanCore.Uniform.Bank.Chi3Rank','CatalanCore.Uniform.Content.RankProducer.Geometry')
s=s.replace('    rw [natCast_eq_of_mod h, Nat.mod_eq_of_lt hx0]',
            '    have hv := congrArg ZMod.val h\n    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hx0] using hv')
digits="""
/-- Alternating full-row membership in residue-digit coordinates. -/
def rowDigit (r m p x d : ℕ) : Prop :=
  x + p * d < r ∨
    (r ≤ x + p * d ∧ x + p * d < r + 2 * m ∧ (x + p * d - r) % 2 = 0)
def colDigit (r m p x d : ℕ) : Prop :=
  x + p * d < r ∨
    (r ≤ x + p * d ∧ x + p * d < r + 2 * m ∧ (x + p * d - r) % 2 = 1)

/-- A uniform support endpoint gives a digit bound, independently of the frame. -/
theorem rowDigit_lt {r m p x d H : ℕ} (hend : r + 2 * m ≤ x + p * H)
    (h : rowDigit r m p x d) : d < H := by
  have hn : x + p * d < r + 2 * m := by
    rcases h with h | ⟨_, h, _⟩ <;> omega
  by_contra hd
  have hm := Nat.mul_le_mul_left p (show H ≤ d by omega)
  omega
theorem colDigit_lt {r m p x d H : ℕ} (hend : r + 2 * m ≤ x + p * H)
    (h : colDigit r m p x d) : d < H := by
  have hn : x + p * d < r + 2 * m := by
    rcases h with h | ⟨_, h, _⟩ <;> omega
  by_contra hd
  have hm := Nat.mul_le_mul_left p (show H ≤ d by omega)
  omega

"""
s=s.replace('section Realize',digits+'section Realize',1)
s=s.replace('end Realize','end Realize\n#print axioms realizes_of',1)
put(G/'Geometry.lean',s)
s=read(L/'Boundary.lean')
s=s.replace('import CatalanCore.Uniform.Bank.Chi3Rank.Count','import CatalanCore.Uniform.Content.RankProducer.Geometry')
s=s.replace('CatalanCore.Uniform.Bank.Lambda','CatalanCore.Uniform.Content.RankProducer.Geometry')
s=s.replace('open Finset CatalanCore.Uniform.Bank.Chi3Rank','open Finset')
put(G/'Boundary.lean',s)
# Bank-specific trim rounding.
s=read(L/'Rounding.lean').replace('Bank.Lambda','Bank.Sevenths').replace('FL','F7').replace('one_fifth_pos','one_sixth_pos')
s=re.sub(r'\b10\b','12',s)
s=re.sub(r'\b5\b','6',s)
s=s.replace('r/10','r/12')
put(B/'Rounding.lean',s)
put(B/'DigitShape.lean',"""import CatalanCore.Uniform.Content.RankProducer.Geometry
import CatalanCore.Uniform.Bank.Sevenths.Rounding
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Uniform.Content.RankProducer.Geometry

theorem rowDigit_lt_seven {r m p x d : ℕ} (hround : 12 * m ≤ r + 6)
    (hrp : r ≤ 6 * p) (hx : 4 ≤ x) (h : rowDigit r m p x d) : d < 7 :=
  rowDigit_lt (by omega) h

theorem colDigit_lt_seven {r m p x d : ℕ} (hround : 12 * m ≤ r + 6)
    (hrp : r ≤ 6 * p) (hx : 4 ≤ x) (h : colDigit r m p x d) : d < 7 :=
  colDigit_lt (by omega) h

#print axioms rowDigit_lt_seven
end CatalanCore.Uniform.Bank.Sevenths
""")
# The q7-specific exact pole palette supplies Realizes; no price is assumed.
s=read(L/'Realize.lean')
s=s.replace('Bank.Lambda','Bank.Sevenths').replace('D4','D7Frame').replace('hp4','hp7').replace('q4','q7')
s=s.replace('import CatalanCore.Uniform.Bank.Chi3Rank.Fibre','import CatalanCore.Uniform.Content.RankProducer.Geometry')
s=s.replace('open CatalanCore.Uniform.Bank.Chi3Rank (realizes_of)',
            'open CatalanCore.Uniform.Content.RankProducer.Geometry (realizes_of)')
s=s.replace('¬ p ∣ 4','¬ p ∣ 7').replace('4 * k + a','7 * k + a')
put(B/'Realize.lean',s)
s=read(L/'CommonMinorRealize.lean')
s=s.replace('Bank.Lambda','Bank.Sevenths').replace('D4','D7Frame').replace('hp4','hp7')
s=s.replace('open CatalanCore.Uniform.Bank.Chi3Rank','open CatalanCore.Uniform.Content.RankProducer.Geometry')
s=s.replace('¬ p ∣ 4','¬ p ∣ 7').replace('4 * k + a','7 * k + a')
put(B/'CommonMinorRealize.lean',s)
# Generate the q7 affine source classifications from q7 data only.
s=read(R/'scripts/codex/bank/lambda/generate_source.py')
s=s.replace('rank-lambda.json','rank-sevenths.json').replace('Bank/Lambda','Bank/Sevenths').replace('Bank.Lambda','Bank.Sevenths')
s=s.replace("namespace CatalanCore.Uniform.Bank.Sevenths.RankSource\\n",
            "namespace CatalanCore.Uniform.Bank.Sevenths.RankSource\\nopen CatalanCore.Uniform.Content.RankProducer.Geometry\\n")
s=s.replace('10 * m','12 * m').replace('r + 5','r + 6').replace('m + 5','m + 6').replace('r ≤ 5 * p','r ≤ 6 * p')
s=s.replace('_lt_six','_lt_seven').replace('d < 6','d < 7')
s=s.replace('a = 1 ∨ a = 3','1 ≤ a ∧ a ≤ 6').replace('4 * k + a','7 * k + a')
s=s.replace('scripts/codex/bank/lambda/source-manifest.json','scripts/codex/bank/sevenths/source-manifest.json')
# Freeze this adapted emitter rather than depending on future edits to the other lane.
put(S/'generate_source.py',s)
exec(compile(s,str(S/'generate_source.py'),'exec'),{'__file__':str(S/'generate_source.py')})
(S/'source-provenance.json').write_text(json.dumps(sources,indent=2)+'\n',encoding='utf-8')
print('Prepared canonical geometry/boundary and q7 rounding, realization, and 143 affine source modules')
