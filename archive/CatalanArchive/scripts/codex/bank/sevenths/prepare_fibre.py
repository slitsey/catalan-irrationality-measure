"""Prepare q7 full physical certificate assignments and canonical balancing proofs."""
from pathlib import Path
import hashlib,json
R=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
B=R/'CatalanCore/Uniform/Bank/Sevenths';G=R/'CatalanCore/Uniform/Content/RankProducer'
S=R/'scripts/codex/bank/sevenths';L=R/'CatalanCore/Uniform/Bank/Lambda'
provenance={}
def read(p):
    s=p.read_text(encoding='utf-8-sig');provenance[str(p.relative_to(R))]=hashlib.sha256(s.encode()).hexdigest();return s
def put(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s,encoding='utf-8')
s=read(L/'RankTools.lean')
s=s[s.index('/-- Rebalancing may discard'):s.index('#print axioms integral_of_denOk')]
put(G/'Restriction.lean',"""import CatalanCore.Uniform.Content.RankProducer.Cert
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open CatalanCore CatalanCore.Uniform.Content.Hybrid
""" + s + """
#print axioms trim_ok
end CatalanCore.Uniform.Content.RankProducer
""")
s=read(L/'RankBalance.lean').replace('import CatalanCore.Uniform.Bank.Lambda.RankTools',
                                  'import CatalanCore.Uniform.Content.RankProducer.Restriction')
s=s.replace('CatalanCore.Uniform.Bank.Lambda.RankTools','CatalanCore.Uniform.Content.RankProducer')
put(G/'Balance.lean',s)
s=read(L/'Assignment.lean')
s=s.replace('import CatalanCore.Uniform.Bank.Lambda.RankBalance','import CatalanCore.Uniform.Content.RankProducer.Balance')
s=s.replace('import CatalanCore.Uniform.Bank.Chi3Rank.Fibre','import CatalanCore.Uniform.Content.RankProducer.Geometry')
s=s.replace('CatalanCore.Uniform.Bank.Lambda.RankTools','CatalanCore.Uniform.Content.RankProducer')
s=s.replace('CatalanCore.Uniform.Bank.Chi3Rank','CatalanCore.Uniform.Content.RankProducer.Geometry')
put(G/'BalancedGeometry.lean',s)
put(B/'Band.lean',"""import CatalanCore.Uniform.Bank.Sevenths.PolePalette
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid

theorem D7Frame_coeff_mem (a p : ℕ) [Fact p.Prime] (i : Fin 2) : (D7Frame a).c i ∈ S p := by
  fin_cases i
  · change (-1 : ℚ) ∈ S p
    exact (S p).neg_mem (S p).one_mem
  · change (1 : ℚ) ∈ S p
    exact (S p).one_mem

theorem D7Frame_den_units (a p : ℕ) [hp : Fact p.Prime] (hp7 : ¬ p ∣ 7) (i : Fin 2) :
    ¬ p ∣ (D7Frame a).q i := by
  fin_cases i
  · exact hp7
  · exact hp.out.not_dvd_one

theorem D7Frame_band (a r m p : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p)
    (hrp : r ≤ 6 * p) (hm : 12 * m ≤ r + 6) (i : Fin 2) :
    (D7Frame a).q i * (r + 2 * m) + (D7Frame a).u i ≤ p ^ 2 := by
  have hN : r + 2 * m ≤ 7 * p + 1 := by omega
  have hpp : 64 * p ≤ p ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_right p hp64
  fin_cases i
  · change 7 * (r + 2 * m) + a ≤ p ^ 2
    nlinarith [ha.2]
  · change 1 * (r + 2 * m) + 1 ≤ p ^ 2
    nlinarith

noncomputable def seventhsPoleSplit (a p r m : ℕ) [Fact p.Prime]
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm : 12 * m ≤ r + 6) :
    PoleSplit p (r + 2 * m) (D7Frame a).f (D7Frame a).e :=
  (D7Frame a).poleSplit (r + 2 * m) (D7Frame_coeff_mem a p) (D7Frame_den_units a p hp7)
    (by omega) (D7Frame_band a r m p ha hp64 hrp hm)

#print axioms D7Frame_band
end CatalanCore.Uniform.Bank.Sevenths
""")
def adapt(s):
    s=s.replace('rank-lambda.json','rank-sevenths.json').replace('Bank/Lambda','Bank/Sevenths')
    s=s.replace('Bank.Lambda','Bank.Sevenths').replace('D4','D7Frame').replace('hp4','hp7')
    s=s.replace('lambdaPoleSplit','seventhsPoleSplit').replace('hp29','hp64').replace('29 ≤ p','64 ≤ p')
    s=s.replace('10 * m','12 * m').replace('r + 5','r + 6').replace('m + 5','m + 6').replace('r ≤ 5 * p','r ≤ 6 * p')
    s=s.replace('a = 1 ∨ a = 3','1 ≤ a ∧ a ≤ 6').replace('4 * k + a','7 * k + a').replace('¬ p ∣ 4','¬ p ∣ 7')
    s=s.replace('import CatalanCore.Uniform.Bank.Sevenths.Boundary',
                'import CatalanCore.Uniform.Content.RankProducer.Boundary')
    s=s.replace('open CatalanCore.Uniform.Bank.Chi3Rank RankSource RankData',
                'open CatalanCore.Uniform.Content.RankProducer.Geometry RankSource RankData')
    s=s.replace('scripts/codex/bank/lambda/fibre-manifest.json','scripts/codex/bank/sevenths/fibre-manifest.json')
    return s
s=adapt(read(R/'scripts/codex/bank/lambda/fibre_assignment.py'))
put(S/'fibre_assignment.py',s)
s=adapt(read(R/'scripts/codex/bank/lambda/generate_fibre.py'))
put(S/'generate_fibre.py',s)
exec(compile(s,str(S/'generate_fibre.py'),'exec'),{'__file__':str(S/'generate_fibre.py')})
(S/'fibre-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n',encoding='utf-8')
print('Prepared full q7 assignments; source-shape, exact palette, Ok, Integral and Realizes proofs')
