from pathlib import Path
import json
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
P=R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-lambda.json'
S=R/'scripts/codex/bank/lambda'
D=R/'CatalanCore/Uniform/Bank/Lambda/RankPalette';D.mkdir(exist_ok=True)
cs=json.loads(P.read_text())['cases'];man=[]
for case in cs:
 for k,(tid,t) in enumerate(case['types'].items()):
  n=f'C{case["prime_class"]}T{k:02}';j=case['root_index'];z=t['pole_bit']
  txt=f'''import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.{n}
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem {n}_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ {n}_den) :
    {n}.Integral p :=
  RankTools.integral_of_denOk {n} {n}_den p {n}_den_ok hp

/-- Digit palette at root {j}, cyclic pole bit {z}, on every coordinate. -/
theorem {n}_palette :
    (∀ d ∈ {n}.R, {n}.lf d = poleL {j} {z} d ∧ {n}.ee d = poleE {j} {z} d) ∧
    (∀ d ∈ {n}.C, {n}.lf d = poleL {j} {z} d ∧ {n}.ee d = poleE {j} {z} d) := by
  constructor <;> decide +kernel
theorem {n}_loads_nonzero :
    (∀ d ∈ {n}.kr, {n}.rload d ≠ (0, 0)) ∧
    (∀ d ∈ {n}.kc, {n}.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem {n}_load_orthogonal : ∀ r ∈ {n}.kr, ∀ c ∈ {n}.kc,
    ({n}.rload r).1 * ({n}.cload c).2 -
      ({n}.rload r).2 * ({n}.cload c).1 = 0 := by decide +kernel
#print axioms {n}_integral
#print axioms {n}_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
'''
  (D/(n+'.lean')).write_text(txt,encoding='utf-8');man.append('CatalanCore.Uniform.Bank.Lambda.RankPalette.'+n)
(D/'Audit.lean').write_text('\n'.join('import '+m for m in man)+'\n',encoding='utf-8')
(S/'palette-manifest.json').write_text(json.dumps(man,indent=2),encoding='utf-8')
print('Prepared 68 integral and palette identification modules')
