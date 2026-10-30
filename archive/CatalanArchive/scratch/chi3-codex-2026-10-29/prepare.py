from pathlib import Path
import re,json,hashlib
root=Path.cwd(); scratch=root/'scratch/chi3-codex-2026-10-29'
def closure(m):
    seen=set(); todo=[m]
    while todo:
        x=todo.pop()
        if x in seen: continue
        seen.add(x); p=root/(x.replace('.','/')+'.lean')
        if p.exists(): todo+=re.findall(r'^import\s+(\S+)',p.read_text(encoding='utf-8-sig'),re.M)
    return sorted(seen)
old=closure('CatalanCore.Uniform.Bank.Chi3Rank.RankFinal')
(scratch/'old-import-closure.json').write_text(json.dumps(old,indent=1))
p=root/'CatalanCore/Uniform/Bank/Chi3New/Decay.lean'
s=p.read_text(encoding='utf-8'); (scratch/'Decay.before.lean').write_text(s,encoding='utf-8')
s=s.replace('import CatalanCore.Uniform.Bank.Chi3.Decay','import CatalanCore.Uniform.Bank.Chi3.Env\nimport CatalanCore.Uniform.Bank.Chi3.Cover.Check\nimport CatalanCore.Uniform.Decay.AltDecay').replace('import CatalanCore.Uniform.Bank.Chi3New.Energy','import CatalanCore.Uniform.Bank.Chi3New.Geom')
s=s.replace('/-! `HasScaledDecay` of the chi3 block family `G12.family p6Frame depth` (lane B, B3f): the frame\nand node hypotheses of `chi3_hasScaledDecay` discharged for `G12 = altGeom (1/2)` and `p6Frame`. -/','/-! Decay of the chi3 block family from the current generated cover and the generic alternating-bank theorem. The public decay statement and constants are unchanged. -/')
pos=s.index('/-- **Window decay')
s=s[:pos]+'''open CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes

namespace GeneratedDecay
open CatalanCore.Uniform.Bank.Chi3.Cover

theorem tab_RP : TabC.RP = altPieces (1 / 2) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (1 / 2) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (1 / 2 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (1 / 2)) (altPieces (1 / 2))
    Cover.Dchi.Inu = true := by decide +kernel
theorem dim_eq : Cover.Dchi.dim = 3 := by decide +kernel
theorem eps_pos : 0 < Cover.Dchi.ε := by decide +kernel
theorem Dt_eq : Cover.Dchi.Dt = Chi3.Dchi.Dt := by decide +kernel
theorem ccert_eq : Cover.Dchi.ccert = Chi3.Dchi.ccert := by decide +kernel

end GeneratedDecay

/-- **Window decay of the chi3 block family**, with the unchanged certified constants. -/
theorem chi3_decay (depth : ℕ) :
    HasScaledDecay (G12.family p6Frame depth) G12.scale (Dchi.Dt : ℝ) (Dchi.ccert : ℝ) := by
  have hm0 : ∀ i, (1 / 3 : ℝ) ≤ p6Frame.μ i := by
    intro i
    have hq : (1 / 3 : ℚ) ≤ p6Frame.μ i := by
      rcases p6_mu i with h | h | h <;> rw [h] <;> norm_num
    have h := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at h
    exact h
  have h := altGeom_hasScaledDecay (1 / 2) half_pos (by norm_num)
    (by decide +kernel : Frame.contourCheck p6Frame = true) p6_hAR
    (by decide +kernel) Cover.TabC GeneratedDecay.tab_RP GeneratedDecay.tab_CP
    GeneratedDecay.tab_Mq Cover.Dchi Cover.Pply Cover.check_true
    (by rw [GeneratedDecay.dim_eq]; rfl) 30 GeneratedDecay.energy_ok
    (m0 := 1 / 3) (by norm_num) hm0 GeneratedDecay.eps_pos depth
  rw [GeneratedDecay.Dt_eq, GeneratedDecay.ccert_eq] at h
  exact h

end CatalanCore.Uniform.Bank.Chi3New
'''
(scratch/'Decay.draft.lean').write_text(s,encoding='utf-8')
print('Saved old closure:',len(old),'modules and theorem replacement draft')
