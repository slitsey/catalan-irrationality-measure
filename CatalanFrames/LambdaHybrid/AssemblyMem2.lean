module

public import CatalanFrames.Lambda.HybTopAll
public import CatalanFrames.LambdaHybrid.Assembly

@[expose] public section

/-!
# λ hybrid measure theorem with `Mem2Content` discharged (MEM2C)

`Assembly.lean` takes the content of the second member `afterTop r m` as the hypothesis
`Mem2Content`.  Here it is proved (`lam_mem2Content`, by bordering the member-1 deficit families
B, E, C5) and the measure theorems are restated without it.  Only `Mem2Decay` and the member-1
decay `HasDecay` remain.  (C7 and GK are NOT transferred: GK is not rank-based; see MEM2C/status.md.)
-/

open CatalanCore CatalanCore.Rect CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

theorem lam_hyb_measure_of_decay' {Λ D C E : ℚ} (hΛ : (24729491161 / 6665218560 : ℚ) ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E) :
    (hybPairFam lamFrame 8).MeasureLB (E : ℝ) :=
  lam_hyb_measure_of_decay hΛ hD
    (lam_mem2Content (by have h := (Rat.cast_le (K := ℝ)).2 hΛ; push_cast at h; exact h))
    M2d hη hC hη2 hE

theorem lam_hyb_measure_G' {Λ D C E : ℚ} (hΛ : (24729491161 / 6665218560 : ℚ) ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E)
    (hE0 : 0 ≤ E) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (E : ℝ) :=
  lam_hyb_measure_G hΛ hD
    (lam_mem2Content (by have h := (Rat.cast_le (K := ℝ)).2 hΛ; push_cast at h; exact h))
    M2d hη hC hη2 hE hE0

#print axioms lam_mem2Content
#print axioms lam_hyb_measure_G'

end CatalanFrames.LambdaHybrid
