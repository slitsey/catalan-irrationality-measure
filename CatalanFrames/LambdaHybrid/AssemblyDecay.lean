module

public import CatalanFrames.LambdaHybrid.Assembly
public import CatalanFrames.Lambda.HybContent
public import CatalanCore.Cert.SigmaHyb.FinalH

@[expose] public section

/-!
# λ hybrid: decay instantiated (MEM2D)

`LamHybDecayK180s` is discharged by `CatalanCore.Cert.SigmaHyb.lam_hybrid_decay`
(`D = 3.9028`, `c = 7.6444`).  The measure theorem is restated with these constants and
`Λ = 3.7102296`: exponent `c/(D - Λ) = 39.6966… ≤ 39.70`.  Only the second-member hypotheses
`Mem2Content`, `Mem2Decay` remain.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-- The content in the `ε`-form `(Λ + ε) r²` for `Λ ≥ 24729491161/6665218560` (a corollary of
`lam_both_eps`). -/
theorem lam_content_eps {Λ : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefHypT lamInst r (r / 8) T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [lam_both_eps hΛ ε hε] with r ⟨T, δ, hd, hl⟩
  exact ⟨T, δ, hd.1, hl⟩

/-- **`lam_hyb_measure_of_decay`**: `μ(λ) ≤ C/(D - Λ)` with the content theorem
`lam_content_deficit2` (`Λ ≥ 24729491161/6665218560`). -/
theorem lam_hyb_measure_of_decay {Λ D C E : ℚ} (hΛ : (24729491161 / 6665218560 : ℚ) ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2c : Mem2Content lamFrame (Λ : ℝ)) (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E) :
    (hybPairFam lamFrame 8).MeasureLB (E : ℝ) :=
  lam_hyb_measure_of_content_eps
    (lam_content_eps (by have h := (Rat.cast_le (K := ℝ)).2 hΛ; push_cast at h; exact h))
    (le_trans (by norm_num) hΛ) hD M2c M2d hη hC hη2 hE

/-- The headline statement in the project's form `G - 5π²/48` (generic scaling lemma). -/
theorem lam_hyb_measure_G {Λ D C E : ℚ} (hΛ : (24729491161 / 6665218560 : ℚ) ≤ Λ)
    (hD : HasDecay (hybridFamUp lamFrame (1 / 8)) (D : ℝ) (C : ℝ))
    (M2c : Mem2Content lamFrame (Λ : ℝ)) (M2d : Mem2Decay lamFrame (D : ℝ) (C : ℝ))
    (hη : Λ < D) (hC : 0 < C) (hη2 : 2 * (D - Λ) < 23 / 10) (hE : C / (D - Λ) ≤ E)
    (hE0 : 0 ≤ E) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (E : ℝ) := by
  have h := lam_hyb_measure_of_decay hΛ hD M2c M2d hη hC hη2 hE
  have h' : Measure.MeasureLBAt lamFrame.const (E : ℝ) := h
  rw [const_eq] at h'
  have := h'.affine (by exact_mod_cast hE0) 2 0 (by norm_num)
  convert this using 1
  push_cast
  ring

/-! ### The k180s numbers -/

/-- Decay for the `k180s` certificate: `D = 3.9027944`, `c = 7.6477917` (to be instantiated by
`decay_of_certG_rect` once `CatalanCore/Cert/SigmaHyb` provides the certificate). -/
def LamHybDecayK180s : Prop :=
  HasDecay (hybridFamUp lamFrame (1 / 8)) (((39027944 / 10000000 : ℚ)) : ℝ)
    (((76477917 / 10000000 : ℚ)) : ℝ)

/-- With `D = 3.9027944`, `c = 7.6477917`, `Λ = 3.7102296`: exponent `≤ 39.72`
(`c/(D-Λ) = 39.71541…`). -/
theorem lam_hyb_measure_k180s (hD : LamHybDecayK180s)
    (M2c : Mem2Content lamFrame (((37102296 / 10000000 : ℚ)) : ℝ))
    (M2d : Mem2Decay lamFrame (((39027944 / 10000000 : ℚ)) : ℝ)
      (((76477917 / 10000000 : ℚ)) : ℝ)) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3972 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_G (Λ := 37102296 / 10000000) (D := 39027944 / 10000000)
    (C := 76477917 / 10000000) (E := 3972 / 100) (by norm_num) hD M2c M2d (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms lam_hyb_measure_of_decay
#print axioms lam_hyb_measure_G
#print axioms lam_hyb_measure_k180s

/-- Member-1 decay for the hybrid λ family, proved. -/
theorem lam_hyb_decay_member1 :
    HasDecay (hybridFamUp lamFrame (1 / 8)) (((39028 / 10000 : ℚ)) : ℝ)
      (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.Cert.SigmaHyb.lam_hybrid_decay

/-- **λ hybrid measure, decay discharged**: `μ ≤ 39.70` for `G - 5π²/48`, given the
second-member content and decay. -/
theorem lam_hyb_measure_decayK
    (M2c : Mem2Content lamFrame (((37102296 / 10000000 : ℚ)) : ℝ))
    (M2d : Mem2Decay lamFrame (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ)) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((3970 / 100 : ℚ)) : ℝ) :=
  lam_hyb_measure_G (Λ := 37102296 / 10000000) (D := 39028 / 10000)
    (C := 76444 / 10000) (E := 3970 / 100) (by norm_num) lam_hyb_decay_member1 M2c M2d
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms lam_hyb_measure_decayK

end CatalanFrames.LambdaHybrid
