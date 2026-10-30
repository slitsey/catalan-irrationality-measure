import CatalanCore.Uniform.Bank.FourthsContent.Auto
import CatalanCore.Uniform.Bank.Fourths.Final
import CatalanCore.Uniform.Bank.Fourths.Frame
set_option Elab.async false

/-! # The λ± measures from the automatic content (lane C1L)

With the automatic content `Auto.lamMinus_content_auto` / `Auto.lamPlus_content_auto` at `Λ_fin = bankData.Λ`
(selection depth `≤ 64`, `depth_le`) and the decay
`HasScaledDecay (FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)) FL.scale DL cL`, the target
bound `314411/10000` follows by `Auto.lambda_mu_le`.  The theorems are conditional only on the decay. -/

namespace CatalanCore.Uniform.Bank.FourthsContent.AutoMeasure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Fourths
  CatalanCore.Uniform.Bank.FourthsContent.Auto

/-- The selection depth of the λ geometry is at most `64` for a two-family frame. -/
theorem depth_le {Fr : Frame} (hd : Fr.d = 2) : FL.selectionDepth Fr 2 ≤ 64 := by
  unfold BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem lam_lt_DL : ((bankData.Λ : ℚ) : ℝ) < (DL : ℝ) := by
  have h : bankData.Λ < DL := by rw [bankData_Λ]; unfold DL; norm_num
  exact_mod_cast h

theorem X_le : (1 : ℝ) * (cL : ℝ) / ((DL : ℝ) - (bankData.Λ : ℚ)) ≤ ((314411 / 10000 : ℚ) : ℝ) := by
  rw [one_mul]; exact lambda_mu_le

theorem content_auto (sgn : Bool) :
    HasScaledContent ((FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)).restrictAdm
      (fun i => i.1 % 2 = 0)) FL.scale ((bankData.Λ : ℚ) : ℝ) := by
  cases sgn
  · exact lamMinus_content_auto _ (depth_le (lambdaFrame_d false))
  · exact lamPlus_content_auto _ (depth_le (lambdaFrame_d true))

/-- **`μ(L(2, χ₋₄) ± 5π²/48) ≤ 314411/10000`** (`lambdaTarget sgn`; `true` is plus), conditional only on the
decay. -/
theorem lambda_measure_auto (sgn : Bool)
    (hD : HasScaledDecay (FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)) FL.scale
      (DL : ℝ) (cL : ℝ)) :
    Measure.MeasureLBAt (lambdaTarget sgn) ((314411 / 10000 : ℚ) : ℝ) := by
  have hmass : (FL.common.mass : ℝ) = 1 := by rw [FL_common_mass]; norm_num
  have hc : (0 : ℝ) < (cL : ℝ) := by unfold cL; norm_num
  have hd : 1 ≤ (lambdaFrame sgn).d := by rw [lambdaFrame_d]; norm_num
  have key := measure_of_family_nv0_even
    ((FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale
    (γ := 1) (K := FL.common.n) (content_auto sgn)
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) lam_lt_DL hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := FL.degree_bound (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := FL_nv0 (lambdaFrame sgn) hd (lambdaFrame_w_ne sgn) (FL.selectionDepth (lambdaFrame sgn) 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : FL.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt (lambdaFrame sgn).const ((314411 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono X_le ((Measure.MeasureLB_iff _ _).1 key)
  have he : lambdaTarget sgn = ((2 : ℚ) : ℝ) * (lambdaFrame sgn).const + ((0 : ℚ) : ℝ) := by
    rw [lambdaFrame_const sgn]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) 2 0 (by norm_num)

#print axioms lambda_measure_auto

end CatalanCore.Uniform.Bank.FourthsContent.AutoMeasure
