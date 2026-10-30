import CatalanCore.Uniform.Bank.Lambda.Final
import CatalanCore.Uniform.Content.Shape.Reindex
import CatalanCore.Measure.Scaling
set_option Elab.async false



namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape


noncomputable def LamNoUF : ℝ :=
  25867615342809042650399 / 7378677391061896920000 + (1 / 50) * Real.log 2





theorem LamNoUF_lt_DL : LamNoUF < (DL : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold LamNoUF DL
  push_cast
  nlinarith


theorem lambda_noUF_X_le :
    (1 : ℝ) * (cL : ℝ) / ((DL : ℝ) - LamNoUF) ≤ ((159693 / 5000 : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have hpos : 0 < (DL : ℝ) - LamNoUF := sub_pos.2 LamNoUF_lt_DL
  rw [one_mul, div_le_iff₀ hpos]
  unfold LamNoUF DL cL
  push_cast
  nlinarith


theorem lambda_noUF_measureLB (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : FL.selectionDepth Fr 2 ≤ depth)
    (hS : HasScaledContent ((FL.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale LamNoUF)
    (hD : HasScaledDecay (FL.family Fr depth) FL.scale (DL : ℝ) (cL : ℝ)) :
    (FL.family Fr depth).MeasureLB ((159693 / 5000 : ℚ) : ℝ) := by
  have hmass : (FL.common.mass : ℝ) = 1 := by rw [FL_common_mass]; norm_num
  have hc : (0 : ℝ) < (cL : ℝ) := by unfold cL; norm_num
  have key := measure_of_family_nv0_even
    ((FL.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale
    (γ := 1) (K := FL.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) LamNoUF_lt_DL hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := FL.degree_bound Fr depth n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := FL_nv0 Fr hd hw depth hdepth
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : FL.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  exact (Measure.MeasureLB_iff _ _).2
    (Measure.MeasureLBAt.mono lambda_noUF_X_le ((Measure.MeasureLB_iff _ _).1 key))


theorem lambda_noUF_measure_of_const (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : FL.selectionDepth Fr 2 ≤ depth) {target : ℝ}
    (hconst : Fr.const = ((1 / 2 : ℚ) : ℝ) * target)
    (hS : HasScaledContent ((FL.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale LamNoUF)
    (hD : HasScaledDecay (FL.family Fr depth) FL.scale (DL : ℝ) (cL : ℝ)) :
    Measure.MeasureLBAt target ((159693 / 5000 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).1 (lambda_noUF_measureLB Fr hd hw depth hdepth hS hD)
  have h' : Measure.MeasureLBAt Fr.const ((159693 / 5000 : ℚ) : ℝ) := h0
  have he : target = ((2 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
    rw [hconst]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (2) 0 (by norm_num)

end CatalanCore.Uniform.Bank.Lambda
