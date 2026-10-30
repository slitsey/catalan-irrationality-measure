module

public import CatalanCore.Uniform.Bank.ThirdsContent.AutoUF
public import CatalanCore.Uniform.Bank.Thirds.Final

@[expose] public section
set_option Elab.async false

/-! # The thirds measure from the automatic UF content (coordinator)

With the automatic content `AutoUF.thirds*_content_autoUF` at `Λ_fin = ufData.Λ` and the matched decay
`ThirdsDecay` (`D = DtT`, `c = ctT`), the target bound `95133/10000` follows by `AutoUF.uf_mu_le`.
The theorems are conditional only on `ThirdsDecay`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent.MeasureUF
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanFrames.Thirds CatalanFrames.P6 CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Bank.ThirdsContent.AutoUF

/-- The selection depth of the thirds geometry is `5` for any two-family frame. -/
theorem depth0_le {Fr : Frame} (hd : Fr.d = 2) : depth0 Fr ≤ 64 := by
  have h1 : G310.allComponents 2 = 6 := by rfl
  have h2 : G310.commonComponents 2 = 2 := by rfl
  unfold depth0 BlockGeom.selectionDepth
  rw [h1, h2, hd]
  norm_num

theorem lam_lt_Dt : ((ufData.Λ : ℚ) : ℝ) < (DtT : ℝ) := by
  have h : ufData.Λ < DtT := by rw [ufData_Λ]; unfold DtT; norm_num
  exact_mod_cast h

/-- The measure of the thirds family at any content constant `Λ < DtT`. -/
theorem thirds_measureLB_lam (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (Λ : ℚ)
    (hΛ : (Λ : ℝ) < (DtT : ℝ))
    (hS : HasScaledContent (FamE Fr (depth0 Fr)) G310.scale (Λ : ℝ))
    (hD : ThirdsDecay Fr (depth0 Fr)) :
    (G310.family Fr (depth0 Fr)).MeasureLB ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - Λ)) := by
  have hmass : (G310.common.mass : ℝ) = 1 := by rw [G310_common_mass]; norm_num
  have hD' : HasScaledDecay ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0))
      G310.scale (DtT : ℝ) (ctT : ℝ) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD ε hε
    exact ⟨R0, fun n hn => h n hn.1⟩
  have hc : (0 : ℝ) < (ctT : ℝ) := by unfold ctT; norm_num
  exact measure_of_family_nv0_even
    ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0)) G310.scale
    (γ := 1) (K := G310.common.n) hS hD' hΛ hc one_pos (Nat.cast_nonneg _)
    (fun n hn => by
      have := G310.degree_bound Fr (depth0 Fr) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := thirds_nv0 Fr hd hw
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by have : G310.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)

theorem X_le : (1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - (ufData.Λ : ℚ)) ≤ ((95133/10000 : ℚ) : ℝ) := by
  rw [one_mul]; exact uf_mu_le

/-- **`μ(L(2,χ₋₃) + π²/9) ≤ 9.52671`** from the automatic content; conditional only on the decay. -/
theorem thirds_measure_plus (hD : ThirdsDecay thirdsAc (depth0 thirdsAc)) :
    Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9) ((95133/10000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB_lam thirdsAc (by show 1 ≤ 2; norm_num) thirds_w_ne ufData.Λ lam_lt_Dt
    (thirdsAc_content_autoUF _ (depth0_le rfl)) hD
  have h1 := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsAc.const ((95133/10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono X_le h1
  exact measureLBAt_of_const (Fam := G310.family thirdsAc (depth0 thirdsAc)) (a := -1 / 2)
    (by norm_num) (by norm_num) thirdsAc_const ((Measure.MeasureLB_iff _ _).mpr h')

/-- **`μ(L(2,χ₋₃) − π²/9) ≤ 9.52671`** from the automatic content; conditional only on the decay. -/
theorem thirds_measure_minus (hD : ThirdsDecay thirdsBc (depth0 thirdsBc)) :
    Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9) ((95133/10000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB_lam thirdsBc (by show 1 ≤ 2; norm_num) thirds_w_ne' ufData.Λ lam_lt_Dt
    (thirdsBc_content_autoUF _ (depth0_le rfl)) hD
  have h1 := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsBc.const ((95133/10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono X_le h1
  exact measureLBAt_of_const (Fam := G310.family thirdsBc (depth0 thirdsBc)) (a := 1 / 2)
    (by norm_num) (by norm_num) thirdsBc_const ((Measure.MeasureLB_iff _ _).mpr h')

end CatalanCore.Uniform.Bank.ThirdsContent.MeasureUF
