import CatalanCore.Uniform.Bank.ThirdsContent.Assemble
import CatalanCore.Uniform.Bank.Thirds.Final
set_option Elab.async false

/-! # The thirds measure without the UF layer (lane B, B4b)

Content constant of the no-UF route (min of tropical, rank, strict LP1/LP2, M3D; bank-prices-noUF
`out-third-strict.json`): `LamT0 = 3906810466483/1189828640000 + (9/200) log 2 ≈ 3.314698`.
With the same `D, c` as the UF route the measure is `μ ≈ 9.55627 < 9.5563`.  The UF route
(`Bank.Thirds.Final`, 9.52671) is untouched. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanFrames.Thirds CatalanFrames.P6

noncomputable def LamT0 : ℝ := 3906810466483 / 1189828640000 + 9 / 200 * Real.log 2

theorem LamT0_lt_Dt : LamT0 < (DtT : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold LamT0 DtT
  push_cast
  norm_num at h ⊢
  linarith

theorem ratio_le0 : (ctT : ℝ) / ((DtT : ℝ) - LamT0) ≤ ((95563 / 10000 : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have hpos : 0 < (DtT : ℝ) - LamT0 := sub_pos.2 LamT0_lt_Dt
  rw [div_le_iff₀ hpos]
  unfold LamT0 DtT ctT
  push_cast
  norm_num at h ⊢
  linarith

/-- Coefficient content of the thirds family at even scales, at the no-UF price. -/
def ThirdsContent0 (Fr : Frame) (depth : ℕ) : Prop :=
  HasScaledContent ((G310.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) G310.scale LamT0

theorem thirds_measureLB0 (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hS : ThirdsContent0 Fr (depth0 Fr)) (hD : ThirdsDecay Fr (depth0 Fr)) :
    (G310.family Fr (depth0 Fr)).MeasureLB
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - LamT0)) := by
  have hmass : (G310.common.mass : ℝ) = 1 := by rw [G310_common_mass]; norm_num
  have hD' : HasScaledDecay ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0))
      G310.scale (DtT : ℝ) (ctT : ℝ) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD ε hε
    exact ⟨R0, fun n hn => h n hn.1⟩
  have hc : (0 : ℝ) < (ctT : ℝ) := by unfold ctT; norm_num
  exact measure_of_family_nv0_even
    ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0)) G310.scale
    (γ := 1) (K := G310.common.n) hS hD' LamT0_lt_Dt hc one_pos (Nat.cast_nonneg _)
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

theorem thirds_X_le0 :
    (1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - LamT0) ≤ ((95563 / 10000 : ℚ) : ℝ) := by
  rw [one_mul]; exact ratio_le0

/-- `μ(L(2,χ₋₃) + π²/9) ≤ 9.5563` from the no-UF content and the decay. -/
theorem thirds_measure_plus_noUF_of
    (hS : ThirdsContent0 thirdsAc (depth0 thirdsAc)) (hD : ThirdsDecay thirdsAc (depth0 thirdsAc)) :
    Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9) ((95563 / 10000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB0 thirdsAc (by show 1 ≤ 2; norm_num) thirds_w_ne hS hD
  have h1 := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsAc.const ((95563 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono thirds_X_le0 h1
  exact measureLBAt_of_const (Fam := G310.family thirdsAc (depth0 thirdsAc)) (a := -1 / 2)
    (by norm_num) (by norm_num) thirdsAc_const ((Measure.MeasureLB_iff _ _).mpr h')

/-- `μ(L(2,χ₋₃) − π²/9) ≤ 9.5563` from the no-UF content and the decay. -/
theorem thirds_measure_minus_noUF_of
    (hS : ThirdsContent0 thirdsBc (depth0 thirdsBc)) (hD : ThirdsDecay thirdsBc (depth0 thirdsBc)) :
    Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9) ((95563 / 10000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB0 thirdsBc (by show 1 ≤ 2; norm_num) thirds_w_ne' hS hD
  have h1 := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsBc.const ((95563 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono thirds_X_le0 h1
  exact measureLBAt_of_const (Fam := G310.family thirdsBc (depth0 thirdsBc)) (a := 1 / 2)
    (by norm_num) (by norm_num) thirdsBc_const ((Measure.MeasureLB_iff _ _).mpr h')

end CatalanCore.Uniform.Bank.ThirdsContent
