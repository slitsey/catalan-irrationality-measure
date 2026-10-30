import CatalanCore.Uniform.Bank.ThirdsContent.Final
import CatalanCore.Uniform.Bank.Thirds.Final
set_option Elab.async false

/-! # The thirds measure from the no-UF content (lane B, B4b)

`LamFin` (Final) is the content constant of the finite-prefix no-UF template; with the matched
decay `ThirdsDecay` (`D = DtT`, `c = ctT`, owned by D17) it gives `μ ≤ 9.5563` for
`L(2,χ₋₃) ± π²/9`.  The theorems are conditional exactly on (i) the rank / LP piece covers and
(ii) `ThirdsDecay`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanFrames.Thirds CatalanFrames.P6

theorem LamFin_lt_Dt : ((LamFin : ℚ) : ℝ) < (DtT : ℝ) := by
  unfold LamFin DtT; push_cast; norm_num

theorem ratio_fin_le : (ctT : ℝ) / ((DtT : ℝ) - (LamFin : ℚ)) ≤ ((95563 / 10000 : ℚ) : ℝ) := by
  have hpos : 0 < (DtT : ℝ) - ((LamFin : ℚ) : ℝ) := sub_pos.2 LamFin_lt_Dt
  rw [div_le_iff₀ hpos]
  unfold LamFin DtT ctT; push_cast; norm_num

theorem thirds_measureLB_fin (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hS : HasScaledContent (FamE Fr (depth0 Fr)) G310.scale ((LamFin : ℚ) : ℝ))
    (hD : ThirdsDecay Fr (depth0 Fr)) :
    (G310.family Fr (depth0 Fr)).MeasureLB
      ((1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - (LamFin : ℚ))) := by
  have hmass : (G310.common.mass : ℝ) = 1 := by rw [G310_common_mass]; norm_num
  have hD' : HasScaledDecay ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0))
      G310.scale (DtT : ℝ) (ctT : ℝ) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD ε hε
    exact ⟨R0, fun n hn => h n hn.1⟩
  have hc : (0 : ℝ) < (ctT : ℝ) := by unfold ctT; norm_num
  exact measure_of_family_nv0_even
    ((G310.family Fr (depth0 Fr)).restrictAdm (fun i => i.1 % 2 = 0)) G310.scale
    (γ := 1) (K := G310.common.n) hS hD' LamFin_lt_Dt hc one_pos (Nat.cast_nonneg _)
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

theorem thirds_X_le_fin :
    (1 : ℝ) * (ctT : ℝ) / ((DtT : ℝ) - (LamFin : ℚ)) ≤ ((95563 / 10000 : ℚ) : ℝ) := by
  rw [one_mul]; exact ratio_fin_le

/-- `μ(L(2,χ₋₃) + π²/9) ≤ 9.5563`, from the rank/LP covers and the decay. -/
theorem thirds_measure_plus_fin
    (h1 : ∀ (depth : ℕ) (i : (FamE thirdsAc depth).ι), (FamE thirdsAc depth).Adm i →
      ∀ P ∈ rlpList_1_1, PieceCov thirdsAc depth 1 i P)
    (h5 : ∀ (depth : ℕ) (i : (FamE thirdsAc depth).ι), (FamE thirdsAc depth).Adm i →
      ∀ P ∈ rlpList_1_5, PieceCov thirdsAc depth 5 i P)
    (hD : ThirdsDecay thirdsAc (depth0 thirdsAc)) :
    Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9) ((95563 / 10000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB_fin thirdsAc (by show 1 ≤ 2; norm_num) thirds_w_ne
    (thirds_content_fin_1 _ h1 h5) hD
  have h1' := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsAc.const ((95563 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono thirds_X_le_fin h1'
  exact measureLBAt_of_const (Fam := G310.family thirdsAc (depth0 thirdsAc)) (a := -1 / 2)
    (by norm_num) (by norm_num) thirdsAc_const ((Measure.MeasureLB_iff _ _).mpr h')

/-- `μ(L(2,χ₋₃) − π²/9) ≤ 9.5563`, from the rank/LP covers and the decay. -/
theorem thirds_measure_minus_fin
    (h1 : ∀ (depth : ℕ) (i : (FamE thirdsBc depth).ι), (FamE thirdsBc depth).Adm i →
      ∀ P ∈ rlpList_2_1, PieceCov thirdsBc depth 1 i P)
    (h5 : ∀ (depth : ℕ) (i : (FamE thirdsBc depth).ι), (FamE thirdsBc depth).Adm i →
      ∀ P ∈ rlpList_2_5, PieceCov thirdsBc depth 5 i P)
    (hD : ThirdsDecay thirdsBc (depth0 thirdsBc)) :
    Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9) ((95563 / 10000 : ℚ) : ℝ) := by
  have h0 := thirds_measureLB_fin thirdsBc (by show 1 ≤ 2; norm_num) thirds_w_ne'
    (thirds_content_fin_2 _ h1 h5) hD
  have h1' := (Measure.MeasureLB_iff _ _).mp h0
  have h' : Measure.MeasureLBAt thirdsBc.const ((95563 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono thirds_X_le_fin h1'
  exact measureLBAt_of_const (Fam := G310.family thirdsBc (depth0 thirdsBc)) (a := 1 / 2)
    (by norm_num) (by norm_num) thirdsBc_const ((Measure.MeasureLB_iff _ _).mpr h')

end CatalanCore.Uniform.Bank.ThirdsContent
