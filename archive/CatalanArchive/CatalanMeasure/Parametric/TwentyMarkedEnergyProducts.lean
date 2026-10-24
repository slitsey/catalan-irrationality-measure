module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyFullFirstEnergy
public import CatalanArchive.CatalanMeasure.Parametric.GroupedPhysicalProduct
public import CatalanMeasure.Parametric.FullIntervalFormula
public import CatalanMeasure.Parametric.PopulationProductPositive

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The common factor has been removed only at marked nodes. -/
def firstMarkedProduct (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  populationOneProduct P N hpm x y s /
    ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

theorem twenty_first_marked_product_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      firstMarkedProduct twenty N hpm x y s ≤
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
          90 * N * m) := by
  filter_upwards [twenty_full_first_energy_eventually hε, eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  have hz : ∀ i, Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i, Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hp := populationOneProduct_pos twenty_admissible hN hpm x y s hz hz0 hs hxi hsi
  have hc : ∀ j, 0 < |(rowCommonFactor twenty N).eval (realCoordinateInv (y j))| := by
    intro j
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of twenty N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcp : 0 < ∏ j, |(rowCommonFactor twenty N).eval (realCoordinateInv (y j))| :=
    prod_pos fun j _ => hc j
  have hlog := log_populationOneProduct_weighted twenty_admissible hN hpm
    x y s hz hz0 hs hxi hsi
  have hval := he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  have hn : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  have hn0 : (20 : ℝ) * N ≠ 0 := by positivity
  have hid : (twenty.n N : ℝ) ^ 2 *
      (-twentyDualTarget + Real.log 2 / 2 + (9 / 2 : ℝ) * ((m : ℝ) / twenty.n N) + ε) =
      (20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) + 90 * N * m := by
    rw [hn]
    field_simp [hn0]
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (twenty.n N : ℝ))
  rw [← hlog, hid] at hbound
  rw [firstMarkedProduct, ← Real.exp_log (div_pos hp hcp)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div hp.ne' hcp.ne', Real.log_prod (fun j _ => (hc j).ne')]
  exact hbound

theorem twenty_grouped_marked_product_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = twenty.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedPhysicalProduct twenty N z x y s ≤
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
          89 * N * (a + b)) := by
  filter_upwards [twenty_grouped_second_energy_eventually hε, eventually_gt_atTop (0 : ℕ)]
    with N he hN r a b hcount z x y s hz hz0 hx hy hs hzi hxi hyi hsi
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hy0 : ∀ i, y i ≠ 0 := fun i => (hy i).1.ne'
  have hlog := log_groupedPhysicalProduct twenty_admissible hN z x y s
    hz hx hy' hs hz0 hy0 hzi hxi hyi hsi
  have hval := he r a b hcount z x y s hz hz0 hx hy hs hzi hxi hyi hsi
  have hn : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  have hn0 : (20 : ℝ) * N ≠ 0 := by positivity
  have hid : (twenty.n N : ℝ) ^ 2 *
      (-twentyDualTarget + Real.log 2 / 2 + (89 / 20 : ℝ) * (((a + b : ℕ) : ℝ) / twenty.n N) + ε) =
      (20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) + 89 * N * (a + b) := by
    rw [hn, Nat.cast_add]
    field_simp [hn0]
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (twenty.n N : ℝ))
  rw [← hlog, hid] at hbound
  have hpos : 0 < groupedPhysicalProduct twenty N z x y s := by
    have hS : 0 < (∏ i, (1 + s i)) ^ (a + b) :=
      pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
    have hZ : 0 < ∏ i, |z i| ^ ((twenty.g N : ℤ) - (twenty.n N - 1 : ℕ)) :=
      prod_pos fun i _ => zpow_pos (abs_pos.mpr (hz0 i)) _
    have hX : 0 < ∏ i, markedSheetWeight twenty N (x i) :=
      prod_pos fun i _ => markedSheetWeight_pos twenty N _
    have hY : 0 < ∏ i, markedSheetWeight twenty N (y i) *
        |y i| ^ (twenty.n N - 1 - 2 * twenty.g N) :=
      prod_pos fun i _ => mul_pos (markedSheetWeight_pos twenty N _)
        (pow_pos (abs_pos.mpr (hy0 i)) _)
    have hPair := groupedPairProduct_pos (Fin.append z x) y
        (fun i => abs_lt.mpr (Fin.addCases (fun j => by simpa using hz j)
          (fun j => by simpa using hx j) i)) (fun i => abs_lt.mpr (hy' i)) hxi hyi
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hS hZ) hX) hY) hPair)
      (paramPinPrincipal_pos twenty_admissible hN z s hz hs hz0 hzi hsi)
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr hbound

end
end CatalanMeasure.Parametric
