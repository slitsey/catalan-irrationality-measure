module
public import CatalanMeasure.Parametric.TargetSecondEnergy
public import CatalanMeasure.Parametric.TwentyMarkedSecondProduct
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Filter Finset
open scoped Topology BigOperators
noncomputable section
theorem grouped_marked_product_at_target {target : ℝ} (D : SecondTrialBoundsAt target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = twenty.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedPhysicalProduct twenty N z x y s ≤
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          89 * N * (a + b)) := by
  filter_upwards [second_energy_at_target D hε, eventually_gt_atTop (0 : ℕ)]
    with N he hN r a b hcount z x y s hz hz0 hx hy hs hzi hxi hyi hsi
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hy0 : ∀ i, y i ≠ 0 := fun i => (hy i).1.ne'
  have hlog := log_groupedPhysicalProduct twenty_admissible hN z x y s
    hz hx hy' hs hz0 hy0 hzi hxi hyi hsi
  have hval := he r a b hcount z x y s hz hz0 hx hy hs hzi hxi hyi hsi
  have hn : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  have hn0 : (20 : ℝ) * N ≠ 0 := by positivity
  have hid : (twenty.n N : ℝ) ^ 2 *
      (-target + Real.log 2 / 2 + (89 / 20 : ℝ) * (((a + b : ℕ) : ℝ) / twenty.n N) + ε) =
      (20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + 89 * N * (a + b) := by
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
