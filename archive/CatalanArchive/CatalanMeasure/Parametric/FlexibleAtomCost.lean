module
public import CatalanArchive.CatalanMeasure.Parametric.FlexibleFirstEnergy
public import CatalanArchive.CatalanMeasure.Parametric.FlexibleSecondSelection
public import CatalanArchive.CatalanMeasure.Parametric.TargetAtomCost
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan Set Finset MeasureTheory Matrix Filter
open scoped Topology BigOperators
noncomputable section
theorem first_marked_sheet_with_trial {target c : ℝ} (F : FirstTrialBoundsAt target c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      markedSheetProduct twenty N hpm x y s ≤
        ((3 / 2 : ℝ) ^ twenty.n N * (twenty.n N : ℝ) ^ ((twenty.n N : ℝ) / 2)) *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            (20*c) * N * m) := by
  filter_upwards [first_marked_product_with_trial F hε,
      Filter.eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  exact (marked_sheet_product_first_le twenty_admissible hN hpm x y s hx hx0 hy hy0 hs).trans
    (mul_le_mul_of_nonneg_left (he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase)
      (by positivity))

theorem marked_sheet_with_trials {target c residual nearCap cost r : ℝ}
    (F : FirstTrialBoundsAt target c) (D : SecondTrialBoundsCostAt target residual nearCap cost) (hfc : 20*c ≤ r) (hsc : 20*cost ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      markedSheetProduct twenty N hpm x y s ≤
        (5 : ℝ) ^ m * twentySheetPrefactor N *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m) := by
  filter_upwards [first_marked_sheet_with_trial F hε,
      second_marked_sheet_product_at_cost target (20*cost) (fun _ he => grouped_marked_product_at_cost D he) hε] with N hfirst hsecond
  intro p m hpm x y s hx hx0 hy hy0 hs hzi hsi
  have hxi : Function.Injective x := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (hzi (by simpa using hij))
  have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  have hH : 0 ≤ twentySheetPrefactor N := by unfold twentySheetPrefactor; positivity
  have hF : (3 / 2 : ℝ) ^ twenty.n N *
      (twenty.n N : ℝ) ^ ((twenty.n N : ℝ) / 2) ≤ twentySheetPrefactor N := by
    unfold twentySheetPrefactor
    exact le_add_of_nonneg_right (by positivity)
  have hI : (1 + 10 * Real.exp 12 * (twenty.n N : ℝ)) ^ twenty.n N ≤
      twentySheetPrefactor N := by
    unfold twentySheetPrefactor
    exact le_add_of_nonneg_left (by positivity)
  by_cases hcase : -1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)
  · have hh := hfirst p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
    apply hh.trans
    apply mul_le_mul
    · exact hF.trans (le_mul_of_one_le_left hH h5)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N*m := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right hfc hNm]
    · exact (Real.exp_pos _).le
    · positivity
  · have hh := hsecond p m hpm x y s hx hx0 hy hy0 hs hzi hsi (le_of_not_gt hcase)
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hI (pow_nonneg (by norm_num) _)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_right hsc hNm]
    · exact (Real.exp_pos _).le
    · positivity

theorem weighted_atom_point_with_trials {target c residual nearCap cost r w : ℝ}
    (F : FirstTrialBoundsAt target c) (D : SecondTrialBoundsCostAt target residual nearCap cost) (hfc : 20*c ≤ r) (hsc : 20*cost ≤ r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin (18*N)),
      |(rowCommonFactor twenty N).eval (CatalanMeasure.chebX (18*N) a)| *
        |restrictedWeight twenty N k (CatalanMeasure.chebX (18*N)) a| ≤
          108000*(N : ℝ)*Real.exp (w*N)) : WeightedAtomPointAt target (r+w) := by
  intro ε hε
  filter_upwards [marked_sheet_with_trials F D hfc hsc hε,
      hweights, eventually_gt_atTop (0 : ℕ)]
    with N hsheet hw hN p m hpm E hEi hEn x y s k a hx hx0 hy hy0 hs hzi hsi hcoord
  let β := fun j => restrictedWeight twenty N (k j) (CatalanMeasure.chebX (18 * N)) (a j)
  let Q : ℝ := 108000 * N * Real.exp (w * N)
  have hweight (j : Fin m) :
      |(rowCommonFactor twenty N).eval (realCoordinateInv (y j))| * |β j| ≤ Q := by
    rw [hcoord j]
    exact hw (k j) (a j)
  have hbase := original_poly_atoms_mixedDouble_mul_weight_le twenty_admissible hN hpm
    E hEi hEn x y s β hx hx0 hy hy0 hs hweight
  have hp := hsheet p m hpm x y s hx hx0 hy hy0 hs hzi hsi
  have hQ : 0 ≤ Q ^ m := by dsimp [Q]; positivity
  have hc : (5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m = (540000 * (N : ℝ)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp ((20 * (N : ℝ)) ^ 2 *
      (-target + Real.log 2 / 2 + ε) + r * N * m) *
      Real.exp (w * (N : ℝ)) ^ m =
      Real.exp ((20 * (N : ℝ)) ^ 2 *
        (-target + Real.log 2 / 2 + ε) + (r+w) * N * m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ markedSheetProduct twenty N hpm x y s * Q ^ m := hbase
    _ ≤ ((5 : ℝ) ^ m * twentySheetPrefactor N *
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m)) * Q ^ m := mul_le_mul_of_nonneg_right hp hQ
    _ = twentySheetPrefactor N * ((5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m) *
        (Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m) * Real.exp (w * (N : ℝ)) ^ m) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, he]


end
end CatalanMeasure.Parametric
