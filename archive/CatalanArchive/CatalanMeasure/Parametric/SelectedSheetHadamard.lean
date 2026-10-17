module

public import CatalanMeasure.Parametric.MarkedSheetExpansion
public import CatalanMeasure.Parametric.RealSheetBounds

/-!
# Complementary Hadamard bound for every actual/near selection
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

theorem selected_laurent_hadamard_bound {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (t : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    |(Matrix.of fun i r : Fin (P.n N) => if t i then x i ^ ((r : ℤ) - P.g N)
      else actualLaurentEntry (P.g N) r (x i)).det| ≤
      (3 / 2 : ℝ) ^ P.n N * (Real.sqrt (P.n N : ℝ)) ^ P.n N /
        (2 : ℝ) ^ ((P.n N).choose 2) *
        ∏ i, (Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) *
          |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) := by
  let C : ℝ := (Real.sqrt (P.n N : ℝ)) ^ P.n N / (2 : ℝ) ^ ((P.n N).choose 2)
  let W : Fin (P.n N) → ℝ := fun i =>
    Real.sqrt (1 + x i ^ 2) ^ (P.n N - 1) *
      |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))
  let V : Fin (P.n N) → Bool → Fin (P.n N) → ℝ := fun i b r =>
    realSheetNode (x i) b ^ ((r : ℤ) - P.g N)
  let c : Fin (P.n N) → Bool → ℝ := fun i b =>
    if t i then (if b then 1 else 0) else realSheetCoefficient (x i) b
  have hm : (Matrix.of fun i r : Fin (P.n N) =>
        if t i then x i ^ ((r : ℤ) - P.g N) else actualLaurentEntry (P.g N) r (x i)) =
      Matrix.of (fun i r => ∑ b : Bool, c i b * V i b r) := by
    ext i r
    have hf : ((x i)⁻¹) ^ ((r : ℤ) - P.g N) = x i ^ ((P.g N : ℤ) - r) := by
      rw [inv_zpow, ← zpow_neg, neg_sub]
    cases ht : t i <;> by_cases hneg : x i < 0 <;>
      simp [c, V, ht, realSheetCoefficient, realSheetNode, actualLaurentEntry, hneg, hf] <;> ring
  have hchoice (ε : Fin (P.n N) → Bool) :
      |(Matrix.of fun i r => V i (ε i) r).det| ≤ C * ∏ i, W i := by
    let z : Fin (P.n N) → ℝ := fun i => realSheetNode (x i) (ε i)
    have hz (i : Fin (P.n N)) : z i ≠ 0 := by
      dsimp only [z, realSheetNode]
      split_ifs
      · exact hx0 i
      · exact inv_ne_zero (hx0 i)
    have hmon := laurent_monomial_det_abs_le (P.g N) z hz
    rw [← Matrix.det_transpose]
    apply hmon.trans
    apply mul_le_mul_of_nonneg_left
    · apply prod_le_prod₀
      · intro i _
        exact mul_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
      · intro i _
        simpa only [z, realSheetNode, W] using
          sheet_choice_weight_le hP hN (hx i) (hx0 i) (ε i)
    · positivity
  have hcoeff : (∏ i, ∑ b : Bool, |c i b|) ≤ (3 / 2 : ℝ) ^ P.n N := by
    calc
      _ ≤ ∏ _i : Fin (P.n N), (3 / 2 : ℝ) := by
        apply prod_le_prod₀
        · intro i _
          exact sum_nonneg fun _ _ => abs_nonneg _
        · intro i _
          cases ht : t i
          · simpa [c, ht] using realSheetCoefficient_abs_sum_le (x i)
          · norm_num [c, ht, Fintype.sum_bool]
      _ = _ := by simp [div_pow]
  have hB : 0 ≤ C * ∏ i, W i := by
    exact (abs_nonneg _).trans (hchoice (fun _ => false))
  rw [hm]
  calc
    _ ≤ (C * ∏ i, W i) * ∏ i, (∑ b : Bool, |c i b|) :=
      abs_det_binary_rows_le V c hB hchoice
    _ ≤ (C * ∏ i, W i) * (3 / 2 : ℝ) ^ P.n N :=
      mul_le_mul_of_nonneg_left hcoeff hB
    _ = _ := by dsimp only [C, W]; ring

end

end CatalanMeasure.Parametric
