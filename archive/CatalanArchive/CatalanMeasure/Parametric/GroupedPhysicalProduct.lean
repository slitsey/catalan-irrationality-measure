module

public import CatalanArchive.CatalanMeasure.Parametric.GroupedNodeWeights
public import CatalanMeasure.Parametric.GroupedFieldAssembly
public import CatalanMeasure.Parametric.PopulationPhysicalValue

/-!
# The grouped physical product after canceling marked common factors
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

def groupedPairProduct {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ) : ℝ :=
  |∏ i : Fin a, ∏ j ∈ Ioi i, (x j - x i)| *
    |∏ i : Fin b, ∏ j ∈ Ioi i, (y j - y i)| * crossCauchyProduct x y

theorem groupedPairProduct_pos {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ)
    (hx : ∀ i, |x i| < 1) (hy : ∀ i, |y i| < 1)
    (hxi : Function.Injective x) (hyi : Function.Injective y) : 0 < groupedPairProduct x y :=
  mul_pos (mul_pos (energy_abs_vandermonde_pos x hxi) (energy_abs_vandermonde_pos y hyi))
    (crossCauchyProduct_pos x y hx hy)

theorem log_groupedPairProduct {a b : ℕ} (x : Fin a → ℝ) (y : Fin b → ℝ)
    (hx : ∀ i, |x i| < 1) (hy : ∀ i, |y i| < 1)
    (hxi : Function.Injective x) (hyi : Function.Injective y) :
    Real.log (groupedPairProduct x y) =
      (∑ i : Fin a, ∑ j ∈ Ioi i, Real.log |x j - x i|) +
        (∑ i : Fin b, ∑ j ∈ Ioi i, Real.log |y j - y i|) +
        Real.log (crossCauchyProduct x y) := by
  rw [groupedPairProduct,
    Real.log_mul (mul_pos (energy_abs_vandermonde_pos x hxi)
      (energy_abs_vandermonde_pos y hyi)).ne' (crossCauchyProduct_pos x y hx hy).ne',
    Real.log_mul (energy_abs_vandermonde_pos x hxi).ne' (energy_abs_vandermonde_pos y hyi).ne',
    log_abs_vandermonde x hxi, log_abs_vandermonde y hyi]

def groupedPhysicalProduct (P : Parameters) (N : ℕ) {r a b : ℕ}
    (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ) : ℝ :=
  (∏ i, (1 + s i)) ^ (a + b) *
    (∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
    (∏ i, markedSheetWeight P N (x i)) *
    (∏ i, markedSheetWeight P N (y i) * |y i| ^ (P.n N - 1 - 2 * P.g N)) *
    groupedPairProduct (Fin.append z x) y * paramPinPrincipal P N z s

def groupedPhysicalConstant (P : Parameters) (N r a b : ℕ) : ℝ :=
  ((r * (P.C N - 1) + (a + b) * (P.n N - P.g N - 1) + r.choose 2 : ℕ) : ℝ) /
    (P.n N : ℝ) ^ 2 * Real.log 2

def groupedPhysicalMarkedField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  -((P.n N - P.g N - 1 : ℕ) : ℝ) / (P.n N : ℝ) * Real.log (1 + x ^ 2)

def groupedPhysicalNearField (P : Parameters) (N : ℕ) (y : ℝ) : ℝ :=
  groupedPhysicalMarkedField P N y +
    ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) / (P.n N : ℝ) * Real.log |y|

set_option maxHeartbeats 1200000 in
theorem log_groupedPhysicalProduct {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {r a b : ℕ} (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ)
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hz0 : ∀ i, z i ≠ 0) (hy0 : ∀ i, y i ≠ 0)
    (hzi : Function.Injective z) (hxi : Function.Injective (Fin.append z x))
    (hyi : Function.Injective y) (hsi : Function.Injective s) :
    Real.log (groupedPhysicalProduct P N z x y s) =
      (P.n N : ℝ) ^ 2 * groupedValueWithFields (P.n N : ℝ)
        (groupedPhysicalConstant P N r a b) (populationPhysicalFreeField P N)
        (groupedPhysicalMarkedField P N) (groupedPhysicalNearField P N)
        (populationPhysicalColumnField P N (a + b)) z x y s := by
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  have hg := two_g_lt_n hP hN
  have hn1 : 1 ≤ P.n N := by have := n_pos hP hN; omega
  have hC1 : 1 ≤ P.C N := by
    rw [C_eq_A_add_residual hP hN]
    omega
  have hH2 : 2 ≤ P.H N := by
    have hh : 0 < P.h N := Nat.mul_pos hP.2.2.2.1 hN
    change 2 ≤ P.C N + P.h N
    omega
  have hzx : ∀ i, |Fin.append z x i| < 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using abs_lt.mpr (hz j)
    · simpa using abs_lt.mpr (hx j)
  have hS : 0 < (∏ i : Fin r, (1 + s i)) ^ (a + b) :=
    pow_pos (prod_pos fun i _ => by linarith [(hs i).1]) _
  have hZ : 0 < ∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
    prod_pos fun i _ => zpow_pos (abs_pos.mpr (hz0 i)) _
  have hX : 0 < ∏ i, markedSheetWeight P N (x i) :=
    prod_pos fun i _ => markedSheetWeight_pos P N _
  have hY : 0 < ∏ i, markedSheetWeight P N (y i) * |y i| ^ (P.n N - 1 - 2 * P.g N) :=
    prod_pos fun i _ => mul_pos (markedSheetWeight_pos P N _)
      (pow_pos (abs_pos.mpr (hy0 i)) _)
  have hV := groupedPairProduct_pos (Fin.append z x) y hzx (fun i => abs_lt.mpr (hy i)) hxi hyi
  have hPin := paramPinPrincipal_pos hP hN z s hz hs hz0 hzi hsi
  unfold groupedPhysicalProduct
  rw [Real.log_mul (by positivity) hPin.ne', Real.log_mul (by positivity) hV.ne',
    Real.log_mul (by positivity) hY.ne', Real.log_mul (by positivity) hX.ne',
    Real.log_mul hS.ne' hZ.ne', Real.log_pow,
    Real.log_prod (fun i _ => (show 0 < 1 + s i by linarith [(hs i).1]).ne'),
    Real.log_prod (fun i _ => zpow_ne_zero _ (abs_ne_zero.mpr (hz0 i))),
    Real.log_prod (fun i _ => (markedSheetWeight_pos P N (x i)).ne'),
    Real.log_prod (fun i _ => (mul_pos (markedSheetWeight_pos P N (y i))
      (pow_pos (abs_pos.mpr (hy0 i)) _)).ne'),
    log_groupedPairProduct (Fin.append z x) y hzx (fun i => abs_lt.mpr (hy i)) hxi hyi,
    log_paramPinPrincipal hP hN z s hz hs hz0 hzi hsi]
  simp_rw [Real.log_zpow, log_markedSheetWeight,
    Real.log_mul (markedSheetWeight_pos P N _).ne' (pow_ne_zero _ (abs_ne_zero.mpr (hy0 _))),
    Real.log_pow, log_markedSheetWeight]
  have hCR : (P.C N : ℝ) = (P.A N : ℝ) + (P.n N : ℝ) - (P.g N : ℝ) := by
    rw [C_eq_A_add_residual hP hN, Nat.cast_add, Nat.cast_sub (by omega : P.g N ≤ P.n N)]
    ring
  have hHR : (P.H N : ℝ) = (P.C N : ℝ) + (P.h N : ℝ) := Nat.cast_add _ _
  unfold groupedValueWithFields groupedPopulationInteraction groupedPhysicalConstant
    groupedPhysicalNearField groupedPhysicalMarkedField populationPhysicalFreeField
    paramPopulationRowField populationPhysicalColumnField pinOffDiagonalInteraction
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_div, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hn1, Nat.cast_sub hC1, Nat.cast_sub hH2, Nat.cast_one, Nat.cast_ofNat,
    Int.cast_sub, Int.cast_natCast]
  norm_num only
  rw [hHR, hCR]
  field_simp
  ring

end

end CatalanMeasure.Parametric
