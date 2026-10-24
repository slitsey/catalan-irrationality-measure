module

public import CatalanMeasure.GenD.Budget
public import CatalanMeasure.GenD.PayW
public import CatalanMeasure.GenD.Analytic.Const
public import CatalanMeasure.GenD.P20.Normalizer
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# P20: scalar budgets and payments of the 728 bank (instance file, numerals only)

Instance of `GenD.Budget` / `GenD.PayW` for `twenty` with the window parameter `w = 1`
(the original recycled-polynomial criterion).  The radius cost is `rho = 20 c2 + 17.913 + 1/1000`;
the extra `1/1000` makes `wc = 17.913 < rho - 20 c2` strict, as required by
`gap_weight_bounds`; the payments keep room (`pay`).
-/

namespace CatalanMeasure.GenD
namespace P20
open Budget Real
noncomputable section

def lo : ℝ := 6931471803 / 10 ^ 10
def hi : ℝ := 6931471808 / 10 ^ 10

theorem log2_bounds : lo ≤ Real.log 2 ∧ Real.log 2 ≤ hi := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> norm_num [lo, hi] at h1 h2 ⊢ <;> linarith

def c07 : ℝ := 7 / 10
def c26 : ℝ := 13 / 5
def nearCap : ℝ := -3 / 4
def target : ℝ := 141027507 / 62500000
def normCap : ℝ := 24149189 / 31250000
def fieldCap : ℝ := -10176053 / 4000000
def residualCap : ℝ := -5247033 / 100000000
def secondCost : ℝ := 429033 / 100000
def n1 : ℝ := 67761 / 100000
def F1 : ℝ := -247913 / 100000
def Lm : ℝ := 168493357 / 10 ^ 8 / 5
def firstCost : ℝ := 421 / 100
def wcap : ℝ := 17913 / 1000
def rho : ℝ := 20 * secondCost + wcap + 1 / 1000
def kappa : ℝ := 728 / rho
def eta : ℝ := 5993 / 3125 + 649 / 1000
def delta : ℝ := 1 / 10 ^ 7

theorem rho_kappa : rho * kappa = 728 := by
  have : rho ≠ 0 := by norm_num [rho, secondCost, wcap]
  unfold kappa; field_simp

/-- All payment arithmetic (window parameter `w = 1`). -/
theorem pay : PayW 1 18 rho eta kappa delta 728 := by
  unfold PayW kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [rho, eta, delta, secondCost, wcap]

theorem second_budget_log2 {a tt : ℝ} (ha : 0 ≤ a) (htt : 0 ≤ tt) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + tt - tt ^ 2) * Real.log 2 + normCap
        + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 + (a - tt) * residualCap
        + tt * nearCap + (9 / 10 : ℝ) * a ≤
      -target + Real.log 2 / 2 + (secondCost + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact second_budget (m := -(normCap + fieldCap + target - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c26, hi, lo, normCap, fieldCap, target, c07, residualCap, secondCost])
    (by norm_num [hi, residualCap, nearCap]) ha htt

theorem first_budget_log2 (a : ℝ) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * Real.log 2 + n1 + (1 - a) * F1
        + a * (1 - a) * Real.log 2 + a * Lm + (9 / 10 : ℝ) * a ≤
      -target + Real.log 2 / 2 + (firstCost + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact first_budget (m := -(n1 + F1 + target - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c07, lo, n1, F1, target])
    (by norm_num [c26, hi, lo, n1, F1, target, c07, Lm, firstCost])
    (by norm_num [c26, lo, F1, Lm, firstCost])

/-! ### generic constants at P20 -/

theorem gRes_p20 : Analytic.gRes design = 9 / 10 := by
  unfold Analytic.gRes design Parametric.twenty; norm_num

theorem gKappa_p20 : Analytic.gKappa design = 3 / 10 := by
  unfold Analytic.gKappa design Parametric.twenty; norm_num

theorem gC0_p20 : Analytic.gC0 design = 1 / 5 := by
  unfold Analytic.gC0; rw [gKappa_p20]; norm_num

theorem gC1_p20 : Analytic.gC1 design = 8 / 5 := by
  unfold Analytic.gC1; rw [gKappa_p20, gRes_p20]; norm_num

theorem second_budget_gen {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-Analytic.gC0 design + Analytic.gC1 design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * residualCap + t * nearCap ≤
        -target + Real.log 2 / 2 + secondCost * a := by
  rw [gC0_p20, gC1_p20]
  have h := second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

/-- `eta < tDelta - gD20`: the payments leave room for the denominator growth. -/
def tDelta : ℝ := (target - Real.log 2 / 2) * 20 ^ 2

theorem eta_le : eta < tDelta - gD20 := by
  obtain ⟨hl, hh⟩ := log2_bounds
  unfold tDelta gD20
  norm_num [eta, target, lo, hi] at hl hh ⊢
  linarith

theorem n0_sub_g0 : ((design.n0 - design.g0 : ℕ) : ℝ) = 18 := by
  norm_num [design, Parametric.twenty]

end
end P20
end CatalanMeasure.GenD
