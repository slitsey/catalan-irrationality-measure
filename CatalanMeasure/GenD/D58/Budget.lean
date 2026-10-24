module

public import CatalanMeasure.GenD.Budget
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# D58 = (58,9,3,5,3): scalar budgets, instances of `GenD.Budget` for both banks

* `K160` : bank `B = 592` (x = 590.7129), `K640` : bank `B = 590` (x = 588.77278).
  The choice of K is data only; the two namespaces differ only in numerals.

Unit convention (R1): Lean works in the design's own `N` (`n = 58 N`).  The qualified ledgers
(`witness-final/q/n58_qual.out`, `n58k640_qual.out`) are in reference units `n0 = 20`
(`n = 20 N'`, `N' = (29/10) N`).  With `t = 29/10`:  `ρ ↦ tρ`, `η, χ ↦ t²η, t²χ`, `δ ↦ tδ`,
`d0 ↦ t d0`, `κ ↦ κ/t`; caps, `c2`, `c07`, `c26` are dimensionless; the cover constant `w` scales like
`ρ`, and `ρ = n0 c2 + w`.  `x` is invariant (`xval_scale`).

Finding: with the existing criterion (recycling window `(p, 2p]`) the Lean-unit `κ = B/ρ` is below 2
(`not_pay_two`); the window must be widened to `(p, θ p]`, `θ ≥ 21/10` (`pay_own`).

Provenance: all data V (Arb/Fraction-qualified, not Lean-reviewed): `witness-final/notes.md`,
config `q/cfg_final_n58.json`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Budget Real
noncomputable section

/-! ### common data -/
def c07 : ℝ := 41 / 58
def c26 : ℝ := 76 / 29
def lo : ℝ := 6931471803 / 10 ^ 10
def hi : ℝ := 6931471808 / 10 ^ 10
def nearCap : ℝ := -77 / 100
def n1 : ℝ := 67761 / 100000
def F1 : ℝ := -248835 / 100000
/-- `λ · (2g/n) = 1.68493357 · 5/29` -/
def Lm : ℝ := 168493357 / 10 ^ 8 * (5 / 29)
def wcap : ℝ := 18203 / 1000
def t : ℝ := 29 / 10
def chiRef : ℝ := 4551 / 2000
def deltaRef : ℝ := 1 / 10 ^ 7
def d0ref : ℝ := 530 / 29
def d0 : ℝ := 53
def delta : ℝ := t * deltaRef
def chi : ℝ := t ^ 2 * chiRef

theorem d0_eq : d0 = t * d0ref := by norm_num [d0, d0ref, t]

theorem log2_bounds : lo ≤ Real.log 2 ∧ Real.log 2 ≤ hi := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> [skip; skip] <;> norm_num [lo, hi] at h1 h2 ⊢ <;> linarith

/-! ### bank K160 : B = 592 -/
namespace K160
def normCap : ℝ := 1547206867 / 2000000000
def fieldCap : ℝ := -253946113 / 100000000
def residualCap : ℝ := -6311641 / 100000000
def target : ℝ := 1127919031 / 500000000
def secondCost : ℝ := 428881 / 100000
def firstCost : ℝ := 8193 / 2000
def rhoRef : ℝ := 64987 / 625
def etaRef : ℝ := 4707419 / 5000000
def B : ℝ := 592
def rho : ℝ := 58 * secondCost + (29 / 10) * wcap
def eta : ℝ := t ^ 2 * etaRef
def kappaRef : ℝ := B / rhoRef
def kappa : ℝ := B / rho

theorem rhoRef_eq : rhoRef = 20 * secondCost + wcap := by norm_num [rhoRef, secondCost, wcap]
theorem rho_eq : rho = t * rhoRef := by norm_num [rho, rhoRef, secondCost, wcap, t]
theorem rho_kappa : rho * kappa = B := by
  have : rho ≠ 0 := by norm_num [rho, secondCost, wcap]
  unfold kappa; field_simp

theorem x_ref : xval d0ref rhoRef etaRef chiRef deltaRef = 275544880000 / 466461591 := by
  norm_num [xval, d0ref, rhoRef, etaRef, chiRef, deltaRef]

theorem x_own : xval d0 rho eta chi delta = 275544880000 / 466461591 := by
  rw [d0_eq, rho_eq, eta, chi, delta, xval_scale (by norm_num [t])]
  exact x_ref

theorem x_bank : 275544880000 / 466461591 < B ∧ B - 275544880000 / 466461591 > 1 / 3 := by
  constructor <;> norm_num [B]

theorem pay_ref : Pay 2 d0ref rhoRef etaRef chiRef kappaRef deltaRef B := by
  unfold Pay kappaRef
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [B, d0ref, rhoRef, etaRef, chiRef, deltaRef]

theorem kappa_lt_two : kappa < 2 := by
  have h : (0 : ℝ) < rho := by norm_num [rho, secondCost, wcap]
  unfold kappa; rw [div_lt_iff₀ h]; norm_num [B, rho, secondCost, wcap]

theorem not_pay_two : ¬ Pay 2 d0 rho eta chi kappa delta B := by
  intro h; have := h.2.2.2.1; have := kappa_lt_two; linarith

theorem pay_own : Pay (21 / 10) d0 rho eta chi kappa delta B := by
  unfold Pay kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [B, d0, rho, eta, chi, delta, t, etaRef, chiRef, deltaRef, secondCost, wcap]

theorem cheb_ref : ChebGate d0ref rhoRef etaRef chiRef B := by
  unfold ChebGate
  rw [max_eq_left (by norm_num [d0ref, etaRef, chiRef] : (4 : ℝ) ≤ d0ref / (etaRef + chiRef))]
  norm_num [B, d0ref, rhoRef, etaRef, chiRef]

theorem cheb_own_fails : ¬ ChebGate d0 rho eta chi B := by
  unfold ChebGate
  rw [max_eq_right (by norm_num [d0, eta, chi, t, etaRef, chiRef] : d0 / (eta + chi) ≤ 4)]
  norm_num [B, rho, secondCost, wcap]

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

end K160

/-! ### bank K640 : B = 590 -/
namespace K640
def normCap : ℝ := 1547304017 / 2000000000
def fieldCap : ℝ := -7936051 / 3125000
def residualCap : ℝ := -6311789 / 100000000
def target : ℝ := 70495771 / 31250000
def secondCost : ℝ := 53611 / 12500
def firstCost : ℝ := 81933 / 20000
def rhoRef : ℝ := 519903 / 5000
def etaRef : ℝ := 4760639 / 5000000
def B : ℝ := 590
def rho : ℝ := 58 * secondCost + (29 / 10) * wcap
def eta : ℝ := t ^ 2 * etaRef
def kappaRef : ℝ := B / rhoRef
def kappa : ℝ := B / rho

theorem rhoRef_eq : rhoRef = 20 * secondCost + wcap := by norm_num [rhoRef, secondCost, wcap]
theorem rho_eq : rho = t * rhoRef := by norm_num [rho, rhoRef, secondCost, wcap, t]
theorem rho_kappa : rho * kappa = B := by
  have : rho ≠ 0 := by norm_num [rho, secondCost, wcap]
  unfold kappa; field_simp

theorem x_ref : xval d0ref rhoRef etaRef chiRef deltaRef = 91849530000 / 156001657 := by
  norm_num [xval, d0ref, rhoRef, etaRef, chiRef, deltaRef]

theorem x_own : xval d0 rho eta chi delta = 91849530000 / 156001657 := by
  rw [d0_eq, rho_eq, eta, chi, delta, xval_scale (by norm_num [t])]
  exact x_ref

theorem x_bank : 91849530000 / 156001657 < B ∧ B - 91849530000 / 156001657 > 1 / 3 := by
  constructor <;> norm_num [B]

theorem pay_ref : Pay 2 d0ref rhoRef etaRef chiRef kappaRef deltaRef B := by
  unfold Pay kappaRef
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [B, d0ref, rhoRef, etaRef, chiRef, deltaRef]

theorem kappa_lt_two : kappa < 2 := by
  have h : (0 : ℝ) < rho := by norm_num [rho, secondCost, wcap]
  unfold kappa; rw [div_lt_iff₀ h]; norm_num [B, rho, secondCost, wcap]

theorem not_pay_two : ¬ Pay 2 d0 rho eta chi kappa delta B := by
  intro h; have := h.2.2.2.1; have := kappa_lt_two; linarith

theorem pay_own : Pay (21 / 10) d0 rho eta chi kappa delta B := by
  unfold Pay kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [B, d0, rho, eta, chi, delta, t, etaRef, chiRef, deltaRef, secondCost, wcap]

theorem cheb_ref : ChebGate d0ref rhoRef etaRef chiRef B := by
  unfold ChebGate
  rw [max_eq_left (by norm_num [d0ref, etaRef, chiRef] : (4 : ℝ) ≤ d0ref / (etaRef + chiRef))]
  norm_num [B, d0ref, rhoRef, etaRef, chiRef]

theorem cheb_own_fails : ¬ ChebGate d0 rho eta chi B := by
  unfold ChebGate
  rw [max_eq_right (by norm_num [d0, eta, chi, t, etaRef, chiRef] : d0 / (eta + chi) ≤ 4)]
  norm_num [B, rho, secondCost, wcap]

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

end K640

end
end D58
end CatalanMeasure.GenD
