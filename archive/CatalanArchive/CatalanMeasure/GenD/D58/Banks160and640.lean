module

public import CatalanMeasure.GenD.D58.Final
public import CatalanMeasure.GenD.Analytic.DeltaChain
public import CatalanMeasure.GenD.Analytic.Instances
public import CatalanMeasure.GenD.D58.C3.Cert
public import CatalanMeasure.GenD.D58.FirstTrialCert
public import CatalanMeasure.GenD.D58.Circle
public import CatalanMeasure.GenD.PayW

@[expose] public section

/-!
# Archived: the banks K160 (`B = 592`) and K640 (`B = 590`, x = 588.77278) of `D58`

Scalar budgets (`D58.Budget`), payments (`D58.Pay`), first-trial contracts (`FirstTrial`,
`FirstTrialCert`), circle side condition (`Circle`) and the final / certificate-level statements
(`Final`, `Certified`), moved out of the main tree when the release moved to the bank `K590`.
-/

namespace CatalanMeasure.GenD
namespace D58
noncomputable section

section
open Budget Real
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

section
open Real
theorem K160.pay_w : PayW (3 / 4) d0 K160.rho (K160.eta + chi) K160.kappa delta K160.B := by
  unfold PayW K160.kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [K160.B, d0, K160.rho, K160.eta, chi, delta, t, K160.etaRef, chiRef, deltaRef,
      K160.secondCost, wcap]

theorem K640.pay_w : PayW (3 / 4) d0 K640.rho (K640.eta + chi) K640.kappa delta K640.B := by
  unfold PayW K640.kappa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [K640.B, d0, K640.rho, K640.eta, chi, delta, t, K640.etaRef, chiRef, deltaRef,
      K640.secondCost, wcap]

end

section
open Set Filter OAI.InternalCatalan CatalanMeasure.Cert CatalanMeasure.G728
open CatalanMeasure.GenD.Analytic
/-- Bank K160 first-population contract. -/
def K160.firstTrial
    (hrow : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      firstRowFieldG (11 / 29) (3 / 29) (49 / 58) lamFirst (5 / 29) firstP firstV x ≤ MX1)
    (hcol : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) firstV s ≤ MY1) :
    FirstTrialBounds Odd.design K160.target K160.firstCost :=
  firstTrial_D58 hrow hcol K160.first_budget_log2

/-- Bank K640 first-population contract. -/
def K640.firstTrial
    (hrow : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      firstRowFieldG (11 / 29) (3 / 29) (49 / 58) lamFirst (5 / 29) firstP firstV x ≤ MX1)
    (hcol : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) firstV s ≤ MY1) :
    FirstTrialBounds Odd.design K640.target K640.firstCost :=
  firstTrial_D58 hrow hcol K640.first_budget_log2

end

section
open Set OAI.InternalCatalan CatalanMeasure.Cert CatalanMeasure.G728
open CatalanMeasure.GenD.Analytic
/-- Bank K160 first-population contract, hypothesis-free. -/
def K160.firstTrialCert : FirstTrialBounds Odd.design K160.target K160.firstCost :=
  K160.firstTrial hrow_D58 hcol_D58

/-- Bank K640 first-population contract, hypothesis-free. -/
def K640.firstTrialCert : FirstTrialBounds Odd.design K640.target K640.firstCost :=
  K640.firstTrial hrow_D58 hcol_D58

end

section
open CatalanMeasure.Parametric
theorem circ_hwc160 : (52788 / 1000 : ℝ) < K160.rho - 58 * K160.secondCost := by
  norm_num [K160.rho, K160.secondCost, wcap]

theorem circ_hwc640 : (52788 / 1000 : ℝ) < K640.rho - 58 * K640.secondCost := by
  norm_num [K640.rho, K640.secondCost, wcap]

end

section
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan
open scoped Topology
/-- Decay rate of `Δ_N` implied by the bank K640 field target. -/
def tDelta640 : ℝ := (K640.target - Real.log 2 / 2) * 58 ^ 2

theorem eta_le640 : K640.eta + chi < tDelta640 - gD58 := by
  obtain ⟨hl, hh⟩ := log2_bounds
  unfold tDelta640 gD58
  norm_num [K640.eta, K640.etaRef, chi, chiRef, t, K640.target, lo, hi] at hl hh ⊢
  linarith

/-- Bank K640: `B = 590`. -/
theorem measure_590_of_delta_small
    (delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K640.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly Odd.design N)| ≤
          Real.exp (-((tDelta640 - ε) * (N : ℝ) ^ 2)))
    (c3 : C3) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design Odd.design
    { B := 590, Z := Znorm, w := 3 / 4, ρ := K640.rho, η := K640.eta + chi, κ := K640.kappa,
      δ := delta, pay := by rw [n0_sub_g0]; simpa [K640.B] using K640.pay_w,
      gD := gD58, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta640,
      delta_small := delta_small, eta_le := eta_le640, nonvanishing := nonvanishing_d58 c3 }
  simpa using h

end

section
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan Set CatalanMeasure.G728
open scoped Topology
section budgets
open Analytic

theorem K640.second_budget_gen {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K640.normCap + (1 - a) * K640.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K640.residualCap + t * nearCap ≤
        -K640.target + Real.log 2 / 2 + K640.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K640.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

end budgets

/-- Bank K640: `B = 590`, from the certificates. -/
theorem measure_590_of_certificates
    {g rc C wc : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (ha4 : 1 - (2 * g / (1 + g ^ 2)) ^ 2 ≤ 4 * (2 * g / (1 + g ^ 2)))
    (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * g / (1 + g ^ 2)) rc C wc)
    (hwc : wc < K640.rho - 58 * K640.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K640.target K640.firstCost)
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (MX MY : ℝ) (field_sum : MX + MY = K640.fieldCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ K640.normCap)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          u 1 * y ≤ nearCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      rowFieldG (11 / 29) (3 / 29) (39 / 29) u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, g ≤ |x| →
      Analytic.resFieldGen (53 / 58) u x ≤ K640.residualCap)
    :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have S : Analytic.SecondFieldCert Odd.design K640.target K640.residualCap nearCap
      K640.secondCost (fun x => g ≤ |x|) :=
    { u := u, v := v, hu := hu, hv := hv, MX := MX, MY := MY, normCap := K640.normCap,
      fieldCap := K640.fieldCap, near_sup := near_sup, norm_le := norm_le,
      field_sum := field_sum,
      row_sup := by
        rw [(Analytic.Instances.d58_row_weights).1, (Analytic.Instances.d58_row_weights).2.1,
          (Analytic.Instances.d58_row_weights).2.2]
        exact row_sup,
      column_sup := by
        rw [(Analytic.Instances.d58_column_weights).1, (Analytic.Instances.d58_column_weights).2]
        exact column_sup,
      residual_sup := fun x hx hg => by
        rw [Analytic.Instances.d58_gRes]; exact residual_sup x hx hg,
      budget := fun ha ht => K640.second_budget_gen ha ht }
  refine measure_590_of_delta_small ?_ C3.c3_d58
  intro ε hε
  exact Analytic.delta_small_of_certificates Odd.design_admissible hg0 hg1 ha4 hr1 hr2 hcirc
    (w := K640.rho - 58 * K640.secondCost) hwc F S
    (r := 58 * K640.secondCost) (by norm_num [Odd.design, K640.firstCost, K640.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta640; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring) ε hε


end

end
end D58
end CatalanMeasure.GenD
