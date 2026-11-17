/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P045.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P042
public import CatalanCore.Li2.Port.Unified.Modular.Base.DecayMediumAssembly
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P041
public import CatalanCore.Li2.Port.Unified.Modular.Base.IntegerFamily
public import CatalanCore.Li2.Port.Unified.Modular.Base.IntegralPolynomials
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P036
public import CatalanCore.Li2.Port.Unified.Modular.Base.OuterPrimeWindows

set_option backward.privateInPublic true

@[expose] public section

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial

/-- The actual parameter-family pole scalar at `-j`. -/
def parameterGamma (lam : ℚ) (n j : ℕ) : ℚ[X] :=
  C (CatalanCore.Li2.Port.Li2.rscale n (4*n) j * ((j:ℚ) * lam⁻¹^j)) *
    (X - C (CatalanCore.Li2.Port.Li2.parameterTau lam j))

lemma parameterGamma_eq_zero (lam : ℚ) {n j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j ≤ n) : parameterGamma lam n j = 0 := by
  simp [parameterGamma, CatalanCore.Li2.Port.Li2.rscale, CatalanCore.Li2.Port.Li2.D_eval_neg_of_le hj1 hjn]

/-- The original class weight remains valid for every parameter that is a
p-adic unit. The simple-pole value is controlled by the parameter moment. -/
theorem parameterGamma_GV (p : ℕ) [Fact p.Prime] (lam : ℚ)
    (hlam : CatalanCore.Li2.Port.Li2.VG p lam 0) (hinv : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ 0)
    {n j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ 4*n)
    (hK : 4*n < p^2) :
    CatalanCore.Li2.Port.Li2.GV p (parameterGamma lam n j) (CatalanCore.Li2.Port.Li2.wv n p j) := by
  by_cases hjn : j ≤ n
  · rw [parameterGamma_eq_zero lam hj1 hjn]
    exact CatalanCore.Li2.Port.Li2.GV.zero _
  · have hjn : n < j := by omega
    have hr : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.rscale n (4*n) j)
        (2 * ((j-1)/p : ℕ) - 3 * ((j-1-n)/p : ℕ) - ((4*n-j)/p : ℕ) : ℚ) :=
      CatalanCore.Li2.Port.Li2.VG.of_eq _ fun _ => by
        rw [CatalanCore.Li2.Port.Li2.rscale_val p hjn hjK hK]
        push_cast
        exact le_rfl
    have hjv := CatalanCore.Li2.Port.Li2.nat_VG_dvd p j (by omega)
    have hpow := hinv.pow j
    have hlog : Nat.log p (4*n) ≤ 1 := by
      rcases Nat.eq_zero_or_pos (4*n) with h0 | h0
      · simp [h0]
      · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hK)
    have hlogQ : ((Nat.log p (4*n) : ℕ) : ℚ) ≤ 1 := by
      exact_mod_cast hlog
    have ht : CatalanCore.Li2.Port.Li2.GV p (X - C (CatalanCore.Li2.Port.Li2.parameterTau lam j))
        (-(if p ≤ j then 2 else 0)) := by
      split_ifs with hpj
      · have hv := parameterTau_VG_log p lam hlam hjK
        have hv' : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.parameterTau lam j) (-2:ℚ) :=
          hv.mono (by linarith)
        exact (CatalanCore.Li2.Port.Li2.GV.X.mono (by norm_num)).sub (CatalanCore.Li2.Port.Li2.GV.C hv')
      · have hzero : Nat.log p j = 0 := Nat.log_of_lt (by omega)
        have hv : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.parameterTau lam j) 0 := by
          simpa [hzero] using! parameterTau_VG_log p lam hlam (le_refl j)
        simpa using! CatalanCore.Li2.Port.Li2.GV.X.sub (CatalanCore.Li2.Port.Li2.GV.C hv)
    have h := (CatalanCore.Li2.Port.Li2.GV.C (hr.mul (hjv.mul hpow))).mul ht
    unfold CatalanCore.Li2.Port.Li2.wv
    rw [if_neg (by omega)]
    refine h.mono (le_of_eq ?_)
    ring

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterGamma_GV

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial
open scoped BigOperators

/-- The parameter-family Hankel entry has the same rank-one nodes as the
original construction, with its actual parameter moment and pole values. -/
theorem parameter_hankel_entry (lam : ℚ) (n a b : ℕ) :
    ParameterFamily.numeratorFunctional lam (4*n)
      ((CatalanCore.Li2.Port.Li2.D n)^3 * X^(a+b)) =
      C (CatalanCore.Li2.Port.Li2.parameterU lam (CatalanCore.Li2.Port.Li2.polynomialPart n (a+b))) +
      ∑ j ∈ Finset.Icc 1 (4*n), parameterGamma lam n j *
        C ((-(j:ℚ))^a * (-(j:ℚ))^b) := by
  unfold ParameterFamily.numeratorFunctional
  have hq : (CatalanCore.Li2.Port.Li2.D n)^3 * X^(a+b) /ₘ CatalanCore.Li2.Port.Li2.D (4*n) =
      CatalanCore.Li2.Port.Li2.polynomialPart n (a+b) := by
    rw [CatalanCore.Li2.Port.Li2.polynomialPart, CatalanCore.Li2.Port.Li2.numerator, mul_comm]
  rw [hq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_mul, eval_pow, eval_pow, eval_X]
  unfold parameterGamma CatalanCore.Li2.Port.Li2.rscale CatalanCore.Li2.Port.Li2.eraseProd
  rw [show (CatalanCore.Li2.Port.Li2.D n).eval (-(j:ℚ)) ^ 3 * (-(j:ℚ))^(a+b) /
      ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ)) =
      (CatalanCore.Li2.Port.Li2.D n).eval (-(j:ℚ)) ^ 3 /
      (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))) *
        ((-(j:ℚ))^a * (-(j:ℚ))^b) by rw [pow_add]; ring]
  simp only [map_mul, map_pow, map_neg]
  ring

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_hankel_entry

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial

lemma parameter_derivative_GV_integral (p : ℕ) [Fact p.Prime]
    {F : ℚ[X]} (hF : CatalanCore.Li2.Port.Li2.GV p F 0) : CatalanCore.Li2.Port.Li2.GV p F.derivative 0 := by
  intro k
  rw [coeff_derivative]
  simpa using! (hF (k+1)).mul (CatalanCore.Li2.Port.Li2.VG.natCast (p := p) (k+1))

/-- At a parameter with integral Newton moments, U_X preserves every
p-integral polynomial, with no logarithmic degree loss. -/
theorem parameterU_GV_integral (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0)
    {q : ℚ[X]} (hq : CatalanCore.Li2.Port.Li2.GV p q 0) :
    CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.parameterU lam q) 0 := by
  unfold CatalanCore.Li2.Port.Li2.parameterU
  have hXq : CatalanCore.Li2.Port.Li2.GV p (X*q) 0 := by
    simpa using! (CatalanCore.Li2.Port.Li2.GV.X.mul hq)
  have hder := parameter_derivative_GV_integral p hXq
  exact parameterG_VG_of_integral_ratio p lam h1 hratio
    (le_refl _) 0 (fun i _ => CatalanCore.Li2.Port.Li2.VG.eval hder (CatalanCore.Li2.Port.Li2.VG.natCast i))

/-- The polynomial-part row in the actual parameter Hankel matrix is
p-integral, even when its degree exceeds p. -/
theorem parameter_polynomialPartMoment_GV (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0) (n k : ℕ) :
    CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.parameterU lam (CatalanCore.Li2.Port.Li2.polynomialPart n k)) 0 :=
  parameterU_GV_integral p lam h1 hratio (CatalanCore.Li2.Port.Li2.polynomialPart_GV p n k)

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameterU_GV_integral
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_polynomialPartMoment_GV

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial
open scoped BigOperators

/-- The actual parameter-family raw determinant obeys the full class-slot
bound, provided the parameter is a p-adic unit and its Newton ratio is integral. -/
theorem parameter_raw_Q_GV (p : ℕ) [hp : Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0)
    (hlam : CatalanCore.Li2.Port.Li2.VG p lam 0) (hinv : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ 0)
    (n : ℕ) (hK : 4*n < p^2) :
    CatalanCore.Li2.Port.Li2.GV p (ParameterFamily.Q lam n)
      (∑ c : Fin p, ∑ k ∈ Finset.range (CatalanCore.Li2.Port.Li2.Ccl p (4*n) c),
        min (CatalanCore.Li2.Port.Li2.wv n p (CatalanCore.Li2.Port.Li2.jn p (4*n) c k) + 2 * k) 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hQ : ParameterFamily.Q lam n = (Matrix.of fun a b : Fin (2*n) =>
      C (CatalanCore.Li2.Port.Li2.parameterU lam (CatalanCore.Li2.Port.Li2.polynomialPart n (a+b))) +
      ∑ c : Fin p, ∑ t ∈ Finset.range (CatalanCore.Li2.Port.Li2.Ccl p (4*n) c),
        parameterGamma lam n (CatalanCore.Li2.Port.Li2.jn p (4*n) c t) *
          C ((-(CatalanCore.Li2.Port.Li2.jn p (4*n) c t : ℚ))^(a:ℕ) *
             (-(CatalanCore.Li2.Port.Li2.jn p (4*n) c t : ℚ))^(b:ℕ))).det := by
    rw [ParameterFamily.Q, ← ParameterFamily.hankelFor_original]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro a b
    change ParameterFamily.numeratorFunctional lam (4*n)
      ((CatalanCore.Li2.Port.Li2.D n)^3 * X^((a:ℕ)+(b:ℕ))) = _
    rw [parameter_hankel_entry,
      CatalanCore.Li2.Port.Li2.regroup p (4*n) hp0,
      ← Fin.sum_univ_eq_sum_range
        (fun c => ∑ t ∈ Finset.range (CatalanCore.Li2.Port.Li2.Ccl p (4*n) c),
          parameterGamma lam n (CatalanCore.Li2.Port.Li2.jn p (4*n) c t) *
          C ((-(CatalanCore.Li2.Port.Li2.jn p (4*n) c t : ℚ))^(a:ℕ) *
             (-(CatalanCore.Li2.Port.Li2.jn p (4*n) c t : ℚ))^(b:ℕ))) p]
    rfl
  rw [hQ]
  apply CatalanCore.Li2.Port.Li2.rank_one_GV
    (fun c : Fin p => CatalanCore.Li2.Port.Li2.Ccl p (4*n) c)
    (fun c t => -(CatalanCore.Li2.Port.Li2.jn p (4*n) c t : ℚ))
    (fun c t => parameterGamma lam n (CatalanCore.Li2.Port.Li2.jn p (4*n) c t))
    p (fun c t => CatalanCore.Li2.Port.Li2.wv n p (CatalanCore.Li2.Port.Li2.jn p (4*n) c t))
  · intro a b
    exact CatalanCore.Li2.Port.Li2.GV.C (parameter_polynomialPartMoment_GV p lam h1 hratio n _)
  · intro c t
    exact (CatalanCore.Li2.Port.Li2.VG.natCast _).neg
  · intro c s t hs ht hst
    have hpv : CatalanCore.Li2.Port.Li2.VG p (p:ℚ) 1 := by
      right
      rw [padicValRat.self hp.out.one_lt]
      norm_num
    have key : ∀ u v : ℕ, u ≤ v → v < CatalanCore.Li2.Port.Li2.Ccl p (4*n) c →
        (CatalanCore.Li2.Port.Li2.jn p (4*n) c u : ℚ) =
        CatalanCore.Li2.Port.Li2.jn p (4*n) c v + (p:ℚ) * ((v-u:ℕ):ℚ) := by
      intro u v huv hv
      have hN : CatalanCore.Li2.Port.Li2.jn p (4*n) c u =
          CatalanCore.Li2.Port.Li2.jn p (4*n) c v + p * (v-u) := by
        unfold CatalanCore.Li2.Port.Li2.jn
        rw [show CatalanCore.Li2.Port.Li2.Ccl p (4*n) c - 1 - u =
          (CatalanCore.Li2.Port.Li2.Ccl p (4*n) c - 1 - v) + (v-u) by omega, Nat.mul_add]
        ring
      rw [hN]
      push_cast
      ring
    rcases lt_or_gt_of_ne hst with h | h
    · rw [key s t h.le ht]
      have := hpv.mul (CatalanCore.Li2.Port.Li2.VG.natCast (p := p) (t-s))
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using! this
    · rw [key t s h.le hs]
      have := (hpv.mul (CatalanCore.Li2.Port.Li2.VG.natCast (p := p) (s-t))).neg
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using! this
  · intro c t ht
    exact parameterGamma_GV p lam hlam hinv
      (by unfold CatalanCore.Li2.Port.Li2.jn; omega)
      (CatalanCore.Li2.Port.Li2.jn_le p (4*n) hp0 ht) hK
  · intro c s t hst ht
    by_cases hjt : CatalanCore.Li2.Port.Li2.jn p (4*n) c t ≤ n
    · have := CatalanCore.Li2.Port.Li2.wv_le_big (n := n) (p := p)
        (CatalanCore.Li2.Port.Li2.jn_le p (4*n) hp0 (lt_of_le_of_lt hst ht))
      simp only [CatalanCore.Li2.Port.Li2.wv, if_pos hjt]
      exact this
    · have e : CatalanCore.Li2.Port.Li2.jn p (4*n) c s =
          CatalanCore.Li2.Port.Li2.jn p (4*n) c t + p * (t-s) := by
        unfold CatalanCore.Li2.Port.Li2.jn
        rw [show CatalanCore.Li2.Port.Li2.Ccl p (4*n) c - 1 - s =
          (CatalanCore.Li2.Port.Li2.Ccl p (4*n) c - 1 - t) + (t-s) by omega, Nat.mul_add]
        ring
      rw [e]
      exact CatalanCore.Li2.Port.Li2.wv_step hp0 (by omega : n < CatalanCore.Li2.Port.Li2.jn p (4*n) c t)
        (e ▸ CatalanCore.Li2.Port.Li2.jn_le p (4*n) hp0 (lt_of_le_of_lt hst ht))

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_raw_Q_GV

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open CatalanCore.Li2.Port.Unified.ParameterFamily Polynomial

/-- The five sharp outer affine rows are precisely the old class-weight
formula. This equality is parameter-independent. -/
theorem outerRaw_norm_eq_outerPrimeBound (p n : ℕ)
    (hnp : n < p) (hpn : p ≤ 4*n) :
    CatalanCore.Li2.Port.Li2.outerRawBound p n + CatalanCore.Li2.Port.Li2.normVal p n = CatalanCore.Li2.Port.Li2.outerPrimeBound p n := by
  unfold CatalanCore.Li2.Port.Li2.outerPrimeBound
  split_ifs with h1 h2 h3 h4
  · have hL : (4*n)/p = 3 := CatalanCore.Li2.Port.Li2.div_eq_of_bounds (by omega) (by omega)
    rw [CatalanCore.Li2.Port.Li2.outerRawBound_w1 hnp h1,
      CatalanCore.Li2.Port.Li2.normVal_outer_low hnp (by omega) hL]
    ring
  · have hL : (4*n)/p = 2 := CatalanCore.Li2.Port.Li2.div_eq_of_bounds (by omega) (by omega)
    rw [CatalanCore.Li2.Port.Li2.outerRawBound_w2 hnp (by omega) h2,
      CatalanCore.Li2.Port.Li2.normVal_outer_low hnp (by omega) hL]
    ring
  · have hL : (4*n)/p = 2 := CatalanCore.Li2.Port.Li2.div_eq_of_bounds (by omega) (by omega)
    rw [CatalanCore.Li2.Port.Li2.outerRawBound_w3 hnp (by omega) h3,
      CatalanCore.Li2.Port.Li2.normVal_outer_low hnp h3 hL]
    ring
  · have hL : (4*n)/p = 1 := CatalanCore.Li2.Port.Li2.div_eq_of_bounds (by omega) (by omega)
    rw [CatalanCore.Li2.Port.Li2.outerRawBound_w4 hnp (by omega) h4,
      CatalanCore.Li2.Port.Li2.normVal_outer_high hnp (by omega) hL]
    ring
  · have hL : (4*n)/p = 1 := CatalanCore.Li2.Port.Li2.div_eq_of_bounds (by omega) (by omega)
    rw [CatalanCore.Li2.Port.Li2.outerRawBound_w5 hnp (by omega) hpn,
      CatalanCore.Li2.Port.Li2.normVal_outer_high hnp (by omega) hL]
    ring

/-- To complete the outer-prime theorem, the parameter family needs the
sharp raw class-slot estimate, not merely the normalized Gram floor. -/
theorem parameter_Qtilde_GV_outer_of_raw (lam : ℚ) (n p : ℕ)
    [Fact p.Prime] (hnp : n < p) (hpn : p ≤ 4*n)
    (hraw : CatalanCore.Li2.Port.Li2.GV p (Qtilde lam n)
      (CatalanCore.Li2.Port.Li2.outerRawBound p n + CatalanCore.Li2.Port.Li2.normVal p n)) :
    CatalanCore.Li2.Port.Li2.GV p (Qtilde lam n) (CatalanCore.Li2.Port.Li2.outerPrimeBound p n) := by
  rw [← outerRaw_norm_eq_outerPrimeBound p n hnp hpn]
  exact hraw

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.outerRaw_norm_eq_outerPrimeBound
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_Qtilde_GV_outer_of_raw

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open Polynomial
open scoped BigOperators

/-- Refined parameter-family Gauss bound, including the exact normalization
valuation and removal of the cancelled class nodes. -/
theorem parameter_Qtilde_GV_prime_refined (p : ℕ) [hp : Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0)
    (hlam : CatalanCore.Li2.Port.Li2.VG p lam 0) (hinv : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ 0)
    (n : ℕ) (hK : 4*n < p^2) :
    CatalanCore.Li2.Port.Li2.GV p (ParameterFamily.Qtilde lam n)
      (∑ c : Fin p, ∑ k ∈ Finset.range
        (CatalanCore.Li2.Port.Li2.Ccl p (4*n) c - CatalanCore.Li2.Port.Li2.Ncl p n c),
        min (CatalanCore.Li2.Port.Li2.Wslot p n c k + 2*k) 0 + CatalanCore.Li2.Port.Li2.normVal p n) := by
  have hp0 := hp.out.pos
  have hraw := parameter_raw_Q_GV p lam h1 hratio hlam hinv n hK
  have hsc : CatalanCore.Li2.Port.Li2.VG p (CatalanCore.Li2.Port.Li2.Sn n ^ (2*n) / CatalanCore.Li2.Port.Li2.Fn n)
      (CatalanCore.Li2.Port.Li2.normVal p n) :=
    CatalanCore.Li2.Port.Li2.VG.of_eq _ fun _ => by rw [CatalanCore.Li2.Port.Li2.normScale_val p hK]
  have h := (CatalanCore.Li2.Port.Li2.GV.C hsc).mul hraw
  rw [ParameterFamily.Qtilde]
  refine h.mono ?_
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun (c : Fin p) _ =>
    CatalanCore.Li2.Port.Li2.class_sum_ge' (p := p) (n := n) (c := c) hp0 c.isLt
  linarith

/-- The actual parameter family has the sharp five-window bound at every
outer prime at least five. -/
theorem parameter_Qtilde_GV_outer (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : CatalanCore.Li2.Port.Li2.VG p (lam/(1-lam)) 0)
    (hlam : CatalanCore.Li2.Port.Li2.VG p lam 0) (hinv : CatalanCore.Li2.Port.Li2.VG p lam⁻¹ 0)
    {n : ℕ} (hnp : n < p) (hpn : p ≤ 4*n) :
    CatalanCore.Li2.Port.Li2.GV p (ParameterFamily.Qtilde lam n)
      (CatalanCore.Li2.Port.Li2.outerPrimeBound p n) := by
  have hK : 4*n < p^2 := CatalanCore.Li2.Port.Li2.outer_prime_square hp5 hnp
  have h := parameter_Qtilde_GV_prime_refined p lam h1 hratio hlam hinv n hK
  change CatalanCore.Li2.Port.Li2.GV p (ParameterFamily.Qtilde lam n)
    (CatalanCore.Li2.Port.Li2.outerRawBound p n + CatalanCore.Li2.Port.Li2.normVal p n) at h
  exact parameter_Qtilde_GV_outer_of_raw lam n p hnp hpn h

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.parameter_Qtilde_GV_outer

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open CatalanCore.Li2.Port.Unified.ParameterFamily CatalanCore.Li2.Port.Unified.Instances.PosHalf
open Filter

/-- Sharp actual outer-prime Gauss bound at the positive-half parameter. -/
theorem posHalf_outer_GV (n p : ℕ) (hn : 4 ≤ n)
    (hp : p.Prime) (hnp : n < p) (hpn : p ≤ 4*n) :
    CatalanCore.Li2.Port.Li2.GV p (Instances.PosHalf.Qtilde n)
      (CatalanCore.Li2.Port.Li2.outerPrimeBound p n) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by omega
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hp1 : ¬ p ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    omega
  have hu := inverseParameter_unit (p := p) 2 (by norm_num) hp2
  have hlam : CatalanCore.Li2.Port.Li2.VG p lambda 0 := by
    rw [lambda_eq_inverse]
    right
    rw [hu.2]
    norm_num
  have hinv : CatalanCore.Li2.Port.Li2.VG p lambda⁻¹ 0 := by
    rw [lambda_eq_inverse]
    exact CatalanCore.Li2.Port.Li2.rational_unit_inverse_VG (inverseParameter 2) hu.1 hu.2
  have hratio : CatalanCore.Li2.Port.Li2.VG p (lambda/(1-lambda)) 0 := by
    rw [lambda_eq_inverse]
    exact inverseParameter_moment_integral 2 (by norm_num) hp2 hp1
  exact parameter_Qtilde_GV_outer p hp5 lambda lambda_ne_one
    hratio hlam hinv hnp hpn

/-- The existing outer five-window PNT applies to the actual positive-half
primitive determinant, with no assumed per-prime Gauss bounds. -/
theorem posHalf_outer_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      ((7/2:ℝ)-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ Finset.Ioc n (4*n),
          if p.Prime then
            ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
          else 0 := by
  filter_upwards [outerWindowSum_eventually_lower ε hε,
    eventually_ge_atTop (4:ℕ)] with n hmass hn
  intro hne
  exact hmass.trans (parameter_outerWindowSum_le_valuation lambda n hne
    (fun p hpI hp => by
      obtain ⟨hnp, hpn⟩ := Finset.mem_Ioc.mp hpI
      exact posHalf_outer_GV n p hn hp hnp hpn))

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.posHalf_outer_GV
#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.posHalf_outer_eventually

end


end
