module

public import CatalanCore.Uniform.Decay.Jet.Gram
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
open scoped Polynomial
namespace CatalanCore.Uniform.Decay.Jet

/-! Balanced rational simple parts are grouped before the bilateral sum. -/

noncomputable def balancedPoleTerm {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (s : ι → ℝ) (z : ℂ) (n : ℤ) : ℂ :=
  -∑ i, c i / (z + n + (s i : ℂ))

theorem balancedPoleTerm_pair {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (s : ι → ℝ) (hc : ∑ i, c i = 0) (z d : ℂ) (n : ℤ) :
    balancedPoleTerm c s z n =
      -∑ i, c i * (1 / (z + n + (s i : ℂ)) - 1 / (z + n + d)) := by
  have h : ∑ i, c i / (z + n + d) = 0 := by rw [← Finset.sum_div, hc, zero_div]
  simp only [balancedPoleTerm, mul_sub, Finset.sum_sub_distrib, mul_one_div, h, sub_zero]

theorem summable_balancedPoleTerm {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (s : ι → ℝ) (hc : ∑ i, c i = 0) (z : ℂ) :
    Summable (balancedPoleTerm c s z) := by
  have hp : ∀ i, Summable fun n : ℤ => c i *
      (1 / (z + n + (s i : ℂ)) - 1 / (z + n + ((0 : ℝ) : ℂ))) := by
    intro i
    exact (CatalanCore.Decay.summable_pair_int z (s i) 0).mul_left (c i)
  apply ((summable_sum (s := Finset.univ) fun i _ => hp i).neg).congr
  intro n
  rw [balancedPoleTerm_pair c s hc z 0 n]
  simp only [Complex.ofReal_zero]

theorem balancedPoleSeries_eq_cot {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (s : ι → ℝ) (hc : ∑ i, c i = 0) {z : ℂ}
    (hz : ∀ i, z + (s i : ℂ) ∈ Complex.integerComplement) :
    (∑' n : ℤ, balancedPoleTerm c s z n) =
      -∑ i, c i * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ)))) := by
  have hs := summable_balancedPoleTerm c s hc z
  have inj1 : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b h
    exact_mod_cast (add_right_cancel h)
  have inj2 : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h
    exact_mod_cast (add_right_cancel (neg_injective h))
  have hs1 := hs.comp_injective inj1
  have hs2 := hs.comp_injective inj2
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have hT : ∀ i, HasSum (fun n : ℕ => (1 / ((z + (s i : ℂ)) - (n + 1)) +
      1 / ((z + (s i : ℂ)) + (n + 1)) : ℂ))
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ))) - 1 / (z + (s i : ℂ))) := by
    intro i
    have h := (summable_cotTerm (hz i)).hasSum
    rw [← cot_series_rep' (hz i)] at h
    exact h
  have hsum := (hasSum_sum (s := Finset.univ) (fun i _ => (hT i).mul_left (c i))).neg
  have hp : ∀ n : ℕ, balancedPoleTerm c s z ((n : ℤ) + 1) +
      balancedPoleTerm c s z (-((n : ℤ) + 1)) =
      -∑ i, c i * (1 / ((z + (s i : ℂ)) - (n + 1)) +
        1 / ((z + (s i : ℂ)) + (n + 1))) := by
    intro n
    unfold balancedPoleTerm
    rw [← neg_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h3 := hs1.tsum_add hs2
  have hfun : (fun n : ℕ => balancedPoleTerm c s z ((n : ℤ) + 1) +
      balancedPoleTerm c s z (-((n : ℤ) + 1))) = fun n : ℕ =>
      -∑ i, c i * (1 / ((z + (s i : ℂ)) - (n + 1)) +
        1 / ((z + (s i : ℂ)) + (n + 1))) := by
    funext n; exact hp n
  simp only [Function.comp_apply] at h3
  rw [hfun] at h3
  rw [hsum.tsum_eq] at h3
  have e0 : balancedPoleTerm c s z 0 = -∑ i, c i * (1 / (z + (s i : ℂ))) := by
    simp only [balancedPoleTerm, Int.cast_zero, add_zero, mul_one_div]
  rw [show (∑' n : ℕ, balancedPoleTerm c s z ((n : ℤ) + 1)) + balancedPoleTerm c s z 0 +
      (∑' n : ℕ, balancedPoleTerm c s z (-((n : ℤ) + 1))) =
      ((∑' n : ℕ, balancedPoleTerm c s z ((n : ℤ) + 1)) +
        (∑' n : ℕ, balancedPoleTerm c s z (-((n : ℤ) + 1)))) + balancedPoleTerm c s z 0 by ring,
    ← h3, e0]
  simp only [mul_sub, Finset.sum_sub_distrib, neg_sub, mul_one_div]
  ring

noncomputable def higherPoleSeries (j : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, 1 / (z + n) ^ j

theorem summable_higherPoleSeries (j : ℕ) (hj : 2 ≤ j) (z : ℂ) :
    Summable (fun n : ℤ => 1 / (z + n) ^ j) := by
  have h := EisensteinSeries.linear_right_summable z 1 (k := j) (by exact_mod_cast hj)
  apply h.congr
  intro n
  simp [one_div]

/-! Normalized cotangent derivative polynomials. Their rational recurrence
contains the factorial normalization: P₀=1, P₁=X, P₂=X²+1/3. -/
noncomputable def cotPolePolynomial : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => Polynomial.C ((n + 2 : ℚ)⁻¹) *
      ((Polynomial.X ^ 2 + 1) * (cotPolePolynomial n).derivative +
        2 * Polynomial.X * cotPolePolynomial n)

noncomputable def higherPoleClosed (n : ℕ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (n + 2) *
    (cotPolePolynomial n).eval₂ (algebraMap ℚ ℂ) (Complex.cot ((Real.pi : ℂ) * z)) /
      Complex.sin ((Real.pi : ℂ) * z) ^ 2

theorem higherPoleClosed_conj (n : ℕ) (z : ℂ) :
    higherPoleClosed n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (higherPoleClosed n z) := by
  have hmap : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := by
    ext q
    simp
  have he := Polynomial.hom_eval₂ (cotPolePolynomial n) (algebraMap ℚ ℂ)
    (starRingEnd ℂ) (Complex.cot ((Real.pi : ℂ) * z))
  rw [hmap] at he
  simp only [higherPoleClosed, map_div₀, map_mul, map_pow, Complex.conj_ofReal,
    ← Complex.sin_conj, ← Complex.cot_conj] at he ⊢
  rw [he]

theorem hasDerivAt_cot_pi {z : ℂ} (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    HasDerivAt (fun w : ℂ => Complex.cot ((Real.pi : ℂ) * w))
      (-(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) ^ 2) z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd := (JetFrame.hasDerivAt_pi_cot hz).const_mul ((Real.pi : ℂ)⁻¹)
  have he : (fun w : ℂ => (Real.pi : ℂ)⁻¹ *
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w))) =
      fun w : ℂ => Complex.cot ((Real.pi : ℂ) * w) := by
    funext w
    rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  rw [he] at hd
  exact hd.congr_deriv (by field_simp <;> ring)

theorem hasDerivAt_cot_polynomial (P : ℚ[X]) {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    HasDerivAt
      (fun w : ℂ => P.eval₂ (algebraMap ℚ ℂ) (Complex.cot ((Real.pi : ℂ) * w)) /
        Complex.sin ((Real.pi : ℂ) * w) ^ 2)
      (-(Real.pi : ℂ) *
        (((Polynomial.X ^ 2 + 1) * P.derivative + 2 * Polynomial.X * P).eval₂
          (algebraMap ℚ ℂ) (Complex.cot ((Real.pi : ℂ) * z))) /
          Complex.sin ((Real.pi : ℂ) * z) ^ 2) z := by
  have hc := hasDerivAt_cot_pi hz
  have hp := (P.hasDerivAt_aeval (Complex.cot ((Real.pi : ℂ) * z))).comp z hc
  simp only [Polynomial.aeval_def] at hp
  have hs := (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).csin).pow 2
  have hd := hp.div hs (pow_ne_zero 2 hz)
  apply hd.congr_deriv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    Complex.cot_eq_cos_div_sin, id_eq, Pi.pow_apply, Function.comp_apply] 
  have ht := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z)
  field_simp
  linear_combination P.derivative.eval₂ (algebraMap ℚ ℂ) (Complex.cos ((Real.pi : ℂ) * z) /
      Complex.sin ((Real.pi : ℂ) * z)) * ht

theorem hasDerivAt_higherPoleClosed (n : ℕ) {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    HasDerivAt (higherPoleClosed n)
      (-((n + 2 : ℕ) : ℂ) * higherPoleClosed (n + 1) z) z := by
  have hd := (hasDerivAt_cot_polynomial (cotPolePolynomial n) hz).const_mul
    ((Real.pi : ℂ) ^ (n + 2))
  have he : higherPoleClosed n = (fun w : ℂ => (Real.pi : ℂ) ^ (n + 2) *
      ((cotPolePolynomial n).eval₂ (algebraMap ℚ ℂ) (Complex.cot ((Real.pi : ℂ) * w)) /
        Complex.sin ((Real.pi : ℂ) * w) ^ 2)) := by
    funext w
    simp only [higherPoleClosed, mul_div_assoc]
  rw [he]
  apply hd.congr_deriv
  simp only [higherPoleClosed, cotPolePolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, map_inv₀, map_add, map_natCast, map_ofNat]
  have hn : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
  push_cast
  have hn' : (2 + (n : ℂ)) ≠ 0 := by exact_mod_cast (by omega : 2 + n ≠ 0)
  field_simp [hn']
  ring_nf
  field_simp [hn']
  <;> ring

noncomputable def polePolynomialMajorant (P : ℚ[X]) (t : ℝ) : ℝ :=
  ∑ k ∈ P.support, ‖(P.coeff k : ℂ)‖ * t ^ k

theorem polePolynomialMajorant_nonneg (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ polePolynomialMajorant P t := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (pow_nonneg ht _)

theorem norm_eval₂_le_polePolynomialMajorant (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t)
    {w : ℂ} (hw : ‖w‖ ≤ t) :
    ‖P.eval₂ (algebraMap ℚ ℂ) w‖ ≤ polePolynomialMajorant P t := by
  rw [Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum polePolynomialMajorant
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw k) (norm_nonneg _)

theorem norm_cot_pi_le_of_sin_guard {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hsin : κ * Real.exp (Real.pi * |z.im|) ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖Complex.cot ((Real.pi : ℂ) * z)‖ ≤ 1 + κ⁻¹ := by
  have ht : 0 ≤ Real.pi * |z.im| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  have hsn : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ :=
    lt_of_lt_of_le (mul_pos hκ (Real.exp_pos _)) hsin
  have hne := norm_pos_iff.mp hsn
  have hr : Real.exp (-(Real.pi * |z.im|)) /
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ κ⁻¹ := by
    calc
      _ ≤ Real.exp (-(Real.pi * |z.im|)) / (κ * Real.exp (Real.pi * |z.im|)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hsin
      _ ≤ Real.exp (Real.pi * |z.im|) / (κ * Real.exp (Real.pi * |z.im|)) :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = _ := by field_simp
  by_cases hy : 0 ≤ z.im
  · have he := CatalanCore.Decay.norm_cot_add_I z hne
    rw [← abs_of_nonneg hy] at he
    have hb : ‖Complex.cot ((Real.pi : ℂ) * z) + I‖ ≤ κ⁻¹ := by rw [he]; exact hr
    have hn := norm_sub_le (Complex.cot ((Real.pi : ℂ) * z) + I) I
    simp only [add_sub_cancel_right, Complex.norm_I] at hn
    linarith
  · have he := CatalanCore.Decay.norm_cot_sub_I z hne
    have hi : Real.pi * z.im = -(Real.pi * |z.im|) := by rw [abs_of_neg (lt_of_not_ge hy)]; ring
    rw [hi] at he
    have hb : ‖Complex.cot ((Real.pi : ℂ) * z) - I‖ ≤ κ⁻¹ := by rw [he]; exact hr
    have hn := norm_add_le (Complex.cot ((Real.pi : ℂ) * z) - I) I
    simp only [sub_add_cancel, Complex.norm_I] at hn
    linarith

noncomputable def higherPoleK (n : ℕ) (κ : ℝ) : ℝ :=
  Real.pi ^ (n + 2) * polePolynomialMajorant (cotPolePolynomial n) (1 + κ⁻¹) / κ ^ 2

theorem higherPoleK_nonneg (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ higherPoleK n κ := by
  exact div_nonneg (mul_nonneg (pow_nonneg Real.pi_pos.le _)
    (polePolynomialMajorant_nonneg _ (by positivity))) (sq_nonneg _)

theorem norm_higherPoleClosed_le (n : ℕ) {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hsin : κ * Real.exp (Real.pi * |z.im|) ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖) :
    ‖higherPoleClosed n z‖ ≤ higherPoleK n κ * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hP := norm_eval₂_le_polePolynomialMajorant (cotPolePolynomial n)
    (by positivity : (0 : ℝ) ≤ 1 + κ⁻¹) (norm_cot_pi_le_of_sin_guard hκ hsin)
  have hpos : 0 < κ * Real.exp (Real.pi * |z.im|) := by positivity
  have hden : (κ * Real.exp (Real.pi * |z.im|)) ^ 2 ≤
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2 := pow_le_pow_left₀ hpos.le hsin 2
  have he : Real.exp (-(2 * Real.pi * |z.im|)) =
      (Real.exp (Real.pi * |z.im|))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [higherPoleClosed, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi ^ (n + 2) * polePolynomialMajorant (cotPolePolynomial n) (1 + κ⁻¹) /
        ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by positivity)) (sq_nonneg _)
    _ ≤ Real.pi ^ (n + 2) * polePolynomialMajorant (cotPolePolynomial n) (1 + κ⁻¹) /
        (κ * Real.exp (Real.pi * |z.im|)) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg (by positivity)
        (polePolynomialMajorant_nonneg _ (by positivity))) (by positivity) hden
    _ = _ := by rw [he]; unfold higherPoleK; field_simp

theorem iteratedDeriv_pi_cot_closed (n : ℕ) {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    iteratedDeriv (n + 1) (fun w : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w)) z =
      ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ)) * higherPoleClosed n z := by
  induction n generalizing z with
  | zero =>
      rw [iteratedDeriv_one, (JetFrame.hasDerivAt_pi_cot hz).deriv]
      simp [higherPoleClosed, cotPolePolynomial]
  | succ n ih =>
      have hc : Continuous (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) := by fun_prop
      have hev : (iteratedDeriv (n + 1) fun w : ℂ =>
          (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w)) =ᶠ[nhds z]
          fun w : ℂ => ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ)) * higherPoleClosed n w := by
        filter_upwards [(hc.tendsto z).eventually (isOpen_ne.mem_nhds hz)] with w hw
        exact ih hw
      rw [iteratedDeriv_succ, hev.deriv_eq, deriv_const_mul_field,
        (hasDerivAt_higherPoleClosed n hz).deriv]
      simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      ring

theorem higherPoleSeries_eq_closed_upper (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    higherPoleSeries (n + 2) z = higherPoleClosed n z := by
  have hmem : z ∈ UpperHalfPlane.upperHalfPlaneSet := hz
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Complex.sin_eq_zero_iff.mp h0
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have he : z = (a : ℂ) := by
      apply mul_left_cancel₀ hpi
      rw [ha]
      ring
    rw [he] at hz
    simpa using hz
  have hs := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
    (k := n + 1) (by omega) hmem
  rw [iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hmem] at hs
  have hd := iteratedDeriv_pi_cot_closed n hsin
  apply mul_left_cancel₀ (show ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ)) ≠ 0 by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast Nat.factorial_ne_zero (n + 1))
  exact hs.symm.trans hd

theorem higherPoleSeries_conj (j : ℕ) (z : ℂ) :
    higherPoleSeries j ((starRingEnd ℂ) z) = (starRingEnd ℂ) (higherPoleSeries j z) := by
  unfold higherPoleSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp only [map_div₀, map_one, map_pow, map_add, map_intCast]

theorem higherPoleSeries_eq_closed (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    higherPoleSeries (n + 2) z = higherPoleClosed n z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hh : 0 < ((starRingEnd ℂ) z).im := by simpa using h
    have he := higherPoleSeries_eq_closed_upper n hh
    rw [higherPoleSeries_conj, higherPoleClosed_conj] at he
    have he' := congrArg (starRingEnd ℂ) he
    simpa using he'
  · exact higherPoleSeries_eq_closed_upper n h

noncomputable def balancedPoleClosed {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (s : ι → ℝ) (z : ℂ) : ℂ :=
  -∑ i, c i * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ))))

theorem norm_balancedPoleClosed_le {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (s : ι → ℝ) (hc : ∑ i, c i = 0)
    {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hsin : ∀ i, κ * Real.exp (Real.pi * |z.im|) ≤
      ‖Complex.sin ((Real.pi : ℂ) * (z + (s i : ℂ)))‖) :
    ‖balancedPoleClosed c s z‖ ≤
      (Real.pi * (∑ i, ‖c i‖) / κ) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hne : ∀ i, Complex.sin ((Real.pi : ℂ) * (z + (s i : ℂ))) ≠ 0 := by
    intro i
    exact norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hκ (Real.exp_pos _)) (hsin i))
  have hr : ∀ i, Real.exp (-(Real.pi * |z.im|)) /
      ‖Complex.sin ((Real.pi : ℂ) * (z + (s i : ℂ)))‖ ≤
      Real.exp (-(2 * Real.pi * |z.im|)) / κ := by
    intro i
    calc
      _ ≤ Real.exp (-(Real.pi * |z.im|)) /
          (κ * Real.exp (Real.pi * |z.im|)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (hsin i)
      _ = _ := by
        rw [show -(2 * Real.pi * |z.im|) = -(Real.pi * |z.im|) + -(Real.pi * |z.im|) by ring,
          Real.exp_add, Real.exp_neg (Real.pi * |z.im|)]
        field_simp
  have hJ : ∃ J : ℂ, ∀ i, ‖Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ))) - J‖ ≤
      Real.exp (-(2 * Real.pi * |z.im|)) / κ := by
    by_cases hy : 0 ≤ z.im
    · refine ⟨-I, fun i => ?_⟩
      rw [sub_neg_eq_add, CatalanCore.Decay.norm_cot_add_I _ (hne i)]
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero, abs_of_nonneg hy] using hr i
    · refine ⟨I, fun i => ?_⟩
      rw [CatalanCore.Decay.norm_cot_sub_I _ (hne i)]
      have hi : Real.pi * z.im = -(Real.pi * |z.im|) := by rw [abs_of_neg (lt_of_not_ge hy)]; ring
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero, hi] using hr i
  obtain ⟨J, hJ⟩ := hJ
  have he : ∑ i, c i * Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ))) =
      ∑ i, c i * (Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ))) - J) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc, zero_mul, sub_zero]
  have hb : ‖∑ i, c i * Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ)))‖ ≤
      (∑ i, ‖c i‖) * (Real.exp (-(2 * Real.pi * |z.im|)) / κ) := by
    rw [he, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hJ i) (norm_nonneg _)
  have he' : balancedPoleClosed c s z = -(Real.pi : ℂ) *
      ∑ i, c i * Complex.cot ((Real.pi : ℂ) * (z + (s i : ℂ))) := by
    unfold balancedPoleClosed
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he', norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact (mul_le_mul_of_nonneg_left hb Real.pi_pos.le).trans_eq (by ring)


#print axioms summable_balancedPoleTerm
#print axioms balancedPoleSeries_eq_cot
#print axioms summable_higherPoleSeries
#print axioms higherPoleClosed_conj
#print axioms hasDerivAt_higherPoleClosed
#print axioms norm_higherPoleClosed_le
#print axioms higherPoleSeries_eq_closed
#print axioms norm_balancedPoleClosed_le

end CatalanCore.Uniform.Decay.Jet
