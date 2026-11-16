module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-!
# Polynomial sup versus `L²` on an interval (ledger ZR03, generic)

For a real polynomial `P` of degree `< h` and a point `t₀ = -u²` to the left of `[a, b]`:

  `P(t₀)² ≤ h² exp(2 h arcosh Y) / (b - a) · ∫_a^b P²`,   `Y = (2u² + a + b)/(b - a)`.

Proof: the shifted Legendre polynomials `P_m = (1/m!) dᵐ/dxᵐ (xᵐ (1-x)ᵐ)` (Rodrigues) are orthogonal
on `[0, 1]` with `∫ P_m² = 1/(2m+1)` (integration by parts and the Beta integral); a polynomial of
degree `< h` expands in `P_0, ..., P_{h-1}`; Cauchy-Schwarz with `Σ_{m<h} (2m+1) = h²`; and
`P_m(-s) = Σ_k C(m,k)² s^k (1+s)^{m-k} ≤ (√s + √(1+s))^{2m} = (Y + √(Y²-1))^m`
(Leibniz applied to the Rodrigues formula; sum of squares ≤ square of sum).
-/

namespace CatalanCore.Zeta5.Rho

open Polynomial intervalIntegral Finset Nat

/-- The Rodrigues weight `(-1)^m X^m (X - 1)^m = X^m (1 - X)^m`. -/
noncomputable def Wt (m : ℕ) : ℝ[X] := C ((-1 : ℝ) ^ m) * (X ^ m * (X - C 1) ^ m)

/-- The shifted Legendre polynomial on `[0,1]` (Rodrigues' formula). -/
noncomputable def Pl (m : ℕ) : ℝ[X] := C ((m ! : ℝ)⁻¹) * derivative^[m] (Wt m)

theorem rodrigues (m : ℕ) : derivative^[m] (Wt m) = C (m ! : ℝ) * Pl m := by
  unfold Pl
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (by positivity : (m ! : ℝ) ≠ 0)]
  simp

theorem eval_Wt (m : ℕ) (x : ℝ) : (Wt m).eval x = x ^ m * (1 - x) ^ m := by
  simp only [Wt, eval_mul, eval_C, eval_pow, eval_X, eval_sub]
  have : (x - 1) ^ m * (-1) ^ m = (1 - x) ^ m := by rw [← mul_pow]; ring_nf
  rw [← this]; ring

theorem monic_core (m : ℕ) : (X ^ m * (X - C 1) ^ m : ℝ[X]).Monic :=
  ((monic_X_pow m).mul ((monic_X_sub_C (1 : ℝ)).pow m))

theorem natDegree_core (m : ℕ) : (X ^ m * (X - C 1) ^ m : ℝ[X]).natDegree = 2 * m := by
  rw [(monic_X_pow m).natDegree_mul ((monic_X_sub_C (1 : ℝ)).pow m), natDegree_X_pow,
    natDegree_pow, natDegree_X_sub_C]
  ring

theorem natDegree_Wt (m : ℕ) : (Wt m).natDegree = 2 * m := by
  unfold Wt
  rw [natDegree_C_mul (pow_ne_zero _ (by norm_num)), natDegree_core]

theorem coeff_Wt_top (m : ℕ) : (Wt m).coeff (2 * m) = (-1) ^ m := by
  unfold Wt
  rw [coeff_C_mul]
  have h1 := (monic_core m).coeff_natDegree
  rw [natDegree_core] at h1
  rw [h1, mul_one]

/-- An iterated derivative of a polynomial of degree at most `n`, `n` times, is a constant. -/
theorem iter_top (p : ℝ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    derivative^[n] p = C ((n ! : ℝ) * p.coeff n) := by
  have hd : (derivative^[n] p).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative p n
    omega
  rw [eq_C_of_natDegree_le_zero hd, coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

theorem natDegree_Pl_le (m : ℕ) : (Pl m).natDegree ≤ m := by
  unfold Pl
  refine (natDegree_C_mul_le _ _).trans ?_
  have := natDegree_iterate_derivative (Wt m) m
  rw [natDegree_Wt] at this
  omega

theorem coeff_Pl_top (m : ℕ) :
    (Pl m).coeff m = (m ! : ℝ)⁻¹ * ((2 * m).descFactorial m : ℝ) * (-1) ^ m := by
  unfold Pl
  rw [coeff_C_mul, coeff_iterate_derivative, show m + m = 2 * m by ring, coeff_Wt_top]
  simp [nsmul_eq_mul, mul_assoc]

theorem natDegree_Pl (m : ℕ) : (Pl m).natDegree = m := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_Pl_le m) ?_
  rw [coeff_Pl_top]
  have : ((2 * m).descFactorial m : ℝ) ≠ 0 := by
    have := Nat.descFactorial_pos.mpr (by omega : m ≤ 2 * m)
    exact_mod_cast this.ne'
  have h2 : (m ! : ℝ)⁻¹ ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero h2 this) (pow_ne_zero _ (by norm_num))

/-- `dᵐ/dxᵐ P_m` is the constant `(-1)^m (2m)! / m!`. -/
theorem iter_Pl (m : ℕ) : derivative^[m] (Pl m) = C ((-1) ^ m * ((2 * m)! : ℝ) / (m ! : ℝ)) := by
  unfold Pl
  rw [iterate_derivative_C_mul, ← Function.iterate_add_apply, iter_top (Wt m) (m + m)
    (by rw [natDegree_Wt]; omega)]
  have : m + m = 2 * m := by ring
  rw [this, coeff_Wt_top, ← C_mul]
  congr 1
  field_simp

/-- Vanishing of derivatives of the weight at both ends. -/
theorem Wt_deriv_zero {m j : ℕ} (hj : j < m) : (derivative^[j] (Wt m)).eval 0 = 0 := by
  have h1 : (X : ℝ[X]) ^ m ∣ Wt m :=
    ⟨C ((-1 : ℝ) ^ m) * (X - C 1) ^ m, by unfold Wt; ring⟩
  have h2 := pow_sub_dvd_iterate_derivative_of_pow_dvd j h1
  have h3 : (X : ℝ[X]) ∣ derivative^[j] (Wt m) :=
    (dvd_pow_self X (by omega : m - j ≠ 0)).trans h2
  obtain ⟨c, hc⟩ := h3
  rw [hc]; simp

theorem Wt_deriv_one {m j : ℕ} (hj : j < m) : (derivative^[j] (Wt m)).eval 1 = 0 := by
  have h1 : (X - C 1 : ℝ[X]) ^ m ∣ Wt m :=
    ⟨C ((-1 : ℝ) ^ m) * X ^ m, by unfold Wt; ring⟩
  have h2 := pow_sub_dvd_iterate_derivative_of_pow_dvd j h1
  have h3 : (X - C 1 : ℝ[X]) ∣ derivative^[j] (Wt m) :=
    (dvd_pow_self _ (by omega : m - j ≠ 0)).trans h2
  obtain ⟨c, hc⟩ := h3
  rw [hc]; simp

theorem integrable_poly (q : ℝ[X]) :
    IntervalIntegrable (fun x => q.eval x) MeasureTheory.volume 0 1 :=
  q.continuous.intervalIntegrable _ _

/-- Repeated integration by parts on `[0,1]`. -/
theorem ibp_iter (w : ℝ[X]) (k : ℕ)
    (hw : ∀ j < k, (derivative^[j] w).eval 0 = 0 ∧ (derivative^[j] w).eval 1 = 0) :
    ∀ q : ℝ[X], ∫ x in (0 : ℝ)..1, q.eval x * (derivative^[k] w).eval x =
      (-1) ^ k * ∫ x in (0 : ℝ)..1, (derivative^[k] q).eval x * w.eval x := by
  induction k with
  | zero => intro q; simp
  | succ k ih =>
    intro q
    have hk := hw k (Nat.lt_succ_self k)
    have step : ∫ x in (0 : ℝ)..1, q.eval x * (derivative^[k + 1] w).eval x =
        - ∫ x in (0 : ℝ)..1, (derivative q).eval x * (derivative^[k] w).eval x := by
      rw [Function.iterate_succ_apply']
      have := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        (a := 0) (b := 1) (u := fun x => q.eval x) (v := fun x => (derivative^[k] w).eval x)
        (u' := fun x => (derivative q).eval x) (v' := fun x => (derivative (derivative^[k] w)).eval x)
        q.continuous.continuousOn (derivative^[k] w).continuous.continuousOn
        (fun x _ => Polynomial.hasDerivAt q x) (fun x _ => Polynomial.hasDerivAt _ x)
        (integrable_poly _) (integrable_poly _)
      rw [this, hk.1, hk.2]; simp
    rw [step, ih (fun j hj => hw j (by omega)) (derivative q), Function.iterate_succ_apply]
    rw [pow_succ]; ring

/-- Beta integral. -/
theorem beta_int (b : ℕ) : ∀ a : ℕ, ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b =
    (a ! : ℝ) * (b !) / ((a + b + 1)! : ℝ) := by
  induction b with
  | zero =>
    intro a
    simp only [pow_zero, mul_one, integral_pow, one_pow]
    simp only [Nat.factorial_zero, add_zero, Nat.cast_one, mul_one]
    rw [Nat.factorial_succ]; push_cast
    have : (a ! : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  | succ b ih =>
    intro a
    have := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := 0) (b := 1) (u := fun x : ℝ => (1 - x) ^ (b + 1))
      (v := fun x : ℝ => x ^ (a + 1) / (a + 1))
      (u' := fun x : ℝ => -((b + 1 : ℝ) * (1 - x) ^ b))
      (v' := fun x : ℝ => x ^ a)
      (by fun_prop) (by fun_prop)
      (fun x _ => by
        have h := ((hasDerivAt_id' x).const_sub 1).fun_pow (b + 1)
        convert h using 1; simp only [Nat.add_sub_cancel]; push_cast; ring)
      (fun x _ => by
        have h := (hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1)
        convert h using 1
        rw [Nat.add_sub_cancel]; push_cast; field_simp)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    have e1 : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1) =
        ∫ x in (0 : ℝ)..1, (1 - x) ^ (b + 1) * x ^ a := by
      refine integral_congr (fun x _ => ?_); ring
    rw [e1, this]
    have e2 : ∫ x in (0 : ℝ)..1, -((b + 1 : ℝ) * (1 - x) ^ b) * (x ^ (a + 1) / (a + 1)) =
        - ((b + 1 : ℝ) / (a + 1)) * ∫ x in (0 : ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      rw [← intervalIntegral.integral_const_mul]
      refine integral_congr (fun x _ => ?_)
      ring
    rw [e2, ih (a + 1)]
    have hf : ((a + 1)! : ℝ) = (a + 1) * (a ! : ℝ) := by push_cast [Nat.factorial_succ]; ring
    have hg : ((a + 1 + b + 1)! : ℝ) = ((a + (b + 1) + 1)! : ℝ) := by
      rw [show a + 1 + b + 1 = a + (b + 1) + 1 by ring]
    have hh : ((b + 1)! : ℝ) = (b + 1) * (b ! : ℝ) := by push_cast [Nat.factorial_succ]; ring
    rw [hg, hf, hh]
    have hp : (((a + (b + 1) + 1)! : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [sub_self, one_pow, zero_pow (Nat.succ_ne_zero b), zero_pow (Nat.succ_ne_zero a),
      zero_mul, zero_div, mul_zero, sub_zero, zero_sub, neg_neg, neg_mul]
    field_simp

theorem Wt_hw (m : ℕ) :
    ∀ j < m, (derivative^[j] (Wt m)).eval 0 = 0 ∧ (derivative^[j] (Wt m)).eval 1 = 0 :=
  fun _ hj => ⟨Wt_deriv_zero hj, Wt_deriv_one hj⟩

theorem norm_Pl (m : ℕ) : ∫ x in (0 : ℝ)..1, (Pl m).eval x ^ 2 = 1 / (2 * m + 1) := by
  have h := ibp_iter (Wt m) m (Wt_hw m) (Pl m)
  rw [rodrigues, iter_Pl] at h
  have e1 : ∫ x in (0 : ℝ)..1, (Pl m).eval x * (C (m ! : ℝ) * Pl m).eval x =
      (m ! : ℝ) * ∫ x in (0 : ℝ)..1, (Pl m).eval x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr (fun x _ => ?_)
    simp only [eval_mul, eval_C]; ring
  have e2 : ∫ x in (0 : ℝ)..1, (C ((-1) ^ m * ((2 * m)! : ℝ) / (m ! : ℝ))).eval x * (Wt m).eval x =
      ((-1) ^ m * ((2 * m)! : ℝ) / (m ! : ℝ)) * ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ m := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr (fun x _ => ?_)
    simp only [eval_C, eval_Wt]
  rw [e1, e2, beta_int m m] at h
  have hsq : ((-1 : ℝ) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
  have hf : ((2 * m + 1)! : ℝ) = (2 * m + 1) * ((2 * m)! : ℝ) := by
    push_cast [Nat.factorial_succ]; ring
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have h2 : (m ! : ℝ) * ∫ x in (0 : ℝ)..1, (Pl m).eval x ^ 2 = (m ! : ℝ) * (1 / (2 * m + 1)) := by
    have h26 : ((2 * m)! : ℝ) ≠ 0 := by positivity
    have key : ∀ X Z : ℝ, (-1 : ℝ) ^ m * ((-1) ^ m * X * Z) = X * Z := fun X Z => by
      calc _ = ((-1 : ℝ) ^ m * (-1) ^ m) * (X * Z) := by ring
        _ = X * Z := by rw [hsq, one_mul]
    rw [h, show m + m + 1 = 2 * m + 1 by ring, hf, mul_div_assoc, key]
    field_simp
  exact mul_left_cancel₀ hm h2

theorem orth_Pl {k m : ℕ} (hkm : k < m) :
    ∫ x in (0 : ℝ)..1, (Pl k).eval x * (Pl m).eval x = 0 := by
  have h := ibp_iter (Wt m) m (Wt_hw m) (Pl k)
  have hz : derivative^[m] (Pl k) = 0 := by
    apply iterate_derivative_eq_zero_of_degree_lt
    exact lt_of_le_of_lt degree_le_natDegree (by rw [natDegree_Pl]; exact_mod_cast hkm)
  rw [rodrigues, hz] at h
  simp only [eval_zero, zero_mul, intervalIntegral.integral_zero, mul_zero] at h
  have e1 : ∫ x in (0 : ℝ)..1, (Pl k).eval x * (C (m ! : ℝ) * Pl m).eval x =
      (m ! : ℝ) * ∫ x in (0 : ℝ)..1, (Pl k).eval x * (Pl m).eval x := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr (fun x _ => ?_)
    simp only [eval_mul, eval_C]; ring
  rw [e1] at h
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_left hm

theorem inner_Pl (m m' : ℕ) :
    ∫ x in (0 : ℝ)..1, (Pl m).eval x * (Pl m').eval x = if m = m' then 1 / (2 * (m : ℝ) + 1) else 0 := by
  rcases lt_trichotomy m m' with h | h | h
  · rw [if_neg h.ne]; exact orth_Pl h
  · subst h; rw [if_pos rfl, ← norm_Pl]; simp [sq]
  · rw [if_neg h.ne']
    simpa [mul_comm] using orth_Pl h

/-- The value of `P_m` to the left of `[0,1]`: all terms are positive. -/
theorem eval_Pl_neg (m : ℕ) (s : ℝ) :
    (Pl m).eval (-s) =
      ∑ k ∈ range (m + 1), ((m.choose k : ℝ)) ^ 2 * s ^ k * (1 + s) ^ (m - k) := by
  unfold Pl Wt
  rw [iterate_derivative_C_mul, iterate_derivative_mul]
  simp only [eval_mul, eval_C, eval_finset_sum, eval_smul, iterate_derivative_X_pow_eq_smul,
    iterate_derivative_X_sub_pow, smul_eq_mul, eval_pow, eval_X, eval_sub, nsmul_eq_mul,
    eval_natCast]
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hsq : ((-1 : ℝ) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
  have hterm : ∀ k ∈ range m.succ,
      (-1 : ℝ) ^ m * ((m.choose k : ℝ) * ((m.descFactorial (m - k) : ℝ) * (-s) ^ (m - (m - k)) *
        ((m.descFactorial k : ℝ) * (-s - 1) ^ (m - k)))) =
      (m ! : ℝ) * ((m.choose k : ℝ) ^ 2 * s ^ k * (1 + s) ^ (m - k)) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e1 : m - (m - k) = k := by omega
    rw [e1, Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.choose_symm hkm]
    have hfac : (m.choose k : ℝ) * k ! * (m - k)! = m ! := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
    have hneg : (-1 : ℝ) ^ m * ((-s) ^ k * (-s - 1) ^ (m - k)) = s ^ k * (1 + s) ^ (m - k) := by
      have a1 : (-s) ^ k = (-1) ^ k * s ^ k := neg_pow s k
      have a2 : (-s - 1) ^ (m - k) = (-1) ^ (m - k) * (1 + s) ^ (m - k) := by
        rw [← neg_pow]; ring_nf
      have a3 : (-1 : ℝ) ^ k * (-1) ^ (m - k) = (-1) ^ m := by
        rw [← pow_add]; congr 1; omega
      rw [a1, a2]
      calc (-1 : ℝ) ^ m * ((-1) ^ k * s ^ k * ((-1) ^ (m - k) * (1 + s) ^ (m - k)))
          = ((-1 : ℝ) ^ m * ((-1) ^ k * (-1) ^ (m - k))) * (s ^ k * (1 + s) ^ (m - k)) := by ring
        _ = _ := by rw [a3, hsq, one_mul]
    push_cast
    rw [← hfac]
    linear_combination ((m.choose k : ℝ) ^ 3 * (m - k)! * k !) * hneg
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ hm, one_mul]

theorem eval_Pl_neg_le (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (Pl m).eval (-s) ∧ (Pl m).eval (-s) ≤ ((√s + √(1 + s)) ^ 2) ^ m := by
  rw [eval_Pl_neg]
  constructor
  · exact Finset.sum_nonneg (fun k _ => by positivity)
  · set a : ℕ → ℝ := fun k => (m.choose k : ℝ) * √s ^ k * √(1 + s) ^ (m - k) with ha
    have h1 : ∀ k, 0 ≤ a k := fun k => by simp only [ha]; positivity
    have h2 : ∑ k ∈ range (m + 1), ((m.choose k : ℝ)) ^ 2 * s ^ k * (1 + s) ^ (m - k) =
        ∑ k ∈ range (m + 1), (a k) ^ 2 := by
      refine sum_congr rfl fun k _ => ?_
      simp only [ha]
      have e1 : (√s ^ k) ^ 2 = s ^ k := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hs]
      have e2 : (√(1 + s) ^ (m - k)) ^ 2 = (1 + s) ^ (m - k) := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by linarith)]
      rw [mul_pow, mul_pow, e1, e2]
    have h3 : ∑ k ∈ range (m + 1), a k = (√s + √(1 + s)) ^ m := by
      rw [add_pow]; refine sum_congr rfl fun k _ => ?_; simp only [ha]; ring
    rw [h2]
    calc _ ≤ (∑ k ∈ range (m + 1), a k) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => h1 k)
      _ = ((√s + √(1 + s)) ^ 2) ^ m := by rw [h3, ← pow_mul, ← pow_mul, mul_comm]

theorem coeff_Pl_ne (m : ℕ) : (Pl m).coeff m ≠ 0 := by
  rw [coeff_Pl_top]
  have : ((2 * m).descFactorial m : ℝ) ≠ 0 := by
    have := Nat.descFactorial_pos.mpr (by omega : m ≤ 2 * m)
    exact_mod_cast this.ne'
  have h2 : (m ! : ℝ)⁻¹ ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero h2 this) (pow_ne_zero _ (by norm_num))

/-- Every polynomial of degree `< h` is a combination of `P_0, …, P_{h-1}`. -/
theorem expand : ∀ (h : ℕ) (p : ℝ[X]), p.degree < h →
    ∃ c : ℕ → ℝ, p = ∑ m ∈ range h, C (c m) * Pl m := by
  intro h
  induction h with
  | zero =>
    intro p hp
    refine ⟨fun _ => 0, ?_⟩
    have : p = 0 := by
      have h0 : p.degree < (0 : ℕ) := hp
      simpa using h0
    simp [this]
  | succ h ih =>
    intro p hp
    set c0 : ℝ := p.coeff h / (Pl h).coeff h with hc0
    set q : ℝ[X] := p - C c0 * Pl h with hq
    have hqd : q.degree < h := by
      rw [degree_lt_iff_coeff_zero]
      intro j hj
      rw [hq, coeff_sub, coeff_C_mul]
      rcases Nat.eq_or_lt_of_le hj with hjh | hjh
      · rw [← hjh, hc0, div_mul_cancel₀ _ (coeff_Pl_ne h), sub_self]
      · have h1 : p.coeff j = 0 := coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast hjh))
        have h2 : (Pl h).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by rw [natDegree_Pl]; exact hjh)
        rw [h1, h2]; simp
    obtain ⟨c, hc⟩ := ih q hqd
    refine ⟨fun m => if m < h then c m else c0, ?_⟩
    rw [Finset.sum_range_succ]
    have e1 : ∑ m ∈ range h, C (if m < h then c m else c0) * Pl m =
        ∑ m ∈ range h, C (c m) * Pl m :=
      sum_congr rfl fun m hm => by rw [if_pos (Finset.mem_range.mp hm)]
    rw [e1]; simp only [lt_irrefl, if_false]; rw [← hc, hq]; ring

theorem integral_sq_expand (h : ℕ) (c : ℕ → ℝ) :
    ∫ x in (0 : ℝ)..1, ((∑ m ∈ range h, C (c m) * Pl m).eval x) ^ 2 =
      ∑ m ∈ range h, c m ^ 2 / (2 * m + 1) := by
  have e : ∀ x : ℝ, ((∑ m ∈ range h, C (c m) * Pl m).eval x) ^ 2 =
      ∑ m ∈ range h, ∑ m' ∈ range h,
        (c m * c m') * ((Pl m).eval x * (Pl m').eval x) := by
    intro x
    simp only [eval_finset_sum, eval_mul, eval_C]
    rw [sq, Finset.sum_mul_sum]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hi : ∀ m m' : ℕ, IntervalIntegrable
      (fun x : ℝ => (c m * c m') * ((Pl m).eval x * (Pl m').eval x)) MeasureTheory.volume 0 1 :=
    fun m m' => (continuous_const.mul ((Pl m).continuous.mul (Pl m').continuous)).intervalIntegrable _ _
  have hi' : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => ∑ m' ∈ range h,
      (c m * c m') * ((Pl m).eval x * (Pl m').eval x)) MeasureTheory.volume 0 1 := fun m =>
    (continuous_finset_sum _ (fun m' _ => continuous_const.mul
      ((Pl m).continuous.mul (Pl m').continuous))).intervalIntegrable _ _
  rw [integral_congr (fun x _ => e x)]
  rw [intervalIntegral.integral_finset_sum (fun m _ => hi' m)]
  refine sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_finset_sum (fun m' _ => hi m m')]
  simp only [intervalIntegral.integral_const_mul, inner_Pl]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, if_pos hm]
  ring

theorem sum_odd (h : ℕ) : ∑ m ∈ range h, (2 * (m : ℝ) + 1) = (h : ℝ) ^ 2 := by
  induction h with
  | zero => simp
  | succ h ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Core estimate on `[0,1]`: `P(-s)² ≤ h² R^{2h} ∫₀¹ P²`, `R = (√s + √(1+s))² = Y + √(Y²-1)`. -/
theorem sq_le_core {h : ℕ} {p : ℝ[X]} (hp : p.degree < h) {s : ℝ} (hs : 0 ≤ s) :
    (p.eval (-s)) ^ 2 ≤
      (h : ℝ) ^ 2 * ((√s + √(1 + s)) ^ 2) ^ (2 * h) * ∫ x in (0 : ℝ)..1, (p.eval x) ^ 2 := by
  obtain ⟨c, hc⟩ := expand h p hp
  subst hc
  rw [integral_sq_expand]
  set R : ℝ := (√s + √(1 + s)) ^ 2 with hR
  have hR1 : 1 ≤ R := by
    have h1 : (0 : ℝ) ≤ √s := Real.sqrt_nonneg _
    have h2 : (√(1 + s)) ^ 2 = 1 + s := Real.sq_sqrt (by linarith)
    have h3 : (0 : ℝ) ≤ √(1 + s) := Real.sqrt_nonneg _
    rw [hR]; nlinarith
  have hev : (∑ m ∈ range h, C (c m) * Pl m).eval (-s) =
      ∑ m ∈ range h, c m * (Pl m).eval (-s) := by simp [eval_finset_sum]
  rw [hev]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range h) (fun m : ℕ => c m / √(2 * (m : ℝ) + 1))
    (fun m : ℕ => √(2 * (m : ℝ) + 1) * (Pl m).eval (-s))
  have hfg : ∀ m ∈ range h, c m / √(2 * (m : ℝ) + 1) * (√(2 * (m : ℝ) + 1) * (Pl m).eval (-s)) =
      c m * (Pl m).eval (-s) := by
    intro m _
    have : √(2 * (m : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  rw [Finset.sum_congr rfl hfg] at hcs
  have hf2 : ∑ m ∈ range h, (c m / √(2 * (m : ℝ) + 1)) ^ 2 = ∑ m ∈ range h, c m ^ 2 / (2 * m + 1) :=
    sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt (by positivity)]
  have hg2 : ∑ m ∈ range h, (√(2 * (m : ℝ) + 1) * (Pl m).eval (-s)) ^ 2 ≤ (h : ℝ) ^ 2 * R ^ (2 * h) := by
    rw [← sum_odd h, Finset.sum_mul]
    refine sum_le_sum fun m hm => ?_
    have hm' : m < h := Finset.mem_range.mp hm
    obtain ⟨hp0, hp1⟩ := eval_Pl_neg_le m hs
    have hp2 : ((Pl m).eval (-s)) ^ 2 ≤ R ^ (2 * h) := by
      calc ((Pl m).eval (-s)) ^ 2 ≤ (R ^ m) ^ 2 := by gcongr
        _ = R ^ (2 * m) := by rw [← pow_mul, mul_comm]
        _ ≤ R ^ (2 * h) := pow_le_pow_right₀ hR1 (by omega)
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact mul_le_mul_of_nonneg_left hp2 (by positivity)
  rw [hf2] at hcs
  have hI0 : 0 ≤ ∑ m ∈ range h, c m ^ 2 / (2 * (m : ℝ) + 1) :=
    Finset.sum_nonneg fun m _ => by positivity
  calc _ ≤ _ := hcs
    _ ≤ (∑ m ∈ range h, c m ^ 2 / (2 * (m : ℝ) + 1)) * ((h : ℝ) ^ 2 * R ^ (2 * h)) :=
        mul_le_mul_of_nonneg_left hg2 hI0
    _ = _ := by ring

theorem R_eq_exp_arcosh {s : ℝ} (hs : 0 ≤ s) :
    (√s + √(1 + s)) ^ 2 = Real.exp (Real.arcosh (1 + 2 * s)) := by
  rw [Real.exp_arcosh (by linarith)]
  have h1 : (1 + 2 * s) ^ 2 - 1 = (2 * √(s * (1 + s))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [h1, Real.sqrt_sq (by positivity), Real.sqrt_mul hs]
  have e1 : √s ^ 2 = s := Real.sq_sqrt hs
  have e2 : √(1 + s) ^ 2 = 1 + s := Real.sq_sqrt (by linarith)
  nlinarith

/-- **ZR03.**  Evaluation at `-u²` against the `L²` norm on `[a, b]`:
`P(-u²)² ≤ h² exp(2 h arcosh Y) / (b - a) · ∫_a^b P²`, `Y = (2u² + a + b)/(b - a)`,
for `deg P < h` and `0 ≤ a < b`. -/
theorem node_bound {h : ℕ} {P : ℝ[X]} (hP : P.natDegree < h) {a b : ℝ} (u : ℝ)
    (hab : a < b) (ha : 0 ≤ a) :
    (P.eval (-u ^ 2)) ^ 2 ≤
      (h : ℝ) ^ 2 * Real.exp (2 * h * Real.arcosh ((2 * u ^ 2 + a + b) / (b - a))) / (b - a) *
        ∫ t in a..b, (P.eval t) ^ 2 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set q : ℝ[X] := C (b - a) * X + C a with hq
  have hqd : q.natDegree = 1 := by
    rw [hq]; exact natDegree_linear (by exact hba.ne')
  set p : ℝ[X] := P.comp q with hp
  have hpd : p.degree < h := by
    have : p.natDegree ≤ P.natDegree := by
      rw [hp, natDegree_comp, hqd, mul_one]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast lt_of_le_of_lt this hP)
  set s : ℝ := (u ^ 2 + a) / (b - a) with hs
  have hs0 : 0 ≤ s := by positivity
  have hcore := sq_le_core hpd hs0
  have hev : p.eval (-s) = P.eval (-u ^ 2) := by
    simp only [hp, eval_comp, hq, eval_add, eval_mul, eval_C, eval_X]
    congr 1
    rw [hs]; field_simp; ring
  have hint : ∫ x in (0 : ℝ)..1, (p.eval x) ^ 2 = (b - a)⁻¹ * ∫ t in a..b, (P.eval t) ^ 2 := by
    have := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1)
      (fun t : ℝ => (P.eval t) ^ 2) hba.ne' a
    simp only [mul_zero, zero_add, mul_one, smul_eq_mul] at this
    rw [show b - a + a = b by ring] at this
    simpa [hp, hq, eval_comp] using this
  have hY : 1 + 2 * s = (2 * u ^ 2 + a + b) / (b - a) := by
    rw [hs]; field_simp; ring
  have hR : ((√s + √(1 + s)) ^ 2) ^ (2 * h) =
      Real.exp (2 * h * Real.arcosh ((2 * u ^ 2 + a + b) / (b - a))) := by
    rw [R_eq_exp_arcosh hs0, ← hY, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [hev, hint, hR] at hcore
  calc _ ≤ _ := hcore
    _ = _ := by field_simp

end CatalanCore.Zeta5.Rho
