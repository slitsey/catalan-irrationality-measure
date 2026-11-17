module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import CatalanCore.Zeta5.Potential.Closed
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import CatalanCore.Zeta5.Cells.Compose
public import CatalanMeasure.GenD.Signed.TaylorCell

@[expose] public section

/-!
# Joukowski potentials of arcsine-type segment measures at complex points (Lai decay, LD12, LD13)

Generic in the segment `{M + h x : |x| ≤ 1}`, the Chebyshev density `f = Σ c_k T_k ≥ 0`, and any
real curve `γ`.  For `ζ = (s - M)/h` off `[-1, 1]`, with `φ = jphi ζ` the inverse Joukowski branch
(`|φ| > 1`, `J φ = ζ`, computed with real square roots only, `jR`, `jd`) and `q = jq ζ = (φ - φ⁻¹)/2`:

* **W2** (`jc_jJ`, `jd_jJ`, `jR_jJ`, `re_inv_pow_jphi`, `jphi_sign_form`): `|φ| = c + √(c² - 1)`,
  `Re φ^{-k} = |φ|^{-k} T_k(d)`.
* **W3(a)** (`logPotC_segMeasure`): the closed form of the logarithmic potential `U^ν(s)`.
* **W3(b)** (`hasDerivAt_jphi`, `poisson_hasSum`, `stieltjes_segMeasure`, `segSt_one`): `dφ/dζ = φ/q`
  and the Stieltjes transform `S₁(s) = ∫ (s - u)⁻¹ dν = (h q)⁻¹ (c₀ + Σ c_k φ^{-k})`.
* **W3(c)** (`hasDerivAt_stA`, `hasDerivAt_segSt`, `norm_segSt_le`, `abs_potT5_le`): `S_m' = -m S_{m+1}`,
  `‖S_m‖ ≤ c₀/dist^m`, and the order-5 remainder `|f 5| ≤ fdbBound`.
* **W3(d)** (`norm_sub_seg_ge`): `dist(s, segment) ≥ |h| (c(ζ) - 1)`.
* **The tower** (`hasDerivAt_logPotC_seg`, `isTower_potT`): `x ↦ U^ν(γ 0 x)` has the order-5
  derivative tower `potT`, an `IsTower` for the generic cell bound `taylor_cell_ub`.

Nothing here is specific to Lai's design: `M, h, c, N, γ` are parameters.
-/

section J1
open Complex Polynomial

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-- The Joukowski map `J(φ) = (φ + φ⁻¹)/2`. -/
def jJ (φ : ℂ) : ℂ := (φ + φ⁻¹) / 2

/-- Elliptic coordinate `c(ζ) = (|ζ - 1| + |ζ + 1|)/2` (`= cosh μ`). -/
def jc (ζ : ℂ) : ℝ := (‖ζ - 1‖ + ‖ζ + 1‖) / 2

/-- Elliptic coordinate `d(ζ) = (|ζ + 1| - |ζ - 1|)/2` (`= cos ν`). -/
def jd (ζ : ℂ) : ℝ := (‖ζ + 1‖ - ‖ζ - 1‖) / 2

/-- `|φ(ζ)| = c + √(c² - 1)`. -/
def jR (ζ : ℂ) : ℝ := jc ζ + Real.sqrt (jc ζ ^ 2 - 1)

/-- The inverse Joukowski branch `φ(ζ)` with `|φ| > 1` off `[-1, 1]`, by real operations only:
`Re φ = R d`, `Im φ = 2 Im ζ / (1 - R⁻²)`. -/
def jphi (ζ : ℂ) : ℂ := ⟨jR ζ * jd ζ, 2 * ζ.im / (1 - (jR ζ)⁻¹ ^ 2)⟩

/-- `q = (φ - φ⁻¹)/2`, the branch of `√(ζ² - 1)` with `φ = ζ + q`. -/
def jq (ζ : ℂ) : ℂ := (jphi ζ - (jphi ζ)⁻¹) / 2

/-! ### W2: elliptic coordinates of `J(φ)` -/

theorem sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem norm_jJ_add_one {φ : ℂ} (hφ : φ ≠ 0) :
    ‖jJ φ + 1‖ = (‖φ‖ ^ 2 + 2 * φ.re + 1) / (2 * ‖φ‖) := by
  have e : jJ φ + 1 = (φ + 1) ^ 2 / (2 * φ) := by unfold jJ; field_simp; ring
  rw [e, norm_div, norm_pow, norm_mul, Complex.norm_two, sq_norm_eq, sq_norm_eq]
  simp; ring

theorem norm_jJ_sub_one {φ : ℂ} (hφ : φ ≠ 0) :
    ‖jJ φ - 1‖ = (‖φ‖ ^ 2 - 2 * φ.re + 1) / (2 * ‖φ‖) := by
  have e : jJ φ - 1 = (φ - 1) ^ 2 / (2 * φ) := by unfold jJ; field_simp; ring
  rw [e, norm_div, norm_pow, norm_mul, Complex.norm_two, sq_norm_eq, sq_norm_eq]
  simp; ring

/-- **W2**: `c(J φ) = (|φ| + |φ|⁻¹)/2`. -/
theorem jc_jJ {φ : ℂ} (hφ : φ ≠ 0) : jc (jJ φ) = (‖φ‖ + ‖φ‖⁻¹) / 2 := by
  have hR : 0 < ‖φ‖ := norm_pos_iff.2 hφ
  unfold jc
  rw [norm_jJ_add_one hφ, norm_jJ_sub_one hφ]
  field_simp; ring

/-- **W2**: `d(J φ) = Re φ / |φ|`. -/
theorem jd_jJ {φ : ℂ} (hφ : φ ≠ 0) : jd (jJ φ) = φ.re / ‖φ‖ := by
  have hR : 0 < ‖φ‖ := norm_pos_iff.2 hφ
  unfold jd
  rw [norm_jJ_add_one hφ, norm_jJ_sub_one hφ]
  field_simp; ring

/-- **W2**: `|φ| = c + √(c² - 1)` for `|φ| ≥ 1`. -/
theorem jR_jJ {φ : ℂ} (hφ : 1 ≤ ‖φ‖) : jR (jJ φ) = ‖φ‖ := by
  have hφ0 : φ ≠ 0 := norm_pos_iff.1 (by linarith)
  have hR : 0 < ‖φ‖ := by linarith
  unfold jR
  rw [jc_jJ hφ0]
  have hinv : ‖φ‖⁻¹ ≤ ‖φ‖ := by
    rw [inv_le_iff_one_le_mul₀' hR]; nlinarith
  have e : ((‖φ‖ + ‖φ‖⁻¹) / 2) ^ 2 - 1 = ((‖φ‖ - ‖φ‖⁻¹) / 2) ^ 2 := by
    field_simp; ring
  rw [e, Real.sqrt_sq (by linarith)]
  ring

theorem one_lt_jc_jJ {φ : ℂ} (hφ : 1 < ‖φ‖) : 1 < jc (jJ φ) := by
  have hφ0 : φ ≠ 0 := norm_pos_iff.1 (by linarith)
  have hR : 0 < ‖φ‖ := by linarith
  rw [jc_jJ hφ0, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : (‖φ‖ - 1) ^ 2 / ‖φ‖ > 0 := div_pos (by nlinarith) hR
  have e : (‖φ‖ - 1) ^ 2 / ‖φ‖ = ‖φ‖ + ‖φ‖⁻¹ - 2 := by field_simp; ring
  linarith

theorem jJ_im (φ : ℂ) : (jJ φ).im = φ.im * (1 - (‖φ‖⁻¹) ^ 2) / 2 := by
  unfold jJ
  simp only [Complex.div_ofNat_im, Complex.add_im, Complex.inv_im]
  rw [← Complex.sq_norm]
  rcases eq_or_ne ‖φ‖ 0 with h | h
  · have : φ = 0 := norm_eq_zero.1 h
    subst this; simp
  · field_simp; ring

/-- On `|φ| > 1`, the real-operation branch inverts `J`. -/
theorem jphi_jJ {φ : ℂ} (hφ : 1 < ‖φ‖) : jphi (jJ φ) = φ := by
  have hφ0 : φ ≠ 0 := norm_pos_iff.1 (by linarith)
  have hR : 0 < ‖φ‖ := by linarith
  have hden : 1 - (‖φ‖⁻¹) ^ 2 ≠ 0 := by
    have : ‖φ‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
    have : 0 < ‖φ‖⁻¹ := inv_pos.2 hR
    nlinarith
  apply Complex.ext
  · simp only [jphi]
    rw [jR_jJ hφ.le, jd_jJ hφ0]; field_simp
  · simp only [jphi]
    rw [jR_jJ hφ.le, jJ_im]
    have h2 : ‖φ‖ ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp

/-- Every `ζ` is `J(φ)` for some `φ` with `|φ| ≥ 1`. -/
theorem exists_jJ (ζ : ℂ) : ∃ φ : ℂ, 1 ≤ ‖φ‖ ∧ jJ φ = ζ := by
  set q : ℂ := (ζ ^ 2 - 1) ^ ((2 : ℕ)⁻¹ : ℂ) with hq
  have hq2 : q ^ 2 = ζ ^ 2 - 1 := by rw [hq]; exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hab : (ζ + q) * (ζ - q) = 1 := by ring_nf; rw [hq2]; ring
  have ha0 : ζ + q ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have hb : ζ - q = (ζ + q)⁻¹ := eq_inv_of_mul_eq_one_right hab
  rcases le_or_gt 1 ‖ζ + q‖ with h | h
  · refine ⟨ζ + q, h, ?_⟩
    unfold jJ; rw [← hb]; ring
  · refine ⟨ζ - q, ?_, ?_⟩
    · rw [hb, norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.2 ha0)).2 h.le
    · unfold jJ
      rw [show (ζ - q)⁻¹ = ζ + q by rw [hb, inv_inv]]; ring

/-- **W2, existence and branch.** Off `[-1, 1]` (`c > 1`), `φ = jphi ζ` satisfies `J φ = ζ`
and `|φ| > 1`. -/
theorem jphi_spec {ζ : ℂ} (h : 1 < jc ζ) : 1 < ‖jphi ζ‖ ∧ jJ (jphi ζ) = ζ := by
  obtain ⟨φ, h1, rfl⟩ := exists_jJ ζ
  have hφ : 1 < ‖φ‖ := by
    rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hφ0 : φ ≠ 0 := norm_pos_iff.1 (by linarith)
      rw [jc_jJ hφ0, ← h1] at h; norm_num at h
  rw [jphi_jJ hφ]; exact ⟨hφ, rfl⟩

theorem jphi_ne_zero {ζ : ℂ} (h : 1 < jc ζ) : jphi ζ ≠ 0 :=
  norm_pos_iff.1 (by linarith [(jphi_spec h).1])

theorem jR_eq_norm {ζ : ℂ} (h : 1 < jc ζ) : jR ζ = ‖jphi ζ‖ := by
  conv_lhs => rw [← (jphi_spec h).2]
  exact jR_jJ (jphi_spec h).1.le

theorem jd_eq {ζ : ℂ} (h : 1 < jc ζ) : jd ζ = (jphi ζ).re / ‖jphi ζ‖ := by
  conv_lhs => rw [← (jphi_spec h).2]
  exact jd_jJ (jphi_ne_zero h)

/-- `ζ = (φ + φ⁻¹)/2 = φ - q`. -/
theorem jphi_eq_add_jq {ζ : ℂ} (h : 1 < jc ζ) : jphi ζ = ζ + jq ζ := by
  have hs := (jphi_spec h).2
  unfold jJ at hs; unfold jq
  linear_combination hs

theorem jq_sq {ζ : ℂ} (h : 1 < jc ζ) : jq ζ ^ 2 = ζ ^ 2 - 1 := by
  have hφ0 := jphi_ne_zero h
  conv_rhs => rw [← (jphi_spec h).2]
  unfold jJ jq; field_simp; ring

theorem jq_ne_zero {ζ : ℂ} (h : 1 < jc ζ) : jq ζ ≠ 0 := by
  have hφ := (jphi_spec h).1
  have hφ0 := jphi_ne_zero h
  unfold jq
  intro h0
  have : jphi ζ = (jphi ζ)⁻¹ := by linear_combination 2 * h0
  have h2 : ‖jphi ζ‖ = ‖jphi ζ‖⁻¹ := by rw [← norm_inv, ← this]
  have : ‖jphi ζ‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
  linarith

/-! ### W2: `Re φ^{-k} = |φ|^{-k} T_k(d)` -/

/-- For `x ≠ 0`: `Re xᵏ = |x|ᵏ T_k(Re x / |x|)`. -/
theorem re_pow_eq_cheb {x : ℂ} (hx : x ≠ 0) (k : ℕ) :
    (x ^ k).re = ‖x‖ ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (x.re / ‖x‖) := by
  rw [← Complex.cos_arg hx, Chebyshev.T_real_cos]
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  have : (k : ℂ) * (↑(arg x) * I) = ((k * arg x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  push_cast; ring_nf

/-- **W2**: `Re φ^{-k} = |φ|^{-k} T_k(d)`. -/
theorem re_inv_pow_jphi {ζ : ℂ} (h : 1 < jc ζ) (k : ℕ) :
    ((jphi ζ ^ k)⁻¹).re = (jR ζ)⁻¹ ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (jd ζ) := by
  have hφ0 := jphi_ne_zero h
  have hR : 0 < ‖jphi ζ‖ := norm_pos_iff.2 hφ0
  rw [← inv_pow, re_pow_eq_cheb (inv_ne_zero hφ0), norm_inv, jR_eq_norm h, jd_eq h,
    Complex.inv_re, ← Complex.sq_norm]
  congr 2
  field_simp

/-- **W2**, the sign form: `φ = R (d + i sgn(Im ζ) √(1 - d²))`. -/
theorem jphi_sign_form {ζ : ℂ} (h : 1 < jc ζ) :
    jphi ζ = (jR ζ : ℂ) * ((jd ζ : ℂ) + I * ((SignType.sign ζ.im : ℝ) *
      Real.sqrt (1 - jd ζ ^ 2) : ℝ)) := by
  have hφ := (jphi_spec h).1
  have hφ0 := jphi_ne_zero h
  set φ := jphi ζ with hφd
  have hR : 0 < ‖φ‖ := norm_pos_iff.2 hφ0
  have hjR := jR_eq_norm h
  have hjd := jd_eq h
  rw [← hφd] at hjR hjd
  -- `Im ζ` and `Im φ` have the same sign
  have him : ζ.im = φ.im * (1 - (‖φ‖⁻¹) ^ 2) / 2 := by
    conv_lhs => rw [← (jphi_spec h).2]
    exact jJ_im φ
  have hpos : 0 < (1 - (‖φ‖⁻¹) ^ 2) / 2 := by
    have : ‖φ‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
    have : 0 < ‖φ‖⁻¹ := inv_pos.2 hR
    nlinarith
  have hsgn : SignType.sign ζ.im = SignType.sign φ.im := by
    rw [him, mul_div_assoc, sign_mul, sign_pos hpos, mul_one]
  have hsq : Real.sqrt (1 - jd ζ ^ 2) = |φ.im| / ‖φ‖ := by
    rw [hjd]
    have e : 1 - (φ.re / ‖φ‖) ^ 2 = (|φ.im| / ‖φ‖) ^ 2 := by
      have := sq_norm_eq φ
      rw [div_pow, div_pow, sq_abs]; field_simp; linarith
    rw [e, Real.sqrt_sq (div_nonneg (abs_nonneg _) hR.le)]
  apply Complex.ext
  · simp [hjR, hjd]; field_simp
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, add_zero, one_mul, zero_add,
      Complex.add_re, sub_zero, mul_zero]
    rw [hsq, hsgn, hjR]
    have := sign_mul_abs φ.im
    field_simp
    linarith

/-! ### W3(b): the inverse branch is holomorphic, `dφ/dζ = φ/q` -/

theorem continuous_jc : Continuous jc := by unfold jc; fun_prop

theorem continuous_jd : Continuous jd := by unfold jd; fun_prop

theorem continuous_jR : Continuous jR := by
  unfold jR
  exact continuous_jc.add (Real.continuous_sqrt.comp ((continuous_jc.pow 2).sub continuous_const))

theorem isOpen_jc : IsOpen {ζ : ℂ | 1 < jc ζ} := isOpen_lt continuous_const continuous_jc

theorem one_lt_jR {ζ : ℂ} (h : 1 < jc ζ) : 1 < jR ζ := by
  unfold jR; linarith [Real.sqrt_nonneg (jc ζ ^ 2 - 1)]

theorem jphi_eq_mk (ζ : ℂ) : jphi ζ = ((jR ζ * jd ζ : ℝ) : ℂ) +
    ((2 * ζ.im / (1 - (jR ζ)⁻¹ ^ 2) : ℝ) : ℂ) * I := by
  apply Complex.ext <;>
    simp only [jphi, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im] <;> ring

theorem continuousAt_jphi {ζ : ℂ} (h : 1 < jc ζ) : ContinuousAt jphi ζ := by
  have hR := one_lt_jR h
  have hden : 1 - (jR ζ)⁻¹ ^ 2 ≠ 0 := by
    have : (jR ζ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    have : 0 < (jR ζ)⁻¹ := inv_pos.2 (by linarith)
    nlinarith
  have hR0 : jR ζ ≠ 0 := by linarith
  rw [show jphi = fun ζ => ((jR ζ * jd ζ : ℝ) : ℂ) +
    ((2 * ζ.im / (1 - (jR ζ)⁻¹ ^ 2) : ℝ) : ℂ) * I from funext jphi_eq_mk]
  have c1 : ContinuousAt (fun ζ : ℂ => jR ζ * jd ζ) ζ :=
    (continuous_jR.mul continuous_jd).continuousAt
  have c2 : ContinuousAt (fun ζ : ℂ => 2 * ζ.im / (1 - (jR ζ)⁻¹ ^ 2)) ζ := by
    refine ContinuousAt.div (by fun_prop) ?_ hden
    exact continuousAt_const.sub ((continuous_jR.continuousAt.inv₀ hR0).pow 2)
  exact (Complex.continuous_ofReal.continuousAt.comp c1).add
    ((Complex.continuous_ofReal.continuousAt.comp c2).mul continuousAt_const)

theorem hasDerivAt_jJ {φ : ℂ} (hφ : φ ≠ 0) : HasDerivAt jJ ((1 - (φ ^ 2)⁻¹) / 2) φ := by
  unfold jJ
  have := ((hasDerivAt_id φ).add (hasDerivAt_inv hφ)).div_const 2
  simpa [sub_eq_add_neg] using this

/-- **W3(b)**: `dφ/dζ = φ/q` off `[-1, 1]`. -/
theorem hasDerivAt_jphi {ζ : ℂ} (h : 1 < jc ζ) :
    HasDerivAt jphi (jphi ζ / jq ζ) ζ := by
  have hφ := (jphi_spec h).1
  have hφ0 := jphi_ne_zero h
  have hq0 := jq_ne_zero h
  have hd : (1 - (jphi ζ ^ 2)⁻¹) / 2 ≠ 0 := by
    intro h0
    apply hq0; unfold jq
    have : (jphi ζ ^ 2)⁻¹ = 1 := by linear_combination -2 * h0
    have h2 : jphi ζ ^ 2 = 1 := by rw [← inv_inv (jphi ζ ^ 2), this, inv_one]
    field_simp; linear_combination h2
  have key := HasDerivAt.of_local_left_inverse (continuousAt_jphi h) (hasDerivAt_jJ hφ0) hd
    (Filter.mem_of_superset (isOpen_jc.mem_nhds h) fun y hy => (jphi_spec hy).2)
  convert key using 1
  unfold jq
  field_simp

/-- **W3(b)**: `dq/dζ = ζ/q`. -/
theorem hasDerivAt_jq {ζ : ℂ} (h : 1 < jc ζ) : HasDerivAt jq (ζ / jq ζ) ζ := by
  have hq0 := jq_ne_zero h
  have e : ∀ᶠ y in nhds ζ, jq y = jphi y - y :=
    Filter.mem_of_superset (isOpen_jc.mem_nhds h) fun y hy => by
      show jq y = jphi y - y
      rw [jphi_eq_add_jq hy]; ring
  have := (hasDerivAt_jphi h).sub (hasDerivAt_id ζ)
  refine (this.congr_of_eventuallyEq e).congr_deriv ?_
  rw [jphi_eq_add_jq h]; field_simp; ring

/-- **W3(b)**: `d φ^{-k}/dζ = -k φ^{-k}/q`. -/
theorem hasDerivAt_jphi_inv_pow {ζ : ℂ} (h : 1 < jc ζ) (k : ℕ) :
    HasDerivAt (fun y => (jphi y ^ k)⁻¹) (-(k : ℂ) * (jphi ζ ^ k)⁻¹ / jq ζ) ζ := by
  have hφ0 := jphi_ne_zero h
  have hq0 := jq_ne_zero h
  have h1 : HasDerivAt (fun y => (jphi y ^ k)⁻¹)
      (-((k : ℂ) * jphi ζ ^ (k - 1) * (jphi ζ / jq ζ)) / (jphi ζ ^ k) ^ 2) ζ :=
    ((hasDerivAt_pow k (jphi ζ)).comp ζ (hasDerivAt_jphi h)).inv (pow_ne_zero k hφ0)
  refine h1.congr_deriv ?_
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

end

end CatalanCore.Tools.Joukowski
end J1

section J2
open Complex Polynomial MeasureTheory Set CatalanCore.Zeta5.Potential OAI.InternalCatalan

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-! ### The segment measure and its logarithmic potential (W3(a), L2 at complex points) -/

/-- The measure `f dω` on the segment `{M + h x : |x| ≤ 1}`, `f = Σ_{k ≤ N} c_k T_k`, as a
measure on `ℂ` (push-forward of the arcsine law in the angle). -/
def segMeasure (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) : Measure ℂ :=
  (arc.withDensity fun θ => ENNReal.ofReal (chebF c N (Real.cos θ))).map
    (fun θ => M + h * (Real.cos θ : ℂ))

/-- The logarithmic potential `U^ν(s) = ∫ log (1/|s - u|) dν(u)`. -/
def logPotC (ν : Measure ℂ) (s : ℂ) : ℝ := -∫ u, Real.log ‖s - u‖ ∂ν

theorem continuous_segMap (M h : ℂ) : Continuous fun θ : ℝ => M + h * (Real.cos θ : ℂ) := by
  fun_prop

theorem integral_segMeasure {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ u, g u ∂(segMeasure M h c N) =
      ∫ θ, chebF c N (Real.cos θ) * g (M + h * (Real.cos θ : ℂ)) ∂arc := by
  unfold segMeasure
  rw [integral_map (continuous_segMap M h).measurable.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun θ => ENNReal.ofReal (chebF c N (Real.cos θ)))
      (ENNReal.measurable_ofReal.comp (continuous_chebF_cos c N).measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hpos _ (cos_mem θ))]

/-- On `[-1, 1]` the elliptic coordinate `c` is `1`. -/
theorem jc_ofReal {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : jc (x : ℂ) = 1 := by
  unfold jc
  have e1 : ‖(x : ℂ) - 1‖ = 1 - x := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2])]; ring
  have e2 : ‖(x : ℂ) + 1‖ = x + 1 := by
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
  rw [e1, e2]; ring

theorem sub_ofReal_ne_zero {ζ : ℂ} (h : 1 < jc ζ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ζ - (x : ℂ) ≠ 0 := by
  intro h0
  rw [sub_eq_zero.1 h0, jc_ofReal hx] at h
  exact lt_irrefl _ h

/-- The Chebyshev expansion of `log |ζ - x|` off `[-1, 1]`:
`log (|φ|/2) - log |ζ - x| = Σ_{k ≥ 1} (2/k) Re(φ^{-k}) T_k(x)`. -/
theorem hasSum_log_jphi {ζ : ℂ} (h : 1 < jc ζ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => (2 * ((jphi ζ ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ)) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)
      (Real.log (jR ζ / 2) - Real.log ‖ζ - x‖) := by
  have hφ := (jphi_spec h).1
  have hφ0 := jphi_ne_zero h
  set φ := jphi ζ with hφd
  set w := φ⁻¹ with hw
  have hwn : ‖w‖ < 1 := by rw [hw, norm_inv]; exact inv_lt_one_of_one_lt₀ hφ
  have hb := barrier_hasSum_chebyshev_log (x := x) (z := w) (abs_le.2 hx) hwn
  have hre := Complex.hasSum_re hb
  -- `ζ - x = (φ/2) (1 - 2 x w + w²)`
  have hfac : ζ - (x : ℂ) = φ / 2 * (1 - 2 * (x : ℂ) * w + w ^ 2) := by
    have hs := (jphi_spec h).2
    rw [← hφd] at hs
    rw [← hs]; unfold jJ; rw [hw]; field_simp; ring
  have hne := sub_ofReal_ne_zero h hx
  have hQ : (1 - 2 * (x : ℂ) * w + w ^ 2) ≠ 0 := by
    intro h0; apply hne; rw [hfac, h0, mul_zero]
  have hR : jR ζ = ‖φ‖ := jR_eq_norm h
  have hlog : Real.log ‖ζ - (x : ℂ)‖ = Real.log (jR ζ / 2) + Real.log ‖1 - 2 * (x : ℂ) * w + w ^ 2‖ := by
    rw [hfac, norm_mul, norm_div, Complex.norm_two, hR,
      Real.log_mul (by positivity) (norm_ne_zero_iff.2 hQ)]
  have e2 : ((-(1 / 2 : ℂ)) * Complex.log (1 - 2 * (x : ℂ) * w + w ^ 2)).re =
      -(1 / 2) * Real.log ‖1 - 2 * (x : ℂ) * w + w ^ 2‖ := by
    simp [Complex.log_re]
  rw [e2] at hre
  have h2 := hre.mul_left 2
  convert h2 using 1
  · funext k
    rw [hw, inv_pow]
    have : (w ^ (k + 1) * Complex.ofReal ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) /
        ((k + 1 : ℕ) : ℂ)).re = (w ^ (k + 1)).re * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
          ((k + 1 : ℕ) : ℝ) := by
      rw [show ((k + 1 : ℕ) : ℂ) = (((k + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.div_ofReal_re, Complex.re_mul_ofReal]
    rw [hw, inv_pow] at this
    rw [this]; ring
  · rw [hlog]; ring

theorem summable_abs_coef {ζ : ℂ} (h : 1 < jc ζ) :
    Summable fun k : ℕ => |2 * ((jphi ζ ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ)| := by
  have hφ := (jphi_spec h).1
  have hφ0 := jphi_ne_zero h
  set r := ‖jphi ζ‖⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.2 (norm_nonneg _)
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hφ
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r))
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  rw [abs_div, abs_mul, abs_two, Nat.abs_cast, div_le_iff₀ (by linarith)]
  have h1 : |((jphi ζ ^ (k + 1))⁻¹).re| ≤ r ^ (k + 1) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_inv, norm_pow, hr, inv_pow]
  have h2 : 0 ≤ r ^ (k + 1) := pow_nonneg hr0 _
  have h3 : (2 * r) * r ^ k = 2 * r ^ (k + 1) := by ring
  rw [h3]
  nlinarith

/-- **L2 at complex points (LD12), transported to the segment (W3(a)).**  For `h ≠ 0`,
`f = Σ_{k ≤ N} c_k T_k ≥ 0` on `[-1, 1]` and `ζ = (s - M)/h` off `[-1, 1]`:
`U^ν(s) = -c₀ log |h| - c₀ log(|φ|/2) + Σ_{k=1}^N (c_k/k) Re φ^{-k}`, with `φ = jphi ζ`,
`|φ| = jR ζ` (real operations only, W2). -/
theorem logPotC_segMeasure {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    logPotC (segMeasure M h c N) s =
      -c 0 * Real.log ‖h‖ - c 0 * Real.log (jR ((s - M) / h) / 2) +
        ∑ k ∈ Finset.range N, c (k + 1) * ((jphi ((s - M) / h) ^ (k + 1))⁻¹).re /
          ((k + 1 : ℕ) : ℝ) := by
  set ζ := (s - M) / h with hζ
  have hsplit : ∀ θ : ℝ, Real.log ‖s - (M + h * (Real.cos θ : ℂ))‖ =
      Real.log ‖h‖ + Real.log ‖ζ - (Real.cos θ : ℂ)‖ := by
    intro θ
    have e : s - (M + h * (Real.cos θ : ℂ)) = h * (ζ - (Real.cos θ : ℂ)) := by
      rw [hζ]; field_simp; ring
    rw [e, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hh)
      (norm_ne_zero_iff.2 (sub_ofReal_ne_zero hs (cos_mem θ)))]
  have hmeas : Measurable fun u : ℂ => Real.log ‖s - u‖ :=
    Real.measurable_log.comp (by fun_prop)
  unfold logPotC
  rw [integral_segMeasure hpos hmeas]
  simp_rw [hsplit]
  have key := integral_chebF_mul_series c N (summable_abs_coef hs)
    (fun θ => hasSum_log_jphi hs (cos_mem θ))
  -- integrability of `f · log |ζ - cos θ|`
  have hcont : Continuous fun θ : ℝ => chebF c N (Real.cos θ) *
      Real.log ‖ζ - (Real.cos θ : ℂ)‖ := by
    refine (continuous_chebF_cos c N).mul (Continuous.log (by fun_prop) fun θ => ?_)
    exact norm_ne_zero_iff.2 (sub_ofReal_ne_zero hs (cos_mem θ))
  have hg : ContinuousOn (fun x : ℝ => chebF c N x * Real.log ‖ζ - (x : ℂ)‖) (Icc (-1) 1) :=
    (continuous_chebF c N).continuousOn.mul (ContinuousOn.log (by fun_prop)
      fun x hx => norm_ne_zero_iff.2 (sub_ofReal_ne_zero hs hx))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hint : Integrable (fun θ : ℝ => chebF c N (Real.cos θ) *
      Real.log ‖ζ - (Real.cos θ : ℂ)‖) arc :=
    integrable_arc_of_bound hcont (fun θ => by simpa [Real.norm_eq_abs] using hC _ (cos_mem θ))
  rw [show (fun θ : ℝ => chebF c N (Real.cos θ) * (Real.log ‖h‖ +
      Real.log ‖ζ - (Real.cos θ : ℂ)‖)) = fun θ => Real.log ‖h‖ * chebF c N (Real.cos θ) +
      chebF c N (Real.cos θ) * Real.log ‖ζ - (Real.cos θ : ℂ)‖ from funext fun θ => by ring]
  rw [integral_add ((integrable_chebF c N).const_mul _) hint, integral_const_mul, integral_chebF]
  rw [show (fun θ : ℝ => chebF c N (Real.cos θ) * (Real.log (jR ζ / 2) -
      Real.log ‖ζ - (Real.cos θ : ℂ)‖)) = fun θ => Real.log (jR ζ / 2) * chebF c N (Real.cos θ) -
      chebF c N (Real.cos θ) * Real.log ‖ζ - (Real.cos θ : ℂ)‖ from funext fun θ => by ring]
    at key
  rw [integral_sub ((integrable_chebF c N).const_mul _) hint, integral_const_mul,
    integral_chebF] at key
  have e3 : ∑ k ∈ Finset.range N, 2 * ((jphi ζ ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ) * c (k + 1) / 2 =
      ∑ k ∈ Finset.range N, c (k + 1) * ((jphi ζ ^ (k + 1))⁻¹).re / ((k + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [e3] at key
  linarith

end

end CatalanCore.Tools.Joukowski
end J2

section J3
open Complex Polynomial MeasureTheory Set CatalanCore.Zeta5.Potential OAI.InternalCatalan

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-! ### The Stieltjes transform of a segment measure (W3(b)): closed form -/

/-- Integration of a `ℂ`-valued function against the segment measure. -/
theorem integral_segMeasure_C {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {g : ℂ → ℂ} (hg : Measurable g) :
    ∫ u, g u ∂(segMeasure M h c N) =
      ∫ θ, (chebF c N (Real.cos θ) : ℂ) * g (M + h * (Real.cos θ : ℂ)) ∂arc := by
  unfold segMeasure
  rw [integral_map (continuous_segMap M h).measurable.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun θ => ENNReal.ofReal (chebF c N (Real.cos θ)))
      (ENNReal.measurable_ofReal.comp (continuous_chebF_cos c N).measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (hpos _ (cos_mem θ))]

/-- The Poisson kernel: `q/(ζ - x) - 1 = Σ_{k ≥ 1} 2 φ^{-k} T_k(x)` for `x ∈ [-1, 1]`. -/
theorem poisson_hasSum {ζ : ℂ} (h : 1 < jc ζ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * (jphi ζ)⁻¹ ^ (k + 1) *
      (((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x : ℝ) : ℂ))
      (jq ζ / (ζ - (x : ℂ)) - 1) := by
  have hφ := (jphi_spec h).1
  have hφ0 := jphi_ne_zero h
  set φ := jphi ζ with hφd
  set w := φ⁻¹ with hw
  have hwn : ‖w‖ < 1 := by rw [hw, norm_inv]; exact inv_lt_one_of_one_lt₀ hφ
  obtain ⟨θ, rfl⟩ : ∃ θ : ℝ, Real.cos θ = x := ⟨Real.arccos x, Real.cos_arccos hx.1 hx.2⟩
  set a : ℂ := w * Complex.exp (θ * I) with ha
  set b : ℂ := w * Complex.exp (-(θ * I)) with hb
  have han : ‖a‖ < 1 := by
    rw [ha, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; exact hwn
  have hbn : ‖b‖ < 1 := by
    have e : Complex.exp (-(θ * I)) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by push_cast; ring_nf
    rw [hb, norm_mul, e, Complex.norm_exp_ofReal_mul_I, mul_one]; exact hwn
  have hA := (hasSum_geometric_of_norm_lt_one han).mul_left a
  have hB := (hasSum_geometric_of_norm_lt_one hbn).mul_left b
  have hAB := hA.add hB
  have hfac : ζ - ((Real.cos θ : ℝ) : ℂ) = φ / 2 * (1 - 2 * ((Real.cos θ : ℝ) : ℂ) * w + w ^ 2) := by
    have hs := (jphi_spec h).2
    rw [← hφd] at hs
    rw [← hs]; unfold jJ; rw [hw]; field_simp; ring
  have hne := sub_ofReal_ne_zero h (cos_mem θ)
  have hE : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by rw [← Complex.exp_add]; simp
  have hcos : ((Real.cos θ : ℝ) : ℂ) = (Complex.exp (θ * I) + Complex.exp (-(θ * I))) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]; ring_nf
  have hne1 : 1 - a ≠ 0 := by
    intro h0; have : a = 1 := by linear_combination -h0
    rw [this] at han; simp at han
  have hne2 : 1 - b ≠ 0 := by
    intro h0; have : b = 1 := by linear_combination -h0
    rw [this] at hbn; simp at hbn
  have e1 : ∀ n : ℕ, Complex.exp (θ * I) ^ n = Complex.exp (((n : ℝ) * θ : ℝ) * I) := by
    intro n; rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have e2 : ∀ n : ℕ, Complex.exp (-(θ * I)) ^ n = Complex.exp (-(((n : ℝ) * θ : ℝ) * I)) := by
    intro n; rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  convert hAB using 1
  · funext k
    rw [Chebyshev.T_real_cos]
    simp only [Int.cast_natCast, Polynomial.eval_comp]
    rw [← pow_succ' a k, ← pow_succ' b k, ha, hb, mul_pow, mul_pow, e1, e2, Complex.ofReal_cos,
      Complex.cos]
    push_cast
    ring_nf
  · have hfac2 : 1 - 2 * ((Real.cos θ : ℝ) : ℂ) * w + w ^ 2 = (1 - a) * (1 - b) := by
      rw [hcos, ha, hb]; linear_combination (-w ^ 2) * hE
    rw [hfac, hfac2]
    have hab : a * b = w ^ 2 := by rw [ha, hb]; linear_combination w ^ 2 * hE
    have hwφ : w * φ = 1 := by rw [hw]; field_simp
    have hjq : jq ζ = (φ - w) / 2 := by unfold jq; rw [← hφd]
    rw [hjq]
    have hφw : φ - w = φ * (1 - w ^ 2) := by linear_combination w * hwφ
    have h3 : (φ - w) / 2 / (φ / 2 * ((1 - a) * (1 - b))) = (1 - w ^ 2) / ((1 - a) * (1 - b)) := by
      rw [hφw]; field_simp
    rw [h3]
    field_simp
    linear_combination hab

/-- Bounded continuous functions of `θ` are integrable for the arcsine law. -/
theorem integrable_arc_C {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ θ, ‖g θ‖ ≤ C) :
    Integrable g arc :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable (ae_of_all _ hC)

theorem summable_re_pow {w : ℂ} (hw : ‖w‖ < 1) :
    Summable fun k : ℕ => |2 * (w ^ (k + 1)).re| := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left (2 * ‖w‖))
  rw [abs_mul, abs_two]
  have h1 : |(w ^ (k + 1)).re| ≤ ‖w‖ ^ (k + 1) :=
    (Complex.abs_re_le_norm _).trans (by rw [norm_pow])
  calc 2 * |(w ^ (k + 1)).re| ≤ 2 * ‖w‖ ^ (k + 1) := by linarith
    _ = 2 * ‖w‖ * ‖w‖ ^ k := by ring

theorem summable_im_pow {w : ℂ} (hw : ‖w‖ < 1) :
    Summable fun k : ℕ => |2 * (w ^ (k + 1)).im| := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left (2 * ‖w‖))
  rw [abs_mul, abs_two]
  have h1 : |(w ^ (k + 1)).im| ≤ ‖w‖ ^ (k + 1) :=
    (Complex.abs_im_le_norm _).trans (by rw [norm_pow])
  calc 2 * |(w ^ (k + 1)).im| ≤ 2 * ‖w‖ ^ (k + 1) := by linarith
    _ = 2 * ‖w‖ * ‖w‖ ^ k := by ring

/-- The Poisson integrand is bounded on `[-1, 1]`. -/
theorem poisson_bdd {ζ : ℂ} (h : 1 < jc ζ) (c : ℕ → ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ θ : ℝ, ‖(chebF c N (Real.cos θ) : ℂ) *
      (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1)‖ ≤ C := by
  have hg : ContinuousOn (fun x : ℝ => (chebF c N x : ℂ) * (jq ζ / (ζ - (x : ℂ)) - 1))
      (Icc (-1) 1) :=
    (Complex.continuous_ofReal.comp (continuous_chebF c N)).continuousOn.mul
      ((continuousOn_const.div (by fun_prop) fun x hx => sub_ofReal_ne_zero h hx).sub
        continuousOn_const)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact ⟨C, fun θ => hC _ (cos_mem θ)⟩

/-- `∫ f · (q/(ζ - x) - 1) dω = Σ_{k ≥ 1} c_k φ^{-k}`. -/
theorem integral_chebF_poisson {ζ : ℂ} (h : 1 < jc ζ) (c : ℕ → ℝ) (N : ℕ) :
    ∫ θ, (chebF c N (Real.cos θ) : ℂ) * (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1) ∂arc =
      ∑ k ∈ Finset.range N, (c (k + 1) : ℂ) * (jphi ζ)⁻¹ ^ (k + 1) := by
  have hφ := (jphi_spec h).1
  have hwn : ‖(jphi ζ)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hφ
  obtain ⟨C, hC⟩ := poisson_bdd h c N
  have hcont : Continuous fun θ : ℝ => (chebF c N (Real.cos θ) : ℂ) *
      (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1) := by
    refine (Complex.continuous_ofReal.comp (continuous_chebF_cos c N)).mul
      ((continuous_const.div (by fun_prop) fun θ => sub_ofReal_ne_zero h (cos_mem θ)).sub
        continuous_const)
  have hint := integrable_arc_C hcont hC
  apply Complex.ext
  · have hre := integral_re hint
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    have hs : ∀ θ : ℝ, HasSum (fun k : ℕ => (2 * ((jphi ζ)⁻¹ ^ (k + 1)).re) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))
        (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1).re := by
      intro θ
      have := Complex.hasSum_re (poisson_hasSum h (cos_mem θ))
      convert this using 2 with k
      rw [Complex.re_mul_ofReal, Complex.mul_re]; norm_num
    have key := integral_chebF_mul_series c N (summable_re_pow hwn) hs
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [key, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re]; ring
  · have him := integral_im hint
    simp only [RCLike.im_to_complex] at him
    rw [← him]
    have hs : ∀ θ : ℝ, HasSum (fun k : ℕ => (2 * ((jphi ζ)⁻¹ ^ (k + 1)).im) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))
        (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1).im := by
      intro θ
      have := Complex.hasSum_im (poisson_hasSum h (cos_mem θ))
      convert this using 2 with k
      rw [Complex.im_mul_ofReal, Complex.mul_im]; norm_num
    have key := integral_chebF_mul_series c N (summable_im_pow hwn) hs
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [key, Complex.im_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_im]; ring

/-- **W3(b), closed form of the Stieltjes transform.**  For `ζ = (s - M)/h` off `[-1, 1]`,
`∫ (s - u)⁻¹ dν(u) = (h q)⁻¹ (c₀ + Σ_{k ≥ 1} c_k φ^{-k})`, i.e. `G′ = -F(φ)/(h q)`. -/
theorem stieltjes_segMeasure {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    ∫ u, (s - u)⁻¹ ∂(segMeasure M h c N) =
      (h * jq ((s - M) / h))⁻¹ *
        ((c 0 : ℂ) + ∑ k ∈ Finset.range N, (c (k + 1) : ℂ) * (jphi ((s - M) / h))⁻¹ ^ (k + 1)) := by
  set ζ := (s - M) / h with hζ
  have hq0 := jq_ne_zero hs
  have hmeas : Measurable fun u : ℂ => (s - u)⁻¹ := by fun_prop
  rw [integral_segMeasure_C hpos hmeas]
  have hpt : ∀ θ : ℝ, (chebF c N (Real.cos θ) : ℂ) * (s - (M + h * (Real.cos θ : ℂ)))⁻¹ =
      (h * jq ζ)⁻¹ * ((chebF c N (Real.cos θ) : ℂ) +
        (chebF c N (Real.cos θ) : ℂ) * (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1)) := by
    intro θ
    have hne := sub_ofReal_ne_zero hs (cos_mem θ)
    have e : s - (M + h * (Real.cos θ : ℂ)) = h * (ζ - (Real.cos θ : ℂ)) := by
      rw [hζ]; field_simp; ring
    rw [e]
    field_simp
    ring
  simp_rw [hpt]
  obtain ⟨C, hC⟩ := poisson_bdd hs c N
  have hcont : Continuous fun θ : ℝ => (chebF c N (Real.cos θ) : ℂ) *
      (jq ζ / (ζ - ((Real.cos θ : ℝ) : ℂ)) - 1) := by
    refine (Complex.continuous_ofReal.comp (continuous_chebF_cos c N)).mul
      ((continuous_const.div (by fun_prop) fun θ => sub_ofReal_ne_zero hs (cos_mem θ)).sub
        continuous_const)
  have hint := integrable_arc_C hcont hC
  have hint0 : Integrable (fun θ : ℝ => (chebF c N (Real.cos θ) : ℂ)) arc :=
    (integrable_chebF c N).ofReal
  have hof := integral_complex_ofReal (μ := arc) (f := fun θ : ℝ => chebF c N (Real.cos θ))
  rw [integral_const_mul, integral_add hint0 hint, integral_chebF_poisson hs c N, hof,
    integral_chebF]

end

end CatalanCore.Tools.Joukowski
end J3

section J4
open Complex Polynomial MeasureTheory Set Metric Filter Topology
  CatalanCore.Zeta5.Potential OAI.InternalCatalan

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-! ### W3(c): the harmonic tower of a Stieltjes-type integral over the arcsine law

Generic in the weight `w`, the curve `p` and the exponent: `stA w p m s = ∫ w θ (s - p θ)^{-m} dω(θ)`. -/

/-- The `m`-th Stieltjes-type integral of a weighted curve against the arcsine law. -/
def stA (w p : ℝ → ℂ) (m : ℕ) (s : ℂ) : ℂ := ∫ θ, w θ * ((s - p θ) ^ m)⁻¹ ∂arc

/-- `‖stA‖ ≤ (∫ g)/d^m` when `‖w‖ ≤ g` and the curve stays at distance `≥ d` from `s`. -/
theorem norm_stA_le {w p : ℝ → ℂ} {g : ℝ → ℝ} (hg : Integrable g arc)
    (hwg : ∀ θ, ‖w θ‖ ≤ g θ) {s : ℂ} {d : ℝ} (hd0 : 0 < d) (hd : ∀ θ, d ≤ ‖s - p θ‖) (m : ℕ) :
    ‖stA w p m s‖ ≤ (∫ θ, g θ ∂arc) / d ^ m := by
  unfold stA
  have hb : ∀ θ, ‖w θ * ((s - p θ) ^ m)⁻¹‖ ≤ g θ / d ^ m := by
    intro θ
    rw [norm_mul, norm_inv, norm_pow, div_eq_mul_inv]
    refine mul_le_mul (hwg θ) ?_ (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _))
      ((norm_nonneg _).trans (hwg θ))
    exact inv_anti₀ (pow_pos hd0 m) (pow_le_pow_left₀ hd0.le (hd θ) m)
  calc ‖∫ θ, w θ * ((s - p θ) ^ m)⁻¹ ∂arc‖
      ≤ ∫ θ, g θ / d ^ m ∂arc :=
        norm_integral_le_of_norm_le (hg.div_const _) (ae_of_all _ hb)
    _ = (∫ θ, g θ ∂arc) / d ^ m := integral_div _ _

/-- **W3(c), differentiation under the integral:** `d/ds stA m = -m · stA (m + 1)`. -/
theorem hasDerivAt_stA {w p : ℝ → ℂ} (hw : Measurable w) (hp : Measurable p) {W : ℝ}
    (hW : ∀ θ, ‖w θ‖ ≤ W) {s : ℂ} {d : ℝ} (hd0 : 0 < d) (hd : ∀ θ, d ≤ ‖s - p θ‖) (m : ℕ) :
    HasDerivAt (stA w p m) (-(m : ℂ) * stA w p (m + 1) s) s := by
  have hd2 : ∀ θ, ∀ x ∈ ball s (d / 2), d / 2 ≤ ‖x - p θ‖ := by
    intro θ x hx
    have h1 : ‖s - x‖ < d / 2 := by rw [← dist_eq_norm]; rw [dist_comm]; exact mem_ball.1 hx
    have h2 := hd θ
    have : s - p θ = (s - x) + (x - p θ) := by ring
    have h3 : ‖s - p θ‖ ≤ ‖s - x‖ + ‖x - p θ‖ := by rw [this]; exact norm_add_le _ _
    linarith
  have hmeas : ∀ (k : ℕ) (x : ℂ), Measurable fun θ => w θ * ((x - p θ) ^ k)⁻¹ := fun k x =>
    hw.mul ((measurable_const.sub hp).pow_const k).inv
  set F : ℂ → ℝ → ℂ := fun x θ => w θ * ((x - p θ) ^ m)⁻¹ with hF
  set F' : ℂ → ℝ → ℂ := fun x θ => w θ * (-(m : ℂ) * ((x - p θ) ^ (m + 1))⁻¹) with hF'
  have hbF : ∀ θ, ‖F s θ‖ ≤ W / d ^ m := by
    intro θ
    simp only [hF]
    rw [norm_mul, norm_inv, norm_pow, div_eq_mul_inv]
    refine mul_le_mul (hW θ) ?_ (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _))
      ((norm_nonneg _).trans (hW θ))
    exact inv_anti₀ (pow_pos hd0 m) (pow_le_pow_left₀ hd0.le (hd θ) m)
  have hint : Integrable (F s) arc :=
    Integrable.mono' (integrable_const (W / d ^ m)) (hmeas m s).aestronglyMeasurable
      (ae_of_all _ hbF)
  have hbF' : ∀ θ, ∀ x ∈ ball s (d / 2), ‖F' x θ‖ ≤ W * m / (d / 2) ^ (m + 1) := by
    intro θ x hx
    simp only [hF']
    rw [norm_mul, norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 : (‖x - p θ‖ ^ (m + 1))⁻¹ ≤ ((d / 2) ^ (m + 1))⁻¹ :=
      inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) (hd2 θ x hx) _)
    calc ‖w θ‖ * ((m : ℝ) * (‖x - p θ‖ ^ (m + 1))⁻¹)
        ≤ W * ((m : ℝ) * ((d / 2) ^ (m + 1))⁻¹) :=
          mul_le_mul (hW θ) (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m))
            (mul_nonneg (Nat.cast_nonneg m) (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _)))
            ((norm_nonneg _).trans (hW θ))
      _ = W * m / (d / 2) ^ (m + 1) := by rw [div_eq_mul_inv]; ring
  have hdiff : ∀ θ, ∀ x ∈ ball s (d / 2), HasDerivAt (fun x => F x θ) (F' x θ) x := by
    intro θ x hx
    have hne : x - p θ ≠ 0 := by
      intro h0
      have := hd2 θ x hx
      rw [h0, norm_zero] at this; linarith
    have h1 : HasDerivAt (fun y : ℂ => (y - p θ) ^ m) ((m : ℂ) * (x - p θ) ^ (m - 1)) x :=
      ((hasDerivAt_pow m (x - p θ)).comp x ((hasDerivAt_id x).sub_const (p θ))).congr_deriv
        (by ring)
    have h2 := (h1.inv (pow_ne_zero m hne)).const_mul (w θ)
    convert h2 using 1
    rcases m with _ | m
    · simp [hF']
    · simp only [hF', Nat.add_sub_cancel]
      field_simp
      ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := arc) (F := F) (F' := F')
    (s := ball s (d / 2)) (x₀ := s) (bound := fun _ => W * m / (d / 2) ^ (m + 1)) (ball_mem_nhds s (half_pos hd0))
    (Eventually.of_forall fun x => (hmeas m x).aestronglyMeasurable) hint
    (by
      refine (hw.mul (measurable_const.mul ((measurable_const.sub hp).pow_const (m + 1)).inv)).aestronglyMeasurable)
    (ae_of_all _ hbF') (integrable_const _) (ae_of_all _ hdiff)
  refine (this.2).congr_deriv ?_
  unfold stA
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [hF']
  ring

/-- **W3(d), distance to the segment:** `‖s - (M + h x)‖ ≥ |h| (c(ζ) - 1)` for `x ∈ [-1, 1]`. -/
theorem norm_sub_seg_ge {M h : ℂ} {s : ℂ} (hh : h ≠ 0) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖h‖ * (jc ((s - M) / h) - 1) ≤ ‖s - (M + h * (x : ℂ))‖ := by
  set ζ := (s - M) / h with hζ
  have e : s - (M + h * (x : ℂ)) = h * (ζ - (x : ℂ)) := by rw [hζ]; field_simp; ring
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e1 : ‖(x : ℂ) - 1‖ = 1 - x := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2])]; ring
  have e2 : ‖(x : ℂ) + 1‖ = x + 1 := by
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
  have t1 : ‖ζ - 1‖ ≤ ‖ζ - (x : ℂ)‖ + ‖(x : ℂ) - 1‖ := by
    calc ‖ζ - 1‖ = ‖(ζ - (x : ℂ)) + ((x : ℂ) - 1)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have t2 : ‖ζ + 1‖ ≤ ‖ζ - (x : ℂ)‖ + ‖(x : ℂ) + 1‖ := by
    calc ‖ζ + 1‖ = ‖(ζ - (x : ℂ)) + ((x : ℂ) + 1)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  unfold jc
  rw [e1] at t1; rw [e2] at t2
  linarith

end

end CatalanCore.Tools.Joukowski
end J4

section J5
open Complex Polynomial MeasureTheory Set Metric Filter Topology
  CatalanCore.Zeta5.Potential OAI.InternalCatalan

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-! ### W3(b)+(c)+(d) for the segment measure `ν = f dω` on `{M + h x : |x| ≤ 1}` -/

/-- `Sₘ(s) = ∫ (s - u)^{-m} dν(u)`. -/
def segSt (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) (m : ℕ) (s : ℂ) : ℂ :=
  ∫ u, ((s - u) ^ m)⁻¹ ∂(segMeasure M h c N)

theorem segSt_eq_stA {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (m : ℕ) (s : ℂ) :
    segSt M h c N m s = stA (fun θ => (chebF c N (Real.cos θ) : ℂ))
      (fun θ => M + h * (Real.cos θ : ℂ)) m s := by
  unfold segSt stA
  have hmeas : Measurable fun u : ℂ => ((s - u) ^ m)⁻¹ := by fun_prop
  exact integral_segMeasure_C hpos hmeas

theorem seg_dist_pos {M h : ℂ} (hh : h ≠ 0) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    0 < ‖h‖ * (jc ((s - M) / h) - 1) :=
  mul_pos (norm_pos_iff.2 hh) (by linarith)

/-- **W3(c)**: `d/ds Sₘ = -m S_{m+1}` off the segment. -/
theorem hasDerivAt_segSt {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) (m : ℕ) :
    HasDerivAt (segSt M h c N m) (-(m : ℂ) * segSt M h c N (m + 1) s) s := by
  have hfun : segSt M h c N m = stA (fun θ => (chebF c N (Real.cos θ) : ℂ))
      (fun θ => M + h * (Real.cos θ : ℂ)) m := funext (segSt_eq_stA hpos m)
  rw [hfun, segSt_eq_stA hpos]
  exact hasDerivAt_stA (Complex.measurable_ofReal.comp (continuous_chebF_cos c N).measurable)
    (by fun_prop)
    (W := ∑ k ∈ Finset.range (N + 1), |c k|)
    (fun θ => by
      simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
      exact abs_chebF_le c N (cos_mem θ))
    (seg_dist_pos hh hs) (fun θ => norm_sub_seg_ge hh (cos_mem θ)) m

/-- **W3(c)**: `‖Sₘ(s)‖ ≤ c₀ / dist^m`, `dist = |h|(c(ζ) - 1)`. -/
theorem norm_segSt_le {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) (m : ℕ) :
    ‖segSt M h c N m s‖ ≤ c 0 / (‖h‖ * (jc ((s - M) / h) - 1)) ^ m := by
  rw [segSt_eq_stA hpos]
  have := norm_stA_le (w := fun θ => (chebF c N (Real.cos θ) : ℂ))
    (p := fun θ => M + h * (Real.cos θ : ℂ)) (g := fun θ => chebF c N (Real.cos θ))
    (integrable_chebF c N)
    (fun θ => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _ (cos_mem θ))])
    (seg_dist_pos hh hs) (fun θ => norm_sub_seg_ge hh (cos_mem θ)) m
  rwa [integral_chebF] at this

/-- `S₁` is the closed form `(h q)⁻¹ F(φ)`. -/
theorem segSt_one {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h)) :
    segSt M h c N 1 s = (h * jq ((s - M) / h))⁻¹ *
      ((c 0 : ℂ) + ∑ k ∈ Finset.range N, (c (k + 1) : ℂ) * (jphi ((s - M) / h))⁻¹ ^ (k + 1)) := by
  unfold segSt
  simp only [pow_one]
  exact stieltjes_segMeasure hh hpos hs

end

end CatalanCore.Tools.Joukowski
end J5

section J6
open Complex Polynomial MeasureTheory Set Metric Filter Topology
  CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells OAI.InternalCatalan

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-! ### The Faà di Bruno tower along a complex curve (real variable, `ℂ`-valued)

`fdb` is the polynomial of `Zeta5/Cells/Compose` over the commutative ring `ℂ`; the tower lemma
and the majorant are re-proved here for `ℂ`-valued functions of a real variable (the `ℝ`-valued
statements there are left untouched, Rule Z1). -/

/-- The derivative tower of a composite `D ∘ γ`, `ℂ`-valued, for orders `1 ≤ j ≤ 4`: only
`D 1, …, D 4` and `Y 1, …, Y 4` enter, so the value slot `D 0` is never needed. -/
theorem hasDerivAt_fdbC {Dc Yc : ℕ → ℝ → ℂ} {x : ℝ}
    (hD : ∀ k, 1 ≤ k → k < 5 → HasDerivAt (Dc k) (Dc (k + 1) x * Yc 1 x) x)
    (hY : ∀ i, 1 ≤ i → i < 5 → HasDerivAt (Yc i) (Yc (i + 1) x) x) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j < 5) :
    HasDerivAt (fun z => fdb (fun k => Dc k z) (fun i => Yc i z) j)
      (fdb (fun k => Dc k x) (fun i => Yc i x) (j + 1)) x := by
  have d1 := hD 1 (by norm_num) (by norm_num)
  have d2 := hD 2 (by norm_num) (by norm_num)
  have d3 := hD 3 (by norm_num) (by norm_num)
  have d4 := hD 4 (by norm_num) (by norm_num)
  have y1 := hY 1 (by norm_num) (by norm_num)
  have y2 := hY 2 (by norm_num) (by norm_num)
  have y3 := hY 3 (by norm_num) (by norm_num)
  have y4 := hY 4 (by norm_num) (by norm_num)
  simp only [Nat.reduceAdd] at d1 d2 d3 d4 y1 y2 y3 y4
  interval_cases j
  · have h := d1.fun_mul y1
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)
  · have h := (d2.fun_mul (y1.fun_pow 2)).fun_add (d1.fun_mul y2)
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)
  · have h := ((d3.fun_mul (y1.fun_pow 3)).fun_add
      (((d2.const_mul 3).fun_mul y1).fun_mul y2)).fun_add (d1.fun_mul y3)
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)
  · have h := (((d4.fun_mul (y1.fun_pow 4)).fun_add
      (((d3.const_mul 6).fun_mul (y1.fun_pow 2)).fun_mul y2)).fun_add
      (d2.fun_mul (((y2.fun_pow 2).const_mul 3).fun_add ((y1.const_mul 4).fun_mul y3)))).fun_add
      (d1.fun_mul y4)
    exact h.congr_deriv (by simp only [fdb, Nat.reduceAdd]; ring)

/-- **The complex Faà di Bruno majorant**: `‖fdb D Y 5‖ ≤ fdbBound Dm Ym` from `‖D k‖ ≤ Dm k`,
`‖Y i‖ ≤ Ym i` (`1 ≤ k, i ≤ 5`).  Same shape as `abs_fdb5_le`. -/
theorem norm_fdb5_le (D Y : ℕ → ℂ) (Dm Ym : ℕ → ℝ) (hD : ∀ k, 1 ≤ k → k ≤ 5 → ‖D k‖ ≤ Dm k)
    (hY : ∀ i, 1 ≤ i → i ≤ 5 → ‖Y i‖ ≤ Ym i) : ‖fdb D Y 5‖ ≤ fdbBound Dm Ym := by
  have y1 := hY 1 (by norm_num) (by norm_num)
  have y2 := hY 2 (by norm_num) (by norm_num)
  have y3 := hY 3 (by norm_num) (by norm_num)
  have y4 := hY 4 (by norm_num) (by norm_num)
  have y5 := hY 5 (by norm_num) (by norm_num)
  have d1 := hD 1 (by norm_num) (by norm_num)
  have d2 := hD 2 (by norm_num) (by norm_num)
  have d3 := hD 3 (by norm_num) (by norm_num)
  have d4 := hD 4 (by norm_num) (by norm_num)
  have d5 := hD 5 (by norm_num) (by norm_num)
  have m : ∀ {a b : ℂ} {A B : ℝ}, ‖a‖ ≤ A → ‖b‖ ≤ B → ‖a * b‖ ≤ A * B := fun {a b A B} ha hb => by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
  have p : ∀ {a : ℂ} {A : ℝ}, ‖a‖ ≤ A → ∀ n : ℕ, ‖a ^ n‖ ≤ A ^ n := fun {a A} ha n => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ha n
  have c : ∀ (k : ℝ) {a : ℂ} {A : ℝ}, 0 ≤ k → ‖a‖ ≤ A → ‖(k : ℂ) * a‖ ≤ k * A := fun k {a} {A} hk0 ha => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_left ha hk0
  have t1 : ‖D 5 * Y 1 ^ 5‖ ≤ Dm 5 * Ym 1 ^ 5 := m d5 (p y1 5)
  have t2 : ‖(10 : ℂ) * D 4 * Y 1 ^ 3 * Y 2‖ ≤ 10 * Dm 4 * Ym 1 ^ 3 * Ym 2 := by
    have := m (m (c 10 (by norm_num) d4) (p y1 3)) y2
    simpa using this
  have i3 : ‖(15 : ℂ) * Y 1 * Y 2 ^ 2 + 10 * Y 1 ^ 2 * Y 3‖ ≤
      15 * Ym 1 * Ym 2 ^ 2 + 10 * Ym 1 ^ 2 * Ym 3 := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · simpa using m (c 15 (by norm_num) y1) (p y2 2)
    · simpa using m (c 10 (by norm_num) (p y1 2)) y3
  have t3 := m d3 i3
  have i4 : ‖(10 : ℂ) * Y 2 * Y 3 + 5 * Y 1 * Y 4‖ ≤ 10 * Ym 2 * Ym 3 + 5 * Ym 1 * Ym 4 := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · simpa using m (c 10 (by norm_num) y2) y3
    · simpa using m (c 5 (by norm_num) y1) y4
  have t4 := m d2 i4
  have t5 := m d1 y5
  have e : fdb D Y 5 = D 5 * Y 1 ^ 5 + 10 * D 4 * Y 1 ^ 3 * Y 2
      + D 3 * (15 * Y 1 * Y 2 ^ 2 + 10 * Y 1 ^ 2 * Y 3)
      + D 2 * (10 * Y 2 * Y 3 + 5 * Y 1 * Y 4) + D 1 * Y 5 := rfl
  rw [e]
  unfold fdbBound
  calc _ ≤ ‖D 5 * Y 1 ^ 5‖ + ‖(10 : ℂ) * D 4 * Y 1 ^ 3 * Y 2‖ +
        ‖D 3 * ((15 : ℂ) * Y 1 * Y 2 ^ 2 + 10 * Y 1 ^ 2 * Y 3)‖ +
        ‖D 2 * ((10 : ℂ) * Y 2 * Y 3 + 5 * Y 1 * Y 4)‖ + ‖D 1 * Y 5‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
    _ ≤ _ := by linarith

end

end CatalanCore.Tools.Joukowski
end J6

section J7
open Complex Polynomial MeasureTheory Set Metric Filter Topology
  CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells OAI.InternalCatalan

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-! ### The first derivative of a logarithmic potential along a real curve -/

/-- `x ↦ log ‖z(x)‖` has derivative `Re(z'/z)` where `z ≠ 0`. -/
theorem hasDerivAt_log_norm {z : ℝ → ℂ} {z' : ℂ} {x : ℝ} (h : HasDerivAt z z' x) (hz : z x ≠ 0) :
    HasDerivAt (fun y => Real.log ‖z y‖) ((z' / z x).re) x := by
  have hn : ‖z x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  have h1 := h.norm_sq
  have h2 := (h1.log hn).const_mul (1 / 2 : ℝ)
  have e : ∀ y, Real.log ‖z y‖ = (1 / 2 : ℝ) * Real.log (‖z y‖ ^ 2) := by
    intro y
    rw [Real.log_pow]; push_cast; ring
  rw [show (fun y => Real.log ‖z y‖) = fun y => (1 / 2 : ℝ) * Real.log (‖z y‖ ^ 2) from funext e]
  refine h2.congr_deriv ?_
  rw [Complex.inner]
  have hnz : ‖z x‖ ^ 2 = Complex.normSq (z x) := by rw [Complex.sq_norm]
  rw [hnz, Complex.div_re]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im]
  have hd : (z x).re * (z x).re + (z x).im * (z x).im ≠ 0 := by
    have := Complex.normSq_pos.2 hz
    rw [Complex.normSq_apply] at this; exact this.ne'
  field_simp
  ring

/-- The potential `-∫ w(θ) log ‖s - p(θ)‖ dω(θ)` of a weighted curve. -/
def ugC (w : ℝ → ℝ) (p : ℝ → ℂ) (s : ℂ) : ℝ := -∫ θ, w θ * Real.log ‖s - p θ‖ ∂arc

/-- **First derivative of a logarithmic potential along a real curve** (W3, the link between the
real field `U` and the Stieltjes tower `S`): `d/dt U(γ t) = -Re(γ'(t) S(γ t))`. -/
theorem hasDerivAt_ugC {w : ℝ → ℝ} {p : ℝ → ℂ} (hw : Measurable w) (hp : Measurable p) {W P : ℝ}
    (hW : ∀ θ, |w θ| ≤ W) (hP : ∀ θ, ‖p θ‖ ≤ P) {γ γd : ℝ → ℂ} {t ε : ℝ} (hε : 0 < ε)
    {B d : ℝ} (hd0 : 0 < d) (hγ : ∀ x ∈ ball t ε, HasDerivAt γ (γd x) x)
    (hB : ∀ x ∈ ball t ε, ‖γd x‖ ≤ B) (hdist : ∀ x ∈ ball t ε, ∀ θ, d ≤ ‖γ x - p θ‖) :
    HasDerivAt (fun x => ugC w p (γ x))
      (-((γd t * stA (fun θ => (w θ : ℂ)) p 1 (γ t)).re)) t := by
  have ht : t ∈ ball t ε := mem_ball_self hε
  set F : ℝ → ℝ → ℝ := fun x θ => w θ * Real.log ‖γ x - p θ‖ with hF
  set F' : ℝ → ℝ → ℝ := fun x θ => w θ * (γd x / (γ x - p θ)).re with hF'
  have hmeasF : ∀ x, Measurable (F x) := fun x =>
    hw.mul (Real.measurable_log.comp (measurable_const.sub hp).norm)
  -- integrability of `F t`
  have hlogb : ∀ θ, |Real.log ‖γ t - p θ‖| ≤ |Real.log d| + |Real.log (‖γ t‖ + P + 1)| := by
    intro θ
    have h1 := hdist t ht θ
    have h2 : ‖γ t - p θ‖ ≤ ‖γ t‖ + P + 1 := by
      have := norm_sub_le (γ t) (p θ)
      linarith [hP θ]
    have h3 : Real.log d ≤ Real.log ‖γ t - p θ‖ := Real.log_le_log hd0 h1
    have h4 : Real.log ‖γ t - p θ‖ ≤ Real.log (‖γ t‖ + P + 1) :=
      Real.log_le_log (hd0.trans_le h1) h2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log d), le_abs_self (Real.log (‖γ t‖ + P + 1)),
      abs_nonneg (Real.log d), abs_nonneg (Real.log (‖γ t‖ + P + 1)), le_abs_self (Real.log d),
      neg_abs_le (Real.log (‖γ t‖ + P + 1))]
  have hint : Integrable (F t) arc :=
    Integrable.mono' (integrable_const (W * (|Real.log d| + |Real.log (‖γ t‖ + P + 1)|)))
      (hmeasF t).aestronglyMeasurable
      (ae_of_all _ fun θ => by
        simp only [hF, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hW θ) (hlogb θ) (abs_nonneg _) ((abs_nonneg _).trans (hW θ)))
  have hdiff : ∀ θ, ∀ x ∈ ball t ε, HasDerivAt (fun x => F x θ) (F' x θ) x := by
    intro θ x hx
    have hz : γ x - p θ ≠ 0 := by
      intro h0
      have := hdist x hx θ
      rw [h0, norm_zero] at this; linarith
    have := hasDerivAt_log_norm (((hγ x hx).sub_const (p θ))) hz
    exact this.const_mul (w θ)
  have hbound : ∀ θ, ∀ x ∈ ball t ε, ‖F' x θ‖ ≤ W * (B / d) := by
    intro θ x hx
    simp only [hF', Real.norm_eq_abs, abs_mul]
    have h1 : |(γd x / (γ x - p θ)).re| ≤ B / d := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_div]
      exact div_le_div₀ ((norm_nonneg _).trans (hB x hx)) (hB x hx) hd0 (hdist x hx θ)
    exact mul_le_mul (hW θ) h1 (abs_nonneg _) ((abs_nonneg _).trans (hW θ))
  have hmeasF' : AEStronglyMeasurable (F' t) arc := by
    refine (hw.mul ?_).aestronglyMeasurable
    exact Complex.measurable_re.comp (measurable_const.div (measurable_const.sub hp))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := arc) (F := F) (F' := F')
    (s := ball t ε) (x₀ := t) (bound := fun _ => W * (B / d)) (ball_mem_nhds t hε)
    (Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable) hint hmeasF'
    (ae_of_all _ hbound) (integrable_const _) (ae_of_all _ hdiff)
  have hres := key.2.neg
  convert hres using 1
  · funext x; rfl
  -- identify `∫ w Re(γ'/(γ - p)) = Re(γ' ∫ w (γ - p)⁻¹)`
  have hmw : Measurable fun θ => (w θ : ℂ) := Complex.measurable_ofReal.comp hw
  have hI : Integrable (fun θ => (w θ : ℂ) * ((γ t - p θ) ^ 1)⁻¹) arc :=
    Integrable.mono' (integrable_const (W / d)) (hmw.mul
      ((measurable_const.sub hp).pow_const 1).inv).aestronglyMeasurable
      (ae_of_all _ fun θ => by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
        refine mul_le_mul (hW θ) ?_ (by positivity) ((abs_nonneg _).trans (hW θ))
        exact inv_anti₀ hd0 (by simpa using hdist t ht θ))
  unfold stA
  have e1 : ∫ θ, F' t θ ∂arc = (∫ θ, γd t * ((w θ : ℂ) * ((γ t - p θ) ^ 1)⁻¹) ∂arc).re := by
    have hr := integral_re (hI.const_mul (γd t))
    simp only [RCLike.re_to_complex] at hr
    rw [← hr]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [hF', RCLike.re_to_complex, pow_one]
    rw [div_eq_mul_inv]
    rw [show γd t * ((w θ : ℂ) * (γ t - p θ)⁻¹) = (w θ : ℂ) * (γd t * (γ t - p θ)⁻¹) by ring,
      Complex.re_ofReal_mul]
  rw [e1, integral_const_mul]

end

end CatalanCore.Tools.Joukowski
end J7

section J8
open Complex Polynomial MeasureTheory Set Metric Filter Topology
  CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells OAI.InternalCatalan
  CatalanMeasure.GenD.Signed.TaylorCell

namespace CatalanCore.Tools.Joukowski

noncomputable section

theorem logPotC_segMeasure_eq {M h : ℂ} {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (s : ℂ) :
    logPotC (segMeasure M h c N) s =
      ugC (fun θ => chebF c N (Real.cos θ)) (fun θ => M + h * (Real.cos θ : ℂ)) s := by
  unfold logPotC ugC
  have hmeas : Measurable fun u : ℂ => Real.log ‖s - u‖ :=
    Real.measurable_log.comp (by fun_prop)
  rw [integral_segMeasure hpos hmeas]

/-- **W3, first derivative of the segment potential along a real curve:**
`d/dt U^ν(γ t) = -Re(γ'(t) S₁(γ t))` whenever `γ t` is off the segment. -/
theorem hasDerivAt_logPotC_seg {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {γ γd : ℝ → ℂ}
    (hγ : ∀ x, HasDerivAt γ (γd x) x) (hγd : Continuous γd) {t : ℝ}
    (ht : 1 < jc ((γ t - M) / h)) :
    HasDerivAt (fun x => logPotC (segMeasure M h c N) (γ x))
      (-((γd t * segSt M h c N 1 (γ t)).re)) t := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun x => (hγ x).continuousAt
  set d0 := ‖h‖ * (jc ((γ t - M) / h) - 1) with hd0
  have hd0p : 0 < d0 := seg_dist_pos hh ht
  -- a ball where the distance stays above `d0 / 2` and `γd` stays below `‖γd t‖ + 1`
  have hev1 : ∀ᶠ x in 𝓝 t, d0 / 2 < ‖h‖ * (jc ((γ x - M) / h) - 1) := by
    have hc : Continuous fun x => ‖h‖ * (jc ((γ x - M) / h) - 1) :=
      continuous_const.mul ((continuous_jc.comp ((hγc.sub continuous_const).div_const h)).sub
        continuous_const)
    exact hc.continuousAt.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ x in 𝓝 t, ‖γd x‖ < ‖γd t‖ + 1 :=
    (hγd.norm.continuousAt).eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev1.and hev2)
  have key := hasDerivAt_ugC (w := fun θ => chebF c N (Real.cos θ))
    (p := fun θ => M + h * (Real.cos θ : ℂ))
    (continuous_chebF_cos c N).measurable (by fun_prop)
    (W := ∑ k ∈ Finset.range (N + 1), |c k|) (P := ‖M‖ + ‖h‖)
    (fun θ => abs_chebF_le c N (cos_mem θ))
    (fun θ => by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one θ))
    (γ := γ) (γd := γd) (t := t) hε (B := ‖γd t‖ + 1) (d := d0 / 2) (by linarith)
    (fun x _ => hγ x) (fun x hx => (hball x hx).2.le)
    (fun x hx θ => ((hball x hx).1.le).trans (norm_sub_seg_ge hh (cos_mem θ)))
  have hfun : (fun x => logPotC (segMeasure M h c N) (γ x)) =
      fun x => ugC (fun θ => chebF c N (Real.cos θ)) (fun θ => M + h * (Real.cos θ : ℂ)) (γ x) :=
    funext fun x => logPotC_segMeasure_eq hpos (γ x)
  rw [hfun]
  convert key using 2
  rw [segSt_eq_stA hpos]

end

end CatalanCore.Tools.Joukowski
end J8

section J9
open Complex Polynomial MeasureTheory Set Metric Filter Topology
  CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells OAI.InternalCatalan
  CatalanMeasure.GenD.Signed.TaylorCell

namespace CatalanCore.Tools.Joukowski

noncomputable section

/-- `D_k = G^{(k)} = (-1)^k (k-1)! S_k`: the derivative tower of the (multivalued) primitive
`G = -∫ log (s - u) dν`, `U^ν = Re G`.  Only `k ≥ 1` is ever used. -/
def segD (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) (k : ℕ) (s : ℂ) : ℂ :=
  (-1) ^ k * ((k - 1).factorial : ℂ) * segSt M h c N k s

/-- `D_{k+1} = D_k'` (the tower relation of W3(b)). -/
theorem hasDerivAt_segD {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h))
    {k : ℕ} (hk : 1 ≤ k) :
    HasDerivAt (segD M h c N k) (segD M h c N (k + 1) s) s := by
  have h1 := (hasDerivAt_segSt hh hpos hs k).const_mul ((-1 : ℂ) ^ k * ((k - 1).factorial : ℂ))
  refine h1.congr_deriv ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [segD, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

/-- The real tower of the segment potential along a curve `γ`: `f 0 = U^ν ∘ γ 0` and, for
`j ≥ 1`, `f j = Re (fdb (D_k ∘ γ 0) (γ i) j)`. -/
def potT (M h : ℂ) (c : ℕ → ℝ) (N : ℕ) (γ : ℕ → ℝ → ℂ) (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then logPotC (segMeasure M h c N) (γ 0 x)
  else (fdb (fun k => segD M h c N k (γ 0 x)) (fun i => γ i x) j).re

theorem continuousAt_segD {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℂ} (hs : 1 < jc ((s - M) / h))
    {k : ℕ} (hk : 1 ≤ k) : ContinuousAt (segD M h c N k) s := by
  have := (hasDerivAt_segSt hh hpos hs k).continuousAt
  exact continuousAt_const.mul this

/-- **LD13, the cross/own potential tower of a segment on a cell (W3).** If the curve `γ` (with
its derivative chain `γ i`, `i < 5`, smooth and `γ 5` continuous) stays off the segment on the
closed cell, then `potT` is a derivative tower of order 5 for `x ↦ U^ν(γ 0 x)`. -/
theorem isTower_potT {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {γ : ℕ → ℝ → ℂ} {a r : ℝ}
    (hγd : ∀ i < 5, ∀ x, HasDerivAt (γ i) (γ (i + 1) x) x) (hγc : Continuous (γ 5))
    (hreg : ∀ x ∈ Icc (a - r) (a + r), 1 < jc ((γ 0 x - M) / h)) :
    IsTower (potT M h c N γ) a r 5 := by
  have hcont : ∀ i ≤ 5, Continuous (γ i) := by
    intro i hi
    rcases Nat.lt_or_ge i 5 with h5 | h5
    · exact continuous_iff_continuousAt.2 fun x => (hγd i h5 x).continuousAt
    · have : i = 5 := le_antisymm hi h5
      subst this; exact hγc
  have hD : ∀ x ∈ Icc (a - r) (a + r), ∀ k, 1 ≤ k → k < 5 →
      HasDerivAt (fun y => segD M h c N k (γ 0 y)) (segD M h c N (k + 1) (γ 0 x) * γ 1 x) x := by
    intro x hx k hk1 hk5
    have h1 : HasDerivAt (fun y => segD M h c N k (γ 0 y))
        (γ 1 x • segD M h c N (k + 1) (γ 0 x)) x :=
      (hasDerivAt_segD hh hpos (hreg x hx) hk1).scomp x (hγd 0 (by norm_num) x)
    exact h1.congr_deriv (by rw [smul_eq_mul, mul_comm])
  have hd0 : ∀ x ∈ Icc (a - r) (a + r), HasDerivAt (fun y => logPotC (segMeasure M h c N) (γ 0 y))
      (-((γ 1 x * segSt M h c N 1 (γ 0 x)).re)) x := fun x hx =>
    hasDerivAt_logPotC_seg hh hpos (γ := γ 0) (γd := γ 1) (fun y => hγd 0 (by norm_num) y)
      (continuous_iff_continuousAt.2 fun y => (hγd 1 (by norm_num) y).continuousAt) (t := x)
      (hreg x hx)
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have e : potT M h c N γ 0 = fun y => logPotC (segMeasure M h c N) (γ 0 y) := by
        funext y; simp [potT]
      rw [e]
      exact (hd0 x hx).continuousAt.continuousWithinAt
    · have hc : ∀ k, 1 ≤ k → k ≤ 5 →
          ContinuousWithinAt (fun y => segD M h c N k (γ 0 y)) (Icc (a - r) (a + r)) x := by
        intro k hk1 hk5
        have hcs := continuousAt_segD hh hpos (hreg x hx) hk1
        exact (hcs.comp (hcont 0 (by norm_num)).continuousAt).continuousWithinAt
      have hy : ∀ i, 1 ≤ i → i ≤ 5 → ContinuousWithinAt (γ i) (Icc (a - r) (a + r)) x :=
        fun i _ hi => (hcont i hi).continuousAt.continuousWithinAt
      have h1 := hc 1 (by norm_num) (by norm_num)
      have h2 := hc 2 (by norm_num) (by norm_num)
      have h3 := hc 3 (by norm_num) (by norm_num)
      have h4 := hc 4 (by norm_num) (by norm_num)
      have h5 := hc 5 (by norm_num) (by norm_num)
      have y1 := hy 1 (by norm_num) (by norm_num)
      have y2 := hy 2 (by norm_num) (by norm_num)
      have y3 := hy 3 (by norm_num) (by norm_num)
      have y4 := hy 4 (by norm_num) (by norm_num)
      have y5 := hy 5 (by norm_num) (by norm_num)
      have hne : j ≠ 0 := by omega
      have e : potT M h c N γ j =
          fun y => (fdb (fun k => segD M h c N k (γ 0 y)) (fun i => γ i y) j).re := by
        funext y; simp [potT, hne]
      rw [e]
      refine Complex.continuous_re.continuousAt.comp_continuousWithinAt ?_
      interval_cases j <;> simp only [fdb] <;> fun_prop
  · intro j hj x hx
    have hx' : x ∈ Icc (a - r) (a + r) := ⟨hx.1.le, hx.2.le⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have e : potT M h c N γ 0 = fun y => logPotC (segMeasure M h c N) (γ 0 y) := by
        funext y; simp [potT]
      have e1 : potT M h c N γ (0 + 1) x = -((γ 1 x * segSt M h c N 1 (γ 0 x)).re) := by
        have : (-1 : ℂ) * ((1 - 1 : ℕ).factorial : ℂ) * segSt M h c N 1 (γ 0 x) * γ 1 x =
            -(γ 1 x * segSt M h c N 1 (γ 0 x)) := by simp; ring
        simp only [potT, fdb, segD, Nat.zero_add, pow_one, Nat.one_ne_zero, if_false]
        rw [this, Complex.neg_re]
      rw [e, e1]
      exact hd0 x hx'
    · have hne : j ≠ 0 := by omega
      have hne1 : j + 1 ≠ 0 := by omega
      have hfd := hasDerivAt_fdbC (Dc := fun k y => segD M h c N k (γ 0 y)) (Yc := γ) (x := x)
        (fun k hk1 hk5 => hD x hx' k hk1 hk5) (fun i _ hi => hγd i hi x) j hj0 hj
      have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hfd
      have e : potT M h c N γ j =
          fun y => (fdb (fun k => segD M h c N k (γ 0 y)) (fun i => γ i y) j).re := by
        funext y; simp [potT, hne]
      have e1 : potT M h c N γ (j + 1) x =
          (fdb (fun k => segD M h c N k (γ 0 x)) (fun i => γ i x) (j + 1)).re := by
        simp [potT, hne1]
      rw [e, e1]
      exact hre

/-- **W3(c)+(d), the order-5 remainder.** On a cell where `d_lo ≤ |h|(c(ζ) - 1)` and
`‖γ i‖ ≤ Ym i`, `|f 5| ≤ fdbBound (k ↦ (k-1)! c₀ / d_lo^k) Ym`. -/
theorem abs_potT5_le {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {γ : ℕ → ℝ → ℂ} {x dlo : ℝ} {Ym : ℕ → ℝ}
    (hreg : 1 < jc ((γ 0 x - M) / h)) (hdlo0 : 0 < dlo)
    (hdlo : dlo ≤ ‖h‖ * (jc ((γ 0 x - M) / h) - 1)) (hY : ∀ i, 1 ≤ i → i ≤ 5 → ‖γ i x‖ ≤ Ym i) :
    |potT M h c N γ 5 x| ≤
      fdbBound (fun k => ((k - 1).factorial : ℝ) * c 0 / dlo ^ k) Ym := by
  have hne : (5 : ℕ) ≠ 0 := by norm_num
  simp only [potT, hne, if_false]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine norm_fdb5_le _ _ _ Ym (fun k hk1 hk5 => ?_) hY
  have hb := norm_segSt_le hh hpos (s := γ 0 x) hreg k
  simp only [segD, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  calc ((k - 1).factorial : ℝ) * ‖segSt M h c N k (γ 0 x)‖
      ≤ ((k - 1).factorial : ℝ) * (c 0 / (‖h‖ * (jc ((γ 0 x - M) / h) - 1)) ^ k) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ ((k - 1).factorial : ℝ) * (c 0 / dlo ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine div_le_div_of_nonneg_left ?_ (pow_pos hdlo0 k) (pow_le_pow_left₀ hdlo0.le hdlo k)
        rw [← integral_chebF c N]
        exact integral_nonneg fun θ => hpos _ (cos_mem θ)
    _ = _ := by ring

end

end CatalanCore.Tools.Joukowski
end J9
