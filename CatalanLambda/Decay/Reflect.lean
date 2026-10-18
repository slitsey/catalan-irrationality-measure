module

public import CatalanLambda.Decay.Lowner
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Reflection split `F = F̃ + E`

* `eterm z n = 1/(z-n-1/4) - 1/(z-n)`, `EC z = ∑_{n ∈ ℤ} eterm z n` (absolutely convergent),
* `Ftil z = -∑_{n ≥ 0} eterm z n`, and `lowFC z = Ftil z + EC z` (series identity),
* closed form `EC z = π cot π(z-1/4) - π cot πz` (via `Complex.cot_series_rep'`),
  and `EC z = π sin(π/4) / (sin(πz - π/4) sin(πz))`,
* the bound `‖EC z‖ ≤ 16 π exp(-2π|Im z|)` for `|Im z| ≥ 1`, and a strip bound away from the poles.
-/

open Complex

namespace CatalanLambda.Decay

/-- Two-pole summability for arbitrary real shifts. -/
theorem summable_pairC (z : ℂ) (c d : ℝ) :
    Summable fun j : ℕ => (1 / (z + j + (c : ℂ)) - 1 / (z + j + (d : ℂ)) : ℂ) := by
  have hs : Summable fun j : ℕ => 4 * |d - c| * ((1 : ℝ) / (j : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.2 (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [Filter.eventually_ge_atTop (⌈2 * ‖z‖ + 2 * |c| + 2 * |d|⌉₊ + 1)] with j hj
  have hj' : 2 * ‖z‖ + 2 * |c| + 2 * |d| + 1 ≤ (j : ℝ) := by
    have h1 := Nat.le_ceil (2 * ‖z‖ + 2 * |c| + 2 * |d|)
    have h2 : ((⌈2 * ‖z‖ + 2 * |c| + 2 * |d|⌉₊ + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    push_cast at h2; linarith
  have key : ∀ e : ℝ, |e| ≤ (j : ℝ) / 2 - ‖z‖ → (j : ℝ) / 2 ≤ ‖z + (j : ℂ) + (e : ℂ)‖ := by
    intro e he
    have h3 := norm_sub_norm_le ((((j : ℝ) + e : ℝ)) : ℂ) (-z)
    have hje : 0 ≤ (j : ℝ) + e := by
      have := neg_abs_le e
      linarith [norm_nonneg z]
    have h4 : ‖((((j : ℝ) + e : ℝ)) : ℂ)‖ = (j : ℝ) + e := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hje]
    rw [h4, norm_neg] at h3
    have h5 : ((((j : ℝ) + e : ℝ)) : ℂ) - -z = z + (j : ℂ) + (e : ℂ) := by push_cast; ring
    rw [h5] at h3
    have := le_abs_self e
    have := neg_abs_le e
    linarith
  have hc : |c| ≤ (j : ℝ) / 2 - ‖z‖ := by
    have := abs_nonneg d; linarith
  have hd : |d| ≤ (j : ℝ) / 2 - ‖z‖ := by
    have := abs_nonneg c; linarith
  have h1 := key c hc
  have h2 := key d hd
  have hjpos : (0 : ℝ) < j := by linarith [norm_nonneg z, abs_nonneg c, abs_nonneg d]
  have ha0 : z + (j : ℂ) + (c : ℂ) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h1)
  have hb0 : z + (j : ℂ) + (d : ℂ) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h2)
  have e : (1 / (z + j + (c : ℂ)) - 1 / (z + j + (d : ℂ)) : ℂ)
      = ((d : ℂ) - c) / ((z + j + (c : ℂ)) * (z + j + (d : ℂ))) := by
    rw [div_sub_div _ _ ha0 hb0]; congr 1; ring
  rw [e, norm_div, norm_mul]
  have hn : ‖((d : ℂ) - c)‖ = |d - c| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hAB := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  have habs := abs_nonneg (d - c)
  nlinarith [mul_le_mul_of_nonneg_left hAB habs]

/-- The `n`-th term of the periodic series: `1/(z-n-1/4) - 1/(z-n)`. -/
noncomputable def eterm (z : ℂ) (n : ℤ) : ℂ := 1 / (z - n - 1 / 4) - 1 / (z - n)

theorem eterm_nat_summable (z : ℂ) : Summable fun n : ℕ => eterm z (n : ℤ) := by
  have h := (summable_pairC (-z) (1 / 4) 0).neg
  refine h.congr (fun n => ?_)
  unfold eterm
  have e1 : z - ((n : ℤ) : ℂ) - 1 / 4 = -(-z + n + ((1 / 4 : ℝ) : ℂ)) := by push_cast; ring
  have e2 : z - ((n : ℤ) : ℂ) = -(-z + n + ((0 : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, e2, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
  ring

theorem eterm_neg_summable (z : ℂ) : Summable fun n : ℕ => eterm z (-((n : ℤ) + 1)) := by
  have h := summable_pairC z (3 / 4) 1
  refine h.congr (fun n => ?_)
  unfold eterm
  have e1 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) - 1 / 4 = z + n + ((3 / 4 : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) = z + n + ((1 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]

theorem summable_eterm (z : ℂ) : Summable (eterm z) :=
  Summable.of_nat_of_neg_add_one (eterm_nat_summable z) (eterm_neg_summable z)

/-- `E(z) = ∑_{n ∈ ℤ} [1/(z-n-1/4) - 1/(z-n)]`. -/
noncomputable def EC (z : ℂ) : ℂ := ∑' n : ℤ, eterm z n

/-- `F̃(z) = -∑_{n ≥ 0} [1/(z-n-1/4) - 1/(z-n)]` (`= ψ(-z) - ψ(1/4-z)`). -/
noncomputable def Ftil (z : ℂ) : ℂ := -∑' n : ℕ, eterm z (n : ℤ)

theorem lowFC_eq_neg_tail (z : ℂ) : lowFC z = ∑' n : ℕ, eterm z (-((n : ℤ) + 1)) := by
  unfold lowFC
  congr 1; ext n
  unfold eterm
  have e1 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) - 1 / 4 = z + n + 3 / 4 := by push_cast; ring
  have e2 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) = z + n + 1 := by push_cast; ring
  rw [e1, e2]

/-- **Reflection split** as a series identity: `F = F̃ + E`. -/
theorem lowFC_split (z : ℂ) : lowFC z = Ftil z + EC z := by
  unfold Ftil EC
  rw [tsum_of_nat_of_neg_add_one (eterm_nat_summable z) (eterm_neg_summable z), lowFC_eq_neg_tail]
  ring

/-- Norm of `sin`. -/
theorem norm_sin_sq (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have h : Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ)
      + ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im w, Complex.sin_add_mul_I]
    push_cast; ring
  rw [h, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith

theorem sin_re_le_norm (w : ℂ) : |Real.sin w.re| ≤ ‖Complex.sin w‖ := by
  have h := norm_sin_sq w
  have h2 : |Real.sin w.re| ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    rw [sq_abs]; nlinarith [sq_nonneg (Real.sinh w.im)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 h2

theorem sinh_abs_ge (t : ℝ) (ht : 3 / 8 ≤ |t|) : Real.exp |t| / 4 ≤ |Real.sinh t| := by
  have key : ∀ s : ℝ, 3 / 8 ≤ s → Real.exp s / 4 ≤ Real.sinh s := by
    intro s hs
    rw [Real.sinh_eq]
    have hE := Real.exp_pos s
    have hm : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    have hq := Real.quadratic_le_exp_of_nonneg (x := 2 * s) (by linarith)
    have h2s : Real.exp (2 * s) = Real.exp s * Real.exp s := by rw [two_mul, Real.exp_add]
    have h3 : Real.exp (-s) * Real.exp s ≤ Real.exp s / 2 * Real.exp s := by
      nlinarith
    have h4 := le_of_mul_le_mul_right h3 hE
    linarith
  have key2 : ∀ s : ℝ, 3 / 8 ≤ s → Real.exp s / 4 ≤ |Real.sinh s| := by
    intro s hs
    have := key s hs
    have hp : 0 < Real.exp s / 4 := by positivity
    rw [abs_of_pos (lt_of_lt_of_le hp this)]
    exact this
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact key2 t ht
  · rw [abs_of_nonpos h] at ht ⊢
    rw [← abs_neg, ← Real.sinh_neg]
    exact key2 (-t) ht

theorem norm_sin_ge (w : ℂ) (hw : 3 / 8 ≤ |w.im|) : Real.exp |w.im| / 4 ≤ ‖Complex.sin w‖ := by
  have h := norm_sin_sq w
  have h1 := sinh_abs_ge _ hw
  have h2 : (Real.exp |w.im| / 4) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    have : (Real.exp |w.im| / 4) ^ 2 ≤ |Real.sinh w.im| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (Real.sin w.re)]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h2

/-- Closed form of `E` via the cotangent series. -/
theorem EC_eq_cot {z : ℂ} (hz : z ∈ Complex.integerComplement)
    (hz' : z - 1 / 4 ∈ Complex.integerComplement) :
    EC z = (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z - 1 / 4))
      - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) := by
  have hs := summable_eterm z
  have inj1 : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b h; simp only at h; omega
  have hs1 : Summable fun n : ℕ => eterm z ((n : ℤ) + 1) := hs.comp_injective inj1
  have hs2 := eterm_neg_summable z
  unfold EC
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have c1 : Summable fun n : ℕ => (1 / ((z - 1 / 4) - (n + 1)) + 1 / ((z - 1 / 4) + (n + 1)) : ℂ) :=
    summable_cotTerm hz'
  have c2 : Summable fun n : ℕ => (1 / (z - (n + 1)) + 1 / (z + (n + 1)) : ℂ) :=
    summable_cotTerm hz
  have hp : ∀ n : ℕ, eterm z ((n : ℤ) + 1) + eterm z (-((n : ℤ) + 1))
      = (1 / ((z - 1 / 4) - (n + 1)) + 1 / ((z - 1 / 4) + (n + 1)) : ℂ)
        - (1 / (z - (n + 1)) + 1 / (z + (n + 1))) := by
    intro n; unfold eterm; push_cast; ring
  have h3 := hs1.tsum_add hs2
  simp only [hp] at h3
  rw [Summable.tsum_sub c1 c2] at h3
  have r1 := cot_series_rep' hz'
  have r2 := cot_series_rep' hz
  have e0 : eterm z 0 = 1 / (z - 1 / 4) - 1 / z := by unfold eterm; simp
  have : ∑' n : ℕ, eterm z ((n : ℤ) + 1) + eterm z 0 + ∑' n : ℕ, eterm z (-((n : ℤ) + 1))
      = (∑' n : ℕ, eterm z ((n : ℤ) + 1) + ∑' n : ℕ, eterm z (-((n : ℤ) + 1))) + eterm z 0 := by ring
  rw [this, ← h3, e0, ← r1, ← r2]
  ring

/-- `E(z) = π sin(π/4) / (sin(πz - π/4) sin(πz))`. -/
theorem EC_eq_sin {z : ℂ} (hz : z ∈ Complex.integerComplement)
    (hz' : z - 1 / 4 ∈ Complex.integerComplement) :
    EC z = (Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ) / 4)
      / (Complex.sin ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) * z)) := by
  rw [EC_eq_cot hz hz']
  have hB : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := sin_pi_mul_ne_zero hz
  have hA' : Complex.sin ((Real.pi : ℂ) * (z - 1 / 4)) ≠ 0 := sin_pi_mul_ne_zero hz'
  have hAe : (Real.pi : ℂ) * (z - 1 / 4) = (Real.pi : ℂ) * z - (Real.pi : ℂ) / 4 := by ring
  rw [hAe] at hA' ⊢
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  have hsub : Complex.sin ((Real.pi : ℂ) / 4)
      = Complex.sin ((Real.pi : ℂ) * z) * Complex.cos ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4)
        - Complex.cos ((Real.pi : ℂ) * z) * Complex.sin ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4) := by
    rw [← Complex.sin_sub]; congr 1; ring
  rw [hsub]
  generalize Complex.sin ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4) = sA at *
  generalize Complex.sin ((Real.pi : ℂ) * z) = sB at *
  field_simp

theorem mem_intCompl_of_im_ne {z : ℂ} (hz : z.im ≠ 0) : z ∈ Complex.integerComplement := by
  rintro ⟨n, rfl⟩
  simp at hz

theorem norm_sin_pi_div_four_le : ‖Complex.sin ((Real.pi : ℂ) / 4)‖ ≤ 1 := by
  have : Complex.sin ((Real.pi : ℂ) / 4) = ((Real.sin (Real.pi / 4) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]; push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.neg_one_le_sin (Real.pi / 4), Real.sin_le_one (Real.pi / 4)]

/-- **Bound away from the real axis**: `‖E z‖ ≤ 16π e^{-2π|Im z|}` for `|Im z| ≥ 1/8`. -/
theorem EC_norm_le_far (z : ℂ) (hy : 1 / 8 ≤ |z.im|) :
    ‖EC z‖ ≤ 16 * Real.pi * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hz : z ∈ Complex.integerComplement :=
    mem_intCompl_of_im_ne (by intro h; rw [h] at hy; simp at hy; linarith)
  have hz' : z - 1 / 4 ∈ Complex.integerComplement :=
    mem_intCompl_of_im_ne (by
      intro h; simp at h; rw [h] at hy; simp at hy; linarith)
  rw [EC_eq_sin hz hz', norm_div, norm_mul, norm_mul]
  have hpi := Real.pi_gt_three
  have hn : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have him1 : ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4).im = Real.pi * z.im := by simp
  have him2 : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  have habs : |Real.pi * z.im| = Real.pi * |z.im| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hge : 3 / 8 ≤ |Real.pi * z.im| := by
    rw [habs]; nlinarith
  have hA := norm_sin_ge ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4) (by rw [him1]; exact hge)
  have hB := norm_sin_ge ((Real.pi : ℂ) * z) (by rw [him2]; exact hge)
  rw [him1, habs] at hA
  rw [him2, habs] at hB
  set E := Real.exp (Real.pi * |z.im|) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hexp : Real.exp (-(2 * Real.pi * |z.im|)) = 1 / (E * E) := by
    rw [hE, ← Real.exp_add, one_div, ← Real.exp_neg]; congr 2; ring
  rw [hexp, hn, div_le_iff₀ (mul_pos (lt_of_lt_of_le (by linarith : 0 < E / 4) hA) (lt_of_lt_of_le (by linarith : 0 < E / 4) hB))]
  have hs := norm_sin_pi_div_four_le
  have hAB := mul_le_mul hA hB (by linarith : 0 ≤ E / 4) (norm_nonneg _)
  have hnn := norm_nonneg (Complex.sin ((Real.pi : ℂ) / 4))
  have hEE : 0 < E * E := by positivity
  have : Real.pi * ‖Complex.sin ((Real.pi : ℂ) / 4)‖ ≤ Real.pi := by nlinarith
  calc Real.pi * ‖Complex.sin ((Real.pi : ℂ) / 4)‖ ≤ Real.pi := this
    _ = 16 * Real.pi * (1 / (E * E)) * (E / 4 * (E / 4)) := by field_simp; ring
    _ ≤ 16 * Real.pi * (1 / (E * E)) * (‖Complex.sin ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4)‖
        * ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by
      gcongr

/-- **Bound near the real axis**, away from the poles of `E`. -/
theorem EC_norm_le_near (z : ℂ) (s : ℝ) (hs : 0 < s)
    (h1 : s ≤ |Real.sin (Real.pi * z.re - Real.pi / 4)|) (h2 : s ≤ |Real.sin (Real.pi * z.re)|) :
    ‖EC z‖ ≤ Real.pi / s ^ 2 := by
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, rfl⟩
    have : Real.sin (Real.pi * (n : ℝ)) = 0 := by
      rw [mul_comm]; exact Real.sin_int_mul_pi n
    simp only [Complex.intCast_re] at h2
    rw [this] at h2; simp at h2; linarith
  have hz' : z - 1 / 4 ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hre : z.re = n + 1 / 4 := by
      have := congrArg Complex.re hn
      simp at this; linarith
    have : Real.sin (Real.pi * z.re - Real.pi / 4) = 0 := by
      rw [hre]
      have : Real.pi * ((n : ℝ) + 1 / 4) - Real.pi / 4 = (n : ℝ) * Real.pi := by ring
      rw [this]; exact Real.sin_int_mul_pi n
    rw [this] at h1; simp at h1; linarith
  rw [EC_eq_sin hz hz', norm_div, norm_mul, norm_mul]
  have hn : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hA := sin_re_le_norm ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4)
  have hB := sin_re_le_norm ((Real.pi : ℂ) * z)
  have e1 : ((Real.pi : ℂ) * z - (Real.pi : ℂ) / 4).re = Real.pi * z.re - Real.pi / 4 := by simp
  have e2 : ((Real.pi : ℂ) * z).re = Real.pi * z.re := by simp
  rw [e1] at hA; rw [e2] at hB
  have hA' := h1.trans hA
  have hB' := h2.trans hB
  have hs2 := norm_sin_pi_div_four_le
  have hnn := norm_nonneg (Complex.sin ((Real.pi : ℂ) / 4))
  rw [hn, div_le_div_iff₀ (mul_pos (lt_of_lt_of_le hs hA') (lt_of_lt_of_le hs hB')) (by positivity)]
  have hAB := mul_le_mul hA' hB' hs.le (by positivity)
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left hs2 hpi.le]

/-- **Uniform exponential bound for `E`** (the shape needed on the rays): if `z` is either at height
`|Im z| ≥ 1/8`, or the real part keeps `sin` of both factors at least `s` away from `0`, then
`‖E z‖ ≤ (16π + π e^{π/4}/s²) · e^{-2π|Im z|}`. -/
theorem EC_norm_le_uniform (s : ℝ) (hs : 0 < s) (z : ℂ)
    (h : 1 / 8 ≤ |z.im| ∨ (s ≤ |Real.sin (Real.pi * z.re - Real.pi / 4)| ∧
      s ≤ |Real.sin (Real.pi * z.re)|)) :
    ‖EC z‖ ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / s ^ 2) *
      Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hpi := Real.pi_pos
  have hexp := Real.exp_pos (-(2 * Real.pi * |z.im|))
  by_cases hy : 1 / 8 ≤ |z.im|
  · have := EC_norm_le_far z hy
    have h2 : 0 ≤ Real.pi * Real.exp (Real.pi / 4) / s ^ 2 := by positivity
    nlinarith
  · have hn : s ≤ |Real.sin (Real.pi * z.re - Real.pi / 4)| ∧ s ≤ |Real.sin (Real.pi * z.re)| := by
      rcases h with h | h
      · exact absurd h hy
      · exact h
    have := EC_norm_le_near z s hs hn.1 hn.2
    have hy' : |z.im| < 1 / 8 := lt_of_not_ge hy
    have h3 : 1 ≤ Real.exp (Real.pi / 4) * Real.exp (-(2 * Real.pi * |z.im|)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [abs_nonneg z.im]
    have h4 : Real.pi / s ^ 2 ≤ Real.pi * Real.exp (Real.pi / 4) / s ^ 2 * Real.exp (-(2 * Real.pi * |z.im|)) := by
      have : Real.pi / s ^ 2 * 1 ≤ Real.pi / s ^ 2 * (Real.exp (Real.pi / 4) * Real.exp (-(2 * Real.pi * |z.im|))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      calc Real.pi / s ^ 2 = Real.pi / s ^ 2 * 1 := by ring
        _ ≤ _ := this
        _ = _ := by ring
    nlinarith [mul_pos hpi hexp]

end CatalanLambda.Decay
