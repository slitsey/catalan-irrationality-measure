module

public import CatalanCore.Frame.Spec
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

@[expose] public section

/-!
# Reflection term `E` of a Loewner frame (WP2a)

For a frame `Fr` (shifts `μ i`, integer weights `w i`, `∑ w = 0`) put
`F(z) = -∑_i w_i ∑_{k ≥ 0} 1/(z + k + μ_i)` (so that `F = F̃ + E`, `F̃` analytic in `Re z < 0`).
The reflection term is the symmetric sum over all integers

* `Fr.eterm z n = -∑_i w_i / (z + n + μ_i)`  (the `n`-th term, `n ∈ ℤ`),
* `Fr.EC z = ∑_{n ∈ ℤ} Fr.eterm z n`  (absolutely convergent because `∑ w = 0`),
* closed form `Fr.EC z = -∑_i w_i π cot π(z + μ_i)`  (`EC_eq_cot`).

For `λ` (`μ = ![3/4, 1]`, `w = ![-1, 1]`) this is the legacy `CatalanLambda.Decay.EC`.

**Uniform decay (the simplification over the legacy case analysis).**  For `Im w ≥ 0` one has the
exact identity `cot πw + i = e^{iπw}/sin πw`, hence
`‖cot πw + i‖ = e^{-π Im w}/‖sin πw‖`; for `Im w ≤ 0` the same with `cot πw - i`.  All shifts
`z + μ_i` have the same imaginary part, so `∑ w = 0` cancels the constant `±i` exactly and
`‖EC z‖ ≤ (π ∑|w_i| / κ) e^{-2π|Im z|}` as soon as `‖sin π(z+μ_i)‖ ≥ κ e^{π|Im z|}` for all `i`
(`norm_EC_le`).  No product-of-sines formula and no per-frame constants are needed; the lower
bound on `‖sin‖` is proved once in `Decay/RayBound` from the contour gap.
-/

open Complex Finset

namespace CatalanCore.Decay

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

/-- Two-pole summability over all of `ℤ`. -/
theorem summable_pair_int (z : ℂ) (c d : ℝ) :
    Summable fun n : ℤ => (1 / (z + n + (c : ℂ)) - 1 / (z + n + (d : ℂ)) : ℂ) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_pairC z c d
  · have h := (summable_pairC (-z) (1 - c) (1 - d)).neg
    refine h.congr (fun n => ?_)
    have e1 : z + ((-((n : ℤ) + 1) : ℤ) : ℂ) + (c : ℂ) = -(-z + n + (((1 - c : ℝ)) : ℂ)) := by
      push_cast; ring
    have e2 : z + ((-((n : ℤ) + 1) : ℤ) : ℂ) + (d : ℂ) = -(-z + n + (((1 - d : ℝ)) : ℂ)) := by
      push_cast; ring
    rw [e1, e2, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
    ring

/-! ### Lower bounds for `‖sin‖` -/

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

/-- `‖cot πw + i‖ = e^{-π Im w} / ‖sin πw‖`  (from `cot + i = e^{iπw}/sin`). -/
theorem norm_cot_add_I (w : ℂ) (h : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    ‖Complex.cot ((Real.pi : ℂ) * w) + Complex.I‖
      = Real.exp (-(Real.pi * w.im)) / ‖Complex.sin ((Real.pi : ℂ) * w)‖ := by
  rw [Complex.cot_eq_cos_div_sin]
  · have e : Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w) + Complex.I
        = Complex.exp (((Real.pi : ℂ) * w) * Complex.I) / Complex.sin ((Real.pi : ℂ) * w) := by
      rw [Complex.exp_mul_I]; field_simp
    rw [e, norm_div, Complex.norm_exp]
    simp

/-- `‖cot πw - i‖ = e^{π Im w} / ‖sin πw‖`  (from `cot - i = e^{-iπw}/sin`). -/
theorem norm_cot_sub_I (w : ℂ) (h : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    ‖Complex.cot ((Real.pi : ℂ) * w) - Complex.I‖
      = Real.exp (Real.pi * w.im) / ‖Complex.sin ((Real.pi : ℂ) * w)‖ := by
  rw [Complex.cot_eq_cos_div_sin]
  · have e : Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w) - Complex.I
        = Complex.exp (-(((Real.pi : ℂ) * w) * Complex.I)) / Complex.sin ((Real.pi : ℂ) * w) := by
      have h2 := Complex.exp_mul_I (-((Real.pi : ℂ) * w))
      rw [show -(((Real.pi : ℂ) * w) * Complex.I) = (-((Real.pi : ℂ) * w)) * Complex.I by ring, h2,
        Complex.cos_neg, Complex.sin_neg]
      field_simp
      ring
    rw [e, norm_div, Complex.norm_exp]
    simp

/-- A weighted sum with total weight zero only sees `f i - J` for any constant `J`. -/
theorem norm_wsum_le {d : ℕ} (w : Fin d → ℤ) (hw : ∑ i, (w i : ℂ) = 0) (f : Fin d → ℂ) (J : ℂ)
    (B : ℝ) (h : ∀ i, ‖f i - J‖ ≤ B) : ‖∑ i, (w i : ℂ) * f i‖ ≤ (∑ i, |(w i : ℝ)|) * B := by
  have e : ∑ i, (w i : ℂ) * f i = ∑ i, (w i : ℂ) * (f i - J) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, zero_mul, sub_zero]
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have : ‖(w i : ℂ)‖ = |(w i : ℝ)| := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

end CatalanCore.Decay

namespace CatalanCore
namespace Frame

variable (Fr : Frame)

/-- The `n`-th term of the reflection series: `-∑_i w_i / (z + n + μ_i)`. -/
noncomputable def eterm (z : ℂ) (n : ℤ) : ℂ := -∑ i, (Fr.w i : ℂ) / (z + n + (Fr.μ i : ℂ))

/-- The reflection term `E(z) = ∑_{n ∈ ℤ} eterm z n`. -/
noncomputable def EC (z : ℂ) : ℂ := ∑' n : ℤ, Fr.eterm z n

theorem sum_w_cast : ∑ i, (Fr.w i : ℂ) = 0 := by
  rw [← Int.cast_sum, Fr.hw]; simp

theorem eterm_eq_pair (z : ℂ) (n : ℤ) (c : ℂ) :
    Fr.eterm z n = -∑ i, (Fr.w i : ℂ) * (1 / (z + n + (Fr.μ i : ℂ)) - 1 / (z + n + c)) := by
  have h1 : ∑ i, (Fr.w i : ℂ) / (z + n + c) = 0 := by
    rw [← Finset.sum_div, Fr.sum_w_cast, zero_div]
  unfold eterm
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one_div, h1, sub_zero]

theorem summable_eterm (z : ℂ) : Summable (Fr.eterm z) := by
  have hp : ∀ i, Summable fun n : ℤ => (Fr.w i : ℂ) *
      (1 / (z + n + (Fr.μ i : ℂ)) - 1 / (z + n + ((0 : ℝ) : ℂ))) := by
    intro i
    have := (Decay.summable_pair_int z (Fr.μ i : ℝ) 0).mul_left (Fr.w i : ℂ)
    simpa using this
  have := (summable_sum (s := Finset.univ) (fun i _ => hp i)).neg
  refine this.congr (fun n => ?_)
  rw [Fr.eterm_eq_pair z n ((0 : ℝ) : ℂ)]

/-- Closed form via the cotangent series. -/
theorem EC_eq_cot {z : ℂ} (hz : ∀ i, z + (Fr.μ i : ℂ) ∈ Complex.integerComplement) :
    Fr.EC z = -∑ i, (Fr.w i : ℂ) *
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))) := by
  have hs := Fr.summable_eterm z
  have inj1 : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b h; simp only at h; omega
  have inj2 : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h; simp only at h; omega
  have hs1 : Summable fun n : ℕ => Fr.eterm z ((n : ℤ) + 1) := hs.comp_injective inj1
  have hs2 : Summable fun n : ℕ => Fr.eterm z (-((n : ℤ) + 1)) := hs.comp_injective inj2
  unfold EC
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have hT : ∀ i, HasSum (fun n : ℕ => (1 / ((z + (Fr.μ i : ℂ)) - (n + 1))
      + 1 / ((z + (Fr.μ i : ℂ)) + (n + 1)) : ℂ))
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) - 1 / (z + (Fr.μ i : ℂ))) := by
    intro i
    have h := (summable_cotTerm (hz i)).hasSum
    rw [← cot_series_rep' (hz i)] at h
    exact h
  have hsum := (hasSum_sum (s := Finset.univ)
    (fun i _ => (hT i).mul_left (Fr.w i : ℂ))).neg
  have hp : ∀ n : ℕ, Fr.eterm z ((n : ℤ) + 1) + Fr.eterm z (-((n : ℤ) + 1))
      = -∑ i, (Fr.w i : ℂ) * (1 / ((z + (Fr.μ i : ℂ)) - (n + 1))
        + 1 / ((z + (Fr.μ i : ℂ)) + (n + 1))) := by
    intro n
    unfold eterm
    rw [← neg_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    ring
  have h3 := hs1.tsum_add hs2
  simp only [hp] at h3
  rw [hsum.tsum_eq] at h3
  have e0 : Fr.eterm z 0 = -∑ i, (Fr.w i : ℂ) * (1 / (z + (Fr.μ i : ℂ))) := by
    unfold eterm; simp only [Int.cast_zero, add_zero, mul_one_div]
  have : ∑' n : ℕ, Fr.eterm z ((n : ℤ) + 1) + Fr.eterm z 0 + ∑' n : ℕ, Fr.eterm z (-((n : ℤ) + 1))
      = (∑' n : ℕ, Fr.eterm z ((n : ℤ) + 1) + ∑' n : ℕ, Fr.eterm z (-((n : ℤ) + 1)))
        + Fr.eterm z 0 := by ring
  rw [this, ← h3, e0]
  simp only [mul_sub, Finset.sum_sub_distrib, neg_sub, mul_one_div]
  ring

/-- **Uniform bound for `E`.**  If `‖sin π(z+μ_i)‖ ≥ κ e^{π|Im z|}` for all `i`, then
`‖E z‖ ≤ (π ∑|w_i| / κ) e^{-2π|Im z|}`.  The constants `∓i` of `cot πw` cancel because `∑ w = 0`. -/
theorem norm_EC_le {z : ℂ} {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ i, κ * Real.exp (Real.pi * |z.im|)
      ≤ ‖Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))‖) :
    ‖Fr.EC z‖ ≤ Real.pi * (∑ i, |(Fr.w i : ℝ)|) / κ * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hpi := Real.pi_pos
  have hE := Real.exp_pos (Real.pi * |z.im|)
  have hz : ∀ i, z + (Fr.μ i : ℂ) ∈ Complex.integerComplement := by
    intro i hmem
    obtain ⟨n, hn⟩ := (by simpa [Complex.integerComplement] using hmem : ∃ n : ℤ, (n : ℂ) = z + (Fr.μ i : ℂ))
    have := h i
    have hs : Complex.sin ((Real.pi : ℂ) * (n : ℂ)) = 0 := by
      rw [mul_comm]; exact Complex.sin_int_mul_pi n
    rw [← hn, hs] at this
    simp at this
    nlinarith [mul_pos hκ hE]
  rw [Fr.EC_eq_cot hz, norm_neg]
  have him : ∀ i, (z + (Fr.μ i : ℂ)).im = z.im := by intro i; simp
  have hsin : ∀ i, Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) ≠ 0 := by
    intro i hz0
    have := h i
    rw [hz0] at this
    simp at this
    nlinarith [mul_pos hκ hE]
  -- the common bound for `‖cot πw ∓ i‖`
  have hb : ∀ i, Real.exp (-(Real.pi * |z.im|))
      / ‖Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))‖
      ≤ Real.exp (-(2 * Real.pi * |z.im|)) / κ := by
    intro i
    have hpos : 0 < κ * Real.exp (Real.pi * |z.im|) := mul_pos hκ hE
    refine (div_le_div_of_nonneg_left (Real.exp_pos _).le hpos (h i)).trans (le_of_eq ?_)
    rw [show -(2 * Real.pi * |z.im|) = -(Real.pi * |z.im|) + -(Real.pi * |z.im|) by ring,
      Real.exp_add, Real.exp_neg (Real.pi * |z.im|)]
    field_simp
  have key : ∃ J : ℂ, ∀ i, ‖Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) - J‖
      ≤ Real.exp (-(2 * Real.pi * |z.im|)) / κ := by
    by_cases hy : 0 ≤ z.im
    · refine ⟨-Complex.I, fun i => ?_⟩
      rw [sub_neg_eq_add, Decay.norm_cot_add_I _ (hsin i), him i]
      have := hb i
      rwa [abs_of_nonneg hy] at this ⊢
    · refine ⟨Complex.I, fun i => ?_⟩
      rw [Decay.norm_cot_sub_I _ (hsin i), him i]
      have e : Real.pi * z.im = -(Real.pi * |z.im|) := by
        rw [abs_of_neg (not_le.1 hy)]; ring
      rw [e]
      exact hb i
  obtain ⟨J, hJ⟩ := key
  have hw := Decay.norm_wsum_le Fr.w Fr.sum_w_cast
    (fun i => Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))) J _ hJ
  have e : ∑ i, (Fr.w i : ℂ) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))))
      = (Real.pi : ℂ) * ∑ i, (Fr.w i : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  calc Real.pi * ‖∑ i, (Fr.w i : ℂ) * Complex.cot ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))‖
      ≤ Real.pi * ((∑ i, |(Fr.w i : ℝ)|) * (Real.exp (-(2 * Real.pi * |z.im|)) / κ)) :=
        mul_le_mul_of_nonneg_left hw hpi.le
    _ = _ := by ring

end Frame
end CatalanCore
