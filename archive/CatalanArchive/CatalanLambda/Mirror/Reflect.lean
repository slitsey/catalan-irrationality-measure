module

public import CatalanArchive.CatalanLambda.Mirror.Atoms
public import CatalanLambda.Decay.Reflect

@[expose] public section

/-!
# Mirror constant: reflection `F̄ = F̃ + Ē`, `Ē z = ∑_{n ∈ ℤ} [1/(z-n-3/4) - 1/(z-n)]`

Closed form `Ē z = π sin(3π/4) / (sin(πz - 3π/4) sin(πz))` and exponential bounds.
-/

open Complex

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (summable_pairC norm_sin_sq sin_re_le_norm sinh_abs_ge norm_sin_ge
  mem_intCompl_of_im_ne)

theorem norm_sin_three_pi_div_four_le : ‖Complex.sin (3 * (Real.pi : ℂ) / 4)‖ ≤ 1 := by
  have : Complex.sin (3 * (Real.pi : ℂ) / 4) = ((Real.sin (3 * Real.pi / 4) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]; push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.neg_one_le_sin (3 * Real.pi / 4), Real.sin_le_one (3 * Real.pi / 4)]

/-- The `n`-th term of the periodic series: `1/(z-n-1/4) - 1/(z-n)`. -/
noncomputable def etermB (z : ℂ) (n : ℤ) : ℂ := 1 / (z - n - 3 / 4) - 1 / (z - n)

theorem etermB_nat_summable (z : ℂ) : Summable fun n : ℕ => etermB z (n : ℤ) := by
  have h := (summable_pairC (-z) (3 / 4) 0).neg
  refine h.congr (fun n => ?_)
  unfold etermB
  have e1 : z - ((n : ℤ) : ℂ) - 3 / 4 = -(-z + n + ((3 / 4 : ℝ) : ℂ)) := by push_cast; ring
  have e2 : z - ((n : ℤ) : ℂ) = -(-z + n + ((0 : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, e2, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
  ring

theorem etermB_neg_summable (z : ℂ) : Summable fun n : ℕ => etermB z (-((n : ℤ) + 1)) := by
  have h := summable_pairC z (1 / 4) 1
  refine h.congr (fun n => ?_)
  unfold etermB
  have e1 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) - 3 / 4 = z + n + ((1 / 4 : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : z - ((-((n : ℤ) + 1) : ℤ) : ℂ) = z + n + ((1 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]

theorem summable_etermB (z : ℂ) : Summable (etermB z) :=
  Summable.of_nat_of_neg_add_one (etermB_nat_summable z) (etermB_neg_summable z)

/-- `E(z) = ∑_{n ∈ ℤ} [1/(z-n-1/4) - 1/(z-n)]`. -/
noncomputable def ECB (z : ℂ) : ℂ := ∑' n : ℤ, etermB z n

/-- Closed form of `E` via the cotangent series. -/
theorem ECB_eq_cot {z : ℂ} (hz : z ∈ Complex.integerComplement)
    (hz' : z - 3 / 4 ∈ Complex.integerComplement) :
    ECB z = (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (z - 3 / 4))
      - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) := by
  have hs := summable_etermB z
  have inj1 : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b h; simp only at h; omega
  have hs1 : Summable fun n : ℕ => etermB z ((n : ℤ) + 1) := hs.comp_injective inj1
  have hs2 := etermB_neg_summable z
  unfold ECB
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2]
  have c1 : Summable fun n : ℕ => (1 / ((z - 3 / 4) - (n + 1)) + 1 / ((z - 3 / 4) + (n + 1)) : ℂ) :=
    summable_cotTerm hz'
  have c2 : Summable fun n : ℕ => (1 / (z - (n + 1)) + 1 / (z + (n + 1)) : ℂ) :=
    summable_cotTerm hz
  have hp : ∀ n : ℕ, etermB z ((n : ℤ) + 1) + etermB z (-((n : ℤ) + 1))
      = (1 / ((z - 3 / 4) - (n + 1)) + 1 / ((z - 3 / 4) + (n + 1)) : ℂ)
        - (1 / (z - (n + 1)) + 1 / (z + (n + 1))) := by
    intro n; unfold etermB; push_cast; ring
  have h3 := hs1.tsum_add hs2
  simp only [hp] at h3
  rw [Summable.tsum_sub c1 c2] at h3
  have r1 := cot_series_rep' hz'
  have r2 := cot_series_rep' hz
  have e0 : etermB z 0 = 1 / (z - 3 / 4) - 1 / z := by unfold etermB; simp
  have : ∑' n : ℕ, etermB z ((n : ℤ) + 1) + etermB z 0 + ∑' n : ℕ, etermB z (-((n : ℤ) + 1))
      = (∑' n : ℕ, etermB z ((n : ℤ) + 1) + ∑' n : ℕ, etermB z (-((n : ℤ) + 1))) + etermB z 0 := by ring
  rw [this, ← h3, e0, ← r1, ← r2]
  ring

/-- `E(z) = π sin(π/4) / (sin(πz - π/4) sin(πz))`. -/
theorem ECB_eq_sin {z : ℂ} (hz : z ∈ Complex.integerComplement)
    (hz' : z - 3 / 4 ∈ Complex.integerComplement) :
    ECB z = (Real.pi : ℂ) * Complex.sin (3 * (Real.pi : ℂ) / 4)
      / (Complex.sin ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) * z)) := by
  rw [ECB_eq_cot hz hz']
  have hB : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := sin_pi_mul_ne_zero hz
  have hA' : Complex.sin ((Real.pi : ℂ) * (z - 3 / 4)) ≠ 0 := sin_pi_mul_ne_zero hz'
  have hAe : (Real.pi : ℂ) * (z - 3 / 4) = (Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4 := by ring
  rw [hAe] at hA' ⊢
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin]
  have hsub : Complex.sin (3 * (Real.pi : ℂ) / 4)
      = Complex.sin ((Real.pi : ℂ) * z) * Complex.cos ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4)
        - Complex.cos ((Real.pi : ℂ) * z) * Complex.sin ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4) := by
    rw [← Complex.sin_sub]; congr 1; ring
  rw [hsub]
  generalize Complex.sin ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4) = sA at *
  generalize Complex.sin ((Real.pi : ℂ) * z) = sB at *
  field_simp

/-- **Bound away from the real axis**: `‖E z‖ ≤ 16π e^{-2π|Im z|}` for `|Im z| ≥ 1/8`. -/
theorem ECB_norm_le_far (z : ℂ) (hy : 1 / 8 ≤ |z.im|) :
    ‖ECB z‖ ≤ 16 * Real.pi * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hz : z ∈ Complex.integerComplement :=
    mem_intCompl_of_im_ne (by intro h; rw [h] at hy; simp at hy; linarith)
  have hz' : z - 3 / 4 ∈ Complex.integerComplement :=
    mem_intCompl_of_im_ne (by
      intro h; simp at h; rw [h] at hy; simp at hy; linarith)
  rw [ECB_eq_sin hz hz', norm_div, norm_mul, norm_mul]
  have hpi := Real.pi_gt_three
  have hn : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have him1 : ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4).im = Real.pi * z.im := by simp
  have him2 : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  have habs : |Real.pi * z.im| = Real.pi * |z.im| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hge : 3 / 8 ≤ |Real.pi * z.im| := by
    rw [habs]; nlinarith
  have hA := norm_sin_ge ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4) (by rw [him1]; exact hge)
  have hB := norm_sin_ge ((Real.pi : ℂ) * z) (by rw [him2]; exact hge)
  rw [him1, habs] at hA
  rw [him2, habs] at hB
  set E := Real.exp (Real.pi * |z.im|) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hexp : Real.exp (-(2 * Real.pi * |z.im|)) = 1 / (E * E) := by
    rw [hE, ← Real.exp_add, one_div, ← Real.exp_neg]; congr 2; ring
  rw [hexp, hn, div_le_iff₀ (mul_pos (lt_of_lt_of_le (by linarith : 0 < E / 4) hA) (lt_of_lt_of_le (by linarith : 0 < E / 4) hB))]
  have hs := norm_sin_three_pi_div_four_le
  have hAB := mul_le_mul hA hB (by linarith : 0 ≤ E / 4) (norm_nonneg _)
  have hnn := norm_nonneg (Complex.sin (3 * (Real.pi : ℂ) / 4))
  have hEE : 0 < E * E := by positivity
  have : Real.pi * ‖Complex.sin (3 * (Real.pi : ℂ) / 4)‖ ≤ Real.pi := by nlinarith
  calc Real.pi * ‖Complex.sin (3 * (Real.pi : ℂ) / 4)‖ ≤ Real.pi := this
    _ = 16 * Real.pi * (1 / (E * E)) * (E / 4 * (E / 4)) := by field_simp; ring
    _ ≤ 16 * Real.pi * (1 / (E * E)) * (‖Complex.sin ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4)‖
        * ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by
      gcongr

/-- **Bound near the real axis**, away from the poles of `E`. -/
theorem ECB_norm_le_near (z : ℂ) (s : ℝ) (hs : 0 < s)
    (h1 : s ≤ |Real.sin (Real.pi * z.re - 3 * Real.pi / 4)|) (h2 : s ≤ |Real.sin (Real.pi * z.re)|) :
    ‖ECB z‖ ≤ Real.pi / s ^ 2 := by
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, rfl⟩
    have : Real.sin (Real.pi * (n : ℝ)) = 0 := by
      rw [mul_comm]; exact Real.sin_int_mul_pi n
    simp only [Complex.intCast_re] at h2
    rw [this] at h2; simp at h2; linarith
  have hz' : z - 3 / 4 ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hre : z.re = n + 3 / 4 := by
      have := congrArg Complex.re hn
      simp at this; linarith
    have : Real.sin (Real.pi * z.re - 3 * Real.pi / 4) = 0 := by
      rw [hre]
      have : Real.pi * ((n : ℝ) + 3 / 4) - 3 * Real.pi / 4 = (n : ℝ) * Real.pi := by ring
      rw [this]; exact Real.sin_int_mul_pi n
    rw [this] at h1; simp at h1; linarith
  rw [ECB_eq_sin hz hz', norm_div, norm_mul, norm_mul]
  have hn : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hA := sin_re_le_norm ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4)
  have hB := sin_re_le_norm ((Real.pi : ℂ) * z)
  have e1 : ((Real.pi : ℂ) * z - 3 * (Real.pi : ℂ) / 4).re = Real.pi * z.re - 3 * Real.pi / 4 := by simp
  have e2 : ((Real.pi : ℂ) * z).re = Real.pi * z.re := by simp
  rw [e1] at hA; rw [e2] at hB
  have hA' := h1.trans hA
  have hB' := h2.trans hB
  have hs2 := norm_sin_three_pi_div_four_le
  have hnn := norm_nonneg (Complex.sin (3 * (Real.pi : ℂ) / 4))
  rw [hn, div_le_div_iff₀ (mul_pos (lt_of_lt_of_le hs hA') (lt_of_lt_of_le hs hB')) (by positivity)]
  have hAB := mul_le_mul hA' hB' hs.le (by positivity)
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left hs2 hpi.le]

/-- **Uniform exponential bound for `E`** (the shape needed on the rays): if `z` is either at height
`|Im z| ≥ 1/8`, or the real part keeps `sin` of both factors at least `s` away from `0`, then
`‖E z‖ ≤ (16π + π e^{π/4}/s²) · e^{-2π|Im z|}`. -/
theorem ECB_norm_le_uniform (s : ℝ) (hs : 0 < s) (z : ℂ)
    (h : 1 / 8 ≤ |z.im| ∨ (s ≤ |Real.sin (Real.pi * z.re - 3 * Real.pi / 4)| ∧
      s ≤ |Real.sin (Real.pi * z.re)|)) :
    ‖ECB z‖ ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / s ^ 2) *
      Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hpi := Real.pi_pos
  have hexp := Real.exp_pos (-(2 * Real.pi * |z.im|))
  by_cases hy : 1 / 8 ≤ |z.im|
  · have := ECB_norm_le_far z hy
    have h2 : 0 ≤ Real.pi * Real.exp (Real.pi / 4) / s ^ 2 := by positivity
    nlinarith
  · have hn : s ≤ |Real.sin (Real.pi * z.re - 3 * Real.pi / 4)| ∧ s ≤ |Real.sin (Real.pi * z.re)| := by
      rcases h with h | h
      · exact absurd h hy
      · exact h
    have := ECB_norm_le_near z s hs hn.1 hn.2
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


end CatalanLambda.Mirror
