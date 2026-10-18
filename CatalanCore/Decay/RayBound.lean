module

public import CatalanCore.Decay.Contour
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Exponential decay of `E` along the rays `x* + r e^{±iφ}` (WP2a)

**Finite-`C_E` form (no near-pole constants).**  For every frame with `ContourOK`, every `N0`,
every `φ ∈ (π/2, π)` with `-cos φ ≤ 4 δ0 sin φ`, and every point `z = x* + r e^{±iφ}`:
`‖E z‖ ≤ C_E · e^{-2π|Im z|}` with the explicit constant
`C_E = π (∑ |w_i|) / κ`, `κ = min (1/4) (δ0 e^{-π/8})`, independent of `N0`.

Proof: by `norm_EC_le` it is enough that `‖sin π(z+μ_i)‖ ≥ κ e^{π|Im z|}` for every `i`.
* If `|Im z| ≥ 1/8`: `‖sin w‖ ≥ e^{|Im w|}/4` (`norm_sin_ge`).
* If `|Im z| < 1/8`: the ray has moved horizontally by `δ = -r cos φ ≤ δ0/2` from `x*`, so by
  `ContourGap` the real parts `Re z + μ_i` keep distance `≥ δ0/2` from `ℤ`, and
  `|sin πu| ≥ 2 dist(u, ℤ)` gives `‖sin w‖ ≥ δ0`.

The hypothesis `-cos φ ≤ 4 δ0 sin φ` holds for the legacy `φ = 3π/5` and for all three frames
(`cot_phiC`); P6's rays `x* + u(-1 ± 3i)` have `-cos φ / sin φ = 1/3`.

At the end: three `example`s instantiate everything at `lamFrame`, `mirrorFrame`, `p6Frame`.
-/

open Complex

namespace CatalanCore
namespace Frame

open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos rayPt_re rayPt_im)

/-- `|sin πu| ≥ 2g` if `u` keeps distance `g` from every integer. -/
lemma two_mul_le_abs_sin_pi {u g : ℝ} (h : ∀ n : ℤ, g ≤ |u - n|) :
    2 * g ≤ |Real.sin (Real.pi * u)| := by
  have hpi := Real.pi_pos
  set n : ℤ := round u with hn
  set t := u - n with ht
  have ht2 : |t| ≤ 1 / 2 := abs_sub_round u
  have hgt : g ≤ |t| := h n
  have e : Real.sin (Real.pi * u) = (-1) ^ n * Real.sin (Real.pi * t) := by
    have : Real.pi * u = Real.pi * t + n * Real.pi := by rw [ht]; ring
    rw [this, Real.sin_add_int_mul_pi]
  have habs : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * t)| := by
    rw [e, abs_mul]; simp
  rw [habs]
  have hs : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t|) := by
    rcases abs_cases t with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [abs_nonneg t]))
    · rw [h1, mul_neg, Real.sin_neg]
      exact abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith)
        (by nlinarith [abs_nonneg t]))
  rw [hs]
  have h3 := Real.mul_le_sin (x := Real.pi * |t|) (by positivity) (by nlinarith [abs_nonneg t])
  have e2 : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
  linarith

/-- The uniform sine constant `κ`. -/
noncomputable def sinKappa (Fr : Frame) : ℝ :=
  min (1 / 4) ((Fr.δ0 : ℝ) * Real.exp (-(Real.pi / 8)))

/-- The finite constant `C_E` (independent of `N0`). -/
noncomputable def rayConst (Fr : Frame) : ℝ :=
  Real.pi * (∑ i, |(Fr.w i : ℝ)|) / Fr.sinKappa

variable {Fr : Frame}

lemma sinKappa_pos (hC : Fr.ContourOK) : 0 < Fr.sinKappa := by
  have : (0 : ℝ) < Fr.δ0 := by exact_mod_cast hC.gap.1
  unfold sinKappa
  exact lt_min (by norm_num) (by positivity)

lemma rayConst_nonneg (hC : Fr.ContourOK) : 0 ≤ Fr.rayConst := by
  have := sinKappa_pos hC
  unfold rayConst
  positivity

/-- `|Im|` and `Re` of a ray point. -/
lemma ray_im_abs {φ : ℝ} (hφ2 : φ < Real.pi) (hφ1 : Real.pi / 2 < φ) {θ : ℝ}
    (hθ : θ = φ ∨ θ = -φ) {x r : ℝ} (hr : 0 ≤ r) :
    |(rayPt x θ r).im| = r * Real.sin φ := by
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hφ2
  rw [rayPt_im]
  have : |Real.sin θ| = Real.sin φ := by
    rcases hθ with h | h
    · rw [h]; exact abs_of_pos hsφ
    · rw [h, Real.sin_neg, abs_neg]; exact abs_of_pos hsφ
  rw [abs_mul, abs_of_nonneg hr, this]

/-- **Sine lower bound at the shifts, along the rays.** -/
theorem sin_lower_ray (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 4 * (Fr.δ0 : ℝ) * Real.sin φ) (N0 : ℕ) {θ : ℝ}
    (hθ : θ = φ ∨ θ = -φ) {r : ℝ} (hr : 0 ≤ r) (i : Fin Fr.d) :
    Fr.sinKappa * Real.exp (Real.pi * |(rayPt (Fr.xstar N0) θ r).im|)
      ≤ ‖Complex.sin ((Real.pi : ℂ) * (rayPt (Fr.xstar N0) θ r + (Fr.μ i : ℂ)))‖ := by
  have hpi := Real.pi_pos
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2
  have hcφ : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  have hcosθ : Real.cos θ = Real.cos φ := by
    rcases hθ with h | h <;> simp [h]
  have habs := ray_im_abs h2 h1 hθ (x := Fr.xstar N0) hr
  have hδ0 : (0 : ℝ) < Fr.δ0 := by exact_mod_cast hC.gap.1
  set z := rayPt (Fr.xstar N0) θ r with hz
  have hwim : ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).im = Real.pi * z.im := by simp
  have hwre : ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).re = Real.pi * (z.re + (Fr.μ i : ℝ)) := by simp
  by_cases hbig : 1 / 8 ≤ |z.im|
  · have hge : 3 / 8 ≤ |((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).im| := by
      rw [hwim, abs_mul, abs_of_pos hpi]
      nlinarith [Real.pi_gt_three]
    have h := Decay.norm_sin_ge _ hge
    rw [hwim, abs_mul, abs_of_pos hpi] at h
    refine le_trans ?_ h
    have hκ : Fr.sinKappa ≤ 1 / 4 := min_le_left _ _
    have := Real.exp_pos (Real.pi * |z.im|)
    nlinarith
  · push_neg at hbig
    have hre : z.re = Fr.xstar N0 + r * Real.cos φ := by rw [hz, rayPt_re, hcosθ]
    set δ := -(r * Real.cos φ) with hδ
    have hδ0' : 0 ≤ δ := by nlinarith
    have hδ1 : δ ≤ (Fr.δ0 : ℝ) / 2 := by
      have hrs : r * Real.sin φ ≤ 1 / 8 := by rw [← habs]; exact hbig.le
      have : δ ≤ 4 * (Fr.δ0 : ℝ) * (r * Real.sin φ) := by
        rw [hδ]; nlinarith [mul_le_mul_of_nonneg_left hcot hr]
      nlinarith
    have hdist : ∀ n : ℤ, (Fr.δ0 : ℝ) / 2 ≤ |(z.re + (Fr.μ i : ℝ)) - n| := by
      intro n
      have hg := hC.gap.2 i (-(N0 : ℤ) - n)
      have hg' : (Fr.δ0 : ℝ) ≤ |((-(N0 : ℤ) - n : ℤ) : ℝ) + (Fr.μ i : ℝ) - (Fr.xs : ℝ)| := by
        exact_mod_cast hg
      have e : (z.re + (Fr.μ i : ℝ)) - n
          = (((-(N0 : ℤ) - n : ℤ) : ℝ) + (Fr.μ i : ℝ) - (Fr.xs : ℝ)) - δ := by
        rw [hre, hδ]; unfold xstar; push_cast; ring
      rw [e]
      have h5 := abs_sub_abs_le_abs_sub
        (((-(N0 : ℤ) - n : ℤ) : ℝ) + (Fr.μ i : ℝ) - (Fr.xs : ℝ)) δ
      rw [abs_of_nonneg hδ0'] at h5
      linarith
    have hsin := two_mul_le_abs_sin_pi hdist
    have h6 := Decay.sin_re_le_norm ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))
    rw [hwre] at h6
    have hexp : Real.exp (Real.pi * |z.im|) ≤ Real.exp (Real.pi / 8) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hκ : Fr.sinKappa ≤ (Fr.δ0 : ℝ) * Real.exp (-(Real.pi / 8)) := min_le_right _ _
    calc Fr.sinKappa * Real.exp (Real.pi * |z.im|)
        ≤ ((Fr.δ0 : ℝ) * Real.exp (-(Real.pi / 8))) * Real.exp (Real.pi / 8) :=
          mul_le_mul hκ hexp (Real.exp_pos _).le (by positivity)
      _ = Fr.δ0 := by rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := by linarith

/-- **`ray_E_bound`.**  `‖E(x* + r e^{±iφ})‖ ≤ C_E e^{-2π r sin φ}` with `C_E = rayConst` finite and
independent of `N0`. -/
theorem ray_E_bound (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 4 * (Fr.δ0 : ℝ) * Real.sin φ) (N0 : ℕ) {θ : ℝ}
    (hθ : θ = φ ∨ θ = -φ) {r : ℝ} (hr : 0 ≤ r) :
    ‖Fr.EC (rayPt (Fr.xstar N0) θ r)‖
      ≤ Fr.rayConst * Real.exp (-(2 * Real.pi * (r * Real.sin φ))) := by
  have := Fr.norm_EC_le (sinKappa_pos hC) (fun i => sin_lower_ray hC h1 h2 hcot N0 hθ hr i)
  rw [ray_im_abs h2 h1 hθ hr] at this
  exact this

/-- **`E_bound`** (design 2.6): a finite constant `C_E`, independent of `N0`. -/
theorem E_bound (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 4 * (Fr.δ0 : ℝ) * Real.sin φ) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (N0 : ℕ) (θ : ℝ), (θ = φ ∨ θ = -φ) → ∀ r : ℝ, 0 ≤ r →
      ‖Fr.EC (rayPt (Fr.xstar N0) θ r)‖ ≤ CE * Real.exp (-(2 * Real.pi * (r * Real.sin φ))) :=
  ⟨Fr.rayConst, rayConst_nonneg hC, fun N0 _ hθ _ hr => ray_E_bound hC h1 h2 hcot N0 hθ hr⟩

/-- The integrable majorant on the rays:
`‖E v_a v_b‖ ≤ C_E e^{-2π r sin φ} / (κ² (xs + r)²)`, `κ² = (1 - |cos φ|)/2`. -/
theorem Ev_ray_bound (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 4 * (Fr.δ0 : ℝ) * Real.sin φ) (N0 a b : ℕ) {θ : ℝ}
    (hθ : θ = φ ∨ θ = -φ) {r : ℝ} (hr : 0 ≤ r) :
    ‖Fr.EC (rayPt (Fr.xstar N0) θ r) *
        ((rayPt (Fr.xstar N0) θ r - a)⁻¹ * (rayPt (Fr.xstar N0) θ r - b)⁻¹)‖
      ≤ Fr.rayConst * Real.exp (-(2 * Real.pi * (r * Real.sin φ)))
        * (1 / (Real.sqrt (kap2 θ) * ((Fr.xs : ℝ) + r))
          * (1 / (Real.sqrt (kap2 θ) * ((Fr.xs : ℝ) + r)))) := by
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h2
  have hs : Real.sin θ ≠ 0 := by
    rcases hθ with h | h
    · rw [h]; exact ne_of_gt hsφ
    · rw [h, Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt hsφ)
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  rw [norm_mul, norm_mul]
  exact mul_le_mul (ray_E_bound hC h1 h2 hcot N0 hθ hr)
    (mul_le_mul (norm_inv_ray_nat_le hC N0 a hs hr) (norm_inv_ray_nat_le hC N0 b hs hr)
      (norm_nonneg _) (by positivity))
    (by positivity) (by have := rayConst_nonneg hC; positivity)

end Frame

/-! ### The three frames -/

namespace Decay

/-- The opening angle `φ = 3π/5` used by the legacy code. -/
noncomputable def phiC : ℝ := 3 * Real.pi / 5

lemma phiC_gt : Real.pi / 2 < phiC := by unfold phiC; linarith [Real.pi_pos]
lemma phiC_lt : phiC < Real.pi := by unfold phiC; linarith [Real.pi_pos]

/-- `-cos φ ≤ sin φ` for `φ = 3π/5`; hence `-cos φ ≤ 4 δ0 sin φ` whenever `δ0 ≥ 1/4`. -/
lemma cot_phiC : -Real.cos phiC ≤ Real.sin phiC := by
  have hpi := Real.pi_pos
  have e1 : phiC = Real.pi - 2 * Real.pi / 5 := by unfold phiC; ring
  rw [e1, Real.cos_pi_sub, Real.sin_pi_sub, neg_neg, ← Real.sin_pi_div_two_sub]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

lemma cot_phiC' {δ0 : ℚ} (h : (1 : ℚ) / 4 ≤ δ0) :
    -Real.cos phiC ≤ 4 * (δ0 : ℝ) * Real.sin phiC := by
  have hs : 0 < Real.sin phiC :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [phiC_gt, Real.pi_pos]) phiC_lt
  have h' : (1 : ℝ) ≤ 4 * (δ0 : ℝ) := by
    have : ((1 : ℚ) / 4 : ℚ) ≤ δ0 := h
    have h2 : ((1 : ℚ) / 4 : ℝ) ≤ (δ0 : ℝ) := by exact_mod_cast this
    push_cast at h2; linarith
  nlinarith [cot_phiC]

lemma gap_aux (m xs δ : ℚ) (k : ℤ) (h1 : δ ≤ m - xs + k) (h2 : m - xs + k - 1 ≤ -δ) (n : ℤ) :
    δ ≤ |(n : ℚ) + m - xs| := by
  rcases le_or_gt k n with h | h
  · have : (k : ℚ) ≤ n := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self _)
  · have : (n : ℚ) ≤ k - 1 := by
      have : n ≤ k - 1 := by omega
      exact_mod_cast this
    exact le_trans (by linarith) (neg_le_abs _)

/-- λ: `μ = ![3/4, 1]`, `w = ![-1, 1]`, contour `x* = -N0 - 3/8`. -/
def lamFrame : Frame where
  d := 2
  μ := ![3 / 4, 1]
  w := ![-1, 1]
  norm := 16
  xs := 3 / 8
  δ0 := 3 / 8
  n0off := 0
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

/-- The mirror frame λ': `μ = ![1/4, 1]`, contour `x* = -N0 - 5/8`
(legacy `x* = -N0' + 3/8` with `N0 = N0' - 1`). -/
def mirrorFrame : Frame where
  d := 2
  μ := ![1 / 4, 1]
  w := ![-1, 1]
  norm := 16
  xs := 5 / 8
  δ0 := 3 / 8
  n0off := 1
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

/-- P6: `μ = ![1, 1/3, 1/2]`, `w = ![1, 2, -3]`, contour `x* = -N0 - 3/4`, pole distance `1/4`. -/
def p6Frame : Frame where
  d := 3
  μ := ![1, 1 / 3, 1 / 2]
  w := ![1, 2, -3]
  norm := 36
  xs := 3 / 4
  δ0 := 1 / 4
  n0off := 1
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  hw := by simp [Fin.sum_univ_three]
  hnorm := by norm_num

theorem lam_contourOK : lamFrame.ContourOK where
  xs_pos := by norm_num [lamFrame]
  gap := by
    refine ⟨by norm_num [lamFrame], fun i n => ?_⟩
    fin_cases i
    · exact gap_aux (3 / 4) (3 / 8) (3 / 8) 0 (by norm_num) (by norm_num) n
    · exact gap_aux 1 (3 / 8) (3 / 8) 0 (by norm_num) (by norm_num) n

theorem mirror_contourOK : mirrorFrame.ContourOK where
  xs_pos := by norm_num [mirrorFrame]
  gap := by
    refine ⟨by norm_num [mirrorFrame], fun i n => ?_⟩
    fin_cases i
    · exact gap_aux (1 / 4) (5 / 8) (3 / 8) 1 (by norm_num) (by norm_num) n
    · exact gap_aux 1 (5 / 8) (3 / 8) 0 (by norm_num) (by norm_num) n

theorem p6_contourOK : p6Frame.ContourOK where
  xs_pos := by norm_num [p6Frame]
  gap := by
    refine ⟨by norm_num [p6Frame], fun i n => ?_⟩
    fin_cases i
    · exact gap_aux 1 (3 / 4) (1 / 4) 0 (by norm_num) (by norm_num) n
    · exact gap_aux (1 / 3) (3 / 4) (1 / 4) 1 (by norm_num) (by norm_num) n
    · exact gap_aux (1 / 2) (3 / 4) (1 / 4) 1 (by norm_num) (by norm_num) n

/-- Three instances of `E_bound`. -/
example := Frame.E_bound lam_contourOK phiC_gt phiC_lt (cot_phiC' (by norm_num [lamFrame]))
example := Frame.E_bound mirror_contourOK phiC_gt phiC_lt (cot_phiC' (by norm_num [mirrorFrame]))
example := Frame.E_bound p6_contourOK phiC_gt phiC_lt (cot_phiC' (by norm_num [p6Frame]))

/-- Three instances of the contour identity. -/
example (N0 a b : ℕ) := Frame.contour_identity lam_contourOK phiC_gt phiC_lt N0 a b
example (N0 a b : ℕ) := Frame.contour_identity mirror_contourOK phiC_gt phiC_lt N0 a b
example (N0 a b : ℕ) := Frame.contour_identity p6_contourOK phiC_gt phiC_lt N0 a b

end Decay
end CatalanCore
