module

public import CatalanCore.Uniform.Decay.Spline.Errors

@[expose] public section

/-!
# The global modulus rule `Ω_g` (lane D, package D5a)

For a spline measure `(A_i, B_i, f_i)` with continuous densities `|f_i| ≤ M_i` on `[0,1]`
(`Bs = ∑ M_i / ‖B_i - A_i‖`, `Vp = ∑ ∫ |f_i|`) and any `a > 0`:

* `U0_modulus_signed` : `|U0 z - U0 w| ≤ 2 π a Bs + Vp/(2a) ‖z - w‖` (any sign);
* `U0_modulus` : for nonnegative densities, `|U0 z - U0 w| ≤ π a Bs + Vp/(2a) ‖z - w‖`;
* `g_modulus` : the certificate field `g = Mm U_σ - U_ν + c |Im z|` (`c = (1-ε)π ≥ 0`) satisfies
  `|g z - g w| ≤ π a (Mm Bσ + Bν) + (Mm Vσ + Vν)/(2a) W + c W` for `‖z - w‖ ≤ W`;
* `Omega_g` : with `Vσ = 1` (probability) and `Vν = Mm` this is the paper's
  `Ω_g(W) = π a (M B_σ + B_ν) + M W / a + (1-ε) π W`.
-/

namespace CatalanCore.Uniform.Decay.Assembly

open Finset intervalIntegral MeasureTheory Set CatalanCore.Uniform.Decay.Spline CatalanLambda.Decay

section

variable {n : ℕ} {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ}

theorem U0_modulus_signed (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, |f i t| ≤ M i) {a : ℝ} (ha : 0 < a) (z w : ℂ) :
    |U0 A B f z - U0 A B f w|
      ≤ 2 * (Real.pi * a * Bs A B M) + Vp f / (2 * a) * ‖z - w‖ := by
  have h1 := smooth_err hAB hf hM ha z
  have h2 := smooth_err hAB hf hM ha w
  have h3 := Urho_lip (A := A) (B := B) hf ha z w
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- One-sidedness of the smoothing for nonnegative densities: `U0 ≥ Urho`. -/
theorem U0_sub_Urho_nonneg (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f i t) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    0 ≤ U0 A B f z - Urho A B f ρ z := by
  unfold U0 Urho
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [← intervalIntegral.integral_sub (intervalIntegrable_f_log hAB hf z i)
    (intervalIntegrable_f_krho hρ hf z i)]
  refine intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ ((z - A i) / (B i - A i)).re := Measure.ae_ne _ _
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Icc] with t ht hmem
  have hLpos : 0 < ‖B i - A i‖ := norm_pos_iff.2 (sub_ne_zero.2 (hAB i).symm)
  have hd := dist_ge z (A i) (B i) (hAB i) t
  have hdpos : 0 < ‖z - (A i + (t : ℂ) * (B i - A i))‖ := by
    refine lt_of_lt_of_le ?_ hd
    exact mul_pos hLpos (abs_pos.2 (sub_ne_zero.2 (Ne.symm ht)))
  set d : ℝ := ‖z - (A i + (t : ℂ) * (B i - A i))‖ with hd'
  have hlog : Real.log d ≤ (1 / 2) * Real.log (d ^ 2 + ρ ^ 2) := by
    have h1 : Real.log (d ^ 2) ≤ Real.log (d ^ 2 + ρ ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ρ])
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have e : f i t * (-Real.log ‖z - pt A B i t‖) - f i t * krho ρ z (pt A B i t)
      = f i t * ((1 / 2) * Real.log (d ^ 2 + ρ ^ 2) - Real.log d) := by
    unfold krho pt
    rw [← hd']
    ring
  show 0 ≤ f i t * (-Real.log ‖z - pt A B i t‖) - f i t * krho ρ z (pt A B i t)
  rw [e]
  exact mul_nonneg (hf0 i t hmem) (by linarith)

/-- **Potential modulus** for nonnegative densities: `|U z - U w| ≤ π a B + V/(2a) ‖z - w‖`. -/
theorem U0_modulus (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f i t) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, |f i t| ≤ M i) {a : ℝ} (ha : 0 < a) (z w : ℂ) :
    |U0 A B f z - U0 A B f w| ≤ Real.pi * a * Bs A B M + Vp f / (2 * a) * ‖z - w‖ := by
  have h1 := smooth_err hAB hf hM ha z
  have h2 := smooth_err hAB hf hM ha w
  have n1 := U0_sub_Urho_nonneg hAB hf hf0 ha z
  have n2 := U0_sub_Urho_nonneg hAB hf hf0 ha w
  have h3 := Urho_lip (A := A) (B := B) hf ha z w
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end

section

variable {n m : ℕ} {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ} {A' B' : Fin m → ℂ}
  {f' : Fin m → ℝ → ℝ}

/-- The certificate field `g = Mm U_σ - U_ν + c |Im z|`. -/
noncomputable def gField (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ) (A' B' : Fin m → ℂ)
    (f' : Fin m → ℝ → ℝ) (Mm c : ℝ) (z : ℂ) : ℝ :=
  Mm * U0 A B f z - U0 A' B' f' z + c * |z.im|

/-- **Modulus of `g`** for nonnegative spline densities `σ` (on `A, B`) and `ν` (on `A', B'`). -/
theorem g_modulus (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f i t) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, |f i t| ≤ M i)
    (hAB' : ∀ i, A' i ≠ B' i) (hf' : ∀ i, Continuous (f' i))
    (hf0' : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f' i t) {M' : Fin m → ℝ}
    (hM' : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, |f' i t| ≤ M' i)
    {Mm c : ℝ} (hMm : 0 ≤ Mm) (hc : 0 ≤ c) {a : ℝ} (ha : 0 < a) (z w : ℂ) :
    |gField A B f A' B' f' Mm c z - gField A B f A' B' f' Mm c w|
      ≤ Real.pi * a * (Mm * Bs A B M + Bs A' B' M')
        + (Mm * Vp f + Vp f') / (2 * a) * ‖z - w‖ + c * ‖z - w‖ := by
  have h1 := U0_modulus hAB hf hf0 hM ha z w
  have h2 := U0_modulus hAB' hf' hf0' hM' ha z w
  have h3 : |(|z.im| - |w.im|)| ≤ ‖z - w‖ := by
    calc |(|z.im| - |w.im|)| ≤ |z.im - w.im| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |(z - w).im| := by simp
      _ ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  have e : gField A B f A' B' f' Mm c z - gField A B f A' B' f' Mm c w
      = Mm * (U0 A B f z - U0 A B f w) - (U0 A' B' f' z - U0 A' B' f' w)
        + c * (|z.im| - |w.im|) := by
    unfold gField; ring
  rw [e]
  have b1 : |Mm * (U0 A B f z - U0 A B f w)| ≤
      Mm * (Real.pi * a * Bs A B M + Vp f / (2 * a) * ‖z - w‖) := by
    rw [abs_mul, abs_of_nonneg hMm]
    exact mul_le_mul_of_nonneg_left h1 hMm
  have b3 : |c * (|z.im| - |w.im|)| ≤ c * ‖z - w‖ := by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left h3 hc
  have t1 := abs_add_le (Mm * (U0 A B f z - U0 A B f w) - (U0 A' B' f' z - U0 A' B' f' w))
    (c * (|z.im| - |w.im|))
  have t2 := abs_sub (Mm * (U0 A B f z - U0 A B f w)) (U0 A' B' f' z - U0 A' B' f' w)
  have : Mm * (Real.pi * a * Bs A B M + Vp f / (2 * a) * ‖z - w‖)
      + (Real.pi * a * Bs A' B' M' + Vp f' / (2 * a) * ‖z - w‖) + c * ‖z - w‖
      = Real.pi * a * (Mm * Bs A B M + Bs A' B' M')
        + (Mm * Vp f + Vp f') / (2 * a) * ‖z - w‖ + c * ‖z - w‖ := by
    field_simp
    ring
  linarith

/-- **`Ω_g`**: the paper's global modulus
`Ω_g(W) = π a (M B_σ + B_ν) + M W / a + c W` (here `c = (1-ε)π`), for a probability `σ`
(`Vp f = 1`) and a measure `ν` of mass `M` (`Vp f' = M`); valid for every `a > 0` and `‖z-w‖ ≤ W`. -/
theorem Omega_g (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f i t) {Mb : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, |f i t| ≤ Mb i)
    (hAB' : ∀ i, A' i ≠ B' i) (hf' : ∀ i, Continuous (f' i))
    (hf0' : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f' i t) {Mb' : Fin m → ℝ}
    (hM' : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, |f' i t| ≤ Mb' i)
    {Mm c : ℝ} (hMm : 0 ≤ Mm) (hc : 0 ≤ c) (hσ : Vp f = 1) (hν : Vp f' = Mm)
    {a W : ℝ} (ha : 0 < a) (z w : ℂ) (hzw : ‖z - w‖ ≤ W) :
    |gField A B f A' B' f' Mm c z - gField A B f A' B' f' Mm c w|
      ≤ Real.pi * a * (Mm * Bs A B Mb + Bs A' B' Mb') + Mm * W / a + c * W := by
  have h := g_modulus hAB hf hf0 hM hAB' hf' hf0' hM' hMm hc ha z w
  rw [hσ, hν] at h
  have hW : 0 ≤ ‖z - w‖ := norm_nonneg _
  have e : (Mm * 1 + Mm) / (2 * a) * ‖z - w‖ = Mm * ‖z - w‖ / a := by field_simp; ring
  rw [e] at h
  have h1 : Mm * ‖z - w‖ / a ≤ Mm * W / a :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzw hMm) ha.le
  have h2 : c * ‖z - w‖ ≤ c * W := mul_le_mul_of_nonneg_left hzw hc
  linarith

end

end CatalanCore.Uniform.Decay.Assembly
