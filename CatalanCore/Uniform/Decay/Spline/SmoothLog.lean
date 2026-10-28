module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The Poisson-type logarithmic integral `∫ (1/2) log (1 + a²/u²) du ≤ π a`  (lane D, D2)

With `phiM a u = (1/2) log (u² + a²) - log u` (even in `u`; equal to `(1/2) log (1 + a²/u²)` for `u ≠ 0`)
and the primitive `Psi a x = (1/2) x log (x² + a²) - x log x + a arctan (x/a)`:

* `Psi_odd`, `Psi_mem` : `|Psi a x| ≤ π a / 2`;
* `hasDerivAt_Psi` : `Psi' = phiM` away from `0`;
* `integral_phiM_le` : `∫_p^q phiM a ≤ π a` for every `p ≤ q`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Real intervalIntegral Set MeasureTheory

theorem log_one_add_sq_le {y : ℝ} (hy : 0 ≤ y) : Real.log (1 + y ^ 2) ≤ 2 * y * Real.arctan y := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 2 * y * Real.arctan y - Real.log (1 + y ^ 2))
      (2 * Real.arctan y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
    have h3 := h1.mul (Real.hasDerivAt_arctan y)
    have h4 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (1 : ℝ)
    have h5 := h4.log (by positivity)
    have h6 := h3.sub h5
    convert h6 using 1
    field_simp
    ring
  have hmono : MonotoneOn (fun y : ℝ => 2 * y * Real.arctan y - Real.log (1 + y ^ 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (fun x _ => (hd x).continuousAt.continuousWithinAt)
    · exact (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have := Real.arctan_nonneg.2 (le_of_lt (mem_Ioi.1 hx))
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simpa using this

/-- The even majorant `(1/2) log (u² + a²) - log |u|`. -/
noncomputable def phiM (a u : ℝ) : ℝ := (1 / 2) * Real.log (u ^ 2 + a ^ 2) - Real.log u

/-- Its primitive. -/
noncomputable def Psi (a x : ℝ) : ℝ :=
  (1 / 2) * (x * Real.log (x ^ 2 + a ^ 2)) - x * Real.log x + a * Real.arctan (x / a)

theorem continuous_Psi (a : ℝ) (ha : 0 < a) : Continuous (Psi a) := by
  unfold Psi
  have h1 : Continuous (fun x : ℝ => x * Real.log (x ^ 2 + a ^ 2)) :=
    continuous_id.mul (Continuous.log (by fun_prop) (fun x => by positivity))
  have h2 := Real.continuous_mul_log
  have h3 : Continuous (fun x : ℝ => a * Real.arctan (x / a)) :=
    continuous_const.mul (Real.continuous_arctan.comp (by fun_prop))
  exact ((continuous_const.mul h1).sub h2).add h3

theorem Psi_neg (a x : ℝ) : Psi a (-x) = - Psi a x := by
  unfold Psi
  rw [Real.log_neg_eq_log, neg_div, Real.arctan_neg]
  have : (-x) ^ 2 = x ^ 2 := by ring
  rw [this]
  ring

theorem hasDerivAt_Psi {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (Psi a) (phiM a x) x := by
  have hpos : x ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + a ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (a ^ 2)
  have h2 := (hasDerivAt_id x).mul (h1.log hpos)
  have h3 := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx)
  have h4 : HasDerivAt (fun x : ℝ => x / a) (1 / a) x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (a⁻¹)
  have h5 := ((Real.hasDerivAt_arctan (x / a)).comp x h4).const_mul a
  have h6 := ((h2.const_mul (1 / 2 : ℝ)).sub h3).add h5
  exact h6.congr_deriv (by simp only [id]; unfold phiM; field_simp; ring)

theorem Psi_nonneg {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Psi a x := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp [Psi]
  unfold Psi
  have h1 : Real.log (x ^ 2) ≤ Real.log (x ^ 2 + a ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h2 : Real.log (x ^ 2) = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have h3 : 0 ≤ a * Real.arctan (x / a) := mul_nonneg ha.le (Real.arctan_nonneg.2 (by positivity))
  nlinarith [mul_le_mul_of_nonneg_left h1 hx]

theorem Psi_le {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) : Psi a x ≤ Real.pi * a / 2 := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp [Psi]; positivity
  · unfold Psi
    set y : ℝ := a / x with hy
    have hy0 : 0 < y := by positivity
    have hxy : x / a = y⁻¹ := by rw [hy]; field_simp
    rw [hxy, Real.arctan_inv_of_pos hy0]
    have hl := log_one_add_sq_le hy0.le
    have e1 : Real.log (x ^ 2 + a ^ 2) - 2 * Real.log x = Real.log (1 + y ^ 2) := by
      have : x ^ 2 + a ^ 2 = x ^ 2 * (1 + y ^ 2) := by rw [hy]; field_simp
      rw [this, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    have e2 : x * y = a := by rw [hy]; field_simp
    have h3 : x * Real.log (1 + y ^ 2) ≤ x * (2 * y * Real.arctan y) :=
      mul_le_mul_of_nonneg_left hl h.le
    have h4 : x * (2 * y * Real.arctan y) = 2 * a * Real.arctan y := by rw [← e2]; ring
    have h5 : x * Real.log (x ^ 2 + a ^ 2) - 2 * x * Real.log x = x * Real.log (1 + y ^ 2) := by
      rw [← e1]; ring
    nlinarith [h3, h4, h5]

theorem Psi_mem {a : ℝ} (ha : 0 < a) (x : ℝ) : |Psi a x| ≤ Real.pi * a / 2 := by
  rw [abs_le]
  rcases le_total 0 x with h | h
  · exact ⟨by linarith [Psi_nonneg ha h, Real.pi_pos, mul_pos Real.pi_pos ha], Psi_le ha h⟩
  · have h' : 0 ≤ -x := by linarith
    have a1 := Psi_nonneg ha h'
    have a2 := Psi_le ha h'
    rw [Psi_neg] at a1 a2
    constructor <;> linarith

theorem intervalIntegrable_phiM {a : ℝ} (ha : 0 < a) (p q : ℝ) :
    IntervalIntegrable (phiM a) volume p q := by
  unfold phiM
  have h1 : Continuous (fun u : ℝ => (1 / 2) * Real.log (u ^ 2 + a ^ 2)) :=
    continuous_const.mul (Continuous.log (by fun_prop) (fun x => by positivity))
  exact (h1.intervalIntegrable _ _).sub (intervalIntegrable_log' (a := p) (b := q))

/-- `∫_p^q phiM a = Psi a q - Psi a p`. -/
theorem integral_phiM_eq {a : ℝ} (ha : 0 < a) {p q : ℝ} (hpq : p ≤ q) :
    ∫ u in p..q, phiM a u = Psi a q - Psi a p := by
  have := integral_eq_of_hasDerivAt_off_countable_of_le (Psi a) (phiM a) hpq
    (Set.countable_singleton (0 : ℝ)) (continuous_Psi a ha).continuousOn
    (fun x hx => hasDerivAt_Psi ha (fun h => hx.2 (by simpa using h)))
    (intervalIntegrable_phiM ha p q)
  exact this

/-- **The Poisson-type integral**: `∫_p^q (1/2) log (1 + a²/u²) du ≤ π a`. -/
theorem integral_phiM_le {a : ℝ} (ha : 0 < a) {p q : ℝ} (hpq : p ≤ q) :
    ∫ u in p..q, phiM a u ≤ Real.pi * a := by
  rw [integral_phiM_eq ha hpq]
  have h1 := Psi_mem ha q
  have h2 := Psi_mem ha p
  rw [abs_le] at h1 h2
  linarith [h1.2, h2.1]

end CatalanCore.Uniform.Decay.Spline
