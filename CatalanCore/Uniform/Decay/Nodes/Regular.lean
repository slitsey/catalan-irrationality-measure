module
public import CatalanCore.Uniform.Decay.Nodes.Scaled
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
@[expose] public section

/-!
# The regularised interval potential `κ` (point `x + i`, unit regularisation)

`kap x y = -(1/2) log ((x-y)² + 1) = elog (x + i) y`.  Its interval integral has the closed form
`kapInt lo hi x = -(1/2) (Gk (x - lo) - Gk (x - hi))` with `Gk s = s log (1+s²) - 2 s + 2 arctan s`
(log, linear and arctan terms), `Gk' = log (1+s²)`.  The difference from the exact interval
potential is bounded by the bounded function `A = Gk/2 - Lam`, `|A| ≤ 3`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset MeasureTheory Set intervalIntegral

noncomputable def Gk (s : ℝ) : ℝ := s * Real.log (1 + s ^ 2) - 2 * s + 2 * Real.arctan s

theorem hasDerivAt_Gk (s : ℝ) : HasDerivAt Gk (Real.log (1 + s ^ 2)) s := by
  have hpos : (1 + s ^ 2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
    have := (hasDerivAt_pow 2 s).const_add 1
    simpa using this
  have h2 := (h1.log hpos)
  have h3 := ((hasDerivAt_id s).mul h2).sub ((hasDerivAt_id s).const_mul 2)
  have h4 := h3.add ((Real.hasDerivAt_arctan s).const_mul 2)
  refine h4.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem continuous_Gk : Continuous Gk := by
  unfold Gk
  have : Continuous fun s : ℝ => Real.log (1 + s ^ 2) :=
    Continuous.log (by fun_prop) (fun s => by positivity)
  exact ((continuous_id.mul this).sub (continuous_const.mul continuous_id)).add
    (continuous_const.mul Real.continuous_arctan)

/-- The regularised kernel `elog (x + i) y`. -/
noncomputable def kap (x y : ℝ) : ℝ := -(1 / 2) * Real.log ((x - y) ^ 2 + 1)

theorem elog_regI (x y : ℝ) : CatalanLambda.Decay.elog ((x : ℂ) + Complex.I) (y : ℂ) = kap x y := by
  rw [← kern_eq_elog]
  unfold kern kap
  simp

/-- Closed form of the regularised interval potential. -/
noncomputable def kapInt (lo hi x : ℝ) : ℝ := -(1 / 2) * (Gk (x - lo) - Gk (x - hi))

theorem integral_kap (lo hi x : ℝ) : ∫ y in lo..hi, kap x y = kapInt lo hi x := by
  have h1 : ∀ y : ℝ, kap x y = (fun s : ℝ => -(1 / 2) * Real.log (s ^ 2 + 1)) (x - y) := fun y => rfl
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => -(1 / 2) * Real.log (s ^ 2 + 1)) x]
  rw [intervalIntegral.integral_const_mul]
  have : ∫ s in (x - hi)..(x - lo), Real.log (s ^ 2 + 1) = Gk (x - lo) - Gk (x - hi) := by
    have hd : ∀ s ∈ uIcc (x - hi) (x - lo), HasDerivAt Gk (Real.log (s ^ 2 + 1)) s := by
      intro s _
      have := hasDerivAt_Gk s
      rwa [add_comm 1 (s ^ 2)] at this
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_
    exact (Continuous.log (by fun_prop) (fun s => by positivity)).intervalIntegrable _ _
  rw [this]
  unfold kapInt
  ring

/-- The bounded difference between the exact and regularised potentials. -/
noncomputable def Abnd (s : ℝ) : ℝ := Gk s / 2 - Lam s

theorem log_one_add_sq_le (u : ℝ) (hu : 0 ≤ u) : Real.log (1 + u ^ 2) ≤ u := by
  have h := Real.sum_le_exp_of_nonneg hu 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have hpos : 0 < 1 + u ^ 2 := by positivity
  rw [Real.log_le_iff_le_exp hpos]
  nlinarith [sq_nonneg (u - 3 / 2), pow_nonneg hu 3]

theorem abs_Abnd_le (s : ℝ) : |Abnd s| ≤ 3 := by
  have hpi := Real.arctan_lt_pi_div_two s
  have hpi' := Real.neg_pi_div_two_lt_arctan s
  have hpi3 : Real.pi ≤ 4 := Real.pi_le_four
  -- core bound |B s| ≤ 1/2 with B s = s (log(1+s²)/2 - log|s|)
  have hB : ∀ s : ℝ, 0 < s → 0 ≤ s * (Real.log (1 + s ^ 2) / 2 - Real.log s) ∧
      s * (Real.log (1 + s ^ 2) / 2 - Real.log s) ≤ 1 / 2 := by
    intro s hs
    have e : Real.log (1 + s ^ 2) / 2 - Real.log s = Real.log (1 + (1 / s) ^ 2) / 2 := by
      have : (1 + s ^ 2) = s ^ 2 * (1 + (1 / s) ^ 2) := by field_simp; ring
      rw [this, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    rw [e]
    have h0 : 0 ≤ Real.log (1 + (1 / s) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (1 / s)])
    have h1 := log_one_add_sq_le (1 / s) (by positivity)
    constructor
    · positivity
    · calc s * (Real.log (1 + (1 / s) ^ 2) / 2) ≤ s * ((1 / s) / 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hs.le
        _ = 1 / 2 := by field_simp
  have hAexp : Abnd s = s * (Real.log (1 + s ^ 2) / 2 - Real.log s) + Real.arctan s := by
    unfold Abnd Gk Lam
    ring
  rw [hAexp]
  rcases lt_trichotomy s 0 with h | h | h
  · have hb := hB (-s) (by linarith)
    have e : (-s) * (Real.log (1 + (-s) ^ 2) / 2 - Real.log (-s)) =
        -(s * (Real.log (1 + s ^ 2) / 2 - Real.log s)) := by
      rw [neg_sq, Real.log_neg_eq_log]; ring
    rw [e] at hb
    rw [abs_le]; constructor <;> nlinarith [hb.1, hb.2]
  · subst h; simp
  · have hb := hB s h
    rw [abs_le]; constructor <;> nlinarith [hb.1, hb.2]

end CatalanCore.Uniform.Decay.Nodes
