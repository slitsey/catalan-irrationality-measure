module

public import CatalanCore.Uniform.Decay.Cells.Facts
public import CatalanCore.Uniform.Decay.PairEnergy.Pot

@[expose] public section

/-!
# Continuity and integrability of segment potentials (lane D, package D6c)

* `segPot_continuous`: `z ↦ ∫₀¹ g(t) (-log ‖z - (A + t (B-A))‖) dt` is continuous for continuous `g`
  (the global modulus `U0_modulus_signed` for a one-segment family);
* `intervalIntegrable_pot`: `t ↦ h(t) log ‖z - (A + t (B-A))‖` is interval integrable for continuous
  `h`, for every `z` (including `z` on the segment).
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Cells

theorem segPot_continuous (A0 B0 : ℂ) (hAB : A0 ≠ B0) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (fun z : ℂ => ∫ t in (0 : ℝ)..1, g t * (-Real.log ‖z - (A0 + (t : ℂ) * (B0 - A0))‖)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hAB' : ∀ _i : Fin 1, (fun _ : Fin 1 => A0) _i ≠ (fun _ : Fin 1 => B0) _i := fun _ => hAB
  have hBs : 0 ≤ Bs (fun _ : Fin 1 => A0) (fun _ : Fin 1 => B0) (fun _ => M) := by
    unfold Bs
    exact Finset.sum_nonneg fun i _ => div_nonneg hM0 (norm_nonneg _)
  refine continuous_of_modulus (K := 2 * (Real.pi * Bs (fun _ : Fin 1 => A0) (fun _ : Fin 1 => B0)
    (fun _ => M))) (V := Vp (fun _ : Fin 1 => g)) (by positivity) (Vp_nonneg _) ?_
  intro a ha z w
  have := U0_modulus_signed (A := fun _ : Fin 1 => A0) (B := fun _ : Fin 1 => B0)
    (f := fun _ : Fin 1 => g) hAB' (fun _ => hg) (M := fun _ => M)
    (fun _ t ht => by simpa using hM t ht) ha z w
  have e : 2 * (Real.pi * a * Bs (fun _ : Fin 1 => A0) (fun _ : Fin 1 => B0) (fun _ => M))
      = 2 * (Real.pi * Bs (fun _ : Fin 1 => A0) (fun _ : Fin 1 => B0) (fun _ => M)) * a := by ring
  rw [e] at this
  simpa [U0, pt] using this

/-- Integrability of a continuous multiple of the log of the distance to a segment. -/
theorem intervalIntegrable_pot (A B z : ℂ) (hu : B - A ≠ 0) {h : ℝ → ℝ} (hh : Continuous h) :
    IntervalIntegrable (fun t : ℝ => h t * Real.log ‖z - (A + (t : ℂ) * (B - A))‖) volume 0 1 := by
  set ζ : ℂ := (z - A) / (B - A) with hζ
  have hform : ∀ t : ℝ, z - (A + (t : ℂ) * (B - A)) = -((B - A) * ((t : ℂ) - ζ)) := by
    intro t; rw [hζ]; field_simp; ring
  by_cases him : ζ.im = 0
  · -- real case: log ‖t - ζ‖ = log |t - r|
    set r : ℝ := ζ.re
    have hz : ζ = (r : ℂ) := by apply Complex.ext <;> simp [r, him]
    have hlog : IntervalIntegrable (fun t : ℝ => Real.log |t - r|) volume 0 1 := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0 - r) (b := 1 - r)).comp_sub_right r
      simpa [Real.log_abs] using this
    have h2 : IntervalIntegrable (fun t : ℝ => Real.log ‖B - A‖ + Real.log |t - r|) volume 0 1 :=
      intervalIntegrable_const.add hlog
    have h3 := h2.continuousOn_mul (g := h) hh.continuousOn
    refine intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 h3).congr_fun_ae ?_)
    have hae : ∀ᵐ x : ℝ ∂volume, x ∉ ({r} : Set ℝ) := (Set.countable_singleton r).ae_notMem _
    filter_upwards [ae_restrict_of_ae hae] with t ht
    have htr : (t : ℂ) - ζ ≠ 0 := by
      rw [hz]; intro h0
      apply ht
      have : t = r := by exact_mod_cast sub_eq_zero.1 h0
      simp [this]
    have hn : ‖(t : ℂ) - ζ‖ = |t - r| := by
      rw [hz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hform t, norm_neg, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr htr), hn]

  · have hc : Continuous (fun t : ℝ => Real.log ‖z - (A + (t : ℂ) * (B - A))‖) := by
      refine Continuous.log (by fun_prop) fun t => ?_
      rw [hform]
      have : (t : ℂ) - ζ ≠ 0 := fun h0 => him (by
        have := congrArg Complex.im h0; simpa using this)
      simp [norm_ne_zero_iff, hu, this]
    exact (hh.mul hc).intervalIntegrable _ _

end CatalanCore.Uniform.Decay.PairEnergy
