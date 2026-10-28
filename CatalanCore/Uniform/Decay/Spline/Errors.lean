module

public import CatalanCore.Uniform.Decay.Spline.Atoms
public import CatalanCore.Uniform.Decay.Spline.Smooth

@[expose] public section

/-!
# Smoothing and midpoint errors for the potential and the energy (lane D, package D2)

For a spline trial measure (pieces `i`: segment `pt A B i`, continuous density `f i`):

* `U0 z = ∑ ∫ f_i (-log ‖z - pt_i‖)`, `Urho ρ z = ∑ ∫ f_i k_ρ(z, pt_i)`;
* `I0 = ∑ ∫ f_i U0(pt_i)`, `Irho0 ρ = ∑ ∫ f_i Urho(pt_i)`;
* `Vp = ∑ ∫ |f_i|`, `Bs M = ∑ M_i / ‖B_i - A_i‖` (arclength-density sum, `|f_i| ≤ M_i`).

Theorems:
* `smooth_err` : `|U0 z - Urho ρ z| ≤ π ρ Bs`.
* `energy_smooth_err` : `|I0 - Irho0 ρ| ≤ Vp π ρ Bs`.
* `usig_atom_err` : `|Usig ρ cK wK z - Urho ρ z| ≤ etaN` (all `z`).
* `energy_atom_err` : `|Irho ρ cK wK - Irho0 ρ| ≤ 2 Vp etaN`.
Here `etaN = (1/(2ρ)) ∑ (L_i/(2N)) ∫|f_i|` is the mesh loss, `→ 0` as `N → ∞`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral MeasureTheory CatalanLambda.Decay

variable {n : ℕ} (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ)

/-- The exact logarithmic potential `∑ ∫ f_i(t) (-log ‖z - pt_i(t)‖) dt`. -/
noncomputable def U0 (z : ℂ) : ℝ :=
  ∑ i, ∫ t in (0 : ℝ)..1, f i t * (-Real.log ‖z - pt A B i t‖)

/-- The `ρ`-smoothed potential. -/
noncomputable def Urho (ρ : ℝ) (z : ℂ) : ℝ :=
  ∑ i, ∫ t in (0 : ℝ)..1, f i t * krho ρ z (pt A B i t)

/-- The exact energy `∑ ∫ f_i U0(pt_i)`. -/
noncomputable def I0 : ℝ := ∑ i, ∫ t in (0 : ℝ)..1, f i t * U0 A B f (pt A B i t)

/-- The smoothed energy. -/
noncomputable def Irho0 (ρ : ℝ) : ℝ := ∑ i, ∫ t in (0 : ℝ)..1, f i t * Urho A B f ρ (pt A B i t)

/-- Presentation total variation. -/
noncomputable def Vp : ℝ := ∑ i, ∫ t in (0 : ℝ)..1, |f i t|

/-- Arclength-density sum. -/
noncomputable def Bs (M : Fin n → ℝ) : ℝ := ∑ i, M i / ‖B i - A i‖

/-- The mesh loss of the midpoint atomisation. -/
noncomputable def etaN (ρ : ℝ) (N : ℕ) : ℝ :=
  (1 / (2 * ρ)) * ∑ i, (‖B i - A i‖ / (2 * N)) * ∫ t in (0 : ℝ)..1, |f i t|

theorem Vp_nonneg : 0 ≤ Vp f := Finset.sum_nonneg (fun i _ =>
  intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg _))

theorem etaN_nonneg {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) : 0 ≤ etaN A B f ρ N :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg _))))

variable {A B f}

theorem continuous_krho {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : Continuous (krho ρ z) :=
  continuous_of_lip (by positivity) (krho_lip hρ z)

theorem intervalIntegrable_f_krho {ρ : ℝ} (hρ : 0 < ρ) (hf : ∀ i, Continuous (f i)) (z : ℂ) (i : Fin n) :
    IntervalIntegrable (fun t => f i t * krho ρ z (pt A B i t)) volume 0 1 :=
  ((hf i).mul ((continuous_krho hρ z).comp (continuous_pt A B i))).intervalIntegrable _ _

theorem intervalIntegrable_f_log (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) (z : ℂ)
    (i : Fin n) :
    IntervalIntegrable (fun t => f i t * (-Real.log ‖z - pt A B i t‖)) volume 0 1 :=
  (intervalIntegrable_log_dist z (A i) (B i) (hAB i)).neg.continuousOn_mul (hf i).continuousOn

/-- **Smoothing of the potential**: `|U - U_ρ| ≤ π ρ B`. -/
theorem smooth_err (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    |U0 A B f z - Urho A B f ρ z| ≤ Real.pi * ρ * Bs A B M := by
  unfold U0 Urho Bs
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [← intervalIntegral.integral_sub (intervalIntegrable_f_log hAB hf z i)
    (intervalIntegrable_f_krho hρ hf z i)]
  have e : ∀ t : ℝ, f i t * (-Real.log ‖z - pt A B i t‖) - f i t * krho ρ z (pt A B i t)
      = f i t * ((1 / 2) * Real.log (‖z - (A i + (t : ℂ) * (B i - A i))‖ ^ 2 + ρ ^ 2)
          - Real.log ‖z - (A i + (t : ℂ) * (B i - A i))‖) := by
    intro t
    unfold krho pt
    ring
  simp_rw [e]
  have := piece_smooth z (A i) (B i) (hAB i) hρ (hf i) (hM i)
  calc _ ≤ M i * (Real.pi * ρ / ‖B i - A i‖) := this
    _ = Real.pi * ρ * (M i / ‖B i - A i‖) := by ring

/-- `Urho` is Lipschitz with constant `Vp / (2ρ)`. -/
theorem Urho_lip (hf : ∀ i, Continuous (f i)) {ρ : ℝ} (hρ : 0 < ρ) (z z' : ℂ) :
    |Urho A B f ρ z - Urho A B f ρ z'| ≤ (Vp f / (2 * ρ)) * ‖z - z'‖ := by
  unfold Urho Vp
  rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [← intervalIntegral.integral_sub (intervalIntegrable_f_krho hρ hf z i)
    (intervalIntegrable_f_krho hρ hf z' i)]
  have hint : IntervalIntegrable (fun t => |f i t| * ((1 / (2 * ρ)) * ‖z - z'‖)) volume 0 1 :=
    ((hf i).abs.mul continuous_const).intervalIntegrable _ _
  have := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t => f i t * krho ρ z (pt A B i t) - f i t * krho ρ z' (pt A B i t))
    (g := fun t => |f i t| * ((1 / (2 * ρ)) * ‖z - z'‖))
    (Filter.Eventually.of_forall (fun t _ => by
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (krho_lip_left hρ z z' _) (abs_nonneg _))) hint
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const]
  ring

theorem continuous_Urho (hf : ∀ i, Continuous (f i)) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (Urho A B f ρ) :=
  continuous_of_lip (div_nonneg (Vp_nonneg f) (by positivity)) (Urho_lip hf hρ)

/-- Midpoint atomisation error for the potential, uniformly in `z`. -/
theorem usig_atom_err (hf : ∀ i, Continuous (f i)) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    |Usig ρ (cK A B N) (wK f N) z - Urho A B f ρ z| ≤ etaN A B f ρ N := by
  rw [usig_K]
  have := midpoint_err A B f (κ := krho ρ z) (Λ := 1 / (2 * ρ)) (by positivity)
    (fun w w' => krho_lip hρ z w w') hf hN
  exact this

theorem measurable_U0 (hf : ∀ i, Continuous (f i)) : Measurable (U0 A B f) := by
  unfold U0
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hm : Measurable (fun p : ℂ × ℝ => f i p.2 * (-Real.log ‖p.1 - pt A B i p.2‖)) := by
    refine ((hf i).measurable.comp measurable_snd).mul ?_
    exact (Real.measurable_log.comp ((measurable_fst.sub
      ((continuous_pt A B i).measurable.comp measurable_snd)).norm)).neg
  have hs := hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  have e : (fun z : ℂ => ∫ t in (0 : ℝ)..1, f i t * (-Real.log ‖z - pt A B i t‖))
      = fun z : ℂ => ∫ t, (fun p : ℂ × ℝ => f i p.2 * (-Real.log ‖p.1 - pt A B i p.2‖)) (z, t)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    funext z; rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  exact hs.measurable

/-- `U0 ∘ pt_i` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_U0_comp (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i))
    {M : Fin n → ℝ} (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) {ρ : ℝ} (hρ : 0 < ρ) (i : Fin n) :
    IntervalIntegrable (fun t => U0 A B f (pt A B i t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hc : Continuous (fun t => |Urho A B f ρ (pt A B i t)| + Real.pi * ρ * Bs A B M) :=
    ((continuous_Urho hf hρ).comp (continuous_pt A B i)).abs.add continuous_const
  refine Integrable.mono' (hc.integrableOn_Ioc) ?_ ?_
  · exact ((measurable_U0 hf).comp (continuous_pt A B i).measurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have h1 := smooth_err hAB hf hM hρ (pt A B i t)
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (U0 A B f (pt A B i t)) (Urho A B f ρ (pt A B i t))
    linarith

/-- Smoothing of the energy: `|I - I_ρ| ≤ V π ρ B`. -/
theorem energy_smooth_err (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) {ρ : ℝ} (hρ : 0 < ρ) :
    |I0 A B f - Irho0 A B f ρ| ≤ Vp f * (Real.pi * ρ * Bs A B M) := by
  unfold I0 Irho0 Vp
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have h1 : IntervalIntegrable (fun t => f i t * U0 A B f (pt A B i t)) volume 0 1 :=
    (intervalIntegrable_U0_comp hAB hf hM hρ i).continuousOn_mul (hf i).continuousOn
  have h2 : IntervalIntegrable (fun t => f i t * Urho A B f ρ (pt A B i t)) volume 0 1 :=
    ((hf i).mul ((continuous_Urho hf hρ).comp (continuous_pt A B i))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub h1 h2]
  have hint : IntervalIntegrable (fun t => |f i t| * (Real.pi * ρ * Bs A B M)) volume 0 1 :=
    ((hf i).abs.mul continuous_const).intervalIntegrable _ _
  have := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t => f i t * U0 A B f (pt A B i t) - f i t * Urho A B f ρ (pt A B i t))
    (g := fun t => |f i t| * (Real.pi * ρ * Bs A B M))
    (Filter.Eventually.of_forall (fun t _ => by
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (smooth_err hAB hf hM hρ _) (abs_nonneg _))) hint
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const]

/-- Midpoint atomisation error for the energy. -/
theorem energy_atom_err (hf : ∀ i, Continuous (f i)) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) :
    |Irho ρ (cK A B N) (wK f N) - Irho0 A B f ρ| ≤ 2 * Vp f * etaN A B f ρ N := by
  rw [Irho_eq_sum]
  set S : ℝ := ∑ k, wK f N k * Urho A B f ρ (cK A B N k) with hS
  have h1 : |∑ k, wK f N k * Usig ρ (cK A B N) (wK f N) (cK A B N k) - S|
      ≤ Vp f * etaN A B f ρ N := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ k, |wK f N k| * etaN A B f ρ N := Finset.sum_le_sum (fun k _ => by
            rw [← mul_sub, abs_mul]
            exact mul_le_mul_of_nonneg_left (usig_atom_err hf hρ hN _) (abs_nonneg _))
      _ = (∑ k, |wK f N k|) * etaN A B f ρ N := by rw [Finset.sum_mul]
      _ ≤ Vp f * etaN A B f ρ N :=
          mul_le_mul_of_nonneg_right (abs_sum_wK_le f hf hN) (etaN_nonneg A B f hρ N)
  have h2 : |S - Irho0 A B f ρ| ≤ Vp f * etaN A B f ρ N := by
    have := midpoint_err A B f (κ := Urho A B f ρ) (Λ := Vp f / (2 * ρ))
      (div_nonneg (Vp_nonneg f) (by positivity)) (Urho_lip hf hρ) hf hN
    have e : S = ∑ i, ∑ j : Fin N, wAt f N i j * Urho A B f ρ (cAt A B N i j) := by
      rw [hS]; unfold wK cK
      exact sum_K (fun x : Fin n × Fin N => wAt f N x.1 x.2 * Urho A B f ρ (cAt A B N x.1 x.2))
    rw [e]
    refine this.trans (le_of_eq ?_)
    unfold etaN
    ring
  have := abs_sub_le (∑ k, wK f N k * Usig ρ (cK A B N) (wK f N) (cK A B N k)) S (Irho0 A B f ρ)
  linarith

end CatalanCore.Uniform.Decay.Spline
