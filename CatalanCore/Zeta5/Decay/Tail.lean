module

public import CatalanCore.Zeta5.Energy.Field
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Z5-DECAY, part 1: the analytic tail `t ≥ 4` (ZD10, ZD11)

For a finite measure `ν` on `ℝ` of mass `λ = 37/40` supported in `[0, b]`, `b < 4`, and any
`M₀ ≥ -8` (the design value is `M₀ ≈ -6.66`) the second conjunct of `CellHyp`
holds outright: `2 U(t) - V(t) + √t/2 ≤ M₀` for all `t ≥ 4`.

* ZD10: `J₁(t) ≥ log t` (`JA_ge`), `J_α(t) ≤ α log t + α³/(3t)` (`JA_le`, from `log(1+x) ≤ x`),
  `U(t) ≤ λ log t` (`potU_le_log`).
* ZD11: with `s = √t ≥ 2` the tail function
  `1.3 log t + 2α³/t - (2π - 1/2) s` is at most `-8.96` (closed form: `log s ≤ s - 1`,
  `π > 3.14`), no derivative and no enclosure of `log 4` needed.  The coefficient is the
  `K = 2` form `2π - 1/K` of `CellHyp` (`√t/2`).
-/

open MeasureTheory Set Real

namespace CatalanCore.Zeta5.Decay

open CatalanCore.Zeta5.Energy

lemma log_add_sq_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Real.log (t + u ^ 2) ≤ Real.log t + u ^ 2 / t := by
  have h1 : 0 < t + u ^ 2 := by positivity
  have h2 : Real.log ((t + u ^ 2) / t) ≤ (t + u ^ 2) / t - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div h1.ne' ht.ne'] at h2
  have h3 : (t + u ^ 2) / t - 1 = u ^ 2 / t := by field_simp; ring
  linarith

lemma intInt_log {t : ℝ} (ht : 0 < t) (A : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log (t + u ^ 2)) MeasureTheory.volume 0 A :=
  (Continuous.log (by fun_prop) (fun u => by positivity)).intervalIntegrable _ _

/-- **ZD10 (lower)**: `A log t ≤ J_A(t)` for `A ≥ 0`, `t > 0` (`J₁(t) ≥ log t` at `A = 1`). -/
theorem JA_ge {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) : A * Real.log t ≤ JA A t := by
  unfold JA
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := A)
    (f := fun _ : ℝ => Real.log t) (g := fun u : ℝ => Real.log (t + u ^ 2)) hA
    (by simp) (intInt_log ht A) (fun u hu => by
      apply Real.log_le_log ht
      have := sq_nonneg u
      linarith)
  simpa using h

/-- **ZD10 (upper)**: `J_A(t) ≤ A log t + A³/(3t)` for `A ≥ 0`, `t > 0`. -/
theorem JA_le {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    JA A t ≤ A * Real.log t + A ^ 3 / (3 * t) := by
  unfold JA
  have hint : IntervalIntegrable (fun u : ℝ => Real.log t + u ^ 2 / t) MeasureTheory.volume 0 A :=
    (by fun_prop : Continuous fun u : ℝ => Real.log t + u ^ 2 / t).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := A)
    (f := fun u : ℝ => Real.log (t + u ^ 2)) (g := fun u : ℝ => Real.log t + u ^ 2 / t) hA
    (intInt_log ht A) hint (fun u _ => log_add_sq_le ht u)
  have e : ∫ u in (0 : ℝ)..A, (Real.log t + u ^ 2 / t) = A * Real.log t + A ^ 3 / (3 * t) := by
    rw [intervalIntegral.integral_add (by simp) (by
      exact (by fun_prop : Continuous fun u : ℝ => u ^ 2 / t).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_div, integral_pow]
    simp
    field_simp
    ring
  linarith

/-- `U(t) ≤ ν(ℝ) · log t` for `t ≥ 4`, `ν` finite, supported in `[0, b]` with `b < 4`. -/
theorem potU_le_log {ν : Measure ℝ} [IsFiniteMeasure ν] {b : ℝ} (hsupp : ν (Icc 0 b)ᶜ = 0)
    (hb : b < 4) {t : ℝ} (ht : 4 ≤ t) : potU ν t ≤ ν.real univ * Real.log t := by
  have hae : ∀ᵐ u ∂ν, u ∈ Icc 0 b := by rw [ae_iff]; exact hsupp
  have ht0 : 0 < t := by linarith
  have htb : 0 < t - b := by linarith
  have hmeas : Measurable fun u : ℝ => Real.log |t - u| :=
    Real.measurable_log.comp (by fun_prop)
  have hint : Integrable (fun u : ℝ => Real.log |t - u|) ν := by
    refine Integrable.of_bound (C := |Real.log (t - b)| + |Real.log t|)
      hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with u hu
    have h1 : |t - u| = t - u := abs_of_pos (by linarith [hu.2])
    rw [Real.norm_eq_abs, h1]
    have hl1 : Real.log (t - b) ≤ Real.log (t - u) :=
      Real.log_le_log htb (by linarith [hu.2])
    have hl2 : Real.log (t - u) ≤ Real.log t :=
      Real.log_le_log (by linarith [hu.2]) (by linarith [hu.1])
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log (t - b)), le_abs_self (Real.log t),
      abs_nonneg (Real.log (t - b)), abs_nonneg (Real.log t)]
  have hmono : ∫ u, Real.log |t - u| ∂ν ≤ ∫ _u, Real.log t ∂ν := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hae] with u hu
    have h1 : |t - u| = t - u := abs_of_pos (by linarith [hu.2])
    show Real.log |t - u| ≤ Real.log t
    rw [h1]
    exact Real.log_le_log (by linarith [hu.2]) (by linarith [hu.1])
  unfold potU
  simpa using hmono

/-- **ZD10/ZD11, the tail inequality**: for all `t ≥ 4`,
`2 U(t) - V(t) + √t/2 ≤ M₀` once `M₀ ≥ -8`. -/
theorem tail_bound {ν : Measure ℝ} [IsFiniteMeasure ν] {b M₀ : ℝ} (hsupp : ν (Icc 0 b)ᶜ = 0)
    (hb : b < 4) (hmass : ν.real univ = 37 / 40) (hM : -8 ≤ M₀) {t : ℝ} (ht : 4 ≤ t) :
    2 * potU ν t - Vfield t + Real.sqrt t / 2 ≤ M₀ := by
  have ht0 : 0 < t := by linarith
  set s := Real.sqrt t with hs
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hs_ge : 2 ≤ s := by
    nlinarith
  have hU := potU_le_log hsupp hb ht
  rw [hmass] at hU
  have hJ1 := JA_ge (A := 1) (by norm_num) ht0
  have hJa := JA_le (A := 3 / 40) (by norm_num) ht0
  have hV : Vfield t = 2 * Real.pi * s + JA 1 t - 6 * JA (3 / 40) t := Vfield_eq_J t
  have hlog : Real.log t = 2 * Real.log s := by
    have : Real.log s = Real.log t / 2 := Real.log_sqrt ht0.le
    linarith
  have hls : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hinv : (3 / 40 : ℝ) ^ 3 / (3 * t) ≤ (3 / 40) ^ 3 / (3 * 4) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hnum : (3 / 40 : ℝ) ^ 3 / (3 * 4) ≤ 1 / 1000 := by norm_num
  have h1 : 2 * potU ν t ≤ 37 / 20 * Real.log t := by linarith
  have hsum : 2 * Real.pi * s ≥ 6.28 * s := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hls (by norm_num : (0 : ℝ) ≤ 2.6)]

/-- The tail conjunct of `CellHyp`. -/
theorem cellHyp_tail {ν : Measure ℝ} [IsFiniteMeasure ν] {b M₀ : ℝ} (hsupp : ν (Icc 0 b)ᶜ = 0)
    (hb : b < 4) (hmass : ν.real univ = 37 / 40) (hM : -8 ≤ M₀) :
    ∀ t : ℝ, 4 ≤ t → 2 * potU ν t - Vfield t + Real.sqrt t / 2 ≤ M₀ :=
  fun _ ht => tail_bound hsupp hb hmass hM ht

/-- **`CellHyp` from the bounded-region inequality alone.** -/
theorem cellHyp_of_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {b M₀ : ℝ}
    (hsupp : ν (Icc 0 b)ᶜ = 0) (hb : b < 4) (hmass : ν.real univ = 37 / 40) (hM : -8 ≤ M₀)
    (hcell : ∀ t ∈ Icc (0 : ℝ) 4, 2 * potU ν t - Vfield t ≤ M₀) : CellHyp ν M₀ :=
  ⟨hcell, cellHyp_tail hsupp hb hmass hM⟩

end CatalanCore.Zeta5.Decay
