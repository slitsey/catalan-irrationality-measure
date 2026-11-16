module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The hard-edge circle estimate (ZD05) and the logarithmic potentials of an arcsine-majorised measure

Let `ν` be a finite measure on `ℝ`, supported in `[0, b]`, with the arcsine majorant

  `ν [m - r, m + r] ≤ F √(2r/b)`  for all `m, r`

(this is `ν ≤ F · ω_{[0,b]}` together with ZD04, `ω [m - r, m + r] ≤ √(2r/b)`).  Then for every
real `t` and `ε > 0`

  `∫ log⁺(ε/|t - u|) dν(u) ≤ 2 √2 F √(ε/b)`        (`integral_posLog_le`, ZD05),

obtained from the layer-cake formula `∫ g dν = ∫₀^∞ ν{g > s} ds` and `ν{log⁺(ε/|t-u|) > s} ≤
ν[t - εe^{-s}, t + εe^{-s}]`.  Consequences: `ν` has no atoms, `log|t - u|` is `ν`-integrable for
every `t`, and `∫ |log|t - u|| dν(u)` is bounded uniformly for bounded `t`.
-/

open MeasureTheory Set Real

namespace CatalanCore.Zeta5.Energy

/-- The hypotheses on a measure `ν` on `ℝ` used by the circle regularisation: support in
`[0, b]` and the arcsine majorant (`ν ≤ F · ω_{[0,b]}`, unfolded by ZD04). -/
structure ArcMaj (ν : Measure ℝ) (b F : ℝ) : Prop where
  b_pos : 0 < b
  F_nonneg : 0 ≤ F
  supp : ν (Icc 0 b)ᶜ = 0
  maj : ∀ m r : ℝ, ν (Icc (m - r) (m + r)) ≤ ENNReal.ofReal (F * Real.sqrt (2 * r / b))

variable {ν : Measure ℝ} {b F : ℝ}

namespace ArcMaj

lemma ae_mem (h : ArcMaj ν b F) : ∀ᵐ u ∂ν, u ∈ Icc (0 : ℝ) b :=
  by simpa using measure_eq_zero_iff_ae_notMem.mp h.supp

/-- `ν` has no atoms. -/
lemma singleton_zero (h : ArcMaj ν b F) (x : ℝ) : ν {x} = 0 := by
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have hF1 : 0 < F + 1 := by linarith [h.F_nonneg]
  set r : ℝ := b * ((ε : ℝ) / (F + 1)) ^ 2 / 2 with hr
  have hr0 : 0 ≤ r := by
    have := h.b_pos
    have : 0 ≤ ((ε : ℝ) / (F + 1)) := by positivity
    positivity
  have h1 : ν {x} ≤ ν (Icc (x - r) (x + r)) := by
    apply measure_mono
    intro y hy
    rw [mem_singleton_iff] at hy
    subst hy
    exact ⟨by linarith, by linarith⟩
  refine h1.trans ((h.maj x r).trans ?_)
  have hsq : Real.sqrt (2 * r / b) = (ε : ℝ) / (F + 1) := by
    have : 2 * r / b = ((ε : ℝ) / (F + 1)) ^ 2 := by
      rw [hr]; field_simp [h.b_pos.ne']
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsq]
  have : F * ((ε : ℝ) / (F + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hF1]
    have hε0 : (0 : ℝ) ≤ ε := ε.coe_nonneg
    nlinarith [hε0, h.F_nonneg]
  calc ENNReal.ofReal (F * ((ε : ℝ) / (F + 1))) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal this
    _ = ε := ENNReal.ofReal_coe_nnreal

end ArcMaj

/-- The regularisation integrand `log⁺(ε/|t - u|)`. -/
noncomputable def regTerm (t ε u : ℝ) : ℝ := Real.posLog (ε / |t - u|)

lemma measurable_regTerm (t ε : ℝ) : Measurable (regTerm t ε) := by
  have : Measurable fun u : ℝ => ε / |t - u| := by fun_prop
  show Measurable fun u => max 0 (Real.log (ε / |t - u|))
  exact measurable_const.max (Real.measurable_log.comp this)

lemma regTerm_nonneg (t ε u : ℝ) : 0 ≤ regTerm t ε u := Real.posLog_nonneg

/-- The level sets of `regTerm` lie in short intervals. -/
lemma regTerm_level {t ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 0 < s) {u : ℝ}
    (hu : s < regTerm t ε u) : u ∈ Icc (t - ε * Real.exp (-s)) (t + ε * Real.exp (-s)) := by
  unfold regTerm at hu
  rw [Real.posLog_apply] at hu
  have hlog : s < Real.log (ε / |t - u|) := by
    rcases lt_max_iff.mp hu with h | h
    · exact absurd h (not_lt.mpr hs.le)
    · exact h
  have hx : 0 < ε / |t - u| := by
    by_contra hx
    have hx0 : ε / |t - u| = 0 := le_antisymm (not_lt.mp hx) (by positivity)
    rw [hx0, Real.log_zero] at hlog
    linarith
  have hd : 0 < |t - u| := by
    by_contra hd
    have : |t - u| = 0 := le_antisymm (not_lt.mp hd) (abs_nonneg _)
    rw [this, div_zero] at hx
    exact lt_irrefl _ hx
  have h2 : Real.exp s < ε / |t - u| := (Real.lt_log_iff_exp_lt hx).mp hlog
  rw [lt_div_iff₀ hd] at h2
  have h3 : |t - u| < ε * Real.exp (-s) := by
    have hes : 0 < Real.exp s := Real.exp_pos s
    rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ hes]
    linarith
  rw [abs_lt] at h3
  constructor <;> linarith [h3.1, h3.2]

/-- **ZD05** in `lintegral` form. -/
lemma lintegral_regTerm_le (hν : ArcMaj ν b F) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫⁻ u, ENNReal.ofReal (regTerm t ε u) ∂ν ≤
      ENNReal.ofReal (2 * (F * Real.sqrt (2 * ε / b))) := by
  rw [lintegral_eq_lintegral_meas_lt ν (ae_of_all _ fun u => regTerm_nonneg t ε u)
    (measurable_regTerm t ε).aemeasurable]
  set C : ℝ := F * Real.sqrt (2 * ε / b) with hC
  have hC0 : 0 ≤ C := mul_nonneg hν.F_nonneg (Real.sqrt_nonneg _)
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ν {a | s < regTerm t ε a} ≤
      ENNReal.ofReal (C * Real.exp (-(1 / 2) * s)) := by
    intro s hs
    have hs : 0 < s := hs
    refine (measure_mono fun u hu => regTerm_level hε hs hu).trans ?_
    have hm := hν.maj t (ε * Real.exp (-s))
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.sqrt (2 * (ε * Real.exp (-s)) / b) =
        Real.sqrt (2 * ε / b) * Real.exp (-(1 / 2) * s) := by
      have e : 2 * (ε * Real.exp (-s)) / b = (2 * ε / b) * (Real.exp (-(1 / 2) * s)) ^ 2 := by
        rw [← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (-(1 / 2) * s) = -s := by push_cast; ring
        rw [this]; ring
      rw [e, Real.sqrt_mul (by have := hν.b_pos; positivity), Real.sqrt_sq (Real.exp_pos _).le]
    rw [this, hC]; ring_nf; exact le_rfl
  have hint : IntegrableOn (fun s : ℝ => C * Real.exp (-(1 / 2) * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul C
  calc ∫⁻ s in Ioi 0, ν {a | s < regTerm t ε a}
      ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal (C * Real.exp (-(1 / 2) * s)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (∫ s in Ioi 0, C * Real.exp (-(1 / 2) * s)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun s => by positivity)).symm
    _ = ENNReal.ofReal (2 * C) := by
        congr 1
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
        norm_num; ring

lemma integrable_regTerm (hν : ArcMaj ν b F) [IsFiniteMeasure ν] {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (regTerm t ε) ν := by
  refine ⟨(measurable_regTerm t ε).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => regTerm_nonneg t ε u)]
  exact (lintegral_regTerm_le hν hε t).trans_lt ENNReal.ofReal_lt_top

/-- **ZD05**: the hard-edge circle estimate,
`∫ log⁺(ε/|t - u|) dν(u) ≤ 2 √2 F √(ε/b)`, for every real `t`. -/
theorem integral_regTerm_le (hν : ArcMaj ν b F) [IsFiniteMeasure ν] {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ u, regTerm t ε u ∂ν ≤ 2 * Real.sqrt 2 * F / Real.sqrt b * Real.sqrt ε := by
  have h := lintegral_regTerm_le hν hε t
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_regTerm hν hε t)
    (ae_of_all _ fun u => regTerm_nonneg t ε u)] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by
    have := hν.F_nonneg; have := Real.sqrt_nonneg (2 * ε / b); positivity)).mp h
  refine h2.trans (le_of_eq ?_)
  have hb := hν.b_pos
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
  field_simp

/-- The part `log⁺|t - u|` of the logarithm: bounded on the support. -/
noncomputable def posTerm (t u : ℝ) : ℝ := Real.posLog |t - u|

lemma measurable_posTerm (t : ℝ) : Measurable (posTerm t) := by
  have : Measurable fun u : ℝ => |t - u| := by fun_prop
  show Measurable fun u => max 0 (Real.log |t - u|)
  exact measurable_const.max (Real.measurable_log.comp this)

lemma posTerm_le (hν : ArcMaj ν b F) (t : ℝ) :
    ∀ᵐ u ∂ν, posTerm t u ≤ Real.log (1 + |t| + b) := by
  filter_upwards [hν.ae_mem] with u hu
  have h1 : |t - u| ≤ |t| + b := by
    calc |t - u| ≤ |t| + |u| := abs_sub _ _
      _ ≤ |t| + b := by rw [abs_of_nonneg hu.1]; linarith [hu.2]
  have h2 : Real.posLog |t - u| ≤ Real.posLog (|t| + b) :=
    Real.posLog_le_posLog (by linarith [abs_nonneg (t - u)]) h1
  have h3 : Real.posLog (|t| + b) ≤ Real.log (1 + (|t| + b)) :=
    Real.posLog_le_log_one_add (by linarith [abs_nonneg t, hν.b_pos])
  unfold posTerm
  calc _ ≤ _ := h2.trans h3
    _ = _ := by ring_nf

lemma integrable_posTerm (hν : ArcMaj ν b F) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (posTerm t) ν := by
  refine Integrable.mono' (integrable_const (Real.log (1 + |t| + b)))
    (measurable_posTerm t).aestronglyMeasurable ?_
  filter_upwards [posTerm_le hν t] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ posTerm t u from Real.posLog_nonneg)]
  exact hu

lemma log_abs_eq (t u : ℝ) : Real.log |t - u| = posTerm t u - regTerm t 1 u := by
  unfold posTerm regTerm
  rw [div_eq_mul_inv, one_mul, Real.posLog_sub_posLog_inv]

lemma abs_log_abs_eq (t u : ℝ) : abs (Real.log |t - u|) = posTerm t u + regTerm t 1 u := by
  unfold posTerm regTerm
  rw [div_eq_mul_inv, one_mul, Real.abs_log_eq_posLog_add_posLog_inv]

/-- `log|t - u|` is `ν`-integrable for every real `t`. -/
lemma integrable_log_abs_sub (hν : ArcMaj ν b F) [IsFiniteMeasure ν] (t : ℝ) :
    Integrable (fun u => Real.log |t - u|) ν := by
  have := (integrable_posTerm hν t).sub (integrable_regTerm hν one_pos t)
  refine this.congr (ae_of_all _ fun u => ?_)
  exact (log_abs_eq t u).symm

/-- A uniform bound for the absolute logarithmic potential. -/
lemma integral_abs_log_le (hν : ArcMaj ν b F) [IsFiniteMeasure ν] (t : ℝ) :
    ∫ u, abs (Real.log |t - u|) ∂ν ≤
      ν.real univ * Real.log (1 + |t| + b) + 2 * Real.sqrt 2 * F / Real.sqrt b * Real.sqrt 1 := by
  have e : ∀ u, abs (Real.log |t - u|) = posTerm t u + regTerm t 1 u := abs_log_abs_eq t
  simp_rw [e]
  rw [integral_add (integrable_posTerm hν t) (integrable_regTerm hν one_pos t)]
  refine add_le_add ?_ (integral_regTerm_le hν one_pos t)
  have := integral_mono_ae (μ := ν) (f := posTerm t) (g := fun _ => Real.log (1 + |t| + b))
    (integrable_posTerm hν t) (integrable_const _) (posTerm_le hν t)
  rw [integral_const, smul_eq_mul] at this
  exact this

end CatalanCore.Zeta5.Energy
