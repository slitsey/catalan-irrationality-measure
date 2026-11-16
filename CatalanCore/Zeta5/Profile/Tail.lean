module

public import CatalanCore.Zeta5.Profile.Antideriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Lemma TL40 (CONTENT-LEDGER §B2)

`∫₄₀^∞ R(x) x⁻³ dx ≤ −147507089/9830400000`, with `R = x F + Q`, `−1/2 ≤ Q ≤ 13/8` (`Defs`) and
the antiderivatives `P, C, D` of `Antideriv`.

The proof follows the ledger: with
`Ψ(x) = λ/x + (P − P̄)/x² + 2C/x³ + 6D/x⁴` one has `Ψ′ = F/x² − 24 D/x⁵` off `ℤ ∪ α⁻¹ℤ`
(`hasDerivAt_Psi`); `D ≤ D₊` and `Q ≤ 13/8` give `R/x³ ≤ Ω′` for `Ω = Ψ − 6D₊/x⁴ − (13/16)/x²`, and
`Ω(X) → 0`. Everything is one fundamental theorem of calculus for a continuous piecewise `C¹`
function (no jump terms) and a limit.
-/

open Set MeasureTheory Filter Topology

namespace CatalanCore.Zeta5.Profile

/-- `D₊ = 74/(360 α²) + 7λ/2880`. -/
noncomputable def Dplus : ℝ := 74 / (360 * (al : ℝ) ^ 2) + 7 * (lam : ℝ) / 2880

/-- `Ω = Ψ − 6D₊/x⁴ − (13/16)/x²`. -/
noncomputable def Om (x : ℝ) : ℝ :=
  (lam : ℝ) / x + (Pp x - Pbar) / x ^ 2 + 2 * Cc x / x ^ 3 + 6 * Dd x / x ^ 4
    - 6 * Dplus / x ^ 4 - 13 / 16 / x ^ 2

/-- The derivative of `Ω`. -/
noncomputable def Omd (x : ℝ) : ℝ :=
  Fs x / x ^ 2 - 24 * Dd x / x ^ 5 + 24 * Dplus / x ^ 5 + 13 / 8 / x ^ 3

theorem hasDerivAt_Om {x : ℝ} (hx : x ∉ exc) (h0 : x ≠ 0) : HasDerivAt Om (Omd x) x := by
  have hP := (hasDerivAt_Pp hx)
  have hC := (hasDerivAt_Cc hx)
  have hD := (hasDerivAt_Dd hx)
  have p2 := hasDerivAt_pow 2 x
  have p3 := hasDerivAt_pow 3 x
  have p4 := hasDerivAt_pow 4 x
  have n1 := hasDerivAt_id x
  have t1 := (hasDerivAt_const x (lam : ℝ)).div n1 h0
  have t2 := (hP.sub_const Pbar).div p2 (pow_ne_zero 2 h0)
  have t3 := (hC.const_mul 2).div p3 (pow_ne_zero 3 h0)
  have t4 := (hD.const_mul 6).div p4 (pow_ne_zero 4 h0)
  have t5 := (hasDerivAt_const x (6 * Dplus)).div p4 (pow_ne_zero 4 h0)
  have t6 := (hasDerivAt_const x (13 / 16 : ℝ)).div p2 (pow_ne_zero 2 h0)
  have := ((((t1.add t2).add t3).add t4).sub t5).sub t6
  unfold Om
  refine this.congr_deriv ?_
  unfold Omd
  simp only [id]
  field_simp
  ring

lemma continuousOn_Om : ContinuousOn Om (Ioi 0) := by
  have h : ∀ x ∈ Ioi (0 : ℝ), ContinuousAt Om x := by
    intro x hx
    have h0 : x ≠ 0 := ne_of_gt hx
    unfold Om
    have := continuous_Pp; have := continuous_Cc; have := continuous_Dd
    fun_prop (disch := first | exact h0 | exact pow_ne_zero _ h0)
  exact fun x hx => (h x hx).continuousWithinAt

lemma integrableOn_Ioi_of_bound {f : ℝ → ℝ} {a C : ℝ} (ha : 0 < a) (hf : Measurable f)
    (hb : ∀ x, a < x → |f x| ≤ C / x ^ 2) : IntegrableOn f (Ioi a) := by
  have h := (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha).const_mul C
  refine Integrable.mono' h hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans ha hx
  rw [Real.norm_eq_abs]
  calc |f x| ≤ C / x ^ 2 := hb x hx
    _ = C * x ^ (-2 : ℝ) := by rw [Real.rpow_neg hx0.le, Real.rpow_two]; ring

lemma measurable_Omd : Measurable Omd := by
  have := continuous_Dd.measurable
  unfold Omd
  have := measurable_Fs
  fun_prop

lemma Omd_bound (x : ℝ) (hx : 40 < x) : |Omd x| ≤ 2000 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hD := Dd_abs x; have hF := Fs_abs x
  have hDp : Dplus = 74 / (360 * (al : ℝ) ^ 2) + 7 * (lam : ℝ) / 2880 := rfl
  have hDp' : 0 ≤ Dplus := by
    rw [hDp]; have := al_pos; unfold lam; positivity
  have hDp2 : Dplus ≤ 700 := by
    rw [hDp]; unfold al lam; norm_num
  unfold Omd
  rw [abs_le] at hD hF
  have x2 : 0 < x ^ 2 := by positivity
  have h5 : (24 : ℝ) / x ^ 5 ≤ 24 / (40 * x ^ 4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [pow_pos hx0 4]
  -- crude: each term is at most a constant over x^2 because x > 40
  have e1 : Fs x / x ^ 2 - 24 * Dd x / x ^ 5 + 24 * Dplus / x ^ 5 + 13 / 8 / x ^ 3
      = (Fs x - (24 * Dd x - 24 * Dplus) / x ^ 3 + 13 / 8 / x) / x ^ 2 := by
    field_simp
    ring
  rw [e1, abs_div, abs_of_pos x2, div_le_div_iff_of_pos_right x2]
  have hx3 : 40 ^ 3 < x ^ 3 := by gcongr
  have h3 : |(24 * Dd x - 24 * Dplus) / x ^ 3| ≤ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hx0 3), div_le_iff₀ (pow_pos hx0 3)]
    norm_num at hx3
    rw [abs_le]; constructor <;> linarith [hD.1, hD.2]
  have h4 : |13 / 8 / x| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hx0]; linarith
  rw [abs_le] at h3 h4 ⊢
  constructor <;> linarith [hF.1, hF.2, h3.1, h3.2, h4.1, h4.2]

/-- Pointwise bound: `R/x³ ≤ Ω′` for `x > 0`. -/
lemma Rg_div_le (x : ℝ) (hx : 0 < x) : Rg x / x ^ 3 ≤ Omd x := by
  have hD := Dd_le x
  have hQ := Qc_le x
  have e : Rg x / x ^ 3 = Fs x / x ^ 2 - 24 * Dd x / x ^ 5 + 24 * Dd x / x ^ 5 + Qc x / x ^ 3 := by
    unfold Rg; field_simp; ring
  rw [e]; unfold Omd
  have h1 : 24 * Dd x / x ^ 5 ≤ 24 * Dplus / x ^ 5 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    unfold Dplus; linarith
  have h2 : Qc x / x ^ 3 ≤ 13 / 8 / x ^ 3 :=
    div_le_div_of_nonneg_right hQ (by positivity)
  linarith

lemma Rg_bound (x : ℝ) (hx : 1 ≤ x) : |Rg x / x ^ 3| ≤ 22 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hF := Fs_abs x
  have hQ1 := Qc_le x; have hQ2 := Qc_ge x
  have hR : |Rg x| ≤ 22 * x := by
    unfold Rg
    rw [abs_le] at hF ⊢
    constructor <;> nlinarith [hF.1, hF.2]
  rw [abs_div, abs_of_pos (pow_pos hx0 3), div_le_div_iff₀ (pow_pos hx0 3) (pow_pos hx0 2)]
  have x2 : 0 < x ^ 2 := by positivity
  calc |Rg x| * x ^ 2 ≤ 22 * x * x ^ 2 := by gcongr
    _ = 22 * x ^ 3 := by ring

lemma integrableOn_Rg : IntegrableOn (fun x : ℝ => (Rg x : ℝ) / x ^ 3) (Ioi 40) := by
  refine integrableOn_Ioi_of_bound (C := 22) (by norm_num) ?_ ?_
  · exact measurable_Rg.div (by fun_prop)
  · intro x hx
    exact Rg_bound x (by linarith)


lemma term_le {a M x : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : |a| ≤ M) (hx : 1 ≤ x) :
    |a / x ^ k| ≤ M / x := by
  have hx0 : 0 < x := by linarith
  have hM : 0 ≤ M := le_trans (abs_nonneg a) ha
  rw [abs_div, abs_of_pos (pow_pos hx0 k)]
  calc |a| / x ^ k ≤ M / x ^ k := div_le_div_of_nonneg_right ha (by positivity)
    _ ≤ M / x := by
      apply div_le_div_of_nonneg_left hM hx0
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ k := pow_le_pow_right₀ hx hk

lemma Om_bound (x : ℝ) (hx : 1 ≤ x) : |Om x| ≤ 30000 / x := by
  have hx0 : 0 < x := by linarith
  have hP := Pp_abs x; have hC := Cc_abs x; have hD := Dd_abs x
  have hDp : Dplus ≤ 700 := by unfold Dplus al lam; norm_num
  have hDp0 : 0 ≤ Dplus := by unfold Dplus al lam; norm_num
  have hl : (lam : ℝ) = 37 / 40 := rfl
  have hPb : Pbar = 2923 / 240 := rfl
  have t1 := term_le (k := 1) (x := x) (a := (lam : ℝ)) (M := 1) le_rfl (by rw [hl]; norm_num) hx
  rw [pow_one] at t1
  have t2 := term_le (k := 2) (x := x) (a := Pp x - Pbar) (M := 40) (by norm_num)
    (by rw [hPb]; rw [abs_le] at hP ⊢; constructor <;> linarith [hP.1, hP.2]) hx
  have t3 := term_le (k := 3) (x := x) (a := 2 * Cc x) (M := 4000) (by norm_num)
    (by rw [abs_mul]; norm_num; linarith) hx
  have t4 := term_le (k := 4) (x := x) (a := 6 * Dd x) (M := 12000) (by norm_num)
    (by rw [abs_mul]; norm_num; linarith) hx
  have t5 := term_le (k := 4) (x := x) (a := 6 * Dplus) (M := 4200) (by norm_num)
    (by rw [abs_of_nonneg (by linarith)]; linarith) hx
  have t6 := term_le (k := 2) (x := x) (a := (13 / 16 : ℝ)) (M := 1) (by norm_num)
    (by norm_num) hx
  have e : 30000 / x = 1 / x + 40 / x + 4000 / x + 12000 / x + 4200 / x + 1 / x
      + (30000 - 1 - 40 - 4000 - 12000 - 4200 - 1) / x := by ring
  have hrest : 0 ≤ (30000 - 1 - 40 - 4000 - 12000 - 4200 - 1) / x := by
    apply div_nonneg <;> linarith
  unfold Om
  rw [abs_le] at t1 t2 t3 t4 t5 t6 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1, t6.2]

lemma tendsto_Om : Tendsto Om atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ => 30000 / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs]; exact Om_bound x hx

lemma Om_forty : Om 40 = (lam : ℝ) / 40 - Pbar / 40 ^ 2 + 6 * (74 / (360 * (al : ℝ) ^ 2) - (lam : ℝ) / 360) / 40 ^ 4
    - 6 * Dplus / 40 ^ 4 - 13 / 16 / 40 ^ 2 := by
  have h1 : Int.fract (40 : ℝ) = 0 := by
    have : (40 : ℝ) = ((40 : ℤ) : ℝ) := by norm_num
    rw [this, Int.fract_intCast]
  have h2 : Int.fract ((al : ℝ) * 40) = 0 := by
    have : (al : ℝ) * 40 = ((3 : ℤ) : ℝ) := by unfold al; norm_num
    rw [this, Int.fract_intCast]
  have hP : Pp 40 = 0 := by unfold Pp; rw [h1, h2]; ring
  have hC : Cc 40 = 0 := by unfold Cc G0; rw [h1, h2]; ring
  have hD : Dd 40 = 74 / (360 * (al : ℝ) ^ 2) - (lam : ℝ) / 360 := by
    unfold Dd B4; rw [h1, h2]
    have : (al : ℝ) ≠ 0 := al_pos.ne'
    field_simp; ring
  unfold Om; rw [hP, hC, hD]; ring

/-- **Lemma TL40.** `∫₄₀^∞ R(x) x⁻³ dx ≤ −147507089/9830400000`. -/
theorem TL40 : ∫ x in Ioi (40 : ℝ), (Rg x : ℝ) / x ^ 3 ≤ -147507089 / 9830400000 := by
  have hOi : IntegrableOn Omd (Ioi 40) :=
    integrableOn_Ioi_of_bound (C := 2000) (by norm_num) measurable_Omd (fun x hx => Omd_bound x hx)
  have hFTC : ∀ X : ℝ, 40 ≤ X → ∫ x in (40 : ℝ)..X, Omd x = Om X - Om 40 := by
    intro X hX
    have hint : IntervalIntegrable Omd volume 40 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2 (hOi.mono_set Ioc_subset_Ioi_self)
    refine integral_eq_of_hasDerivAt_off_countable_of_le Om Omd hX exc_countable ?_ ?_ hint
    · exact continuousOn_Om.mono (fun y hy => lt_of_lt_of_le (by norm_num) hy.1)
    · intro x hx
      exact hasDerivAt_Om hx.2 (by linarith [hx.1.1])
  have hle : ∀ X : ℝ, 40 ≤ X →
      ∫ x in (40 : ℝ)..X, (Rg x : ℝ) / x ^ 3 ≤ Om X - Om 40 := by
    intro X hX
    have hint : IntervalIntegrable Omd volume 40 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2 (hOi.mono_set Ioc_subset_Ioi_self)
    have hint2 : IntervalIntegrable (fun x : ℝ => (Rg x : ℝ) / x ^ 3) volume 40 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2
        (integrableOn_Rg.mono_set Ioc_subset_Ioi_self)
    rw [← hFTC X hX]
    exact intervalIntegral.integral_mono_on hX hint2 hint
      (fun x hx => Rg_div_le x (by linarith [hx.1]))
  have hT := intervalIntegral_tendsto_integral_Ioi (a := 40) integrableOn_Rg tendsto_id
  have hT2 : Tendsto (fun X : ℝ => Om X - Om 40) atTop (nhds (0 - Om 40)) :=
    tendsto_Om.sub tendsto_const_nhds
  have := le_of_tendsto_of_tendsto hT hT2
    (eventually_atTop.2 ⟨40, fun X hX => hle X hX⟩)
  refine this.trans ?_
  rw [Om_forty]
  unfold Dplus Pbar lam al
  norm_num

end CatalanCore.Zeta5.Profile
