module

public import CatalanCore.Uniform.Decay.Cert.CheckMain

@[expose] public section

/-!
# Signed spline data and its elementary Boolean checks (lane D, package D8)

`SplineDataS` is `SplineData` plus a total-variation bound `Vt ∈ ℚ`.  The elementary check
`basicOkS` differs from `basicOk` in three places only:

* `segOkS` : the Bernstein test is two-sided, `-M_i ≤ f_i ≤ M_i` (`bernOkK coef (-M) M`);
* `dofOkS` : the decay target uses the loss `Vt · (…)` in place of `1 · (…)`;
* `varOk`  : `Vp f ≤ Vt`, certified either by `∑ M_i ≤ Vt` (each `∫₀¹ |f_i| ≤ M_i`), or, for
  nonnegative densities, by `Vt = 1` together with the one-sided Bernstein tests `0 ≤ f_i`
  (exact mass one).  The second branch is the positive case `V = 1` of `Cert.basicOk`.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset intervalIntegral CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

/-- Spline data with a total-variation bound. -/
structure SplineDataS extends SplineData where
  Vt : ℚ

namespace SplineDataS

variable (D : SplineDataS)

/-- Per-segment elementary checks, two-sided Bernstein bound. -/
def segOkS (i : Fin D.n) : Bool :=
  let s := D.seg i
  decide (s.ax ≠ s.bx ∨ s.ay ≠ s.byy) && decide (s.coef ≠ []) && bernOkK s.coef (-s.M) s.M &&
  decide (0 < s.Lq) && decide (0 ≤ s.M) && decide (s.Lq ^ 2 ≤ (s.bx - s.ax) ^ 2 + (s.byy - s.ay) ^ 2) &&
  decide (s.ax ^ 2 + s.ay ^ 2 ≤ D.Rc ^ 2) && decide (s.bx ^ 2 + s.byy ^ 2 ≤ D.Rc ^ 2) &&
  decide (s.tau < D.n)

/-- Decay exponent target with the variation `Vt`. -/
def dofOkS : Bool :=
  decide (D.Dt ≤ 2 * (D.Mq * D.mprime + D.dim * D.Scap) - D.Mq ^ 2 * D.Ibound + D.Inu
    - (2 * D.Mq ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
      + D.Mq ^ 2 * (D.Vt * D.lossS + 2 * D.Vt * D.theta)))

/-- Variation certificate. -/
def varOk : Bool :=
  decide (∑ i : Fin D.n, D.M i ≤ D.Vt) ||
    (decide (D.Vt = 1) && (List.finRange D.n).all (fun i => bernOkK (D.l i) 0 (D.M i)))

/-- All elementary checks (signed). -/
def basicOkS : Bool :=
  decide (0 < D.Mq) && decide (0 < D.ε) && decide (D.ε < 1) && decide (0 < D.r0) && decide (0 < D.W) &&
  decide (0 < D.rho) && decide (0 < D.theta) && decide (0 < D.etaS) && decide (0 ≤ D.Rc) &&
  decide (0 ≤ D.ccert) && decide (2 * (D.mprime - D.gmin) ≤ D.ccert) &&
  (List.finRange D.n).all D.segOkS && (List.finRange D.n).all D.conjOk &&
  decide (∑ i : Fin D.n, SplineData.massOf (D.l i) = 1) &&
  decide (0 ≤ D.lossS) && decide ((315 / 100 : ℚ) * D.rho * D.BsQ ≤ D.lossS) &&
  coverOk 0 D.umax D.rayBoxes && coverOk 0 1 D.lineCells && D.dofOkS && D.varOk

variable {D}

theorem all_finRangeS {p : Fin D.n → Bool} (h : (List.finRange D.n).all p = true) (i : Fin D.n) :
    p i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_finRange i)

/-- Facts from `segOkS`. -/
theorem segOkS_facts (hR : 0 ≤ D.Rc) {i : Fin D.n} (h : D.segOkS i = true) :
    D.A i ≠ D.B i ∧ D.l i ≠ [] ∧ bernOkK (D.l i) (-(D.M i)) (D.M i) = true ∧
    0 < (D.seg i).Lq ∧ 0 ≤ D.M i ∧ ((D.seg i).Lq : ℝ) ≤ ‖D.B i - D.A i‖ ∧
    ‖D.A i‖ ≤ (D.Rc : ℝ) ∧ ‖D.B i‖ ≤ (D.Rc : ℝ) ∧ (D.seg i).tau < D.n := by
  simp only [segOkS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h4m⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨?_, h2, h3, h4, h4m, ?_, norm_mk_le h6 hR, norm_mk_le h7 hR, h8⟩
  · intro heq
    have hx := congrArg Complex.re heq
    have hy := congrArg Complex.im heq
    simp only [SplineData.A, SplineData.B] at hx hy
    rcases h1 with h1 | h1
    · exact h1 (by exact_mod_cast hx)
    · exact h1 (by exact_mod_cast hy)
  · have e : D.B i - D.A i = ⟨(((D.seg i).bx - (D.seg i).ax : ℚ) : ℝ),
        (((D.seg i).byy - (D.seg i).ay : ℚ) : ℝ)⟩ := by
      apply Complex.ext <;> simp [SplineData.A, SplineData.B]
    rw [e]
    exact le_norm_mk h5 h4.le

/-- Real mass of the densities from the rational mass. -/
theorem mass_real_of_rat
    (hmass : ∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1), coeffs (D.l i) j / ((j : ℚ) + 1) = 1) :
    ∑ i, ∫ t in (0 : ℝ)..1, D.f i t = 1 := by
  simp_rw [SplineData.f, integral_ratPoly]
  rw [← Rat.cast_sum]
  rw [hmass]; norm_num

/-- Soundness of the variation certificate. -/
theorem varOk_sound (hv : D.varOk = true)
    (hne : ∀ i, D.l i ≠ []) (hbern : ∀ i, bernOkK (D.l i) (-(D.M i)) (D.M i) = true)
    (hmass : ∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1), coeffs (D.l i) j / ((j : ℚ) + 1) = 1) :
    Vp D.f ≤ (D.Vt : ℝ) := by
  simp only [varOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with h | ⟨hV1, hpos⟩
  · -- `∫₀¹ |f_i| ≤ M_i`
    have hbd : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |D.f i t| ≤ (D.M i : ℝ) := by
      intro i t h0 h1
      have := ratPoly_bounds (hne i) (hbern i) h0 h1
      rw [abs_le]
      unfold SplineData.f
      constructor
      · have := this.1; push_cast at this; linarith
      · exact this.2
    have hi : ∀ i, ∫ t in (0 : ℝ)..1, |D.f i t| ≤ (D.M i : ℝ) := by
      intro i
      have h1 : ‖∫ t in (0 : ℝ)..1, |D.f i t|‖ ≤ (D.M i : ℝ) * |(1 : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIoc_of_le zero_le_one] using
          (Set.Ioc_subset_Icc_self ht)
        rw [Real.norm_eq_abs, abs_abs]
        exact hbd i t ht'.1 ht'.2
      simpa using (le_abs_self _).trans h1
    unfold Vp
    calc ∑ i, ∫ t in (0 : ℝ)..1, |D.f i t| ≤ ∑ i, (D.M i : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
      _ = ((∑ i, D.M i : ℚ) : ℝ) := by push_cast; rfl
      _ ≤ (D.Vt : ℝ) := by exact_mod_cast h
  · have hf0 : ∀ i t, 0 ≤ t → t ≤ 1 → 0 ≤ D.f i t := by
      intro i t h0 h1
      have hh := ratPoly_bounds (hne i) (all_finRangeS hpos i) h0 h1
      have := hh.1
      unfold SplineData.f
      simpa using this
    have h1 : Vp D.f = ∑ i, ∫ t in (0 : ℝ)..1, D.f i t := by
      unfold Vp
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le zero_le_one] using ht
      exact abs_of_nonneg (hf0 i t ht'.1 ht'.2)
    rw [h1, mass_real_of_rat hmass, hV1]; norm_num

/-- Everything `basicOkS` establishes, in the form the signed bridge consumes. -/
structure BasicFactsS (D : SplineDataS) : Prop where
  hM : 0 < D.Mq
  hε0 : 0 < (D.ε : ℝ)
  hε1 : (D.ε : ℝ) < 1
  r0_pos : 0 < D.r0
  W_pos : 0 < D.W
  hρ : 0 < (D.rho : ℝ)
  hθ : 0 < D.theta
  hηS : 0 < D.etaS
  hRc : 0 ≤ (D.Rc : ℝ)
  hcc : 0 ≤ (D.ccert : ℝ)
  hccert : 2 * ((D.mprime : ℝ) - D.gmin) ≤ D.ccert
  hAB : ∀ i, D.A i ≠ D.B i
  hne : ∀ i, D.l i ≠ []
  hbern : ∀ i, bernOkK (D.l i) (-(D.M i)) (D.M i) = true
  hM0 : ∀ i, 0 ≤ D.M i
  hmass : ∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1), coeffs (D.l i) j / ((j : ℚ) + 1) = 1
  hvar : Vp D.f ≤ (D.Vt : ℝ)
  hAR : ∀ i, ‖D.A i‖ ≤ (D.Rc : ℝ)
  hBR : ∀ i, ‖D.B i‖ ≤ (D.Rc : ℝ)
  hτ : Function.Involutive D.tauF
  hAτ : ∀ i, D.A (D.tauF i) = (starRingEnd ℂ) (D.A i)
  hBτ : ∀ i, D.B (D.tauF i) = (starRingEnd ℂ) (D.B i)
  hlτ : ∀ i, D.l (D.tauF i) = D.l i
  hloss : Real.pi * (D.rho : ℝ) * Bs D.A D.B (fun i => (D.M i : ℝ)) ≤ D.lossS
  hray : ∀ u : ℝ, (0 : ℝ) ≤ u → u ≤ D.umax → ∃ p ∈ D.rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ p.2
  hline : ∀ x : ℝ, (0 : ℝ) ≤ x → x ≤ 1 → ∃ p ∈ D.lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  hD : D.Dt ≤ 2 * (D.Mq * D.mprime + D.dim * D.Scap) - D.Mq ^ 2 * D.Ibound + D.Inu
    - (2 * D.Mq ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
      + D.Mq ^ 2 * (D.Vt * D.lossS + 2 * D.Vt * D.theta))

theorem basicOkS_sound (h : D.basicOkS = true) : BasicFactsS D := by
  have hvarOk : D.varOk = true := by
    simp only [basicOkS, Bool.and_eq_true] at h
    exact h.2
  simp only [basicOkS, dofOkS, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hε0, hε1, hr0, hW, hρ, hθ, hη, hRc, hcc, hcert, hseg, hconj, hmass, hl0, hloss,
    hray, hline, hD, -⟩ := h
  have hsegF : ∀ i, D.segOkS i = true := fun i => all_finRangeS hseg i
  have F := fun i => segOkS_facts hRc (hsegF i)
  have hconjF := fun i => SplineData.conjOk_facts (D := D.toSplineData) (all_finRangeS hconj i)
  have htauLt : ∀ i, (D.seg i).tau < D.n := fun i => (F i).2.2.2.2.2.2.2.2
  have hBs : Bs D.A D.B (fun i => (D.M i : ℝ)) ≤ (D.BsQ : ℝ) := by
    unfold Bs SplineData.BsQ
    push_cast
    exact Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (by exact_mod_cast (F i).2.2.2.2.1)
      (by exact_mod_cast (F i).2.2.2.1) (F i).2.2.2.2.2.1
  have hBs0 : 0 ≤ Bs D.A D.B (fun i => (D.M i : ℝ)) :=
    Finset.sum_nonneg fun i _ => div_nonneg (Rat.cast_nonneg.mpr (F i).2.2.2.2.1) (norm_nonneg _)
  have hlossR : (315 / 100 : ℝ) * D.rho * D.BsQ ≤ D.lossS := by
    have := (Rat.cast_le (K := ℝ)).2 hloss
    push_cast at this
    exact this
  have hρR : (0 : ℝ) < D.rho := by exact_mod_cast hρ
  have hpi : Real.pi ≤ 315 / 100 := by have := Real.pi_lt_d2; norm_num at this ⊢; linarith
  have hvar := varOk_sound hvarOk (fun i => (F i).2.1) (fun i => (F i).2.2.1)
    hmass
  refine ⟨hM, by exact_mod_cast hε0, by exact_mod_cast hε1, hr0, hW, hρR, hθ, hη,
    by exact_mod_cast hRc, by exact_mod_cast hcc, ?_, fun i => (F i).1, fun i => (F i).2.1,
    fun i => (F i).2.2.1, fun i => (F i).2.2.2.2.1, hmass, hvar,
    fun i => (F i).2.2.2.2.2.2.1, fun i => (F i).2.2.2.2.2.2.2.1,
    fun i => Fin.ext (by rw [SplineData.tauF_val htauLt]; exact (hconjF i).2.2.2.2.2),
    ?_, ?_, fun i => (hconjF i).2.2.2.2.1, ?_,
    fun u hu => coverOk_sound hray u (by simpa using hu),
    fun u hu hu1 => coverOk_sound hline u (by simpa using hu) (by simpa using hu1), hD⟩
  · exact_mod_cast hcert
  · intro i
    obtain ⟨a1, a2, -, -, -, -⟩ := hconjF i
    apply Complex.ext <;> simp [SplineData.A, a1, a2]
  · intro i
    obtain ⟨-, -, b1, b2, -, -⟩ := hconjF i
    apply Complex.ext <;> simp [SplineData.B, b1, b2]
  · calc Real.pi * (D.rho : ℝ) * Bs D.A D.B (fun i => (D.M i : ℝ))
        ≤ (315 / 100 : ℝ) * D.rho * Bs D.A D.B (fun i => (D.M i : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hBs0
          exact mul_le_mul_of_nonneg_right hpi hρR.le
      _ ≤ (315 / 100 : ℝ) * D.rho * D.BsQ := mul_le_mul_of_nonneg_left hBs (by positivity)
      _ ≤ D.lossS := hlossR

end SplineDataS

end CatalanCore.Uniform.Decay.Cert
