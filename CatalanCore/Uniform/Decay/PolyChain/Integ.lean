module

public import CatalanCore.Uniform.Decay.Polygon.Data
public import CatalanCore.Decay.Rect.IntegR

@[expose] public section

/-!
# Theorem N over a polygon contour (lane D, package D7)

The polygon analogue of `Frame.integrand_le_rect`, `det_bound_rect`, `theoremN_rect`
(`CatalanCore/Decay/Rect/IntegR.lean`).  The contour enters only through D4's
`SourceRep Fr N0 pts d C V` (exact entries, Andréief bound, weight bounds, residual mass) and
through the energy hypothesis `PolyEnergy`, which quantifies over free points in the range of the
polygon position map `polyPt`.

* `amp C = |C|/(2π) + 1 ≥ 1` is the amplitude (so `Cl = log (amp C) ≥ 0`).
* `vP`, `qP`: the integrable majorant and the remaining weight; `‖polyW‖ ≤ vP · qP`
  (`norm_polyW_le_vq`), `log qP ≤ (1-e)(log amp - 2π|Im|)` (`log_qP_le`),
  `∫ vP ≤ atomMass + 2 amp^e (L + ‖d‖/(2π e Im d))` (`integral_vP_le`) for `chainLen ≤ L`.
* **`theoremN_poly`**: `|det T[s,t]| ≤ exp (T + Nn log M0)`,
  `M0 = Wabs R + (Wabs ⌈xs⌉ + 2 amp^e (L + ‖d‖/(2π e Im d)) + 1)`.
-/

open Finset MeasureTheory Set
open CatalanLambda.Decay (cexpr)

namespace CatalanCore.Uniform.Decay.PolyChain

open CatalanCore CatalanCore.Decay CatalanCore.Uniform.Decay.Polygon

variable {Fr : Frame}

/-- The amplitude `|C|/(2π) + 1`. -/
noncomputable def amp (C : ℝ) : ℝ := |C| / (2 * Real.pi) + 1

theorem one_le_amp (C : ℝ) : 1 ≤ amp C := by
  unfold amp
  have : 0 ≤ |C| / (2 * Real.pi) := by have := Real.pi_pos; positivity
  linarith

theorem amp_pos (C : ℝ) : 0 < amp C := lt_of_lt_of_le one_pos (one_le_amp C)

theorem log_amp_nonneg (C : ℝ) : 0 ≤ Real.log (amp C) := Real.log_nonneg (one_le_amp C)

theorem div_le_amp (C : ℝ) : C / (2 * Real.pi) ≤ amp C := by
  unfold amp
  have hpi := Real.pi_pos
  have : C / (2 * Real.pi) ≤ |C| / (2 * Real.pi) :=
    div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
  linarith

/-- The upper path point `γ(u)`. -/
noncomputable abbrev gam (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (u : ℝ) : ℂ :=
  pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u

/-- The upper path velocity `γ'(u)`. -/
noncomputable abbrev gamD (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (u : ℝ) : ℂ :=
  pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u

/-- The path part of the majorant: `amp^e e^{-2π e |Im γ|} ‖γ'‖`. -/
noncomputable def vPath (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C e : ℝ) (u : ℝ) : ℝ :=
  amp C ^ e * (Real.exp (-((2 * Real.pi * e) * |(gam Fr N0 pts d u).im|)) * ‖gamD Fr N0 pts d u‖)

/-- Integrable majorant on the polygon space. -/
noncomputable def vP (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C e : ℝ) : Fr.XT N0 → ℝ :=
  Sum.elim (fun p => |(Fr.w p.1.2 : ℝ)|)
    (Sum.elim (fun u => vPath Fr N0 pts d C e u.1) (fun u => vPath Fr N0 pts d C e u.1))

/-- Remaining weight on the polygon space. -/
noncomputable def qP (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C e : ℝ) : Fr.XT N0 → ℝ :=
  Sum.elim (fun _ => 1)
    (Sum.elim (fun u => amp C ^ (1 - e) * Real.exp (-((1 - e) * (2 * Real.pi * |(gam Fr N0 pts d u.1).im|))))
      (fun u => amp C ^ (1 - e) * Real.exp (-((1 - e) * (2 * Real.pi * |(gam Fr N0 pts d u.1).im|)))))

theorem vPath_nonneg (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C e u : ℝ) :
    0 ≤ vPath Fr N0 pts d C e u := by
  unfold vPath; have := amp_pos C; positivity

theorem vP_nonneg (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C e : ℝ) (x : Fr.XT N0) :
    0 ≤ vP Fr N0 pts d C e x := by
  rcases x with p | u | u
  · simp [vP]
  · exact vPath_nonneg N0 pts d C e u.1
  · exact vPath_nonneg N0 pts d C e u.1

theorem qP_pos (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C e : ℝ) (x : Fr.XT N0) :
    0 < qP Fr N0 pts d C e x := by
  have := amp_pos C
  rcases x with p | u | u <;> simp [qP] <;> positivity

/-- `|Im|` of a polygon-space point: `0` on atoms, `|Im γ(u)|` on both copies. -/
theorem polyPt_im_abs {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) (x : Fr.XT N0) :
    |(polyPt Fr N0 pts d x).im| = Sum.elim (fun _ => (0 : ℝ))
      (Sum.elim (fun u => |(gam Fr N0 pts d u.1).im|) (fun u => |(gam Fr N0 pts d u.1).im|)) x := by
  rcases x with p | u | u
  · simp [polyPt]
  · simp [polyPt, gam]
  · simp only [polyPt, Sum.elim_inr, gam]
    rw [hS.conj_pt u.1, Complex.conj_im, abs_neg]

theorem amp_split {C e : ℝ} (b : ℝ) :
    amp C ^ e * Real.exp (-(e * b)) * (amp C ^ (1 - e) * Real.exp (-((1 - e) * b)))
      = amp C * Real.exp (-b) := by
  have hA := amp_pos C
  have h1 : amp C ^ e * amp C ^ (1 - e) = amp C := by
    rw [← Real.rpow_add hA]; simp
  have h2 : Real.exp (-(e * b)) * Real.exp (-((1 - e) * b)) = Real.exp (-b) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ = (amp C ^ e * amp C ^ (1 - e)) * (Real.exp (-(e * b)) * Real.exp (-((1 - e) * b))) := by ring
    _ = _ := by rw [h1, h2]

/-- **Weight factorisation**: `‖polyW‖ ≤ vP · qP`. -/
theorem norm_polyW_le_vq {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) (e : ℝ) (x : Fr.XT N0) :
    ‖polyW Fr N0 pts d x‖ ≤ vP Fr N0 pts d C e x * qP Fr N0 pts d C e x := by
  have key : ∀ u : ℝ, 0 ≤ u → ∀ E : ℝ,
      E ≤ C / (2 * Real.pi) * Real.exp (-(2 * Real.pi * |(gam Fr N0 pts d u).im|))
        * ‖gamD Fr N0 pts d u‖ →
      E ≤ vPath Fr N0 pts d C e u *
        (amp C ^ (1 - e) * Real.exp (-((1 - e) * (2 * Real.pi * |(gam Fr N0 pts d u).im|)))) := by
    intro u _ E hE
    set b : ℝ := 2 * Real.pi * |(gam Fr N0 pts d u).im| with hb
    have e1 : vPath Fr N0 pts d C e u * (amp C ^ (1 - e) * Real.exp (-((1 - e) * b)))
        = (amp C ^ e * Real.exp (-(e * b)) * (amp C ^ (1 - e) * Real.exp (-((1 - e) * b))))
          * ‖gamD Fr N0 pts d u‖ := by
      unfold vPath
      have : (2 * Real.pi * e) * |(gam Fr N0 pts d u).im| = e * b := by rw [hb]; ring
      rw [this]; ring
    rw [e1, amp_split]
    refine hE.trans ?_
    have h0 : 0 ≤ Real.exp (-b) * ‖gamD Fr N0 pts d u‖ := by positivity
    have := mul_le_mul_of_nonneg_right (div_le_amp C) h0
    calc C / (2 * Real.pi) * Real.exp (-b) * ‖gamD Fr N0 pts d u‖
        = C / (2 * Real.pi) * (Real.exp (-b) * ‖gamD Fr N0 pts d u‖) := by ring
      _ ≤ amp C * (Real.exp (-b) * ‖gamD Fr N0 pts d u‖) := this
      _ = _ := by ring
  rcases x with p | u | u
  · rw [hS.weight_atom p]; simp [vP, qP]
  · simp only [polyW, vP, qP, Sum.elim_inr, Sum.elim_inl]
    exact key u.1 u.2.le _ (hS.weight_up u.1 u.2.le)
  · simp only [polyW, vP, qP, Sum.elim_inr]
    exact key u.1 u.2.le _ (hS.weight_low u.1 u.2.le)

/-- **The logarithmic field bound** for `qP`. -/
theorem log_qP_le {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) {e : ℝ} (he1 : e < 1) (x : Fr.XT N0) :
    Real.log (qP Fr N0 pts d C e x)
      ≤ (1 - e) * (Real.log (amp C) - 2 * Real.pi * |(polyPt Fr N0 pts d x).im|) := by
  have hA := amp_pos C
  have hl := log_amp_nonneg C
  rw [polyPt_im_abs hS]
  have h1 : 0 < 1 - e := by linarith
  rcases x with p | u | u
  · simp only [qP, Sum.elim_inl, Real.log_one, mul_zero, sub_zero]
    exact mul_nonneg h1.le hl
  · simp only [qP, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    nlinarith
  · simp only [qP, Sum.elim_inr]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    nlinarith

theorem vPath_integrable {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) {e : ℝ} (he0 : 0 < e) :
    IntegrableOn (fun u => vPath Fr N0 pts d C e u) (Ioi 0) := by
  have hc : 0 < 2 * Real.pi * e := by have := Real.pi_pos; positivity
  exact ((hS.mass _ hc).1.const_mul (amp C ^ e))

theorem integrable_vP {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) {e : ℝ} (he0 : 0 < e) :
    Integrable (vP Fr N0 pts d C e) (Fr.muT N0) := by
  unfold Frame.muT
  rw [integrable_sumM_iff_gen, integrable_sumM_iff_gen]
  have hI := vPath_integrable hS he0
  exact ⟨Integrable.of_finite, (integrable_comap_Ioi_real _).2 hI,
    (integrable_comap_Ioi_real _).2 hI⟩

/-- **Total mass of the majorant.** -/
theorem integral_vP_le {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) {e : ℝ} (he0 : 0 < e) {L : ℝ}
    (hL : chainLen ((Fr.xstar N0 : ℝ) : ℂ) pts ≤ L) :
    ∫ x, vP Fr N0 pts d C e x ∂(Fr.muT N0)
      ≤ Fr.atomMass N0 + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im))) := by
  have hc : 0 < 2 * Real.pi * e := by have := Real.pi_pos; positivity
  have hint := integrable_vP hS he0
  have hI := vPath_integrable hS he0
  have hray : ∫ u in Ioi (0 : ℝ), vPath Fr N0 pts d C e u
      ≤ amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im)) := by
    unfold vPath
    rw [integral_const_mul]
    have hA : 0 ≤ amp C ^ e := by have := amp_pos C; positivity
    refine mul_le_mul_of_nonneg_left ?_ hA
    have := (hS.mass _ hc).2
    linarith
  unfold Frame.muT at hint ⊢
  rw [integral_sumM_gen _ _ _ hint]
  have hint2 := ((integrable_sumM_iff_gen _ _ _).1 hint).2
  rw [integral_sumM_gen _ _ _ hint2]
  have hA : ∫ p : ↥(Fr.atomIdx N0), vP Fr N0 pts d C e (Sum.inl p)
        ∂(Measure.count : Measure ↥(Fr.atomIdx N0)) = Fr.atomMass N0 := by
    rw [integral_count]
    simp [vP, Frame.atomMass]
  have hsub := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
    (fun u => vPath Fr N0 pts d C e u)
  have hU : ∫ x : RayP, vP Fr N0 pts d C e (Sum.inr (Sum.inl x))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ u in Ioi (0 : ℝ), vPath Fr N0 pts d C e u := by
    simp only [vP, Sum.elim_inr, Sum.elim_inl]; exact hsub
  have hLo : ∫ x : RayP, vP Fr N0 pts d C e (Sum.inr (Sum.inr x))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ u in Ioi (0 : ℝ), vPath Fr N0 pts d C e u := by
    simp only [vP, Sum.elim_inr]; exact hsub
  rw [hA, hU, hLo]; linarith

/-! ### The energy hypothesis and the integration step -/

/-- The pointwise energy hypothesis on the polygon space: for distinct free points in the range of
the polygon position map and every weight `q` obeying the field bound with parameter `e`,
`∑ log q + ½ (log‖C(x,s)‖² + log‖C(x,t)‖²) ≤ T`. -/
def PolyEnergy (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (k : ℕ) (e Cl T : ℝ)
    (s t : Fin k → ℕ) : Prop :=
  ∀ (x : Fin k → ℂ), Function.Injective x → (∀ l, x l ∈ Set.range (polyPt Fr N0 pts d)) →
    ∀ (q : Fin k → ℝ), (∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(x l).im|)) →
    ∑ l, Real.log (q l) + (1 / 2) * (Real.log (‖cexpr x (fun i => (s i : ℂ))‖ ^ 2)
        + Real.log (‖cexpr x (fun i => (t i : ℂ))‖ ^ 2)) ≤ T

/-- **Pointwise bound for the polygon Andréief integrand.** -/
theorem integrand_le_poly {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) {e : ℝ} (he1 : e < 1) {k : ℕ} {s t : Fin k → ℕ} {T : ℝ}
    (hE : PolyEnergy Fr N0 pts d k e (Real.log (amp C)) T s t) (z : Fin k → Fr.XT N0) :
    (∏ l, ‖polyW Fr N0 pts d (z l)‖) *
        (‖cexpr (fun l => polyPt Fr N0 pts d (z l)) (fun i => (s i : ℂ))‖ *
          ‖cexpr (fun l => polyPt Fr N0 pts d (z l)) (fun i => (t i : ℂ))‖)
      ≤ Real.exp T * ∏ l, vP Fr N0 pts d C e (z l) := by
  classical
  set x : Fin k → ℂ := fun l => polyPt Fr N0 pts d (z l) with hx
  have hv0 : 0 ≤ ∏ l, vP Fr N0 pts d C e (z l) :=
    Finset.prod_nonneg (fun l _ => vP_nonneg N0 pts d C e _)
  by_cases hinj : Function.Injective x
  · have hq0 : ∀ l, 0 < qP Fr N0 pts d C e (z l) := fun l => qP_pos N0 pts d C e _
    have hA := hE x hinj (fun l => ⟨z l, rfl⟩)
      (fun l => qP Fr N0 pts d C e (z l)) (fun l => log_qP_le hS he1 (z l))
    have hP0 : 0 ≤ ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ := by positivity
    have hP : 0 < ∏ l, qP Fr N0 pts d C e (z l) := Finset.prod_pos (fun l _ => hq0 l)
    have step1 : (∏ l, ‖polyW Fr N0 pts d (z l)‖)
        ≤ ∏ l, (vP Fr N0 pts d C e (z l) * qP Fr N0 pts d C e (z l)) :=
      Finset.prod_le_prod₀ (fun l _ => norm_nonneg _) (fun l _ => norm_polyW_le_vq hS e _)
    have step2 : (∏ l, qP Fr N0 pts d C e (z l)) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖) ≤ Real.exp T := by
      by_cases h0 : ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ = 0
      · rw [h0, mul_zero]; exact (Real.exp_pos _).le
      · have hpos : 0 < ‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖ :=
          lt_of_le_of_ne hP0 (Ne.symm h0)
        have hs0 : ‖cexpr x (fun i => (s i : ℂ))‖ ≠ 0 := fun h => h0 (by rw [h, zero_mul])
        have ht0 : ‖cexpr x (fun i => (t i : ℂ))‖ ≠ 0 := fun h => h0 (by rw [h, mul_zero])
        rw [← Real.log_le_iff_le_exp (mul_pos hP hpos), Real.log_mul hP.ne' hpos.ne',
          Real.log_prod (fun l _ => (hq0 l).ne'), Real.log_mul hs0 ht0]
        have e1 : Real.log (‖cexpr x (fun i => (s i : ℂ))‖ ^ 2)
            = 2 * Real.log ‖cexpr x (fun i => (s i : ℂ))‖ := by
          rw [Real.log_pow]; norm_num
        have e2 : Real.log (‖cexpr x (fun i => (t i : ℂ))‖ ^ 2)
            = 2 * Real.log ‖cexpr x (fun i => (t i : ℂ))‖ := by
          rw [Real.log_pow]; norm_num
        linarith
    calc (∏ l, ‖polyW Fr N0 pts d (z l)‖) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖)
        ≤ (∏ l, (vP Fr N0 pts d C e (z l) * qP Fr N0 pts d C e (z l))) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖) :=
          mul_le_mul_of_nonneg_right step1 hP0
      _ = (∏ l, vP Fr N0 pts d C e (z l)) * ((∏ l, qP Fr N0 pts d C e (z l)) *
          (‖cexpr x (fun i => (s i : ℂ))‖ * ‖cexpr x (fun i => (t i : ℂ))‖)) := by
          rw [Finset.prod_mul_distrib]; ring
      _ ≤ (∏ l, vP Fr N0 pts d C e (z l)) * Real.exp T := mul_le_mul_of_nonneg_left step2 hv0
      _ = _ := by ring
  · have hz0 := Frame.cexpr_zero_of_not_inj x (fun i => (s i : ℂ)) hinj
    rw [hz0]; simp
    positivity

/-- **The integrated bound for `norm · T[s,t]` on a polygon.** -/
theorem det_bound_poly {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) {e : ℝ} (he0 : 0 < e) (he1 : e < 1) {L : ℝ}
    (hL : chainLen ((Fr.xstar N0 : ℝ) : ℂ) pts ≤ L) {k : ℕ} {s t : Fin k → ℕ}
    (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : PolyEnergy Fr N0 pts d k e (Real.log (amp C)) T s t) :
    ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * (Real.exp T
          * (Fr.atomMass N0 + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im)))) ^ k) := by
  classical
  have hb := hS.andreief k s t hs ht
  have hmeas := integrable_vP hS he0
  have hGi : Integrable (fun z : Fin k → Fr.XT N0 => Real.exp T * ∏ l, vP Fr N0 pts d C e (z l))
      (Measure.pi fun _ => Fr.muT N0) :=
    (Integrable.fintype_prod (f := fun (_ : Fin k) (x : Fr.XT N0) => vP Fr N0 pts d C e x)
      (μ := fun _ => Fr.muT N0) (fun _ => hmeas)).const_mul _
  have hle : ∫ z : Fin k → Fr.XT N0, (∏ l, ‖polyW Fr N0 pts d (z l)‖) *
            (‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((polyPt Fr N0 pts d (z l') - polyPt Fr N0 pts d (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (polyPt Fr N0 pts d (z l) - s i)‖ *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((polyPt Fr N0 pts d (z l') - polyPt Fr N0 pts d (z l)) * ((t l : ℂ) - t l')))
              / ∏ l, ∏ i, (polyPt Fr N0 pts d (z l) - t i)‖) ∂(Measure.pi fun _ => Fr.muT N0)
      ≤ ∫ z : Fin k → Fr.XT N0, Real.exp T * ∏ l, vP Fr N0 pts d C e (z l)
          ∂(Measure.pi fun _ => Fr.muT N0) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hGi
      (Filter.Eventually.of_forall (fun z => ?_))
    · positivity
    · exact integrand_le_poly hS he1 hE z
  have hint0 : 0 ≤ ∫ x, vP Fr N0 pts d C e x ∂(Fr.muT N0) :=
    integral_nonneg (fun x => vP_nonneg N0 pts d C e x)
  have hG : ∫ z : Fin k → Fr.XT N0, Real.exp T * ∏ l, vP Fr N0 pts d C e (z l)
        ∂(Measure.pi fun _ => Fr.muT N0)
      ≤ Real.exp T * (Fr.atomMass N0 + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im)))) ^ k := by
    rw [integral_const_mul, integral_fintype_prod_eq_pow (fun x => vP Fr N0 pts d C e x),
      Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hint0 (integral_vP_le hS he0 hL) k)
      (Real.exp_pos T).le
  calc _ ≤ _ := hb
    _ ≤ (1 / (k.factorial : ℝ)) * (Real.exp T
          * (Fr.atomMass N0 + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im)))) ^ k) := by
        exact mul_le_mul_of_nonneg_left (hle.trans hG) (by positivity)

theorem chainLen_nonneg : ∀ (a : ℂ) (l : List ℂ), 0 ≤ chainLen a l
  | _, [] => le_rfl
  | a, b :: l => by
    simp only [chainLen]
    have := chainLen_nonneg b l
    positivity

/-- **Theorem N over a polygon.**  For every source representation over a physical polygon, every
`k × k` rectangular minor `T[s,t]` (injective row nodes `s`, column nodes `t`, `k ≤ Nn`, head
`N0 ≤ R`, physical chain length `≤ L`) obeying the polygon energy hypothesis satisfies
`|det T[s,t]| ≤ exp (T + Nn · log M0)`,
`M0 = Wabs R + (Wabs ⌈xs⌉ + 2 amp^e (L + ‖d‖/(2π e Im d)) + 1)`. -/
theorem theoremN_poly (hnorm : (1 : ℚ) ≤ Fr.norm) {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ}
    (hS : SourceRep Fr N0 pts d C V) (hd : 0 < d.im) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {L : ℝ} (hL : chainLen ((Fr.xstar N0 : ℝ) : ℂ) pts ≤ L) {k Nn : ℕ} (hkN : k ≤ Nn)
    {R : ℝ} (hR : (N0 : ℝ) ≤ R) {s t : Fin k → ℕ}
    (hs : Function.Injective s) (ht : Function.Injective t) {T : ℝ}
    (hE : PolyEnergy Fr N0 pts d k e (Real.log (amp C)) T s t) :
    |(Matrix.of fun i j : Fin k => Fr.Tent (s i) (t j)).det|
      ≤ Real.exp (T + Nn * Real.log (Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
          + 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im))) + 1))) := by
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => Fr.Tent (s i) (t j) with hM
  have hnorm' : (1 : ℝ) ≤ Fr.norm := by exact_mod_cast hnorm
  have hcast : (Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ))
      = Complex.ofRealHom.mapMatrix ((Fr.norm : ℝ) • M) := by
    ext i j; simp [hM]
  have hdet : ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      = (Fr.norm : ℝ) ^ k * |M.det| := by
    rw [hcast, ← RingHom.map_det, Matrix.det_smul]
    simp [Complex.norm_real, abs_mul, abs_of_pos (show (0 : ℝ) < Fr.norm by linarith)]
  have hb := det_bound_poly hS he0 he1 hL hs ht hE
  rw [hdet] at hb
  have hL0 : 0 ≤ L := (chainLen_nonneg _ _).trans hL
  set cE : ℝ := 2 * (amp C ^ e * (L + ‖d‖ / ((2 * Real.pi * e) * d.im))) with hcE
  have hcE0 : 0 ≤ cE := by
    have := amp_pos C
    have : 0 < (2 * Real.pi * e) * d.im := by have := Real.pi_pos; positivity
    rw [hcE]; positivity
  have hW0 := Fr.Wabs_nonneg
  have hR0 : 0 ≤ R := le_trans (Nat.cast_nonneg _) hR
  set M0 : ℝ := Fr.Wabs * R + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + cE + 1) with hM0
  have hM01 : 1 ≤ M0 := by
    have : (0 : ℝ) ≤ Fr.Wabs * R := by positivity
    have : (0 : ℝ) ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    linarith
  have hbase : Fr.atomMass N0 + cE ≤ M0 := by
    have h1 := Fr.atomMass_le N0
    have h2 : ((N0 : ℝ) + ⌈(Fr.xs : ℝ)⌉₊) * Fr.Wabs ≤ Fr.Wabs * R + Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by
      nlinarith
    rw [hM0]; linarith
  have hbase0 : 0 ≤ Fr.atomMass N0 + cE := by
    have : 0 ≤ Fr.atomMass N0 := by
      unfold Frame.atomMass
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hpow : (Fr.atomMass N0 + cE) ^ k ≤ M0 ^ Nn :=
    (pow_le_pow_left₀ hbase0 hbase k).trans (pow_le_pow_right₀ hM01 hkN)
  have hMh : M0 ^ Nn = Real.exp (Nn * Real.log M0) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]; simp
  have hfac : (1 : ℝ) ≤ k.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have hE0 := Real.exp_pos T
  have step : (Fr.norm : ℝ) ^ k * |M.det| ≤ Real.exp T * M0 ^ Nn := by
    refine hb.trans ?_
    calc (1 / (k.factorial : ℝ)) * (Real.exp T * (Fr.atomMass N0 + cE) ^ k)
        ≤ 1 * (Real.exp T * (Fr.atomMass N0 + cE) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by linarith)]; exact hfac
      _ ≤ Real.exp T * M0 ^ Nn := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hE0.le
  have h1 : |M.det| ≤ (Fr.norm : ℝ) ^ k * |M.det| := by
    nlinarith [abs_nonneg M.det, one_le_pow₀ hnorm' (n := k)]
  refine (h1.trans step).trans (le_of_eq ?_)
  rw [hMh, ← Real.exp_add]

end CatalanCore.Uniform.Decay.PolyChain
