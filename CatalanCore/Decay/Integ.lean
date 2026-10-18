module

public import CatalanCore.Decay.Lemma
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Theorem N for a general frame: weights, integration step, node-removal bound (WP2b)

Generalisation of the legacy `ThmNInteg` + `ThmNFinal`.  Differences from the λ code:

* the ray constant is the finite `C_E = Fr.rayConst` of `RayBound` (`Aco = (C_E + 1)/(2π)`);
* the atoms carry the weight `|w_i|` (so the atom mass is `∑_{(m,i)} |w_i| ≤ (N0 + ⌈xs⌉) ∑|w_i|`);
* the free points satisfy `m0 ≤ -Re z` with `m0 ≤ min (xs, μ_i)`;
* `norm ≥ 1` (so that the factor `norm^k` can be dropped).

`theoremN` : for `h ≥ h0` (`hW`) and `N0 + n0off = ⌊r0 h⌋`, every principal minor of `T`
satisfies `|det T[S]| ≤ exp(-h² D + h (h - k) c_cert + Eerr h)`.
-/

open Finset MeasureTheory Set
open CatalanLambda.Decay (gfun Usig Utau Irho cexpr nodeC rmask rayPt)

namespace CatalanCore

namespace Frame

open Decay

variable {Fr : Frame}

/-- `norm ≥ 1` joins the frame hypotheses of the decay argument. -/
structure DecayOK' (Fr : Frame) : Prop extends DecayOK Fr where
  norm_ge : (1 : ℚ) ≤ Fr.norm

/-- Sum of the absolute values of the weights. -/
noncomputable def Wabs (Fr : Frame) : ℝ := ∑ i, |(Fr.w i : ℝ)|

/-- The amplitude of the bound for `‖w‖ = ‖E‖/2π` on the rays. -/
noncomputable def Aco (Fr : Frame) : ℝ := (Fr.rayConst + 1) / (2 * Real.pi)

lemma Aco_pos (hC : Fr.ContourOK) : 0 < Fr.Aco := by
  have := Fr.rayConst_nonneg hC
  unfold Aco; positivity

lemma Wabs_nonneg (Fr : Frame) : 0 ≤ Fr.Wabs := Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- The decay factor `2π r sin φ` along a ray. -/
noncomputable def bray (r : ℝ) : ℝ := 2 * Real.pi * (r * Real.sin phiR)

lemma bray_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ bray r := by
  unfold bray
  have := sin_phiR_pos
  positivity

/-- The decay rate of `v_ε` along a ray. -/
noncomputable def betaE (ε : ℝ) : ℝ := ε * (2 * Real.pi * Real.sin phiR)

lemma betaE_pos {ε : ℝ} (hε : 0 < ε) : 0 < betaE ε := by
  unfold betaE; have := sin_phiR_pos; positivity

/-- Integrable majorant `v_ε` (atoms: `|w_i|`; rays: `A^ε e^{-ε b(r)}`). -/
noncomputable def vEps (Fr : Frame) (ε : ℝ) (N0 : ℕ) : Fr.XT N0 → ℝ :=
  Sum.elim (fun p => |(Fr.w p.1.2 : ℝ)|)
    (Sum.elim (fun r => Fr.Aco ^ ε * Real.exp (-(ε * bray r.1)))
      (fun r => Fr.Aco ^ ε * Real.exp (-(ε * bray r.1))))

/-- Remaining weight `q_ε` (atoms: 1; rays: `A^{1-ε} e^{-(1-ε) b(r)}`). -/
noncomputable def qEps (Fr : Frame) (ε : ℝ) (N0 : ℕ) : Fr.XT N0 → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun r => Fr.Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r.1)))
    (fun r => Fr.Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r.1))))

lemma vEps_nonneg (hC : Fr.ContourOK) (ε : ℝ) (N0 : ℕ) (x : Fr.XT N0) : 0 ≤ vEps Fr ε N0 x := by
  have := Aco_pos hC
  rcases x with p | r | r <;> simp [vEps] <;> positivity

lemma qEps_pos (hC : Fr.ContourOK) (ε : ℝ) (N0 : ℕ) (x : Fr.XT N0) : 0 < qEps Fr ε N0 x := by
  have := Aco_pos hC
  rcases x with p | r | r <;> simp [qEps] <;> positivity

lemma ptT_atom_or_ray (N0 : ℕ) (x : Fr.XT N0) :
    Fr.IsAtom N0 (Fr.ptT N0 x) ∨ Fr.IsRay N0 (Fr.ptT N0 x) := by
  rcases x with p | r | r
  · left
    exact ⟨p.1, p.2, rfl⟩
  · right
    exact ⟨r.1, r.2, phiR, Or.inl rfl, by simp [ptT]⟩
  · right
    exact ⟨r.1, r.2, -phiR, Or.inr rfl, by simp [ptT]⟩

theorem ptT_re (hC : Fr.ContourOK) {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    (N0 : ℕ) (x : Fr.XT N0) : m0 ≤ -(Fr.ptT N0 x).re := by
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hN : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
  rcases x with p | r | r
  · simp only [ptT, Sum.elim_inl, atomPos, Complex.ofReal_re]
    have := hm0μ p.1.2
    have : (0 : ℝ) ≤ (p.1.1 : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [CatalanLambda.Decay.rayPt_re]
    have := cos_phiR_neg
    have hr : 0 < r.1 := r.2
    unfold xstar
    nlinarith
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [CatalanLambda.Decay.rayPt_re, Real.cos_neg]
    have := cos_phiR_neg
    have hr : 0 < r.1 := r.2
    unfold xstar
    nlinarith

theorem ptT_im_abs (N0 : ℕ) (x : Fr.XT N0) :
    |(Fr.ptT N0 x).im| = Sum.elim (fun _ => (0 : ℝ))
      (Sum.elim (fun r => r.1 * Real.sin phiR) (fun r => r.1 * Real.sin phiR)) x := by
  have hs : 0 < Real.sin phiR := sin_phiR_pos
  rcases x with p | r | r
  · simp [ptT]
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [CatalanLambda.Decay.rayPt_im, abs_of_pos (mul_pos r.2 hs)]
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [CatalanLambda.Decay.rayPt_im, Real.sin_neg, mul_neg, abs_neg, abs_of_pos (mul_pos r.2 hs)]

theorem norm_wT_le_vq (hC : Fr.ContourOK) (hδ : (1 : ℚ) / 12 ≤ Fr.δ0) (ε : ℝ) (N0 : ℕ)
    (x : Fr.XT N0) : ‖Fr.wT N0 x‖ ≤ vEps Fr ε N0 x * qEps Fr ε N0 x := by
  have hA := Aco_pos hC
  have key : ∀ r : ℝ, 0 ≤ r → ∀ E : ℝ, E ≤ (Fr.rayConst + 1) * Real.exp (-bray r) →
      E / (2 * Real.pi) ≤ Fr.Aco ^ ε * Real.exp (-(ε * bray r)) *
        (Fr.Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r))) := by
    intro r _ E hE
    have e : Fr.Aco ^ ε * Real.exp (-(ε * bray r)) * (Fr.Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r)))
        = Fr.Aco * Real.exp (-bray r) := by
      have h1 : Fr.Aco ^ ε * Fr.Aco ^ (1 - ε) = Fr.Aco := by
        rw [← Real.rpow_add hA]; simp
      have h2 : Real.exp (-(ε * bray r)) * Real.exp (-((1 - ε) * bray r)) = Real.exp (-bray r) := by
        rw [← Real.exp_add]; congr 1; ring
      calc _ = (Fr.Aco ^ ε * Fr.Aco ^ (1 - ε)) * (Real.exp (-(ε * bray r)) * Real.exp (-((1 - ε) * bray r))) := by ring
        _ = _ := by rw [h1, h2]
    rw [e, Aco, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hCE := Fr.rayConst_nonneg hC
  have hray : ∀ θ : ℝ, (θ = phiR ∨ θ = -phiR) → ∀ r : ℝ, 0 ≤ r →
      ‖Fr.EC (rayPt (Fr.xstar N0) θ r)‖ ≤ (Fr.rayConst + 1) * Real.exp (-bray r) := by
    intro θ hθ r hr
    have := Fr.ray_E_bound hC phiR_gt phiR_lt (phiR_cot hδ) N0 hθ hr
    unfold bray
    refine this.trans ?_
    have : 0 ≤ Real.exp (-(2 * Real.pi * (r * Real.sin phiR))) := (Real.exp_pos _).le
    nlinarith
  rcases x with p | r | r
  · rw [norm_wT_atom]; simp [vEps, qEps]
  · rw [norm_wT_up]
    simp only [vEps, qEps, Sum.elim_inr, Sum.elim_inl]
    exact key _ r.2.le _ (hray phiR (Or.inl rfl) r.1 r.2.le)
  · rw [norm_wT_low]
    simp only [vEps, qEps, Sum.elim_inr, Sum.elim_inl]
    exact key _ r.2.le _ (hray (-phiR) (Or.inr rfl) r.1 r.2.le)

/-- The logarithmic field bound for `q_ε`. -/
lemma log_qEps_le (hC : Fr.ContourOK) {ε : ℝ} (hε1 : ε < 1) (N0 : ℕ) (x : Fr.XT N0) :
    Real.log (qEps Fr ε N0 x)
      ≤ (1 - ε) * (max (Real.log Fr.Aco) 0 - 2 * Real.pi * |(Fr.ptT N0 x).im|) := by
  have hA := Aco_pos hC
  rw [ptT_im_abs]
  have h1 : 0 < 1 - ε := by linarith
  have hC1 := le_max_left (Real.log Fr.Aco) 0
  have hC0 := le_max_right (Real.log Fr.Aco) 0
  rcases x with p | r | r
  · simp only [qEps, Sum.elim_inl, Real.log_one, mul_zero, sub_zero]
    exact mul_nonneg h1.le hC0
  · simp only [qEps, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    unfold bray
    nlinarith
  · simp only [qEps, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    unfold bray
    nlinarith

lemma vEps_ray (hC : Fr.ContourOK) (ε : ℝ) (r : ℝ) :
    Fr.Aco ^ ε * Real.exp (-(ε * bray r)) = Fr.Aco ^ ε * Real.exp (-(betaE ε) * r) := by
  unfold bray betaE; congr 2; ring

lemma integrable_vEps (hC : Fr.ContourOK) {ε : ℝ} (hε : 0 < ε) (N0 : ℕ) :
    Integrable (vEps Fr ε N0) (Fr.muT N0) := by
  unfold muT
  rw [integrable_sumM_iff_gen, integrable_sumM_iff_gen]
  have hb := betaE_pos hε
  have hI : IntegrableOn (fun r : ℝ => Fr.Aco ^ ε * Real.exp (-(betaE ε) * r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(betaE ε)) (by linarith) 0).const_mul _
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · refine (integrable_comap_Ioi_real (fun r => Fr.Aco ^ ε * Real.exp (-(betaE ε) * r))).2 hI |>.congr ?_
    exact Filter.Eventually.of_forall (fun r => by simp [vEps, vEps_ray hC])
  · refine (integrable_comap_Ioi_real (fun r => Fr.Aco ^ ε * Real.exp (-(betaE ε) * r))).2 hI |>.congr ?_
    exact Filter.Eventually.of_forall (fun r => by simp [vEps, vEps_ray hC])

/-- The atom mass `∑_{(m,i) ∈ atoms} |w_i|`. -/
noncomputable def atomMass (Fr : Frame) (N0 : ℕ) : ℝ := ∑ p : ↥(Fr.atomIdx N0), |(Fr.w p.1.2 : ℝ)|

lemma atomMass_le (Fr : Frame) (N0 : ℕ) :
    Fr.atomMass N0 ≤ ((N0 : ℝ) + ⌈(Fr.xs : ℝ)⌉₊) * Fr.Wabs := by
  classical
  unfold atomMass
  rw [Finset.sum_coe_sort (Fr.atomIdx N0) (fun p => |(Fr.w p.2 : ℝ)|)]
  have hsub : Fr.atomIdx N0 ⊆ (range (N0 + ⌈(Fr.xs : ℝ)⌉₊)) ×ˢ (univ : Finset (Fin Fr.d)) :=
    Finset.filter_subset _ _
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans ?_
  rw [Finset.sum_product]
  simp [Wabs]

/-- The total mass of `v_ε`. -/
theorem integral_vEps (hC : Fr.ContourOK) {ε : ℝ} (hε : 0 < ε) (N0 : ℕ) :
    ∫ x, vEps Fr ε N0 x ∂(Fr.muT N0) = Fr.atomMass N0 + 2 * (Fr.Aco ^ ε / betaE ε) := by
  have hb := betaE_pos hε
  have hint := integrable_vEps hC hε N0
  have hI : IntegrableOn (fun r : ℝ => Fr.Aco ^ ε * Real.exp (-(betaE ε) * r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(betaE ε)) (by linarith) 0).const_mul _
  have hray : ∫ r in Ioi (0 : ℝ), Fr.Aco ^ ε * Real.exp (-(betaE ε) * r) = Fr.Aco ^ ε / betaE ε := by
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -(betaE ε)) (by linarith) 0]
    simp; field_simp
  unfold muT at hint ⊢
  rw [integral_sumM_gen _ _ _ hint]
  have hint2 := ((integrable_sumM_iff_gen _ _ _).1 hint).2
  rw [integral_sumM_gen _ _ _ hint2]
  have hA : ∫ p : ↥(Fr.atomIdx N0), vEps Fr ε N0 (Sum.inl p)
        ∂(Measure.count : Measure ↥(Fr.atomIdx N0)) = Fr.atomMass N0 := by
    rw [integral_count]
    simp [vEps, atomMass]
  have hU : ∫ x : RayP, vEps Fr ε N0 (Sum.inr (Sum.inl x))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) = Fr.Aco ^ ε / betaE ε := by
    have := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r => Fr.Aco ^ ε * Real.exp (-(betaE ε) * r))
    simp only [vEps, Sum.elim_inr, Sum.elim_inl, vEps_ray hC]
    rw [this, hray]
  have hL : ∫ x : RayP, vEps Fr ε N0 (Sum.inr (Sum.inr x))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) = Fr.Aco ^ ε / betaE ε := by
    have := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r => Fr.Aco ^ ε * Real.exp (-(betaE ε) * r))
    simp only [vEps, Sum.elim_inr, Sum.elim_inl, vEps_ray hC]
    rw [this, hray]
  rw [hA, hU, hL]; ring

/-- The exponent `T` of Lemma A. -/
noncomputable def Texp {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (Fr : Frame) (F : Cert.CertCore K ρ ε c m) (D m0 : ℝ) (h k : ℕ) : ℝ :=
  -(h : ℝ) ^ 2 * D + h * ((h : ℝ) - k) * F.ccert
    + Rerr h (Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ (max (Real.log Fr.Aco) 0) m0

/-- **Pointwise bound for the Andréief integrand.** -/
theorem integrand_le {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOK) (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {h k : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h)
    (s : Fin k → Fin h) (hs : Function.Injective s) (z : Fin k → Fr.XT N0) :
    (∏ l, ‖Fr.wT N0 (z l)‖) *
        ‖cexpr (fun l => Fr.ptT N0 (z l)) (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2
      ≤ Real.exp (Texp Fr F D m0 h k) * ∏ l, vEps Fr ε N0 (z l) := by
  classical
  have hC := hFr.contour
  set x : Fin k → ℂ := fun l => Fr.ptT N0 (z l) with hx
  set y : Fin k → ℂ := fun i => (((s i : Fin h) : ℕ) : ℂ) with hy
  have hv0 : 0 ≤ ∏ l, vEps Fr ε N0 (z l) :=
    Finset.prod_nonneg (fun l _ => vEps_nonneg hC ε N0 _)
  by_cases hinj : Function.Injective x
  · have hA := lemmaA hFr F hD hm0 hh hN0 hW s hs x hinj
      (fun l => ptT_atom_or_ray N0 (z l)) (fun l => ptT_re hC hm0xs hm0μ N0 (z l))
      (fun l => qEps Fr ε N0 (z l)) (max (Real.log Fr.Aco) 0)
      (le_max_right _ _) (fun l => log_qEps_le hC F.hε1 N0 (z l))
    have hq0 : ∀ l, 0 < qEps Fr ε N0 (z l) := fun l => qEps_pos hC ε N0 _
    have hC0 : 0 ≤ ‖cexpr x y‖ ^ 2 := by positivity
    have step1 : (∏ l, ‖Fr.wT N0 (z l)‖) ≤ ∏ l, (vEps Fr ε N0 (z l) * qEps Fr ε N0 (z l)) :=
      Finset.prod_le_prod₀ (fun l _ => norm_nonneg _)
        (fun l _ => norm_wT_le_vq hC hFr.delta ε N0 _)
    have step2 : (∏ l, qEps Fr ε N0 (z l)) * ‖cexpr x y‖ ^ 2 ≤ Real.exp (Texp Fr F D m0 h k) := by
      by_cases h0 : ‖cexpr x y‖ ^ 2 = 0
      · rw [h0, mul_zero]; exact (Real.exp_pos _).le
      · have hpos : 0 < ‖cexpr x y‖ ^ 2 := lt_of_le_of_ne hC0 (Ne.symm h0)
        have hP : 0 < (∏ l, qEps Fr ε N0 (z l)) := Finset.prod_pos (fun l _ => hq0 l)
        rw [← Real.log_le_iff_le_exp (mul_pos hP hpos), Real.log_mul hP.ne' hpos.ne',
          Real.log_prod (fun l _ => (hq0 l).ne')]
        exact hA
    calc (∏ l, ‖Fr.wT N0 (z l)‖) * ‖cexpr x y‖ ^ 2
        ≤ (∏ l, (vEps Fr ε N0 (z l) * qEps Fr ε N0 (z l))) * ‖cexpr x y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right step1 hC0
      _ = (∏ l, vEps Fr ε N0 (z l)) * ((∏ l, qEps Fr ε N0 (z l)) * ‖cexpr x y‖ ^ 2) := by
          rw [Finset.prod_mul_distrib]; ring
      _ ≤ (∏ l, vEps Fr ε N0 (z l)) * Real.exp (Texp Fr F D m0 h k) :=
          mul_le_mul_of_nonneg_left step2 hv0
      _ = _ := by ring
  · -- a coincidence among the free points: the Cauchy expression vanishes
    have hz0 : cexpr x y = 0 := by
      unfold Function.Injective at hinj
      push Not at hinj
      obtain ⟨a, b, hab, hne⟩ := hinj
      have key : ∀ l l' : Fin k, l < l' → x l = x l' → cexpr x y = 0 := by
        intro l l' hlt hxe
        unfold cexpr
        rw [div_eq_zero_iff]; left
        refine Finset.prod_eq_zero (Finset.mem_univ l) (Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) ?_)
        rw [hxe, sub_self, zero_mul]
      rcases lt_trichotomy a b with h1 | h1 | h1
      · exact key a b h1 hab
      · exact absurd h1 hne
      · exact key b a h1 hab.symm
    rw [hz0]; simp
    positivity

/-- **The integrated bound for `norm · T[S]`.** -/
theorem det_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOK) (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {h k : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h)
    (s : Fin k → Fin h) (hs : Function.Injective s) :
    ‖(Matrix.of fun i j : Fin k =>
        (((Fr.norm : ℝ) * Fr.Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * (Real.exp (Texp Fr F D m0 h k)
          * (Fr.atomMass N0 + 2 * (Fr.Aco ^ ε / betaE ε)) ^ k) := by
  classical
  have hC := hFr.contour
  have hs' : Function.Injective (fun i => ((s i : Fin h) : ℕ)) :=
    fun a b hab => hs (Fin.ext hab)
  have hb := Fr.tent_andreief_bound hC hFr.delta N0 k (fun i => ((s i : Fin h) : ℕ)) hs'
  have hε := F.hε0
  have hmeas := integrable_vEps hC hε N0
  have hGi : Integrable (fun z : Fin k → Fr.XT N0 => Real.exp (Texp Fr F D m0 h k) * ∏ l, vEps Fr ε N0 (z l))
      (Measure.pi fun _ => Fr.muT N0) :=
    (Integrable.fintype_prod (f := fun (_ : Fin k) (x : Fr.XT N0) => vEps Fr ε N0 x)
      (μ := fun _ => Fr.muT N0) (fun _ => hmeas)).const_mul _
  have hle : ∫ z : Fin k → Fr.XT N0, (∏ l, ‖Fr.wT N0 (z l)‖) *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((Fr.ptT N0 (z l') - Fr.ptT N0 (z l)) * ((((s l : Fin h) : ℕ) : ℂ) - (((s l' : Fin h) : ℕ) : ℂ))))
              / ∏ l, ∏ i, (Fr.ptT N0 (z l) - (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2 ∂(Measure.pi fun _ => Fr.muT N0)
      ≤ ∫ z : Fin k → Fr.XT N0, Real.exp (Texp Fr F D m0 h k) * ∏ l, vEps Fr ε N0 (z l)
          ∂(Measure.pi fun _ => Fr.muT N0) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hGi
      (Filter.Eventually.of_forall (fun z => ?_))
    · positivity
    · exact integrand_le hFr F hD hm0 hm0xs hm0μ hh hN0 hW s hs z
  have hG : ∫ z : Fin k → Fr.XT N0, Real.exp (Texp Fr F D m0 h k) * ∏ l, vEps Fr ε N0 (z l)
        ∂(Measure.pi fun _ => Fr.muT N0)
      = Real.exp (Texp Fr F D m0 h k) * (Fr.atomMass N0 + 2 * (Fr.Aco ^ ε / betaE ε)) ^ k := by
    rw [integral_const_mul, integral_fintype_prod_eq_pow (fun x => vEps Fr ε N0 x),
      integral_vEps hC hε]
    simp
  calc _ ≤ _ := hb
    _ ≤ (1 / (k.factorial : ℝ)) * (Real.exp (Texp Fr F D m0 h k)
          * (Fr.atomMass N0 + 2 * (Fr.Aco ^ ε / betaE ε)) ^ k) := by
        rw [← hG]
        exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The explicit error term `E(h) = R(h) + h log(…)`; it is `O(h log h)`. -/
noncomputable def Eerr {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (Fr : Frame) (F : Cert.CertCore K ρ ε c m) (m0 : ℝ) (h : ℕ) : ℝ :=
  Rerr h (Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ (max (Real.log Fr.Aco) 0) m0
    + h * Real.log (Fr.Wabs * F.r0 * h
        + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (Fr.Aco ^ ε / betaE ε) + 1))

/-- **Theorem N** (node-removal bound for every principal minor of `T`), general frame.
`|det T[S]| ≤ exp(-h² D + h (h - k) c_cert + E(h))`. -/
theorem theoremN {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOK') (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {h k : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h)
    (s : Fin k → Fin h) (hs : Function.Injective s) :
    |(Matrix.of fun i j : Fin k => Fr.Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ))).det|
      ≤ Real.exp (-(h : ℝ) ^ 2 * D + h * ((h : ℝ) - k) * F.ccert + Eerr Fr F m0 h) := by
  have hC := hFr.contour
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hkh : k ≤ h := by simpa using Fintype.card_le_of_injective s hs
  have hkh' : (k : ℝ) ≤ h := by exact_mod_cast hkh
  set M : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun i j => Fr.Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) with hM
  have hnorm : (1 : ℝ) ≤ Fr.norm := by exact_mod_cast hFr.norm_ge
  have hcast : (Matrix.of fun i j : Fin k =>
        (((Fr.norm : ℝ) * Fr.Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ))
      = Complex.ofRealHom.mapMatrix ((Fr.norm : ℝ) • M) := by
    ext i j; simp [hM]
  have hdet : ‖(Matrix.of fun i j : Fin k =>
        (((Fr.norm : ℝ) * Fr.Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ)).det‖
      = (Fr.norm : ℝ) ^ k * |M.det| := by
    rw [hcast, ← RingHom.map_det, Matrix.det_smul]
    simp [Complex.norm_real, abs_mul, abs_of_pos (show (0 : ℝ) < Fr.norm by linarith)]
  have hb := det_bound hFr.toDecayOK F hD hm0 hm0xs hm0μ hh hN0 hW s hs
  rw [hdet] at hb
  set cE : ℝ := 2 * (Fr.Aco ^ ε / betaE ε) with hcE
  have hAp := Aco_pos hC
  have hcE0 : 0 ≤ cE := by
    have := betaE_pos F.hε0
    positivity
  have hr0 : (0 : ℝ) ≤ F.r0 := by exact_mod_cast F.r0_pos.le
  have hN1 : (N0 : ℝ) ≤ F.r0 * h := by
    have := Nat.floor_le (show (0 : ℝ) ≤ F.r0 * h by positivity)
    rw [← hN0] at this
    push_cast at this
    have : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
    linarith
  have hW0 := Fr.Wabs_nonneg
  set M0 : ℝ := Fr.Wabs * F.r0 * h + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + cE + 1) with hM0
  have hM01 : 1 ≤ M0 := by
    have : (0 : ℝ) ≤ Fr.Wabs * F.r0 * h := by positivity
    have : (0 : ℝ) ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    linarith
  have hbase : Fr.atomMass N0 + cE ≤ M0 := by
    have h1 := Fr.atomMass_le N0
    have h2 : ((N0 : ℝ) + ⌈(Fr.xs : ℝ)⌉₊) * Fr.Wabs ≤ Fr.Wabs * F.r0 * h + Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by
      nlinarith
    rw [hM0]; linarith
  have hbase0 : 0 ≤ Fr.atomMass N0 + cE := by
    have : 0 ≤ Fr.atomMass N0 := by
      unfold atomMass
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hpow : (Fr.atomMass N0 + cE) ^ k ≤ M0 ^ h :=
    (pow_le_pow_left₀ hbase0 hbase k).trans (pow_le_pow_right₀ hM01 hkh)
  have hMh : M0 ^ h = Real.exp (h * Real.log M0) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]; simp
  have hfac : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have hE0 := Real.exp_pos (Texp Fr F D m0 h k)
  have step : (Fr.norm : ℝ) ^ k * |M.det| ≤ Real.exp (Texp Fr F D m0 h k) * M0 ^ h := by
    refine hb.trans ?_
    calc (1 / (k.factorial : ℝ)) * (Real.exp (Texp Fr F D m0 h k) * (Fr.atomMass N0 + cE) ^ k)
        ≤ 1 * (Real.exp (Texp Fr F D m0 h k) * (Fr.atomMass N0 + cE) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by linarith)]; exact hfac
      _ ≤ Real.exp (Texp Fr F D m0 h k) * M0 ^ h := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hE0.le
  have : |M.det| ≤ Real.exp (Texp Fr F D m0 h k) * M0 ^ h := by
    have h1 : |M.det| ≤ (Fr.norm : ℝ) ^ k * |M.det| := by
      nlinarith [abs_nonneg M.det, one_le_pow₀ hnorm (n := k)]
    exact h1.trans step
  refine this.trans (le_of_eq ?_)
  rw [hMh, ← Real.exp_add]
  congr 1
  unfold Texp Eerr
  rw [hM0]
  ring

end Frame
end CatalanCore
