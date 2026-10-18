import CatalanLambda.Decay.ThmNLemmaA
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import CatalanLambda.Decay.AndreiefTentR

/-!
# Theorem N_ρ: the combined space, the weights, and the integration step
-/

open Finset MeasureTheory Set CatalanLambda.Decay

namespace CatalanLambda.Decay.R

/-- Classification of the points of the combined space. -/
theorem ptT_atom_or_ray (N0 : ℕ) (x : XT N0) :
    IsAtom N0 (ptT N0 x) ∨ IsRay N0 (ptT N0 x) := by
  rcases x with ⟨m, b⟩ | r | r
  · left
    cases b
    · left; exact ⟨m, m.2, by simp [ptT, atomPos1]⟩
    · right; exact ⟨m, m.2, by simp [ptT, atomPos2]⟩
  · right
    exact ⟨r.1, r.2, phiR, Or.inl rfl, by simp [ptT]⟩
  · right
    exact ⟨r.1, r.2, -phiR, Or.inr rfl, by simp [ptT]⟩

lemma cos_phiR_neg : Real.cos phiR < 0 := by
  rw [cos_phiR]; have : 0 < Real.sqrt 10 := by positivity
  have : 0 < 1 / Real.sqrt 10 := by positivity
  linarith

theorem ptT_re (N0 : ℕ) (x : XT N0) : 3 / 8 ≤ -(ptT N0 x).re := by
  rcases x with ⟨m, b⟩ | r | r
  · have hm : (0 : ℝ) ≤ (m : ℕ) := Nat.cast_nonneg _
    cases b <;> simp [ptT] <;> linarith
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_re]
    have := cos_phiR_neg
    have hr : 0 < r.1 := r.2
    unfold xstar
    have : (0 : ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg _
    nlinarith
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_re, Real.cos_neg]
    have := cos_phiR_neg
    have hr : 0 < r.1 := r.2
    unfold xstar
    have : (0 : ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg _
    nlinarith

theorem ptT_im_abs (N0 : ℕ) (x : XT N0) :
    |(ptT N0 x).im| = Sum.elim (fun _ => (0 : ℝ))
      (Sum.elim (fun r => r.1 * Real.sin phiR) (fun r => r.1 * Real.sin phiR)) x := by
  have hs : 0 < Real.sin phiR := sin_phiR_pos
  rcases x with ⟨m, b⟩ | r | r
  · cases b <;> simp [ptT]
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_im, abs_of_pos (mul_pos r.2 hs)]
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_im, Real.sin_neg, mul_neg, abs_neg, abs_of_pos (mul_pos r.2 hs)]

/-- The constant of the ray bound for `E`. -/
noncomputable def C0 : ℝ := 16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2

/-- Amplitude of the bound for `‖w‖ = |E|/2π` on the rays. -/
noncomputable def Aco : ℝ := C0 / (2 * Real.pi)

lemma Aco_pos : 0 < Aco := by
  unfold Aco C0; positivity

/-- The decay factor `2π r sin φ` along a ray. -/
noncomputable def bray (r : ℝ) : ℝ := 2 * Real.pi * (r * Real.sin phiR)

/-- Integrable majorant `v_ε` (atoms: 1; rays: `A^ε e^{-ε b(r)}`). -/
noncomputable def vEps (ε : ℝ) (N0 : ℕ) : XT N0 → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun r => Aco ^ ε * Real.exp (-(ε * bray r.1)))
    (fun r => Aco ^ ε * Real.exp (-(ε * bray r.1))))

/-- Remaining weight `q_ε` (atoms: 1; rays: `A^{1-ε} e^{-(1-ε) b(r)}`). -/
noncomputable def qEps (ε : ℝ) (N0 : ℕ) : XT N0 → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun r => Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r.1)))
    (fun r => Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r.1))))

lemma vEps_nonneg (ε : ℝ) (N0 : ℕ) (x : XT N0) : 0 ≤ vEps ε N0 x := by
  have := Aco_pos
  rcases x with ⟨m, b⟩ | r | r <;> simp [vEps] <;> positivity

lemma qEps_pos (ε : ℝ) (N0 : ℕ) (x : XT N0) : 0 < qEps ε N0 x := by
  have := Aco_pos
  rcases x with ⟨m, b⟩ | r | r <;> simp [qEps] <;> positivity

lemma bray_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ bray r := by
  unfold bray
  have := sin_phiR_pos
  positivity

lemma norm_wT_le_vq (ε : ℝ) (N0 : ℕ) (x : XT N0) :
    ‖wT N0 x‖ ≤ vEps ε N0 x * qEps ε N0 x := by
  have hA := Aco_pos
  have key : ∀ r : ℝ, 0 ≤ r → ∀ E : ℝ, E ≤ C0 * Real.exp (-bray r) →
      E / (2 * Real.pi) ≤ Aco ^ ε * Real.exp (-(ε * bray r)) *
        (Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r))) := by
    intro r _ E hE
    have e : Aco ^ ε * Real.exp (-(ε * bray r)) * (Aco ^ (1 - ε) * Real.exp (-((1 - ε) * bray r)))
        = Aco * Real.exp (-bray r) := by
      have h1 : Aco ^ ε * Aco ^ (1 - ε) = Aco := by
        rw [← Real.rpow_add hA]; simp
      have h2 : Real.exp (-(ε * bray r)) * Real.exp (-((1 - ε) * bray r)) = Real.exp (-bray r) := by
        rw [← Real.exp_add]; congr 1; ring
      calc _ = (Aco ^ ε * Aco ^ (1 - ε)) * (Real.exp (-(ε * bray r)) * Real.exp (-((1 - ε) * bray r))) := by ring
        _ = _ := by rw [h1, h2]
    rw [e, Aco, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  rcases x with ⟨m, b⟩ | r | r
  · rw [norm_wT_atom]; simp [vEps, qEps]
  · rw [norm_wT_up]
    simp only [vEps, qEps, Sum.elim_inr, Sum.elim_inl]
    apply key _ r.2.le
    have := EC_ray_bound_R N0 (θ := phiR) (Or.inl rfl) r.2.le
    unfold C0 bray; exact this
  · rw [norm_wT_low]
    simp only [vEps, qEps, Sum.elim_inr, Sum.elim_inl]
    apply key _ r.2.le
    have := EC_ray_bound_R N0 (θ := -phiR) (Or.inr rfl) r.2.le
    unfold C0 bray; exact this

/-- The logarithmic field bound for `q_ε`. -/
lemma log_qEps_le {ε : ℝ} (hε1 : ε < 1) (N0 : ℕ) (x : XT N0) :
    Real.log (qEps ε N0 x) ≤ (1 - ε) * (max (Real.log Aco) 0 - 2 * Real.pi * |(ptT N0 x).im|) := by
  have hA := Aco_pos
  rw [ptT_im_abs]
  have h1 : 0 < 1 - ε := by linarith
  have hC := le_max_left (Real.log Aco) 0
  have hC0 := le_max_right (Real.log Aco) 0
  rcases x with ⟨m, b⟩ | r | r
  · simp only [qEps, Sum.elim_inl, Real.log_one, mul_zero, sub_zero]
    exact mul_nonneg h1.le hC0
  · simp only [qEps, ptT, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    unfold bray
    nlinarith
  · simp only [qEps, ptT, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    unfold bray
    nlinarith

section sumgen
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma integrable_sumM_iff_gen (μ : Measure α) (ν : Measure β) (F : α ⊕ β → E) :
    Integrable F (sumM μ ν) ↔
      Integrable (fun a => F (Sum.inl a)) μ ∧ Integrable (fun b => F (Sum.inr b)) ν := by
  unfold sumM
  rw [integrable_add_measure, (meInl α β).integrable_map_iff,
    (meInr α β).integrable_map_iff]
  rfl

lemma integral_sumM_gen (μ : Measure α) (ν : Measure β) (F : α ⊕ β → E)
    (h : Integrable F (sumM μ ν)) :
    ∫ x, F x ∂(sumM μ ν) = ∫ a, F (Sum.inl a) ∂μ + ∫ b, F (Sum.inr b) ∂ν := by
  unfold sumM at h ⊢
  rw [integrable_add_measure] at h
  rw [integral_add_measure h.1 h.2, (meInl α β).integral_map,
    (meInr α β).integral_map]

end sumgen

lemma integrable_comap_Ioi_real (g : ℝ → ℝ) :
    Integrable (fun r : RayP => g r.1) (Measure.comap Subtype.val (volume : Measure ℝ))
      ↔ IntegrableOn g (Ioi 0) := by
  have := (MeasurableEmbedding.subtype_coe (measurableSet_Ioi (a := (0:ℝ)))).integrable_map_iff
    (μ := Measure.comap Subtype.val (volume : Measure ℝ)) (g := g)
  rw [map_comap_subtype_coe measurableSet_Ioi] at this
  exact this.symm

/-- The decay rate of `v_ε` along a ray. -/
noncomputable def betaE (ε : ℝ) : ℝ := ε * (2 * Real.pi * Real.sin phiR)

lemma betaE_pos {ε : ℝ} (hε : 0 < ε) : 0 < betaE ε := by
  unfold betaE; have := sin_phiR_pos; positivity

lemma vEps_ray (ε : ℝ) (r : ℝ) :
    Aco ^ ε * Real.exp (-(ε * bray r)) = Aco ^ ε * Real.exp (-(betaE ε) * r) := by
  unfold bray betaE; congr 2; ring

lemma integrable_vEps {ε : ℝ} (hε : 0 < ε) (N0 : ℕ) : Integrable (vEps ε N0) (muT N0) := by
  unfold muT
  rw [integrable_sumM_iff_gen, integrable_sumM_iff_gen]
  have hb := betaE_pos hε
  have hI : IntegrableOn (fun r : ℝ => Aco ^ ε * Real.exp (-(betaE ε) * r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(betaE ε)) (by linarith) 0).const_mul _
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · refine (integrable_comap_Ioi_real (fun r => Aco ^ ε * Real.exp (-(betaE ε) * r))).2 hI |>.congr ?_
    exact Filter.Eventually.of_forall (fun r => by simp [vEps, vEps_ray])
  · refine (integrable_comap_Ioi_real (fun r => Aco ^ ε * Real.exp (-(betaE ε) * r))).2 hI |>.congr ?_
    exact Filter.Eventually.of_forall (fun r => by simp [vEps, vEps_ray])

/-- The total mass of `v_ε`. -/
theorem integral_vEps {ε : ℝ} (hε : 0 < ε) (N0 : ℕ) :
    ∫ x, vEps ε N0 x ∂(muT N0) = 2 * N0 + 2 * (Aco ^ ε / betaE ε) := by
  have hb := betaE_pos hε
  have hint := integrable_vEps hε N0
  have hI : IntegrableOn (fun r : ℝ => Aco ^ ε * Real.exp (-(betaE ε) * r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -(betaE ε)) (by linarith) 0).const_mul _
  have hray : ∫ r in Ioi (0 : ℝ), Aco ^ ε * Real.exp (-(betaE ε) * r) = Aco ^ ε / betaE ε := by
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -(betaE ε)) (by linarith) 0]
    simp; field_simp
  unfold muT at hint ⊢
  rw [integral_sumM_gen _ _ _ hint]
  have hint2 := ((integrable_sumM_iff_gen _ _ _).1 hint).2
  rw [integral_sumM_gen _ _ _ hint2]
  have hA : ∫ p : Fin N0 × Bool, vEps ε N0 (Sum.inl p) ∂(Measure.count : Measure (Fin N0 × Bool))
      = 2 * N0 := by
    rw [integral_count]
    simp [vEps]; ring
  have hU : ∫ x : RayP, vEps ε N0 (Sum.inr (Sum.inl x))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) = Aco ^ ε / betaE ε := by
    have := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r => Aco ^ ε * Real.exp (-(betaE ε) * r))
    simp only [vEps, Sum.elim_inr, Sum.elim_inl, vEps_ray]
    rw [this, hray]
  have hL : ∫ x : RayP, vEps ε N0 (Sum.inr (Sum.inr x))
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) = Aco ^ ε / betaE ε := by
    have := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r => Aco ^ ε * Real.exp (-(betaE ε) * r))
    simp only [vEps, Sum.elim_inr, Sum.elim_inl, vEps_ray]
    rw [this, hray]
  rw [hA, hU, hL]; ring

/-- The exponent `T` of Lemma A_ρ. -/
noncomputable def Texp {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (h k : ℕ) : ℝ :=
  -(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert
    + Rerr h (∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ (max (Real.log Aco) 0)

/-- **Pointwise bound for the Andréief integrand.** -/
theorem integrand_le {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h k : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h)
    (s : Fin k → Fin h) (hs : Function.Injective s) {N0 : ℕ} (hN0 : N0 = ⌊(F.r0 : ℝ) * h⌋₊)
    (z : Fin k → XT N0) :
    (∏ l, ‖wT N0 (z l)‖) *
        ‖cexpr (fun l => ptT N0 (z l)) (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2
      ≤ Real.exp (Texp F h k) * ∏ l, vEps ε N0 (z l) := by
  classical
  set x : Fin k → ℂ := fun l => ptT N0 (z l) with hx
  set y : Fin k → ℂ := fun i => (((s i : Fin h) : ℕ) : ℂ) with hy
  have hv0 : 0 ≤ ∏ l, vEps ε N0 (z l) := Finset.prod_nonneg (fun l _ => vEps_nonneg ε N0 _)
  by_cases hinj : Function.Injective x
  · have hA := lemmaA F hh hW s hs x hinj (fun l => by subst hN0; exact ptT_atom_or_ray _ (z l))
      (fun l => ptT_re N0 (z l)) (fun l => qEps ε N0 (z l)) (max (Real.log Aco) 0)
      (le_max_right _ _) (fun l => log_qEps_le F.hε1 N0 (z l))
    have hq0 : ∀ l, 0 < qEps ε N0 (z l) := fun l => qEps_pos ε N0 _
    have hC0 : 0 ≤ ‖cexpr x y‖ ^ 2 := by positivity
    have step1 : (∏ l, ‖wT N0 (z l)‖) ≤ ∏ l, (vEps ε N0 (z l) * qEps ε N0 (z l)) :=
      Finset.prod_le_prod₀ (fun l _ => norm_nonneg _) (fun l _ => norm_wT_le_vq ε N0 _)
    have step2 : (∏ l, qEps ε N0 (z l)) * ‖cexpr x y‖ ^ 2 ≤ Real.exp (Texp F h k) := by
      by_cases h0 : ‖cexpr x y‖ ^ 2 = 0
      · rw [h0, mul_zero]; exact (Real.exp_pos _).le
      · have hpos : 0 < ‖cexpr x y‖ ^ 2 := lt_of_le_of_ne hC0 (Ne.symm h0)
        have hP : 0 < (∏ l, qEps ε N0 (z l)) := Finset.prod_pos (fun l _ => hq0 l)
        rw [← Real.log_le_iff_le_exp (mul_pos hP hpos), Real.log_mul hP.ne' hpos.ne',
          Real.log_prod (fun l _ => (hq0 l).ne')]
        exact hA
    calc (∏ l, ‖wT N0 (z l)‖) * ‖cexpr x y‖ ^ 2
        ≤ (∏ l, (vEps ε N0 (z l) * qEps ε N0 (z l))) * ‖cexpr x y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right step1 hC0
      _ = (∏ l, vEps ε N0 (z l)) * ((∏ l, qEps ε N0 (z l)) * ‖cexpr x y‖ ^ 2) := by
          rw [Finset.prod_mul_distrib]; ring
      _ ≤ (∏ l, vEps ε N0 (z l)) * Real.exp (Texp F h k) :=
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

/-- **The integrated bound for `16 T[S]`.** -/
theorem det16_bound {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h k : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h)
    (s : Fin k → Fin h) (hs : Function.Injective s) :
    ‖(Matrix.of fun i j : Fin k => ((16 * Tent (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * (Real.exp (Texp F h k)
          * (2 * (⌊(F.r0 : ℝ) * h⌋₊ : ℕ) + 2 * (Aco ^ ε / betaE ε)) ^ k) := by
  classical
  set N0 := ⌊(F.r0 : ℝ) * h⌋₊ with hN0
  have hs' : Function.Injective (fun i => ((s i : Fin h) : ℕ)) :=
    fun a b hab => hs (Fin.ext hab)
  have hb := tent_andreief_bound N0 k (fun i => ((s i : Fin h) : ℕ)) hs'
  have hε := F.hε0
  have hmeas := integrable_vEps hε N0
  have hGi : Integrable (fun z : Fin k → XT N0 => Real.exp (Texp F h k) * ∏ l, vEps ε N0 (z l))
      (Measure.pi fun _ => muT N0) :=
    (Integrable.fintype_prod (f := fun (_ : Fin k) (x : XT N0) => vEps ε N0 x)
      (μ := fun _ => muT N0) (fun _ => hmeas)).const_mul _
  have hle : ∫ z : Fin k → XT N0, (∏ l, ‖wT N0 (z l)‖) *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((ptT N0 (z l') - ptT N0 (z l)) * ((((s l : Fin h) : ℕ) : ℂ) - (((s l' : Fin h) : ℕ) : ℂ))))
              / ∏ l, ∏ i, (ptT N0 (z l) - (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2 ∂(Measure.pi fun _ => muT N0)
      ≤ ∫ z : Fin k → XT N0, Real.exp (Texp F h k) * ∏ l, vEps ε N0 (z l) ∂(Measure.pi fun _ => muT N0) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hGi
      (Filter.Eventually.of_forall (fun z => ?_))
    · positivity
    · exact integrand_le F hh hW s hs hN0 z
  have hG : ∫ z : Fin k → XT N0, Real.exp (Texp F h k) * ∏ l, vEps ε N0 (z l)
        ∂(Measure.pi fun _ => muT N0)
      = Real.exp (Texp F h k) * (2 * N0 + 2 * (Aco ^ ε / betaE ε)) ^ k := by
    rw [integral_const_mul, integral_fintype_prod_eq_pow (fun x => vEps ε N0 x), integral_vEps hε]
    simp
  calc _ ≤ _ := hb
    _ ≤ (1 / (k.factorial : ℝ)) * (Real.exp (Texp F h k) * (2 * N0 + 2 * (Aco ^ ε / betaE ε)) ^ k) := by
        rw [← hG]
        exact mul_le_mul_of_nonneg_left hle (by positivity)

end CatalanLambda.Decay.R
