module

public import CatalanArchive.CatalanLambda.Mirror.LemmaA
public import CatalanLambda.Decay.ThmNInteg

@[expose] public section

/-!
# Mirror constant: the integration step (`det16_boundB`)
-/

open Finset MeasureTheory Set CatalanLambda.Decay

namespace CatalanLambda.Mirror

open CatalanLambda.Decay.R (RayP XT muT vEps qEps Aco Aco_pos C0 bray vEps_nonneg qEps_pos
  bray_nonneg betaE integrable_vEps integral_vEps cos_phiR_neg sin_phiR_pos)

/-- Classification of the points of the combined space. -/
theorem ptTB_atom_or_ray (N0 : ℕ) (x : XT N0) :
    IsAtomB N0 (ptTB N0 x) ∨ IsRayB N0 (ptTB N0 x) := by
  rcases x with ⟨m, b⟩ | r | r
  · left
    cases b
    · left; exact ⟨m, m.2, by simp [ptTB, atomPos1B]⟩
    · right; exact ⟨m, m.2, by simp [ptTB, atomPos2B]⟩
  · right
    exact ⟨r.1, r.2, phiR, Or.inl rfl, by simp [ptTB]⟩
  · right
    exact ⟨r.1, r.2, -phiR, Or.inr rfl, by simp [ptTB]⟩


theorem ptTB_re (N0 : ℕ) (hN : 1 ≤ N0) (x : XT N0) : 1 / 4 ≤ -(ptTB N0 x).re := by
  rcases x with ⟨m, b⟩ | r | r
  · have hm : (0 : ℝ) ≤ (m : ℕ) := Nat.cast_nonneg _
    cases b <;> simp [ptTB] <;> linarith
  · simp only [ptTB, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_re]
    have := cos_phiR_neg
    have hr : 0 < r.1 := r.2
    unfold xstarB
    have : (1 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hN
    nlinarith
  · simp only [ptTB, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_re, Real.cos_neg]
    have := cos_phiR_neg
    have hr : 0 < r.1 := r.2
    unfold xstarB
    have : (1 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hN
    nlinarith

theorem ptTB_im_abs (N0 : ℕ) (x : XT N0) :
    |(ptTB N0 x).im| = Sum.elim (fun _ => (0 : ℝ))
      (Sum.elim (fun r => r.1 * Real.sin phiR) (fun r => r.1 * Real.sin phiR)) x := by
  have hs : 0 < Real.sin phiR := sin_phiR_pos
  rcases x with ⟨m, b⟩ | r | r
  · cases b <;> simp [ptTB]
  · simp only [ptTB, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_im, abs_of_pos (mul_pos r.2 hs)]
  · simp only [ptTB, Sum.elim_inr, Sum.elim_inl]
    rw [rayPt_im, Real.sin_neg, mul_neg, abs_neg, abs_of_pos (mul_pos r.2 hs)]


lemma norm_wT_le_vq (ε : ℝ) (N0 : ℕ) (x : XT N0) :
    ‖wTB N0 x‖ ≤ vEps ε N0 x * qEps ε N0 x := by
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
  · simp only [vEps, qEps, Sum.elim_inl, mul_one]
    exact norm_wTB_atom N0 _
  · rw [norm_wTB_up]
    simp only [vEps, qEps, Sum.elim_inr, Sum.elim_inl]
    apply key _ r.2.le
    have := ECB_ray_bound_R N0 (θ := phiR) (Or.inl rfl) r.2.le
    unfold C0 bray; exact this
  · rw [norm_wTB_low]
    simp only [vEps, qEps, Sum.elim_inr, Sum.elim_inl]
    apply key _ r.2.le
    have := ECB_ray_bound_R N0 (θ := -phiR) (Or.inr rfl) r.2.le
    unfold C0 bray; exact this

/-- The logarithmic field bound for `q_ε`. -/
lemma log_qEps_leB {ε : ℝ} (hε1 : ε < 1) (N0 : ℕ) (x : XT N0) :
    Real.log (qEps ε N0 x) ≤ (1 - ε) * (max (Real.log Aco) 0 - 2 * Real.pi * |(ptTB N0 x).im|) := by
  have hA := Aco_pos
  rw [ptTB_im_abs]
  have h1 : 0 < 1 - ε := by linarith
  have hC := le_max_left (Real.log Aco) 0
  have hC0 := le_max_right (Real.log Aco) 0
  rcases x with ⟨m, b⟩ | r | r
  · simp only [qEps, Sum.elim_inl, Real.log_one, mul_zero, sub_zero]
    exact mul_nonneg h1.le hC0
  · simp only [qEps, ptTB, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    unfold bray
    nlinarith
  · simp only [qEps, ptTB, Sum.elim_inr, Sum.elim_inl]
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_rpow hA, Real.log_exp]
    unfold bray
    nlinarith


/-- The exponent `T` of Lemma A_ρ. -/
noncomputable def TexpB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) (h k : ℕ) : ℝ :=
  -(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert
    + RerrB h (∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ (max (Real.log Aco) 0)

/-- **Pointwise bound for the Andréief integrand.** -/
theorem integrand_leB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h k : ℕ} (hh : 0 < h) (hW : 11 / (8 * (F.W : ℝ)) ≤ h)
    (s : Fin k → Fin h) (hs : Function.Injective s) {N0 : ℕ} (hN0 : N0 = ⌊(F.r0 : ℝ) * h⌋₊)
    (hN : 1 ≤ N0) (z : Fin k → XT N0) :
    (∏ l, ‖wTB N0 (z l)‖) *
        ‖cexpr (fun l => ptTB N0 (z l)) (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2
      ≤ Real.exp (TexpB F h k) * ∏ l, vEps ε N0 (z l) := by
  classical
  set x : Fin k → ℂ := fun l => ptTB N0 (z l) with hx
  set y : Fin k → ℂ := fun i => (((s i : Fin h) : ℕ) : ℂ) with hy
  have hv0 : 0 ≤ ∏ l, vEps ε N0 (z l) := Finset.prod_nonneg (fun l _ => vEps_nonneg ε N0 _)
  by_cases hinj : Function.Injective x
  · have hA := lemmaAB F hh hW s hs x hinj (fun l => by subst hN0; exact ptTB_atom_or_ray _ (z l))
      (fun l => ptTB_re N0 hN (z l)) (fun l => qEps ε N0 (z l)) (max (Real.log Aco) 0)
      (le_max_right _ _) (fun l => log_qEps_leB F.hε1 N0 (z l))
    have hq0 : ∀ l, 0 < qEps ε N0 (z l) := fun l => qEps_pos ε N0 _
    have hC0 : 0 ≤ ‖cexpr x y‖ ^ 2 := by positivity
    have step1 : (∏ l, ‖wTB N0 (z l)‖) ≤ ∏ l, (vEps ε N0 (z l) * qEps ε N0 (z l)) :=
      Finset.prod_le_prod₀ (fun l _ => norm_nonneg _) (fun l _ => norm_wT_le_vq ε N0 _)
    have step2 : (∏ l, qEps ε N0 (z l)) * ‖cexpr x y‖ ^ 2 ≤ Real.exp (TexpB F h k) := by
      by_cases h0 : ‖cexpr x y‖ ^ 2 = 0
      · rw [h0, mul_zero]; exact (Real.exp_pos _).le
      · have hpos : 0 < ‖cexpr x y‖ ^ 2 := lt_of_le_of_ne hC0 (Ne.symm h0)
        have hP : 0 < (∏ l, qEps ε N0 (z l)) := Finset.prod_pos (fun l _ => hq0 l)
        rw [← Real.log_le_iff_le_exp (mul_pos hP hpos), Real.log_mul hP.ne' hpos.ne',
          Real.log_prod (fun l _ => (hq0 l).ne')]
        exact hA
    calc (∏ l, ‖wTB N0 (z l)‖) * ‖cexpr x y‖ ^ 2
        ≤ (∏ l, (vEps ε N0 (z l) * qEps ε N0 (z l))) * ‖cexpr x y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right step1 hC0
      _ = (∏ l, vEps ε N0 (z l)) * ((∏ l, qEps ε N0 (z l)) * ‖cexpr x y‖ ^ 2) := by
          rw [Finset.prod_mul_distrib]; ring
      _ ≤ (∏ l, vEps ε N0 (z l)) * Real.exp (TexpB F h k) :=
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
theorem det16_boundB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {h k : ℕ} (hh : 0 < h) (hW : 11 / (8 * (F.W : ℝ)) ≤ h)
    (s : Fin k → Fin h) (hs : Function.Injective s)
    (hN1 : 1 ≤ ⌊(F.r0 : ℝ) * h⌋₊) :
    ‖(Matrix.of fun i j : Fin k => ((16 * TbarEnt (((s i : Fin h) : ℕ)) (((s j : Fin h) : ℕ)) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * (Real.exp (TexpB F h k)
          * (2 * (⌊(F.r0 : ℝ) * h⌋₊ : ℕ) + 2 * (Aco ^ ε / betaE ε)) ^ k) := by
  classical
  set N0 := ⌊(F.r0 : ℝ) * h⌋₊ with hN0
  have hs' : Function.Injective (fun i => ((s i : Fin h) : ℕ)) :=
    fun a b hab => hs (Fin.ext hab)
  have hb := tent_andreief_boundB N0 k hN1 (fun i => ((s i : Fin h) : ℕ)) hs'
  have hε := F.hε0
  have hmeas := integrable_vEps hε N0
  have hGi : Integrable (fun z : Fin k → XT N0 => Real.exp (TexpB F h k) * ∏ l, vEps ε N0 (z l))
      (Measure.pi fun _ => muT N0) :=
    (Integrable.fintype_prod (f := fun (_ : Fin k) (x : XT N0) => vEps ε N0 x)
      (μ := fun _ => muT N0) (fun _ => hmeas)).const_mul _
  have hle : ∫ z : Fin k → XT N0, (∏ l, ‖wTB N0 (z l)‖) *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((ptTB N0 (z l') - ptTB N0 (z l)) * ((((s l : Fin h) : ℕ) : ℂ) - (((s l' : Fin h) : ℕ) : ℂ))))
              / ∏ l, ∏ i, (ptTB N0 (z l) - (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2 ∂(Measure.pi fun _ => muT N0)
      ≤ ∫ z : Fin k → XT N0, Real.exp (TexpB F h k) * ∏ l, vEps ε N0 (z l) ∂(Measure.pi fun _ => muT N0) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hGi
      (Filter.Eventually.of_forall (fun z => ?_))
    · positivity
    · exact integrand_leB F hh hW s hs hN0 hN1 z
  have hG : ∫ z : Fin k → XT N0, Real.exp (TexpB F h k) * ∏ l, vEps ε N0 (z l)
        ∂(Measure.pi fun _ => muT N0)
      = Real.exp (TexpB F h k) * (2 * N0 + 2 * (Aco ^ ε / betaE ε)) ^ k := by
    rw [integral_const_mul, integral_fintype_prod_eq_pow (fun x => vEps ε N0 x), integral_vEps hε]
    simp
  calc _ ≤ _ := hb
    _ ≤ (1 / (k.factorial : ℝ)) * (Real.exp (TexpB F h k) * (2 * N0 + 2 * (Aco ^ ε / betaE ε)) ^ k) := by
        rw [← hG]
        exact mul_le_mul_of_nonneg_left hle (by positivity)



end CatalanLambda.Mirror
