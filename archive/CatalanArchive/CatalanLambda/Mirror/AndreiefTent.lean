module

public import CatalanLambda.Mirror.RayBound
public import CatalanLambda.Decay.AndreiefTentR

@[expose] public section

/-!
# Mirror constant: absolute-value Andréief bound for principal submatrices of `16 T̄`

Combined space `XT N0 = (Fin N0 × Bool) ⊕ (Ioi 0 ⊕ Ioi 0)` (reused from the `λ` case): the atoms
`-(m+1/4)` with weight `-1` and `-(m+1)` with weight `+1` (weight `0` for `m = N0 - 1`), the
upper ray and the lower ray.
-/

open MeasureTheory Complex Set CatalanLambda.Decay

namespace CatalanLambda.Mirror

open CatalanLambda.Decay.R (RayP XT muT integrable_comap_Ioi atom_pt_prod im_rayPt
  det_inv_eq_cauchy sin_phiR_pos)

/-- Upper-ray weight `-(2πi)⁻¹ E(z) e^{iφ}`. -/
noncomputable def wUpB (N0 : ℕ) (r : ℝ) : ℂ :=
  -((2 * Real.pi * I)⁻¹ * (ECB (rayPt (xstarB N0) phiR r) * exp ((phiR : ℂ) * I)))

/-- Lower-ray weight `(2πi)⁻¹ E(z) e^{-iφ}`. -/
noncomputable def wLowB (N0 : ℕ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (ECB (rayPt (xstarB N0) (-phiR) r) * exp (((-phiR : ℝ) : ℂ) * I))

/-- The complex position of a point of `XT N0`. -/
noncomputable def ptTB (N0 : ℕ) : XT N0 → ℂ :=
  Sum.elim (fun p => if p.2 then (((-(((p.1 : ℕ) : ℝ) + 1)) : ℝ) : ℂ)
      else (((-(((p.1 : ℕ) : ℝ) + 1 / 4)) : ℝ) : ℂ))
    (Sum.elim (fun r => rayPt (xstarB N0) phiR r.1) (fun r => rayPt (xstarB N0) (-phiR) r.1))

/-- The complex weight (density) on `XT N0`. -/
noncomputable def wTB (N0 : ℕ) : XT N0 → ℂ :=
  Sum.elim (fun p => if p.2 then (if (p.1 : ℕ) + 1 < N0 then (1 : ℂ) else 0) else -1)
    (Sum.elim (fun r => wUpB N0 r.1) (fun r => wLowB N0 r.1))

lemma integrable_entryB (N0 a b : ℕ) (hN : 1 ≤ N0) :
    Integrable (fun z => wTB N0 z * (ptTB N0 z - a)⁻¹ * (ptTB N0 z - b)⁻¹) (muT N0) := by
  unfold muT
  rw [integrable_sumM_iff, integrable_sumM_iff]
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · have h := Integrable.const_mul (integrableOn_E_ray_RB N0 a b hN (θ := phiR)
      (Or.inl rfl)) (-(2 * Real.pi * I)⁻¹)
    refine (integrable_comap_Ioi (fun r => wUpB N0 r * (rayPt (xstarB N0) phiR r - a)⁻¹
      * (rayPt (xstarB N0) phiR r - b)⁻¹)).2 (IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi)
    simp only [wUpB]; ring
  · have h := Integrable.const_mul (integrableOn_E_ray_RB N0 a b hN (θ := -phiR)
      (Or.inr rfl)) ((2 * Real.pi * I)⁻¹)
    refine (integrable_comap_Ioi (fun r => wLowB N0 r * (rayPt (xstarB N0) (-phiR) r - a)⁻¹
      * (rayPt (xstarB N0) (-phiR) r - b)⁻¹)).2 (IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi)
    simp only [wLowB]; ring

lemma atom_sumB (N0 a b : ℕ) (hN : 1 ≤ N0) :
    ∑ p : Fin N0 × Bool, (wTB N0 (Sum.inl p) * (ptTB N0 (Sum.inl p) - a)⁻¹
        * (ptTB N0 (Sum.inl p) - b)⁻¹)
      = -((∑ m ∈ Finset.range N0, atomTermB a b m : ℝ) : ℂ)
        - ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, wTB, ptTB, Sum.elim_inl, ite_true, Bool.false_eq_true, ite_false]
  obtain ⟨k, rfl⟩ : ∃ k, N0 = k + 1 := ⟨N0 - 1, by omega⟩
  -- the summand as a function of the natural number `m`
  have key : ∀ m : ℕ, m < k + 1 →
      ((if m + 1 < k + 1 then (1 : ℂ) else 0) * (((-((m : ℝ) + 1) : ℝ) : ℂ) - a)⁻¹
          * (((-((m : ℝ) + 1) : ℝ) : ℂ) - b)⁻¹
        + -1 * (((-((m : ℝ) + 1 / 4) : ℝ) : ℂ) - a)⁻¹
          * (((-((m : ℝ) + 1 / 4) : ℝ) : ℂ) - b)⁻¹)
      = -((atomTermB a b m : ℝ) : ℂ)
        - (if m = k then ((1 / (((a : ℝ) + (k + 1 : ℕ)) * ((b : ℝ) + (k + 1 : ℕ))) : ℝ) : ℂ) else 0) := by
    intro m hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    rw [mul_assoc, mul_assoc, atom_pt_prod a b ((m : ℝ) + 1) (by linarith),
      atom_pt_prod a b ((m : ℝ) + 1 / 4) (by linarith)]
    unfold atomTermB atomU
    by_cases hmk : m = k
    · subst hmk
      have : ¬ (m + 1 < m + 1) := lt_irrefl _
      simp only [this, if_false, if_true, zero_mul]
      push_cast
      simp only [one_div, mul_inv]
      ring
    · have : m + 1 < k + 1 := by omega
      simp only [this, if_true, hmk, if_false, one_mul]
      push_cast
      simp only [one_div, mul_inv]
      ring
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
      ((if m + 1 < k + 1 then (1 : ℂ) else 0) * (((-((m : ℝ) + 1) : ℝ) : ℂ) - a)⁻¹
          * (((-((m : ℝ) + 1) : ℝ) : ℂ) - b)⁻¹
        + -1 * (((-((m : ℝ) + 1 / 4) : ℝ) : ℂ) - a)⁻¹
          * (((-((m : ℝ) + 1 / 4) : ℝ) : ℂ) - b)⁻¹)) (k + 1)]
  rw [Finset.sum_congr rfl (fun m hm => key m (Finset.mem_range.1 hm)), Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Complex.ofReal_sum]
  simp [Finset.sum_ite_eq']

/-- **The entries of `16 T` as integrals against the combined measure.** -/
theorem entry_TB (N0 a b : ℕ) (hN : 1 ≤ N0) :
    ∫ z, wTB N0 z * (ptTB N0 z - a)⁻¹ * (ptTB N0 z - b)⁻¹ ∂(muT N0)
      = ((16 * TbarEnt a b : ℝ) : ℂ) := by
  have hint := integrable_entryB N0 a b hN
  unfold muT at hint ⊢
  rw [integral_sumM _ _ _ hint]
  have hint2 := ((integrable_sumM_iff _ _ _).1 hint).2
  rw [integral_sumM _ _ _ hint2]
  have hA : ∫ p : Fin N0 × Bool, (wTB N0 (Sum.inl p) * (ptTB N0 (Sum.inl p) - a)⁻¹
        * (ptTB N0 (Sum.inl p) - b)⁻¹) ∂(Measure.count : Measure (Fin N0 × Bool))
      = -((∑ m ∈ Finset.range N0, atomTermB a b m : ℝ) : ℂ)
        - ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ) := by
    rw [integral_count]; exact atom_sumB N0 a b hN
  have hU : ∫ x : RayP, (wTB N0 (Sum.inr (Sum.inl x)) * (ptTB N0 (Sum.inr (Sum.inl x)) - a)⁻¹
        * (ptTB N0 (Sum.inr (Sum.inl x)) - b)⁻¹) ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), wUpB N0 r * (rayPt (xstarB N0) phiR r - a)⁻¹
          * (rayPt (xstarB N0) phiR r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => wUpB N0 r * (rayPt (xstarB N0) phiR r - a)⁻¹
          * (rayPt (xstarB N0) phiR r - b)⁻¹)
  have hL : ∫ x : RayP, (wTB N0 (Sum.inr (Sum.inr x)) * (ptTB N0 (Sum.inr (Sum.inr x)) - a)⁻¹
        * (ptTB N0 (Sum.inr (Sum.inr x)) - b)⁻¹) ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), wLowB N0 r * (rayPt (xstarB N0) (-phiR) r - a)⁻¹
          * (rayPt (xstarB N0) (-phiR) r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => wLowB N0 r * (rayPt (xstarB N0) (-phiR) r - a)⁻¹
          * (rayPt (xstarB N0) (-phiR) r - b)⁻¹)
  have eU : ∫ r in Ioi (0 : ℝ), wUpB N0 r * (rayPt (xstarB N0) phiR r - a)⁻¹
          * (rayPt (xstarB N0) phiR r - b)⁻¹
      = -(2 * Real.pi * I)⁻¹ * rayI (xstarB N0) phiR
          (fun z => ECB z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
    unfold rayI
    rw [← integral_const_mul]
    congr 1; funext r; simp only [wUpB]; ring
  have eL : ∫ r in Ioi (0 : ℝ), wLowB N0 r * (rayPt (xstarB N0) (-phiR) r - a)⁻¹
          * (rayPt (xstarB N0) (-phiR) r - b)⁻¹
      = (2 * Real.pi * I)⁻¹ * rayI (xstarB N0) (-phiR)
          (fun z => ECB z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
    unfold rayI
    rw [← integral_const_mul]
    congr 1; funext r; simp only [wLowB]; ring
  rw [hA, hU, hL, eU, eL, contour_identity_RB N0 a b hN, CatalanLambda.Decay.contL]
  ring

/-- No point of the combined space is a natural-number node. -/
lemma ptTB_ne (N0 : ℕ) (z : XT N0) (n : ℕ) : ptTB N0 z ≠ (n : ℂ) := by
  rcases z with ⟨m, s⟩ | r | r
  · cases s
    · simp only [ptTB, Sum.elim_inl, Bool.false_eq_true, ite_false]
      intro h
      have h' : (-(((m : ℕ) : ℝ) + 1 / 4)) = (n : ℝ) := by exact_mod_cast h
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · simp only [ptTB, Sum.elim_inl, ite_true]
      intro h
      have h' : (-(((m : ℕ) : ℝ) + 1)) = (n : ℝ) := by exact_mod_cast h
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  · simp only [ptTB, Sum.elim_inr, Sum.elim_inl]
    intro h
    have := congrArg Complex.im h
    rw [im_rayPt] at this
    simp only [Complex.natCast_im] at this
    have hr : 0 < r.1 := r.2
    have := mul_eq_zero.1 this
    rcases this with h1 | h1
    · linarith
    · linarith [sin_phiR_pos]
  · simp only [ptTB, Sum.elim_inr]
    intro h
    have := congrArg Complex.im h
    rw [im_rayPt] at this
    simp only [Complex.natCast_im] at this
    have hr : 0 < r.1 := r.2
    have := mul_eq_zero.1 this
    rcases this with h1 | h1
    · linarith
    · rw [Real.sin_neg] at h1; linarith [sin_phiR_pos]

/-- **Absolute-value Andréief bound for every principal submatrix of `16 T`.**
For any injective node family `s : Fin k → ℕ`, `|det (16 T[S])|` is bounded by
`(1/k!) ∫_{X^k} ∏_l |w(z_l)| · |Cauchy det(pt z, s)|² d(μ^{⊗k})`. -/
theorem tent_andreief_boundB (N0 k : ℕ) (hN : 1 ≤ N0) (s : Fin k → ℕ) (hs : Function.Injective s) :
    ‖(Matrix.of fun i j : Fin k => ((16 * TbarEnt (s i) (s j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → XT N0,
          (∏ l, ‖wTB N0 (z l)‖) *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((ptTB N0 (z l') - ptTB N0 (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (ptTB N0 (z l) - s i)‖ ^ 2 ∂(Measure.pi fun _ => muT N0) := by
  have h := norm_det_le_andreief (muT N0) (wTB N0) (fun (i : Fin k) z => (ptTB N0 z - (s i : ℂ))⁻¹)
    (fun (i : Fin k) z => (ptTB N0 z - (s i : ℂ))⁻¹) (fun i j => integrable_entryB N0 (s i) (s j) hN)
  have hM : (Matrix.of fun i j : Fin k => ∫ z, wTB N0 z * (ptTB N0 z - (s i : ℂ))⁻¹
        * (ptTB N0 z - (s j : ℂ))⁻¹ ∂(muT N0))
      = Matrix.of fun i j : Fin k => ((16 * TbarEnt (s i) (s j) : ℝ) : ℂ) := by
    ext i j; exact entry_TB N0 (s i) (s j) hN
  rw [hM] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [det_inv_eq_cauchy s hs (fun l => ptTB N0 (z l)) (fun l i => ptTB_ne N0 (z l) (s i))]
  ring

/-- Norms of the weight: `≤ 1` on atoms, `|E|/(2π)` on the rays. -/
lemma norm_wTB_atom (N0 : ℕ) (p : Fin N0 × Bool) : ‖wTB N0 (Sum.inl p)‖ ≤ 1 := by
  rcases p with ⟨m, b⟩
  cases b
  · simp [wTB]
  · by_cases h : (m : ℕ) + 1 < N0 <;> simp [wTB, h]

lemma norm_wTB_up (N0 : ℕ) (r : RayP) :
    ‖wTB N0 (Sum.inr (Sum.inl r))‖ = ‖ECB (rayPt (xstarB N0) phiR r.1)‖ / (2 * Real.pi) := by
  simp only [wTB, Sum.elim_inr, Sum.elim_inl, wUpB, norm_neg, norm_mul, norm_inv,
    Complex.norm_exp_ofReal_mul_I]
  have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖I‖ = 2 * Real.pi := by
    rw [show ‖(2:ℂ)‖ = 2 by simp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [this]; field_simp

lemma norm_wTB_low (N0 : ℕ) (r : RayP) :
    ‖wTB N0 (Sum.inr (Sum.inr r))‖ = ‖ECB (rayPt (xstarB N0) (-phiR) r.1)‖ / (2 * Real.pi) := by
  simp only [wTB, Sum.elim_inr, wLowB, norm_mul, norm_inv, Complex.norm_exp_ofReal_mul_I]
  have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖I‖ = 2 * Real.pi := by
    rw [show ‖(2:ℂ)‖ = 2 by simp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [this]; field_simp

end CatalanLambda.Mirror
