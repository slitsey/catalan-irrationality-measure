module

public import CatalanLambda.Decay.Contour
public import CatalanLambda.Decay.RayBound
public import CatalanLambda.Decay.AndreiefGeneric
public import CatalanLambda.Decay.CauchyDetFull
public import CatalanLambda.Decay.AndreiefSum

@[expose] public section

/-!
# Absolute-value Andréief bound for principal submatrices of `16 T`

The combined space `XT N0 = (Fin N0 × Bool) ⊕ (Ioi 0 ⊕ Ioi 0)` carries: the `2 N0` signed atoms,
the upper ray `x* + r e^{iφ}` and the lower ray `x* + r e^{-iφ}` (`r > 0`).
-/

open MeasureTheory Complex Set

namespace CatalanLambda.Decay

/-- Ray parameter space. -/
abbrev RayP : Type := Set.Ioi (0 : ℝ)

/-- The combined space: atoms, upper ray, lower ray. -/
abbrev XT (N0 : ℕ) : Type := (Fin N0 × Bool) ⊕ (RayP ⊕ RayP)

/-- The combined measure: counting measure on atoms, Lebesgue measure on both rays. -/
noncomputable def muT (N0 : ℕ) : Measure (XT N0) :=
  sumM (Measure.count : Measure (Fin N0 × Bool))
    (sumM (Measure.comap Subtype.val (volume : Measure ℝ))
      (Measure.comap Subtype.val (volume : Measure ℝ)))

instance (N0 : ℕ) : SigmaFinite (muT N0) := by
  unfold muT
  have : SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) : Measure RayP) := by
    refine SigmaFinite.of_map _ (f := Subtype.val) measurable_subtype_coe.aemeasurable ?_
    rw [map_comap_subtype_coe measurableSet_Ioi]
    infer_instance
  infer_instance

/-- Upper-ray weight `-(2πi)⁻¹ E(z) e^{iφ}`. -/
noncomputable def wUp (N0 : ℕ) (r : ℝ) : ℂ :=
  -((2 * Real.pi * I)⁻¹ * (EC (rayPt (xstar N0) phiC r) * exp ((phiC : ℂ) * I)))

/-- Lower-ray weight `(2πi)⁻¹ E(z) e^{-iφ}`. -/
noncomputable def wLow (N0 : ℕ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (EC (rayPt (xstar N0) (-phiC) r) * exp (((-phiC : ℝ) : ℂ) * I))

/-- The complex position of a point of `XT N0`. -/
noncomputable def ptT (N0 : ℕ) : XT N0 → ℂ :=
  Sum.elim (fun p => if p.2 then (((-(((p.1 : ℕ) : ℝ) + 1)) : ℝ) : ℂ)
      else (((-(((p.1 : ℕ) : ℝ) + 3 / 4)) : ℝ) : ℂ))
    (Sum.elim (fun r => rayPt (xstar N0) phiC r.1) (fun r => rayPt (xstar N0) (-phiC) r.1))

/-- The complex weight (density) on `XT N0`. -/
noncomputable def wT (N0 : ℕ) : XT N0 → ℂ :=
  Sum.elim (fun p => if p.2 then (1 : ℂ) else -1)
    (Sum.elim (fun r => wUp N0 r.1) (fun r => wLow N0 r.1))

lemma integrable_comap_Ioi (g : ℝ → ℂ) :
    Integrable (fun r : RayP => g r.1) (Measure.comap Subtype.val (volume : Measure ℝ))
      ↔ IntegrableOn g (Ioi 0) := by
  have := (MeasurableEmbedding.subtype_coe (measurableSet_Ioi (a := (0:ℝ)))).integrable_map_iff
    (μ := Measure.comap Subtype.val (volume : Measure ℝ)) (g := g)
  rw [map_comap_subtype_coe measurableSet_Ioi] at this
  exact this.symm

lemma integrable_entry (N0 a b : ℕ) :
    Integrable (fun z => wT N0 z * (ptT N0 z - a)⁻¹ * (ptT N0 z - b)⁻¹) (muT N0) := by
  unfold muT
  rw [integrable_sumM_iff, integrable_sumM_iff]
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · have h := Integrable.const_mul (integrableOn_E_ray N0 a b (θ := phiC)
      (ne_of_gt (by linarith [sin_phiC_ge]))) (-(2 * Real.pi * I)⁻¹)
    refine (integrable_comap_Ioi (fun r => wUp N0 r * (rayPt (xstar N0) phiC r - a)⁻¹
      * (rayPt (xstar N0) phiC r - b)⁻¹)).2 (IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi)
    simp only [wUp]; ring
  · have h := Integrable.const_mul (integrableOn_E_ray N0 a b (θ := -phiC)
      (by rw [Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt (by linarith [sin_phiC_ge])))) ((2 * Real.pi * I)⁻¹)
    refine (integrable_comap_Ioi (fun r => wLow N0 r * (rayPt (xstar N0) (-phiC) r - a)⁻¹
      * (rayPt (xstar N0) (-phiC) r - b)⁻¹)).2 (IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi)
    simp only [wLow]; ring

lemma atom_pt_prod (a b : ℕ) (μ : ℝ) (_hμ : 0 < μ) :
    (((-μ : ℝ) : ℂ) - a)⁻¹ * (((-μ : ℝ) : ℂ) - b)⁻¹
      = ((1 / (((a : ℝ) + μ) * ((b : ℝ) + μ)) : ℝ) : ℂ) := by
  have h1 : ((-μ : ℝ) : ℂ) - a = -(((a : ℝ) + μ : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((-μ : ℝ) : ℂ) - b = -(((b : ℝ) + μ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, inv_neg, inv_neg, neg_mul_neg, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul]
  congr 1
  rw [one_div, mul_inv]

lemma atom_sum (N0 a b : ℕ) :
    ∑ p : Fin N0 × Bool, (wT N0 (Sum.inl p) * (ptT N0 (Sum.inl p) - a)⁻¹
        * (ptT N0 (Sum.inl p) - b)⁻¹)
      = -((∑ m ∈ Finset.range N0, atomTerm a b m : ℝ) : ℂ) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, wT, ptT, Sum.elim_inl, ite_true, Bool.false_eq_true, ite_false]
  have key : ∀ m : Fin N0,
      (1 * (((-(((m : ℕ) : ℝ) + 1) : ℝ) : ℂ) - a)⁻¹ * (((-(((m : ℕ) : ℝ) + 1) : ℝ) : ℂ) - b)⁻¹
        + -1 * (((-(((m : ℕ) : ℝ) + 3 / 4) : ℝ) : ℂ) - a)⁻¹
          * (((-(((m : ℕ) : ℝ) + 3 / 4) : ℝ) : ℂ) - b)⁻¹)
      = -((atomTerm a b (m : ℕ) : ℝ) : ℂ) := by
    intro m
    have hm : (0 : ℝ) ≤ (m : ℕ) := Nat.cast_nonneg _
    rw [one_mul, neg_one_mul, neg_mul, atom_pt_prod a b _ (by linarith),
      atom_pt_prod a b _ (by linarith)]
    unfold atomTerm atomU
    simp only [one_div, mul_inv]
    push_cast
    ring
  simp_rw [key]
  rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Fin.sum_univ_eq_sum_range]

/-- **The entries of `16 T` as integrals against the combined measure.** -/
theorem entry_T (N0 a b : ℕ) :
    ∫ z, wT N0 z * (ptT N0 z - a)⁻¹ * (ptT N0 z - b)⁻¹ ∂(muT N0)
      = ((16 * Tent a b : ℝ) : ℂ) := by
  have hint := integrable_entry N0 a b
  unfold muT at hint ⊢
  rw [integral_sumM _ _ _ hint]
  have hint2 := ((integrable_sumM_iff _ _ _).1 hint).2
  rw [integral_sumM _ _ _ hint2]
  have hA : ∫ p : Fin N0 × Bool, (wT N0 (Sum.inl p) * (ptT N0 (Sum.inl p) - a)⁻¹
        * (ptT N0 (Sum.inl p) - b)⁻¹) ∂(Measure.count : Measure (Fin N0 × Bool))
      = -((∑ m ∈ Finset.range N0, atomTerm a b m : ℝ) : ℂ) := by
    rw [integral_count]; exact atom_sum N0 a b
  have hU : ∫ x : RayP, (wT N0 (Sum.inr (Sum.inl x)) * (ptT N0 (Sum.inr (Sum.inl x)) - a)⁻¹
        * (ptT N0 (Sum.inr (Sum.inl x)) - b)⁻¹) ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), wUp N0 r * (rayPt (xstar N0) phiC r - a)⁻¹
          * (rayPt (xstar N0) phiC r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => wUp N0 r * (rayPt (xstar N0) phiC r - a)⁻¹
          * (rayPt (xstar N0) phiC r - b)⁻¹)
  have hL : ∫ x : RayP, (wT N0 (Sum.inr (Sum.inr x)) * (ptT N0 (Sum.inr (Sum.inr x)) - a)⁻¹
        * (ptT N0 (Sum.inr (Sum.inr x)) - b)⁻¹) ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), wLow N0 r * (rayPt (xstar N0) (-phiC) r - a)⁻¹
          * (rayPt (xstar N0) (-phiC) r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => wLow N0 r * (rayPt (xstar N0) (-phiC) r - a)⁻¹
          * (rayPt (xstar N0) (-phiC) r - b)⁻¹)
  have eU : ∫ r in Ioi (0 : ℝ), wUp N0 r * (rayPt (xstar N0) phiC r - a)⁻¹
          * (rayPt (xstar N0) phiC r - b)⁻¹
      = -(2 * Real.pi * I)⁻¹ * rayI (xstar N0) phiC
          (fun z => EC z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
    unfold rayI
    rw [← integral_const_mul]
    congr 1; funext r; simp only [wUp]; ring
  have eL : ∫ r in Ioi (0 : ℝ), wLow N0 r * (rayPt (xstar N0) (-phiC) r - a)⁻¹
          * (rayPt (xstar N0) (-phiC) r - b)⁻¹
      = (2 * Real.pi * I)⁻¹ * rayI (xstar N0) (-phiC)
          (fun z => EC z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
    unfold rayI
    rw [← integral_const_mul]
    congr 1; funext r; simp only [wLow]; ring
  rw [hA, hU, hL, eU, eL, contour_identity N0 a b, contL]
  ring

lemma im_rayPt (x θ r : ℝ) : (rayPt x θ r).im = r * Real.sin θ := by
  simp [rayPt, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]

/-- No point of the combined space is a natural-number node. -/
lemma ptT_ne (N0 : ℕ) (z : XT N0) (n : ℕ) : ptT N0 z ≠ (n : ℂ) := by
  rcases z with ⟨m, s⟩ | r | r
  · cases s
    · simp only [ptT, Sum.elim_inl, Bool.false_eq_true, ite_false]
      intro h
      have h' : (-(((m : ℕ) : ℝ) + 3 / 4)) = (n : ℝ) := by exact_mod_cast h
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · simp only [ptT, Sum.elim_inl, ite_true]
      intro h
      have h' : (-(((m : ℕ) : ℝ) + 1)) = (n : ℝ) := by exact_mod_cast h
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    intro h
    have := congrArg Complex.im h
    rw [im_rayPt] at this
    simp only [Complex.natCast_im] at this
    have hr : 0 < r.1 := r.2
    have := mul_eq_zero.1 this
    rcases this with h1 | h1
    · linarith
    · linarith [sin_phiC_ge]
  · simp only [ptT, Sum.elim_inr]
    intro h
    have := congrArg Complex.im h
    rw [im_rayPt] at this
    simp only [Complex.natCast_im] at this
    have hr : 0 < r.1 := r.2
    have := mul_eq_zero.1 this
    rcases this with h1 | h1
    · linarith
    · rw [Real.sin_neg] at h1; linarith [sin_phiC_ge]

/-- The determinant `det[(x_l - s_i)⁻¹]` is the Cauchy determinant. -/
lemma det_inv_eq_cauchy {k : ℕ} (s : Fin k → ℕ) (hs : Function.Injective s) (x : Fin k → ℂ)
    (hx : ∀ l i, x l ≠ (s i : ℂ)) :
    (Matrix.of fun i l => (x l - (s i : ℂ))⁻¹).det
      = (∏ l, ∏ l' ∈ Finset.Ioi l, ((x l' - x l) * ((s l : ℂ) - s l'))) / ∏ l, ∏ i, (x l - s i) := by
  have hinj : Function.Injective (fun i => (s i : ℂ)) :=
    fun i j h => hs (Nat.cast_injective (R := ℂ) h)
  have : (Matrix.of fun i l => (x l - (s i : ℂ))⁻¹)
      = Matrix.transpose (Matrix.of fun l i => 1 / (x l - (fun i => (s i : ℂ)) i)) := by
    ext i l; simp [one_div]
  rw [this, Matrix.det_transpose, cauchy_det x (fun i => (s i : ℂ)) hinj hx]

/-- **Absolute-value Andréief bound for every principal submatrix of `16 T`.**
For any injective node family `s : Fin k → ℕ`, `|det (16 T[S])|` is bounded by
`(1/k!) ∫_{X^k} ∏_l |w(z_l)| · |Cauchy det(pt z, s)|² d(μ^{⊗k})`. -/
theorem tent_andreief_bound (N0 k : ℕ) (s : Fin k → ℕ) (hs : Function.Injective s) :
    ‖(Matrix.of fun i j : Fin k => ((16 * Tent (s i) (s j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → XT N0,
          (∏ l, ‖wT N0 (z l)‖) *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((ptT N0 (z l') - ptT N0 (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (ptT N0 (z l) - s i)‖ ^ 2 ∂(Measure.pi fun _ => muT N0) := by
  have h := norm_det_le_andreief (muT N0) (wT N0) (fun (i : Fin k) z => (ptT N0 z - (s i : ℂ))⁻¹)
    (fun (i : Fin k) z => (ptT N0 z - (s i : ℂ))⁻¹) (fun i j => integrable_entry N0 (s i) (s j))
  have hM : (Matrix.of fun i j : Fin k => ∫ z, wT N0 z * (ptT N0 z - (s i : ℂ))⁻¹
        * (ptT N0 z - (s j : ℂ))⁻¹ ∂(muT N0))
      = Matrix.of fun i j : Fin k => ((16 * Tent (s i) (s j) : ℝ) : ℂ) := by
    ext i j; exact entry_T N0 (s i) (s j)
  rw [hM] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [det_inv_eq_cauchy s hs (fun l => ptT N0 (z l)) (fun l i => ptT_ne N0 (z l) (s i))]
  ring

/-- Norms of the weight: `1` on atoms, `|E|/(2π)` on the rays. -/
lemma norm_wT_atom (N0 : ℕ) (p : Fin N0 × Bool) : ‖wT N0 (Sum.inl p)‖ = 1 := by
  rcases p with ⟨m, b⟩
  cases b <;> simp [wT]

lemma norm_wT_up (N0 : ℕ) (r : RayP) :
    ‖wT N0 (Sum.inr (Sum.inl r))‖ = ‖EC (rayPt (xstar N0) phiC r.1)‖ / (2 * Real.pi) := by
  simp only [wT, Sum.elim_inr, Sum.elim_inl, wUp, norm_neg, norm_mul, norm_inv,
    norm_exp_ofReal_mul_I]
  have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖I‖ = 2 * Real.pi := by
    rw [show ‖(2:ℂ)‖ = 2 by simp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [this]; field_simp

lemma norm_wT_low (N0 : ℕ) (r : RayP) :
    ‖wT N0 (Sum.inr (Sum.inr r))‖ = ‖EC (rayPt (xstar N0) (-phiC) r.1)‖ / (2 * Real.pi) := by
  simp only [wT, Sum.elim_inr, wLow, norm_mul, norm_inv, norm_exp_ofReal_mul_I]
  have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖I‖ = 2 * Real.pi := by
    rw [show ‖(2:ℂ)‖ = 2 by simp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [this]; field_simp

end CatalanLambda.Decay
