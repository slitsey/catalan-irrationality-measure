module

public import CatalanCore.Decay.Atoms
public import CatalanCore.Decay.RayBound
public import CatalanLambda.Decay.AndreiefGeneric
public import CatalanLambda.Decay.AndreiefSum
public import CatalanLambda.Decay.CauchyDetFull
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The combined space and the Andréief bound for a general frame (WP2b)

For a frame `Fr` with `ContourOK`, `N0 : ℕ` and the ray angle `φ_R = π - arctan 3` (direction
`(-1, 3)`, the direction of the certified rays), the combined space is
`XT N0 = (atoms) ⊕ (upper ray ⊕ lower ray)`:

* atoms: the finite set `atomIdx N0 ⊂ ℕ × Fin d` of pairs `(m, i)` whose pole `-(m + μ_i)` lies to the
  right of the contour vertex `x* = -N0 - xs`; position `-(m + μ_i)`, weight `w_i` (counting measure);
* the two rays `x* + r e^{±iφ_R}`, `r > 0` (Lebesgue measure), weight `∓(2πi)⁻¹ E e^{±iφ}`.

`entry_T` : `∫ w (z - a)⁻¹ (z - b)⁻¹ dμ = norm · T_{ab}`; `tent_andreief_bound` is the absolute-value
Andréief bound for every principal minor of `norm · T`.  Compared with the legacy λ code, the
atoms are indexed by `(m, i)` (a density `d` of atoms per unit), carry the integer weight `w_i`, and
the integrability on the rays uses the finite `C_E` of `RayBound`.

Also here: `integrableOn_E_ray` (left open by WP2a), and the ray direction `phiR`.
-/

open MeasureTheory Complex Set Finset
open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos sumM meInl meInr integrable_sumM_iff
  integral_sumM integrableOn_of_bound norm_det_le_andreief cauchy_det rayPt_re rayPt_im)

namespace CatalanCore
namespace Decay

/-- The angle of the direction `(-1, 3)`: `π - arctan 3`. -/
noncomputable def phiR : ℝ := Real.pi - Real.arctan 3

lemma phiR_gt : Real.pi / 2 < phiR := by
  unfold phiR
  have := Real.arctan_lt_pi_div_two 3
  linarith

lemma phiR_lt : phiR < Real.pi := by
  unfold phiR
  have := Real.arctan_pos.2 (show (0 : ℝ) < 3 by norm_num)
  linarith

lemma sin_phiR : Real.sin phiR = 3 / Real.sqrt 10 := by
  unfold phiR
  rw [Real.sin_pi_sub, Real.sin_arctan]
  norm_num

lemma cos_phiR : Real.cos phiR = -(1 / Real.sqrt 10) := by
  unfold phiR
  rw [Real.cos_pi_sub, Real.cos_arctan]
  norm_num

lemma sin_phiR_pos : 0 < Real.sin phiR := by
  rw [sin_phiR]; positivity

lemma cos_phiR_neg : Real.cos phiR < 0 := by
  rw [cos_phiR]; have : 0 < Real.sqrt 10 := by positivity
  have : 0 < 1 / Real.sqrt 10 := by positivity
  linarith

/-- `-cos φ_R ≤ 4 δ0 sin φ_R` as soon as `δ0 ≥ 1/12`. -/
lemma phiR_cot {δ0 : ℚ} (h : (1 : ℚ) / 12 ≤ δ0) :
    -Real.cos phiR ≤ 4 * (δ0 : ℝ) * Real.sin phiR := by
  rw [sin_phiR, cos_phiR, neg_neg]
  have hs : 0 < Real.sqrt 10 := by positivity
  have h' : (1 : ℝ) / 12 ≤ (δ0 : ℝ) := by have := (Rat.cast_le (K := ℝ)).2 h; push_cast at this; exact this
  rw [show 4 * (δ0 : ℝ) * (3 / Real.sqrt 10) = (12 * δ0) / Real.sqrt 10 by ring]
  exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- Ray parameter space. -/
abbrev RayP : Type := Set.Ioi (0 : ℝ)

lemma integrable_comap_Ioi (g : ℝ → ℂ) :
    Integrable (fun r : RayP => g r.1) (Measure.comap Subtype.val (volume : Measure ℝ))
      ↔ IntegrableOn g (Ioi 0) := by
  have := (MeasurableEmbedding.subtype_coe (measurableSet_Ioi (a := (0:ℝ)))).integrable_map_iff
    (μ := Measure.comap Subtype.val (volume : Measure ℝ)) (g := g)
  rw [map_comap_subtype_coe measurableSet_Ioi] at this
  exact this.symm

lemma integrable_comap_Ioi_real (g : ℝ → ℝ) :
    Integrable (fun r : RayP => g r.1) (Measure.comap Subtype.val (volume : Measure ℝ))
      ↔ IntegrableOn g (Ioi 0) := by
  have := (MeasurableEmbedding.subtype_coe (measurableSet_Ioi (a := (0:ℝ)))).integrable_map_iff
    (μ := Measure.comap Subtype.val (volume : Measure ℝ)) (g := g)
  rw [map_comap_subtype_coe measurableSet_Ioi] at this
  exact this.symm

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

end Decay

namespace Frame

open Decay

variable (Fr : Frame)

/-! ### Integrability of the ray integrand (left open by WP2a) -/

theorem integrableOn_E_ray (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 4 * (Fr.δ0 : ℝ) * Real.sin φ) (N0 a b : ℕ) {θ : ℝ}
    (hθ : θ = φ ∨ θ = -φ) :
    IntegrableOn (fun r : ℝ => (Fr.EC (rayPt (Fr.xstar N0) θ r)
      * ((rayPt (Fr.xstar N0) θ r - a)⁻¹ * (rayPt (Fr.xstar N0) θ r - b)⁻¹))
        * exp ((θ : ℂ) * I)) (Ioi 0) := by
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h2
  have hs : Real.sin θ ≠ 0 := by
    rcases hθ with h | h
    · rw [h]; exact ne_of_gt hsφ
    · rw [h, Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt hsφ)
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := Fr.xstar N0 with hxdef
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hlim : ∀ r : ℝ, HasSum (fun n : ℤ => (Fr.eterm (rayPt x θ r) n
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      ((Fr.EC (rayPt x θ r) * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I)) :=
    fun r => ((Fr.summable_eterm _).hasSum.mul_right _).mul_right _
  have hmeas : ∀ n : ℤ, Measurable fun r : ℝ => (Fr.eterm (rayPt x θ r) n
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I) := by
    intro n
    unfold rayPt eterm
    fun_prop
  have hae : AEStronglyMeasurable (fun r : ℝ => (Fr.EC (rayPt x θ r)
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (volume.restrict (Ioi 0)) := by
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ℤ))
      (f := fun s r => ∑ n ∈ s, (Fr.eterm (rayPt x θ r) n
        * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (fun s => (Finset.measurable_sum s (fun n _ => hmeas n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r => hlim r)
  refine integrableOn_of_bound hae (m := (Fr.xs : ℝ)) (C := Fr.rayConst / K ^ 2) hxs ?_
  intro r hr
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hb := Fr.Ev_ray_bound hC h1 h2 hcot N0 a b hθ hr0
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  refine hb.trans ?_
  have hex : Real.exp (-(2 * Real.pi * (r * Real.sin φ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 * Real.pi * (r * Real.sin φ) := by positivity
    linarith
  have hCE := Fr.rayConst_nonneg hC
  have hxr : 0 < (Fr.xs : ℝ) + r := by linarith
  have e : 1 / (K * ((Fr.xs : ℝ) + r)) * (1 / (K * ((Fr.xs : ℝ) + r)))
      = (1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2) := by
    field_simp
  rw [e]
  calc Fr.rayConst * Real.exp (-(2 * Real.pi * (r * Real.sin φ))) *
        (1 / K ^ 2 * (1 / ((Fr.xs : ℝ) + r) ^ 2))
      ≤ Fr.rayConst * 1 * (1 / K ^ 2 * (1 / ((Fr.xs : ℝ) + r) ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hex hCE
    _ = Fr.rayConst / K ^ 2 * (1 / ((Fr.xs : ℝ) + r) ^ 2) := by ring

/-! ### The combined space -/

open Classical in
/-- The atoms: pairs `(m, i)` whose pole `-(m + μ_i)` lies strictly to the right of `x*`
(equivalently, the pairs appearing in `atomHead`). -/
noncomputable def atomIdx (N0 : ℕ) : Finset (ℕ × Fin Fr.d) :=
  (range (N0 + ⌈(Fr.xs : ℝ)⌉₊) ×ˢ (univ : Finset (Fin Fr.d))).filter
    (fun p => ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (p.1 : ℝ) + (Fr.μ p.2 : ℝ)))

/-- The position of the atom `(m, i)`: `-(m + μ_i)`. -/
noncomputable def atomPos (p : ℕ × Fin Fr.d) : ℝ := -((p.1 : ℝ) + (Fr.μ p.2 : ℝ))

/-- The combined space: atoms, upper ray, lower ray. -/
abbrev XT (N0 : ℕ) : Type := ↥(Fr.atomIdx N0) ⊕ (RayP ⊕ RayP)

/-- The combined measure: counting measure on atoms, Lebesgue measure on both rays. -/
noncomputable def muT (N0 : ℕ) : Measure (Fr.XT N0) :=
  sumM (Measure.count : Measure ↥(Fr.atomIdx N0))
    (sumM (Measure.comap Subtype.val (volume : Measure ℝ))
      (Measure.comap Subtype.val (volume : Measure ℝ)))

instance (N0 : ℕ) : SigmaFinite (Fr.muT N0) := by
  unfold muT
  have : SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) : Measure RayP) := by
    refine SigmaFinite.of_map _ (f := Subtype.val) measurable_subtype_coe.aemeasurable ?_
    rw [map_comap_subtype_coe measurableSet_Ioi]
    infer_instance
  infer_instance

/-- Upper-ray weight `-(2πi)⁻¹ E(z) e^{iφ}`. -/
noncomputable def wUp (N0 : ℕ) (r : ℝ) : ℂ :=
  -((2 * Real.pi * I)⁻¹ * (Fr.EC (rayPt (Fr.xstar N0) phiR r) * exp ((phiR : ℂ) * I)))

/-- Lower-ray weight `(2πi)⁻¹ E(z) e^{-iφ}`. -/
noncomputable def wLow (N0 : ℕ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (Fr.EC (rayPt (Fr.xstar N0) (-phiR) r) * exp (((-phiR : ℝ) : ℂ) * I))

/-- The complex position of a point of `XT N0`. -/
noncomputable def ptT (N0 : ℕ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => ((Fr.atomPos p.1 : ℝ) : ℂ))
    (Sum.elim (fun r => rayPt (Fr.xstar N0) phiR r.1) (fun r => rayPt (Fr.xstar N0) (-phiR) r.1))

/-- The complex weight (density) on `XT N0`. -/
noncomputable def wT (N0 : ℕ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => ((Fr.w p.1.2 : ℤ) : ℂ))
    (Sum.elim (fun r => Fr.wUp N0 r.1) (fun r => Fr.wLow N0 r.1))

variable {Fr}

lemma integrable_entry (hC : Fr.ContourOK) (hδ : (1 : ℚ) / 12 ≤ Fr.δ0) (N0 a b : ℕ) :
    Integrable (fun z => Fr.wT N0 z * (Fr.ptT N0 z - a)⁻¹ * (Fr.ptT N0 z - b)⁻¹) (Fr.muT N0) := by
  unfold muT
  rw [integrable_sumM_iff, integrable_sumM_iff]
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · have h := Integrable.const_mul (Fr.integrableOn_E_ray hC phiR_gt phiR_lt (phiR_cot hδ) N0 a b
      (θ := phiR) (Or.inl rfl)) (-(2 * Real.pi * I)⁻¹)
    refine (integrable_comap_Ioi (fun r => Fr.wUp N0 r * (rayPt (Fr.xstar N0) phiR r - a)⁻¹
      * (rayPt (Fr.xstar N0) phiR r - b)⁻¹)).2 (IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi)
    simp only [wUp]; ring
  · have h := Integrable.const_mul (Fr.integrableOn_E_ray hC phiR_gt phiR_lt (phiR_cot hδ) N0 a b
      (θ := -phiR) (Or.inr rfl)) ((2 * Real.pi * I)⁻¹)
    refine (integrable_comap_Ioi (fun r => Fr.wLow N0 r * (rayPt (Fr.xstar N0) (-phiR) r - a)⁻¹
      * (rayPt (Fr.xstar N0) (-phiR) r - b)⁻¹)).2 (IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi)
    simp only [wLow]; ring

lemma atom_pt_prod (a b : ℕ) (μ : ℝ) :
    (((-μ : ℝ) : ℂ) - a)⁻¹ * (((-μ : ℝ) : ℂ) - b)⁻¹
      = ((1 / (((a : ℝ) + μ) * ((b : ℝ) + μ)) : ℝ) : ℂ) := by
  have h1 : ((-μ : ℝ) : ℂ) - a = -(((a : ℝ) + μ : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((-μ : ℝ) : ℂ) - b = -(((b : ℝ) + μ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, inv_neg, inv_neg, neg_mul_neg, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul]
  congr 1
  rw [one_div, mul_inv]

/-- `atomHead` as a sum over the atom index set. -/
lemma atomHead_eq (N0 a b : ℕ) :
    Fr.atomHead N0 a b = ∑ p ∈ Fr.atomIdx N0, Fr.atomR p.2 a b (p.1 : ℝ) := by
  classical
  unfold atomHead headTerm atomIdx
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ => ?_))
  simp only [ite_not]

lemma atom_sum (N0 a b : ℕ) :
    ∑ p : ↥(Fr.atomIdx N0), (Fr.wT N0 (Sum.inl p) * (Fr.ptT N0 (Sum.inl p) - a)⁻¹
        * (Fr.ptT N0 (Sum.inl p) - b)⁻¹)
      = ((Fr.atomHead N0 a b : ℝ) : ℂ) := by
  have key : ∀ p : ↥(Fr.atomIdx N0), (Fr.wT N0 (Sum.inl p) * (Fr.ptT N0 (Sum.inl p) - a)⁻¹
        * (Fr.ptT N0 (Sum.inl p) - b)⁻¹) = ((Fr.atomR p.1.2 a b (p.1.1 : ℝ) : ℝ) : ℂ) := by
    intro p
    simp only [wT, ptT, Sum.elim_inl, atomPos]
    rw [mul_assoc, atom_pt_prod a b]
    unfold atomR
    push_cast
    ring
  simp_rw [key]
  rw [Finset.sum_coe_sort (Fr.atomIdx N0) (fun p => ((Fr.atomR p.2 a b (p.1 : ℝ) : ℝ) : ℂ)),
    atomHead_eq]
  push_cast
  rfl

/-- **The entries of `norm · T` as integrals against the combined measure.** -/
theorem entry_T (hC : Fr.ContourOK) (hδ : (1 : ℚ) / 12 ≤ Fr.δ0) (N0 a b : ℕ) :
    ∫ z, Fr.wT N0 z * (Fr.ptT N0 z - a)⁻¹ * (Fr.ptT N0 z - b)⁻¹ ∂(Fr.muT N0)
      = (((Fr.norm : ℝ) * Fr.Tent a b : ℝ) : ℂ) := by
  have hint := integrable_entry hC hδ N0 a b
  unfold muT at hint ⊢
  rw [integral_sumM _ _ _ hint]
  have hint2 := ((integrable_sumM_iff _ _ _).1 hint).2
  rw [integral_sumM _ _ _ hint2]
  have hA : ∫ p : ↥(Fr.atomIdx N0), (Fr.wT N0 (Sum.inl p) * (Fr.ptT N0 (Sum.inl p) - a)⁻¹
        * (Fr.ptT N0 (Sum.inl p) - b)⁻¹) ∂(Measure.count : Measure ↥(Fr.atomIdx N0))
      = ((Fr.atomHead N0 a b : ℝ) : ℂ) := by
    rw [integral_count]; exact atom_sum N0 a b
  have hU : ∫ x : RayP, (Fr.wT N0 (Sum.inr (Sum.inl x)) * (Fr.ptT N0 (Sum.inr (Sum.inl x)) - a)⁻¹
        * (Fr.ptT N0 (Sum.inr (Sum.inl x)) - b)⁻¹) ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), Fr.wUp N0 r * (rayPt (Fr.xstar N0) phiR r - a)⁻¹
          * (rayPt (Fr.xstar N0) phiR r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => Fr.wUp N0 r * (rayPt (Fr.xstar N0) phiR r - a)⁻¹
          * (rayPt (Fr.xstar N0) phiR r - b)⁻¹)
  have hL : ∫ x : RayP, (Fr.wT N0 (Sum.inr (Sum.inr x)) * (Fr.ptT N0 (Sum.inr (Sum.inr x)) - a)⁻¹
        * (Fr.ptT N0 (Sum.inr (Sum.inr x)) - b)⁻¹) ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), Fr.wLow N0 r * (rayPt (Fr.xstar N0) (-phiR) r - a)⁻¹
          * (rayPt (Fr.xstar N0) (-phiR) r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => Fr.wLow N0 r * (rayPt (Fr.xstar N0) (-phiR) r - a)⁻¹
          * (rayPt (Fr.xstar N0) (-phiR) r - b)⁻¹)
  have eU : ∫ r in Ioi (0 : ℝ), Fr.wUp N0 r * (rayPt (Fr.xstar N0) phiR r - a)⁻¹
          * (rayPt (Fr.xstar N0) phiR r - b)⁻¹
      = -(2 * Real.pi * I)⁻¹ * rayI (Fr.xstar N0) phiR
          (fun z => Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
    unfold rayI
    rw [← integral_const_mul]
    congr 1; funext r; simp only [wUp]; ring
  have eL : ∫ r in Ioi (0 : ℝ), Fr.wLow N0 r * (rayPt (Fr.xstar N0) (-phiR) r - a)⁻¹
          * (rayPt (Fr.xstar N0) (-phiR) r - b)⁻¹
      = (2 * Real.pi * I)⁻¹ * rayI (Fr.xstar N0) (-phiR)
          (fun z => Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
    unfold rayI
    rw [← integral_const_mul]
    congr 1; funext r; simp only [wLow]; ring
  have hci := Fr.contour_identity hC phiR_gt phiR_lt N0 a b
  rw [← Fr.norm_mul_Tent a b] at hci
  rw [hA, hU, hL, eU, eL, hci, contL]
  ring

lemma im_rayPt (x θ r : ℝ) : (rayPt x θ r).im = r * Real.sin θ := by
  simp [rayPt, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]

/-- No point of the combined space is a natural-number node. -/
lemma ptT_ne (N0 : ℕ) (z : Fr.XT N0) (n : ℕ) : Fr.ptT N0 z ≠ (n : ℂ) := by
  rcases z with p | r | r
  · simp only [ptT, Sum.elim_inl, atomPos]
    intro h
    have h' : (-(((p.1.1 : ℕ) : ℝ) + (Fr.μ p.1.2 : ℝ))) = (n : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ ((p.1.1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have := Fr.mu_pos p.1.2
    linarith
  · simp only [ptT, Sum.elim_inr, Sum.elim_inl]
    intro h
    have := congrArg Complex.im h
    rw [im_rayPt] at this
    simp only [Complex.natCast_im] at this
    have hr : 0 < r.1 := r.2
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith [sin_phiR_pos]
  · simp only [ptT, Sum.elim_inr]
    intro h
    have := congrArg Complex.im h
    rw [im_rayPt] at this
    simp only [Complex.natCast_im] at this
    have hr : 0 < r.1 := r.2
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · rw [Real.sin_neg] at h1; linarith [sin_phiR_pos]

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

/-- **Absolute-value Andréief bound for every principal submatrix of `norm · T`.** -/
theorem tent_andreief_bound (hC : Fr.ContourOK) (hδ : (1 : ℚ) / 12 ≤ Fr.δ0) (N0 k : ℕ)
    (s : Fin k → ℕ) (hs : Function.Injective s) :
    ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (s j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT N0,
          (∏ l, ‖Fr.wT N0 (z l)‖) *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((Fr.ptT N0 (z l') - Fr.ptT N0 (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (Fr.ptT N0 (z l) - s i)‖ ^ 2 ∂(Measure.pi fun _ => Fr.muT N0) := by
  have h := norm_det_le_andreief (Fr.muT N0) (Fr.wT N0) (fun (i : Fin k) z => (Fr.ptT N0 z - (s i : ℂ))⁻¹)
    (fun (i : Fin k) z => (Fr.ptT N0 z - (s i : ℂ))⁻¹)
    (fun i j => integrable_entry hC hδ N0 (s i) (s j))
  have hM : (Matrix.of fun i j : Fin k => ∫ z, Fr.wT N0 z * (Fr.ptT N0 z - (s i : ℂ))⁻¹
        * (Fr.ptT N0 z - (s j : ℂ))⁻¹ ∂(Fr.muT N0))
      = Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (s j) : ℝ) : ℂ) := by
    ext i j; exact entry_T hC hδ N0 (s i) (s j)
  rw [hM] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [det_inv_eq_cauchy s hs (fun l => Fr.ptT N0 (z l)) (fun l i => ptT_ne N0 (z l) (s i))]
  ring

/-- **Rectangular (two node families) Andréief bound** (hybrid-readiness, design 9.3): for a ROW node
family `s` and a COLUMN node family `t`, both injective,
`|det (norm · T[s, t])| ≤ (1/k!) ∫ ∏|w| · |C(z, s)| · |C(z, t)|`.  The square case `s = t` is
`tent_andreief_bound`. -/
theorem tent_andreief_bound_rect (hC : Fr.ContourOK) (hδ : (1 : ℚ) / 12 ≤ Fr.δ0) (N0 k : ℕ)
    (s t : Fin k → ℕ) (hs : Function.Injective s) (ht : Function.Injective t) :
    ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT N0,
          (∏ l, ‖Fr.wT N0 (z l)‖) *
            (‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((Fr.ptT N0 (z l') - Fr.ptT N0 (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (Fr.ptT N0 (z l) - s i)‖ *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((Fr.ptT N0 (z l') - Fr.ptT N0 (z l)) * ((t l : ℂ) - t l')))
              / ∏ l, ∏ i, (Fr.ptT N0 (z l) - t i)‖) ∂(Measure.pi fun _ => Fr.muT N0) := by
  have h := norm_det_le_andreief (Fr.muT N0) (Fr.wT N0)
    (fun (i : Fin k) z => (Fr.ptT N0 z - (s i : ℂ))⁻¹)
    (fun (i : Fin k) z => (Fr.ptT N0 z - (t i : ℂ))⁻¹)
    (fun i j => integrable_entry hC hδ N0 (s i) (t j))
  have hM : (Matrix.of fun i j : Fin k => ∫ z, Fr.wT N0 z * (Fr.ptT N0 z - (s i : ℂ))⁻¹
        * (Fr.ptT N0 z - (t j : ℂ))⁻¹ ∂(Fr.muT N0))
      = Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ) := by
    ext i j; exact entry_T hC hδ N0 (s i) (t j)
  rw [hM] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [det_inv_eq_cauchy s hs (fun l => Fr.ptT N0 (z l)) (fun l i => ptT_ne N0 (z l) (s i)),
    det_inv_eq_cauchy t ht (fun l => Fr.ptT N0 (z l)) (fun l i => ptT_ne N0 (z l) (t i))]
  ring

/-- Norms of the weights: `|w_i|` on atoms, `‖E‖/(2π)` on the rays. -/
lemma norm_wT_atom (N0 : ℕ) (p : ↥(Fr.atomIdx N0)) :
    ‖Fr.wT N0 (Sum.inl p)‖ = |(Fr.w p.1.2 : ℝ)| := by
  simp [wT]

lemma norm_wT_up (N0 : ℕ) (r : RayP) :
    ‖Fr.wT N0 (Sum.inr (Sum.inl r))‖ = ‖Fr.EC (rayPt (Fr.xstar N0) phiR r.1)‖ / (2 * Real.pi) := by
  simp only [wT, Sum.elim_inr, Sum.elim_inl, wUp, norm_neg, norm_mul, norm_inv,
    Complex.norm_exp_ofReal_mul_I]
  have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖I‖ = 2 * Real.pi := by
    rw [show ‖(2:ℂ)‖ = 2 by simp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [this]; field_simp

lemma norm_wT_low (N0 : ℕ) (r : RayP) :
    ‖Fr.wT N0 (Sum.inr (Sum.inr r))‖ = ‖Fr.EC (rayPt (Fr.xstar N0) (-phiR) r.1)‖ / (2 * Real.pi) := by
  simp only [wT, Sum.elim_inr, wLow, norm_mul, norm_inv, Complex.norm_exp_ofReal_mul_I]
  have : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖I‖ = 2 * Real.pi := by
    rw [show ‖(2:ℂ)‖ = 2 by simp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [this]; field_simp

end Frame
end CatalanCore
