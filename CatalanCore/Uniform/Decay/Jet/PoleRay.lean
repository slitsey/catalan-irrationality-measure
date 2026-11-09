module

public import CatalanCore.Uniform.Decay.Jet.PoleContour
public import CatalanCore.Uniform.Decay.Jet.PoleSeries

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
open scoped Polynomial
namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore.Uniform.Support

/-! Sum–integral interchange at every pole order. Frame is used only as a
carrier of shifts and crossing geometry; its integer weights are irrelevant. -/
open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos norm_inv_rayPt_le
  integrableOn_invsq norm_exp_ofReal_mul_I)

noncomputable def balancedRayBound (Fr : Frame) (c : Fin Fr.d → ℂ)
    (N0 : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  ∑ i, ‖c i‖ * (Fr.Dn N0 n i / Real.sqrt (kap2 θ) ^ 2)

theorem summable_balancedRayBound (Fr : Frame) (c : Fin Fr.d → ℂ) (N0 : ℕ) (θ : ℝ) :
    Summable (balancedRayBound Fr c N0 θ) := by
  unfold balancedRayBound
  apply summable_sum
  intro i _
  apply Summable.mul_left
  apply Summable.div_const
  have h := (CatalanCore.Decay.summable_pair_int ((Fr.xstar N0 : ℝ) : ℂ)
    (Fr.μ i : ℝ) Fr.cref).norm
  apply h.congr
  intro n
  unfold Frame.Dn
  congr 1
  push_cast
  rw [one_div, one_div]
  ring_nf

theorem balancedPoleTerm_eq_D (Fr : Frame) (c : Fin Fr.d → ℂ) (hc : ∑ i, c i = 0)
    (z : ℂ) (n : ℤ) :
    balancedPoleTerm c (fun i => (Fr.μ i : ℝ)) z n = -∑ i, c i *
      ((z - ((-(n : ℝ) - Fr.μ i : ℝ) : ℂ))⁻¹ -
        (z - ((-(n : ℝ) - Fr.cref : ℝ) : ℂ))⁻¹) := by
  rw [balancedPoleTerm_pair c _ hc z ((Fr.cref : ℝ) : ℂ) n]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  simp only [one_div]
  congr 2 <;> congr 1 <;> ring

theorem norm_balancedPoleTerm_ray_le (Fr : Frame) (c : Fin Fr.d → ℂ)
    (hc : ∑ i, c i = 0) (hC : Fr.ContourOK) (N0 : ℕ) (n : ℤ) {θ r : ℝ}
    (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖balancedPoleTerm c (fun i => (Fr.μ i : ℝ)) (rayPt (Fr.xstar N0) θ r) n‖ ≤
      balancedRayBound Fr c N0 θ n := by
  rw [balancedPoleTerm_eq_D Fr c hc, norm_neg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (Frame.norm_D_ray_le _ _ (Fr.pole_ne hC N0 n i) (Fr.cref_ne N0 n) hs hr) (norm_nonneg _)

theorem rayI_balancedPoleSeries_hasSum (Fr : Frame) (c : Fin Fr.d → ℂ)
    (hc : ∑ i, c i = 0) (hC : Fr.ContourOK) (N0 a b : ℕ) {θ : ℝ}
    (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI (Fr.xstar N0) θ
      (fun z => balancedPoleTerm c (fun i => (Fr.μ i : ℝ)) z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI (Fr.xstar N0) θ (fun z =>
        (∑' n : ℤ, balancedPoleTerm c (fun i => (Fr.μ i : ℝ)) z n) * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hK := Real.sqrt_pos.mpr (kap2_pos hs)
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  let K := Real.sqrt (kap2 θ)
  let x := Fr.xstar N0
  unfold rayI
  apply hasSum_integral_of_dominated_convergence
    (fun n r => balancedRayBound Fr c N0 θ n * ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2)))
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [balancedPoleTerm, rayPt]
    fun_prop
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 ≤ r := le_of_lt hr
    have hpos : 0 < K * ((Fr.xs : ℝ) + r) := by dsimp [K]; positivity
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_balancedPoleTerm_ray_le Fr c hc hC N0 n hs (le_of_lt hr)
    have h2 := Fr.norm_inv_ray_nat_le hC N0 a hs (le_of_lt hr)
    have h3 := Fr.norm_inv_ray_nat_le hC N0 b hs (le_of_lt hr)
    have hB : 0 ≤ balancedRayBound Fr c N0 θ n := by
      unfold balancedRayBound Frame.Dn
      positivity
    calc
      _ ≤ balancedRayBound Fr c N0 θ n *
          ((1 / (K * ((Fr.xs : ℝ) + r))) * (1 / (K * ((Fr.xs : ℝ) + r)))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity) hB
      _ = _ := by field_simp
  · exact Filter.Eventually.of_forall fun r => (summable_balancedRayBound Fr c N0 θ).mul_right _
  · have hI := (integrableOn_invsq (Fr.xs : ℝ) hxs).const_mul (1 / K ^ 2)
    have he : (fun r : ℝ => ∑' n : ℤ, balancedRayBound Fr c N0 θ n *
        ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2))) =
        fun r => (∑' n : ℤ, balancedRayBound Fr c N0 θ n) *
          ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2)) := by
      funext r
      exact tsum_mul_right
    rw [he]
    exact hI.const_mul _
  · exact Filter.Eventually.of_forall fun r =>
      ((summable_balancedPoleTerm c (fun i => (Fr.μ i : ℝ)) hc _).hasSum.mul_right _).mul_right _

noncomputable def higherRayBound (Fr : Frame) (N0 : ℕ) (θ : ℝ)
    (j : ℕ) (q : Fin Fr.d) (n : ℤ) : ℝ :=
  (1 / (Real.sqrt (kap2 θ)) ^ j) *
    (1 / |Fr.xstar N0 - (-(n : ℝ) - (Fr.μ q : ℝ))| ^ j)

theorem summable_higherRayBound (Fr : Frame) (N0 : ℕ) (θ : ℝ)
    (j : ℕ) (hj : 2 ≤ j) (q : Fin Fr.d) :
    Summable (higherRayBound Fr N0 θ j q) := by
  have h := (summable_higherPoleSeries j hj
    (((Fr.xstar N0 : ℝ) + (Fr.μ q : ℝ) : ℝ) : ℂ)).norm
  apply (h.mul_left (1 / (Real.sqrt (kap2 θ)) ^ j)).congr
  intro n
  simp only [higherRayBound, norm_div, norm_one, norm_pow]
  congr 2
  rw [show (((Fr.xstar N0 : ℝ) + (Fr.μ q : ℝ) : ℝ) : ℂ) + (n : ℂ) =
    (((Fr.xstar N0 : ℝ) - (-(n : ℝ) - (Fr.μ q : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

theorem norm_higherPoleTerm_ray_le (Fr : Frame) (hC : Fr.ContourOK) (N0 : ℕ)
    (j : ℕ) (q : Fin Fr.d) (n : ℤ) {θ r : ℝ}
    (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖1 / (rayPt (Fr.xstar N0) θ r + (n : ℂ) + (Fr.μ q : ℂ)) ^ j‖ ≤
      higherRayBound Fr N0 θ j q n := by
  have hK := Real.sqrt_pos.mpr (kap2_pos hs)
  have hp := Fr.pole_ne hC N0 n q
  have hdist : 0 < |Fr.xstar N0 - (-(n : ℝ) - (Fr.μ q : ℝ))| :=
    abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hp))
  have h := norm_inv_rayPt_le (x := Fr.xstar N0) (θ := θ)
    (-(n : ℝ) - (Fr.μ q : ℝ)) hp hs hr
  have hb : ‖(rayPt (Fr.xstar N0) θ r - ((-(n : ℝ) - (Fr.μ q : ℝ) : ℝ) : ℂ))⁻¹‖ ≤
      1 / (Real.sqrt (kap2 θ) * |Fr.xstar N0 - (-(n : ℝ) - (Fr.μ q : ℝ))|) := by
    apply h.trans
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hK.le
    linarith
  rw [show rayPt (Fr.xstar N0) θ r + (n : ℂ) + (Fr.μ q : ℂ) =
    rayPt (Fr.xstar N0) θ r - ((-(n : ℝ) - (Fr.μ q : ℝ) : ℝ) : ℂ) by push_cast; ring]
  rw [one_div, ← inv_pow, norm_pow]
  calc
    _ ≤ (1 / (Real.sqrt (kap2 θ) * |Fr.xstar N0 - (-(n : ℝ) - (Fr.μ q : ℝ))|)) ^ j :=
      pow_le_pow_left₀ (norm_nonneg _) hb j
    _ = _ := by unfold higherRayBound; rw [div_pow, mul_pow]; simp only [one_pow]; field_simp

theorem rayI_higherPoleSeries_hasSum (Fr : Frame) (hC : Fr.ContourOK)
    (N0 a b : ℕ) (j : ℕ) (hj : 2 ≤ j) (q : Fin Fr.d) {θ : ℝ}
    (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI (Fr.xstar N0) θ
      (fun z => (1 / (z + n + (Fr.μ q : ℂ)) ^ j) * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI (Fr.xstar N0) θ (fun z =>
        higherPoleSeries j (z + (Fr.μ q : ℂ)) * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hK := Real.sqrt_pos.mpr (kap2_pos hs)
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  let K := Real.sqrt (kap2 θ)
  let x := Fr.xstar N0
  unfold rayI
  apply hasSum_integral_of_dominated_convergence
    (fun n r => higherRayBound Fr N0 θ j q n * ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2)))
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [rayPt]
    fun_prop
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 ≤ r := le_of_lt hr
    have hpos : 0 < K * ((Fr.xs : ℝ) + r) := by dsimp [K]; positivity
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_higherPoleTerm_ray_le Fr hC N0 j q n hs (le_of_lt hr)
    have h2 := Fr.norm_inv_ray_nat_le hC N0 a hs (le_of_lt hr)
    have h3 := Fr.norm_inv_ray_nat_le hC N0 b hs (le_of_lt hr)
    have hB : 0 ≤ higherRayBound Fr N0 θ j q n := by unfold higherRayBound; positivity
    calc
      _ ≤ higherRayBound Fr N0 θ j q n *
          ((1 / (K * ((Fr.xs : ℝ) + r))) * (1 / (K * ((Fr.xs : ℝ) + r)))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity) hB
      _ = _ := by field_simp
  · exact Filter.Eventually.of_forall fun r => (summable_higherRayBound Fr N0 θ j hj q).mul_right _
  · have hI := (integrableOn_invsq (Fr.xs : ℝ) hxs).const_mul (1 / K ^ 2)
    have he : (fun r : ℝ => ∑' n : ℤ, higherRayBound Fr N0 θ j q n *
        ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2))) =
        fun r => (∑' n : ℤ, higherRayBound Fr N0 θ j q n) *
          ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2)) := by
      funext r
      exact tsum_mul_right
    rw [he]
    exact hI.const_mul _
  · refine Filter.Eventually.of_forall fun r => ?_
    have hh := ((summable_higherPoleSeries j hj (rayPt x θ r + (Fr.μ q : ℂ))).hasSum.mul_right
      ((rayPt x θ r - (a : ℂ))⁻¹ * (rayPt x θ r - (b : ℂ))⁻¹)).mul_right
        (Complex.exp ((θ : ℂ) * Complex.I))
    apply hh.congr_fun
    intro n
    rw [show rayPt x θ r + (Fr.μ q : ℂ) + (n : ℂ) =
      rayPt x θ r + n + (Fr.μ q : ℂ) by ring]

theorem rayI_sum_gPole {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (n : ι → ℕ) (p : ι → ℝ) {x θ a b : ℝ}
    (hp : ∀ i ∈ s, p i ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin θ ≠ 0) :
    rayI x θ (fun z => ∑ i ∈ s, c i * gPole (n i) (p i) a b z) =
      ∑ i ∈ s, c i * rayI x θ (gPole (n i) (p i) a b) := by
  unfold rayI
  simp only [Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum s (fun i hi =>
    (integrableOn_ray_gPole (n i) (hp i hi) ha hb hs).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_const_mul _ _

theorem contL_sum_gPole {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (n : ι → ℕ) (p : ι → ℝ) {x φ a b : ℝ}
    (hp : ∀ i ∈ s, p i ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin φ ≠ 0) :
    contL x φ (fun z => ∑ i ∈ s, c i * gPole (n i) (p i) a b z) =
      ∑ i ∈ s, c i * contL x φ (gPole (n i) (p i) a b) := by
  have hs' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.mpr hs
  unfold contL
  rw [rayI_sum_gPole s c n p hp ha hb hs', rayI_sum_gPole s c n p hp ha hb hs,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring


#print axioms summable_balancedRayBound
#print axioms rayI_balancedPoleSeries_hasSum
#print axioms summable_higherRayBound
#print axioms rayI_higherPoleSeries_hasSum
#print axioms contL_sum_gPole

end CatalanCore.Uniform.Decay.Jet
