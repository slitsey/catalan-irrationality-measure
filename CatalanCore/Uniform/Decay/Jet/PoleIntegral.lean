module

public import CatalanCore.Uniform.Decay.Jet.PoleSource
public import CatalanCore.Uniform.Decay.Jet.PoleGram
public import CatalanCore.Uniform.Decay.Jet.PoleRay

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
open scoped Polynomial
open CatalanCore.Uniform.Decay.Polygon
open CatalanCore.Uniform.Decay.PolyChain

namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore.Uniform.Support

/-! The full grouped reflection source has a summable ray majorant. -/
open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos integrableOn_invsq)

noncomputable def poleRayBound (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 : ℕ)
    (θ : ℝ) (n : ℤ) : ℝ :=
  balancedRayBound (D.clearanceFrame xs δ0 n0) (fun i => (D.coeff i 1 : ℂ)) N0 θ n +
    ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 2 (D.w i),
      ‖(D.coeff i j : ℂ)‖ * higherRayBound (D.clearanceFrame xs δ0 n0) N0 θ j i n

theorem summable_poleRayBound (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 : ℕ) (θ : ℝ) :
    Summable (poleRayBound D xs δ0 n0 N0 θ) := by
  apply Summable.add (summable_balancedRayBound _ _ _ _)
  apply summable_sum
  intro i _
  apply summable_sum
  intro j hj
  exact (summable_higherRayBound (D.clearanceFrame xs δ0 n0) N0 θ j
    (Finset.mem_Icc.mp hj).1 i).mul_left ‖(D.coeff i j : ℂ)‖

theorem poleRayBound_nonneg (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 : ℕ) (θ : ℝ) (n : ℤ) :
    0 ≤ poleRayBound D xs δ0 n0 N0 θ n := by
  unfold poleRayBound balancedRayBound Frame.Dn higherRayBound
  positivity

theorem norm_poleTerm_ray_le (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) (n : ℤ) {θ r : ℝ}
    (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖poleTerm D (rayPt ((D.clearanceFrame xs δ0 n0).xstar N0) θ r) n‖ ≤
      poleRayBound D xs δ0 n0 N0 θ n := by
  rw [poleTerm_split]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact norm_balancedPoleTerm_ray_le (D.clearanceFrame xs δ0 n0)
      (fun i => (D.coeff i 1 : ℂ)) (pole_simple_balance D) hC N0 n hs hr
  · unfold poleHigherTerm
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [div_eq_mul_inv, norm_mul]
    have he := norm_higherPoleTerm_ray_le (D.clearanceFrame xs δ0 n0) hC N0 j i n hs hr
    simp only [one_div] at he
    exact mul_le_mul_of_nonneg_left he (norm_nonneg _)

theorem rayI_poleTerm_hasSum (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI ((D.clearanceFrame xs δ0 n0).xstar N0) θ
      (fun z => poleTerm D z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI ((D.clearanceFrame xs δ0 n0).xstar N0) θ (poleSrc D a b)) := by
  let F := D.clearanceFrame xs δ0 n0
  let x := F.xstar N0
  let K := Real.sqrt (kap2 θ)
  have hK : 0 < K := Real.sqrt_pos.mpr (kap2_pos hs)
  have hxs : (0 : ℝ) < xs := by exact_mod_cast hC.xs_pos
  unfold rayI
  apply hasSum_integral_of_dominated_convergence
    (fun n r => poleRayBound D xs δ0 n0 N0 θ n * ((1 / K ^ 2) * (1 / ((xs : ℝ) + r) ^ 2)))
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [poleTerm, rayPt]
    fun_prop
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 ≤ r := le_of_lt hr
    have hpos : 0 < K * ((xs : ℝ) + r) := by positivity
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_poleTerm_ray_le D xs δ0 n0 N0 hC n hs hr0
    have h2 := F.norm_inv_ray_nat_le hC N0 a hs hr0
    have h3 := F.norm_inv_ray_nat_le hC N0 b hs hr0
    calc
      _ ≤ poleRayBound D xs δ0 n0 N0 θ n *
          ((1 / (K * ((xs : ℝ) + r))) * (1 / (K * ((xs : ℝ) + r)))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity)
          (poleRayBound_nonneg D xs δ0 n0 N0 θ n)
      _ = _ := by field_simp
  · exact Filter.Eventually.of_forall fun r => (summable_poleRayBound D xs δ0 n0 N0 θ).mul_right _
  · have hI := (integrableOn_invsq (xs : ℝ) hxs).const_mul (1 / K ^ 2)
    have he : (fun r : ℝ => ∑' n : ℤ, poleRayBound D xs δ0 n0 N0 θ n *
        ((1 / K ^ 2) * (1 / ((xs : ℝ) + r) ^ 2))) =
        fun r => (∑' n : ℤ, poleRayBound D xs δ0 n0 N0 θ n) *
          ((1 / K ^ 2) * (1 / ((xs : ℝ) + r) ^ 2)) := by
      funext r
      exact tsum_mul_right
    rw [he]
    exact hI.const_mul _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    have him : (rayPt x θ r).im ≠ 0 := by
      simp only [rayPt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, zero_add]
      exact mul_ne_zero (ne_of_gt hr) hs
    have he : (∑' n : ℤ, poleTerm D (rayPt x θ r) n) = poleClosed D (rayPt x θ r) :=
      (poleE_eq_tsum_poleTerm D _).symm.trans (poleE_eq_closed D him)
    have hh := ((summable_poleTerm D (rayPt x θ r)).hasSum.mul_right
      ((rayPt x θ r - (a : ℂ))⁻¹ * (rayPt x θ r - (b : ℂ))⁻¹)).mul_right
        (Complex.exp ((θ : ℂ) * Complex.I))
    rw [he] at hh
    exact hh

abbrev PoleOrderLabel (D : PoleDatum) := (i : Fin D.n) × Fin (D.w i)

theorem poleTerm_fin (D : PoleDatum) (z : ℂ) (n : ℤ) :
    poleTerm D z n = -∑ i : Fin D.n, ∑ j : Fin (D.w i),
      (D.coeff i (j.val + 1) : ℂ) / (z + n + (D.s i : ℂ)) ^ (j.val + 1) := by
  unfold poleTerm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (D.coeff i (j + 1) : ℂ) / (z + (n : ℂ) + (D.s i : ℂ)) ^ (j + 1)) (D.w i)]
  exact JetFrame.sum_Icc_shift' _ _

theorem poleTerm_kernel_eq (D : PoleDatum) (n : ℤ) (a b : ℕ) :
    (fun z : ℂ => poleTerm D z n * ((z - a)⁻¹ * (z - b)⁻¹)) =
      fun z => ∑ q : PoleOrderLabel D, -(D.coeff q.1 (q.2.val + 1) : ℂ) *
        gPole q.2.val (-(n : ℝ) - (D.s q.1 : ℝ)) (a : ℝ) (b : ℝ) z := by
  funext z
  rw [poleTerm_fin, Fintype.sum_sigma]
  simp only [Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [gPole]
  push_cast
  rw [show z - (-(n : ℂ) - (D.s i : ℂ)) = z + n + (D.s i : ℂ) by ring]
  rw [div_eq_mul_inv, ← inv_pow]
  ring

noncomputable def poleTailTerm (D : PoleDatum) (xs : ℚ) (N0 a b m : ℕ) : ℝ :=
  ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
    if (N0 : ℝ) + xs < (m : ℝ) + (D.s i : ℝ)
    then (D.coeff i j : ℝ) * poleAtom j (D.s i : ℝ) a b m else 0

noncomputable def poleHeadTerm (D : PoleDatum) (xs : ℚ) (N0 a b m : ℕ) : ℝ :=
  ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
    if (N0 : ℝ) + xs < (m : ℝ) + (D.s i : ℝ)
    then 0 else (D.coeff i j : ℝ) * poleAtom j (D.s i : ℝ) a b m

theorem poleHeadTerm_add_tail (D : PoleDatum) (xs : ℚ) (N0 a b m : ℕ) :
    poleHeadTerm D xs N0 a b m + poleTailTerm D xs N0 a b m = poleAtomSum D a b m := by
  unfold poleHeadTerm poleTailTerm poleAtomSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem poleHeadTerm_eq_zero (D : PoleDatum) (xs : ℚ) (N0 a b m : ℕ)
    (hm : N0 + ⌈(xs : ℝ)⌉₊ ≤ m) : poleHeadTerm D xs N0 a b m = 0 := by
  have hceil : (xs : ℝ) ≤ ⌈(xs : ℝ)⌉₊ := Nat.le_ceil _
  have hmm : (N0 : ℝ) + (⌈(xs : ℝ)⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
  unfold poleHeadTerm
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hs : (0 : ℝ) < (D.s i : ℝ) := by exact_mod_cast (D.hs i).1
  rw [if_pos (by linarith)]

theorem contL_poleTerm_negative (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) (n : ℤ) (hn : n < 0)
    {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi) :
    contL ((D.clearanceFrame xs δ0 n0).xstar N0) φ
      (fun z => poleTerm D z n * ((z - a)⁻¹ * (z - b)⁻¹)) = 0 := by
  let F := D.clearanceFrame xs δ0 n0
  have hs : Real.sin φ ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  rw [poleTerm_kernel_eq, contL_sum_gPole Finset.univ _ _ _
    (fun q _ => F.pole_ne hC N0 n q.1)
    (F.xstar_lt_nat hC N0 a).ne' (F.xstar_lt_nat hC N0 b).ne' hs]
  apply Finset.sum_eq_zero
  intro q _
  have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
  have hμ : (D.s q.1 : ℝ) ≤ 1 := by exact_mod_cast (D.hs q.1).2
  have hxs : (0 : ℝ) < xs := by exact_mod_cast hC.xs_pos
  have hx : F.xstar N0 < -(n : ℝ) - (D.s q.1 : ℝ) := by
    dsimp [F, Frame.xstar, PoleDatum.clearanceFrame]
    have hN : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
    linarith
  rw [contL_gPole_east q.2.val _ _ _ _ _ h1 h2 hx
    (F.xstar_lt_nat hC N0 a) (F.xstar_lt_nat hC N0 b), mul_zero]

theorem contL_poleTerm_nat (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b m : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {φ : ℝ}
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi) :
    contL ((D.clearanceFrame xs δ0 n0).xstar N0) φ
      (fun z => poleTerm D z (m : ℤ) * ((z - a)⁻¹ * (z - b)⁻¹)) =
      (2 * Real.pi * I) * (poleTailTerm D xs N0 a b m : ℂ) := by
  let F := D.clearanceFrame xs δ0 n0
  have hs : Real.sin φ ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  rw [poleTerm_kernel_eq, contL_sum_gPole Finset.univ _ _ _
    (fun q _ => F.pole_ne hC N0 (m : ℤ) q.1)
    (F.xstar_lt_nat hC N0 a).ne' (F.xstar_lt_nat hC N0 b).ne' hs,
    Fintype.sum_sigma]
  unfold poleTailTerm
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hf := JetFrame.sum_Icc_shift'
    (fun j => (if (N0 : ℝ) + xs < (m : ℝ) + (D.s i : ℝ)
      then (D.coeff i j : ℝ) * poleAtom j (D.s i : ℝ) a b m else 0)) (D.w i)
  have hfc := congrArg (fun t : ℝ => (t : ℂ)) hf
  push_cast at hfc
  rw [hfc, Finset.sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hsp : (0 : ℝ) < (D.s i : ℝ) := by exact_mod_cast (D.hs i).1
  have hpa : -(m : ℝ) - (D.s i : ℝ) ≠ (a : ℝ) := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hpb : -(m : ℝ) - (D.s i : ℝ) ≠ (b : ℝ) := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    linarith
  have hder : ((j.val.factorial : ℂ)⁻¹) *
      iteratedDeriv j.val (poleKernel (a : ℝ) (b : ℝ)) (-(m : ℝ) - (D.s i : ℝ)) =
        (poleAtom (j.val + 1) (D.s i : ℝ) a b m : ℂ) := by
    rw [poleKernel_iteratedDeriv j.val _ _ hpa hpb]
    simpa only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_ratCast] using normalized_kernel_atom j.val hsp a b m
  have hp := F.pole_ne hC N0 (m : ℤ) i
  simp only [Int.cast_natCast] at hp ⊢
  change -(m : ℝ) - (D.s i : ℝ) ≠ F.xstar N0 at hp
  rw [contL_gPole j.val _ _ _ _ _ h1 h2 hp
    (F.xstar_lt_nat hC N0 a) (F.xstar_lt_nat hC N0 b)]
  by_cases ht : (N0 : ℝ) + xs < (m : ℝ) + (D.s i : ℝ)
  · have hw : -(m : ℝ) - (D.s i : ℝ) < F.xstar N0 := by
      dsimp [F, Frame.xstar, PoleDatum.clearanceFrame]
      linarith
    rw [if_pos hw, if_pos ht]
    push_cast
    calc
      _ = (2 * Real.pi * I) * (D.coeff i (j.val + 1) : ℂ) *
          (((j.val.factorial : ℂ)⁻¹) *
            iteratedDeriv j.val (poleKernel (a : ℝ) (b : ℝ)) (-(m : ℝ) - (D.s i : ℝ))) := by ring
      _ = _ := by rw [hder]; ring
  · have hw : ¬ (-(m : ℝ) - (D.s i : ℝ) < F.xstar N0) := by
      dsimp [F, Frame.xstar, PoleDatum.clearanceFrame]
      linarith
    rw [if_neg hw, if_neg ht]
    simp

theorem hasSum_poleTail (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {φ : ℝ}
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi) :
    HasSum (fun m : ℕ => (poleTailTerm D xs N0 a b m : ℂ))
      ((2 * Real.pi * I)⁻¹ * contL ((D.clearanceFrame xs δ0 n0).xstar N0) φ (poleSrc D a b)) := by
  have hs : Real.sin φ ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hs' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.mpr hs
  have hh := ((rayI_poleTerm_hasSum D xs δ0 n0 N0 a b hC hs').sub
    (rayI_poleTerm_hasSum D xs δ0 n0 N0 a b hC hs)).mul_left ((2 * Real.pi * I)⁻¹)
  have he (n : ℤ) (hn : n ∉ Set.range (Nat.cast : ℕ → ℤ)) :
      (2 * Real.pi * I)⁻¹ *
        (rayI ((D.clearanceFrame xs δ0 n0).xstar N0) (-φ)
          (fun z => poleTerm D z n * ((z - a)⁻¹ * (z - b)⁻¹)) -
         rayI ((D.clearanceFrame xs δ0 n0).xstar N0) φ
          (fun z => poleTerm D z n * ((z - a)⁻¹ * (z - b)⁻¹))) = 0 := by
    have hn' : n < 0 := by
      by_contra h
      exact hn ⟨n.toNat, by simp [Int.toNat_of_nonneg (not_lt.mp h)]⟩
    rw [← contL, contL_poleTerm_negative D xs δ0 n0 N0 a b hC n hn' h1 h2, mul_zero]
  have hnat := (Nat.cast_injective.hasSum_iff he).mpr hh
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  apply hnat.congr_fun
  intro m
  have heq : (2 * Real.pi * I)⁻¹ *
      (rayI ((D.clearanceFrame xs δ0 n0).xstar N0) (-φ)
        (fun z => poleTerm D z (m : ℤ) * ((z - a)⁻¹ * (z - b)⁻¹)) -
       rayI ((D.clearanceFrame xs δ0 n0).xstar N0) φ
        (fun z => poleTerm D z (m : ℤ) * ((z - a)⁻¹ * (z - b)⁻¹))) =
        (poleTailTerm D xs N0 a b m : ℂ) := by
    rw [← contL, contL_poleTerm_nat D xs δ0 n0 N0 a b m hC h1 h2,
      ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  first
  | simpa only [Function.comp_apply] using heq
  | simpa only [Function.comp_apply] using heq.symm

noncomputable def poleHeadSum (D : PoleDatum) (xs : ℚ) (N0 a b : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (N0 + ⌈(xs : ℝ)⌉₊), poleHeadTerm D xs N0 a b m

theorem pole_contour_identity (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {φ : ℝ}
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi) :
    ((∑' m : ℕ, poleAtomSum D a b m : ℝ) : ℂ) =
      (poleHeadSum D xs N0 a b : ℂ) + (2 * Real.pi * I)⁻¹ *
        contL ((D.clearanceFrame xs δ0 n0).xstar N0) φ (poleSrc D a b) := by
  have hT := hasSum_poleTail D xs δ0 n0 N0 a b hC h1 h2
  have hH : HasSum (fun m : ℕ => (poleHeadTerm D xs N0 a b m : ℂ))
      (∑ m ∈ Finset.range (N0 + ⌈(xs : ℝ)⌉₊), (poleHeadTerm D xs N0 a b m : ℂ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro m hm
    rw [poleHeadTerm_eq_zero D xs N0 a b m (by simpa using hm)]
    simp
  have hh := hH.add hT
  have he (m : ℕ) : (poleHeadTerm D xs N0 a b m : ℂ) +
      (poleTailTerm D xs N0 a b m : ℂ) = (poleAtomSum D a b m : ℂ) := by
    rw [← Complex.ofReal_add, poleHeadTerm_add_tail]
  simp only [he] at hh
  rw [Complex.ofReal_tsum, hh.tsum_eq]
  unfold poleHeadSum
  push_cast
  rfl

theorem pole_upper_deform (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {pts : List ℂ} {d : ℂ}
    (hpts : ∀ z ∈ pts, 0 < z.im) (hd : 0 < d.im) :
    polyI (poleSrc D a b) (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts d =
      rayI ((D.clearanceFrame xs δ0 n0).xstar N0) phiRef (poleSrc D a b) := by
  rw [rayI_eq_rayInt]
  refine deform (σ := 1) (δ := diskR (D.clearanceFrame xs δ0 n0)) (by simp) (diskR_pos hC)
    (poleSrc_differentiableOn_halfP D 1 a b)
    (poleSrc_differentiableOn_ball D xs δ0 n0 hC N0 a b) pts
    (fun z hz => by simpa using hpts z hz) (by simpa using hd) ?_
    (poleK_nonneg D (by norm_num)) (poleSrc_decay D (by simp) a b)
  rw [one_mul, Complex.exp_ofReal_mul_I_im]
  exact sin_phiRef_pos

theorem pole_lower_deform (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {pts : List ℂ} {d : ℂ}
    (hpts : ∀ z ∈ pts, 0 < z.im) (hd : 0 < d.im) :
    polyI (poleSrc D a b) (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ)
      (conjL pts) ((starRingEnd ℂ) d) =
      rayI ((D.clearanceFrame xs δ0 n0).xstar N0) (-phiRef) (poleSrc D a b) := by
  rw [rayI_eq_rayInt]
  refine deform (σ := -1) (δ := diskR (D.clearanceFrame xs δ0 n0)) (by simp) (diskR_pos hC)
    (poleSrc_differentiableOn_halfP D (-1) a b)
    (poleSrc_differentiableOn_ball D xs δ0 n0 hC N0 a b) (conjL pts)
    (fun z hz => ?_) (by simpa using hd) ?_
    (poleK_nonneg D (by norm_num)) (poleSrc_decay D (by simp) a b)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    simpa using hpts w hw
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    linarith [sin_phiRef_pos]

theorem pole_gram_formula (D : PoleDatum) (xs δ0 : ℚ) (n0 N0 a b : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) {pts : List ℂ} {d : ℂ}
    (hpts : ∀ z ∈ pts, 0 < z.im) (hd : 0 < d.im) :
    (((lw D.f D.e a b : ℝ) + if a = b then D.xi else 0 : ℝ) : ℂ) =
      (poleHeadSum D xs N0 a b : ℂ) + (2 * Real.pi * I)⁻¹ *
        (polyI (poleSrc D a b) (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ)
            (conjL pts) ((starRingEnd ℂ) d) -
         polyI (poleSrc D a b) (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts d) := by
  have h := pole_contour_identity D xs δ0 n0 N0 a b hC phiRef_gt phiRef_lt
  rw [poleAtomSum_gram] at h
  rw [pole_upper_deform D xs δ0 n0 N0 a b hC hpts hd,
    pole_lower_deform D xs δ0 n0 N0 a b hC hpts hd]
  exact h


#print axioms rayI_poleTerm_hasSum
#print axioms poleTerm_kernel_eq
#print axioms contL_poleTerm_negative
#print axioms contL_poleTerm_nat
#print axioms hasSum_poleTail
#print axioms pole_contour_identity
#print axioms pole_gram_formula

end CatalanCore.Uniform.Decay.Jet
