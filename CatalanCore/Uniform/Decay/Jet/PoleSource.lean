module

public import CatalanCore.Uniform.Decay.Jet.Field
public import CatalanCore.Uniform.Decay.Jet.Decay
public import CatalanCore.Uniform.Decay.Jet.PoleSeries
public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Decay.Polygon.Bounds
public import CatalanCore.Uniform.Decay.Polygon.Data

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
open scoped Polynomial
open CatalanCore.Uniform.Decay.Polygon
open CatalanCore.Uniform.Decay.PolyChain

/-! Definitions from the frozen Q04 source/setup contract; no proof is assumed.
Permanent PoleSource owns these definitions and the complete closed analytic component; Source imports them and still owes the unconditional supplier.
-/
namespace CatalanCore.Uniform.Support
def PoleDatum.clearanceFrame (D : PoleDatum) (xs δ0 : ℚ) (n0 : ℕ) : Frame :=
  { d := D.n, μ := D.s, w := fun _ => 0, norm := 1,
    xs := xs, δ0 := δ0, n0off := n0,
    hμ := D.hs, hμinj := fun _ _ h hEq => h (D.hinj hEq),
    hw := by simp, hnorm := by norm_num }


-- D, S and R are PoleDatum, PoleGramSplit D, PoleRefMatch D Fr.

end CatalanCore.Uniform.Support

namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore CatalanCore.Uniform.Support
universe u

def poleHead (Fr : Frame) (N0 : ℕ) : Fr.XT N0 → Prop :=
  Sum.elim (fun _ => True) (fun _ => False)

instance poleHead_decidable (Fr : Frame) (N0 : ℕ) : DecidablePred (poleHead Fr N0) := by
  intro z
  cases z <;> simp only [poleHead, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

noncomputable def poleCenter {D : PoleDatum} {S : PoleGramSplit D} {Fr : Frame}
    (R : PoleRefMatch D S Fr) (N0 : ℕ) (pts : List ℂ) (dir : ℂ) :
    Fr.XT N0 → ℂ :=
  Sum.elim
    (fun p => -(p.1.1 : ℂ) - (D.s (R.role p.1.2).1 : ℂ))
    (fun z => polyPt Fr N0 pts dir (Sum.inr z))

noncomputable def poleCoefficients {D : PoleDatum} {Fr : Frame}
    (S : PoleGramSplit D) (R : PoleRefMatch D S Fr) (N0 : ℕ) :
    Fr.XT N0 → Fin (S.J + 1) → ℂ :=
  Sum.elim (fun p j => (S.coeff (R.role p.1.2) j : ℂ))
    (fun _ _ => 0)

noncomputable def poleRows {D : PoleDatum} {Fr : Frame}
    (S : PoleGramSplit D) (R : PoleRefMatch D S Fr)
    (N0 : ℕ) (pts : List ℂ) (dir : ℂ) : ℕ → Fr.XT N0 → ℂ :=
  jetRowFinite (poleHead Fr N0) S.J
    (poleCenter R N0 pts dir) (polyPt Fr N0 pts dir)
    (poleCoefficients S R N0)

-- The outer sum is over complete balanced rational increments δ(z+n),
-- not separate unbalanced simple-pole sums.
noncomputable def poleE (D : PoleDatum) (z : ℂ) : ℂ :=
  -(∑' n : ℤ, ∑ i : Fin D.n, ∑ j : Fin (D.w i),
    (D.coeff i ((j : ℕ) + 1) : ℂ) /
      (z + (n : ℂ) + (D.s i : ℂ)) ^ ((j : ℕ) + 1))

noncomputable def poleW {D : PoleDatum} {Fr : Frame}
    (S : PoleGramSplit D) (R : PoleRefMatch D S Fr)
    (N0 : ℕ) (pts : List ℂ) (dir : ℂ) : Fr.XT N0 → ℂ :=
  Sum.elim
    (fun p => (S.weight (R.role p.1.2) : ℂ))
    (Sum.elim
      (fun r => -((2 * Real.pi * Complex.I)⁻¹ *
        poleE D (pathPt dir ((Fr.xstar N0 : ℝ) : ℂ) pts r.1) *
        pathDer dir ((Fr.xstar N0 : ℝ) : ℂ) pts r.1))
      (fun r => (2 * Real.pi * Complex.I)⁻¹ *
        poleE D (pathPt (starRingEnd ℂ dir)
          ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1) *
        pathDer (starRingEnd ℂ dir)
          ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1))

structure FiniteJetHypotheses {L : Type u}
    (J : ℕ) (H C0 g d0 a : ℝ)
    (head : L → Prop) [DecidablePred head]
    (x y : L → ℂ) (A : L → Fin (J + 1) → ℂ) : Prop where
  center_real_neg : ∀ q, head q →
    (x q).im = 0 ∧ (x q).re ≤ -a
  reference_real : ∀ q, head q → (y q).im = 0
  displacement : ∀ q, head q → ‖x q - y q‖ ≤ C0
  coeff_bound : ∀ q, head q → ∀ j, ‖A q j‖ ≤ H
  contour_center : ∀ q, ¬head q → x q = y q
  head_sep : ∀ q q', head q → head q' → y q ≠ y q' →
    g ≤ ‖y q - y q'‖
  contour_gap : ∀ q q', head q → ¬head q' →
    d0 ≤ ‖y q - y q'‖
  reference_node_ne : ∀ q (t : ℕ), y q ≠ (t : ℂ)
  collision : ∀ q q', y q = y q' → ∀ t : ℕ,
    jetRowFinite head J x y A t q =
      jetRowFinite head J x y A t q'

structure PoleJetSetup (D : PoleDatum) (S : PoleGramSplit D)
    (Fr : Frame) (R : PoleRefMatch D S Fr)
    (N0 : ℕ) (pts : List ℂ) (dir : ℂ)
    (H C0 g d0 a : ℝ) : Prop where
  weight_ne : ∀ q, Fr.w q ≠ 0
  jet_hypotheses : FiniteJetHypotheses S.J H C0 g d0 a
    (poleHead Fr N0) (poleCenter R N0 pts dir)
    (polyPt Fr N0 pts dir) (poleCoefficients S R N0)



end CatalanCore.Uniform.Decay.Jet


namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore.Uniform.Support

/-! The frozen literal poleE is identified with a holomorphic closed source
only off the real axis, exactly where positive-parameter path labels lie. -/

noncomputable def poleTerm (D : PoleDatum) (z : ℂ) (n : ℤ) : ℂ :=
  -∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
    (D.coeff i j : ℂ) / (z + n + (D.s i : ℂ)) ^ j

noncomputable def poleHigherTerm (D : PoleDatum) (z : ℂ) (n : ℤ) : ℂ :=
  ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 2 (D.w i),
    (D.coeff i j : ℂ) / (z + n + (D.s i : ℂ)) ^ j

noncomputable def poleClosed (D : PoleDatum) (z : ℂ) : ℂ :=
  balancedPoleClosed (fun i => (D.coeff i 1 : ℂ)) (fun i => (D.s i : ℝ)) z -
    ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 2 (D.w i),
      (D.coeff i j : ℂ) * higherPoleClosed (j - 2) (z + (D.s i : ℂ))

theorem pole_simple_balance (D : PoleDatum) : ∑ i : Fin D.n, (D.coeff i 1 : ℂ) = 0 := by
  exact_mod_cast D.balance

theorem poleTerm_split (D : PoleDatum) (z : ℂ) (n : ℤ) :
    poleTerm D z n =
      balancedPoleTerm (fun i => (D.coeff i 1 : ℂ)) (fun i => (D.s i : ℝ)) z n -
        poleHigherTerm D z n := by
  have hset (i : Fin D.n) : Finset.Icc 1 (D.w i) = insert 1 (Finset.Icc 2 (D.w i)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    have := D.hw i
    omega
  have hnot : ∀ i : Fin D.n, 1 ∉ Finset.Icc 2 (D.w i) := by intro i; simp
  simp only [poleTerm, poleHigherTerm, balancedPoleTerm, hset, Finset.sum_insert (hnot _),
    pow_one, Finset.sum_add_distrib, Complex.ofReal_ratCast]
  ring

theorem summable_poleHigherTerm (D : PoleDatum) (z : ℂ) : Summable (poleHigherTerm D z) := by
  apply summable_sum
  intro i _
  apply summable_sum
  intro j hj
  have h := (summable_higherPoleSeries j (Finset.mem_Icc.mp hj).1 (z + (D.s i : ℂ))).mul_left
    (D.coeff i j : ℂ)
  apply h.congr
  intro n
  rw [show z + (D.s i : ℂ) + (n : ℂ) = z + n + (D.s i : ℂ) by ring]
  ring

theorem summable_poleTerm (D : PoleDatum) (z : ℂ) : Summable (poleTerm D z) := by
  have h := (summable_balancedPoleTerm (fun i => (D.coeff i 1 : ℂ))
    (fun i => (D.s i : ℝ)) (pole_simple_balance D) z).sub (summable_poleHigherTerm D z)
  apply h.congr
  intro n
  exact (poleTerm_split D z n).symm

theorem poleE_eq_tsum_poleTerm (D : PoleDatum) (z : ℂ) :
    poleE D z = ∑' n : ℤ, poleTerm D z n := by
  rw [poleE, ← tsum_neg]
  apply tsum_congr
  intro n
  unfold poleTerm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he := JetFrame.sum_Icc_shift'
    (fun j => (D.coeff i j : ℂ) / (z + (n : ℂ) + (D.s i : ℂ)) ^ j) (D.w i)
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (D.coeff i (j + 1) : ℂ) / (z + (n : ℂ) + (D.s i : ℂ)) ^ (j + 1)) (D.w i)]
  exact he.symm

theorem poleE_eq_closed (D : PoleDatum) {z : ℂ} (hz : z.im ≠ 0) :
    poleE D z = poleClosed D z := by
  rw [poleE_eq_tsum_poleTerm]
  have he : poleTerm D z = fun n =>
      balancedPoleTerm (fun i => (D.coeff i 1 : ℂ)) (fun i => (D.s i : ℝ)) z n -
        poleHigherTerm D z n := by
    funext n
    exact poleTerm_split D z n
  rw [he, (summable_balancedPoleTerm (fun i => (D.coeff i 1 : ℂ))
    (fun i => (D.s i : ℝ)) (pole_simple_balance D) z).tsum_sub (summable_poleHigherTerm D z)]
  rw [balancedPoleSeries_eq_cot _ _ (pole_simple_balance D)]
  · unfold poleClosed balancedPoleClosed
    congr 1
    unfold poleHigherTerm
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun j hj => by
      have h := (summable_higherPoleSeries j (Finset.mem_Icc.mp hj).1 (z + (D.s i : ℂ))).mul_left
        (D.coeff i j : ℂ)
      apply h.congr
      intro n
      simp only [mul_one_div]
      congr 2
      ring)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Summable.tsum_finsetSum (fun j hj => by
      have h := (summable_higherPoleSeries j (Finset.mem_Icc.mp hj).1 (z + (D.s i : ℂ))).mul_left
        (D.coeff i j : ℂ)
      apply h.congr
      intro n
      simp only [mul_one_div]
      congr 2
      ring)]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j - 2 + 2 = j := by have := (Finset.mem_Icc.mp hj).1; omega
    rw [← higherPoleSeries_eq_closed (j - 2) (by simpa using hz), hji]
    unfold higherPoleSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [mul_one_div]
    congr 2
    ring
  · intro i
    intro hmem
    obtain ⟨n, hn⟩ := (by simpa [Complex.integerComplement] using hmem :
      ∃ n : ℤ, (n : ℂ) = z + ((D.s i : ℝ) : ℂ))
    apply hz
    have he := congrArg Complex.im hn
    simpa using he.symm

noncomputable def poleK (D : PoleDatum) (κ : ℝ) : ℝ :=
  Real.pi * (∑ i : Fin D.n, ‖(D.coeff i 1 : ℂ)‖) / κ +
    ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 2 (D.w i),
      ‖(D.coeff i j : ℂ)‖ * higherPoleK (j - 2) κ

theorem poleK_nonneg (D : PoleDatum) {κ : ℝ} (hκ : 0 < κ) : 0 ≤ poleK D κ := by
  unfold poleK
  apply add_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (norm_nonneg _) (higherPoleK_nonneg _ hκ)

theorem norm_poleClosed_le (D : PoleDatum) {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hsin : ∀ i : Fin D.n, κ * Real.exp (Real.pi * |z.im|) ≤
      ‖Complex.sin ((Real.pi : ℂ) * (z + (D.s i : ℂ)))‖) :
    ‖poleClosed D z‖ ≤ poleK D κ * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hB := norm_balancedPoleClosed_le (fun i => (D.coeff i 1 : ℂ))
    (fun i => (D.s i : ℝ)) (pole_simple_balance D) hκ (by simpa using hsin)
  have hH : ‖∑ i : Fin D.n, ∑ j ∈ Finset.Icc 2 (D.w i),
      (D.coeff i j : ℂ) * higherPoleClosed (j - 2) (z + (D.s i : ℂ))‖ ≤
      (∑ i : Fin D.n, ∑ j ∈ Finset.Icc 2 (D.w i),
        ‖(D.coeff i j : ℂ)‖ * higherPoleK (j - 2) κ) *
          Real.exp (-(2 * Real.pi * |z.im|)) := by
    rw [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, mul_assoc]
    have hh := norm_higherPoleClosed_le (j - 2) hκ
      (z := z + (D.s i : ℂ)) (by simpa using hsin i)
    simp only [Complex.add_im, Complex.ratCast_im, add_zero] at hh
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
  exact (norm_sub_le _ _).trans ((add_le_add hB hH).trans_eq (by unfold poleK; ring))

theorem poleClosed_differentiableAt (D : PoleDatum) {z : ℂ}
    (hz : ∀ i : Fin D.n, Complex.sin ((Real.pi : ℂ) * (z + (D.s i : ℂ))) ≠ 0) :
    DifferentiableAt ℂ (poleClosed D) z := by
  unfold poleClosed balancedPoleClosed
  apply DifferentiableAt.sub
  · apply DifferentiableAt.neg
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.const_mul
    simp only [Complex.cot_eq_cos_div_sin]
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    simpa only [Complex.ofReal_ratCast] using hz i
  · apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.fun_sum
    intro j _
    exact ((hasDerivAt_higherPoleClosed (j - 2) (hz i)).comp z
      ((hasDerivAt_id z).add_const (D.s i : ℂ))).differentiableAt.const_mul _

noncomputable def poleSrc (D : PoleDatum) (a b : ℕ) (z : ℂ) : ℂ :=
  poleClosed D z * ((z - (a : ℂ))⁻¹ * (z - (b : ℂ))⁻¹)

theorem poleSrc_differentiableAt (D : PoleDatum) (a b : ℕ) {z : ℂ}
    (hz : ∀ i : Fin D.n, Complex.sin ((Real.pi : ℂ) * (z + (D.s i : ℂ))) ≠ 0)
    (ha : z - (a : ℂ) ≠ 0) (hb : z - (b : ℂ) ≠ 0) :
    DifferentiableAt ℂ (poleSrc D a b) z := by
  have ha' : DifferentiableAt ℂ (fun w : ℂ => (w - (a : ℂ))⁻¹) z :=
    (((hasDerivAt_id z).sub_const (a : ℂ)).inv ha).differentiableAt
  have hb' : DifferentiableAt ℂ (fun w : ℂ => (w - (b : ℂ))⁻¹) z :=
    (((hasDerivAt_id z).sub_const (b : ℂ)).inv hb).differentiableAt
  exact (poleClosed_differentiableAt D hz).mul (ha'.mul hb')

theorem norm_poleClosed_high (D : PoleDatum) {z : ℂ} (hz : 1 / 8 ≤ |z.im|) :
    ‖poleClosed D z‖ ≤ poleK D (1 / 4) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  apply norm_poleClosed_le D (by norm_num)
  intro i
  have hw : ((Real.pi : ℂ) * (z + (D.s i : ℂ))).im = Real.pi * z.im := by simp
  have hge : 3 / 8 ≤ |((Real.pi : ℂ) * (z + (D.s i : ℂ))).im| := by
    rw [hw, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have h := CatalanCore.Decay.norm_sin_ge _ hge
  rw [hw, abs_mul, abs_of_pos Real.pi_pos] at h
  linarith

theorem poleSrc_differentiableOn_halfP (D : PoleDatum) (σ : ℝ) (a b : ℕ) :
    DifferentiableOn ℂ (poleSrc D a b) (halfP σ) := by
  intro z hz
  have hi := im_ne_of_halfP hz
  have hp := poleFree_of_im_ne (Fr := D.clearanceFrame 1 1 0) hi
  exact (poleSrc_differentiableAt D a b hp (sub_nat_ne_of_im hi a)
    (sub_nat_ne_of_im hi b)).differentiableWithinAt

theorem poleSrc_differentiableOn_ball (D : PoleDatum) (xs δ0 : ℚ) (n0 : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) (N0 a b : ℕ) :
    DifferentiableOn ℂ (poleSrc D a b)
      (Metric.ball (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ)
        (diskR (D.clearanceFrame xs δ0 n0))) := by
  intro z hz
  have hz0 : z ∈ Metric.ball (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) (δ0 : ℝ) :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hp := poleFree_of_ball hC N0 hz0
  exact (poleSrc_differentiableAt D a b hp (node_ne_of_ball hC N0 a hz)
    (node_ne_of_ball hC N0 b hz)).differentiableWithinAt

theorem poleSrc_decay (D : PoleDatum) {σ : ℝ} (hσ : |σ| = 1) (a b : ℕ) :
    ∀ z : ℂ, 1 ≤ σ * z.im → ‖poleSrc D a b z‖ ≤ poleK D (1 / 4) / (σ * z.im) ^ 2 := by
  intro z hz
  have habs : |z.im| = σ * z.im := by
    rw [← one_mul |z.im|, ← hσ, ← abs_mul]
    exact abs_of_pos (by linarith)
  have hi : z.im ≠ 0 := by intro h; rw [h, mul_zero] at hz; linarith
  have hE := norm_poleClosed_high D (z := z) (by rw [habs]; linarith)
  have hex : Real.exp (-(2 * Real.pi * |z.im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, abs_nonneg z.im]
  have hK := poleK_nonneg D (by norm_num : (0 : ℝ) < 1 / 4)
  have hE' : ‖poleClosed D z‖ ≤ poleK D (1 / 4) := hE.trans (by nlinarith)
  unfold poleSrc
  rw [norm_mul, norm_mul]
  have h1 := norm_inv_sub_nat_le hi a
  have h2 := norm_inv_sub_nat_le hi b
  rw [habs] at h1 h2
  calc
    _ ≤ poleK D (1 / 4) * ((1 / (σ * z.im)) * (1 / (σ * z.im))) :=
      mul_le_mul hE' (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by positivity) hK
    _ = _ := by field_simp

theorem poleSrc_path (D : PoleDatum) (xs δ0 : ℚ) (n0 : ℕ)
    (hC : (D.clearanceFrame xs δ0 n0).ContourOK) (N0 a b : ℕ)
    {σ : ℝ} (hσ : |σ| = 1) {pts : List ℂ} {d : ℂ}
    (hpts : ∀ z ∈ pts, 0 < σ * z.im) (hd : 0 < σ * d.im) :
    IntegrableOn (fun u => poleSrc D a b
      (pathPt d (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts u) *
        pathDer d (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts u) (Set.Ioi 0) ∧
    (∫ u in Set.Ioi (0 : ℝ), poleSrc D a b
      (pathPt d (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts u) *
        pathDer d (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts u) =
      polyI (poleSrc D a b) (((D.clearanceFrame xs δ0 n0).xstar N0 : ℝ) : ℂ) pts d := by
  exact pathInt_of_deform (by simp) (diskR_pos hC)
    (poleSrc_differentiableOn_halfP D σ a b)
    (poleSrc_differentiableOn_ball D xs δ0 n0 hC N0 a b) pts hpts hd
    (poleK_nonneg D (by norm_num)) (poleSrc_decay D hσ a b)


#print axioms summable_poleTerm
#print axioms poleE_eq_tsum_poleTerm
#print axioms poleE_eq_closed
#print axioms norm_poleClosed_le
#print axioms poleClosed_differentiableAt
#print axioms poleSrc_decay
#print axioms poleSrc_path

end CatalanCore.Uniform.Decay.Jet
