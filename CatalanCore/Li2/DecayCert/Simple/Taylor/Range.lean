module
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Horner
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Quadratic
/-! Range soundness of the fused lattice evaluator: `modelRangeF` encloses every function that an
`IntTaylorModel` represents (`ModelsF`) on `|u| ≤ radius`. -/
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section

/-- `m` encloses `f` on `|u| ≤ r`: real coefficients in the boxes, remainder `m.remainder/S`. -/
def ModelsF (m : IntTaylorModel) (r : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ a : List ℝ, List.Forall₂ Contains m.coeff a ∧
    ∀ u : ℝ, |u| ≤ r → |f u-evalModel a u| ≤ dec S m.remainder

theorem evalModel_nil' (u : ℝ) : evalModel [] u=0 := by simp [evalModel]

/-- Perturbation bound by the upward Horner value. -/
theorem evalModel_abs_le (R : ℤ) (e : List ℝ) (w : List ℤ)
    (h : List.Forall₂ (fun x b => |x| ≤ dec S b) e w) (u : ℝ) (hu : |u| ≤ dec S R) :
    |evalModel e u| ≤ dec S (hornerF R w) := by
  induction h with
  | nil => simp [evalModel_nil',hornerF,dec]
  | @cons x b xs ws hx _ ih =>
    rw [evalModel_cons]
    simp only [hornerF,dec_add]
    have hR : 0 ≤ dec S R := (abs_nonneg u).trans hu
    have h1 : |u*evalModel xs u| ≤ dec S R*dec S (hornerF R ws) := by
      rw [abs_mul]
      exact mul_le_mul hu ih (abs_nonneg _) hR
    have h2 := upMulF_sound (hornerF R ws) R
    have h3 := abs_add_le x (u*evalModel xs u)
    rw [mul_comm (dec S R)] at h1
    linarith

theorem evalModel_mid_le (R : ℤ) (cs : List FBox) (a : List ℝ) (h : List.Forall₂ Contains cs a)
    (u : ℝ) (hu : |u| ≤ dec S R) :
    |evalModel a u-evalModel (cs.map (fun c => dec S (midF c))) u| ≤ dec S (hornerF R (cs.map widthF)) := by
  induction h with
  | nil => simp [evalModel_nil',hornerF,dec]
  | @cons c x cs xs hx _ ih =>
    simp only [List.map_cons,evalModel_cons,hornerF,dec_add]
    have hR : 0 ≤ dec S R := (abs_nonneg u).trans hu
    have h0 := midpoint_error c x hx
    have h1 : |u*(evalModel xs u-evalModel (cs.map (fun c => dec S (midF c))) u)| ≤
        dec S R*dec S (hornerF R (cs.map widthF)) := by
      rw [abs_mul]
      exact mul_le_mul hu ih (abs_nonneg _) hR
    have h2 := upMulF_sound (hornerF R (cs.map widthF)) R
    have he : x+u*evalModel xs u-(dec S (midF c)+u*evalModel (cs.map (fun c => dec S (midF c))) u)=
        (x-dec S (midF c))+u*(evalModel xs u-evalModel (cs.map (fun c => dec S (midF c))) u) := by ring
    rw [he]
    have h3 := abs_add_le (x-dec S (midF c)) (u*(evalModel xs u-evalModel (cs.map (fun c => dec S (midF c))) u))
    rw [mul_comm (dec S R)] at h1
    linarith

theorem evalModel_mid_split (l : List FBox) (u : ℝ) :
    evalModel (l.map (fun c => dec S (midF c))) u=
      dec S (midF (l[0]?.getD boxZero))+u*evalModel ((l.drop 1).map (fun c => dec S (midF c))) u := by
  cases l with
  | nil => simp [evalModel_nil',midF,boxZero,dec]
  | cons c l => simp [evalModel_cons]

theorem upMulF_mono_abs (A R : ℤ) (x u : ℝ) (hx : |x| ≤ dec S A) (hu : |u| ≤ dec S R) :
    |u*x| ≤ dec S (upMulF A R) := by
  rw [abs_mul]
  have hA : 0 ≤ dec S A := (abs_nonneg x).trans hx
  calc |u| * |x| ≤ dec S R*dec S A := mul_le_mul hu hx (abs_nonneg _) ((abs_nonneg u).trans hu)
    _ = dec S A*dec S R := mul_comm _ _
    _ ≤ dec S (upMulF A R) := upMulF_sound A R

theorem modelUpperF_sound (R : ℤ) (m : IntTaylorModel) (r : ℝ) (f : ℝ → ℝ) (hm : ModelsF m r f)
    (u : ℝ) (hu : |u| ≤ r) (hR : r ≤ dec S R) : f u ≤ dec S (modelUpperF R m) := by
  obtain ⟨a,ha,hf⟩ := hm
  have huR : |u| ≤ dec S R := hu.trans hR
  have h1 := (abs_le.mp (hf u hu)).2
  have h2 := (abs_le.mp (evalModel_mid_le R m.coeff a ha u huR)).2
  have e0 := evalModel_mid_split m.coeff u
  have e1 : evalModel ((m.coeff.drop 1).map (fun c => dec S (midF c))) u=
      dec S (midF (m.coeff[1]?.getD boxZero))+u*evalModel ((m.coeff.drop 2).map (fun c => dec S (midF c))) u := by
    simpa using evalModel_mid_split (m.coeff.drop 1) u
  have e2 : evalModel ((m.coeff.drop 2).map (fun c => dec S (midF c))) u=
      dec S (midF (m.coeff[2]?.getD boxZero))+u*evalModel ((m.coeff.drop 3).map (fun c => dec S (midF c))) u := by
    simpa using evalModel_mid_split (m.coeff.drop 2) u
  have ht0 : |evalModel ((m.coeff.drop 3).map (fun c => dec S (midF c))) u| ≤
      dec S (hornerF R ((m.coeff.drop 3).map (fun c => |midF c|))) := by
    apply evalModel_abs_le R _ _ _ u huR
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro c _
    rw [dec_abs S (midF c) S_pos]
  have ht := upMulF_mono_abs _ R _ u
    (upMulF_mono_abs _ R _ u (upMulF_mono_abs _ R _ u ht0 huR) huR) huR
  have hq := qmaxF_sound (midF (m.coeff[1]?.getD boxZero)) (midF (m.coeff[2]?.getD boxZero)) R u huR
  have hw : (m.coeff.reverse.foldl (fun acc a => widthF a+upMulF acc R) 0)=hornerF R (m.coeff.map widthF) := by
    rw [hornerF_fold,List.foldl_reverse,List.foldl_reverse,List.foldr_map]
  have hd : ((m.coeff.drop 3).reverse.foldl (fun acc a => |midF a|+upMulF acc R) 0)=
      hornerF R ((m.coeff.drop 3).map (fun c => |midF c|)) := by
    rw [hornerF_fold,List.foldl_reverse,List.foldl_reverse,List.foldr_map]
  unfold modelUpperF
  simp only [hw,hd,dec_add]
  have hT := (le_abs_self _).trans ht
  rw [e0,e1,e2] at h2
  nlinarith [hT,hq,h1,h2]

theorem evalModel_neg (a : List ℝ) (u : ℝ) : evalModel (a.map (fun x => -x)) u=-evalModel a u := by
  induction a with
  | nil => simp [evalModel_nil']
  | cons x a ih => simp only [List.map_cons,evalModel_cons,ih]; ring

theorem modelsF_neg (m : IntTaylorModel) (r : ℝ) (f : ℝ → ℝ) (hm : ModelsF m r f) :
    ModelsF ⟨m.coeff.map boxNegF,m.remainder⟩ r (fun u => -f u) := by
  obtain ⟨a,ha,hf⟩ := hm
  refine ⟨a.map (fun x => -x),?_,?_⟩
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    exact ha.imp (fun c x h => boxNegF_sound c x h)
  · intro u hu
    rw [evalModel_neg]
    have := hf u hu
    rw [show -f u - -evalModel a u=-(f u-evalModel a u) by ring,abs_neg]
    exact this

/-- `modelRangeF` encloses every function the model represents. -/
theorem modelRangeF_sound (radius : ℚ) (m : IntTaylorModel) (f : ℝ → ℝ) (hm : ModelsF m radius f)
    (u : ℝ) (hu : |u| ≤ radius) :
    dec S (modelRangeF radius m).1 ≤ f u ∧ f u ≤ dec S (modelRangeF radius m).2 := by
  have hR : (radius:ℝ) ≤ dec S (boxOfQ radius).2 := (boxOfQ_sound radius).2
  constructor
  · have h := modelUpperF_sound _ _ _ _ (modelsF_neg m radius f hm) u hu hR
    simp only [modelRangeF]
    rw [show dec S (-modelUpperF (boxOfQ radius).2 ⟨m.coeff.map boxNegF,m.remainder⟩)=
      -dec S (modelUpperF (boxOfQ radius).2 ⟨m.coeff.map boxNegF,m.remainder⟩) by simp [dec,neg_div]]
    linarith
  · exact modelUpperF_sound _ _ _ _ hm u hu hR

#print axioms modelRangeF_sound
end
end CatalanCore.Li2.DecayCert.Simple
