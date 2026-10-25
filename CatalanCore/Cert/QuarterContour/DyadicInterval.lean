module
public import CatalanCore.Cert.QuarterCompute.DyadicInterval
public import Mathlib.Tactic
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.DyadicInterval
open CatalanCore.Cert.QuarterCompute.DyadicInterval

def Contains (H : ℤ) (a : Interval) (x : ℝ) : Prop := (a.1 : ℝ)/H ≤ x ∧ x ≤ (a.2 : ℝ)/H

lemma mul_between {a b x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    min (a*y) (b*y) ≤ x*y ∧ x*y ≤ max (a*y) (b*y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hy),
      (mul_le_mul_of_nonneg_right hb hy).trans (le_max_right _ _)⟩
  · have hy' : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb hy'),
      (mul_le_mul_of_nonpos_right ha hy').trans (le_max_left _ _)⟩

lemma rectangle_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have ha : min (a*c) (a*d) ≤ a*y ∧ a*y ≤ max (a*c) (a*d) := by
    simpa only [mul_comm] using (mul_between hy.1 hy.2 (y := a))
  have hb : min (b*c) (b*d) ≤ b*y ∧ b*y ≤ max (b*c) (b*d) := by
    simpa only [mul_comm] using (mul_between hy.1 hy.2 (y := b))
  have hxy := mul_between hx.1 hx.2 (y := y)
  constructor
  · exact (le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)).trans hxy.1
  · exact hxy.2.trans (max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _)))

lemma add_sound (H : ℤ) (a b : Interval) (x y : ℝ)
    (hx : Contains H a x) (hy : Contains H b y) : Contains H (add a b) (x+y) := by
  unfold Contains add at *
  push_cast
  constructor
  · simpa only [add_div] using add_le_add hx.1 hy.1
  · simpa only [add_div] using add_le_add hx.2 hy.2

lemma mul_sound (H : ℤ) (hH : 0 < H) (a b : Interval) (x y : ℝ)
    (hx : Contains H a x) (hy : Contains H b y) : Contains H (mul H a b) (x*y) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hxa : (a.1 : ℝ) ≤ x*H := (div_le_iff₀ hp).mp hx.1
  have hxb : x*H ≤ (a.2 : ℝ) := (le_div_iff₀ hp).mp hx.2
  have hya : (b.1 : ℝ) ≤ y*H := (div_le_iff₀ hp).mp hy.1
  have hyb : y*H ≤ (b.2 : ℝ) := (le_div_iff₀ hp).mp hy.2
  have hrect := rectangle_bounds ⟨hxa,hxb⟩ ⟨hya,hyb⟩
  have hlo : (prodLo a b : ℝ) ≤ (x*H)*(y*H) := by
    simpa only [prodLo,Int.cast_min,Int.cast_mul] using hrect.1
  have hhi : (x*H)*(y*H) ≤ (prodHi a b : ℝ) := by
    simpa only [prodHi,Int.cast_max,Int.cast_mul] using hrect.2
  have hfloor : ((prodLo a b/H : ℤ) : ℝ)*H ≤ (prodLo a b : ℝ) := by
    exact_mod_cast Int.ediv_mul_le (prodLo a b) (ne_of_gt hH)
  have hceil : (prodHi a b : ℝ) ≤ (ceilDiv (prodHi a b) H : ℝ)*H := by
    have h := Int.ediv_mul_le (-(prodHi a b)) (ne_of_gt hH)
    have hc : prodHi a b ≤ ceilDiv (prodHi a b) H*H := by unfold ceilDiv; nlinarith only [h]
    exact_mod_cast hc
  change (((prodLo a b/H : ℤ) : ℝ)/(H : ℝ) ≤ x*y) ∧ (x*y ≤ (ceilDiv (prodHi a b) H : ℝ)/(H : ℝ))
  constructor
  · apply (div_le_iff₀ hp).mpr
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith only [hfloor,hlo]
  · apply (le_div_iff₀ hp).mpr
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith only [hhi,hceil]

lemma encloseRatio_sound (H c d : ℤ) (hH : 0 < H) (hd : 0 < d) :
    Contains H (encloseRatio H c d) ((c : ℝ)/d) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : ((c*H/d : ℤ) : ℝ)*d ≤ (c : ℝ)*H := by
    exact_mod_cast Int.ediv_mul_le (c*H) (ne_of_gt hd)
  have hhi : (c : ℝ)*H ≤ (((c*H/d : ℤ)+1 : ℤ) : ℝ)*d := by
    exact_mod_cast (Int.lt_ediv_add_one_mul_self (c*H) hd).le
  constructor
  · exact (div_le_div_iff₀ hp hdp).mpr hlo
  · exact (div_le_div_iff₀ hdp hp).mpr hhi

noncomputable def evalReal (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | c::cs => c+x*evalReal x cs

lemma horner_sound (H : ℤ) (hH : 0 < H) (cs : List Interval) (rs : List ℝ)
    (hc : List.Forall₂ (Contains H) cs rs) (v : Interval) (x : ℝ) (hx : Contains H v x) :
    Contains H (horner H cs v) (evalReal x rs) := by
  induction hc with
  | nil => simp [horner,evalReal,Contains]
  | @cons c r cs rs hcr hcs ih =>
    exact add_sound H c (mul H v (horner H cs v)) r (x*evalReal x rs) hcr (mul_sound H hH v _ x _ hx ih)

lemma coefficients_sound (H d : ℤ) (hH : 0 < H) (hd : 0 < d) (cs : List ℤ)
    (v : Interval) (x : ℝ) (hx : Contains H v x) :
    Contains H (horner H (coefficients H d cs) v)
      (evalReal x (cs.map (fun c => (c : ℝ)/d))) := by
  apply horner_sound H hH _ _ _ v x hx
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact .cons (encloseRatio_sound H c d hH hd) ih

end CatalanCore.Cert.QuarterContour.DyadicInterval
#print axioms CatalanCore.Cert.QuarterContour.DyadicInterval.coefficients_sound