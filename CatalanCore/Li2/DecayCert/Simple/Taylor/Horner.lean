module
public import CatalanCore.Li2.DecayCert.Simple.Taylor.Defs
public import CatalanCore.Li2.DecayCert.Lattice.Simple.Fixed
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert.LatticeSimple
noncomputable section
 theorem upMulF_sound (a b : ℤ) : dec S a*dec S b≤dec S (upMulF a b) := by
  have h:=div_le_div_of_nonneg_right (ceilDiv_ge (a*b) S S_pos.ne') S_real_pos.le
  convert h using 1 <;> simp only [dec,upMulF,Int.cast_mul] <;> ring
 theorem dec_nonneg_iff (a : ℤ) : 0≤dec S a ↔ 0≤a := by
  simp only [dec,le_div_iff₀ S_real_pos,zero_mul]
  constructor <;> intro h <;> exact_mod_cast h
 theorem upMulF_nonneg (a b : ℤ) (ha : 0≤a) (hb : 0≤b) : 0≤upMulF a b := by
  apply (dec_nonneg_iff _).mp
  exact (mul_nonneg ((dec_nonneg_iff _).mpr ha) ((dec_nonneg_iff _).mpr hb)).trans (upMulF_sound a b)
 def hornerF (R : ℤ) : List ℤ → ℤ
  | []=>0
  | a::xs=>a+upMulF (hornerF R xs) R
 theorem hornerF_nonneg (R : ℤ) (hR : 0≤R) (xs : List ℤ) (hx : ∀a∈xs,0≤a) :
    0≤hornerF R xs := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih =>
    exact add_nonneg (hx a (by simp))
      (upMulF_nonneg _ _ (ih (fun a ha=>hx a (by simp [ha]))) hR)
 theorem hornerF_sound (R : ℤ) (xs : List ℤ) (hx : ∀a∈xs,0≤a) (u : ℝ)
    (hu : |u|≤dec S R) : |evalModel (xs.map (dec S)) u|≤dec S (hornerF R xs) := by
  induction xs with
  | nil => simp [hornerF,evalModel,dec]
  | cons a xs ih =>
    have ht:=ih (fun a ha=>hx a (by simp [ha]))
    have ha : 0≤dec S a := (dec_nonneg_iff a).mpr (hx a (by simp))
    have hR : 0≤dec S R := (abs_nonneg u).trans hu
    have hmul:=mul_le_mul ht hu (abs_nonneg u) ((dec_nonneg_iff _).mpr
      (hornerF_nonneg R ((dec_nonneg_iff _).mp hR) xs (fun a ha=>hx a (by simp [ha]))))
    have hup:=upMulF_sound (hornerF R xs) R
    simp only [List.map_cons,evalModel_cons,hornerF,dec_add]
    have hh:=abs_add_le (dec S a) (u*evalModel (xs.map (dec S)) u)
    rw [abs_mul,abs_of_nonneg ha] at hh
    nlinarith
 theorem hornerF_fold (R : ℤ) (xs : List ℤ) :
    hornerF R xs=xs.reverse.foldl (fun acc a=>a+upMulF acc R) 0 := by
  rw [List.foldl_reverse]
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldr_cons,hornerF] using congrArg (fun v=>a+upMulF v R) ih
 theorem midpoint_error (a : FBox) (x : ℝ) (hx : Contains a x) :
    |x-dec S (midF a)|≤dec S (widthF a) := by
  have hl : dec S (midF a-a.1)≤dec S (widthF a) := by
    unfold dec widthF
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left (midF a-a.1) (a.2-midF a)) S_real_pos.le
  have hh : dec S (a.2-midF a)≤dec S (widthF a) := by
    unfold dec widthF
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_right (midF a-a.1) (a.2-midF a)) S_real_pos.le
  rw [dec_sub] at hl hh
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
#print axioms upMulF_sound
#print axioms hornerF_sound
#print axioms hornerF_fold
#print axioms midpoint_error
end
end CatalanCore.Li2.DecayCert.Simple
