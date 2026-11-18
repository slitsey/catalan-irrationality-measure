module
public import CatalanCore.Li2.DecayCert.RealCells
public import CatalanMeasure.GenD.Signed.TaylorCell
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial Set MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeSimple
open CatalanMeasure.GenD.Signed.TaylorCell
noncomputable section

def upperMul (S a b : ℤ) : ℤ := fm S a b+1

def hornerUpper (S R : ℤ) : List ℤ→ℤ
  | []=>0
  | a::rest=>|a|+upperMul S R (hornerUpper S R rest)

theorem upperMul_sound (S a b : ℤ) (hS : 0<S) :
    dec S a*dec S b≤dec S (upperMul S a b) := by
  have hh := (abs_lt.mp (fm_spec S a b hS)).1
  have he : dec S (upperMul S a b)=dec S (fm S a b)+1/(S:ℝ) := by
    simp only [upperMul,dec,Int.cast_add,Int.cast_one,add_div]
  rw [he]
  linarith

theorem dec_abs (S a : ℤ) (hS : 0<S) : dec S |a|=|dec S a| := by
  have hSR : (0:ℝ)<(S:ℝ) := by exact_mod_cast hS
  simp only [dec,Int.cast_abs,abs_div,abs_of_pos hSR]

theorem evalModel_cons (a : ℝ) (xs : List ℝ) (u : ℝ) :
    evalModel (a::xs) u=a+u*evalModel xs u := by
  unfold evalModel
  rw [List.length_cons,Finset.sum_range_succ']
  simp only [List.getElem!_cons_zero,pow_zero,mul_one,List.getElem!_cons_succ,pow_succ]
  rw [Finset.mul_sum,add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem hornerUpper_sound (S R : ℤ) (hS : 0<S) (xs : List ℤ) (u : ℝ)
    (hu : |u|≤dec S R) :
    |evalModel (xs.map (dec S)) u|≤dec S (hornerUpper S R xs) := by
  have hR : 0≤dec S R := (abs_nonneg u).trans hu
  induction xs with
  | nil => simp [hornerUpper,evalModel,dec]
  | cons a xs ih =>
    simp only [List.map_cons,evalModel_cons]
    have hmul : |u| *|evalModel (xs.map (dec S)) u|≤dec S R*dec S (hornerUpper S R xs) :=
      mul_le_mul hu ih (abs_nonneg _) hR
    have hupp:=upperMul_sound S R (hornerUpper S R xs) hS
    have habs:=abs_add_le (dec S a) (u*evalModel (xs.map (dec S)) u)
    rw [abs_mul] at habs
    calc
      _≤|dec S a|+dec S (upperMul S R (hornerUpper S R xs)) := by linarith
      _=dec S (hornerUpper S R (a::xs)) := by
        simp only [hornerUpper,dec_add,dec_abs S a hS]

noncomputable def gridQ (S a : ℤ) : ℚ := (a:ℚ)/(S:ℚ)

def fixedUpper (S R E a0 a1 a2 : ℤ) (tail : List ℤ) : ℚ :=
  ((a0+hornerUpper S R (0::0::0::tail)+E:ℤ):ℚ)/(S:ℚ)+
    quadSupQ ((a1:ℚ)/(S:ℚ)) ((a2:ℚ)/(S:ℚ)) ((R:ℚ)/(S:ℚ))

theorem gridQ_cast (S a : ℤ) : (gridQ S a:ℝ)=dec S a := by simp [gridQ,dec]

theorem evalModel_split_three (S a0 a1 a2 : ℤ) (tail : List ℤ) (u : ℝ) :
    evalModel ((a0::a1::a2::tail).map (dec S)) u=
      dec S a0+dec S a1*u+dec S a2*u^2+
        evalModel ((0::0::0::tail).map (dec S)) u := by
  simp only [List.map_cons,evalModel_cons,dec,Int.cast_zero,zero_div,zero_add]
  ring

theorem fixedUpper_sound (S R E a0 a1 a2 : ℤ) (tail : List ℤ) (hS : 0<S)
    (f : ℝ→ℝ) (hm : Models f ((a0::a1::a2::tail).map (dec S)) (dec S R) (dec S E))
    (u : ℝ) (hu : |u|≤dec S R) : f u≤(fixedUpper S R E a0 a1 a2 tail:ℝ) := by
  have he := (abs_le.mp (hm.2.2 u hu)).2
  have ht := (le_abs_self (evalModel ((0::0::0::tail).map (dec S)) u)).trans
    (hornerUpper_sound S R hS (0::0::0::tail) u hu)
  have hq := quad_le_quadSupR (dec S a1) (dec S a2) (dec S R) u hu
  have hqc : (quadSupQ ((a1:ℚ)/(S:ℚ)) ((a2:ℚ)/(S:ℚ)) ((R:ℚ)/(S:ℚ)):ℝ)=
      quadSupR (dec S a1) (dec S a2) (dec S R) := by
    rw [quadSupQ_cast]
    simp only [Rat.cast_div,Rat.cast_intCast,dec]
  rw [evalModel_split_three] at he
  have hbound : (fixedUpper S R E a0 a1 a2 tail:ℝ)=
      dec S a0+dec S (hornerUpper S R (0::0::0::tail))+dec S E+
        quadSupR (dec S a1) (dec S a2) (dec S R) := by
    simp only [fixedUpper,Rat.cast_add,Rat.cast_div,Rat.cast_intCast,Int.cast_add,add_div,hqc,dec]
  rw [hbound]
  linarith
#print axioms hornerUpper_sound
#print axioms fixedUpper_sound
end
end CatalanCore.Li2.DecayCert.LatticeSimple
