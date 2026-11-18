module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1000000
open Polynomial
namespace CatalanCore.Li2.NVMod.DataSupport
variable {R : Type*} [CommRing R]

noncomputable def coefficientsPoly : List R→R[X]
  | []=>0
  | a::as=>C a+X*coefficientsPoly as

def coefficientsAdd : List R→List R→List R
  | [],ys=>ys
  | xs,[]=>xs
  | x::xs,y::ys=>(x+y)::coefficientsAdd xs ys

def coefficientsScale (c : R) (xs : List R) : List R := xs.map (c*·)

def coefficientsMul : List R→List R→List R
  | [],_=>[]
  | a::as,bs=>coefficientsAdd (coefficientsScale a bs) (0::coefficientsMul as bs)

theorem coefficientsPoly_add (xs ys : List R) :
    coefficientsPoly (coefficientsAdd xs ys)=coefficientsPoly xs+coefficientsPoly ys := by
  induction xs generalizing ys with
  | nil=>simp [coefficientsAdd,coefficientsPoly]
  | cons a as ih=>
    cases ys with
    | nil=>simp [coefficientsAdd,coefficientsPoly]
    | cons b bs=>simp only [coefficientsAdd,coefficientsPoly,ih,map_add];ring

theorem coefficientsPoly_scale (c : R) (xs : List R) :
    coefficientsPoly (coefficientsScale c xs)=C c*coefficientsPoly xs := by
  induction xs with
  | nil=>simp [coefficientsScale,coefficientsPoly]
  | cons a as ih=>simp only [coefficientsScale,List.map_cons,coefficientsPoly,map_mul] at *;rw [ih];ring

theorem coefficientsPoly_mul (xs ys : List R) :
    coefficientsPoly (coefficientsMul xs ys)=coefficientsPoly xs*coefficientsPoly ys := by
  induction xs with
  | nil=>simp [coefficientsMul,coefficientsPoly]
  | cons a as ih=>
    rw [coefficientsMul,coefficientsPoly_add,coefficientsPoly_scale,coefficientsPoly,ih,
      coefficientsPoly]
    simp only [map_zero,zero_add]
    ring

theorem coefficientsPoly_map {S : Type*} [CommRing S] (f : R→+*S) (xs : List R) :
    (coefficientsPoly xs).map f=coefficientsPoly (xs.map f) := by
  induction xs with
  | nil=>simp [coefficientsPoly]
  | cons a as ih=>simp [coefficientsPoly,ih]

theorem coefficientsPoly_coeff (xs : List R) (j : ℕ) :
    (coefficientsPoly xs).coeff j=xs.getD j 0 := by
  induction xs generalizing j with
  | nil=>simp [coefficientsPoly]
  | cons a as ih=>
    cases j with
    | zero=>simp [coefficientsPoly]
    | succ j=>simp [coefficientsPoly,Polynomial.coeff_X_mul,ih]

def linearProductCoefficients : List R→List R
  | []=>[1]
  | a::as=>coefficientsMul [a,1] (linearProductCoefficients as)

theorem linearProductCoefficients_spec (xs : List R) :
    coefficientsPoly (linearProductCoefficients xs)=(xs.map (fun a=>X+C a)).prod := by
  induction xs with
  | nil=>simp [linearProductCoefficients,coefficientsPoly]
  | cons a as ih=>
    simp only [linearProductCoefficients,coefficientsPoly_mul,ih,List.map_cons,List.prod_cons]
    congr 1
    simp [coefficientsPoly,add_comm]
#print axioms coefficientsPoly_mul
#print axioms linearProductCoefficients_spec
end CatalanCore.Li2.NVMod.DataSupport
