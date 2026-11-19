module
public import CatalanCore.Li2.NVMod.ResBase
public import CatalanCore.Li2.NVMod.ResRec
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

def omegaNumerator (C m : ℕ) : ℚ[X] :=
  ∑ b∈Icc 1 m,Polynomial.C (1/(b:ℚ)^2)*X^(C+b-m)

def liNumerator (O j : ℕ) : ℚ[X] :=
  if j=0 then X*(1-X)^(O-1) else
    ∑ i∈Icc 1 j,Polynomial.C ((Nat.stirlingSecond j i:ℚ)*(i.factorial:ℚ))*
      X^i*(1-X)^(O-(i+1))

theorem rationalMap_C (q : ℚ) :
    (algebraMap ℚ[X] (RatFunc ℚ)) (Polynomial.C q)=(q:RatFunc ℚ) :=
  rfPoly_C_rat q

theorem rationalMap_X : (algebraMap ℚ[X] (RatFunc ℚ)) X=rfX := rfl

theorem rfX_ne : (rfX:RatFunc ℚ)≠0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

theorem one_sub_rfX_ne : (1-rfX:RatFunc ℚ)≠0 := by
  have h : (1-X:ℚ[X])≠0 := by
    intro he
    have hh := congrArg (fun P : ℚ[X]=>P.coeff 0) he
    norm_num at hh
  have hh := RatFunc.algebraMap_ne_zero h
  simpa only [rfPoly,rfX,map_sub,map_one] using hh

theorem power_div_cancel (x v : RatFunc ℚ) (a b : ℕ) (hx : x≠0) (hb : b≤a) :
    x^a*(v/x^b)=v*x^(a-b) := by
  calc
    x^a*(v/x^b)=v*(x^a/x^b) := by ring
    _=v*x^(a-b) := by rw [pow_sub₀ x hx hb,div_eq_mul_inv]

theorem omegaNumerator_spec (C m : ℕ) (hm : m≤C) :
    rfPoly (omegaNumerator C m)=(rfX:RatFunc ℚ)^C*omegaRF m := by
  simp only [omegaNumerator,rfPoly,map_sum,map_mul,map_pow,omegaRF,Finset.mul_sum,
    rationalMap_C,rationalMap_X]
  apply Finset.sum_congr rfl
  intro b hb
  have he : (C:ℤ)+((b:ℤ)-m)=((C+b-m:ℕ):ℤ) := by
    have hbm := Finset.mem_Icc.mp hb
    omega
  have hp : (rfX:RatFunc ℚ)^C*rfX^((b:ℤ)-m)=rfX^(C+b-m) := by
    rw [←zpow_natCast,←zpow_add₀ rfX_ne,he,zpow_natCast]
  push_cast
  rw [←mul_div_assoc,hp]
  ring

theorem liNumerator_spec (O j : ℕ) (hj : j+1≤O) :
    rfPoly (liNumerator O j)=(1-rfX:RatFunc ℚ)^O*liNeg j rfX := by
  by_cases h0 : j=0
  · subst j
    simp only [liNumerator,liNeg,ite_true,rfPoly,map_mul,map_pow,map_sub,map_one,
      rationalMap_C,rationalMap_X]
    change rfX*(1-rfX:RatFunc ℚ)^(O-1)=(1-rfX)^O*(rfX/(1-rfX))
    simpa only [pow_one] using
      (power_div_cancel (1-rfX) rfX O 1 one_sub_rfX_ne hj).symm
  · simp only [liNumerator,liNeg,if_neg h0,rfPoly,map_sum,map_mul,map_pow,map_sub,map_one,
      Finset.mul_sum,rationalMap_C,rationalMap_X]
    apply Finset.sum_congr rfl
    intro i hi
    have hiO : i+1≤O := (Nat.add_le_add_right (Finset.mem_Icc.mp hi).2 1).trans hj
    push_cast
    exact (power_div_cancel (1-rfX)
      ((Nat.stirlingSecond j i:RatFunc ℚ)*(i.factorial:RatFunc ℚ)*rfX^i)
      O (i+1) one_sub_rfX_ne hiO).symm

#print axioms omegaNumerator_spec
#print axioms liNumerator_spec
end
end CatalanCore.Li2.NVMod.DataSupport
