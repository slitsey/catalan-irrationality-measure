module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialFamily
public import CatalanCore.Li2.NVMod.InfinityWeight
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

def evalJet2 {R : Type*} [CommRing R] (x : R) : List R→R×R×R
  | []=>(0,0,0)
  | a::as=>let j:=evalJet2 x as;(a+x*j.1,j.1+x*j.2.1,2*j.2.1+x*j.2.2)

theorem evalJet2_spec {R : Type*} [CommRing R] (xs : List R) (x : R) :
    (evalJet2 x xs).1=(coefficientsPoly xs).eval x ∧
    (evalJet2 x xs).2.1=(coefficientsPoly xs).derivative.eval x ∧
    (evalJet2 x xs).2.2=(coefficientsPoly xs).derivative.derivative.eval x := by
  induction xs with
  | nil=>simp [evalJet2,coefficientsPoly]
  | cons a as ih=>
    refine ⟨?_,?_,?_⟩ <;>
      simp [evalJet2,coefficientsPoly,Polynomial.derivative_mul,ih.1,ih.2.1,ih.2.2] <;> ring

theorem intJet2_spec (xs : List ℤ) (x : ℤ) :
    ((coefficientsPoly xs).map (Int.castRingHom ℚ)).eval (x:ℚ)=((evalJet2 x xs).1:ℚ) ∧
    ((coefficientsPoly xs).map (Int.castRingHom ℚ)).derivative.eval (x:ℚ)=((evalJet2 x xs).2.1:ℚ) ∧
    ((coefficientsPoly xs).map (Int.castRingHom ℚ)).derivative.derivative.eval (x:ℚ)=((evalJet2 x xs).2.2:ℚ) := by
  have h:=evalJet2_spec xs x
  refine ⟨?_,?_,?_⟩
  · rw [map_eval_int]
    exact congrArg (fun z : ℤ=>(z:ℚ)) h.1.symm
  · rw [Polynomial.derivative_map,map_eval_int]
    exact congrArg (fun z : ℤ=>(z:ℚ)) h.2.1.symm
  · rw [Polynomial.derivative_map,Polynomial.derivative_map,map_eval_int]
    exact congrArg (fun z : ℤ=>(z:ℚ)) h.2.2.symm

theorem eval_derivative_fraction (F : RatFunc ℚ) (P Q : ℚ[X]) (x : ℚ)
    (hQ : Q.eval x≠0) (hF : F=rfPoly P/rfPoly Q) :
    rfEval (rfDeriv F) x=(P.derivative.eval x*Q.eval x-P.eval x*Q.derivative.eval x)/(Q.eval x)^2 := by
  have hq : Q≠0:=by intro hz;apply hQ;simp [hz]
  have hd : rfDeriv F=rfPoly (P.derivative*Q-P*Q.derivative)/rfPoly (Q^2) := by
    simpa only [rfPoly,map_pow] using rfDeriv_fraction F P Q hq hF
  have he:=rfEval_fraction (rfDeriv F) (P.derivative*Q-P*Q.derivative) (Q^2) x
    (pow_ne_zero 2 hq) (by simpa using pow_ne_zero 2 hQ) hd
  simpa only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow] using he

theorem logarithmic_fraction (F : RatFunc ℚ) (P Q : ℚ[X]) (hP : P≠0) (hQ : Q≠0)
    (hF : F=rfPoly P/rfPoly Q) :
    rfDeriv F/F=rfPoly (P.derivative*Q-P*Q.derivative)/rfPoly (P*Q) := by
  have hp : rfPoly P≠0:=RatFunc.algebraMap_ne_zero hP
  have hq : rfPoly Q≠0:=RatFunc.algebraMap_ne_zero hQ
  rw [rfDeriv_fraction F P Q hQ hF,hF]
  simp only [rfPoly,map_mul,map_sub] at hp hq ⊢
  field_simp [hp,hq]
  <;> ring

theorem fraction_log_jet (F : RatFunc ℚ) (P Q : ℚ[X]) (x : ℚ)
    (hP : P.eval x≠0) (hQ : Q.eval x≠0) (hF : F=rfPoly P/rfPoly Q) :
    rfEval F x=P.eval x/Q.eval x ∧
    rfEval (rfDeriv F/F) x=P.derivative.eval x/P.eval x-Q.derivative.eval x/Q.eval x ∧
    rfEval (rfDeriv (rfDeriv F/F)) x=
      P.derivative.derivative.eval x/P.eval x-(P.derivative.eval x/P.eval x)^2-
        Q.derivative.derivative.eval x/Q.eval x+(Q.derivative.eval x/Q.eval x)^2 := by
  have hp : P≠0:=by intro hz;apply hP;simp [hz]
  have hq : Q≠0:=by intro hz;apply hQ;simp [hz]
  let S:=P.derivative*Q-P*Q.derivative
  let T:=P*Q
  have ht : T.eval x≠0:=by simpa only [T,Polynomial.eval_mul] using mul_ne_zero hP hQ
  have ht0 : T≠0:=mul_ne_zero hp hq
  have hl : rfDeriv F/F=rfPoly S/rfPoly T:=logarithmic_fraction F P Q hp hq hF
  refine ⟨rfEval_fraction F P Q x hq hQ hF,?_,?_⟩
  · rw [rfEval_fraction _ S T x ht0 ht hl]
    simp only [S,T,Polynomial.eval_sub,Polynomial.eval_mul]
    field_simp [hP,hQ]
    <;> ring
  · rw [eval_derivative_fraction _ S T x ht hl]
    simp only [S,T,Polynomial.derivative_sub,Polynomial.derivative_mul,
      Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul]
    field_simp [hP,hQ]
    <;> ring
#print axioms fraction_log_jet
#print axioms intJet2_spec
end
end CatalanCore.Li2.NVMod.DataSupport
