module
public import CatalanCore.Li2.NVMod.RationalCalculus
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem rfPoly_ne_zero {P : ℚ[X]} (hP : P≠0) : rfPoly P≠0 := RatFunc.algebraMap_ne_zero hP
private theorem canonical_fraction (F : RatFunc ℚ) : F=rfPoly F.num/rfPoly F.denom :=
  (RatFunc.num_div_denom F).symm
theorem rfDeriv_poly (P : ℚ[X]) : rfDeriv (rfPoly P)=rfPoly P.derivative := by
  rw [rfDeriv_fraction (rfPoly P) P 1 (by norm_num) (by simp [rfPoly])]
  simp only [Polynomial.derivative_one,mul_one,mul_zero,sub_zero,rfPoly,map_one,one_pow,div_one]
theorem rfDeriv_zero : rfDeriv 0=0 := by
  have hh:=rfDeriv_poly (0:ℚ[X])
  simpa only [rfPoly,map_zero,Polynomial.derivative_zero] using hh
theorem rfDeriv_add (F G : RatFunc ℚ) : rfDeriv (F+G)=rfDeriv F+rfDeriv G := by
  have hF := rfPoly_ne_zero (RatFunc.denom_ne_zero F)
  have hG := rfPoly_ne_zero (RatFunc.denom_ne_zero G)
  simp only [rfPoly] at hF hG
  have hsum : F+G=rfPoly (F.num*G.denom+F.denom*G.num)/rfPoly (F.denom*G.denom) := by
    calc
      _=rfPoly F.num/rfPoly F.denom+rfPoly G.num/rfPoly G.denom :=
        congrArg₂ (fun x y : RatFunc ℚ=>x+y) (canonical_fraction F) (canonical_fraction G)
      _=_ := by
        simp only [rfPoly,map_add,map_mul]
        field_simp [hF,hG]
        <;> ring
  rw [rfDeriv_fraction (F+G) _ _ (mul_ne_zero (RatFunc.denom_ne_zero F) (RatFunc.denom_ne_zero G)) hsum]
  unfold rfDeriv
  simp only [Polynomial.derivative_add,Polynomial.derivative_mul,rfPoly,map_add,map_mul,map_sub]
  field_simp [hF,hG]
  <;> ring
theorem rfDeriv_mul (F G : RatFunc ℚ) : rfDeriv (F*G)=rfDeriv F*G+F*rfDeriv G := by
  have hF := rfPoly_ne_zero (RatFunc.denom_ne_zero F)
  have hG := rfPoly_ne_zero (RatFunc.denom_ne_zero G)
  simp only [rfPoly] at hF hG
  have hprod : F*G=rfPoly (F.num*G.num)/rfPoly (F.denom*G.denom) := by
    calc
      _=(rfPoly F.num/rfPoly F.denom)*(rfPoly G.num/rfPoly G.denom) :=
        congrArg₂ (fun x y : RatFunc ℚ=>x*y) (canonical_fraction F) (canonical_fraction G)
      _=_ := by simp only [rfPoly,map_mul];ring
  rw [rfDeriv_fraction (F*G) _ _ (mul_ne_zero (RatFunc.denom_ne_zero F) (RatFunc.denom_ne_zero G)) hprod]
  have hR : rfDeriv F*G+F*rfDeriv G=
      rfDeriv F*(rfPoly G.num/rfPoly G.denom)+(rfPoly F.num/rfPoly F.denom)*rfDeriv G :=
    congrArg₂ (fun x y : RatFunc ℚ=>x+y)
      (congrArg (fun x : RatFunc ℚ=>rfDeriv F*x) (canonical_fraction G))
      (congrArg (fun x : RatFunc ℚ=>x*rfDeriv G) (canonical_fraction F))
  rw [hR]
  unfold rfDeriv
  simp only [Polynomial.derivative_mul,rfPoly,map_mul,map_sub,map_add]
  field_simp [hF,hG]
  <;> ring
theorem rfDeriv_sum {ι : Type*} (S : Finset ι) (f : ι→RatFunc ℚ) :
    rfDeriv (∑ i∈S,f i)=∑ i∈S,rfDeriv (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,rfDeriv_zero]
  | @insert i S hi ih => rw [Finset.sum_insert hi,rfDeriv_add,ih,Finset.sum_insert hi]
def RFRegular (x : ℚ) (F : RatFunc ℚ) : Prop := F.denom.eval x≠0
theorem RFRegular.fraction (x : ℚ) (P Q : ℚ[X]) (hQ : Q≠0) (hx : Q.eval x≠0) :
    RFRegular x (rfPoly P/rfPoly Q) := by
  obtain ⟨T,hT⟩:=RatFunc.denom_div_dvd P Q
  intro hz
  simp only [rfPoly] at hz
  apply hx
  rw [hT,Polynomial.eval_mul,hz,zero_mul]
theorem RFRegular.poly (x : ℚ) (P : ℚ[X]) : RFRegular x (rfPoly P) := by
  simpa only [rfPoly,map_one,div_one] using RFRegular.fraction x P 1 (by norm_num) (by norm_num)
private theorem canonical_add (F G : RatFunc ℚ) :
    F+G=rfPoly (F.num*G.denom+F.denom*G.num)/rfPoly (F.denom*G.denom) := by
  have hF:=rfPoly_ne_zero (RatFunc.denom_ne_zero F)
  have hG:=rfPoly_ne_zero (RatFunc.denom_ne_zero G)
  simp only [rfPoly] at hF hG
  calc
    _=rfPoly F.num/rfPoly F.denom+rfPoly G.num/rfPoly G.denom :=
      congrArg₂ (fun x y : RatFunc ℚ=>x+y) (canonical_fraction F) (canonical_fraction G)
    _=_ := by simp only [rfPoly,map_mul,map_add];field_simp [hF,hG] <;> ring
private theorem canonical_mul (F G : RatFunc ℚ) :
    F*G=rfPoly (F.num*G.num)/rfPoly (F.denom*G.denom) := by
  calc
    _=(rfPoly F.num/rfPoly F.denom)*(rfPoly G.num/rfPoly G.denom) :=
      congrArg₂ (fun x y : RatFunc ℚ=>x*y) (canonical_fraction F) (canonical_fraction G)
    _=_ := by simp only [rfPoly,map_mul];ring
theorem RFRegular.add {x : ℚ} {F G : RatFunc ℚ} (hF : RFRegular x F) (hG : RFRegular x G) :
    RFRegular x (F+G) := by
  rw [canonical_add]
  apply RFRegular.fraction x _ _ (mul_ne_zero (RatFunc.denom_ne_zero F) (RatFunc.denom_ne_zero G))
  simpa only [Polynomial.eval_mul] using mul_ne_zero hF hG
theorem RFRegular.mul {x : ℚ} {F G : RatFunc ℚ} (hF : RFRegular x F) (hG : RFRegular x G) :
    RFRegular x (F*G) := by
  rw [canonical_mul]
  apply RFRegular.fraction x _ _ (mul_ne_zero (RatFunc.denom_ne_zero F) (RatFunc.denom_ne_zero G))
  simpa only [Polynomial.eval_mul] using mul_ne_zero hF hG
theorem RFRegular.deriv {x : ℚ} {F : RatFunc ℚ} (hF : RFRegular x F) : RFRegular x (rfDeriv F) := by
  have hp : rfDeriv F=rfPoly (F.num.derivative*F.denom-F.num*F.denom.derivative)/rfPoly (F.denom^2) := by
    simp only [rfDeriv,rfPoly,map_pow]
  rw [hp]
  apply RFRegular.fraction x _ _ (pow_ne_zero 2 (RatFunc.denom_ne_zero F))
  simpa only [Polynomial.eval_pow] using pow_ne_zero 2 hF
theorem rfEval_poly (P : ℚ[X]) (x : ℚ) : rfEval (rfPoly P) x=P.eval x := by
  have hh:=rfEval_fraction (rfPoly P) P 1 x (by norm_num) (by norm_num) (by simp [rfPoly])
  simpa only [Polynomial.eval_one,div_one] using hh
theorem rfEval_zero (x : ℚ) : rfEval 0 x=0 := by
  simpa only [rfPoly,map_zero,Polynomial.eval_zero] using rfEval_poly (0:ℚ[X]) x
theorem rfEval_add {x : ℚ} {F G : RatFunc ℚ} (hF : RFRegular x F) (hG : RFRegular x G) :
    rfEval (F+G) x=rfEval F x+rfEval G x := by
  have hh:=rfEval_fraction (F+G) (F.num*G.denom+F.denom*G.num) (F.denom*G.denom) x
    (mul_ne_zero (RatFunc.denom_ne_zero F) (RatFunc.denom_ne_zero G))
    (by simpa only [Polynomial.eval_mul] using mul_ne_zero hF hG) (canonical_add F G)
  rw [hh]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,rfEval]
  change F.denom.eval x≠0 at hF
  change G.denom.eval x≠0 at hG
  field_simp [hF,hG]
  <;> ring
theorem rfEval_mul {x : ℚ} {F G : RatFunc ℚ} (hF : RFRegular x F) (hG : RFRegular x G) :
    rfEval (F*G) x=rfEval F x*rfEval G x := by
  have hh:=rfEval_fraction (F*G) (F.num*G.num) (F.denom*G.denom) x
    (mul_ne_zero (RatFunc.denom_ne_zero F) (RatFunc.denom_ne_zero G))
    (by simpa only [Polynomial.eval_mul] using mul_ne_zero hF hG) (canonical_mul F G)
  rw [hh]
  simp only [Polynomial.eval_mul,rfEval]
  ring
theorem RFRegular.sum {ι : Type*} (S : Finset ι) (f : ι→RatFunc ℚ) (x : ℚ)
    (h : ∀ i∈S,RFRegular x (f i)) : RFRegular x (∑ i∈S,f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,rfPoly,map_zero] using RFRegular.poly x (0:ℚ[X])
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
theorem rfEval_sum {ι : Type*} (S : Finset ι) (f : ι→RatFunc ℚ) (x : ℚ)
    (h : ∀ i∈S,RFRegular x (f i)) : rfEval (∑ i∈S,f i) x=∑ i∈S,rfEval (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,rfEval_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,rfEval_add (h i (Finset.mem_insert_self _ _))
      (RFRegular.sum S f x (fun j hj=>h j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)),Finset.sum_insert hi]
#print axioms rfDeriv_poly
#print axioms rfDeriv_add
#print axioms rfDeriv_mul
#print axioms rfDeriv_sum
#print axioms RFRegular.deriv
#print axioms rfEval_add
#print axioms rfEval_mul
#print axioms rfEval_sum
end
end CatalanCore.Li2.NVMod
