module
public import CatalanCore.Li2.NVMod.RationalRules
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

def jetScalar {F : Type*} [Field F] (v v1 v2 : F) (d : ℕ) : F :=
  if d=0 then -v2/2 else if d=1 then -v1 else if d=2 then -v else 0
def jetBlock {F : Type*} [Field F] (n : ℕ) (v v1 v2 : F) : Matrix (Fin n) (Fin n) F :=
  fun i j=>jetScalar v v1 v2 (i.val+j.val)
theorem jet_det_one {F : Type*} [Field F] (v v1 v2 : F) : (jetBlock 1 v v1 v2).det= -v2/2 := by
  rw [Matrix.det_fin_one]
  rfl
theorem jet_det_two {F : Type*} [Field F] (v v1 v2 : F) :
    (jetBlock 2 v v1 v2).det=v*v2/2-v1^2 := by
  rw [Matrix.det_fin_two]
  norm_num [jetBlock,jetScalar]
  <;> ring
theorem jet_det_three {F : Type*} [Field F] (v v1 v2 : F) : (jetBlock 3 v v1 v2).det=v^3 := by
  rw [Matrix.det_fin_three]
  norm_num [jetBlock,jetScalar]
  <;> ring
private theorem second_product_identity (F : RatFunc ℚ) (P : ℚ[X]) :
    rfDeriv (rfDeriv (F*rfPoly P))=
      rfDeriv (rfDeriv F)*rfPoly P+rfDeriv F*rfPoly P.derivative+
        rfDeriv F*rfPoly P.derivative+F*rfPoly P.derivative.derivative := by
  simp only [rfDeriv_mul,rfDeriv_add,rfDeriv_poly]
  ring
theorem second_product_eval (F : RatFunc ℚ) (P : ℚ[X]) (x : ℚ) (hF : RFRegular x F) :
    rfEval (rfDeriv (rfDeriv (F*rfPoly P))) x=
      rfEval (rfDeriv (rfDeriv F)) x*P.eval x+
        2*rfEval (rfDeriv F) x*P.derivative.eval x+rfEval F x*P.derivative.derivative.eval x := by
  have ha:=hF.deriv.deriv.mul (RFRegular.poly x P)
  have hb:=hF.deriv.mul (RFRegular.poly x P.derivative)
  have hc:=hF.mul (RFRegular.poly x P.derivative.derivative)
  rw [second_product_identity,rfEval_add ((ha.add hb).add hb) hc,
    rfEval_add (ha.add hb) hb,rfEval_add ha hb,
    rfEval_mul hF.deriv.deriv (RFRegular.poly x P),rfEval_mul hF.deriv (RFRegular.poly x P.derivative),
    rfEval_mul hF (RFRegular.poly x P.derivative.derivative),rfEval_poly,rfEval_poly,rfEval_poly]
  ring
theorem second_product_linear_power (F : RatFunc ℚ) (t d : ℕ)
    (hF : RFRegular (-(t:ℚ)) F) (hd : d≤4) :
    -rfEval (rfDeriv (rfDeriv (F*rfPoly ((X+C (t:ℚ))^d)))) (-(t:ℚ))/2=
      jetScalar (rfEval F (-(t:ℚ))) (rfEval (rfDeriv F) (-(t:ℚ)))
        (rfEval (rfDeriv (rfDeriv F)) (-(t:ℚ))) d := by
  rw [second_product_eval _ _ _ hF]
  have hcases : d=0∨d=1∨d=2∨d=3∨d=4 := by omega
  rcases hcases with rfl|rfl|rfl|rfl|rfl <;>
    norm_num [jetScalar,Polynomial.derivative_pow,Polynomial.derivative_add,
      Polynomial.derivative_mul,Polynomial.derivative_C,Polynomial.derivative_X,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] <;> ring

private theorem rfDeriv_one : rfDeriv (1:RatFunc ℚ)=0 := by
  simpa only [rfPoly,map_one,Polynomial.derivative_one,map_zero] using rfDeriv_poly (1:ℚ[X])
private theorem inverse_fraction (F : RatFunc ℚ) : F⁻¹=rfPoly F.denom/rfPoly F.num := by
  calc
    _=(rfPoly F.num/rfPoly F.denom)⁻¹ := congrArg Inv.inv (RatFunc.num_div_denom F).symm
    _=_ := inv_div _ _
private theorem numerator_eval_nonzero {x : ℚ} {F : RatFunc ℚ} (hne : rfEval F x≠0) : F.num.eval x≠0 := by
  intro hz
  apply hne
  simp only [rfEval,hz,zero_div]
private theorem rfRegular_inv {x : ℚ} {F : RatFunc ℚ} (hne : rfEval F x≠0) : RFRegular x F⁻¹ := by
  have hN:=numerator_eval_nonzero hne
  have hP : F.num≠0 := by intro h;rw [h,Polynomial.eval_zero] at hN;exact hN rfl
  rw [inverse_fraction]
  exact RFRegular.fraction x _ _ hP hN
private theorem rfEval_inv {x : ℚ} {F : RatFunc ℚ} (hne : rfEval F x≠0) :
    rfEval F⁻¹ x=(rfEval F x)⁻¹ := by
  have hN:=numerator_eval_nonzero hne
  have hP : F.num≠0 := by intro h;rw [h,Polynomial.eval_zero] at hN;exact hN rfl
  rw [rfEval_fraction F⁻¹ _ _ x hP hN (inverse_fraction F),rfEval,inv_div]
private theorem rfEval_deriv_inv {x : ℚ} {F : RatFunc ℚ} (hF : RFRegular x F) (hne : rfEval F x≠0) :
    rfEval (rfDeriv F⁻¹) x= -rfEval (rfDeriv F) x/(rfEval F x)^2 := by
  have hi:=rfRegular_inv hne
  have hFn : F≠0 := by intro h;rw [h,rfEval_zero] at hne;exact hne rfl
  have hd:=rfDeriv_mul F F⁻¹
  rw [mul_inv_cancel₀ hFn,rfDeriv_one] at hd
  have he:=congrArg (fun H : RatFunc ℚ=>rfEval H x) hd
  rw [rfEval_zero,rfEval_add (hF.deriv.mul hi) (hF.mul hi.deriv),
    rfEval_mul hF.deriv hi,rfEval_mul hF hi.deriv,rfEval_inv hne] at he
  have hl : rfEval (rfDeriv F) x/rfEval F x+rfEval F x*rfEval (rfDeriv F⁻¹) x=0 := by
    simpa only [div_eq_mul_inv] using he.symm
  apply mul_left_cancel₀ hne
  calc
    _=(rfEval (rfDeriv F) x/rfEval F x+rfEval F x*rfEval (rfDeriv F⁻¹) x)-rfEval (rfDeriv F) x/rfEval F x := by ring
    _=0-rfEval (rfDeriv F) x/rfEval F x := by rw [hl]
    _=_ := by field_simp [hne] <;> ring
theorem logarithmic_jet (F : RatFunc ℚ) (x : ℚ) (hF : RFRegular x F) (hne : rfEval F x≠0) :
    let v := rfEval F x
    let v1 := rfEval (rfDeriv F) x
    let v2 := rfEval (rfDeriv (rfDeriv F)) x
    let σ := rfEval (rfDeriv F/F) x
    let σ' := rfEval (rfDeriv (rfDeriv F/F)) x
    v*(σ^2+σ')=v2 ∧ v^2*(σ'-σ^2)=v*v2-2*v1^2 := by
  have hi:=rfRegular_inv hne
  have hs : rfEval (rfDeriv F/F) x=rfEval (rfDeriv F) x/rfEval F x := by
    rw [div_eq_mul_inv,rfEval_mul hF.deriv hi,rfEval_inv hne]
    simp only [div_eq_mul_inv]
  have hd : rfDeriv (rfDeriv F/F)=rfDeriv (rfDeriv F)*F⁻¹+rfDeriv F*rfDeriv F⁻¹ := by
    rw [div_eq_mul_inv,rfDeriv_mul]
  have hds : rfEval (rfDeriv (rfDeriv F/F)) x=
      rfEval (rfDeriv (rfDeriv F)) x/rfEval F x-(rfEval (rfDeriv F) x)^2/(rfEval F x)^2 := by
    rw [hd,rfEval_add (hF.deriv.deriv.mul hi) (hF.deriv.mul hi.deriv),
      rfEval_mul hF.deriv.deriv hi,rfEval_mul hF.deriv hi.deriv,rfEval_inv hne,rfEval_deriv_inv hF hne]
    ring
  dsimp only
  rw [hs,hds]
  constructor <;> field_simp [hne] <;> ring

theorem first_product_eval (F : RatFunc ℚ) (P : ℚ[X]) (x : ℚ) (hF : RFRegular x F) :
    rfEval (rfDeriv (F*rfPoly P)) x=
      rfEval (rfDeriv F) x*P.eval x+rfEval F x*P.derivative.eval x := by
  rw [rfDeriv_mul,rfDeriv_poly,
    rfEval_add (hF.deriv.mul (RFRegular.poly x P)) (hF.mul (RFRegular.poly x P.derivative)),
    rfEval_mul hF.deriv (RFRegular.poly x P),rfEval_mul hF (RFRegular.poly x P.derivative),
    rfEval_poly,rfEval_poly]
private theorem linear_power_double_zero (t d : ℕ) (hd : 2≤d) :
    ((X+C (t:ℚ))^d).eval (-(t:ℚ))=0 ∧
      (((X+C (t:ℚ))^d).derivative).eval (-(t:ℚ))=0 := by
  let Q : ℚ[X] := X+C (t:ℚ)
  have hQ : Q.derivative=1 := by simp [Q]
  have hx : Q.eval (-(t:ℚ))=0 := by simp [Q]
  have hD : (Q^d).derivative=C (d:ℚ)*Q^(d-1) := by
    simp only [Polynomial.derivative_pow,hQ,mul_one,map_natCast]
  constructor
  · change (Q^d).eval (-(t:ℚ))=0
    rw [Polynomial.eval_pow,hx,zero_pow (by omega : d≠0)]
  · change (Q^d).derivative.eval (-(t:ℚ))=0
    rw [hD,Polynomial.eval_mul,Polynomial.eval_pow,hx,zero_pow (by omega : d-1≠0),mul_zero]
private theorem linear_power_triple_zero (t d : ℕ) (hd : 3≤d) :
    (((X+C (t:ℚ))^d).derivative.derivative).eval (-(t:ℚ))=0 := by
  let Q : ℚ[X] := X+C (t:ℚ)
  have hQ : Q.derivative=1 := by simp [Q]
  have hx : Q.eval (-(t:ℚ))=0 := by simp [Q]
  have hD : (Q^d).derivative=C (d:ℚ)*Q^(d-1) := by
    simp only [Polynomial.derivative_pow,hQ,mul_one,map_natCast]
  change (Q^d).derivative.derivative.eval (-(t:ℚ))=0
  rw [hD,Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add,
    Polynomial.derivative_pow,hQ,mul_one]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,hx,
    zero_pow (by omega : d-1-1≠0),mul_zero]
theorem first_product_vanish (F : RatFunc ℚ) (t d : ℕ) (hF : RFRegular (-(t:ℚ)) F) (hd : 2≤d) :
    rfEval (rfDeriv (F*rfPoly ((X+C (t:ℚ))^d))) (-(t:ℚ))=0 := by
  rw [first_product_eval _ _ _ hF,(linear_power_double_zero t d hd).1,
    (linear_power_double_zero t d hd).2,mul_zero,mul_zero,add_zero]
theorem second_product_vanish (F : RatFunc ℚ) (t d : ℕ) (hF : RFRegular (-(t:ℚ)) F) (hd : 3≤d) :
    rfEval (rfDeriv (rfDeriv (F*rfPoly ((X+C (t:ℚ))^d)))) (-(t:ℚ))=0 := by
  rw [second_product_eval _ _ _ hF,(linear_power_double_zero t d (by omega)).1,
    (linear_power_double_zero t d (by omega)).2,linear_power_triple_zero t d hd]
  ring
theorem jet_det_logarithmic (F : RatFunc ℚ) (x : ℚ) (hF : RFRegular x F) (hne : rfEval F x≠0) :
    let v := rfEval F x
    let v1 := rfEval (rfDeriv F) x
    let v2 := rfEval (rfDeriv (rfDeriv F)) x
    let σ := rfEval (rfDeriv F/F) x
    let σ' := rfEval (rfDeriv (rfDeriv F/F)) x
    (jetBlock 1 v v1 v2).det= -v*(σ^2+σ')/2 ∧
      (jetBlock 2 v v1 v2).det=v^2*(σ'-σ^2)/2 := by
  dsimp only
  rw [jet_det_one,jet_det_two]
  have hjet:=logarithmic_jet F x hF hne
  dsimp only at hjet
  constructor
  · rw [←hjet.1]
    ring
  · rw [hjet.2]
    ring
#print axioms jet_det_three
#print axioms first_product_vanish
#print axioms second_product_vanish
#print axioms jet_det_logarithmic
end
end CatalanCore.Li2.NVMod
