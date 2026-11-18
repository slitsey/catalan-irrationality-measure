module
public import CatalanCore.Li2.NVMod.RationalMoments
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace CatalanCore.Li2.NVMod
noncomputable section
def rfDeriv (F : RatFunc ℚ) : RatFunc ℚ :=
  rfPoly (F.num.derivative*F.denom-F.num*F.denom.derivative)/(rfPoly F.denom)^2
def rfEval (F : RatFunc ℚ) (x : ℚ) : ℚ := F.num.eval x/F.denom.eval x
private theorem derivative_cross (N D P Q : ℚ[X]) (h : N*Q=P*D) :
    (N.derivative*D-N*D.derivative)*Q^2=(P.derivative*Q-P*Q.derivative)*D^2 := by
  have hd:=congrArg Polynomial.derivative h
  simp only [Polynomial.derivative_mul] at hd
  have he : N.derivative*Q=P.derivative*D+P*D.derivative-N*Q.derivative := by
    exact eq_sub_of_add_eq hd
  calc
    _=(N.derivative*Q)*D*Q-(N*Q)*D.derivative*Q := by ring
    _=(P.derivative*D+P*D.derivative-N*Q.derivative)*D*Q-(P*D)*D.derivative*Q := by rw [he,h]
    _=(P.derivative*D+P*D.derivative)*D*Q-(N*Q)*D*Q.derivative-(P*D)*D.derivative*Q := by ring
    _=(P.derivative*D+P*D.derivative)*D*Q-(P*D)*D*Q.derivative-(P*D)*D.derivative*Q := by rw [h]
    _=_ := by ring
theorem rfDeriv_fraction (F : RatFunc ℚ) (P Q : ℚ[X]) (hQ : Q≠0)
    (hF : F=rfPoly P/rfPoly Q) :
    rfDeriv F=rfPoly (P.derivative*Q-P*Q.derivative)/(rfPoly Q)^2 := by
  have hc : F.num*Q=P*F.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr hF
  have hd:=derivative_cross F.num F.denom P Q hc
  unfold rfDeriv
  apply (div_eq_div_iff (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero F)))
    (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hQ))).mpr
  simpa only [rfPoly,map_mul,map_sub,map_pow] using congrArg (rfPoly : ℚ[X]→RatFunc ℚ) hd
theorem rfEval_fraction (F : RatFunc ℚ) (P Q : ℚ[X]) (x : ℚ)
    (hQ : Q≠0) (hQx : Q.eval x≠0) (hF : F=rfPoly P/rfPoly Q) :
    rfEval F x=P.eval x/Q.eval x := by
  have hc : F.num*Q=P*F.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr hF
  have hd : F.denom∣Q := by simpa only [hF,rfPoly] using RatFunc.denom_div_dvd P Q
  have hDx : F.denom.eval x≠0 := by
    obtain ⟨T,hT⟩:=hd
    intro hz
    apply hQx
    rw [hT,Polynomial.eval_mul,hz,zero_mul]
  unfold rfEval
  apply (div_eq_div_iff hDx hQx).mpr
  simpa only [Polynomial.eval_mul] using congrArg (Polynomial.eval x) hc
#print axioms rfDeriv_fraction
#print axioms rfEval_fraction
end
end CatalanCore.Li2.NVMod
