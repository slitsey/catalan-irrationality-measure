module
public import CatalanMeasure.Parametric.MixedMajorant
public import CatalanMeasure.Lemma6
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem paramRealRowAmplitude_zero {P : Parameters} (hAdm : Admissible P)
    {N r : ℕ} (hN : 0<N) (hr : r<P.n N) : realRowAmplitude P N r 0=0 :=by
  have hA : 0<P.A N :=by
    have hb : 0<P.b N :=Nat.mul_pos hAdm.2.1 hN
    unfold Parameters.A
    omega
  rw [realRowAmplitude_of_nonpos P N r le_rfl,← Polynomial.coeff_zero_eq_eval_zero,
    realPoly_coeff,rowP_coeff_eq_zero_of_lt hAdm hN hr hA]
  simp

theorem paramRowDet_eq_zero_of_zero {P : Parameters} (hAdm : Admissible P)
    {N : ℕ} (hN : 0<N) {p m : ℕ} (hpm : p+m=P.n N)
    (τ : Fin m → ℝ) (t : Fin p → ℝ) {i : Fin p} (hti : t i=0) :
    CatalanMeasure.rowDet (paramPinRowFun P N) τ t=0 :=by
  unfold CatalanMeasure.rowDet
  apply Matrix.det_eq_zero_of_column_eq_zero (Fin.castAdd m i)
  intro r
  simp only [Matrix.of_apply,paramPinRowFun,Fin.append_left,hti]
  exact paramRealRowAmplitude_zero hAdm hN (by have :=r.isLt;omega)

theorem paramRowDet_eq_zero_of_not_injective (P : Parameters) {N p m : ℕ}
    (τ : Fin m → ℝ) (t : Fin p → ℝ) (hi : ¬Function.Injective (Fin.append t τ)) :
    CatalanMeasure.rowDet (paramPinRowFun P N) τ t=0 :=by
  unfold Function.Injective at hi
  push Not at hi
  obtain ⟨c,c',hc,hne⟩ :=hi
  unfold CatalanMeasure.rowDet
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply,hc]

end
end CatalanMeasure.Parametric
