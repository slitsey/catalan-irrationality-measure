module
public import CatalanCore.Li2.NVMod.Series
public import CatalanCore.Li2.NVMod.Moments
@[expose] public section
set_option Elab.async false
open Polynomial
open scoped nonZeroDivisors
namespace CatalanCore.Li2.NVMod
noncomputable section
def polyHahnQ : ℚ[X]→+*HahnSeries ℤ ℚ :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp Polynomial.coeToPowerSeries.ringHom
theorem polyHahnQ_injective : Function.Injective polyHahnQ :=
  HahnSeries.ofPowerSeries_injective.comp (Polynomial.coe_injective ℚ)
theorem polyHahnQ_X : polyHahnQ X=hX := by
  simp only [polyHahnQ,RingHom.comp_apply,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X,HahnSeries.ofPowerSeries_X,hX]
theorem polyHahnQ_C (a : ℚ) : polyHahnQ (C a)=HahnSeries.C a := by
  simp only [polyHahnQ,RingHom.comp_apply,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C,HahnSeries.ofPowerSeries_C]
def affinePolyHahnQ (a b : ℚ) : ℚ[X]→+*HahnSeries ℤ ℚ :=
  polyHahnQ.comp (Polynomial.compRingHom (C b*X+C a))
theorem affinePolyHahnQ_injective (a b : ℚ) (hb : b≠0) :
    Function.Injective (affinePolyHahnQ a b) := by
  apply polyHahnQ_injective.comp
  intro P Q h
  change P.comp (C b*X+C a)=Q.comp (C b*X+C a) at h
  have he : (C b*X+C a).comp (C b⁻¹*(X-C a))=X := by
    simp only [add_comp,mul_comp,C_comp,X_comp]
    rw [←mul_assoc,←map_mul,mul_inv_cancel₀ hb,map_one,one_mul]
    ring
  have hh:=congrArg (fun R : ℚ[X]=>R.comp (C b⁻¹*(X-C a))) h
  simpa only [comp_assoc,he,comp_X] using hh
theorem affinePolyHahnQ_eq (a b : ℚ) :
    affinePolyHahnQ a b=Polynomial.eval₂RingHom
      (algebraMap ℚ (HahnSeries ℤ ℚ)) (HahnSeries.C b*hX+HahnSeries.C a) := by
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · simp only [affinePolyHahnQ,RingHom.comp_apply,Polynomial.coe_compRingHom_apply,
      Polynomial.X_comp,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
      map_add,map_mul,polyHahnQ_C,polyHahnQ_X]
def affineRFHahnQ (a b : ℚ) (hb : b≠0) : RatFunc ℚ→+*HahnSeries ℤ ℚ :=
  RatFunc.liftRingHom (affinePolyHahnQ a b) (by
    intro P hP
    change affinePolyHahnQ a b P∈(HahnSeries ℤ ℚ)⁰
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hz
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hP)
      ((affinePolyHahnQ_injective a b hb) (by simpa using hz)))
theorem expandRF_affineQ (a b : ℚ) (hb : b≠0) (F : RatFunc ℚ) :
    expandRF F (HahnSeries.C b*hX+HahnSeries.C a)=affineRFHahnQ a b hb F := by
  rw [affineRFHahnQ,RatFunc.liftRingHom_apply,affinePolyHahnQ_eq]
  rfl
theorem atZero_eq_hom (F : RatFunc ℚ) : atZero F=affineRFHahnQ 0 1 one_ne_zero F := by
  simpa only [atZero,map_zero,map_one,one_mul,add_zero] using expandRF_affineQ 0 1 one_ne_zero F
theorem atOne_eq_hom (F : RatFunc ℚ) : atOne F=affineRFHahnQ 1 (-1) (by norm_num) F := by
  simpa only [atOne,map_one,map_neg,neg_one_mul,add_comm,sub_eq_add_neg] using
    expandRF_affineQ 1 (-1) (by norm_num) F
#print axioms atZero_eq_hom
#print axioms atOne_eq_hom
end
end CatalanCore.Li2.NVMod
