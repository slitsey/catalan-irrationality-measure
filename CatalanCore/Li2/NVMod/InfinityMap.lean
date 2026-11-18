module
public import CatalanCore.Li2.NVMod.Expansion
public import Mathlib.Algebra.Polynomial.Reverse
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped nonZeroDivisors
namespace CatalanCore.Li2.NVMod
noncomputable section
private theorem polyHahnQ_eval : polyHahnQ=Polynomial.eval₂RingHom
    (algebraMap ℚ (HahnSeries ℤ ℚ)) hX := by
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · simp only [polyHahnQ_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
def infPolyHahnQ : ℚ[X]→+*HahnSeries ℤ ℚ :=
  Polynomial.eval₂RingHom (algebraMap ℚ (HahnSeries ℤ ℚ)) hX⁻¹
theorem infPolyHahnQ_injective : Function.Injective infPolyHahnQ := by
  have hx : (hX : HahnSeries ℤ ℚ)≠0 := HahnSeries.single_ne_zero one_ne_zero
  have hz (P : ℚ[X]) (hP : infPolyHahnQ P=0) : P=0 := by
    letI : Invertible ((hX : HahnSeries ℤ ℚ)⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
    change P.eval₂ (algebraMap ℚ (HahnSeries ℤ ℚ)) hX⁻¹=0 at hP
    have hr := (Polynomial.eval₂_reverse_eq_zero_iff
      (algebraMap ℚ (HahnSeries ℤ ℚ)) (hX : HahnSeries ℤ ℚ)⁻¹ P).mpr hP
    simp only [invOf_eq_inv,inv_inv] at hr
    have hp0 : polyHahnQ P.reverse=0 := by
      rw [polyHahnQ_eval]
      exact hr
    have hrev : P.reverse=0 := polyHahnQ_injective (hp0.trans polyHahnQ.map_zero.symm)
    exact Polynomial.reverse_eq_zero.mp hrev
  intro P Q h
  exact sub_eq_zero.mp (hz (P-Q) (by rw [map_sub,h,sub_self]))
def infRFHahnQ : RatFunc ℚ→+*HahnSeries ℤ ℚ :=
  RatFunc.liftRingHom infPolyHahnQ (by
    intro P hP
    change infPolyHahnQ P∈(HahnSeries ℤ ℚ)⁰
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hz
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hP)
      (infPolyHahnQ_injective (by simpa using hz)))
theorem atInf_eq_hom (F : RatFunc ℚ) : atInf F=infRFHahnQ F := by
  rw [infRFHahnQ,RatFunc.liftRingHom_apply]
  rfl
#print axioms infPolyHahnQ_injective
#print axioms atInf_eq_hom
end
end CatalanCore.Li2.NVMod
