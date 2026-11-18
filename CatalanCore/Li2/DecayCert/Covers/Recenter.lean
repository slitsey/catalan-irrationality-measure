module
public import CatalanCore.Li2.DecayCert.Compile
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

def ComplexSegmentModel (d : SegmentData) (p e : ℂ) (a : List ℂ) (r err : ℝ) : Prop :=
  0 ≤ r ∧ 0 ≤ err ∧ ∀ u : ℂ,‖u‖ ≤ r →
    |P d.ν (p+e*u)-(∑ j ∈ Finset.range a.length,a[j]! *u^j).re| ≤ err

theorem list_complex_poly_displacement (a : List ℂ) (u v : ℂ) (R δ : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (hδ : ‖u-v‖ ≤ δ) :
    ‖(∑ j ∈ Finset.range a.length,a[j]! *u^j)-(∑ j ∈ Finset.range a.length,a[j]! *v^j)‖ ≤
      δ*∑ j ∈ Finset.range a.length,(j:ℝ)*‖a[j]!‖*R^(j-1) := by
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  cases j with
  | zero => simp
  | succ n =>
    rw [show a[n+1]! *u^(n+1)-a[n+1]! *v^(n+1)=a[n+1]! *(u^(n+1)-v^(n+1)) by ring,norm_mul]
    have hp := norm_pow_sub_pow_bound u v R hR hu hv n
    calc
      _ ≤ ‖a[n+1]!‖*((n+1:ℕ)*R^n*‖u-v‖) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ ‖a[n+1]!‖*((n+1:ℕ)*R^n*δ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by positivity)) (norm_nonneg _)
      _ = _ := by simp only [Nat.add_sub_cancel_right]; push_cast; ring

theorem rationalJoukowski_recenter (d : SegmentData) (φ p e : ℂ)
    (hφ : 1 < ‖φ‖) (he : e ≠ 0) (rt : ℝ) (hrt : 0 ≤ rt) (a : List ℂ) (err : ℝ)
    (hm : ComplexSegmentModel d (d.M+d.h*jJ φ) e a (rt+‖(p-(d.M+d.h*jJ φ))/e‖) err) :
    ComplexSegmentModel d p e a rt (err+‖(p-(d.M+d.h*jJ φ))/e‖*
      ∑ j ∈ Finset.range a.length,(j:ℝ)*‖a[j]!‖*(rt+‖(p-(d.M+d.h*jJ φ))/e‖)^(j-1)) := by
  let q := d.M+d.h*jJ φ
  let shift := (p-q)/e
  let R := rt+‖shift‖
  have hR : 0 ≤ R := add_nonneg hrt (norm_nonneg _)
  have hgrad : 0 ≤ ∑ j ∈ Finset.range a.length,(j:ℝ)*‖a[j]!‖*R^(j-1) := by
    apply Finset.sum_nonneg
    intro j hj
    positivity
  refine ⟨hrt,add_nonneg hm.2.1 (mul_nonneg (norm_nonneg _) hgrad),?_⟩
  intro u hu
  have hv : ‖u+shift‖ ≤ R := (norm_add_le _ _).trans (add_le_add hu (le_refl ‖shift‖))
  have huR : ‖u‖ ≤ R := hu.trans (le_add_of_nonneg_right (norm_nonneg _))
  have heq : q+e*(u+shift)=p+e*u := by dsimp only [shift]; field_simp [he] <;> ring
  have hp := hm.2.2 (u+shift) hv
  rw [heq] at hp
  have hd := list_complex_poly_displacement a (u+shift) u R ‖shift‖ hR hv huR
    (by simp only [add_sub_cancel_left,le_refl])
  have hr := (Complex.abs_re_le_norm ((∑ j ∈ Finset.range a.length,a[j]! *(u+shift)^j)-
    (∑ j ∈ Finset.range a.length,a[j]! *u^j))).trans hd
  rw [Complex.sub_re] at hr
  have ht := abs_add_le (P d.ν (p+e*u)-(∑ j ∈ Finset.range a.length,a[j]! *(u+shift)^j).re)
    ((∑ j ∈ Finset.range a.length,a[j]! *(u+shift)^j).re-(∑ j ∈ Finset.range a.length,a[j]! *u^j).re)
  have hadd : P d.ν (p+e*u)-(∑ j ∈ Finset.range a.length,a[j]! *(u+shift)^j).re+
      ((∑ j ∈ Finset.range a.length,a[j]! *(u+shift)^j).re-(∑ j ∈ Finset.range a.length,a[j]! *u^j).re)=
      P d.ν (p+e*u)-(∑ j ∈ Finset.range a.length,a[j]! *u^j).re := by ring
  rw [hadd] at ht
  exact ht.trans (add_le_add hp hr)
#print axioms list_complex_poly_displacement
#print axioms rationalJoukowski_recenter
end
end CatalanCore.Li2.DecayCert
