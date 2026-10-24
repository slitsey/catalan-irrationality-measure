module
public import Mathlib.Tactic
@[expose] public section
open Finset
namespace CatalanCore.Linalg
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

lemma sum_inverse_zero (h2 : (2:K)≠0) : (∑c:K,c⁻¹)=0 := by
  have H := Equiv.sum_comp (Equiv.neg K) (fun c:K=>c⁻¹)
  simp only [Equiv.neg_apply,inv_neg,Finset.sum_neg_distrib] at H
  apply (mul_eq_zero.mp (show (2:K)*(∑c:K,c⁻¹)=0 by linear_combination -H)).resolve_left h2

lemma sum_inverse_translate_zero (h2 : (2:K)≠0) (z : K) :
    (∑c:K,(c-z)⁻¹)=0 := by
  have H := (Equiv.subRight z).sum_comp (fun c:K=>c⁻¹)
  exact H.trans (sum_inverse_zero h2)

/-- On a finite field the complementary potential is the negative potential.
This treats the other short arc without a separate reflection identity. -/
theorem complementary_cauchy_kernel (h2 : (2:K)≠0) (s : Finset K)
    (z y : K) (hz : z∈s) (hy : y∈s) :
    (∑c∈s,(c-y)⁻¹)-(∑c∈s,(c-z)⁻¹)=
      -(y-z)*∑c∈sᶜ,((c-z)*(c-y))⁻¹ := by
  have ht (w : K) : (∑c∈sᶜ,(c-w)⁻¹)+(∑c∈s,(c-w)⁻¹)=0 := by
    rw [Finset.sum_compl_add_sum, sum_inverse_translate_zero h2]
  have he (c : K) (hc : c∈sᶜ) :
      (c-y)⁻¹-(c-z)⁻¹=(y-z)*((c-z)*(c-y))⁻¹ := by
    have hcz : c-z≠0 := sub_ne_zero.mpr (fun h=> (Finset.mem_compl.mp hc) (h ▸ hz))
    have hcy : c-y≠0 := sub_ne_zero.mpr (fun h=> (Finset.mem_compl.mp hc) (h ▸ hy))
    field_simp
    <;> ring
  have H : (∑c∈sᶜ,(c-y)⁻¹)-(∑c∈sᶜ,(c-z)⁻¹)=
      (y-z)*∑c∈sᶜ,((c-z)*(c-y))⁻¹ := by
    rw [←Finset.sum_sub_distrib,Finset.mul_sum]
    exact Finset.sum_congr rfl he
  linear_combination ht y-ht z-H

/-- Completing the finite-field Cauchy sum produces the local moment term. -/
theorem complete_cauchy_sum (h2 : (2:K)≠0) {z y : K} (hzy : z≠y) :
    (∑c∈(Finset.univ.erase z).erase y,((c-z)*(c-y))⁻¹)=2/(z-y)^2 := by
  have hdy : z-y≠0:=sub_ne_zero.mpr hzy
  have hdz : y-z≠0:=sub_ne_zero.mpr hzy.symm
  have hz : (∑c∈(Finset.univ.erase z).erase y,(c-z)⁻¹)=-(y-z)⁻¹ := by
    have H:=sum_erase_add (s:=Finset.univ.erase z) (f:=fun c:K=>(c-z)⁻¹)
      (a:=y) (by simp [hzy.symm])
    have H': (∑c∈Finset.univ.erase z,(c-z)⁻¹)=0 := by
      have H'':=sum_erase_add (s:=Finset.univ) (f:=fun c:K=>(c-z)⁻¹) (a:=z) (by simp)
      simpa using H''.trans (sum_inverse_translate_zero h2 z)
    rw [H'] at H
    linear_combination H
  have hy : (∑c∈(Finset.univ.erase z).erase y,(c-y)⁻¹)=-(z-y)⁻¹ := by
    rw [Finset.erase_right_comm]
    have H:=sum_erase_add (s:=Finset.univ.erase y) (f:=fun c:K=>(c-y)⁻¹)
      (a:=z) (by simp [hzy])
    have H': (∑c∈Finset.univ.erase y,(c-y)⁻¹)=0 := by
      have H'':=sum_erase_add (s:=Finset.univ) (f:=fun c:K=>(c-y)⁻¹) (a:=y) (by simp)
      simpa using H''.trans (sum_inverse_translate_zero h2 y)
    rw [H'] at H
    linear_combination H
  have he (c : K) (hc : c∈(Finset.univ.erase z).erase y) :
      ((c-z)*(c-y))⁻¹=((c-z)⁻¹-(c-y)⁻¹)/(z-y) := by
    have hcz : c-z≠0:=sub_ne_zero.mpr (by simpa using (mem_erase.mp (mem_erase.mp hc).2).1)
    have hcy : c-y≠0:=sub_ne_zero.mpr (mem_erase.mp hc).1
    field_simp
    <;> ring
  rw [Finset.sum_congr rfl he,←Finset.sum_div,Finset.sum_sub_distrib,hz,hy]
  rw [show y-z=-(z-y) by ring,inv_neg]
  field_simp
  <;> ring
end CatalanCore.Linalg
