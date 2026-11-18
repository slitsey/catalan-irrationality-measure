module
public import CatalanCore.Li2.NVMod.Special
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Finset
namespace CatalanCore.Li2.NVMod
noncomputable section

def specialKeys : Finset TypeKey := {⟨.V,1,4,2⟩,⟨.V,1,3,2⟩,⟨.V,0,3,3⟩,⟨.V,1,3,1⟩}

theorem special_constants_nonzero (z : ℚ) (hz : Allowed z) (A : TypeKey) (hA : A∈specialKeys) : K A z≠0 := by
  have hz0 := hz.1
  have hz1 := hz.2.1
  have h12 : z≠ -12 := by intro he;apply hz.2.2;rw [he];norm_num [Z0]
  have h4 : z≠ -4 := by intro he;apply hz.2.2;rw [he];norm_num [Z0]
  have h45 : z≠ -4/5 := by intro he;apply hz.2.2;rw [he];norm_num [Z0]
  have hR : z≠12/13 := by intro he;apply hz.2.2;rw [he];norm_num [Z0]
  have hzm1 : z-1≠0 := sub_ne_zero.mpr hz1
  have h1mz : 1-z≠0 := sub_ne_zero.mpr hz1.symm
  simp only [specialKeys,Finset.mem_insert,Finset.mem_singleton] at hA
  rcases hA with rfl|rfl|rfl|rfl
  · change KV 1 4 2 z≠0
    rw [special_V142 z hz0 hz1]
    apply div_ne_zero
    · apply mul_ne_zero
      · apply neg_ne_zero.mpr
        intro hh
        exact h12 (add_eq_zero_iff_eq_neg.mp hh)
      · intro hh
        apply hR
        apply (eq_div_iff (by norm_num : (13:ℚ)≠0)).mpr
        simpa only [mul_comm] using sub_eq_zero.mp hh
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hz0)) hzm1
  · change KV 1 3 2 z≠0
    rw [special_V132 z hz0 hz1]
    apply div_ne_zero
    · apply neg_ne_zero.mpr
      intro hh
      apply h45
      apply (eq_div_iff (by norm_num : (5:ℚ)≠0)).mpr
      simpa only [mul_comm] using add_eq_zero_iff_eq_neg.mp hh
    · exact mul_ne_zero hz0 (pow_ne_zero _ h1mz)
  · change KV 0 3 3 z≠0
    rw [special_V033 z hz0 hz1]
    apply div_ne_zero
    · intro hh
      exact h4 (add_eq_zero_iff_eq_neg.mp hh)
    · exact mul_ne_zero (by norm_num) hzm1
  · change KV 1 3 1 z≠0
    rw [special_V131 z hz0 hz1]
    exact div_ne_zero (by norm_num) hz0

#print axioms special_constants_nonzero
end
end CatalanCore.Li2.NVMod
