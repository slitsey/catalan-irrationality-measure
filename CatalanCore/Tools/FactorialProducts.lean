module
public import CatalanCore.Decay.TheoremA
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Tools.FactorialProducts
open CatalanCore.Decay.TheoremA

theorem sum_log_factorial_le (M : ℕ) (hM : 1 ≤ M) :
    (∑ i ∈ Finset.range M, Real.log (i.factorial)) ≤
      (M:ℝ)^2/2*Real.log M-3/4*(M:ℝ)^2+M*Real.log M+2*M := by
  have hMR : 1 ≤ (M:ℝ) := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg hMR
  have hterm : ∀ i ∈ Finset.range M, Real.log (i.factorial) ≤
      (i:ℝ)*Real.log i-i+Real.log M+1 := by
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    by_cases hi0 : i=0
    · subst i
      simp only [Nat.factorial_zero,Nat.cast_one,Real.log_one,Nat.cast_zero,zero_mul,sub_zero,zero_add]
      linarith
    · have hi1 : 1 ≤ i := by omega
      have hh := CatalanCore.Zeta5.Energy.log_factorial_le hi1
      have hlogi : Real.log (i:ℝ) ≤ Real.log (M:ℝ) := Real.log_le_log
        (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast hiM.le)
      linarith
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul] at hsum
  rw [sum_range_cast'] at hsum
  have hmono : MonotoneOn (fun x : ℝ => x*Real.log x)
      (Icc 1 (1+((M-1:ℕ):ℝ))) := monotoneOn_x_log'.mono (fun x hx => hx.1)
  have hcmp := hmono.sum_le_integral
  have hend : 1+((M-1:ℕ):ℝ)=(M:ℝ) := by rw [Nat.cast_sub hM]; push_cast; ring
  rw [hend,integral_x_log' one_pos hMR] at hcmp
  have heSum : (∑ i ∈ Finset.range M, (i:ℝ)*Real.log i)=
      ∑ i ∈ Finset.range (M-1), (1+(i:ℝ))*Real.log (1+(i:ℝ)) := by
    obtain ⟨k,rfl⟩ : ∃ k, M=k+1 := ⟨M-1,by omega⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel,Nat.cast_zero,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [heSum] at hsum
  unfold Gx at hcmp
  norm_num only [Real.log_one,one_pow,one_mul,one_div] at hcmp
  nlinarith
end CatalanCore.Tools.FactorialProducts

namespace CatalanCore.Tools.FactorialProducts

theorem sum_log_factorial_error (M : ℕ) (hM : 2 ≤ M) :
    |(∑ i ∈ Finset.range M, Real.log (i.factorial))-
      ((M:ℝ)^2/2*Real.log M-3/4*(M:ℝ)^2)| ≤ M*Real.log M+2*M := by
  have hl := CatalanCore.Decay.TheoremA.sum_log_factorial_ge hM
  have hu := sum_log_factorial_le M (by omega)
  have hMR : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  rw [abs_le]
  constructor <;> nlinarith
end CatalanCore.Tools.FactorialProducts
#print axioms CatalanCore.Tools.FactorialProducts.sum_log_factorial_le
#print axioms CatalanCore.Tools.FactorialProducts.sum_log_factorial_error
