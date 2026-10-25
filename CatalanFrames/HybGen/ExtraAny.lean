module
public import CatalanCore.Arith.Hybrid.Extra
@[expose] public section
open Finset
namespace CatalanFrames.HybGen
/-- The higher-level sum is supported below sqrt(LN), so its outer cutoff is arbitrary. -/
theorem ex_sum_bound_any (r m Bd Lc : ℕ) (exG : ℕ → ℕ) (Lg : ℕ)
    (hexG : ∀ p, p.Prime → exG p ≤ 2*(r+m)*Lg)
    (hexG0 : ∀ p, p.Prime → Lc*(r+2*m) < p^2 → exG p = 0) :
    ∑ p ∈ (range Bd).filter Nat.Prime, (exG p : ℝ)*Real.log p ≤
      ((Nat.sqrt (Lc*(r+2*m)) : ℝ)+1)*
        (2*(r+m : ℝ)*Lg*Real.log ((Lc : ℝ)*(r+2*m)+5)) := by
  set P := (range Bd).filter Nat.Prime with hP
  have hsplit : ∀ p ∈ P, (exG p : ℝ)*Real.log p ≤
      (if p ≤ Nat.sqrt (Lc*(r+2*m)) then
        2*(r+m : ℝ)*Lg*Real.log ((Lc : ℝ)*(r+2*m)+5) else 0) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    split_ifs with h
    · have hpQ : p ≤ Lc*(r+2*m)+5 :=
        (h.trans (Nat.sqrt_le_self _)).trans (by omega)
      have hlogle : Real.log p ≤ Real.log ((Lc : ℝ)*(r+2*m)+5) := by
        apply Real.log_le_log (by exact_mod_cast hpp.pos)
        exact_mod_cast hpQ
      have h1 : (exG p : ℝ) ≤ 2*(r+m : ℝ)*Lg := by exact_mod_cast hexG p hpp
      exact mul_le_mul h1 hlogle hlog (by positivity)
    · have hgt : Lc*(r+2*m) < p^2 := by
        by_contra hh
        push_neg at hh
        exact h (Nat.le_sqrt'.mpr hh)
      rw [hexG0 p hpp hgt]
      simp
  refine (sum_le_sum hsplit).trans ?_
  rw [← sum_filter]
  have hsub : P.filter (fun p => p ≤ Nat.sqrt (Lc*(r+2*m))) ⊆
      range (Nat.sqrt (Lc*(r+2*m))+1) := by
    intro x hx
    simp at hx ⊢
    omega
  have hnn : 0 ≤ 2*(r+m : ℝ)*Lg*Real.log ((Lc : ℝ)*(r+2*m)+5) := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have hh : (0 : ℝ) ≤ (Lc : ℝ)*(r+2*m) := by positivity
    linarith
  rw [sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hnn
  have hh := card_le_card hsub
  simp only [card_range] at hh
  exact_mod_cast hh
end CatalanFrames.HybGen
#print axioms CatalanFrames.HybGen.ex_sum_bound_any
