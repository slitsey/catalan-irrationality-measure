module
public import CatalanMeasure.Parametric.TwentyTwoAdicBudget
public import CatalanMeasure.Parametric.TwoAdicCoefficientEntryBounds
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem twenty_two_adic_selector_exponent_lower (N : ℕ)
    (τ : Fin (20*N) → Fin 3) (u j : Fin (20*N) → ℕ)
    (huE : Set.InjOn u {k | τ k = 1})
    (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, 3*N ≤ j k) :
    -(42 : ℝ) * (N : ℝ)^2 - 40*N ≤
      ((∑ k : Fin (20*N),
        if τ k = 0 then (26*N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ)
        else (u k : ℤ) : ℤ) : ℝ) := by
  classical
  let E : Finset (Fin (20*N)) := Finset.univ.filter (fun k => τ k = 1)
  let B : Finset (Fin (20*N)) := Finset.univ.filter (fun k => τ k = 2)
  have huE' : Set.InjOn u (E : Set (Fin (20*N))) := by
    intro x hx y hy hxy
    exact huE (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have huB' : Set.InjOn u (B : Set (Fin (20*N))) := by
    intro x hx y hy hxy
    exact huB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have hdisj : Disjoint E B := by
    apply Finset.disjoint_left.mpr
    intro k hkE hkB
    have he : τ k = 1 := (Finset.mem_filter.mp hkE).2
    have hb' : τ k = 2 := (Finset.mem_filter.mp hkB).2
    have hn : (1 : Fin 3) = 2 := he.symm.trans hb'
    norm_num at hn
  have hcard : E.card + B.card ≤ 20*N := by
    have hc := Finset.card_le_card (Finset.subset_univ (E ∪ B))
    rw [Finset.card_union_of_disjoint hdisj] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have heach (k : Fin (20*N)) :
      (if τ k = 0 then (26*N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ)
        else (u k : ℤ)) =
      (26*N : ℤ) +
        (if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ) - (26*N : ℤ)
          else 0) +
        (if τ k = 2 then (u k : ℤ) - (26*N : ℤ) else 0) := by
    by_cases h₀ : τ k = 0
    · simp [h₀]
    by_cases h₁ : τ k = 1
    · simp [h₁]
    have h₂ : τ k = 2 := by omega
    simp [h₂]
  have hsumE : (∑ k : Fin (20*N),
      if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ) - (26*N : ℤ)
        else 0) =
      ∑ k ∈ E, (2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ) - (26*N : ℤ)) := by
    simp only [E, Finset.sum_filter]
  have hsumB : (∑ k : Fin (20*N),
      if τ k = 2 then (u k : ℤ) - (26*N : ℤ) else 0) =
      ∑ k ∈ B, ((u k : ℤ) - (26*N : ℤ)) := by
    simp only [B, Finset.sum_filter]
  have hsumC : (∑ _ : Fin (20*N), (26*N : ℤ)) = (20*N : ℤ) * (26*N : ℤ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Int.nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat]
  have hsum : (∑ k : Fin (20*N),
      if τ k = 0 then (26*N : ℤ)
      else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ)
      else (u k : ℤ)) =
      2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) -
        (27*N : ℤ) * (E.card : ℤ) + (∑ k ∈ B, (u k : ℤ)) +
        (26*N : ℤ) * ((20*N : ℤ) - (E.card : ℤ) - (B.card : ℤ)) := by
    simp_rw [heach]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumE, hsumB, hsumC]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Int.nsmul_eq_mul]
    ring
  rw [hsum]
  exact twenty_two_adic_selector_budget N E B u j huE' huB'
    (fun _ _ _ _ h => hj h) (fun k _ => hb k) hcard

theorem twenty_two_adic_selector_zpow_le (N : ℕ)
    (τ : Fin (20*N) → Fin 3) (u j : Fin (20*N) → ℕ)
    (huE : Set.InjOn u {k | τ k = 1})
    (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, 3*N ≤ j k) :
    (2 : ℝ) ^ (-(∑ k : Fin (20*N),
        if τ k = 0 then (26*N : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (27*N : ℤ)
        else (u k : ℤ))) ≤
      (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N) := by
  have h := twenty_two_adic_selector_exponent_lower N τ u j huE huB hj hb
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  simp only [Int.cast_neg]
  linarith only [h]


end
end CatalanMeasure.Parametric
