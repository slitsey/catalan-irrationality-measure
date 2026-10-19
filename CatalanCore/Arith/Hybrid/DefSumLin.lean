module

public import CatalanCore.Arith.Hybrid.DefSum

@[expose] public section

/-!
# Staircase deficits and the prime number theorem in a class

`clsSum_ge_unif`: eventually in `r`, **uniformly** in `r/2 ≤ A ≤ B ≤ 2r`,
`∑_{A < p ≤ B, p ≡ c (M)} log p ≥ (B - A)/φ(M) - ε r`.
`staircase_ge`: for a deficit `δ` with layers `{p : A j < p ≤ B j, p ≡ c} ⊆ {δ ≥ j}` the weighted sum
`∑ δ p log p` dominates `∑ⱼ ((B j - A j)/φ(M) - ε r)`.  A linear deficit (`δ = r + m - p`,
`δ = (5p+1)/4 - r - m`, ...) is a staircase with `A j`, `B j` affine in `j`, so Abel summation and
integrals are avoided.
-/

open Finset Filter Topology CatalanCore.NT

namespace CatalanCore.Arith.Hybrid

variable {M : ℕ}

lemma clsSum_ge_unif [NeZero M] {c : ZMod M} (hc : IsUnit c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ A B : ℕ, r ≤ 2 * A → A ≤ B → B ≤ 2 * r →
      ((B : ℝ) - A) / (M.totient : ℝ) - ε * r ≤ clsSum M c (fun _ => 1) A B := by
  have hl := thetaClass_lower hc (by positivity : 0 < ε / 4)
  have hu := thetaClass_upper hc (by positivity : 0 < ε / 4)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hl.and hu)
  filter_upwards [eventually_ge_atTop (2 * ⌈X0⌉₊), eventually_ge_atTop 1] with r hr hr1 A B hA hAB hB
  have hXA : X0 ≤ (A : ℝ) := by
    have h1 : (⌈X0⌉₊ : ℝ) ≤ A := by exact_mod_cast (by omega : ⌈X0⌉₊ ≤ A)
    exact (Nat.le_ceil X0).trans h1
  have hXB : X0 ≤ (B : ℝ) := hXA.trans (by exact_mod_cast hAB)
  have e : clsSum M c (fun _ => 1) A B = thetaClass M c (B : ℝ) - thetaClass M c (A : ℝ) := by
    unfold clsSum thetaClass
    rw [Nat.floor_natCast, Nat.floor_natCast, thetaClassN_sub M c hAB]
    simp
  rw [e]
  have h1 := (hX0 B hXB).1
  have h2 := (hX0 A hXA).2
  have hAr : (A : ℝ) ≤ 2 * r := by exact_mod_cast hAB.trans hB
  have hBr : (B : ℝ) ≤ 2 * r := by exact_mod_cast hB
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hφ : (M.totient : ℝ)⁻¹ * ((B : ℝ) - A) = ((B : ℝ) - A) / (M.totient : ℝ) := by
    rw [inv_mul_eq_div]
  have : ((M.totient : ℝ)⁻¹ - ε / 4) * B - ((M.totient : ℝ)⁻¹ + ε / 4) * A =
      (M.totient : ℝ)⁻¹ * ((B : ℝ) - A) - ε / 4 * (A + B) := by ring
  nlinarith

/-- **Staircase lower bound.** -/
theorem staircase_ge [NeZero M] {c : ZMod M} (hc : IsUnit c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ (S : Finset ℕ) (δ : ℕ → ℕ) (J : ℕ) (A B : ℕ → ℕ),
      (∀ p ∈ S, p.Prime) →
      (∀ j ∈ Finset.Icc 1 J, r ≤ 2 * A j ∧ A j ≤ B j ∧ B j ≤ 2 * r) →
      (∀ j ∈ Finset.Icc 1 J, ∀ p, A j < p → p ≤ B j → p.Prime → (p : ZMod M) = c →
        p ∈ S ∧ j ≤ δ p) →
      ∑ j ∈ Finset.Icc 1 J, (((B j : ℝ) - A j) / (M.totient : ℝ) - ε * r) ≤
        ∑ p ∈ S, (δ p : ℝ) * Real.log p := by
  classical
  filter_upwards [clsSum_ge_unif hc hε] with r hr S δ J A B hSp hAB hlay
  set Sj : ℕ → Finset ℕ := fun j =>
    if j ∈ Finset.Icc 1 J then (Finset.Ioc (A j) (B j)).filter (fun p => p.Prime ∧ (p : ZMod M) = c)
    else ∅ with hSj
  have hsub : ∀ j, Sj j ⊆ S := by
    intro j p hp
    by_cases hj : j ∈ Finset.Icc 1 J
    · simp only [hSj, if_pos hj, Finset.mem_filter, Finset.mem_Ioc] at hp
      exact (hlay j hj p hp.1.1 hp.1.2 hp.2.1 hp.2.2).1
    · have h0 : Sj j = ∅ := if_neg hj
      rw [h0] at hp
      simp at hp
  have hδ : ∀ j p, p ∈ Sj j → j ≤ δ p := by
    intro j p hp
    by_cases hj : j ∈ Finset.Icc 1 J
    · simp only [hSj, if_pos hj, Finset.mem_filter, Finset.mem_Ioc] at hp
      exact (hlay j hj p hp.1.1 hp.1.2 hp.2.1 hp.2.2).2
    · have h0 : Sj j = ∅ := if_neg hj
      rw [h0] at hp
      simp at hp
  have hL := layer_le S δ (fun p => Real.log p)
    (fun p hp => Real.log_nonneg (by exact_mod_cast (hSp p hp).one_lt.le)) J Sj hsub hδ
  refine le_trans ?_ hL
  refine Finset.sum_le_sum fun j hj => ?_
  have := hr (A j) (B j) (hAB j hj).1 (hAB j hj).2.1 (hAB j hj).2.2
  refine this.trans (le_of_eq ?_)
  simp only [hSj, if_pos hj, clsSum]
  simp

end CatalanCore.Arith.Hybrid
