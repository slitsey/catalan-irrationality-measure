module

public import CatalanFrames.Lambda.HybDefEB
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section

/-!
# λ: the deficit sum of E (class 1)

`lam_E1_deficit_sum`: eventually in `r`, `∑_p defE1 r p · log p ≥ m ((1/7 - ε) r - 4 log r)`
(`m = r/8`; the primes `5r/7 < p ≤ r`, `p ≡ 1 (4)`, up to four exceptions near the window ends).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma defE1_eq (r p : ℕ) : defE1 r p = cleanDef (r / 8) (cleanE1 r) p := by
  classical
  unfold defE1 cleanDef
  rfl

theorem lam_E1_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defE1 r p : ℝ) * Real.log p := by
  classical
  have hs : (0 : ℝ) < ((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := by norm_num
  have hst : ((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
  have ht : ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ 1 := by norm_num
  have hu : IsUnit (1 : ZMod 4) := isUnit_one
  have h := cleanSum_ge (M := 4) hu hs hst ht hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  set Exc : Finset ℕ := Finset.Icc (5 * r / 7) (5 * r / 7 + 2) ∪ {r} with hExc
  have hcard : Exc.card ≤ 4 := by
    refine (Finset.card_union_le _ _).trans ?_
    simp only [Nat.card_Icc, Finset.card_singleton]
    omega
  have hcl : ∀ p, ⌊((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) * r⌋₊ < p →
      p ≤ ⌊((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * r⌋₊ → p.Prime → (p : ZMod 4) = 1 → p ∉ Exc →
      cleanE1 r p := by
    intro p h1 h2 hp hc hnot
    rw [floor_frac] at h1 h2
    have h4 : p % 4 = 1 := by
      have := congrArg ZMod.val hc
      rw [ZMod.val_natCast] at this
      rw [this]
      decide
    have hnot' : ¬ (5 * r / 7 ≤ p ∧ p ≤ 5 * r / 7 + 2) ∧ p ≠ r := by
      simp only [hExc, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton, not_or] at hnot
      exact hnot
    refine ⟨hp, h4, by omega, by omega⟩
  have := hr (lamInst) (r / 8) (cleanE1 r) Exc hcl
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hc4 : (Exc.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  have hm0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (defE1 r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (cleanDef (r / 8) (cleanE1 r) p : ℝ) * Real.log p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [defE1_eq]
  rw [e]
  refine le_trans ?_ this
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  apply mul_le_mul_of_nonneg_left _ hm0
  have : ((((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) ≤ 1) := by norm_num
  have e2 : (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) / 2 = 1 / 7 := by
    norm_num
  rw [e2]
  nlinarith [hlog, hc4]

end CatalanFrames.Lambda
