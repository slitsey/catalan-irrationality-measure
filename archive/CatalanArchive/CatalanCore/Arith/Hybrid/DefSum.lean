module

public import CatalanCore.Arith.Hybrid.LemmaE.Summation
public import CatalanCore.Arith.Hybrid.DefRank

@[expose] public section

/-!
# Generic summation of deficit families

A *deficit family* is a function `δ : ℕ → ℕ` with `DefHypT I r m T δ`.  This file collects the
frame-independent combinators that let the families of Lemma E, B, C5, C7, GK be plugged in one at
a time:

* `DefHypT.mono_T`: a larger exponent bound keeps the family valid;
* `DefHypT.glue`: replace the deficit on a window `S` by another valid family;
* `defSum_ge`: if `δ ≥ ∑ᵢ δᵢ` pointwise and `∑ δᵢ log p ≥ Lᵢ`, then `∑ δ log p ≥ ∑ Lᵢ`;
* `layer_le`: layer-cake lower bound `∑ⱼ ∑_{p ∈ Sⱼ} w p ≤ ∑_p δ p w p` for staircase deficits.
-/

open Finset Filter CatalanCore.Arith

namespace CatalanCore.Arith.Hybrid

section Glue

variable {Fr : Frame} {I : HybInst Fr} {r m : ℕ}

lemma DefHypT.mono_T {T T' δ : ℕ → ℕ} (h : DefHypT I r m T δ)
    (hle : ∀ p, p.Prime → p < Bnd I r m → T p ≤ T' p) : DefHypT I r m T' δ := by
  intro p hp hb
  obtain ⟨h1, h2⟩ := h p hp hb
  refine ⟨h1.trans (hle p hp hb), fun [Fact p.Prime] => (h2).mono ?_⟩
  have := hle p hp hb
  omega

/-- Replace the deficit by `δ₂` on the set `S` (no disjointness needed). -/
lemma DefHypT.glue {T δ₁ δ₂ : ℕ → ℕ} (S : ℕ → Prop) [DecidablePred S]
    (h1 : DefHypT I r m T δ₁) (h2 : DefHypT I r m T δ₂) :
    DefHypT I r m T (fun p => if S p then δ₂ p else δ₁ p) := by
  intro p hp hb
  by_cases hS : S p
  · simpa only [if_pos hS] using h2 p hp hb
  · simpa only [if_neg hS] using h1 p hp hb

end Glue

section Sums

/-- **Sum of deficit families.**  If `δ` dominates `∑ᵢ δᵢ` on `P` and each family has a lower bound
`Lᵢ` on its `log`-weighted sum, then `δ` has the sum of the bounds. -/
lemma defSum_ge {ι : Type*} (s : Finset ι) (P : Finset ℕ) (δ : ℕ → ℕ) (δi : ι → ℕ → ℕ)
    (L : ι → ℝ) (hdom : ∀ p ∈ P, ∑ i ∈ s, δi i p ≤ δ p)
    (hL : ∀ i ∈ s, L i ≤ ∑ p ∈ P, (δi i p : ℝ) * Real.log p)
    (hlog : ∀ p ∈ P, 0 ≤ Real.log p) :
    ∑ i ∈ s, L i ≤ ∑ p ∈ P, (δ p : ℝ) * Real.log p := by
  calc ∑ i ∈ s, L i ≤ ∑ i ∈ s, ∑ p ∈ P, (δi i p : ℝ) * Real.log p := Finset.sum_le_sum hL
    _ = ∑ p ∈ P, (∑ i ∈ s, (δi i p : ℝ)) * Real.log p := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ ∑ p ∈ P, (δ p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum fun p hp => ?_
        refine mul_le_mul_of_nonneg_right ?_ (hlog p hp)
        exact_mod_cast hdom p hp

/-- Layer-cake lower bound for a staircase deficit. -/
lemma layer_le (S : Finset ℕ) (δ : ℕ → ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p) (J : ℕ)
    (Sj : ℕ → Finset ℕ) (hsub : ∀ j, Sj j ⊆ S) (hδ : ∀ j p, p ∈ Sj j → j ≤ δ p) :
    ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ Sj j, w p ≤ ∑ p ∈ S, (δ p : ℝ) * w p := by
  classical
  have e : ∀ j, ∑ p ∈ Sj j, w p = ∑ p ∈ S, if p ∈ Sj j then w p else 0 := by
    intro j
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsub j h, h⟩, fun h => h.2⟩
  simp_rw [e]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hw p hp)
  have hc : ((Finset.Icc 1 J).filter (fun j => p ∈ Sj j)).card ≤ δ p := by
    have : (Finset.Icc 1 J).filter (fun j => p ∈ Sj j) ⊆ Finset.Icc 1 (δ p) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      exact ⟨hj.1.1, hδ j p hj.2⟩
    simpa using Finset.card_le_card this
  exact_mod_cast hc

end Sums

end CatalanCore.Arith.Hybrid
