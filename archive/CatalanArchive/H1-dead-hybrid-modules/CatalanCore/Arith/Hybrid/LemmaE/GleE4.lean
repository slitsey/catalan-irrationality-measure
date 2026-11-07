module

public import CatalanCore.Arith.Hybrid.LemmaE.GleE3
public import CatalanCore.Arith.Hybrid.RankWit

@[expose] public section

/-!
# Lemma E, class 1: `gleAt_E` (dual form) and the dual value

`gleAt_E`: `GLE p (∑u + ∑v - m) (fullPoly)` with `∑u + ∑v = 2 (2r - p - k) + 4m` (`wE_sum`).
Together with `TE`-hypothesis `hUU` (the scalar Schur complement on `U`, supplied for λ in
`CatalanFrames.Lambda.HybLemmaE2`).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section Main

variable {o p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

/-- **Lemma E at a prime `p < r` of class 1, in dual form.** -/
theorem gleAt_E_wit {o : ℕ} (hL : LamData Fr o) (S : ESetup o p r m j k) (sU : ZMod p)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) (he : -(4 * ((j : ℕ) : ZMod p)⁻¹) + 1 ≠ 0)
    (hUU : ∀ a b : ℕ, r - p ≤ a → a < k → r - p ≤ b → b < k →
      TE p j r k a b = (16 : ZMod p)⁻¹ * ((if a = b then sU else 0) +
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹)) :
    HasRankWit Fr p r m (fun a => wE p r k (Frame.hybRow r m a))
      (fun b => wE p r k (Frame.hybCol r m b)) m := by
  have hrank := rank_BE_le S sU hj he hUU
  refine ⟨BE p j r m k, fun a b => hred_E hL S a b, ?_⟩
  omega

theorem gleAt_E {o : ℕ} (hL : LamData Fr o) (S : ESetup o p r m j k) (sU : ZMod p)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) (he : -(4 * ((j : ℕ) : ZMod p)⁻¹) + 1 ≠ 0)
    (hUU : ∀ a b : ℕ, r - p ≤ a → a < k → r - p ≤ b → b < k →
      TE p j r k a b = (16 : ZMod p)⁻¹ * ((if a = b then sU else 0) +
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹)) :
    GLE p (∑ a, wE p r k (Frame.hybRow r m a) + ∑ b, wE p r k (Frame.hybCol r m b) - m)
      (Fr.fullPoly r m) :=
  (gleAt_E_wit hL S sU hj he hUU).gle

lemma sum_wE_C (hrk : r - p ≤ k) (hkr : k ≤ r) :
    ∑ c : Fin r, wE p r k (c : ℕ) = (r - p) + (r - k) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => wE p r k i) r]
  have hg : ∀ i ∈ Finset.range r, wE p r k i = if r - p ≤ i ∧ i < k then 0 else 1 := by
    intro i hi
    unfold wE
    rw [if_pos (Finset.mem_range.1 hi)]
  rw [Finset.sum_congr rfl hg]
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hkr,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (r - p)) hrk]
  have h1 : ∑ i ∈ Finset.Ico 0 (r - p), (if r - p ≤ i ∧ i < k then 0 else 1) = r - p := by
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro i hi
      have := Finset.mem_Ico.1 hi
      rw [if_neg (by omega)]
  have h2 : ∑ i ∈ Finset.Ico (r - p) k, (if r - p ≤ i ∧ i < k then 0 else 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_Ico.1 hi
    rw [if_pos (by omega)]
  have h3 : ∑ i ∈ Finset.Ico k r, (if r - p ≤ i ∧ i < k then 0 else 1) = r - k := by
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro i hi
      have := Finset.mem_Ico.1 hi
      rw [if_neg (by omega)]
  rw [h1, h2, h3]; ring

/-- The dual value of the D-potentials. -/
lemma wE_sum (hrk : r - p ≤ k) (hkr : k ≤ r) :
    ∑ a : Fin r ⊕ Fin m, wE p r k (Frame.hybRow r m a) +
      ∑ b : Fin r ⊕ Fin m, wE p r k (Frame.hybCol r m b) =
      2 * ((r - p) + (r - k)) + 4 * m := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hz1 : ∑ i : Fin m, wE p r k (Frame.hybRow r m (Sum.inr i)) = 2 * m := by
    have : ∀ i : Fin m, wE p r k (Frame.hybRow r m (Sum.inr i)) = 2 := fun i => by
      show wE p r k (r + 2 * (i : ℕ)) = 2
      exact wE_Z (by omega)
    simp [this, mul_comm]
  have hz2 : ∑ i : Fin m, wE p r k (Frame.hybCol r m (Sum.inr i)) = 2 * m := by
    have : ∀ i : Fin m, wE p r k (Frame.hybCol r m (Sum.inr i)) = 2 := fun i => by
      show wE p r k (r + 2 * (i : ℕ) + 1) = 2
      exact wE_Z (by omega)
    simp [this, mul_comm]
  have hc : ∀ c : Fin r, wE p r k (Frame.hybRow r m (Sum.inl c)) = wE p r k (c : ℕ) := fun c => rfl
  have hc' : ∀ c : Fin r, wE p r k (Frame.hybCol r m (Sum.inl c)) = wE p r k (c : ℕ) := fun c => rfl
  simp only [hc, hc', hz1, hz2, sum_wE_C hrk hkr]
  ring

end Main

end CatalanCore.Arith.Hybrid
