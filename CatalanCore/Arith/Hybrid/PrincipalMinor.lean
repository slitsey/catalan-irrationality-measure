module

public import CatalanCore.Arith.Hybrid.Majorant
public import Mathlib.GroupTheory.Perm.ViaEmbedding

@[expose] public section

/-!
# Principal restrictions preserve a tropical denominator bound

All weights are natural numbers. A permutation of a subset extends by the identity,
so its weight is at most the tropical value on the full index set.
-/

open Finset Polynomial Matrix

namespace CatalanCore.Arith.Hybrid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tropVal_embedding_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : ι → ι → ℕ) (e : κ ↪ ι) :
    tropVal (fun a b : κ => W (e a) (e b)) ≤ tropVal W := by
  classical
  apply tropVal_le_of_forall
  intro σ
  let τ : Equiv.Perm ι := σ.viaEmbedding e
  have hτ (a : κ) : τ (e a) = e (σ a) := σ.viaEmbedding_apply e a
  calc
    ∑ b : κ, W (e (σ b)) (e b) = ∑ b ∈ Finset.univ.image e, W (τ b) b := by
      calc
        _ = ∑ b : κ, W (τ (e b)) (e b) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hτ]
        _ = _ := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact e.injective h
    _ ≤ ∑ b : ι, W (τ b) b := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ tropVal W := le_tropVal W τ

theorem tropVal_subtype_le (W : ι → ι → ℕ) (s : Finset ι) :
    tropVal (fun a b : s => W a b) ≤ tropVal W :=
  tropVal_embedding_le W ⟨Subtype.val, Subtype.val_injective⟩

theorem det_submatrix_gle {p : ℕ} [Fact p.Prime]
    (M : Matrix ι ι ℚ[X]) (W : ι → ι → ℕ)
    (h : ∀ a b, GLE p (W a b) (M a b)) (s : Finset ι) :
    GLE p (tropVal W) (M.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  exact (det_gle (M.submatrix (Subtype.val : s → ι) Subtype.val)
    (fun a b : s => W a b) (fun a b => h a b)).mono (tropVal_subtype_le W s)

end CatalanCore.Arith.Hybrid
