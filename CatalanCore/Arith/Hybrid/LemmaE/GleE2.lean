module

public import CatalanCore.Arith.Hybrid.LemmaE.GleE

@[expose] public section

/-!
# Lemma E, class 1: the rank bound and `gleAt_E`
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section Main

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

/-- The reduction matrix in the block index type. -/
noncomputable def BmE (p j r m k : ℕ) [Fact p.Prime] :
    Matrix ((UE p r k ⊕ Fin m) ⊕ PE p r k) ((UE p r k ⊕ Fin m) ⊕ PE p r k) (RatFunc (ZMod p)) :=
  (BE p j r m k).submatrix
    (eE r m (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm
    (eE r m (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm

lemma BmE_toBlocks₁₁_ll (a a' : UE p r k) :
    (BmE p j r m k).toBlocks₁₁ (Sum.inl a) (Sum.inl a') =
      BE p j r m k (Sum.inl a.1) (Sum.inl a'.1) := by
  simp [BmE, Matrix.toBlocks₁₁, eE_symm_ll]

lemma BmE_toBlocks₁₁_lr (a : UE p r k) (y : Fin m) :
    (BmE p j r m k).toBlocks₁₁ (Sum.inl a) (Sum.inr y) =
      BE p j r m k (Sum.inl a.1) (Sum.inr y) := by
  simp [BmE, Matrix.toBlocks₁₁, eE_symm_ll, eE_symm_lr]

lemma BmE_toBlocks₁₁_rl (x : Fin m) (a : UE p r k) :
    (BmE p j r m k).toBlocks₁₁ (Sum.inr x) (Sum.inl a) =
      BE p j r m k (Sum.inr x) (Sum.inl a.1) := by
  simp [BmE, Matrix.toBlocks₁₁, eE_symm_ll, eE_symm_lr]

lemma BmE_toBlocks₁₁_rr (x y : Fin m) :
    (BmE p j r m k).toBlocks₁₁ (Sum.inr x) (Sum.inr y) =
      BE p j r m k (Sum.inr x) (Sum.inr y) := by
  simp [BmE, Matrix.toBlocks₁₁, eE_symm_lr]

lemma BmE_toBlocks₁₂_l (a : UE p r k) (c : PE p r k) :
    (BmE p j r m k).toBlocks₁₂ (Sum.inl a) c =
      BE p j r m k (Sum.inl a.1) (Sum.inl c.1) := by
  simp [BmE, Matrix.toBlocks₁₂, eE_symm_ll, eE_symm_r]

lemma BmE_toBlocks₁₂_r (x : Fin m) (c : PE p r k) :
    (BmE p j r m k).toBlocks₁₂ (Sum.inr x) c = BE p j r m k (Sum.inr x) (Sum.inl c.1) := by
  simp [BmE, Matrix.toBlocks₁₂, eE_symm_lr, eE_symm_r]

lemma BmE_toBlocks₂₁_l (c : PE p r k) (a : UE p r k) :
    (BmE p j r m k).toBlocks₂₁ c (Sum.inl a) =
      BE p j r m k (Sum.inl c.1) (Sum.inl a.1) := by
  simp [BmE, Matrix.toBlocks₂₁, eE_symm_ll, eE_symm_r]

lemma BmE_toBlocks₂₁_r (c : PE p r k) (y : Fin m) :
    (BmE p j r m k).toBlocks₂₁ c (Sum.inr y) = BE p j r m k (Sum.inl c.1) (Sum.inr y) := by
  simp [BmE, Matrix.toBlocks₂₁, eE_symm_lr, eE_symm_r]

lemma BmE_toBlocks₂₂ (c c' : PE p r k) :
    (BmE p j r m k).toBlocks₂₂ c c' = BE p j r m k (Sum.inl c.1) (Sum.inl c'.1) := by
  simp [BmE, Matrix.toBlocks₂₂, eE_symm_r]

lemma wE_u (a : UE p r k) : wE p r k (a.1 : ℕ) = 0 := wE_U a.2.1 a.2.2 a.1.2

lemma wE_c (c : PE p r k) : wE p r k (c.1 : ℕ) = 1 := wE_P c.2 c.1.2

end Main

end CatalanCore.Arith.Hybrid
