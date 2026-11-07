module

public import CatalanCore.Arith.Hybrid.DefC7Tab
public import CatalanCore.Arith.Hybrid.DefC5
public import CatalanCore.Arith.Hybrid.DefBFinal

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4): the reduction matrix `B̄` in block form

The index types: `BU7 = U = [r - p, k)` (unpaired low block, weight `0`), `BP7 = 𝒫 = C ∖ U`.
`T57, Up57, Wp57, Mp57` are the blocks of `B̄` in `(U ⊕ X) ⊕ 𝒫` built from `TcF7`
(`hred5`: they reduce the entries of `Full(X)` under the D2 weights).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Defs7

variable (p r k : ℕ)

/-- The low block `U`. -/
abbrev BU7 := {c : Fin r // r - p ≤ (c : ℕ) ∧ (c : ℕ) < k}
/-- The block `𝒫 = C ∖ U`. -/
abbrev BP7 := {c : Fin r // ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)}

variable (m : ℕ)

/-- Reindexing `Fin r ⊕ Fin m ≃ (U ⊕ X) ⊕ 𝒫`. -/
def eU7 : Fin r ⊕ Fin m ≃ (BU7 p r k ⊕ Fin m) ⊕ BP7 p r k :=
  (((Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm).sumCongr
      (Equiv.refl (Fin m))).trans
    ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

variable {p r k m}

lemma eU7_inl_pos {c : Fin r} (h : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) :
    eU7 p r k m (Sum.inl c) = Sum.inl (Sum.inl ⟨c, h⟩) := by
  have h1 : (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm c =
      Sum.inl ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_pos _ (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) _ c h
  simp [eU7, h1]

lemma eU7_inl_neg {c : Fin r} (h : ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)) :
    eU7 p r k m (Sum.inl c) = Sum.inr ⟨c, h⟩ := by
  have h1 : (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm c =
      Sum.inr ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_neg _ (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) _ c h
  simp [eU7, h1]

lemma eU7_inr (i : Fin m) : eU7 p r k m (Sum.inr i) = Sum.inl (Sum.inr i) := by
  simp [eU7]

lemma card_BU_BP7 : Fintype.card (BP7 p r k) + Fintype.card (BU7 p r k) = r := by
  have := Fintype.card_congr
    (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k))
  rw [Fintype.card_sum, Fintype.card_fin] at this
  have h2 : Fintype.card (BP7 p r k) =
      Fintype.card {c : Fin r // ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)} := Fintype.card_congr (Equiv.refl _)
  have h3 : Fintype.card (BU7 p r k) =
      Fintype.card {c : Fin r // r - p ≤ (c : ℕ) ∧ (c : ℕ) < k} := Fintype.card_congr (Equiv.refl _)
  omega

end Defs7

section Mats7

variable (p : ℕ) [Fact p.Prime] (r k m : ℕ)

/-- Row label of `U ⊕ X`. -/
def rowlab7 : BU7 p r k ⊕ Fin m → ℕ := Sum.elim (fun u => (u.1 : ℕ)) (fun x => r + 2 * (x : ℕ))
/-- Column label of `U ⊕ Y`. -/
def collab7 : BU7 p r k ⊕ Fin m → ℕ := Sum.elim (fun u => (u.1 : ℕ)) (fun y => r + 2 * (y : ℕ) + 1)

noncomputable def T57 : Matrix (BU7 p r k ⊕ Fin m) (BU7 p r k ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TcF7 p r k (rowlab7 p r k m a) (collab7 p r k m b)) +
    (match a, b with
      | Sum.inl u, Sum.inl w => if u = w then rfX p else 0
      | _, _ => 0)

noncomputable def Up57 : Matrix (BU7 p r k ⊕ Fin m) (BP7 p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun a c => rfC p (TcF7 p r k (rowlab7 p r k m a) (c.1 : ℕ))

noncomputable def Wp57 : Matrix (BP7 p r k) (BU7 p r k ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun c b => rfC p (TcF7 p r k (c.1 : ℕ) (collab7 p r k m b))

noncomputable def Mp57 : Matrix (BP7 p r k) (BP7 p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun c d => rfC p (TcF7 p r k (c.1 : ℕ) (d.1 : ℕ))

/-- The reduction matrix on `Fin r ⊕ Fin m`. -/
noncomputable def BTc7 : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TcF7 p r k (Frame.hybRow r m a) (Frame.hybCol r m b)) +
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' ∧ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) then rfX p else 0
      | _, _ => 0)

lemma BTc7_eq (a b : Fin r ⊕ Fin m) :
    fromBlocks (T57 p r k m) (Up57 p r k m) (Wp57 p r k m) (Mp57 p r k) (eU7 p r k m a) (eU7 p r k m b) =
      BTc7 p r k m a b := by
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hc : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k <;> by_cases hc' : r - p ≤ (c' : ℕ) ∧ (c' : ℕ) < k
    · rw [eU7_inl_pos hc, eU7_inl_pos hc']
      have hc1 : r ≤ (c : ℕ) + p := by omega
      simp [T57, BTc7, rowlab7, collab7, Frame.hybRow, Frame.hybCol, Fin.ext_iff, Subtype.ext_iff, hc1, hc.2]
    · rw [eU7_inl_pos hc, eU7_inl_neg hc']
      have hne : c ≠ c' := fun h => hc' (h ▸ hc)
      simp [Up57, BTc7, rowlab7, Frame.hybRow, Frame.hybCol, hne]
    · rw [eU7_inl_neg hc, eU7_inl_pos hc']
      have hne : c ≠ c' := fun h => hc (h ▸ hc')
      simp [Wp57, BTc7, collab7, Frame.hybRow, Frame.hybCol, hne]
    · rw [eU7_inl_neg hc, eU7_inl_neg hc']
      simp [Mp57, BTc7, Frame.hybRow, Frame.hybCol]
      intro _ h2 h3
      exact absurd ⟨by omega, h3⟩ hc
  · by_cases hc : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
    · rw [eU7_inl_pos hc, eU7_inr]
      simp [T57, BTc7, rowlab7, collab7, Frame.hybRow, Frame.hybCol]
    · rw [eU7_inl_neg hc, eU7_inr]
      simp [Wp57, BTc7, collab7, Frame.hybRow, Frame.hybCol]
  · by_cases hc : r - p ≤ (c' : ℕ) ∧ (c' : ℕ) < k
    · rw [eU7_inr, eU7_inl_pos hc]
      simp [T57, BTc7, rowlab7, collab7, Frame.hybRow, Frame.hybCol]
    · rw [eU7_inr, eU7_inl_neg hc]
      simp [Up57, BTc7, rowlab7, Frame.hybRow, Frame.hybCol]
  · rw [eU7_inr, eU7_inr]
    simp [T57, BTc7, rowlab7, collab7, Frame.hybRow, Frame.hybCol]

end Mats7

end CatalanCore.Arith.Hybrid
