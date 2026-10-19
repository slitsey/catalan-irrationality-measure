module

public import CatalanCore.Arith.Hybrid.DefC5Tab
public import CatalanCore.Arith.Hybrid.DefC5
public import CatalanCore.Arith.Hybrid.DefBFinal

@[expose] public section

/-!
# Theorem C5: the reduction matrix `B̄` in block form

The index types: `BU = U = [r - p, k)` (unpaired low block, weight `0`), `BP = 𝒫 = C ∖ U`.
`T5, Up5, Wp5, Mp5` are the blocks of `B̄` in `(U ⊕ X) ⊕ 𝒫` built from `TcF`
(`hred5`: they reduce the entries of `Full(X)` under the D2 weights).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Defs

variable (p r k : ℕ)

/-- The low block `U`. -/
abbrev BU := {c : Fin r // r - p ≤ (c : ℕ) ∧ (c : ℕ) < k}
/-- The block `𝒫 = C ∖ U`. -/
abbrev BP := {c : Fin r // ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)}

variable (m : ℕ)

/-- Reindexing `Fin r ⊕ Fin m ≃ (U ⊕ X) ⊕ 𝒫`. -/
def eU : Fin r ⊕ Fin m ≃ (BU p r k ⊕ Fin m) ⊕ BP p r k :=
  (((Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm).sumCongr
      (Equiv.refl (Fin m))).trans
    ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

variable {p r k m}

lemma eU_inl_pos {c : Fin r} (h : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) :
    eU p r k m (Sum.inl c) = Sum.inl (Sum.inl ⟨c, h⟩) := by
  have h1 : (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm c =
      Sum.inl ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_pos _ (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) _ c h
  simp [eU, h1]

lemma eU_inl_neg {c : Fin r} (h : ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)) :
    eU p r k m (Sum.inl c) = Sum.inr ⟨c, h⟩ := by
  have h1 : (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)).symm c =
      Sum.inr ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_neg _ (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) _ c h
  simp [eU, h1]

lemma eU_inr (i : Fin m) : eU p r k m (Sum.inr i) = Sum.inl (Sum.inr i) := by
  simp [eU]

lemma card_BU_BP : Fintype.card (BP p r k) + Fintype.card (BU p r k) = r := by
  have := Fintype.card_congr
    (Equiv.sumCompl (fun c : Fin r => r - p ≤ (c : ℕ) ∧ (c : ℕ) < k))
  rw [Fintype.card_sum, Fintype.card_fin] at this
  have h2 : Fintype.card (BP p r k) =
      Fintype.card {c : Fin r // ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)} := Fintype.card_congr (Equiv.refl _)
  have h3 : Fintype.card (BU p r k) =
      Fintype.card {c : Fin r // r - p ≤ (c : ℕ) ∧ (c : ℕ) < k} := Fintype.card_congr (Equiv.refl _)
  omega

end Defs

section Mats

variable (p : ℕ) [Fact p.Prime] (r k m : ℕ)

/-- Row label of `U ⊕ X`. -/
def rowlab : BU p r k ⊕ Fin m → ℕ := Sum.elim (fun u => (u.1 : ℕ)) (fun x => r + 2 * (x : ℕ))
/-- Column label of `U ⊕ Y`. -/
def collab : BU p r k ⊕ Fin m → ℕ := Sum.elim (fun u => (u.1 : ℕ)) (fun y => r + 2 * (y : ℕ) + 1)

noncomputable def T5 : Matrix (BU p r k ⊕ Fin m) (BU p r k ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TcF p r k (rowlab p r k m a) (collab p r k m b)) +
    (match a, b with
      | Sum.inl u, Sum.inl w => if u = w then rfX p else 0
      | _, _ => 0)

noncomputable def Up5 : Matrix (BU p r k ⊕ Fin m) (BP p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun a c => rfC p (TcF p r k (rowlab p r k m a) (c.1 : ℕ))

noncomputable def Wp5 : Matrix (BP p r k) (BU p r k ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun c b => rfC p (TcF p r k (c.1 : ℕ) (collab p r k m b))

noncomputable def Mp5 : Matrix (BP p r k) (BP p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun c d => rfC p (TcF p r k (c.1 : ℕ) (d.1 : ℕ))

/-- The reduction matrix on `Fin r ⊕ Fin m`. -/
noncomputable def BTc : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TcF p r k (Frame.hybRow r m a) (Frame.hybCol r m b)) +
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' ∧ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) then rfX p else 0
      | _, _ => 0)

lemma BTc_eq (a b : Fin r ⊕ Fin m) :
    fromBlocks (T5 p r k m) (Up5 p r k m) (Wp5 p r k m) (Mp5 p r k) (eU p r k m a) (eU p r k m b) =
      BTc p r k m a b := by
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hc : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k <;> by_cases hc' : r - p ≤ (c' : ℕ) ∧ (c' : ℕ) < k
    · rw [eU_inl_pos hc, eU_inl_pos hc']
      have hc1 : r ≤ (c : ℕ) + p := by omega
      simp [T5, BTc, rowlab, collab, Frame.hybRow, Frame.hybCol, Fin.ext_iff, Subtype.ext_iff, hc1, hc.2]
    · rw [eU_inl_pos hc, eU_inl_neg hc']
      have hne : c ≠ c' := fun h => hc' (h ▸ hc)
      simp [Up5, BTc, rowlab, Frame.hybRow, Frame.hybCol, hne]
    · rw [eU_inl_neg hc, eU_inl_pos hc']
      have hne : c ≠ c' := fun h => hc (h ▸ hc')
      simp [Wp5, BTc, collab, Frame.hybRow, Frame.hybCol, hne]
    · rw [eU_inl_neg hc, eU_inl_neg hc']
      simp [Mp5, BTc, Frame.hybRow, Frame.hybCol]
      intro _ h2 h3
      exact absurd ⟨by omega, h3⟩ hc
  · by_cases hc : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
    · rw [eU_inl_pos hc, eU_inr]
      simp [T5, BTc, rowlab, collab, Frame.hybRow, Frame.hybCol]
    · rw [eU_inl_neg hc, eU_inr]
      simp [Wp5, BTc, collab, Frame.hybRow, Frame.hybCol]
  · by_cases hc : r - p ≤ (c' : ℕ) ∧ (c' : ℕ) < k
    · rw [eU_inr, eU_inl_pos hc]
      simp [T5, BTc, rowlab, collab, Frame.hybRow, Frame.hybCol]
    · rw [eU_inr, eU_inl_neg hc]
      simp [Up5, BTc, rowlab, Frame.hybRow, Frame.hybCol]
  · rw [eU_inr, eU_inr]
    simp [T5, BTc, rowlab, collab, Frame.hybRow, Frame.hybCol]

end Mats

end CatalanCore.Arith.Hybrid
