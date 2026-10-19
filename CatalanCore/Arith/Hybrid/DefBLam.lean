module

public import CatalanCore.Arith.Hybrid.LamEntries
public import CatalanCore.Arith.Hybrid.DefBC5

@[expose] public section

/-!
# Theorem B for a λ-like frame: the reduction matrix and its entries

The matrix `B̄` of Theorem B in the index type `Fin r ⊕ Fin m`, built from the label-level residue
table `Tfull` (`TB`, `TD` of `LamEntries`), the block equivalence `eB` onto
`(B0 ⊕ X) ⊕ B1`, and the lifts (`hred`).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Defs

variable (p : ℕ) [Fact p.Prime] (r m j k : ℕ)

/-- The symmetric residue table on labels. -/
noncomputable def Tfull (A B : ℕ) : ZMod p :=
  if A < B then TB p j k A B else if B < A then TB p j k B A else TD p j k A

/-- Blocks of `C`. -/
abbrev Blk0 (r k : ℕ) := {c : Fin r // (c : ℕ) < k}
abbrev Blk1 (r k : ℕ) := {c : Fin r // ¬ (c : ℕ) < k}

/-- Reindexing `Fin r ⊕ Fin m ≃ (B0 ⊕ X) ⊕ B1`. -/
def eB (r m k : ℕ) : Fin r ⊕ Fin m ≃ (Blk0 r k ⊕ Fin m) ⊕ Blk1 r k :=
  (((Equiv.sumCompl (fun c : Fin r => (c : ℕ) < k)).symm).sumCongr (Equiv.refl (Fin m))).trans
    ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

lemma eB_inl_pos {c : Fin r} (h : (c : ℕ) < k) :
    eB r m k (Sum.inl c) = Sum.inl (Sum.inl ⟨c, h⟩) := by
  have h1 : (Equiv.sumCompl (fun c : Fin r => (c : ℕ) < k)).symm c = Sum.inl ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_pos _ (fun c : Fin r => (c : ℕ) < k) _ c h
  simp [eB, h1]

lemma eB_inl_neg {c : Fin r} (h : ¬ (c : ℕ) < k) :
    eB r m k (Sum.inl c) = Sum.inr ⟨c, h⟩ := by
  have h1 : (Equiv.sumCompl (fun c : Fin r => (c : ℕ) < k)).symm c = Sum.inr ⟨c, h⟩ :=
    @Equiv.sumCompl_symm_apply_of_neg _ (fun c : Fin r => (c : ℕ) < k) _ c h
  simp [eB, h1]

lemma eB_inr (i : Fin m) : eB r m k (Sum.inr i) = Sum.inl (Sum.inr i) := by
  simp [eB]

lemma Tfull_symm (A B : ℕ) : Tfull p j k A B = Tfull p j k B A := by
  unfold Tfull
  by_cases h : A < B
  · rw [if_pos h, if_neg (by omega), if_pos h]
  · by_cases h' : B < A
    · rw [if_neg h, if_pos h', if_pos h']
    · have : A = B := by omega
      subst this; rfl

lemma Tfull_ge_k {A B : ℕ} (hA : k ≤ A) (hB : k ≤ B) (hAB : A ≠ B) : Tfull p j k A B = 0 := by
  unfold Tfull TB
  by_cases h : A < B
  · rw [if_pos h, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega), if_neg (by omega), if_neg (by omega)]

lemma Tfull_diag_ge {A : ℕ} (hA : k ≤ A) :
    Tfull p j k A A = (((j : ℕ) : ZMod p)⁻¹) ^ 2 := by
  unfold Tfull TD
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_neg (by omega)]

end Defs

section Mat

variable (p : ℕ) [Fact p.Prime] (r m j k : ℕ)

/-- The parameters of `BbarB` for Theorem B. -/
noncomputable def A0L : Matrix (Blk0 r k) (Blk0 r k) (RatFunc (ZMod p)) :=
  Matrix.of fun u w => rfC p (Tfull p j k u.1 w.1) + (if u = w then rfX p else 0)

noncomputable def VL : Matrix (Blk0 r k) (Blk1 r k) (RatFunc (ZMod p)) :=
  Matrix.of fun u c => rfC p (Tfull p j k u.1 c.1)

noncomputable def piL : RatFunc (ZMod p) := rfC p ((((j : ℕ) : ZMod p)⁻¹) ^ 2)

noncomputable def GxL : Matrix (Fin m) (Blk0 r k) (RatFunc (ZMod p)) :=
  Matrix.of fun x u => rfC p (Tfull p j k (r + 2 * (x : ℕ)) u.1)

noncomputable def GyL : Matrix (Blk0 r k) (Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun u y => rfC p (Tfull p j k u.1 (r + 2 * (y : ℕ) + 1))

/-- The target reduction matrix on `Fin r ⊕ Fin m`. -/
noncomputable def BT : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (Tfull p j k (Frame.hybRow r m a) (Frame.hybCol r m b)) +
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' ∧ (c : ℕ) < k then rfX p else 0
      | _, _ => 0)

lemma BT_eq (hkr : k ≤ r) (a b : Fin r ⊕ Fin m) :
    BbarB (A0L p r j k) (VL p r j k) (piL p j) (GxL p r m j k) (GyL p r m j k)
      (eB r m k a) (eB r m k b) = BT p r m j k a b := by
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hc : (c : ℕ) < k <;> by_cases hc' : (c' : ℕ) < k
    · rw [eB_inl_pos r m k hc, eB_inl_pos r m k hc']
      simp [BbarB, A0L, BT, Frame.hybRow, Frame.hybCol, Fin.ext_iff, Subtype.ext_iff, hc]
    · rw [eB_inl_pos r m k hc, eB_inl_neg r m k hc']
      have hne : (c : ℕ) ≠ c' := by omega
      simp [BbarB, VL, BT, Frame.hybRow, Frame.hybCol, hne]
      intro h; exact absurd (by rw [h]) hne
    · rw [eB_inl_neg r m k hc, eB_inl_pos r m k hc']
      have hne : (c : ℕ) ≠ c' := by omega
      simp [BbarB, VL, BT, Frame.hybRow, Frame.hybCol, hne, Tfull_symm p j k (c : ℕ) c', Fin.ext_iff]
    · rw [eB_inl_neg r m k hc, eB_inl_neg r m k hc']
      by_cases hcc : (c : ℕ) = c'
      · simp [BbarB, piL, BT, Frame.hybRow, Frame.hybCol, hcc, Tfull_diag_ge p j k (show k ≤ (c' : ℕ) by omega),
          Fin.ext_iff, Subtype.ext_iff, Matrix.one_apply]
        intro h; omega
      · have hz := Tfull_ge_k p j k (show k ≤ (c : ℕ) by omega) (show k ≤ (c' : ℕ) by omega) hcc
        simp [BbarB, piL, BT, Frame.hybRow, Frame.hybCol, hz, rfC_zero, Matrix.one_apply, Fin.ext_iff,
          Subtype.ext_iff, hcc]
  · by_cases hc : (c : ℕ) < k
    · rw [eB_inl_pos r m k hc, eB_inr]
      simp [BbarB, GyL, BT, Frame.hybRow, Frame.hybCol]
    · rw [eB_inl_neg r m k hc, eB_inr]
      have hz := Tfull_ge_k p j k (show k ≤ (c : ℕ) by omega)
        (show k ≤ r + 2 * (i' : ℕ) + 1 by omega) (by have := c.2; omega)
      simp [BbarB, BT, Frame.hybRow, Frame.hybCol, hz, rfC_zero]
  · by_cases hc : (c' : ℕ) < k
    · rw [eB_inr, eB_inl_pos r m k hc]
      simp [BbarB, GxL, BT, Frame.hybRow, Frame.hybCol]
    · rw [eB_inr, eB_inl_neg r m k hc]
      have hz := Tfull_ge_k p j k (show k ≤ r + 2 * (i : ℕ) by omega)
        (show k ≤ (c' : ℕ) by omega) (by have := c'.2; omega)
      simp [BbarB, BT, Frame.hybRow, Frame.hybCol, hz, rfC_zero]
  · rw [eB_inr, eB_inr]
    have hz := Tfull_ge_k p j k (show k ≤ r + 2 * (i : ℕ) by omega)
      (show k ≤ r + 2 * (i' : ℕ) + 1 by omega) (by omega)
    simp [BbarB, BT, Frame.hybRow, Frame.hybCol, hz, rfC_zero]

end Mat

end CatalanCore.Arith.Hybrid
