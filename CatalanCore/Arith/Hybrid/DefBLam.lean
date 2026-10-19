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

lemma lift_good {w : ℕ} {x : ℚ} {y : ZMod p} (h : Good p ((p : ℚ) ^ w * x) y) :
    ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ w) * C x ∧ phiP p g = rfC p y := by
  obtain ⟨g, h1, h2⟩ := exists_lift_const p w x h.1
  refine ⟨g, h1, ?_⟩
  rw [h2]
  congr 1
  exact h.2

end Mat

section Hred

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

lemma hybRow_lt (a : Fin r ⊕ Fin m) : Frame.hybRow r m a < r + 2 * m := by
  rcases a with c | i
  · have := c.2; simp [Frame.hybRow] <;> omega
  · have := i.2; simp [Frame.hybRow] <;> omega

lemma hybCol_lt (a : Fin r ⊕ Fin m) : Frame.hybCol r m a < r + 2 * m := by
  rcases a with c | i
  · have := c.2; simp [Frame.hybCol] <;> omega
  · have := i.2; simp [Frame.hybCol] <;> omega

/-- Off-diagonal labels. -/
lemma lift_offdiag (hL : LamData Fr) (S : BSetup p r m j k) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (uPot p r k A + uPot p r k B)) * C (Fr.Mn A B) ∧
      phiP p g = rfC p (Tfull p j k A B) := by
  rcases lt_or_gt_of_ne hAB with h | h
  · have := good_TB hL S h hB
    have e : Tfull p j k A B = TB p j k A B := by unfold Tfull; rw [if_pos h]
    rw [e]; exact lift_good p this
  · have := good_TB hL S h hA
    have e : Tfull p j k A B = TB p j k B A := by
      unfold Tfull; rw [if_neg (by omega), if_pos h]
    rw [e, add_comm (uPot p r k A), Mn_symm]; exact lift_good p this

/-- **The entries of `Full(X)` reduce to the table `BT`.** -/
theorem hred_B (hL : LamData Fr) (S : BSetup p r m j k) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (uPot p r k (Frame.hybRow r m a) + uPot p r k (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧ phiP p g = BT p r m j k a b := by
  have hA := hybRow_lt (r := r) (m := m) a
  have hB := hybCol_lt (r := r) (m := m) b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hcr := c.2
      have hgood := good_TD hL S (A := (c : ℕ)) hcr
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (uPot p r k c + uPot p r k c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ = TD p j k c := hgood.2
        rw [e1]
        have e2 : Tfull p j k c c = TD p j k c := by
          unfold Tfull; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
        have e3 : uPot p r k (c : ℕ) = 0 ↔ (c : ℕ) < k := by
          by_cases hck : (c : ℕ) < k
          · have h' : ¬ k ≤ (c : ℕ) := by omega
            simp [uPot, hcr, h', hck]
          · have h' : k ≤ (c : ℕ) := by omega
            simp [uPot, hcr, h', hck]
        rw [add_comm]
        simp [BT, Frame.hybRow, Frame.hybCol, e2, e3]
    · have hne : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
      obtain ⟨g, h1, h2⟩ := lift_offdiag hL S hne (by have := c.2; omega) (by have := c'.2; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BT, hcc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiag hL S (A := c) (B := r + 2 * (i' : ℕ) + 1) (by have := c.2; omega)
      (by have := c.2; omega) hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BT, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiag hL S (A := r + 2 * (i : ℕ)) (B := c') (by have := c'.2; omega)
      hA (by have := c'.2; omega)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BT, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiag hL S (A := r + 2 * (i : ℕ)) (B := r + 2 * (i' : ℕ) + 1)
      (by omega) hA hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BT, Frame.hybRow, Frame.hybCol]

end Hred

end CatalanCore.Arith.Hybrid
