module

public import CatalanCore.Uniform.Content.Smith.LP2Entries

@[expose] public section

/-!
# LP2 for a general two-term frame: the reduction matrix `B̄` and its entries

The matrix `BTg` on `Fin r ⊕ Fin m` built from the symmetric label table `Tsym` (`Tg`/`Td` of
`LP2Table`), the block equivalence `eB` onto `(B0 ⊕ X) ⊕ B1` of `DefBLam`, and the lifts
(`LP2Hyp.hred`: every entry of `Full(X)` scaled by the D4 potentials lifts to an integral polynomial
reducing to the corresponding entry of `BTg`).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

section Defs

variable (p : ℕ) [Fact p.Prime] (r m k : ℕ) (nr v : ZMod p)

/-- The symmetric residue table on labels. -/
noncomputable def Tsym (A B : ℕ) : ZMod p :=
  if A < B then Tg p k nr v A B else if B < A then Tg p k nr v B A else Td p k nr v A

lemma Tsym_symm (A B : ℕ) : Tsym p k nr v A B = Tsym p k nr v B A := by
  unfold Tsym
  by_cases h : A < B
  · rw [if_pos h, if_neg (by omega), if_pos h]
  · by_cases h' : B < A
    · rw [if_neg h, if_pos h', if_pos h']
    · have : A = B := by omega
      subst this; rfl

lemma Tsym_ge_k {A B : ℕ} (hA : k ≤ A) (hB : k ≤ B) (hAB : A ≠ B) : Tsym p k nr v A B = 0 := by
  unfold Tsym
  by_cases h : A < B
  · rw [if_pos h]; unfold Tg; rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]; unfold Tg; rw [if_neg (by omega), if_neg (by omega)]

lemma Tsym_diag_ge {A : ℕ} (hA : k ≤ A) : Tsym p k nr v A A = nr⁻¹ * v ^ 2 := by
  unfold Tsym Td
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_neg (by omega)]

lemma Tsym_diag_lt {A : ℕ} (hA : A < k) : Tsym p k nr v A A = nr⁻¹ * E2 k A := by
  unfold Tsym Td
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos hA]

end Defs

section Mat

variable (p : ℕ) [Fact p.Prime] (r m k : ℕ) (nr v : ZMod p)

noncomputable def A0g : Matrix (Blk0 r k) (Blk0 r k) (RatFunc (ZMod p)) :=
  Matrix.of fun u w => rfC p (Tsym p k nr v u.1 w.1) + (if u = w then rfX p else 0)

noncomputable def Vg : Matrix (Blk0 r k) (Blk1 r k) (RatFunc (ZMod p)) :=
  Matrix.of fun u c => rfC p (Tsym p k nr v u.1 c.1)

noncomputable def piG : RatFunc (ZMod p) := rfC p (nr⁻¹ * v ^ 2)

noncomputable def GxG : Matrix (Fin m) (Blk0 r k) (RatFunc (ZMod p)) :=
  Matrix.of fun x u => rfC p (Tsym p k nr v (r + 2 * (x : ℕ)) u.1)

noncomputable def GyG : Matrix (Blk0 r k) (Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun u y => rfC p (Tsym p k nr v u.1 (r + 2 * (y : ℕ) + 1))

/-- The target reduction matrix on `Fin r ⊕ Fin m`. -/
noncomputable def BTg : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (Tsym p k nr v (Frame.hybRow r m a) (Frame.hybCol r m b)) +
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' ∧ (c : ℕ) < k then rfX p else 0
      | _, _ => 0)

lemma BTg_eq (hkr : k ≤ r) (a b : Fin r ⊕ Fin m) :
    BbarB (A0g p r k nr v) (Vg p r k nr v) (piG p nr v) (GxG p r m k nr v) (GyG p r m k nr v)
      (eB r m k a) (eB r m k b) = BTg p r m k nr v a b := by
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hc : (c : ℕ) < k <;> by_cases hc' : (c' : ℕ) < k
    · rw [eB_inl_pos r m k hc, eB_inl_pos r m k hc']
      simp [BbarB, A0g, BTg, Frame.hybRow, Frame.hybCol, Fin.ext_iff, Subtype.ext_iff, hc]
    · rw [eB_inl_pos r m k hc, eB_inl_neg r m k hc']
      have hne : (c : ℕ) ≠ c' := by omega
      simp [BbarB, Vg, BTg, Frame.hybRow, Frame.hybCol, hne]
      intro h; exact absurd (by rw [h]) hne
    · rw [eB_inl_neg r m k hc, eB_inl_pos r m k hc']
      have hne : (c : ℕ) ≠ c' := by omega
      simp [BbarB, Vg, BTg, Frame.hybRow, Frame.hybCol, hne, Tsym_symm p k nr v (c : ℕ) c',
        Fin.ext_iff]
    · rw [eB_inl_neg r m k hc, eB_inl_neg r m k hc']
      by_cases hcc : (c : ℕ) = c'
      · simp [BbarB, piG, BTg, Frame.hybRow, Frame.hybCol, hcc,
          Tsym_diag_ge p k nr v (show k ≤ (c' : ℕ) by omega),
          Fin.ext_iff, Subtype.ext_iff, Matrix.one_apply]
        intro h; omega
      · have hz := Tsym_ge_k p k nr v (show k ≤ (c : ℕ) by omega) (show k ≤ (c' : ℕ) by omega) hcc
        simp [BbarB, piG, BTg, Frame.hybRow, Frame.hybCol, hz, rfC_zero, Matrix.one_apply,
          Fin.ext_iff, Subtype.ext_iff, hcc]
  · by_cases hc : (c : ℕ) < k
    · rw [eB_inl_pos r m k hc, eB_inr]
      simp [BbarB, GyG, BTg, Frame.hybRow, Frame.hybCol]
    · rw [eB_inl_neg r m k hc, eB_inr]
      have hz := Tsym_ge_k p k nr v (show k ≤ (c : ℕ) by omega)
        (show k ≤ r + 2 * (i' : ℕ) + 1 by omega) (by have := c.2; omega)
      simp [BbarB, BTg, Frame.hybRow, Frame.hybCol, hz, rfC_zero]
  · by_cases hc : (c' : ℕ) < k
    · rw [eB_inr, eB_inl_pos r m k hc]
      simp [BbarB, GxG, BTg, Frame.hybRow, Frame.hybCol]
    · rw [eB_inr, eB_inl_neg r m k hc]
      have hz := Tsym_ge_k p k nr v (show k ≤ r + 2 * (i : ℕ) by omega)
        (show k ≤ (c' : ℕ) by omega) (by have := c'.2; omega)
      simp [BbarB, BTg, Frame.hybRow, Frame.hybCol, hz, rfC_zero]
  · rw [eB_inr, eB_inr]
    have hz := Tsym_ge_k p k nr v (show k ≤ r + 2 * (i : ℕ) by omega)
      (show k ≤ r + 2 * (i' : ℕ) + 1 by omega) (by omega)
    simp [BbarB, BTg, Frame.hybRow, Frame.hybCol, hz, rfC_zero]

end Mat

section Hred

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ}

lemma LP2Hyp.lift_offdiag (H : LP2Hyp Fr p q o r m k j) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (uPot p r k A + uPot p r k B)) * C (Fr.Mn A B) ∧
      phiP p g = rfC p (Tsym p k (red p Fr.norm) (vk p q j) A B) := by
  rcases lt_or_gt_of_ne hAB with h | h
  · have := H.good_Tg h hB
    have e : Tsym p k (red p Fr.norm) (vk p q j) A B = Tg p k (red p Fr.norm) (vk p q j) A B := by
      unfold Tsym; rw [if_pos h]
    rw [e]; exact lift_good p this
  · have := H.good_Tg h hA
    have e : Tsym p k (red p Fr.norm) (vk p q j) A B = Tg p k (red p Fr.norm) (vk p q j) B A := by
      unfold Tsym; rw [if_neg (by omega), if_pos h]
    rw [e, add_comm (uPot p r k A), Mn_symm]; exact lift_good p this

/-- **The entries of `Full(X)` reduce to the table `BTg`.** -/
theorem LP2Hyp.hred (H : LP2Hyp Fr p q o r m k j) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (uPot p r k (Frame.hybRow r m a) + uPot p r k (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧
      phiP p g = BTg p r m k (red p Fr.norm) (vk p q j) a b := by
  have hA := hybRow_lt (r := r) (m := m) a
  have hB := hybCol_lt (r := r) (m := m) b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hcr := c.2
      have hgood := H.good_Td (A := (c : ℕ)) hcr
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (uPot p r k c + uPot p r k c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ = Td p k (red p Fr.norm) (vk p q j) c := hgood.2
        rw [e1]
        have e2 : Tsym p k (red p Fr.norm) (vk p q j) c c = Td p k (red p Fr.norm) (vk p q j) c := by
          unfold Tsym; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
        have e3 : uPot p r k (c : ℕ) = 0 ↔ (c : ℕ) < k := by
          by_cases hck : (c : ℕ) < k
          · have h' : ¬ k ≤ (c : ℕ) := by omega
            simp [uPot, hcr, h', hck]
          · have h' : k ≤ (c : ℕ) := by omega
            simp [uPot, hcr, h', hck]
        rw [add_comm]
        simp [BTg, Frame.hybRow, Frame.hybCol, e2, e3]
    · have hne : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
      obtain ⟨g, h1, h2⟩ := H.lift_offdiag hne (by have := c.2; have := H.hrp; omega)
        (by have := c'.2; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BTg, hcc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag (A := c) (B := r + 2 * (i' : ℕ) + 1)
      (by have := c.2; omega) (by have := c.2; omega) hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTg, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag (A := r + 2 * (i : ℕ)) (B := c')
      (by have := c'.2; omega) hA (by have := c'.2; omega)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTg, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag (A := r + 2 * (i : ℕ)) (B := r + 2 * (i' : ℕ) + 1)
      (by omega) hA hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTg, Frame.hybRow, Frame.hybCol]

end Hred

end CatalanCore.Uniform.Content.Smith
