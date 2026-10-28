module

public import CatalanCore.Uniform.Content.Smith.LP1Table

@[expose] public section

/-!
# LP1 for a general two-term frame: the symmetric table, the block form of `B̄`, and `hred`

Port of the Theorem C5 reduction (`DefC5Tab`, `DefC5Mat`, `DefC5Red`) to the frame-generic table
`TCgenG`, `TCDgenG` (constants `nr`, `v`, `v₂`).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

section Tab

variable (p : ℕ) [Fact p.Prime] (r k : ℕ) (nr v v2 : ZMod p)

/-- The symmetric residue table on labels. -/
noncomputable def TcG (A B : ℕ) : ZMod p :=
  if A < B then TCgenG p k nr v v2 (wC p r k A + wC p r k B) A B
  else if B < A then TCgenG p k nr v v2 (wC p r k B + wC p r k A) B A
  else TCDgenG p k nr v (wC p r k A + wC p r k A) A

variable {p r k nr v v2}

lemma TcG_symm (A B : ℕ) : TcG p r k nr v v2 A B = TcG p r k nr v v2 B A := by
  unfold TcG
  split_ifs <;> first | omega | rfl | (obtain rfl : A = B := by omega
                                       rfl)

lemma TcG_lt {A B : ℕ} (h : A < B) :
    TcG p r k nr v v2 A B = TCgenG p k nr v v2 (wC p r k A + wC p r k B) A B := by
  unfold TcG; rw [if_pos h]

lemma TcG_diag (A : ℕ) :
    TcG p r k nr v v2 A A = TCDgenG p k nr v (wC p r k A + wC p r k A) A := by
  unfold TcG; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

end Tab

section Wt

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ}

lemma wC_U' (H : LP1Hyp Fr p q o r m k j) {A : ℕ} (h1 : r - p ≤ A) (h2 : A < k) :
    wC p r k A = 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; unfold wC; split_ifs <;> omega

lemma wC_P' {A : ℕ} (hA : A < r) (h : ¬ (r - p ≤ A ∧ A < k)) : wC p r k A = 1 := by
  unfold wC; split_ifs <;> omega

lemma wC_low' {A : ℕ} (h1 : r ≤ A) (h2 : A < p + k) : wC p r k A = 2 := by
  unfold wC; split_ifs <;> omega

lemma wC_high' (H : LP1Hyp Fr p q o r m k j) {A : ℕ} (h1 : p + k ≤ A) : wC p r k A = 1 := by
  have := H.hUk; unfold wC; split_ifs <;> omega

lemma wC_le' {A : ℕ} : wC p r k A ≤ 2 := by unfold wC; split_ifs <;> omega

theorem LP1Hyp.good_TcG (H : LP1Hyp Fr p q o r m k j) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (wC p r k A + wC p r k B) * Fr.Mn A B)
      (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) A B) := by
  have C := H.cfg
  have hkp := C.sg.hkp
  have hrp := H.hrp
  have hUk := H.hUk
  have hN2 := C.sg.hN2
  rcases lt_or_gt_of_ne hAB with h | h
  · rw [TcG_lt h]
    refine C.good_TCgen h hB ?_ ?_
    · intro hw; unfold wC at hw; split_ifs at hw <;> omega
    · intro hw hd; unfold wC at hw; split_ifs at hw <;> omega
  · rw [TcG_symm, TcG_lt h, Mn_symm, add_comm]
    refine C.good_TCgen h hA ?_ ?_
    · intro hw; unfold wC at hw; split_ifs at hw <;> omega
    · intro hw hd; unfold wC at hw; split_ifs at hw <;> omega

theorem LP1Hyp.good_TcD (H : LP1Hyp Fr p q o r m k j) {A : ℕ} (hA : A < r) :
    Good p ((p : ℚ) ^ (wC p r k A + wC p r k A) * Fr.Mn A A)
      (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) A A) := by
  have C := H.cfg
  have hkp := C.sg.hkp
  have hrp := H.hrp
  have hUk := H.hUk
  rw [TcG_diag]
  refine C.good_TCDgen (by omega) (by omega) ?_ ?_
  · unfold wC; split_ifs <;> omega
  · intro hw; unfold wC at hw; split_ifs at hw <;> omega

end Wt

section Mats

variable (p : ℕ) [Fact p.Prime] (r k m : ℕ) (nr v v2 : ZMod p)

noncomputable def T5G : Matrix (BU p r k ⊕ Fin m) (BU p r k ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TcG p r k nr v v2 (rowlab p r k m a) (collab p r k m b)) +
    (match a, b with
      | Sum.inl u, Sum.inl w => if u = w then rfX p else 0
      | _, _ => 0)

noncomputable def Up5G : Matrix (BU p r k ⊕ Fin m) (BP p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun a c => rfC p (TcG p r k nr v v2 (rowlab p r k m a) (c.1 : ℕ))

noncomputable def Wp5G : Matrix (BP p r k) (BU p r k ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun c b => rfC p (TcG p r k nr v v2 (c.1 : ℕ) (collab p r k m b))

noncomputable def Mp5G : Matrix (BP p r k) (BP p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun c d => rfC p (TcG p r k nr v v2 (c.1 : ℕ) (d.1 : ℕ))

/-- The reduction matrix on `Fin r ⊕ Fin m`. -/
noncomputable def BTcG : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TcG p r k nr v v2 (Frame.hybRow r m a) (Frame.hybCol r m b)) +
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' ∧ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) then rfX p else 0
      | _, _ => 0)

lemma BTcG_eq (a b : Fin r ⊕ Fin m) :
    fromBlocks (T5G p r k m nr v v2) (Up5G p r k m nr v v2) (Wp5G p r k m nr v v2)
      (Mp5G p r k nr v v2) (eU p r k m a) (eU p r k m b) = BTcG p r k m nr v v2 a b := by
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hc : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k <;> by_cases hc' : r - p ≤ (c' : ℕ) ∧ (c' : ℕ) < k
    · rw [eU_inl_pos hc, eU_inl_pos hc']
      have hc1 : r ≤ (c : ℕ) + p := by omega
      simp [T5G, BTcG, rowlab, collab, Frame.hybRow, Frame.hybCol, Fin.ext_iff, Subtype.ext_iff,
        hc1, hc.2]
    · rw [eU_inl_pos hc, eU_inl_neg hc']
      have hne : c ≠ c' := fun h => hc' (h ▸ hc)
      simp [Up5G, BTcG, rowlab, Frame.hybRow, Frame.hybCol, hne]
    · rw [eU_inl_neg hc, eU_inl_pos hc']
      have hne : c ≠ c' := fun h => hc (h ▸ hc')
      simp [Wp5G, BTcG, collab, Frame.hybRow, Frame.hybCol, hne]
    · rw [eU_inl_neg hc, eU_inl_neg hc']
      simp [Mp5G, BTcG, Frame.hybRow, Frame.hybCol]
      intro _ h2 h3
      exact absurd ⟨by omega, h3⟩ hc
  · by_cases hc : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
    · rw [eU_inl_pos hc, eU_inr]
      simp [T5G, BTcG, rowlab, collab, Frame.hybRow, Frame.hybCol]
    · rw [eU_inl_neg hc, eU_inr]
      simp [Wp5G, BTcG, collab, Frame.hybRow, Frame.hybCol]
  · by_cases hc : r - p ≤ (c' : ℕ) ∧ (c' : ℕ) < k
    · rw [eU_inr, eU_inl_pos hc]
      simp [T5G, BTcG, rowlab, collab, Frame.hybRow, Frame.hybCol]
    · rw [eU_inr, eU_inl_neg hc]
      simp [Up5G, BTcG, rowlab, Frame.hybRow, Frame.hybCol]
  · rw [eU_inr, eU_inr]
    simp [T5G, BTcG, rowlab, collab, Frame.hybRow, Frame.hybCol]

end Mats

section Hred

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ}

lemma LP1Hyp.lift_offdiag5 (H : LP1Hyp Fr p q o r m k j) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wC p r k A + wC p r k B)) * C (Fr.Mn A B) ∧
      phiP p g = rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) A B) :=
  lift_good p (H.good_TcG hAB hA hB)

/-- **The entries of `Full(X)` reduce to the table `BTcG`.** -/
theorem LP1Hyp.hred (H : LP1Hyp Fr p q o r m k j) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wC p r k (Frame.hybRow r m a) + wC p r k (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧
      phiP p g = BTcG p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) a b := by
  have hA := hybRow_lt (r := r) (m := m) a
  have hB := hybCol_lt (r := r) (m := m) b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hcr := c.2
      have hgood := H.good_TcD (A := (c : ℕ)) hcr
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (wC p r k c + wC p r k c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ =
            TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c c := hgood.2
        rw [e1]
        have e3 : wC p r k (c : ℕ) = 0 ↔ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) := by
          by_cases h : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
          · rw [wC_U' H h.1 h.2]; exact ⟨fun _ => h, fun _ => rfl⟩
          · rw [wC_P' c.2 h]; exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' h⟩
        have e4 : wC p r k c + wC p r k c = 0 ↔ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) := by
          rw [← e3]; omega
        rw [add_comm]
        by_cases hq : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
        · have h0 : wC p r k c + wC p r k c = 0 := e4.2 hq
          have hq1 : r ≤ (c : ℕ) + p := by omega
          simp [BTcG, Frame.hybRow, Frame.hybCol, h0, hq1, hq.2]
        · have h0 : ¬ (wC p r k c + wC p r k c = 0) := fun h => hq (e4.1 h)
          have hq1 : ¬ (r ≤ (c : ℕ) + p ∧ (c : ℕ) < k) := fun ⟨h1, h2⟩ => hq ⟨by omega, h2⟩
          have h0' : ¬ (wC p r k c = 0) := fun h => h0 (by omega)
          simp [BTcG, Frame.hybRow, Frame.hybCol, h0', hq1]
    · have hne : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
      obtain ⟨g, h1, h2⟩ := H.lift_offdiag5 hne (by have := c.2; omega) (by have := c'.2; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BTcG, hcc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag5 (A := c) (B := r + 2 * (i' : ℕ) + 1)
      (by have := c.2; omega) (by have := c.2; omega) hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTcG, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag5 (A := r + 2 * (i : ℕ)) (B := c')
      (by have := c'.2; omega) hA (by have := c'.2; omega)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTcG, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := H.lift_offdiag5 (A := r + 2 * (i : ℕ)) (B := r + 2 * (i' : ℕ) + 1)
      (by omega) hA hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTcG, Frame.hybRow, Frame.hybCol]

end Hred

end CatalanCore.Uniform.Content.Smith
