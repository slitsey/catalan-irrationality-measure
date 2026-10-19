module

public import CatalanCore.Arith.Hybrid.DefC5Mat

@[expose] public section

/-!
# Theorem C5: the entries of `Full(X)` reduce to `BTc` (`hred_C`)
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Hred

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m k : ℕ}

lemma lift_offdiag5 {o : ℕ} (hL : LamData Fr o) (S : CSetup o p r m k) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wC p r k A + wC p r k B)) * C (Fr.Mn A B) ∧
      phiP p g = rfC p (TcF p r k A B) :=
  lift_good p (good_TcF S hL hAB hA hB)

/-- **The entries of `Full(X)` reduce to the table `BTc`.** -/
theorem hred_C {o : ℕ} (hL : LamData Fr o) (S : CSetup o p r m k) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wC p r k (Frame.hybRow r m a) + wC p r k (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧ phiP p g = BTc p r k m a b := by
  have hA := hybRow_lt (r := r) (m := m) a
  have hB := hybCol_lt (r := r) (m := m) b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hcr := c.2
      have hgood := good_TcD S hL (A := (c : ℕ)) hcr
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (wC p r k c + wC p r k c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ = TcF p r k c c := hgood.2
        rw [e1]
        have e3 : wC p r k (c : ℕ) = 0 ↔ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) := by
          by_cases h : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
          · rw [wC_U S h.1 h.2]; exact ⟨fun _ => h, fun _ => rfl⟩
          · rw [wC_P S c.2 h]; exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' h⟩
        have e4 : wC p r k c + wC p r k c = 0 ↔ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) := by
          rw [← e3]; omega
        rw [add_comm]
        by_cases hq : r - p ≤ (c : ℕ) ∧ (c : ℕ) < k
        · have h0 : wC p r k c + wC p r k c = 0 := e4.2 hq
          have hq1 : r ≤ (c : ℕ) + p := by omega
          simp [BTc, Frame.hybRow, Frame.hybCol, h0, hq1, hq.2]
        · have h0 : ¬ (wC p r k c + wC p r k c = 0) := fun h => hq (e4.1 h)
          have hq1 : ¬ (r ≤ (c : ℕ) + p ∧ (c : ℕ) < k) := fun ⟨h1, h2⟩ => hq ⟨by omega, h2⟩
          have h0' : ¬ (wC p r k c = 0) := fun h => h0 (by omega)
          simp [BTc, Frame.hybRow, Frame.hybCol, h0', hq1]
    · have hne : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
      obtain ⟨g, h1, h2⟩ := lift_offdiag5 hL S hne (by have := c.2; omega) (by have := c'.2; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BTc, hcc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiag5 hL S (A := c) (B := r + 2 * (i' : ℕ) + 1)
      (by have := c.2; omega) (by have := c.2; omega) hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiag5 hL S (A := r + 2 * (i : ℕ)) (B := c')
      (by have := c'.2; omega) hA (by have := c'.2; omega)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiag5 hL S (A := r + 2 * (i : ℕ)) (B := r + 2 * (i' : ℕ) + 1)
      (by omega) hA hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BTc, Frame.hybRow, Frame.hybCol]

end Hred

end CatalanCore.Arith.Hybrid
