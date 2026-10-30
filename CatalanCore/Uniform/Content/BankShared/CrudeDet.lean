module

public import CatalanCore.Uniform.Content.BankShared.FrameEntry
public import CatalanCore.Rect.Full
public import CatalanCore.Uniform.Frame.Family

@[expose] public section
set_option Elab.async false

/-! # Crude clearing of the hybrid determinant (canonical extraction of B4b proofs)

`fullN_det_gle`: for nodes bounded by `N`, every coefficient of `det FullN` is
`p ^ (card * (2 ⌊log_p N⌋ + cFr Fr))`-integral (tropical bound with the constant weight table). -/

namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Polynomial Finset

section
variable {p : ℕ} [hp : Fact p.Prime] (Fr : Frame)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tropVal_const {ι : Type} [Fintype ι] [DecidableEq ι] (e : ℕ) :
    tropVal (fun _ _ : ι => e) = Fintype.card ι * e := by
  unfold tropVal
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Finset.sup_const Finset.univ_nonempty]

lemma C_mn_gle {N A B : ℕ} (hN : 0 < N) (hA : A ≤ N) (hB : B ≤ N) :
    GLE p (2 * Nat.log p N + cFr Fr) (C (Fr.Mn A B)) :=
  GLE.C_iff.2 (mn_mem (p := p) Fr hN hA hB)

theorem fullN_entry_gle (c : ι → ℕ) (xs ys : κ → ℕ) {N : ℕ} (hN : 0 < N)
    (hc : ∀ a, c a ≤ N) (hx : ∀ i, xs i ≤ N) (hy : ∀ i, ys i ≤ N) (u v : ι ⊕ κ) :
    GLE p (2 * Nat.log p N + cFr Fr) (Rect.FullN Fr c xs ys (X : ℚ[X]) u v) := by
  rw [Rect.blk_map_C]
  have hX : GLE p (2 * Nat.log p N + cFr Fr) (X : ℚ[X]) := GLE.X.mono (Nat.zero_le _)
  rcases u with a | i <;> rcases v with b | j
  · simp only [Rect.Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.map_apply,
      Matrix.smul_apply, Matrix.one_apply, Rect.blkA, Matrix.of_apply, smul_eq_mul]
    by_cases h : a = b
    · simp only [h, if_true, mul_one]
      exact (C_mn_gle Fr hN (hc b) (hc b)).add hX
    · simp only [h, if_false, mul_zero, add_zero]
      exact C_mn_gle Fr hN (hc a) (hc b)
  · simp only [Rect.Blk, Matrix.fromBlocks_apply₁₂, Matrix.map_apply, Rect.blkB, Matrix.of_apply]
    exact C_mn_gle Fr hN (hc a) (hy j)
  · simp only [Rect.Blk, Matrix.fromBlocks_apply₂₁, Matrix.map_apply, Rect.blkC, Matrix.of_apply]
    exact C_mn_gle Fr hN (hx i) (hc b)
  · simp only [Rect.Blk, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Rect.RXY, Rect.blkD,
      Matrix.of_apply]
    exact C_mn_gle Fr hN (hx i) (hy j)

theorem fullN_det_gle (c : ι → ℕ) (xs ys : κ → ℕ) {N : ℕ} (hN : 0 < N)
    (hc : ∀ a, c a ≤ N) (hx : ∀ i, xs i ≤ N) (hy : ∀ i, ys i ≤ N) :
    GLE p (Fintype.card (ι ⊕ κ) * (2 * Nat.log p N + cFr Fr))
      (Rect.FullN Fr c xs ys (X : ℚ[X])).det := by
  have h := det_gle (p := p) (Rect.FullN Fr c xs ys (X : ℚ[X]))
    (fun _ _ => 2 * Nat.log p N + cFr Fr) (fullN_entry_gle Fr c xs ys hN hc hx hy)
  rwa [tropVal_const] at h

end

end CatalanCore.Uniform.Content.BankShared
