module

public import CatalanCore.Uniform.Content.UFMember.Wit
public import CatalanCore.Uniform.Content.Member.LPD

@[expose] public section

/-!
# UF member package, step 1d: deletion members of the hybrid matrix

`ufMember_gle_of_full`: a deletion member `FullN Fr (common|S) xs ys` (common nodes outside `S`
deleted, borders kept) inherits the FULL matrix's Theorem-UF price, with no debit.  The member's
own leading data (H6 `ufMember_gle`) is not needed; the full matrix's `LeadingData` suffices.
`rankMember_gle_of_full` is the same for the plain UC4 price `2h - |s| - G`.
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFMember

variable {p : ℕ} [Fact p.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- **UC4 price for a deletion member from the full matrix's leading data** (debit 0). -/
theorem rankMember_gle_of_full (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    (D : LeadingData p (FullN Fr common xs ys (X : ℚ[X]))) (G : ℕ)
    (hG : D.nextRed.rank + G ≤ D.s.card) :
    GLE p (2 * Fintype.card (ι ⊕ κ) - D.s.card - G)
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  rw [fullN_member_eq_submatrix]
  exact D.gle_det_submatrix G hG _ _ (memberEmbedding S).injective (memberEmbedding S).injective

/-- **Theorem UF for a deletion member from the full matrix's leading data** (debit 0). -/
theorem ufMember_gle_of_full (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    (D : LeadingData p (FullN Fr common xs ys (X : ℚ[X]))) (R0 : ℕ)
    (hR : R0 + D.s.card = Fintype.card (ι ⊕ κ)) (v : ZMod p → ZMod p)
    (I Kill : Finset (ZMod p)) (mR mC ρ σ : D.s → ZMod p)
    (hI : ∀ c ∈ I, v c = 0) (hKill : ∀ c ∈ Kill, v c = 0)
    (hnext : ∀ i j, D.nextRed i j =
      rfH p (mR i * mC j * ∑ c, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹))) :
    GLE p (Fintype.card (ι ⊕ κ) + R0 - (D.s.card - (p - (I ∪ Kill).card)))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  rw [fullN_member_eq_submatrix]
  exact D.gle_det_uf_submatrix R0 hR v I Kill mR mC ρ σ hI hKill hnext _ _
    (memberEmbedding S).injective (memberEmbedding S).injective

end CatalanCore.Uniform.Content.UFMember
