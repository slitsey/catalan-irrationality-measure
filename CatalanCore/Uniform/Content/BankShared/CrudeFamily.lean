module

public import CatalanCore.Uniform.Content.BankShared.CrudeDet
public import CatalanCore.Uniform.Content.BankShared.ExceptionSmall

@[expose] public section
set_option Elab.async false

/-! # `p^(Ecrude)`-clearing of every member (canonical extraction of B4b proofs)

For a node family `G` whose nodes at scale `r` are `≤ 14 r` and whose matrix size is `≤ 2 r`, every
coefficient of `G.polynomial Fr i` is `p ^ Ecrude (cFr Fr) r p`-integral, for every prime `p`
(no exceptional-prime assumption, no cancellation).  This is the clearing statement behind
`BankShared.exc_of_Ecrude`. -/

namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Polynomial Finset
  CatalanCore.Uniform CatalanCore.Uniform.Content.BankShared

theorem polynomial_gle_Ecrude (Fr : Frame) (G : NodeFamily) (i : G.Index)
    (hN : ∀ a ∈ (G i.1).C ∪ (G i.1).X' ∪ (G i.1).Y', a ≤ 14 * i.1)
    (hcard : i.2.card + (G i.1).k ≤ 2 * i.1) (p : ℕ) [Fact p.Prime] :
    GLE p (Ecrude (cFr Fr) i.1 p) (G.polynomial Fr i) := by
  unfold NodeFamily.polynomial
  have hsz : Fintype.card (i.2 ⊕ Fin (G i.1).k) = i.2.card + (G i.1).k := by
    simp [Fintype.card_sum, Fintype.card_coe]
  rcases Nat.eq_zero_or_pos i.1 with h0 | hr
  · have hz : Fintype.card (i.2 ⊕ Fin (G i.1).k) = 0 := by omega
    have hE : IsEmpty (i.2 ⊕ Fin (G i.1).k) := Fintype.card_eq_zero_iff.1 hz
    rw [Matrix.det_isEmpty]
    exact (GLE.one (p := p)).mono (Nat.zero_le _)
  · have hNpos : 0 < 14 * i.1 := by omega
    have h := fullN_det_gle (p := p) Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
      (G i.1).xs (G i.1).ys hNpos
      (fun a => hN _ (by
        have := a.1.2
        simp [this]))
      (fun j => hN _ (by
        have := Finset.orderEmbOfFin_mem (G i.1).X' rfl j
        simp [Rect.Geometry.xs, this]))
      (fun j => hN _ (by
        have := Finset.orderEmbOfFin_mem (G i.1).Y' (G i.1).card_eq.symm j
        simp [Rect.Geometry.ys, this]))
    refine h.mono ?_
    rw [hsz]
    unfold Ecrude
    have hl : Nat.log p (14 * i.1) ≤ Nat.log p (14 * i.1) := le_rfl
    calc (i.2.card + (G i.1).k) * (2 * Nat.log p (14 * i.1) + cFr Fr)
        ≤ (2 * i.1) * (3 * Nat.log p (14 * i.1) + cFr Fr) :=
          Nat.mul_le_mul hcard (by omega)
      _ = 2 * i.1 * (3 * Nat.log p (14 * i.1) + cFr Fr) := rfl

end CatalanCore.Uniform.Content.BankShared
