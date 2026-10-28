module

public import CatalanCore.Uniform.Content.RankProducer.Member

@[expose] public section

/-!
# The certificate rank layer as a `DebitLayer` (lane H15)
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.RankProducer

open scoped Classical

/-- Node-set facts of a block geometry used by the member rank transfer. -/
theorem geometry_facts (Gm : Rect.Geometry) :
    Function.Injective (fun a : Gm.C => (a : ℕ)) ∧ (∀ i j, Gm.xs i ≠ (j : Gm.C)) ∧
      (∀ i j, Gm.ys i ≠ (j : Gm.C)) ∧ (∀ i j, Gm.xs i ≠ Gm.ys j) := by
  have hx : ∀ i, Gm.xs i ∈ Gm.X' := fun i =>
    Finset.orderEmbOfFin_mem Gm.X' rfl i
  have hy : ∀ i, Gm.ys i ∈ Gm.Y' := fun i =>
    Finset.orderEmbOfFin_mem Gm.Y' Gm.card_eq.symm i
  refine ⟨Subtype.val_injective, fun i j h => ?_, fun i j h => ?_, fun i j h => ?_⟩
  · exact Finset.disjoint_left.1 Gm.disjCX j.2 (h ▸ hx i)
  · exact Finset.disjoint_left.1 Gm.disjCY j.2 (h ▸ hy i)
  · exact Finset.disjoint_left.1 Gm.disjXY (hx i) (h ▸ hy j)

/-- **The certificate rank layer (debit `debit`).**  Given a supplier of `RankMember`s priced at
most `base r p + debit * k` for every admissible member and valid `(r, p)`. -/
noncomputable def DebitLayer.rank (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    (u q : Fin Fr.d → ℕ) (hu : ∀ j, Fr.μ j = u j / q j) (hq : ∀ j, 0 < q j)
    (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ) (debit : ℕ)
    (wit : ∀ i : NodeFamily.Index G.geometry, (G.family Fr depth).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], valid i.1 p →
        ∃ M : RankMember Fr u q (fun a : (G.geometry i.1).C => (a : ℕ)) (G.geometry i.1).xs
            (G.geometry i.1).ys i.2 p, M.price ≤ base i.1 p + debit * delCount G i) :
    DebitLayer G Fr depth where
  base := base
  debit := debit
  valid := valid
  gle := by
    intro i hi p _ hv
    obtain ⟨M, hM⟩ := wit i hi p hv
    obtain ⟨h1, h2, h3, h4⟩ := geometry_facts (G.geometry i.1)
    exact (RankMember.gle Fr u q hu hq _ _ _ h1 h2 h3 h4 i.2 p M).mono hM

end CatalanCore.Uniform.Content.RankProducer
