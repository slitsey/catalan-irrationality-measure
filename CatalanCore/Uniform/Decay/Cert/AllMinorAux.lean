module

public import CatalanCore.Uniform.Decay.Cert.FullTent
public import CatalanCore.Uniform.Decay.Nodes.EnumGeom

@[expose] public section

/-!
# Reindexing the retained pencil by the canonical node enumeration (lane D, package D5)

For `S ⊆ C_r` (retained common nodes) the index set `S ⊕ Fin m` of the retained pencil embeds into
the canonical enumeration `G.nodeEnum r` (common nodes first).  `sIdx` is the embedding; its row
and column images are the physical nodes of `FullN`.  `det_fullN_eq_tent_fin` identifies
`det FullN` with the `Tent` determinant of the node lists `nR ∘ s`, `nQ ∘ s` (`s : Fin k → Fin N`),
and `sIdx_keep` records that all border nodes are kept.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset Matrix CatalanCore CatalanCore.Uniform Rect

variable (G : BlockGeom) (r : ℕ)

/-- Embedding of the retained pencil index set into the enumeration. -/
noncomputable def sIdx (S : Finset (G.geometry r).C) :
    (S ⊕ Fin (G.geometry r).k) → Fin ((G.geometry r).C.card + (G.geometry r).X'.card) :=
  Sum.elim (fun a => Fin.castAdd _
      (((G.geometry r).C.orderIsoOfFin rfl).symm ⟨a.1.1, a.1.2⟩))
    (fun j => Fin.natAdd _ j)

variable {G r}

theorem orderEmb_symm (C : Finset ℕ) (x : C) :
    (C.orderEmbOfFin rfl) ((C.orderIsoOfFin rfl).symm x) = x.1 := by
  have h := (C.orderIsoOfFin rfl).apply_symm_apply x
  have h2 := congrArg Subtype.val h
  rw [Finset.coe_orderIsoOfFin_apply] at h2
  exact h2

theorem nR_sIdx_inl {S : Finset (G.geometry r).C} (a : S) :
    (G.nodeEnum r).nR (sIdx G r S (Sum.inl a)) = a.1.1 := by
  simp only [sIdx, Sum.elim_inl, BlockGeom.nodeEnum, enumApp, Fin.append_left]
  exact orderEmb_symm _ _

theorem nQ_sIdx_inl {S : Finset (G.geometry r).C} (a : S) :
    (G.nodeEnum r).nQ (sIdx G r S (Sum.inl a)) = a.1.1 := by
  simp only [sIdx, Sum.elim_inl, BlockGeom.nodeEnum, enumApp, Fin.append_left]
  exact orderEmb_symm _ _

theorem nR_sIdx_inr {S : Finset (G.geometry r).C} (j : Fin (G.geometry r).k) :
    (G.nodeEnum r).nR (sIdx G r S (Sum.inr j)) = (G.geometry r).xs j := by
  simp only [sIdx, Sum.elim_inr, BlockGeom.nodeEnum, enumApp]
  exact Fin.append_right _ _ j

theorem nQ_sIdx_inr {S : Finset (G.geometry r).C} (j : Fin (G.geometry r).k) :
    (G.nodeEnum r).nQ (sIdx G r S (Sum.inr j)) = (G.geometry r).ys j := by
  simp only [sIdx, Sum.elim_inr, BlockGeom.nodeEnum, enumApp]
  exact Fin.append_right _ _ j

end CatalanCore.Uniform.Decay.Cert
