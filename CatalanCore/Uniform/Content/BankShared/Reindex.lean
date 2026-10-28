import CatalanCore.Uniform.Content.Shape.Alt
set_option Elab.async false

/-! # Shared contract 1 (lane H17): the family member is a common minor

For every block geometry `G` which has the standard hybrid shape at the scale `r`
(`HybShape G r`, true for `altGeom c hc` at every even `r`), the member `(r, S)` of
`G.family Fr depth` is the polynomial `commonMinorPoly Fr r m s`, where `m = (G.geometry r).k =
G.borderSize r` and `s : Finset (Fin r)` is the retained set `S` read in `Fin r`.  The relabelling
`S ≃ s` is explicit.  No admissibility hypothesis occurs; `depth` plays no role. -/

namespace CatalanCore.Uniform.Content.BankShared
open Polynomial Finset CatalanCore CatalanCore.Rect CatalanCore.Uniform
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape

variable {G : BlockGeom} {r : ℕ}

theorem hybShape_lt_scale (hs : HybShape G r) (x : (G.geometry r).C) : x.1 < r := by
  have h : x.1 ∈ Finset.range r := by rw [← hs.C_eq]; exact x.2
  exact Finset.mem_range.mp h

/-- The retained set, read in `Fin r`. -/
def retainedFin (hs : HybShape G r) (S : Finset (G.geometry r).C) : Finset (Fin r) :=
  S.map ⟨fun a => ⟨a.1, hybShape_lt_scale hs a⟩, fun a b h => Subtype.ext (by simpa using h)⟩

theorem mem_retainedFin (hs : HybShape G r) (S : Finset (G.geometry r).C) (c : Fin r) :
    c ∈ retainedFin hs S ↔ ∃ a ∈ S, (a : ℕ) = c.val := by
  unfold retainedFin
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, Fin.ext h⟩

/-- The explicit retained-index equivalence. -/
noncomputable def retainedEquiv (hs : HybShape G r) (S : Finset (G.geometry r).C) :
    retainedFin hs S ≃ S where
  toFun c := ⟨((mem_retainedFin hs S c.1).1 c.2).choose,
    ((mem_retainedFin hs S c.1).1 c.2).choose_spec.1⟩
  invFun a := ⟨⟨a.1.1, hybShape_lt_scale hs a.1⟩, (mem_retainedFin hs S _).2 ⟨a.1, a.2, rfl⟩⟩
  left_inv c := Subtype.ext (Fin.ext (((mem_retainedFin hs S c.1).1 c.2).choose_spec.2))
  right_inv a := Subtype.ext (Subtype.ext
    (((mem_retainedFin hs S ⟨a.1.1, hybShape_lt_scale hs a.1⟩).1
      ((mem_retainedFin hs S _).2 ⟨a.1, a.2, rfl⟩)).choose_spec.2))

theorem retainedEquiv_val (hs : HybShape G r) (S : Finset (G.geometry r).C)
    (c : retainedFin hs S) : (((retainedEquiv hs S c).1 : (G.geometry r).C) : ℕ) = c.1.val :=
  ((mem_retainedFin hs S c.1).1 c.2).choose_spec.2

theorem card_retainedFin (hs : HybShape G r) (S : Finset (G.geometry r).C) :
    (retainedFin hs S).card = S.card := Finset.card_map _

theorem geometry_k_eq_borderSize (G : BlockGeom) (r : ℕ) :
    (G.geometry r).k = G.borderSize r := by
  show (G.trim.keep (G.row.nodes r) (G.borderSize r)).card = _
  rw [G.trim.card]
  exact Nat.min_eq_left (min_le_left _ _)

/-- **Polynomial identity.**  The `FullN` determinant on the retained core and the unchanged
borders is the common-minor polynomial. -/
theorem alt_member_commonMinor_det (Fr : Frame) (hs : HybShape G r)
    (S : Finset (G.geometry r).C) :
    (FullN Fr (fun a : S => ((a.1 : (G.geometry r).C) : ℕ))
        (G.geometry r).xs (G.geometry r).ys (X : ℚ[X])).det =
      commonMinorPoly Fr r (G.geometry r).k (retainedFin hs S) := by
  classical
  have hdet := Rect.det_fullN_reindex Fr (R := ℚ[X])
    (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs (G.geometry r).ys
    (fun a : retainedFin hs S => (a.1 : Fin r).val)
    (fun i : Fin (G.geometry r).k => r + 2 * i.val)
    (fun i : Fin (G.geometry r).k => r + 2 * i.val + 1)
    (retainedEquiv hs S) (Equiv.refl _)
    (fun a => retainedEquiv_val hs S a) (fun i => hs.xs_eq i) (fun i => hs.ys_eq i) (X : ℚ[X])
  exact hdet.symm

/-- **Shared contract 1 (`alt_member_commonMinor`).**  The member `(r, S)` of the block family is
the common-minor polynomial of the retained set, at any scale where the geometry has the hybrid
shape (every even `r` for `altGeom`); no admissibility hypothesis. -/
theorem alt_member_commonMinor (Fr : Frame) (depth : ℕ) (hs : HybShape G r)
    (S : Finset (G.geometry r).C) :
    (G.family Fr depth).Q ⟨r, S⟩ =
      commonMinorPoly Fr r (G.geometry r).k (retainedFin hs S) :=
  alt_member_commonMinor_det Fr hs S

/-- The same with the border size `G.borderSize r`. -/
theorem alt_member_commonMinor_borderSize (Fr : Frame) (depth : ℕ) (hs : HybShape G r)
    (S : Finset (G.geometry r).C) :
    (G.family Fr depth).Q ⟨r, S⟩ =
      commonMinorPoly Fr r (G.borderSize r) (retainedFin hs S) := by
  rw [← geometry_k_eq_borderSize]; exact alt_member_commonMinor Fr depth hs S

/-- The alternating geometry at an even scale, for every slope `c`. -/
theorem altGeom_member_commonMinor (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ)
    (hr : r % 2 = 0) (S : Finset ((altGeom c hc).geometry r).C) :
    ((altGeom c hc).family Fr depth).Q ⟨r, S⟩ =
      commonMinorPoly Fr r ((altGeom c hc).borderSize r) (retainedFin (altGeom_hybShape c hc hr) S) :=
  alt_member_commonMinor_borderSize Fr depth (altGeom_hybShape c hc hr) S

end CatalanCore.Uniform.Content.BankShared
