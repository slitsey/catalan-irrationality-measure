module

public import CatalanCore.Uniform.Content.UFMember.Wit3
public import CatalanCore.Uniform.Content.UFMember.Wrap
public import CatalanCore.Uniform.Content.Member.Combine

@[expose] public section

/-!
# UF member package, step 5 (assembly): Smith / UF debit layers

* `smithLayer` (debit 1): from a scaled-gauge `ThreeLevelWit` of the FULL hybrid matrix at each
  valid `(r, p)` (the level-2 Smith certificate of `smith-deletion/THEOREM.md`), every admissible
  deletion member is priced at `base r p + 1 · k`.  `base` only needs to dominate the witness
  price.  This is the layer `DebitLayer.smith` of H5 with its bare hypothesis DISCHARGED from
  full-matrix data.
* `leadLayer` (debit 0): from the full matrix's `LeadingData` with a corank bound (UC4, original
  gauge), e.g. the UF form `LeadingData.rank_le_of_uf`; every member at the full price.

Either layer can be passed as an `ext` layer to H6's `hasContent_twoTerm(_on)`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ}

/-- The full hybrid matrix at scale `r`. -/
noncomputable abbrev fullMat (G : BlockGeom) (Fr : Frame) (r : ℕ) :=
  FullN Fr (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs (G.geometry r).ys (X : ℚ[X])

/-- Smith-layer data at `(r, p)`: a scaled-gauge three-level witness of the full matrix. -/
structure SmithDatum (G : BlockGeom) (Fr : Frame) (r p : ℕ) [Fact p.Prime] where
  b : ℕ
  W : ThreeLevelWit p ((fullMat G Fr r).map (UFMember.scaleU p)) b

/-- **The Smith layer (debit 1), from full-matrix data.** -/
noncomputable def smithLayer (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (D : ∀ r p : ℕ, [Fact p.Prime] → valid r p → SmithDatum G Fr r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (D r p h).W.price ≤ base r p) :
    DebitLayer G Fr depth where
  base := base
  debit := 1
  valid := valid
  gle := by
    intro i _ p hp hv
    have h := ufMember3_gle_scaled Fr (fun a : (G.geometry i.1).C => (a : ℕ))
      (G.geometry i.1).xs (G.geometry i.1).ys i.2 (D i.1 p hv).W
    have hc : Fintype.card (G.geometry i.1).C = (G.geometry i.1).C.card := Fintype.card_coe _
    rw [hc] at h
    refine h.mono ?_
    rw [one_mul]
    have := hbase i.1 p hv
    unfold delCount
    omega

/-- Leading data of the full matrix with a certified corank bound (original gauge). -/
structure LeadDatum (G : BlockGeom) (Fr : Frame) (r p : ℕ) [Fact p.Prime] where
  D : LeadingData p (fullMat G Fr r)
  G0 : ℕ
  hG : D.nextRed.rank + G0 ≤ D.s.card

/-- **The two-level layer (debit 0), from full-matrix leading data.** -/
noncomputable def leadLayer (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (D : ∀ r p : ℕ, [Fact p.Prime] → valid r p → LeadDatum G Fr r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p,
      2 * Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) - (D r p h).D.s.card -
        (D r p h).G0 ≤ base r p) :
    DebitLayer G Fr depth where
  base := base
  debit := 0
  valid := valid
  gle := by
    intro i _ p hp hv
    have h := rankMember_gle_of_full Fr (fun a : (G.geometry i.1).C => (a : ℕ))
      (G.geometry i.1).xs (G.geometry i.1).ys i.2 (D i.1 p hv).D (D i.1 p hv).G0 (D i.1 p hv).hG
    refine h.mono ?_
    rw [zero_mul, add_zero]
    exact hbase i.1 p hv

end CatalanCore.Uniform.Content.UFMember
