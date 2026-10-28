module

public import CatalanCore.Uniform.Content.Member.BlockContent
public import CatalanCore.Uniform.Content.Member.LPD

@[expose] public section

/-!
# Combining debit layers into `HasContent` (lane H5)

A *debit layer* is a per-prime price of the deletion members of the form
`base r p + debit · k`, where `k` is the number of deleted common nodes:

* tropical layer (`DebitLayer.trop`): `debit = 0` (hereditary, `member_gle_trop`);
* hybrid rank layer and M3D: `debit = 0` (built from `member_gle_rank` resp. H4's `M3D_debit`);
* Lemma LPD layer (`DebitLayer.lpd`): `debit = 1`, from the rank bound of the full reduction (H3);
* Theorem SD Smith layer: `debit = 1`; a bare hypothesis until H2 (UF) is discharged.

The content of the family is the per-prime MINIMUM of the layers, covered by the exact
piecewise-linear class templates (`hasContent_of_debitLayers`).  The debit is absorbed into the
slack because `k ≤ depth` for every admissible member.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform

namespace CatalanCore.Uniform.Content.Member

/-- Number of deleted common nodes of a member. -/
def delCount (G : BlockGeom) (i : NodeFamily.Index G.geometry) : ℕ :=
  (G.geometry i.1).C.card - i.2.card

lemma delCount_le (G : BlockGeom) (Fr : Frame) (depth : ℕ) (i : NodeFamily.Index G.geometry)
    (hi : (G.family Fr depth).Adm i) : delCount G i ≤ depth := hi

/-- A per-prime price `base r p + debit · k` of the deletion members, valid on a window of
`(r, p)`. -/
structure DebitLayer (G : BlockGeom) (Fr : Frame) (depth : ℕ) where
  base : ℕ → ℕ → ℕ
  debit : ℕ
  valid : ℕ → ℕ → Prop
  gle : ∀ (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i →
    ∀ (p : ℕ) [Fact p.Prime], valid i.1 p →
      GLE p (base i.1 p + debit * delCount G i) ((G.family Fr depth).Q i)

namespace DebitLayer

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ}

/-- The effective price at the maximal deletion count. -/
def eff (L : DebitLayer G Fr depth) (r p : ℕ) : ℕ := L.base r p + L.debit * depth

/-- **Tropical layer (debit 0).**  Any entry table valid for the full hybrid matrix at scale
`r` prices all common deletions. -/
noncomputable def trop (valid : ℕ → ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hW : ∀ r p, valid r p → ∀ [Fact p.Prime], ∀ a b,
      GLE p (W r p a b) (FullN Fr (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
        (G.geometry r).ys (X : ℚ[X]) a b)) : DebitLayer G Fr depth where
  base := fun r p => tropVal (W r p)
  debit := 0
  valid := valid
  gle := by
    intro i _ p _ hv
    rw [zero_mul, add_zero]
    exact member_gle_trop Fr (fun a : (G.geometry i.1).C => (a : ℕ)) (G.geometry i.1).xs
      (G.geometry i.1).ys i.2 (W i.1 p) (hW i.1 p hv)

/-- Data of Lemma LPD for the full hybrid matrix at scale `r` and prime `p` (lane H3): feasible
potentials, the integral lift, and the rank bound of the reduction. -/
structure LPDatum (Fr : Frame) (G : BlockGeom) (r : ℕ) (p : ℕ) [Fact p.Prime] where
  u : (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ
  v : (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ
  Bl : Matrix ((G.geometry r).C ⊕ Fin (G.geometry r).k)
    ((G.geometry r).C ⊕ Fin (G.geometry r).k) (LocRing p)[X]
  c : ℕ
  hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u i + v j)) *
    FullN Fr (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs (G.geometry r).ys
      (X : ℚ[X]) i j
  hrk : (Bl.map (phiP p)).rank + c ≤ Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k)

/-- **Lemma LPD layer (debit 1)** over the H3 data; `base` is the full-member price
`Σ (u + v) - c` of the datum. -/
def lpd (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (D : ∀ r p : ℕ, [Fact p.Prime] → valid r p → LPDatum Fr G r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p,
      base r p = ∑ a, (D r p h).u a + ∑ a, (D r p h).v a - (D r p h).c) :
    DebitLayer G Fr depth where
  base := base
  debit := 1
  valid := valid
  gle := by
    intro i _ p hp hv
    have h := lpd_member_debit Fr (fun a : (G.geometry i.1).C => (a : ℕ)) (G.geometry i.1).xs
      (G.geometry i.1).ys i.2 (D i.1 p hv).u (D i.1 p hv).v (D i.1 p hv).Bl
      (D i.1 p hv).hB (D i.1 p hv).c (D i.1 p hv).hrk
    have hc : Fintype.card (G.geometry i.1).C = (G.geometry i.1).C.card := Fintype.card_coe _
    rw [hc] at h
    rw [hbase i.1 p hv, one_mul]
    exact h

/-- **Smith layer (debit 1), Theorem SD interface.**  `base r p` is the full-member price
`max(0, 2|C| + m - max(G0, σ, 2σ - s))`; the hypothesis is the member's GLE bound with the debit `k`
(lane H2/UF, pending). -/
def smith (base : ℕ → ℕ → ℕ) (valid : ℕ → ℕ → Prop)
    (h : ∀ (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], valid i.1 p →
        GLE p (base i.1 p + 1 * delCount G i) ((G.family Fr depth).Q i)) :
    DebitLayer G Fr depth where
  base := base
  debit := 1
  valid := valid
  gle := h

end DebitLayer

end CatalanCore.Uniform.Content.Member
