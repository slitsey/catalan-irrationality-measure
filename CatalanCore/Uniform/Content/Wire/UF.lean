module

public import CatalanCore.Uniform.Content.Member.Combine
public import CatalanCore.Uniform.Content.Smith.Derived
public import CatalanCore.Uniform.Content.Smith.Weights

@[expose] public section

/-!
# UF as an OPTIONAL debit-0 layer on a deletion member (lane H6, tasks 2-3)

What is proved here.  For a deletion member `(r, S)` the member matrix is
`Φ_S = FullN Fr (fun a : S => a) xs ys X` (index `S ⊕ κ`).  If the member carries its own
`LeadingData` (H1: exact leading part, unit `L, P`, kill set `s`) whose next matrix is the weighted
Cauchy matrix of the derived frame (`hnext`), with the weights vanishing off a retained set, then
H2's `LeadingData.gle_det_uf` prices the member directly, with NO debit relative to the member's
own size (`ufMember_gle`).  `memberLayer` packages such a member bound as a layer; the
UF layer is therefore one more element of the layer list, and the whole machine runs without it
(`Wire.Output`), with a weaker but valid price.

What is NOT discharged, recorded in `evidence/claude/H6/NOTES.md`: the conditional data of UF
(S5-S7 weight identities in the Gauss DVR, the identification of the loads of the `J`-supported
kernels with the form `(m, m·h)`, the wedge-kill set, the affine arc counts) and the
Smith-length transfer (Lemma A1 / A2 / A3) that would produce the member's `LeadingData` from the
full matrix.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.Wire

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ}

/-- A layer given by a member bound (debit as a parameter) on a window. -/
def memberLayer (base : ℕ → ℕ → ℕ) (debit : ℕ) (valid : ℕ → ℕ → Prop)
    (h : ∀ (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], valid i.1 p →
        GLE p (base i.1 p + debit * delCount G i) ((G.family Fr depth).Q i)) :
    DebitLayer G Fr depth where
  base := base
  debit := debit
  valid := valid
  gle := h

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **UF for a deletion member**, from the member's own leading data (H2 `gle_det_uf`). -/
theorem ufMember_gle {p : ℕ} [Fact p.Prime] (Φ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (D : LeadingData p Φ) (R0 : ℕ) (hR : R0 + D.s.card = Fintype.card (ι ⊕ κ))
    (v : ZMod p → ZMod p) (I Kill : Finset (ZMod p))
    (mR mC ρ σ : D.s → ZMod p)
    (hI : ∀ c ∈ I, v c = 0) (hKill : ∀ c ∈ Kill, v c = 0)
    (hnext : ∀ i j, D.nextRed i j =
      rfH p (mR i * mC j * ∑ c, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹))) :
    GLE p (Fintype.card (ι ⊕ κ) + R0 - (D.s.card - (p - (I ∪ Kill).card))) Φ.det :=
  D.gle_det_uf R0 hR v I Kill mR mC ρ σ hI hKill hnext

end CatalanCore.Uniform.Content.Wire
