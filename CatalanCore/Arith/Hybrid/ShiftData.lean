module
public import CatalanCore.Arith.Hybrid.ShiftLead
public import CatalanCore.Arith.Hybrid.TwoLevelFull
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # The interface instance, conditional on the weighted same-cell congruence

`shiftData_of_wt` builds the `ShiftCauchyData` of the actual scaled Schur complement from
* the leading cross-cell blocks (`lead_cross_cell_rows/cols`, proved), and
* the weighted same-cell congruence `wt` and the zero pattern of the weight `zero` (hypotheses:
  `wt` is the open obligation N1; `zero` follows from `response_long_eq_free/_occupied` once `wt`
  fixes the weight `w`).

Row residues are those of the row nodes `xs`, column residues those of `ys`. -/

section Data
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)

include hL hp hN hr hk hx hy in
theorem shiftData_of_wt (CR CC : Finset Z) (w : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p))
    (hCR : ∀ z ∈ CR, r ≤ xs z) (hCC : ∀ y ∈ CC, r ≤ ys y)
    (hcellR : ∀ z ∈ CR, ∀ z' ∈ CR, xs z ≤ xs z' →
      ChainClasses.NoCut (ChainClasses.Cut (p:ℤ) (r:ℤ) (ChainClasses.Singular (p:ℤ) (o:ℤ)))
        (xs z : ℤ) (xs z' : ℤ))
    (hcellC : ∀ y ∈ CC, ∀ y' ∈ CC, ys y ≤ ys y' →
      ChainClasses.NoCut (ChainClasses.Cut (p:ℤ) (r:ℤ) (ChainClasses.Singular (p:ℤ) (o:ℤ)))
        (ys y : ℤ) (ys y' : ℤ))
    (hdist : ∀ z y, ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0)
    (hwt : ∀ z ∈ CR, ∀ y ∈ CC, ∃ T' : (LocRing p)[X],
      toQ p T' = LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
        (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
        (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
        (ChainModel.Nm Fr p r xs ys) z y ∧
      phiP p T' = ∑ c : ZMod p, rfC p ((c - ((xs z : ℕ) : ZMod p))⁻¹) * w c *
        rfC p ((c - ((ys y : ℕ) : ZMod p))⁻¹))
    (hzero : ∀ c, c ∉ sb → w c = 0 ∨ (∃ y, y ∉ CC ∧ ((ys y : ℕ) : ZMod p) = c) ∨
      (∃ z, z ∉ CR ∧ ((xs z : ℕ) : ZMod p) = c)) :
    ShiftCauchyData p (LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
        (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
        (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
        (ChainModel.Nm Fr p r xs ys))
      (fun z => ((xs z : ℕ) : ZMod p)) (fun y => ((ys y : ℕ) : ZMod p)) CR CC w sb where
  lead₁ := fun y _ => lead_cross_cell_rows hL hp hN hr hk hx hy CR hCR hcellR
    (fun z _ y' => hdist z y') y
  lead₂ := fun z _ => lead_cross_cell_cols hL hp hN hr hk hx hy CC hCC hcellC
    (fun y _ z' => hdist z' y) z
  wt := hwt
  zero := hzero

end Data

#print axioms shiftData_of_wt
end CatalanCore.Arith.Hybrid
