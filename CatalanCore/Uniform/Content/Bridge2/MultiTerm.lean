module

public import CatalanCore.Uniform.Content.Bridge.Hybrid

@[expose] public section

/-!
# End-to-end hybrid with multi-term layers (lane B, package B0)

Mirror of `BlockGeom.measure_of_twoTerm_even` with `hasContent_multiTerm_on` in place of
`hasContent_twoTerm_on`.  Covering hypotheses are only at even `r`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.BlockGeom

variable {G : BlockGeom} {Fr : Frame} {depth e : ℕ} {M : ℕ} [NeZero M]

/-- **End-to-end hybrid (multi-term layers).** -/
theorem measure_of_multiTerm_even {D c : ℝ}
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p = 0)
    (pre : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ (tmpl c).α0 * r)
    (cov : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, r % 2 = 0 → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
        (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
          ≤ K * r)
    (hD : HasScaledDecay (G.family Fr depth) G.scale D c)
    (L : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hCd : ∀ i, (G.common.block i).d ∣ L)
    (hXd : ∀ i, (G.row.block i).d ∣ L)
    (hYd : ∀ i, (G.column.block i).d ∣ L)
    (hdepth : G.selectionDepth Fr L ≤ depth)
    (hη : contentConstant M tmpl < D) (hc : 0 < c) :
    (G.family Fr depth).MeasureLB ((G.common.mass : ℝ) * c / (D - contentConstant M tmpl)) :=
  measure_of_content_even G Fr depth tmpl
    (hasContent_multiTerm_on (P := fun r => r % 2 = 0) W hrat a b ext tmpl K hK
      tail pre cov exc)
    hD (G.hasNV0 Fr L depth hL hd hw hCd hXd hYd hdepth) hη hc

end CatalanCore.Uniform.BlockGeom
