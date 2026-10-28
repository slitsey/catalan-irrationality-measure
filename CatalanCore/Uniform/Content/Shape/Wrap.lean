module

public import CatalanCore.Uniform.Content.Shape.Even

@[expose] public section

/-!
# Two-term and multi-term outputs on a scale predicate (lane H7)

The statements of `Wire.hasContent_twoTerm` / `hasContent_multiTerm`, with every covering
hypothesis required only at scales `r` with `P r`; the conclusion is for the family restricted to
those scales.  Take `P r := r % 2 = 0` for the alternating geometry (`altGeom_hybShape`).
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire

namespace CatalanCore.Uniform.Content.Shape

variable {G : BlockGeom} {Fr : Frame} {depth e : ℕ} {M : ℕ} [NeZero M]

theorem hasContent_twoTerm_on (P : ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p = 0)
    (pre : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ (tmpl c).α0 * r)
    (cov : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
        (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
          : ℝ) ≤ K * r) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_of_debitLayers_on G Fr depth P (k := e + 3)
    (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext)
    (fun r p _ => tropGlobal_valid W hrat r p) tmpl K hK tail pre cov exc

theorem hasContent_multiTerm_on (P : ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p = 0)
    (pre : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ (tmpl c).α0 * r)
    (cov : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, P r → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
        (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
          ≤ K * r) :
    HasContent ((G.family Fr depth).restrictAdm (fun i => P i.1))
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_of_debitLayers_on G Fr depth P (k := e + 1)
    (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext)
    (fun r p _ => tropGlobal_valid W hrat r p) tmpl K hK tail pre cov exc

end CatalanCore.Uniform.Content.Shape
