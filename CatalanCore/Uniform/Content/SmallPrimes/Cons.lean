module

public import CatalanCore.Uniform.Content.SmallPrimes.Output
public import CatalanCore.Uniform.Content.UFWire.Layer

@[expose] public section

/-!
# The UF-extended two-term output with a small-prime budget (lane H14)

`hasContent_twoTerm_cons'` is `UFWire.hasContent_twoTerm_cons` with the prefix hypothesis
relaxed by a `SmallBudget`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.SmallPrimes

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {depth e : ℕ} {M : ℕ} [NeZero M]

/-- **Output: two-term frames on the alternating geometry with one extra (UF) layer `L`.**
`HasContent` of the even-scale family from the layers `[trop, M3D, LP1, LP2, L] ++ ext'`; the
covering hypotheses are over the existential choice of layer (`L` is index `4`).  Take
`L := ufLayer ..` (or `ufLayerF ..`). -/
theorem hasContent_twoTerm_cons'
    (W : ∀ r p : ℕ, ((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k →
      ((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        ((altGeom c hc).geometry r).xs a)
        (Sum.elim (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
          ((altGeom c hc).geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (kf jf : ℕ → ℕ → ℕ)
    (L : DebitLayer (altGeom c hc) Fr depth)
    (ext' : Fin e → DebitLayer (altGeom c hc) Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
            (Fin.cons L ext') j).valid r p ∧
          (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
            (Fin.cons L ext') j).eff r p = 0)
    (pre : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
            (Fin.cons L ext') j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
            (Fin.cons L ext') j).eff r p : ℕ) : ℝ)
            ≤ (tmpl c).α0 * r + B.X r p)
    (cov : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
            (Fin.cons L ext') j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
            (Fin.cons L ext') j).eff r p : ℕ) : ℝ)
            ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, r % 2 = 0 → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
          (Fin.cons L ext') j).valid r p ∧
        (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf
          (Fin.cons L ext') j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0))
      ((((altGeom c hc).common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_twoTerm_on' (fun r => r % 2 = 0) W hrat a b q o kf jf
    (Fin.cons L ext') tmpl K hK B tail pre cov exc


end CatalanCore.Uniform.Content.SmallPrimes
