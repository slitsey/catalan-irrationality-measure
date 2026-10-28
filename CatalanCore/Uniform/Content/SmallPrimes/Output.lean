module

public import CatalanCore.Uniform.Content.SmallPrimes.Layers
public import CatalanCore.Uniform.Content.Wire.Output
public import CatalanCore.Uniform.Content.Shape.Wrap

@[expose] public section

/-!
# `HasContent` outputs with a small-prime budget (lane H14)

`hasContent_twoTerm'`, `hasContent_multiTerm'` and their scale-restricted forms
`hasContent_twoTerm_on'`, `hasContent_multiTerm_on'`: the namesakes in `Wire.Output` and
`Shape.Wrap`, with the prefix hypothesis `pre : eff ≤ alpha0 * r` replaced by
`eff ≤ alpha0 * r + B.X r p` for a `SmallBudget B` (total `o(r^2)`, e.g. `SmallBudget.sqrtLog`).
Primes up to `t1 * r` may therefore have price `r log r` as long as the exceptional ones are few.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.SmallPrimes

variable {G : BlockGeom} {Fr : Frame} {depth e : ℕ} {M : ℕ} [NeZero M]

/-- **Output (two-term frames: fifths, thirds, lambda, sevenths).** -/
theorem hasContent_twoTerm'
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p = 0)
    (pre : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ (tmpl c).α0 * r + B.X r p)
    (cov : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊P.s * r⌋₊ < p → p ≤ ⌊P.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ P.α * r + P.β * p + P.C)
    (exc : ∀ r p : ℕ, p.Prime → p ∣ M →
      ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
        (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
          : ℝ) ≤ K * r) :
    HasContent (G.family Fr depth)
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_of_debitLayersB G Fr depth (k := e + 3)
    (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext)
    (fun r p => tropGlobal_valid W hrat r p) tmpl K hK B tail pre cov exc

/-- **Output (general multi-term frames without LP).** -/
theorem hasContent_multiTerm'
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p = 0)
    (pre : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ (tmpl c).α0 * r + B.X r p)
    (cov : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊P.s * r⌋₊ < p → p ≤ ⌊P.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ P.α * r + P.β * p + P.C)
    (exc : ∀ r p : ℕ, p.Prime → p ∣ M →
      ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
        (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
          ≤ K * r) :
    HasContent (G.family Fr depth)
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_of_debitLayersB G Fr depth (k := e + 1)
    (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext)
    (fun r p => tropGlobal_valid W hrat r p) tmpl K hK B tail pre cov exc


theorem hasContent_twoTerm_on' (P : ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p = 0)
    (pre : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ (tmpl c).α0 * r + B.X r p)
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
  hasContent_of_debitLayers_onB G Fr depth P (k := e + 3)
    (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext)
    (fun r p _ => tropGlobal_valid W hrat r p) tmpl K hK B tail pre cov exc

theorem hasContent_multiTerm_on' (P : ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (B : SmallBudget)
    (tail : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p = 0)
    (pre : ∀ r : ℕ, P r → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ (tmpl c).α0 * r + B.X r p)
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
  hasContent_of_debitLayers_onB G Fr depth P (k := e + 1)
    (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext)
    (fun r p _ => tropGlobal_valid W hrat r p) tmpl K hK B tail pre cov exc


end CatalanCore.Uniform.Content.SmallPrimes
