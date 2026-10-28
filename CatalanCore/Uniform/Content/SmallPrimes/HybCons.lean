module

public import CatalanCore.Uniform.Content.SmallPrimes.Hyb
public import CatalanCore.Uniform.Content.SmallPrimes.Cons

@[expose] public section

/-!
# The UF-extended hybrid output on the alternating geometry (lane H14)

`hasContent_twoTerm_cons_alt`: `hasContent_twoTerm_cons'` with the prefix hypothesis replaced by the
leading-table bound `tropVal (U r p) ≤ alpha0 * r` and the entrywise excess hypothesis
(`Hyb`); the small-prime budget is `SmallBudget.sqrtLog L C`, discharged with no data.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.SmallPrimes

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {depth e : ℕ} {M : ℕ} [NeZero M]

theorem hasContent_twoTerm_cons_alt
    (W : ∀ r p : ℕ, ((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k → ((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs a)
        (Sum.elim (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).ys b) ∈ LocRing p)
    (a b kf jf : ℕ → ℕ → ℕ)
    (Lu : DebitLayer (altGeom c hc) Fr depth)
    (ext' : Fin e → DebitLayer (altGeom c hc) Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (U : ∀ r p : ℕ, ((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k → ((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k → ℕ) (L C e0 : ℕ)
    (hC : (2 + (c : ℝ) / 2) * e0 ≤ C)
    (tail : ∀ r : ℕ, r % 2 = 0 → ∀ cl : ZMod M, IsUnit cl → ∀ p : ℕ, p.Prime →
      (p : ZMod M) = cl → ⌊(tmpl cl).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf (Fin.cons Lu ext') j).valid r p ∧ (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf (Fin.cons Lu ext') j).eff r p = 0)
    (preU : ∀ r : ℕ, r % 2 = 0 → ∀ cl : ZMod M, IsUnit cl → ∀ p : ℕ,
      p ≤ ⌊(tmpl cl).t1 * r⌋₊ → p.Prime → (p : ZMod M) = cl →
        (tropVal (U r p) : ℝ) ≤ (tmpl cl).α0 * r)
    (hexc : ∀ r : ℕ, r % 2 = 0 → ∀ p : ℕ, p.Prime → ∀ x y,
      W r p x y ≤ U r p x y + (if p * p ≤ L * r then e0 * (Nat.log 2 r + 1) else 0))
    (cov : ∀ r : ℕ, r % 2 = 0 → ∀ cl : ZMod M, IsUnit cl → ∀ Q ∈ (tmpl cl).l, ∀ p : ℕ,
      ⌊ Q.s * r⌋₊ < p → p ≤ ⌊ Q.t * r⌋₊ → p.Prime → (p : ZMod M) = cl →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf (Fin.cons Lu ext') j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf (Fin.cons Lu ext') j).eff r p : ℕ) : ℝ) ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, r % 2 = 0 → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf (Fin.cons Lu ext') j).valid r p ∧ (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf (Fin.cons Lu ext') j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0))
      ((((altGeom c hc).common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) :=
  hasContent_twoTerm_cons' W hrat a b kf jf Lu ext' tmpl K hK (SmallBudget.sqrtLog L C) tail
    (fun r hr cl hcl p h1 hp hpc => ⟨0, tropGlobal_valid W hrat r p, by
      show (((tropGlobal (depth := depth) W hrat).eff r p : ℕ) : ℝ) ≤ _
      rw [tropGlobal_eff]
      exact trop_le_budget_card (W r p) (U r p) _ (altGeom_card_le c hc hr) L C e0 hC
        (preU r hr cl hcl p h1 hp hpc) (hexc r hr p hp)⟩) cov exc

end CatalanCore.Uniform.Content.SmallPrimes
