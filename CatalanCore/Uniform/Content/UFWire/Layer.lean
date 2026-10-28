module

public import CatalanCore.Uniform.Content.UFWire.Cell
public import CatalanCore.Uniform.Content.Shape.Wrap

@[expose] public section

/-!
# The UF debit layer and the `HasContent` output (lane H8)

* `ufLayer`: from cells `UFCell` on a validity window `valid r p` and a price `base ≥ bound`, the
  `DebitLayer (altGeom c hc) Fr depth` of debit 1 (`smithJKLayer`).
* `hasContent_twoTerm_uf`: the H7 output `Shape.hasContent_twoTerm_on` with `P r := r % 2 = 0`
  and `ext = [ufLayer] ++ ext'` (the UF layer is index `4` of `twoTermLayers`).
* `uf_cover_of_bound`: bookkeeping for the covering hypotheses: if a cell is available at `(r, p)`
  and `bound + depth ≤ B`, the layer provides `eff ≤ B`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFWire

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {T : TwoTermData Fr q o}

/-- **The UF debit layer** of the alternating geometry (two-term frame): per `(r, p)` in the
validity window a `UFCell`, priced by `base ≥ UFCell.bound`. -/
noncomputable def ufLayer {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCell c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p) :
    DebitLayer (altGeom c hc) Fr depth :=
  smithJKLayer valid base (fun r p _ h => (cell r p h).datum)
    (fun r p _ h => (cell r p h).price_le.trans (hbase r p h))

theorem ufLayer_valid {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCell c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p) :
    (ufLayer (depth := depth) (T := T) valid base cell hbase).valid = valid := rfl

theorem ufLayer_debit {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCell c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p) :
    (ufLayer (depth := depth) (T := T) valid base cell hbase).debit = 1 := rfl

theorem ufLayer_base {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCell c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p) :
    (ufLayer (depth := depth) (T := T) valid base cell hbase).base = base := rfl

/-- Covering bookkeeping: the effective price of the UF layer at `(r, p)`. -/
theorem ufLayer_eff {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCell c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p)
    (r p : ℕ) : (ufLayer (depth := depth) (T := T) valid base cell hbase).eff r p =
      base r p + depth := by
  simp [DebitLayer.eff, ufLayer_base, ufLayer_debit]

variable {depth e : ℕ} {M : ℕ} [NeZero M]

/-- **Output: two-term frames on the alternating geometry with one extra (UF) layer `L`.**
`HasContent` of the even-scale family from the layers `[trop, M3D, LP1, LP2, L] ++ ext'`; the
covering hypotheses are over the existential choice of layer (`L` is index `4`).  Take
`L := ufLayer ..` (or `ufLayerF ..`). -/
theorem hasContent_twoTerm_cons
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
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
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
            ≤ (tmpl c).α0 * r)
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
  hasContent_twoTerm_on (fun r => r % 2 = 0) W hrat a b q o kf jf
    (Fin.cons L ext') tmpl K hK tail pre cov exc

/-- The UF layer sits at index `4` of the layer list. -/
theorem twoTermLayers_uf_index (Ltrop : DebitLayer (altGeom c hc) Fr depth) (a b : ℕ → ℕ → ℕ)
    (kf jf : ℕ → ℕ → ℕ) (L : DebitLayer (altGeom c hc) Fr depth)
    (ext' : Fin e → DebitLayer (altGeom c hc) Fr depth) :
    twoTermLayers Ltrop a b q o kf jf (Fin.cons L ext') 4 = L := rfl

end CatalanCore.Uniform.Content.UFWire
