module

public import CatalanCore.Uniform.Content.Wire.LP
public import CatalanCore.Uniform.Content.Wire.M3D
public import CatalanCore.Uniform.Content.Wire.UF
public import CatalanCore.Uniform.Content.Member.Entries
public import CatalanCore.Uniform.Content.Member.HasContent

@[expose] public section

/-!
# `HasContent` for hybrid block-geometry families (lane H6, output)

The layer list of a bank is

* index `0`: the tropical layer from the rational entry valuations `W` of the bank (global);
* `M3D` (debit 0), `LP1`, `LP2` (debit 1; two-term frames only), and
* `ext`: any further bank layers (rank layer `member_gle_rank`, UF `ufMember_gle`, Smith
  `smithSD`, ...), each given as a `DebitLayer`.  UF is optional: take `ext` without it.

`hasContent_twoTerm` is H5's `hasContent_of_debitLayers` for the list
`[trop, M3D, LP1, LP2] ++ ext`; `hasContent_multiTerm` for `[trop, M3D] ++ ext` (frames without
LP, e.g. the three-term frame of `L(2, chi_{-3})`).  What remains as hypotheses is frame / bank
data only: the entry valuations, the two-term configuration windows (`LP1Hyp`, `LP2Hyp` through
`lp1Valid`, `lp2Valid`), the M3D witness segment and cut-freeness (`m3dValid`), the class
templates and the covering conditions.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.Wire

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ}

/-- The global tropical layer from rational entry valuations of the bank. -/
noncomputable def tropGlobal
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p) :
    DebitLayer G Fr depth :=
  DebitLayer.tropRat (fun _ _ => True) W (fun r p _ _ => hrat r p)

theorem tropGlobal_valid
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (r p : ℕ) : (tropGlobal (depth := depth) W hrat).valid r p := trivial

variable {e : ℕ}

/-- Layer list of a two-term bank: `[trop, M3D, LP1, LP2] ++ ext`. -/
noncomputable def twoTermLayers (Ltrop : DebitLayer G Fr depth) (a b : ℕ → ℕ → ℕ)
    (q o : ℕ) (kf jf : ℕ → ℕ → ℕ) (ext : Fin e → DebitLayer G Fr depth) :
    Fin (e + 1 + 1 + 1 + 1) → DebitLayer G Fr depth :=
  Fin.cons Ltrop (Fin.cons (m3dLayer G Fr depth a b) (Fin.cons (lp1Layer G Fr depth q o kf jf)
    (Fin.cons (lp2Layer G Fr depth q o kf jf) ext)))

/-- Layer list of a multi-term bank without LP: `[trop, M3D] ++ ext`. -/
noncomputable def multiTermLayers (Ltrop : DebitLayer G Fr depth) (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth) : Fin (e + 1 + 1) → DebitLayer G Fr depth :=
  Fin.cons Ltrop (Fin.cons (m3dLayer G Fr depth a b) ext)

variable {M : ℕ} [NeZero M]

/-- **Output (two-term frames: fifths, thirds, lambda, sevenths).** -/
theorem hasContent_twoTerm
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (q o : ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p = 0)
    (pre : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).valid r p ∧
          (((twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext j).eff r p : ℕ)
            : ℝ) ≤ (tmpl c).α0 * r)
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
  hasContent_of_debitLayers G Fr depth (k := e + 3)
    (twoTermLayers (tropGlobal (depth := depth) W hrat) a b q o kf jf ext)
    (fun r p => tropGlobal_valid W hrat r p) tmpl K hK tail pre cov exc

/-- **Output (general multi-term frames without LP).** -/
theorem hasContent_multiTerm
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ)
    (ext : Fin e → DebitLayer G Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p = 0)
    (pre : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).valid r p ∧
          (((multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext j).eff r p : ℕ) : ℝ)
            ≤ (tmpl c).α0 * r)
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
  hasContent_of_debitLayers G Fr depth (k := e + 1)
    (multiTermLayers (tropGlobal (depth := depth) W hrat) a b ext)
    (fun r p => tropGlobal_valid W hrat r p) tmpl K hK tail pre cov exc

end CatalanCore.Uniform.Content.Wire
