module

public import CatalanCore.Uniform.Content.UFFamily4.Content

@[expose] public section

/-!
# `HasContent` for the thirds frame with the UF layer (lane H, H13)

`thirdsUFContent` is `hasContent_twoTerm_cons` with `L := thirdsUFLayer T` (geometry `c = 3/10`,
`q = 3`, `o = 2`).  The UF layer is used on the band `Band r p` (`60 ≤ p`, `3 r < 10 p ≤ 39 r`) for
those template pieces `Q` with `useUF c Q`; the bound it must meet there is `UFBound`, a statement
about each family region separately (no first-match bookkeeping: `idx` is hidden by
`thirds_cover`).  Everything else (`tail`, `pre`, `exc`, and the pieces off the band or not using
UF) is passed through.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.UFFamily3

namespace CatalanCore.Uniform.Content.UFFamily4

/-- **The per-family price bound for a template piece** `α r + β p + C` on the strip
`⌊s r⌋ < p ≤ ⌊t r⌋`: in every family region `i` meeting the strip inside the band, the UF price
`baseOf i r p + depth` is at most the piece. -/
def UFBound (depth : ℕ) (s t α β C : ℝ) : Prop :=
  ∀ r p : ℕ, r % 2 = 0 → Band r p → ⌊s * r⌋₊ < p → p ≤ ⌊t * r⌋₊ →
    ∀ i, RegOf i r p → (((baseOf i r p + depth : ℕ)) : ℝ) ≤ α * r + β * p + C

variable {Fr : Frame}

/-- The layer list of the thirds frame: `[trop, M3D, LP1, LP2, UF] ++ ext'`. -/
noncomputable abbrev thirdsLayers (T : TwoTermData Fr 3 2) {depth e : ℕ}
    (W : ∀ r p : ℕ, ((altGeom cT cT_pos).geometry r).C ⊕ Fin ((altGeom cT cT_pos).geometry r).k →
      ((altGeom cT cT_pos).geometry r).C ⊕ Fin ((altGeom cT cT_pos).geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : ((altGeom cT cT_pos).geometry r).C => (a : ℕ))
        ((altGeom cT cT_pos).geometry r).xs a)
        (Sum.elim (fun a : ((altGeom cT cT_pos).geometry r).C => (a : ℕ))
          ((altGeom cT cT_pos).geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext' : Fin e → DebitLayer (altGeom cT cT_pos) Fr depth) :
    Fin (e + 1 + 1 + 1 + 1 + 1) → DebitLayer (altGeom cT cT_pos) Fr depth :=
  twoTermLayers (tropGlobal (depth := depth) W hrat) a b 3 2 kf jf
    (Fin.cons (thirdsUFLayer (depth := depth) T) ext')

/-- **Content for the thirds frame with the UF layer.**  For the thirds even-scale family
(`altGeom (3/10)`, two-term data `T : TwoTermData Fr 3 2` of norm `1`):

* the UF layer prices every `(r, p)` of the band (`thirds_valid`) by the first family containing it
  (`thirds_cover`), and the template pieces flagged `useUF` need only the per-family bound `UFBound`;
* pieces off the band, or not flagged, and the prefix / tail / exceptional primes are passed
  through exactly as in `hasContent_twoTerm_cons`. -/
theorem thirdsUFContent (T : TwoTermData Fr 3 2) (hn : Fr.norm = 1) {depth e M : ℕ} [NeZero M]
    (W : ∀ r p : ℕ, ((altGeom cT cT_pos).geometry r).C ⊕ Fin ((altGeom cT cT_pos).geometry r).k →
      ((altGeom cT cT_pos).geometry r).C ⊕ Fin ((altGeom cT cT_pos).geometry r).k → ℕ)
    (hrat : ∀ r p, ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : ((altGeom cT cT_pos).geometry r).C => (a : ℕ))
        ((altGeom cT cT_pos).geometry r).xs a)
        (Sum.elim (fun a : ((altGeom cT cT_pos).geometry r).C => (a : ℕ))
          ((altGeom cT cT_pos).geometry r).ys b) ∈ LocRing p)
    (a b : ℕ → ℕ → ℕ) (kf jf : ℕ → ℕ → ℕ)
    (ext' : Fin e → DebitLayer (altGeom cT cT_pos) Fr depth)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K) (useUF : ZMod M → Piece → Prop)
    (tail : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p →
        ∃ j, (thirdsLayers T W hrat a b kf jf ext' j).valid r p ∧
          (thirdsLayers T W hrat a b kf jf ext' j).eff r p = 0)
    (pre : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (thirdsLayers T W hrat a b kf jf ext' j).valid r p ∧
          (((thirdsLayers T W hrat a b kf jf ext' j).eff r p : ℕ) : ℝ) ≤ (tmpl c).α0 * r)
    (hUF : ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, useUF c Q →
      UFBound depth Q.s Q.t Q.α Q.β Q.C)
    (covOther : ∀ r : ℕ, r % 2 = 0 → ∀ c : ZMod M, IsUnit c → ∀ Q ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊Q.s * r⌋₊ < p → p ≤ ⌊Q.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ¬ (Band r p ∧ useUF c Q) →
        ∃ j, (thirdsLayers T W hrat a b kf jf ext' j).valid r p ∧
          (((thirdsLayers T W hrat a b kf jf ext' j).eff r p : ℕ) : ℝ)
            ≤ Q.α * r + Q.β * p + Q.C)
    (exc : ∀ r : ℕ, r % 2 = 0 → ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ j, (thirdsLayers T W hrat a b kf jf ext' j).valid r p ∧
        (((thirdsLayers T W hrat a b kf jf ext' j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent (((altGeom cT cT_pos).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0))
      ((((altGeom cT cT_pos).common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) := by
  have hidx := twoTermLayers_uf_index (tropGlobal (depth := depth) W hrat) a b
    (q := 3) (o := 2) kf jf (thirdsUFLayer (depth := depth) T) ext'
  refine hasContent_twoTerm_cons W hrat a b kf jf (thirdsUFLayer (depth := depth) T) ext' tmpl K hK
    tail pre ?_ exc
  intro r hr c hc Q hQ p hs ht hp hpc
  by_cases hb : Band r p ∧ useUF c Q
  · obtain ⟨hband, hu⟩ := hb
    refine ⟨4, ?_, ?_⟩
    · rw [hidx]
      exact thirds_valid T hn hp hr hband
    · rw [hidx]
      obtain ⟨h60, hlo, hhi⟩ := hband
      obtain ⟨h2, h3⟩ := prime_odd_of_ge hp h60
      have hcov := thirds_cover hr h2 h3 hlo hhi h60
      obtain ⟨hreg, heff⟩ := thirds_eff (depth := depth) T hcov
      rw [heff]
      exact hUF c hc Q hQ hu r p hr ⟨h60, hlo, hhi⟩ hs ht _ hreg
  · exact covOther r hr c hc Q hQ p hs ht hp hpc hb

end CatalanCore.Uniform.Content.UFFamily4
