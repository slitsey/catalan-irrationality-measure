module

public import CatalanCore.Arith.Hybrid.Pieces

@[expose] public section

/-!
# Piecewise-linear class templates and the content constant (lane H5)

A template for a residue class is the data of the exact piecewise-linear majorant of the
per-prime price: a constant `α0 · r` on `(0, t1 · r]`, then a chain of linear pieces
`α + β θ` (`θ = p / r`).  The content constant of a family of templates, one per class of the
modulus `M`, is the sum over the unit classes of the exact piecewise-linear integrals, divided by
the density `φ(M)`.  Everything is generic in the frame and in the block data.
-/

open CatalanCore.Arith.Hybrid Filter Finset

namespace CatalanCore.Uniform.Content.Member

/-- A class template: constant prefix `α0` on `(0, t1]`, followed by a chain of linear pieces. -/
structure Template where
  α0 : ℝ
  t1 : ℝ
  l : List Piece
  hα0 : 0 ≤ α0
  ht1 : 0 < t1
  chain : Chain t1 l

namespace Template

/-- The right end of the template. -/
noncomputable def tend (T : Template) : ℝ := lastEnd T.t1 T.l

/-- The exact integral of the template: prefix plus the linear pieces. -/
noncomputable def mass (T : Template) : ℝ := T.α0 * T.t1 + listInt T.l

lemma t1_le_tend (T : Template) : T.t1 ≤ T.tend := lastEnd_ge T.l T.t1 T.chain

lemma tend_pos (T : Template) : 0 < T.tend := lt_of_lt_of_le T.ht1 T.t1_le_tend

end Template

/-- A chain piece has nonnegative integral. -/
lemma piece_int_nonneg {P : Piece} (hst : P.s ≤ P.t) (h0 : 0 ≤ P.α + P.β * P.s)
    (h1 : 0 ≤ P.α + P.β * P.t) : 0 ≤ P.int := by
  have e : P.int = (P.t - P.s) / 2 * ((P.α + P.β * P.s) + (P.α + P.β * P.t)) := by
    unfold Piece.int; ring
  rw [e]
  exact mul_nonneg (by linarith) (by linarith)

lemma listInt_nonneg : ∀ (l : List Piece) (s0 : ℝ), Chain s0 l → 0 ≤ listInt l
  | [], _, _ => by simp [listInt]
  | P :: l, s0, h => by
    obtain ⟨-, -, h3, -, h5, h6, h7⟩ := h
    simp only [listInt]
    exact add_nonneg (piece_int_nonneg h3 h5 h6) (listInt_nonneg l P.t h7)

lemma Template.mass_nonneg (T : Template) : 0 ≤ T.mass := by
  unfold Template.mass
  exact add_nonneg (mul_nonneg T.hα0 T.ht1.le) (listInt_nonneg T.l T.t1 T.chain)

/-- The set of unit classes of `ZMod M`. -/
noncomputable def unitClasses (M : ℕ) [NeZero M] : Finset (ZMod M) :=
  (Finset.univ : Finset (ZMod M)).filter IsUnit

lemma mem_unitClasses {M : ℕ} [NeZero M] {c : ZMod M} : c ∈ unitClasses M ↔ IsUnit c := by
  unfold unitClasses
  simp

lemma card_unitClasses_le (M : ℕ) [NeZero M] : (unitClasses M).card ≤ M := by
  unfold unitClasses
  exact (Finset.card_filter_le _ _).trans (by simp [ZMod.card])

/-- **The content constant.**  The sum over the unit classes of the exact piecewise-linear
integrals of the class templates, over the density `φ(M)`. -/
noncomputable def contentConstant (M : ℕ) [NeZero M] (tmpl : ZMod M → Template) : ℝ :=
  (∑ c ∈ unitClasses M, (tmpl c).mass) / (M.totient : ℝ)

lemma contentConstant_nonneg (M : ℕ) [NeZero M] (tmpl : ZMod M → Template) :
    0 ≤ contentConstant M tmpl :=
  div_nonneg (Finset.sum_nonneg fun c _ => (tmpl c).mass_nonneg) (Nat.cast_nonneg _)

/-- A common right end: the sum of the right ends of all class templates. -/
noncomputable def commonEnd (M : ℕ) [NeZero M] (tmpl : ZMod M → Template) : ℝ := ∑ c, (tmpl c).tend

lemma tend_le_commonEnd (M : ℕ) [NeZero M] (tmpl : ZMod M → Template) (c : ZMod M) :
    (tmpl c).tend ≤ commonEnd M tmpl := by
  unfold commonEnd
  exact Finset.single_le_sum (f := fun c => (tmpl c).tend)
    (fun c _ => (tmpl c).tend_pos.le) (Finset.mem_univ c)

end CatalanCore.Uniform.Content.Member
