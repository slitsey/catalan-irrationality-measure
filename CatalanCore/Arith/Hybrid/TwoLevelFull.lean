module

public import CatalanCore.Arith.Hybrid.TwoLevelCauchy
public import CatalanCore.Arith.Hybrid.LemmaE.TCore

@[expose] public section

/-!
# F2, generic part : the two family members from Cauchy data on the scaled Schur complement

`ShiftCauchyData` is the exact interface that the frame-side entry congruences
(`lead_cross_cell`, `weighted_same_cell`, `response_long_eq`) must deliver, stated for the
scaled Schur complement `T = Tscaled …` (entries `p`-integral up to one factor `p`):

* (lead) the lift of `p T z y` reduces to `κ(y) · (res y - res z)⁻¹` for `z ∈ CR`, `y ∉ CC`
  (and symmetrically);
* (wt) for `z ∈ CR`, `y ∈ CC`, `T z y` is `p`-integral and reduces to
  `∑_c F(z,c) w(c) G(c,y)` with `F(z,c) = (c - res z)⁻¹`, `G(c,y) = (c - res y)⁻¹`;
* (zero) `w c = 0` off `sb` unless `c` is the residue of a node outside `CC` or outside `CR`.

Member 1 follows from `tcore_of_det_gle` and the two-level principle; member 2 from the same with
the bordered two-level principle (`gle_det_two_level_border`), at cost exactly `2w + 1`.
-/

open Polynomial CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

variable (p : ℕ) [Fact p.Prime]

/-- Frame-side Cauchy data for a scaled Schur complement `T`. -/
structure ShiftCauchyData {κ : Type*} (T : Matrix κ κ ℚ[X]) (res : κ → ZMod p)
    (CR CC : Finset κ) (w : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p)) : Prop where
  lead₁ : ∀ y, y ∉ CC → ∃ k0 : RatFunc (ZMod p), ∀ z ∈ CR, ∀ g : (LocRing p)[X],
    toQ p g = C (p : ℚ) * T z y → phiP p g = k0 * rfC p ((res y - res z)⁻¹)
  lead₂ : ∀ z, z ∉ CR → ∃ k0 : RatFunc (ZMod p), ∀ y ∈ CC, ∀ g : (LocRing p)[X],
    toQ p g = C (p : ℚ) * T z y → phiP p g = k0 * rfC p ((res y - res z)⁻¹)
  wt : ∀ z ∈ CR, ∀ y ∈ CC, ∃ T' : (LocRing p)[X], toQ p T' = T z y ∧
    phiP p T' = ∑ c : ZMod p, rfC p ((c - res z)⁻¹) * w c * rfC p ((c - res y)⁻¹)
  zero : ∀ c, c ∉ sb → w c = 0 ∨ (∃ y, y ∉ CC ∧ res y = c) ∨ (∃ z, z ∉ CR ∧ res z = c)

lemma toQ_injective : Function.Injective (toQ p) :=
  Polynomial.map_injective _ Subtype.val_injective

/-- From Cauchy data to a two-level witness of `det T`, with weights `u ≡ 1`, `v ≡ 0`. -/
theorem exists_twoLevelWit_of_shiftData {κ : Type} [Fintype κ] [DecidableEq κ]
    (T : Matrix κ κ ℚ[X]) (res : κ → ZMod p) (CR CC : Finset κ)
    (w : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p))
    (hint : ∀ z y, GLE p 1 (T z y)) (D : ShiftCauchyData p T res CR CC w sb) :
    ∃ W : TwoLevelWit p T sb.card, W.u = (fun _ => 1) ∧ W.v = (fun _ => 0) ∧
      W.s.card = CR.card + CC.card - Fintype.card κ ∧
      W.cost = Fintype.card κ -
        ((CR.card + CC.card - Fintype.card κ) +
          ((CR.card + CC.card - Fintype.card κ) - sb.card)) := by
  classical
  have h1 : ∀ z y, ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ 1) * T z y :=
    fun z y => exists_lift p (hint z y)
  choose Bl hBl using h1
  have hCp : toQ p (C ((p : ℕ) : LocRing p)) = C (p : ℚ) := by simp [toQ]
  obtain ⟨W, hu, hv, hs, hW⟩ := exists_twoLevelWit_of_cauchy p T Bl (fun _ => 1) (fun _ => 0)
    (fun i j => by simpa using hBl i j) res CR CC
    (fun y hy => by
      obtain ⟨k0, hk⟩ := D.lead₁ y hy
      exact ⟨k0, fun z hz => hk z hz _ (by simpa using hBl z y)⟩)
    (fun z hz => by
      obtain ⟨k0, hk⟩ := D.lead₂ z hz
      exact ⟨k0, fun y hy => hk y hy _ (by simpa using hBl z y)⟩)
    w
    (fun z hz y hy => by
      obtain ⟨T', hT1, hT2⟩ := D.wt z hz y hy
      refine ⟨T', toQ_injective p ?_, hT2⟩
      rw [map_mul, hCp, hT1, hBl z y, pow_one])
    sb D.zero
  refine ⟨W, hu, hv, hs, ?_⟩
  rw [hW]
  simp

/-- **Member 1.** -/
theorem gle_full_of_shiftData {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (g : ℚ[X]) (hg : gn p g = 1)
    (N : Matrix ι ι ℚ[X]) (hAN : Full.toBlocks₁₁ * N = g • (1 : Matrix ι ι ℚ[X]))
    (s0 : ℕ) (hdet : C ((p : ℚ) ^ s0) * Full.toBlocks₁₁.det = g)
    (res : κ → ZMod p) (CR CC : Finset κ) (w : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p))
    (hint : ∀ z y, GLE p 1 (LemmaE.Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂ Full.toBlocks₂₁
      Full.toBlocks₂₂ N z y))
    (D : ShiftCauchyData p (LemmaE.Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂ Full.toBlocks₂₁
      Full.toBlocks₂₂ N) res CR CC w sb) :
    GLE p (Fintype.card κ -
        ((CR.card + CC.card - Fintype.card κ) +
          ((CR.card + CC.card - Fintype.card κ) - sb.card)) + s0) Full.det := by
  obtain ⟨W, -, -, -, hW⟩ := exists_twoLevelWit_of_shiftData p _ res CR CC w sb hint D
  have := W.gle
  rw [hW] at this
  exact LemmaE.tcore_of_det_gle p Full g hg N hAN s0 hdet _ this

/-- **Member 2** (bordered by the common node): the border entries of the scaled Schur complement
are `GLE w` (corner `GLE 2w`); the cost of the border is exactly `2w + 1`, i.e. `topC` when
`w = topW`. -/
theorem gle_full_of_shiftData_border {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ]
    (Full : Matrix (ι ⊕ Option κ) (ι ⊕ Option κ) ℚ[X]) (g : ℚ[X]) (hg : gn p g = 1)
    (N : Matrix ι ι ℚ[X]) (hAN : Full.toBlocks₁₁ * N = g • (1 : Matrix ι ι ℚ[X]))
    (s0 : ℕ) (hdet : C ((p : ℚ) ^ s0) * Full.toBlocks₁₁.det = g)
    (res : κ → ZMod p) (CR CC : Finset κ) (w0 : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p))
    (T : Matrix (Option κ) (Option κ) ℚ[X])
    (hT : T = LemmaE.Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂ Full.toBlocks₂₁
      Full.toBlocks₂₂ N)
    (hint : ∀ z y : κ, GLE p 1 (T (some z) (some y)))
    (D : ShiftCauchyData p (Matrix.of fun z y : κ => T (some z) (some y)) res CR CC w0 sb)
    (w : ℕ) (hr : ∀ i, GLE p w (T (some i) none)) (hc : ∀ j, GLE p w (T none (some j)))
    (hd : GLE p (w + w) (T none none))
    (hk : (CR.card + CC.card - Fintype.card κ) +
      ((CR.card + CC.card - Fintype.card κ) - sb.card) ≤ Fintype.card κ) :
    GLE p (Fintype.card κ -
        ((CR.card + CC.card - Fintype.card κ) +
          ((CR.card + CC.card - Fintype.card κ) - sb.card)) + (w + w + 1) + s0) Full.det := by
  obtain ⟨W, hu, hv, hs, hW⟩ := exists_twoLevelWit_of_shiftData p
    (Matrix.of fun z y : κ => T (some z) (some y)) res CR CC w0 sb (fun z y => hint z y) D
  have hb := gle_det_two_level_border W (fun i => by simp [hu]) w hr hc hd (by
    rw [hs, hu, hv]; simpa using hk)
  rw [hW] at hb
  subst hT
  exact LemmaE.tcore_of_det_gle p Full g hg N hAN s0 hdet _ hb

#print axioms CatalanCore.Arith.Hybrid.gle_full_of_shiftData
#print axioms CatalanCore.Arith.Hybrid.gle_full_of_shiftData_border

end CatalanCore.Arith.Hybrid
