module
public import CatalanCore.Arith.Hybrid.ShiftZero
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
open ChainClasses

/-! # The two-level row bound for one long cell, conditional on N1 only

`WeightedSameCell` is the single remaining frame obligation (the weighted same-cell congruence).
Given it, the geometry of one cell `[a,b) ⊆ [r, r+2m)` (cut-free, with long residues) yields both
members with `σ = (b - a) - m` and `b = |zoneSb|` (`twoLevel_row_both`). -/

section Count
variable {r m : ℕ}

/-- Rows and columns of the zone in `[a,b)` count the integers of the interval. -/
theorem card_cellRows_add_cellCols {a b : ℕ} (hra : r ≤ a) (hb : b ≤ r + 2 * m) :
    (cellRows r m a b).card + (cellCols r m a b).card = b - a := by
  classical
  let f : Fin m ⊕ Fin m → ℕ := fun x => Sum.elim (fun i => r + 2 * i.val) (fun j => r + 2 * j.val + 1) x
  have hf : Function.Injective f := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j <;> simp only [f, Sum.elim_inl, Sum.elim_inr] at hxy
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))
  have himg : ((cellRows r m a b).disjSum (cellCols r m a b)).image f = Finset.Ico a b := by
    ext k
    simp only [Finset.mem_image, Finset.mem_disjSum, Finset.mem_Ico]
    constructor
    · rintro ⟨x, ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩, rfl⟩
      · rw [mem_cellRows] at hi; simp only [f, Sum.elim_inl]; omega
      · rw [mem_cellCols] at hj; simp only [f, Sum.elim_inr]; omega
    · intro hk
      by_cases he : (k - r) % 2 = 0
      · refine ⟨Sum.inl ⟨(k - r) / 2, by omega⟩, Or.inl ⟨⟨(k - r) / 2, by omega⟩, ?_, rfl⟩,
          by simp only [f, Sum.elim_inl]; omega⟩
        rw [mem_cellRows]; simp only; omega
      · refine ⟨Sum.inr ⟨(k - r) / 2, by omega⟩, Or.inr ⟨⟨(k - r) / 2, by omega⟩, ?_, rfl⟩,
          by simp only [f, Sum.elim_inr]; omega⟩
        rw [mem_cellCols]; simp only; omega
  have := Finset.card_image_of_injective ((cellRows r m a b).disjSum (cellCols r m a b)) hf
  rw [himg, Finset.card_disjSum, Nat.card_Ico] at this
  exact this.symm

end Count

section Row
variable {Fr : Frame} {p o r m : ℕ} [Fact p.Prime]

/-- **N1**, the weighted same-cell congruence for the cell `[a,b)` with source row node `x0`:
there are constants `α, β` for which `T_zy` reduces to the weighted Cauchy sum with the weight
`w(c) = α (c̄_C - c̄(c)) + β 1_S(c)`, for every row `z` and column `y` of the cell. -/
def WeightedSameCell (Fr : Frame) (p o r m a b h x0 : ℕ) [Fact p.Prime] : Prop :=
  ∃ α β : RatFunc (ZMod p), ChainModel.ZoneWt Fr p r m (cellRows r m a b) (cellCols r m a b)
    (zoneWeight Fr p o r h x0 α β)

/-- **Both members for one long cell, conditional on N1.**  `σ = (b - a) - m` is the overfull
count and `B = |zoneSb|` the number of uncovered short residues. -/
theorem twoLevel_row_both (I : HybInst Fr) [I.DiagOK r m] (hL : LamData Fr o) (hp : 5 ≤ p)
    (hm : 2 * m < p) (hN : 4 * (r + 2 * m + 1) < p * p) {k : ℕ}
    (hk : (4 : ZMod p) * k = (o : ZMod p)) (hb : p ≤ r + 2 * m)
    {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    {a b : ℕ} (hra : r ≤ a) (hbN : b ≤ r + 2 * m)
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    (z0 : Fin m) (hz0 : a ≤ r + 2 * z0.val ∧ r + 2 * z0.val < b)
    (hlong : ∀ k, a ≤ k → k < b → r ≤ k → k < r + 2 * m → ((k : ℕ) : ZMod p) ∉ shortArc p h)
    (hN1 : WeightedSameCell Fr p o r m a b h (r + 2 * z0.val))
    (hσ : (b - a - m) + ((b - a - m) - (zoneSb p r m h).card) ≤ m) :
    GLE p (m - ((b - a - m) + ((b - a - m) - (zoneSb p r m h).card)) + 2 * r) (Fr.fullPoly r m) ∧
    GLE p (m - ((b - a - m) + ((b - a - m) - (zoneSb p r m h).card)) + topC I r m p + 2 * r)
      ((Rect.afterTop r m).fullPolyG Fr) := by
  obtain ⟨α, β, hwt⟩ := hN1
  have hcard := card_cellRows_add_cellCols (r := r) (m := m) (a := a) (b := b) hra hbN
  have hN0 : 4 * (r + 2 * m) < p * p := by omega
  have hcell := zoneCell_of_cut (p := p) (o := o) (r := r) (m := m) hcut
  have hzero := zoneZero_of_response (Fr := Fr) hL hp hm hN0 hh hroot hcut z0 hz0 hlong α β
  have hσ' : ((cellRows r m a b).card + (cellCols r m a b).card - m) +
      (((cellRows r m a b).card + (cellCols r m a b).card - m) - (zoneSb p r m h).card) ≤ m := by
    rw [hcard]; exact hσ
  have H1 := ChainModel.twoLevel_fullPoly_gle_of_wt (Fr := Fr) hL hp hm hN0 hk
    (cellRows r m a b) (cellCols r m a b) _ (zoneSb p r m h) hcell hwt hzero
  have H2 := ChainModel.twoLevel_top_gle_of_wt I hL hp hm hN hk hb
    (cellRows r m a b) (cellCols r m a b) _ (zoneSb p r m h) hcell hwt hzero hσ'
  rw [hcard] at H1 H2
  exact ⟨H1, H2⟩

end Row
#print axioms twoLevel_row_both
end CatalanCore.Arith.Hybrid
