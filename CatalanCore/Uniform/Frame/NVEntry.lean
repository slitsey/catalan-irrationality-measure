module
public import CatalanCore.Uniform.Frame.NVModel
public import CatalanCore.Uniform.NV.FrameStep
public import Mathlib.Algebra.BigOperators.Intervals
@[expose] public section

namespace CatalanCore.Uniform.NVAdapter
open Finset Polynomial Matrix
open CatalanCore.Arith.Hybrid.FiniteFieldCorank CatalanCore.Rect.CharZeroNV

private theorem prefix_sub (g : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Icc 1 b, g k) - (∑ k ∈ Icc 1 a, g k) = ∑ k ∈ Ioc a b, g k := by
  have hs : Icc 1 a ⊆ Icc 1 b := by intro k hk; simp only [mem_Icc] at *; omega
  have he : Icc 1 b \ Icc 1 a = Ioc a b := by
    ext k
    simp only [mem_sdiff,mem_Icc,mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff hs (f := g)
  rw [he] at hsum
  linear_combination -hsum

/-- Exact off-diagonal source identity, with the original frame normalization. -/
theorem mn_offdiag (Fr : Frame) (a b : ℕ) (hab : a ≠ b) :
    Fr.Mn a b = (NV.framePrefix Fr a - NV.framePrefix Fr b) / ((a : ℚ) - b) := by
  unfold Frame.Mn
  rw [if_neg hab]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
    have hs := prefix_sub Fr.Delta (Nat.le_of_lt hlt)
    dsimp [NV.framePrefix]
    rw [← hs]
    rw [show (a : ℚ) - b = -((b : ℚ) - a) by ring, div_neg]
    simp only [div_eq_mul_inv]
    ring
  · rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
    have hs := prefix_sub Fr.Delta (Nat.le_of_lt hgt)
    dsimp [NV.framePrefix]
    rw [← hs]
    ring

/-- The N provider's scalar functions give exactly the actual pencil entries. -/
theorem loewnerEntry_nat (Fr : Frame) (U : ℚ) (a b : ℕ) :
    NV.loewnerEntry (NV.onNaturals (NV.framePrefix Fr)) (NV.onNaturals (NV.frameJet Fr U))
      (a : ℚ) (b : ℚ) = (if a = b then U else 0) + Fr.Mn a b := by
  by_cases hab : a = b
  · subst b
    simp [NV.loewnerEntry, NV.frameJet, Frame.Mn]
    ring
  · have hcast : (a : ℚ) ≠ b := by exact_mod_cast hab
    simp only [NV.loewnerEntry, if_neg hcast, NV.onNaturals_nat, if_neg hab, zero_add]
    exact (mn_offdiag Fr a b hab).symm

/-- Actual FullN is exactly the reindexed general N matrix, for arbitrary
balanced finite common and border node sets. -/
theorem fullN_eq_model (Fr : Frame) (U : ℚ) (G : Rect.Geometry) :
    Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U =
      ((model G).matrix (NV.onNaturals (NV.framePrefix Fr))
        (NV.onNaturals (NV.frameJet Fr U))).submatrix (rowField G) (rowField G) := by
  rw [matrix_reindex]
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp only [Matrix.of_apply,rowField_inl,colField_inl]
    rw [loewnerEntry_nat]
    by_cases hab : a = b
    · subst b
      simp [Rect.FullN,Rect.Blk,Rect.blkA,Matrix.one_apply]
      ring
    · have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Subtype.ext h)
      simp [Rect.FullN,Rect.Blk,Rect.blkA,Matrix.one_apply,hab,hne]
  · have hy : G.ys b ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ b
    have hne : (a : ℕ) ≠ G.ys b := by
      intro h
      exact Finset.disjoint_left.mp G.disjCY a.property (h.symm ▸ hy)
    simp only [Matrix.of_apply,rowField_inl,colField_inr]
    rw [loewnerEntry_nat]
    simp [hne,Rect.FullN,Rect.Blk,Rect.blkB]
  · have hx : G.xs a ∈ G.X' := Finset.orderEmbOfFin_mem _ _ a
    have hne : G.xs a ≠ (b : ℕ) := by
      intro h
      exact Finset.disjoint_left.mp G.disjCX b.property (h ▸ hx)
    simp only [Matrix.of_apply,rowField_inr,colField_inl]
    rw [loewnerEntry_nat]
    simp [hne,Rect.FullN,Rect.Blk,Rect.blkC]
  · have hx : G.xs a ∈ G.X' := Finset.orderEmbOfFin_mem _ _ a
    have hy : G.ys b ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ b
    have hne : G.xs a ≠ G.ys b := by
      intro h
      exact Finset.disjoint_left.mp G.disjXY hx (h.symm ▸ hy)
    simp only [Matrix.of_apply,rowField_inr,colField_inr]
    rw [loewnerEntry_nat]
    simp [hne,Rect.FullN,Rect.Blk,Rect.blkD]

end CatalanCore.Uniform.NVAdapter




