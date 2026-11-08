module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/Trimmed130Support.lean
Original SHA256: 1a668dbbeb94f2575646908e3b184974c8411b393ba9dec42c8afc3e88199ce3
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.Trimmed130BranchData
public import OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal
public import CatalanMeasure.GenD.Signed.Davis.ResidualDomain

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Set OAI.InternalCatalan CatalanMeasure.Improvement.Fields

theorem realCoordinateInv_strictMonoOn :
    StrictMonoOn realCoordinateInv (Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  apply sub_pos.mp
  rw [realCoordinateInv_sub]
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hxy)) (energy_one_sub_mul_pos hy hx))
    (mul_pos (realCoordinateInv_denominator_pos y) (realCoordinateInv_denominator_pos x))

theorem le_of_realCoordinateInv_le {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (h : realCoordinateInv x ≤ realCoordinateInv y) : x ≤ y := by
  by_contra hn
  have hh := realCoordinateInv_strictMonoOn hy hx (lt_of_not_ge hn)
  exact (not_lt_of_ge h) hh

theorem coordinate_mem_trimmedSupport {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hs : allowedT t) :
    trimmedResidualSupport (realCoordinate t) := by
  have hx := realCoordinate_mem ht
  have hi := realCoordinate_right_inverse ht
  have houter : realCoordinateInv (-2409 / 2500) = (outerLeft : ℝ) := by
    norm_num [realCoordinateInv, outerLeft]
  have hleft : realCoordinateInv (-19501 / 100000) = (innerLeft : ℝ) := by
    norm_num [realCoordinateInv, innerLeft]
  have hright : realCoordinateInv (98749 / 1000000) = (innerRight : ℝ) := by
    norm_num [realCoordinateInv, innerRight]
  rcases hs with hl | hr
  · apply Or.inl
    constructor
    · apply le_of_realCoordinateInv_le (by norm_num) hx
      rw [houter, hi]
      exact hl.1
    · apply le_of_realCoordinateInv_le hx (by norm_num)
      rw [hi, hleft]
      exact hl.2
  · apply Or.inr
    constructor
    · apply le_of_realCoordinateInv_le (by norm_num) hx
      rw [hright, hi]
      exact hr.1
    · exact hx.2.le

end CatalanMeasure.Refinement.Trimmed130

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.Trimmed130.realCoordinateInv_strictMonoOn
#print axioms CatalanMeasure.Refinement.Trimmed130.le_of_realCoordinateInv_le
#print axioms CatalanMeasure.Refinement.Trimmed130.coordinate_mem_trimmedSupport
