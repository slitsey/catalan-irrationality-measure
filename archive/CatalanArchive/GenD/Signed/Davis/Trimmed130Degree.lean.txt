module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/Trimmed130Degree.lean
Original SHA256: 4e9c9c1fb47a99940540a73d1f28031a72c18a2e0aed7f6edd9e5c2604860107
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Data
public import CatalanMeasure.GenD.Signed.Davis.PolynomialData

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial

def leadingCoefficient : ℚ := coefficientAt powerCoefficients 130

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem powerCoefficients_length : powerCoefficients.length = 131 := by decide +kernel

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem leadingCoefficient_pos : 0 < leadingCoefficient := by decide +kernel

theorem leadingCoefficient_ne_zero : leadingCoefficient ≠ 0 := leadingCoefficient_pos.ne'

theorem rationalP_natDegree : rationalP.natDegree = 130 := by
  apply polynomialFromCoeffs_natDegree_eq powerCoefficients 130
  · rw [powerCoefficients_length]
  · exact leadingCoefficient_ne_zero

theorem rationalP_leadingCoeff : rationalP.leadingCoeff = leadingCoefficient := by
  apply polynomialFromCoeffs_leadingCoeff powerCoefficients 130
  · rw [powerCoefficients_length]
  · exact leadingCoefficient_ne_zero

theorem realP_natDegree : realP.natDegree = 130 := by
  rw [realP, Polynomial.natDegree_map, rationalP_natDegree]

theorem realP_leadingCoeff : realP.leadingCoeff = (leadingCoefficient : ℝ) := by
  rw [realP, Polynomial.leadingCoeff_map, rationalP_leadingCoeff]
  rfl

theorem realP_ne_zero : realP ≠ 0 := by
  intro h
  have hh := congrArg Polynomial.natDegree h
  rw [realP_natDegree, natDegree_zero] at hh
  norm_num at hh

theorem realP_eval_rational (x : ℚ) :
    realP.eval (x : ℝ) = (rationalHorner powerCoefficients x : ℝ) :=
  polynomialFromCoeffs_eval_map_real powerCoefficients x

end CatalanMeasure.Refinement.Trimmed130

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.Trimmed130.leadingCoefficient
#print axioms CatalanMeasure.Refinement.Trimmed130.powerCoefficients_length
#print axioms CatalanMeasure.Refinement.Trimmed130.leadingCoefficient_pos
#print axioms CatalanMeasure.Refinement.Trimmed130.leadingCoefficient_ne_zero
#print axioms CatalanMeasure.Refinement.Trimmed130.rationalP_natDegree
#print axioms CatalanMeasure.Refinement.Trimmed130.rationalP_leadingCoeff
#print axioms CatalanMeasure.Refinement.Trimmed130.realP_natDegree
#print axioms CatalanMeasure.Refinement.Trimmed130.realP_leadingCoeff
#print axioms CatalanMeasure.Refinement.Trimmed130.realP_ne_zero
#print axioms CatalanMeasure.Refinement.Trimmed130.realP_eval_rational
