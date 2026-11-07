module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/GeneralNodalWeights.lean
Original SHA256: b7209cba5c25f23acfb7f77fc9c802cfb802f27fdf9438cdcbdb9c4592bb663d
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Analytic.GapWeights

@[expose] public section

/-!
# Weight bounds from an arbitrary nodal polynomial family

This file separates the coefficient-functional and exponential-absorption
arguments from the special quadratic inverse-image nodes in `GapWeights`.
The hypotheses are finite-degree nodal factorization, a uniform positive
derivative bound, and a weighted circle bound. No symmetry is used.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Finset OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

theorem general_common_basis_coeff_zero (P : Parameters) (hg : P.g0 ≤ P.n0)
    (N : ℕ) {τ : Fin ((P.n0 - P.g0) * N) → ℝ}
    (hτ : Function.Injective τ) (j : Fin ((P.n0 - P.g0) * N))
    (i : ℕ) (hi : P.H N ≤ i) :
    (rowCommonFactor P N * quadBasis τ j).coeff i = 0 := by
  have hf := rowCommonFactor_natDegree_le P N
  have hb : (quadBasis τ j).natDegree ≤ (P.n0 - P.g0) * N - 1 :=
    quadBasis_natDegree_le hτ j
  have hd : (rowCommonFactor P N * quadBasis τ j).natDegree ≤
      (rowCommonFactor P N).natDegree + (quadBasis τ j).natDegree :=
    natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  have hJ : (P.n0 - P.g0) * N + P.g0 * N = P.n0 * N := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hg]
  have hpos : 0 < (P.n0 - P.g0) * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.A, Parameters.n,
    Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hi hf
  obtain ⟨t, ht⟩ : ∃ t, t = (P.n0 - P.g0) * N := ⟨_, rfl⟩
  rw [← ht] at hJ hpos
  have hb2 : (quadBasis τ j).natDegree ≤ t - 1 := by rw [ht]; exact hb
  obtain ⟨nn, hnn⟩ : ∃ nn, nn = P.n0 * N := ⟨_, rfl⟩
  rw [← hnn] at hJ hi
  omega

end
end Analytic
end CatalanMeasure.GenD

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.GenD.Analytic.general_common_basis_coeff_zero
