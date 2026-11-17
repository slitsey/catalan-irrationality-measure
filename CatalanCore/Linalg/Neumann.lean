module
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
open scoped BigOperators Matrix.Norms.Operator
namespace CatalanCore.Linalg

/-- A left approximate inverse proves nonsingularity from a strict row residual.
The witness C needs neither an inverse proof nor its determinant. -/
theorem det_ne_zero_of_left_residual {K ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Fintype ι] [DecidableEq ι] (A C : Matrix ι ι K)
    (h : ∀ i, (∑ j, ‖(1-C*A) i j‖)<1) : A.det≠0 := by
  letI : CompleteSpace (Matrix ι ι K) := FiniteDimensional.complete K (Matrix ι ι K)
  have hrow : ∀ i, (∑ j, ‖(1-C*A) i j‖₊)<1 := by
    intro i
    apply NNReal.coe_lt_coe.mp
    simpa only [NNReal.coe_sum,coe_nnnorm,NNReal.coe_one] using h i
  have hn : ‖(1-C*A)‖₊<1 := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.sup_lt_iff (by norm_num : (0:NNReal)<1)).2 (fun i _ => hrow i)
  have hnR : ‖(1-C*A)‖<1 := by
    simpa only [coe_nnnorm,NNReal.coe_one] using (NNReal.coe_lt_coe.mpr hn)
  have hu := isUnit_one_sub_of_norm_lt_one hnR
  have hprod : IsUnit (C*A) := by simpa only [sub_sub_cancel] using hu
  have hdet : (C*A).det≠0 := ((Matrix.isUnit_iff_isUnit_det _).mp hprod).ne_zero
  intro hz
  apply hdet
  rw [Matrix.det_mul,hz,mul_zero]

#print axioms det_ne_zero_of_left_residual
end CatalanCore.Linalg


