module

public import CatalanCore.Frame.Spec
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P036

@[expose] public section

namespace CatalanCore.Li2

/-- The real dilogarithm series at a rational argument. -/
noncomputable def value (z : ℚ) : ℝ :=
  ∑' k : ℕ, (z : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ^ 2

/-- Tang's normalized Hankel polynomial family, at its original scale n. -/
noncomputable def li2Family (z : ℚ) : PolyFamily where
  const := value z
  ι := ℕ
  deg := fun n => 2 * n
  Adm := fun n => 1 ≤ n
  Q := Port.Unified.ParameterFamily.Qtilde z

/-- The asymptotic scale is independent of the polynomial degree bound. -/
def scale (n : ℕ) : ℕ := n

/-- The primitive integer family used by the measure criterion (content exponent zero).
The raw family remains the input to LD; `P_eq_dtilde_Qtilde` supplies the scaling bridge. -/
noncomputable def primitiveFamily (z : ℚ) : PolyFamily where
  const := value z
  ι := ℕ
  deg := fun n => 2 * n
  Adm := fun n => 1 ≤ n
  Q := fun n => (Port.Unified.ParameterFamily.P z n).map (algebraMap ℤ ℚ)


open Polynomial
open Port.Unified.ParameterFamily

theorem li2Family_natDegree_le (z : ℚ) (n : ℕ) :
    ((li2Family z).Q n).natDegree ≤ (li2Family z).deg n := by
  change (C (Port.Li2.Sn n ^ (2*n) / Port.Li2.Fn n) * Q z n).natDegree ≤ 2*n
  exact (natDegree_C_mul_le _ _).trans (Q_natDegree_le z n)

theorem li2Family_entry_identity (z : ℚ) (n k : ℕ) :
    (Port.Unified.ParameterFamily.numeratorFunctional z (4 * n)
      (Port.Li2.numerator n k)).aeval (value z) =
    (Port.Unified.ParameterFamily.intercept z n k : ℝ) +
      value z * (Port.Unified.ParameterFamily.slope z n k : ℝ) := by
  rw [numeratorFunctional_entry]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  change (intercept z n k : ℝ) + value z * (Port.Unified.ParameterFamily.slope z n k : ℝ) = _
  rfl

theorem li2Family_Qtilde_identity (z : ℚ) (n : ℕ) :
    (li2Family z).evalR n (value z) =
      ((Port.Li2.Sn n ^ (2 * n) / Port.Li2.Fn n : ℚ) : ℝ) *
        ((Port.Unified.ParameterFamily.A z n).map (Rat.castHom ℝ) +
          value z • (Port.Unified.ParameterFamily.B z n).map (Rat.castHom ℝ)).det := by
  have heval : (Q z n).aeval (value z) =
      ((A z n).map (Rat.castHom ℝ) + value z • (B z n).map (Rat.castHom ℝ)).det := by
    change (aeval (value z) : ℚ[X] →ₐ[ℚ] ℝ).toRingHom
      (((X : ℚ[X]) • (B z n).map C + (A z n).map C).det) = _
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, aeval_C, aeval_X]
    change (X : ℚ[X]).aeval (value z) * (C (B z n i j)).aeval (value z) +
      (C (A z n i j)).aeval (value z) = (A z n i j : ℝ) + value z * (B z n i j : ℝ)
    simp only [aeval_X, aeval_C]
    change value z * (B z n i j : ℝ) + (A z n i j : ℝ) = _
    exact add_comm _ _
  change (Qtilde z n).aeval (value z) = _
  rw [Qtilde, map_mul, aeval_C, heval]
  rfl

end CatalanCore.Li2
#print axioms CatalanCore.Li2.li2Family_natDegree_le
#print axioms CatalanCore.Li2.li2Family_entry_identity
#print axioms CatalanCore.Li2.li2Family_Qtilde_identity
