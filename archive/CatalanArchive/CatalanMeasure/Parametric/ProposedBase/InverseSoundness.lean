module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.Definitions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Matrix Finset
noncomputable section

theorem inverse_of_int_checks {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j,(∑ k,A i k*B k j)%1009=if i=j then (1:ℤ) else 0) :
    Matrix.of (fun i j =>(A i j:ZMod 1009))*
      Matrix.of (fun i j =>(B i j:ZMod 1009))=1 := by
  ext i j
  have hh := congrArg (fun z:ℤ =>(z:ZMod 1009)) (h i j)
  have hc : (((∑ k,A i k*B k j)%1009:ℤ):ZMod 1009) =
      ((∑ k,A i k*B k j:ℤ):ZMod 1009) := by
    simpa only [Nat.cast_ofNat] using ZMod.intCast_mod (∑ k,A i k*B k j) 1009
  rw [hc] at hh
  simpa [Int.cast_sum,Int.cast_mul,Matrix.mul_apply,Matrix.one_apply] using hh

end
end CatalanMeasure.Parametric.ProposedBase
