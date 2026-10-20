module
public import CatalanCore.Arith.Hybrid.LemmaE.ModelBounds
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {R : Type*} [CommRing R] [IsDomain R]
  {I Z S : Type*} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z] [DecidableEq S]
lemma blockRect_smul (r : I → S) (z : Z → S) (s : R) (C : Matrix Z I R) :
    blockRect z r (s • C)=s • blockRect z r C := by
  ext a i
  simp only [blockRect, Matrix.smul_apply]
  split_ifs <;> simp
lemma projected_row_solve (r : I → S) (z : Z → S) (s : R) (hs : s≠0)
    (A : Matrix I I R) (C : Matrix Z I R) :
    modelRow r z (blockProject r (s • A)) (s • C) * blockProject r A =
      (blockProject r (s • A)).det • blockRect z r C := by
  have H:=modelRow_mul r z (blockProject r (s • A)) (s • C)
  have HQ : blockProject r (s • A)=s • blockProject r A := blockRect_smul r r s A
  rw [HQ, Matrix.mul_smul, blockRect_smul, smul_smul] at H
  ext a i
  have hi:=congrArg (fun M=>M a i) H
  simp only [Matrix.smul_apply, smul_eq_mul] at hi ⊢
  apply mul_left_cancel₀ hs
  simpa only [HQ, mul_assoc, mul_comm, mul_left_comm] using hi
lemma projected_col_solve (r : I → S) (z : Z → S) (s : R) (hs : s≠0)
    (A : Matrix I I R) (B : Matrix I Z R) :
    blockProject r A * modelCol r z (blockProject r (s • A)) (s • B) =
      (blockProject r (s • A)).det • blockRect r z B := by
  have H:=mul_modelCol r z (blockProject r (s • A)) (s • B)
  have HQ : blockProject r (s • A)=s • blockProject r A := blockRect_smul r r s A
  rw [HQ, Matrix.smul_mul, blockRect_smul z r, smul_smul] at H
  ext i a
  have hi:=congrArg (fun M=>M i a) H
  simp only [Matrix.smul_apply, smul_eq_mul] at hi ⊢
  apply mul_left_cancel₀ hs
  simpa only [HQ, mul_assoc, mul_comm, mul_left_comm] using hi
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.projected_row_solve
