module

public import CatalanCore.Arith.Hybrid.LemmaE.BlockProjection

@[expose] public section

/-! # Cleared partners of a projected primitive model -/
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {R : Type*} [CommRing R] {I Z S : Type*}
  [Fintype I] [DecidableEq I] [DecidableEq S]

def modelRow (r : I → S) (z : Z → S) (Q : Matrix I I R) (C2 : Matrix Z I R) : Matrix Z I R :=
  blockRect z r C2 * Q.adjugate

def modelCol (r : I → S) (z : Z → S) (Q : Matrix I I R) (B2 : Matrix I Z R) : Matrix I Z R :=
  Q.adjugate * blockRect r z B2

lemma modelRow_mul (r : I → S) (z : Z → S) (Q : Matrix I I R) (C2 : Matrix Z I R) :
    modelRow r z Q C2 * Q = Q.det • blockRect z r C2 := by
  rw [modelRow, Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one]

lemma mul_modelCol (r : I → S) (z : Z → S) (Q : Matrix I I R) (B2 : Matrix I Z R) :
    Q * modelCol r z Q B2 = Q.det • blockRect r z B2 := by
  rw [modelCol, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]

/-- Model row partners commute with reindexing of core and zone coordinates. -/
lemma modelRow_submatrix {I' Z' : Type*} [Fintype I'] [DecidableEq I']
    (r : I → S) (z : Z → S) (Q : Matrix I I R) (C2 : Matrix Z I R)
    (e : I' ≃ I) (f : Z' → Z) :
    (modelRow r z Q C2).submatrix f e =
      modelRow (r ∘ e) (z ∘ f) (Q.submatrix e e) (C2.submatrix f e) := by
  simp only [modelRow, Matrix.adjugate_submatrix_equiv_self]
  rw [← Matrix.submatrix_mul_equiv _ _ f e e]
  rfl

lemma modelCol_submatrix {I' Z' : Type*} [Fintype I'] [DecidableEq I']
    (r : I → S) (z : Z → S) (Q : Matrix I I R) (B2 : Matrix I Z R)
    (e : I' ≃ I) (f : Z' → Z) :
    (modelCol r z Q B2).submatrix e f =
      modelCol (r ∘ e) (z ∘ f) (Q.submatrix e e) (B2.submatrix e f) := by
  simp only [modelCol, Matrix.adjugate_submatrix_equiv_self]
  rw [← Matrix.submatrix_mul_equiv _ _ e e f]
  rfl

section Domain
variable [IsDomain R]
lemma modelRow_support (r : I → S) (z : Z → S) (Q : Matrix I I R) (C2 : Matrix Z I R)
    (hd : Q.det ≠ 0) (hQ : ∀ i j, r i ≠ r j → Q i j = 0) :
    ∀ a i, z a ≠ r i → modelRow r z Q C2 a i = 0 :=
  mul_label_support z r r _ _ (fun _ _ h => blockRect_zero z r C2 h)
    (adjugate_label_support r Q hd hQ)

lemma modelCol_support (r : I → S) (z : Z → S) (Q : Matrix I I R) (B2 : Matrix I Z R)
    (hd : Q.det ≠ 0) (hQ : ∀ i j, r i ≠ r j → Q i j = 0) :
    ∀ i a, r i ≠ z a → modelCol r z Q B2 i a = 0 :=
  mul_label_support r r z _ _ (adjugate_label_support r Q hd hQ)
    (fun _ _ h => blockRect_zero r z B2 h)
end Domain

section Integral
variable {p : ℕ} [Fact p.Prime]
lemma blockRect_int1 (r : I → S) (z : Z → S) (M : Matrix Z I ℚ[X])
    (hM : ∀ a i, Int1 p (M a i)) : ∀ a i, Int1 p (blockRect z r M a i) := by
  intro a i
  change Int1 p (if z a=r i then M a i else 0)
  split_ifs
  · exact hM a i
  · exact Int1.zero

lemma matrix_mul_int1 {J L : Type} [Fintype J]
    (M : Matrix I J ℚ[X]) (N : Matrix J L ℚ[X])
    (hM : ∀ i j, Int1 p (M i j)) (hN : ∀ j l, Int1 p (N j l)) :
    ∀ i l, Int1 p ((M*N) i l) := by
  intro i l
  rw [Matrix.mul_apply]
  exact Int1.sum (fun j _ => (hM i j).mul (hN j l))

lemma modelRow_int1 (r : I → S) (z : Z → S) (Q : Matrix I I ℚ[X]) (C2 : Matrix Z I ℚ[X])
    (hQ : ∀ i j, Int1 p (Q i j)) (hC : ∀ a i, Int1 p (C2 a i)) :
    ∀ a i, Int1 p (modelRow r z Q C2 a i) := by
  intro a i
  change Int1 p (∑ j, blockRect z r C2 a j * Q.adjugate j i)
  exact Int1.sum (fun j _ => (blockRect_int1 r z C2 hC a j).mul (adj_int1 hQ j i))

lemma modelCol_int1 (r : I → S) (z : Z → S) (Q : Matrix I I ℚ[X]) (B2 : Matrix I Z ℚ[X])
    (hQ : ∀ i j, Int1 p (Q i j)) (hB : ∀ i a, Int1 p (B2 i a)) :
    ∀ i a, Int1 p (modelCol r z Q B2 i a) := by
  intro i a
  change Int1 p (∑ j, Q.adjugate i j * blockRect r z B2 j a)
  apply Int1.sum
  intro j _
  apply (adj_int1 hQ i j).mul
  change Int1 p (if r j=z a then B2 j a else 0)
  split_ifs
  · exact hB j a
  · exact Int1.zero
end Integral
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.modelRow_support
#print axioms CatalanCore.Arith.Hybrid.LemmaE.modelCol_int1
