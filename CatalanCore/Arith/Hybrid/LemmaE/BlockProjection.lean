module

public import CatalanCore.Arith.Hybrid.LemmaE.Rescale

@[expose] public section

/-! # Projection onto equal-label blocks

Labels need not be enumerated. Class diagonal projectors give adjugate support,
so the cleared model partners use no fraction-field inverse API.
-/
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE

section Algebra
variable {R : Type*} [CommRing R] {I J L S : Type*} [DecidableEq S]

/-- Retain an entry precisely when its row and column labels agree. -/
def blockRect (r : I → S) (c : J → S) (M : Matrix I J R) : Matrix I J R :=
  fun i j => if r i = c j then M i j else 0

abbrev blockProject (r : I → S) (M : Matrix I I R) := blockRect r r M

lemma blockRect_zero (r : I → S) (c : J → S) (M : Matrix I J R)
    {i : I} {j : J} (h : r i ≠ c j) : blockRect r c M i j = 0 := if_neg h

/-- Equal-label support is preserved by multiplication. -/
lemma mul_label_support [Fintype J] (r : I → S) (c : J → S) (d : L → S)
    (M : Matrix I J R) (N : Matrix J L R)
    (hM : ∀ i j, r i ≠ c j → M i j = 0)
    (hN : ∀ j l, c j ≠ d l → N j l = 0) :
    ∀ i l, r i ≠ d l → (M*N) i l = 0 := by
  intro i l hil
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : r i = c j
  · rw [hN j l (by intro h; exact hil (hij.trans h)), mul_zero]
  · rw [hM i j hij, zero_mul]

lemma blockRect_submatrix {I' J' : Type*} (r : I → S) (c : J → S)
    (M : Matrix I J R) (f : I' → I) (g : J' → J) :
    (blockRect r c M).submatrix f g =
      blockRect (r ∘ f) (c ∘ g) (M.submatrix f g) := rfl

variable [Fintype I] [DecidableEq I]

def classProjector (r : I → S) (s : S) : Matrix I I R :=
  Matrix.diagonal (fun i => if r i=s then 1 else 0)

lemma commute_classProjector (r : I → S) (M : Matrix I I R)
    (hM : ∀ i j, r i ≠ r j → M i j = 0) (s : S) :
    M * classProjector r s = classProjector r s * M := by
  ext i j
  simp only [classProjector, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : r i=r j
  · simp [hij, mul_comm]
  · rw [hM i j hij]; simp
end Algebra

section Adjugate
variable {R : Type*} [CommRing R] [IsDomain R] {I S : Type*}
  [Fintype I] [DecidableEq I] [DecidableEq S]

/-- Nonzero determinant gives cancellation over a domain, without assuming a unit determinant. -/
lemma mul_left_cancel_of_det_ne_zero (M : Matrix I I R) (hM : M.det ≠ 0)
    {A B : Matrix I I R} (h : M*A=M*B) : A=B := by
  have hh := congrArg (fun Z => M.adjugate * Z) h
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at hh
  apply Matrix.ext
  intro i j
  have he := congrFun (congrFun hh i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at he
  exact mul_left_cancel₀ hM he

lemma adjugate_commute_of_commute (M P : Matrix I I R) (hM : M.det ≠ 0)
    (hMP : M*P=P*M) : M.adjugate*P=P*M.adjugate := by
  apply mul_left_cancel_of_det_ne_zero M hM
  have hleft : M*(M.adjugate*P)=M.det • P := by
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
  have hright : M*(P*M.adjugate)=M.det • P := by
    rw [← Matrix.mul_assoc, hMP, Matrix.mul_assoc, Matrix.mul_adjugate,
      Matrix.mul_smul, Matrix.mul_one]
  exact hleft.trans hright.symm

/-- The adjugate of a nonsingular equal-label block matrix has the same support. -/
theorem adjugate_label_support (r : I → S) (M : Matrix I I R) (hd : M.det ≠ 0)
    (hM : ∀ i j, r i ≠ r j → M i j = 0) :
    ∀ i j, r i ≠ r j → M.adjugate i j = 0 := by
  intro i j hij
  have he := adjugate_commute_of_commute M (classProjector r (r j)) hd
    (commute_classProjector r M hM (r j))
  have hh := congrFun (congrFun he i) j
  simpa [classProjector, Matrix.mul_diagonal, Matrix.diagonal_mul, hij] using hh

end Adjugate

section Primitive
variable {p : ℕ} [Fact p.Prime] {I : Type} {S : Type*}
  [Fintype I] [DecidableEq I] [DecidableEq S]

lemma blockProject_shift (r : I → S) (M : Matrix I I ℚ) :
    blockProject r (M.map C + (X : ℚ[X]) • 1) =
      (blockProject r M).map C + (X : ℚ[X]) • 1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : r i=r j
  · simp [blockRect, hij]
  · have hne : i≠j := by intro h; exact hij (congrArg r h)
    simp [blockRect, hij, hne, Matrix.one_apply]

/-- The projected constant-plus-variable model is automatically primitive. -/
theorem prim_blockProject_shift (r : I → S) (M : Matrix I I ℚ)
    (hM : ∀ i j, M i j ∈ CatalanCore.Basic.LocRing p) :
    gn p (blockProject r (M.map C + (X : ℚ[X]) • 1)).det = 1 := by
  have hI : ∀ i j, blockProject r M i j ∈ CatalanCore.Basic.LocRing p := by
    intro i j
    change (if r i=r j then M i j else 0) ∈ CatalanCore.Basic.LocRing p
    split_ifs
    · exact hM i j
    · exact (CatalanCore.Basic.LocRing p).zero_mem
  rw [blockProject_shift r M]
  exact prim_det_shift (p := p) (blockProject r M) hI
end Primitive
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.adjugate_label_support
#print axioms CatalanCore.Arith.Hybrid.LemmaE.prim_blockProject_shift
