module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Rank bookkeeping over a field

Small, generic rank lemmas used by the rank-principle deficits (Theorems B and C5):
`rank_add_le'`, `rank_sum_vecMulVec_le` (a sum of `d` rank-one matrices has rank `≤ d`),
`rank_fromBlocks_diag_le` and `rank_fromBlocks_schur_le` (an invertible block costs its size).
-/

open Matrix

namespace CatalanCore.Linalg

section Field

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

lemma rank_add_le' (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine Submodule.mem_sup.2 ⟨A.mulVecLin x, ⟨x, rfl⟩, B.mulVecLin x, ⟨x, rfl⟩, ?_⟩
    simp []
  exact (Submodule.finrank_mono this).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix m n K) (c : ι → ℕ)
    (h : ∀ i ∈ s, (f i).rank ≤ c i) : (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' _ _).trans (add_le_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma rank_sum_vecMulVec_le {ι : Type*} [DecidableEq n] (s : Finset ι) (a : ι → m → K)
    (b : ι → n → K) : (∑ i ∈ s, Matrix.vecMulVec (a i) (b i)).rank ≤ s.card := by
  have := rank_sum_le s (fun i => Matrix.vecMulVec (a i) (b i)) (fun _ => 1)
    (fun i _ => Matrix.rank_vecMulVec_le _ _)
  simpa using this

end Field

section Blocks

variable {K : Type*} [Field K] {l m n q : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype q]
  [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq q]

/-- `fromBlocks S 0 0 0` has the rank of `S`. -/
lemma rank_fromBlocks_corner_le (S : Matrix l m K) :
    (fromBlocks S (0 : Matrix l n K) (0 : Matrix q m K) (0 : Matrix q n K)).rank ≤ S.rank := by
  let Pl : Matrix (l ⊕ q) l K := Matrix.of fun a b =>
    Sum.elim (fun i => (1 : Matrix l l K) i b) (fun _ => (0 : K)) a
  let Pm : Matrix m (m ⊕ n) K := Matrix.of fun a b =>
    Sum.elim (fun j => (1 : Matrix m m K) a j) (fun _ => (0 : K)) b
  have : fromBlocks S (0 : Matrix l n K) (0 : Matrix q m K) (0 : Matrix q n K) = Pl * S * Pm := by
    ext (i | i) (j | j) <;> simp [Pl, Pm, Matrix.mul_apply, Matrix.one_apply, Matrix.fromBlocks]
  rw [this]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- A block-diagonal matrix: the rank is at most `rank S` plus the number of rows of `D`. -/
lemma rank_fromBlocks_diag_le (S : Matrix l m K) (D : Matrix q n K) :
    (fromBlocks S (0 : Matrix l n K) (0 : Matrix q m K) D).rank ≤ S.rank + Fintype.card q := by
  have h : fromBlocks S (0 : Matrix l n K) (0 : Matrix q m K) D =
      fromBlocks S 0 0 0 + fromBlocks (0 : Matrix l m K) 0 0 D := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks]
  rw [h]
  refine (rank_add_le' _ _).trans (add_le_add (rank_fromBlocks_corner_le S) ?_)
  have := rank_le_card_of_support_subset (fromBlocks (0 : Matrix l m K) 0 0 D)
    (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩) (by
      intro i hi
      rcases i with i | i
      · exfalso; apply hi; ext j; rcases j with j | j <;> simp [Matrix.row, Matrix.fromBlocks]
      · simp)
  simpa using this

/-- Schur complement bound: an invertible block of size `|q|` costs at most `|q|`. -/
lemma rank_fromBlocks_schur_le (A : Matrix l m K) (B : Matrix l q K) (C : Matrix q m K)
    (D : Matrix q q K) [Invertible D] :
    (fromBlocks A B C D).rank ≤ (A - B * ⅟D * C).rank + Fintype.card q := by
  rw [fromBlocks_eq_of_invertible₂₂ A B C D]
  refine (rank_mul_le_left _ _).trans ?_
  refine (rank_mul_le_right _ _).trans ?_
  exact rank_fromBlocks_diag_le _ _

end Blocks

end CatalanCore.Linalg
