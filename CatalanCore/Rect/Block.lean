module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

/-!
# Block determinants with a variable on the common diagonal (WP-H1, pure linear algebra)

For `A : ι × ι`, `B : ι × κ`, `C : κ × ι`, `D : κ × κ` put
`Blk A B C D x = fromBlocks (A + x • 1) B C D`.  This is the shape of the hybrid matrix
`Full(X)`: the variable sits only on the diagonal of the `ι`-block (the common nodes).

* `det_blk_schur`      : `det Blk = det D * det (x • 1 + (A - B D⁻¹ C))` when `det D` is a unit.
* `det_add_scalar_expansion'` : principal-minor expansion `det (T + t • 1)` (any fintype index).
* `det_blk_expansion`  : `det Blk (x + t) = ∑_{S ⊆ ι} t^{|ι|-|S|} det Blk_S x` over a field,
  where `Blk_S` keeps only the rows/columns `S` of the `ι`-block (`D` unconditional).
-/

open Finset Matrix

namespace CatalanCore.Rect

section Blk

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {R : Type*} [CommRing R]

/-- `fromBlocks (A + x • 1) B C D`. -/
def Blk (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D : Matrix κ κ R) (x : R) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Matrix.fromBlocks (A + x • 1) B C D

/-- Schur step: with `D` invertible, `det Blk = det D * det (x • 1 + (A - B D⁻¹ C))`. -/
theorem det_blk_schur (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) (hD : IsUnit D.det) (x : R) :
    (Blk A B C D x).det = D.det * (x • (1 : Matrix ι ι R) + (A - B * D⁻¹ * C)).det := by
  have : Invertible D := Matrix.invertibleOfIsUnitDet D hD
  rw [Blk, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  abel

end Blk

section Expansion

variable {n : Type} [Fintype n] [DecidableEq n]
  {R : Type*} [CommRing R] [Nontrivial R]

/-- `det (T + t I) = ∑_S t^{|n|-|S|} det T[S]` (all principal minors). -/
theorem det_add_scalar_expansion' (T : Matrix n n R) (t : R) :
    (T + t • (1 : Matrix n n R)).det
      = ∑ S ∈ (univ : Finset n).powerset, t ^ (Fintype.card n - S.card) *
          (T.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det := by
  have h1 : (T + t • (1 : Matrix n n R)).det = (-T).charpoly.eval t := by
    rw [Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    simp [sub_neg_eq_add, add_comm]
  rw [h1, Polynomial.eval_eq_sum_range, Finset.sum_powerset]
  have hnd : (-T).charpoly.natDegree = Fintype.card n := by
    simp
  rw [hnd, ← Finset.sum_range_reflect]
  simp only [Finset.card_univ]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ Fintype.card n := by have := Finset.mem_range.1 hk; omega
  have e : Fintype.card n + 1 - 1 - k = Fintype.card n - k := by omega
  rw [e]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (-T) k hk'
  have hsum : (-1 : R) ^ k * ∑ s ∈ (univ : Finset n).powersetCard k,
        ((-T).submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det
      = ∑ s ∈ (univ : Finset n).powersetCard k,
        (T.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hcard : s.card = k := (Finset.mem_powersetCard.1 hs).2
    have hn : (-T).submatrix (Subtype.val : s → n) (Subtype.val : s → n)
        = -(T.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) := by
      ext i j; simp
    rw [hn, Matrix.det_neg, Fintype.card_coe, hcard, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    simp
  have hcon : ∀ s ∈ (univ : Finset n).powersetCard k, t ^ (Fintype.card n - s.card) *
      (T.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det
      = t ^ (Fintype.card n - k) *
      (T.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det := by
    intro s hs
    rw [(Finset.mem_powersetCard.1 hs).2]
  rw [Finset.sum_congr rfl hcon, ← Finset.mul_sum, ← hsum, hc]
  ring

end Expansion

/-- `det (X • 1 + S) = charpoly (-S)`: the determinant `det (X I + S)` is a (monic) char. poly. -/
theorem det_map_C_add_X {n : Type} [Fintype n] [DecidableEq n] {K : Type*} [CommRing K]
    (S : Matrix n n K) :
    (S.map Polynomial.C + (Polynomial.X : Polynomial K) • (1 : Matrix n n (Polynomial K))).det
      = (-S).charpoly := by
  simp only [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [add_comm]

section FieldExpansion

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {K : Type*} [Field K]

/-- The block matrix restricted to the common nodes `S ⊆ ι` (rows and columns). -/
def blkRestrict {R : Type*} [CommRing R] (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) (S : Finset ι) (x : R) : Matrix (S ⊕ κ) (S ⊕ κ) R :=
  Blk (A.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι))
    (B.submatrix (Subtype.val : S → ι) id) (C.submatrix id (Subtype.val : S → ι)) D x

/-- Minor expansion of the block determinant, `det D ≠ 0` version. -/
theorem det_blk_expansion_of_ne (A : Matrix ι ι K) (B : Matrix ι κ K) (C : Matrix κ ι K)
    (D : Matrix κ κ K) (hD : D.det ≠ 0) (x t : K) :
    (Blk A B C D (x + t)).det
      = ∑ S ∈ (univ : Finset ι).powerset, t ^ (Fintype.card ι - S.card) *
          (blkRestrict A B C D S x).det := by
  have hu : IsUnit D.det := hD.isUnit
  set Sc : Matrix ι ι K := A - B * D⁻¹ * C with hSc
  have h1 : (Blk A B C D (x + t)).det
      = D.det * ((x • (1 : Matrix ι ι K) + Sc) + t • (1 : Matrix ι ι K)).det := by
    rw [det_blk_schur A B C D hu]
    congr 2
    rw [add_smul, hSc]
    abel
  rw [h1, det_add_scalar_expansion', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have h2 : (blkRestrict A B C D S x).det
      = D.det * (((x • (1 : Matrix ι ι K) + Sc)).submatrix (Subtype.val : S → ι)
          (Subtype.val : S → ι)).det := by
    rw [blkRestrict, det_blk_schur _ _ _ D hu]
    congr 2
    ext i j
    simp [Sc, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.submatrix_apply]
  rw [h2]
  ring

/-- A ring homomorphism commutes with `det`, in `Matrix.map` form. -/
theorem map_det' {R S : Type*} [CommRing R] [CommRing S] {n : Type} [Fintype n] [DecidableEq n]
    (φ : R →+* S) (M : Matrix n n R) : φ M.det = (M.map φ).det := RingHom.map_det φ M

/-- Ring homomorphisms commute with `Blk`. -/
theorem map_blk {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D : Matrix κ κ R) (x : R) :
    (Blk A B C D x).map φ = Blk (A.map φ) (B.map φ) (C.map φ) (D.map φ) (φ x) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Blk, Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply] <;>
    split_ifs <;> simp

/-- Ring homomorphisms commute with `blkRestrict`. -/
theorem map_blkRestrict {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D : Matrix κ κ R)
    (T : Finset ι) (x : R) :
    (blkRestrict A B C D T x).map φ
      = blkRestrict (A.map φ) (B.map φ) (C.map φ) (D.map φ) T (φ x) := by
  rw [blkRestrict, blkRestrict, map_blk]
  rfl

/-- **Minor expansion of the block determinant** (no hypothesis on `D`):
`det Blk (x + t) = ∑_{S ⊆ ι} t^{|ι|-|S|} det Blk_S x`. -/
theorem det_blk_expansion (A : Matrix ι ι K) (B : Matrix ι κ K) (C : Matrix κ ι K)
    (D : Matrix κ κ K) (x t : K) :
    (Blk A B C D (x + t)).det
      = ∑ S ∈ (univ : Finset ι).powerset, t ^ (Fintype.card ι - S.card) *
          (blkRestrict A B C D S x).det := by
  classical
  open Polynomial in
  -- perturb `D` by a transcendental `X` and work in the fraction field
  let D' : Matrix κ κ K[X] := D.map Polynomial.C + (Polynomial.X : K[X]) • 1
  let φ : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective K
  have hdet : D'.det ≠ 0 := by
    have : D'.det = (-D).charpoly := by
      simp only [D']
      exact det_map_C_add_X D
    rw [this]
    exact (Matrix.charpoly_monic _).ne_zero
  have hL : (D'.map φ).det ≠ 0 := by
    have h := map_det' φ D'
    rw [← h]
    exact (map_ne_zero_iff φ hφ).2 hdet
  have key := det_blk_expansion_of_ne ((A.map Polynomial.C).map φ) ((B.map Polynomial.C).map φ)
    ((C.map Polynomial.C).map φ) (D'.map φ) hL (φ (Polynomial.C x)) (φ (Polynomial.C t))
  -- pull back to `K[X]`
  have key' : (Blk (A.map Polynomial.C) (B.map Polynomial.C) (C.map Polynomial.C) D'
        (Polynomial.C x + Polynomial.C t)).det
      = ∑ S ∈ (univ : Finset ι).powerset, (Polynomial.C t) ^ (Fintype.card ι - S.card) *
          (blkRestrict (A.map Polynomial.C) (B.map Polynomial.C) (C.map Polynomial.C) D' S
            (Polynomial.C x)).det := by
    apply hφ
    rw [map_det' φ, map_blk, map_add, key, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_mul, map_pow, map_det' φ, map_blkRestrict]
  have h0 := congrArg (Polynomial.evalRingHom (0 : K)) key'
  have hA : (A.map Polynomial.C).map (Polynomial.evalRingHom (0 : K)) = A := by
    ext i j; simp
  have hB : (B.map Polynomial.C).map (Polynomial.evalRingHom (0 : K)) = B := by
    ext i j; simp
  have hC : (C.map Polynomial.C).map (Polynomial.evalRingHom (0 : K)) = C := by
    ext i j; simp
  have hD : D'.map (Polynomial.evalRingHom (0 : K)) = D := by
    ext i j; by_cases hij : i = j <;> simp [D', Matrix.one_apply, Matrix.smul_apply, hij]
  simp only [map_det' (Polynomial.evalRingHom (0 : K)), map_blk, map_sum, map_mul, map_pow,
    map_blkRestrict, hA, hB, hC, hD] at h0
  simp only [map_add, Polynomial.coe_evalRingHom, Polynomial.eval_C] at h0
  exact h0

end FieldExpansion

end CatalanCore.Rect
