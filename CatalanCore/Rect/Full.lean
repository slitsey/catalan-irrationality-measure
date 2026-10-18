module

public import CatalanCore.Frame.Spec
public import CatalanCore.Rect.Block

@[expose] public section

/-!
# The hybrid matrix `Full(X)` on node families (WP-H1)

`FullN Fr c xs ys x` is the `(ι ⊕ κ)`-square Löwner matrix with
* common nodes `c : ι → ℕ` (rows and columns, the block `C`),
* row nodes `xs : κ → ℕ` (the block `X'`) and column nodes `ys : κ → ℕ` (the block `Y'`),

entries `Fr.Mn (row node) (column node)`, and the variable `x` added at the cells `(a, a)`, `a ∈ ι`.
The identification of the `i`-th row node of `X'` with the `i`-th column node of `Y'` is what makes
the determinant meaningful (it is the order-preserving identification).

**Sign convention** (fixed here).  `Frame.Mn` is the entry of `T = (1/norm) L_F`, *not* of the
kernel `Rk = -Mn` of the paper (`BI-lambda-paper` §10, `Full`).  So our `FullN … X` is the paper's
`T_t`-matrix with `X = λ + t`:
`det Full_paper(X) = (-1)^{|C|+m} det FullN(-X)`.  This agrees with `Frame.Ppoly`
(`det (X I + M)`) at `m = 0`, which is the negative control (`Geometry.fullPoly_zero`).

Main statements (all for a general `ι`, `κ`):
* `det_fullN_eq`        : `det FullN(X) = det R_{X'Y'} · schurP` (Schur step; `det R ≠ 0`);
* `schurP_monic`, `schurP_natDegree` : `schurP` is monic of degree `|ι|`;
* `det_fullN_expansion` : `det FullN(x+t) = ∑_{S ⊆ ι} t^{|ι|-|S|} det FullN_S(x)` (unconditional),
  where `FullN_S` is `FullN` for the common nodes `c ∘ (↑ : S → ι)`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Rect

variable (Fr : Frame)

section Def

variable {R : Type*} [CommRing R] [Algebra ℚ R]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The four blocks of the hybrid matrix, over `R`. -/
def blkA (c : ι → ℕ) : Matrix ι ι R := Matrix.of fun a b => algebraMap ℚ R (Fr.Mn (c a) (c b))
def blkB (c : ι → ℕ) (ys : κ → ℕ) : Matrix ι κ R :=
  Matrix.of fun a j => algebraMap ℚ R (Fr.Mn (c a) (ys j))
def blkC (c : ι → ℕ) (xs : κ → ℕ) : Matrix κ ι R :=
  Matrix.of fun i b => algebraMap ℚ R (Fr.Mn (xs i) (c b))
def blkD (xs ys : κ → ℕ) : Matrix κ κ R :=
  Matrix.of fun i j => algebraMap ℚ R (Fr.Mn (xs i) (ys j))

/-- `Full(x)`: Löwner matrix on rows `c ⊔ xs`, columns `c ⊔ ys`, with `x` at the cells `(a,a)`,
`a` a common node. -/
def FullN (c : ι → ℕ) (xs ys : κ → ℕ) (x : R) : Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Blk (blkA Fr c) (blkB Fr c ys) (blkC Fr c xs) (blkD Fr xs ys) x

end Def

section Over

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The block `R_{X'Y'}` over `ℚ`. -/
def RXY (xs ys : κ → ℕ) : Matrix κ κ ℚ := blkD (R := ℚ) Fr xs ys

/-- The Schur complement matrix `M = R_CC - R_CY' R_X'Y'⁻¹ R_X'C` over `ℚ`. -/
noncomputable def schurM (c : ι → ℕ) (xs ys : κ → ℕ) : Matrix ι ι ℚ :=
  blkA (R := ℚ) Fr c - blkB (R := ℚ) Fr c ys * (RXY Fr xs ys)⁻¹ * blkC (R := ℚ) Fr c xs

/-- `P(X) = det (X I + M)`, a polynomial over `ℚ`. -/
noncomputable def schurP (c : ι → ℕ) (xs ys : κ → ℕ) : ℚ[X] :=
  ((schurM Fr c xs ys).map Polynomial.C + (X : ℚ[X]) • (1 : Matrix ι ι ℚ[X])).det

theorem schurP_eq_charpoly (c : ι → ℕ) (xs ys : κ → ℕ) :
    schurP Fr c xs ys = (-schurM Fr c xs ys).charpoly :=
  det_map_C_add_X _

theorem schurP_monic (c : ι → ℕ) (xs ys : κ → ℕ) : (schurP Fr c xs ys).Monic := by
  rw [schurP_eq_charpoly]; exact Matrix.charpoly_monic _

theorem schurP_natDegree (c : ι → ℕ) (xs ys : κ → ℕ) :
    (schurP Fr c xs ys).natDegree = Fintype.card ι := by
  rw [schurP_eq_charpoly]; simpa using (-schurM Fr c xs ys).charpoly_natDegree_eq_dim

/-- `Algebra.map` into `ℚ[X]` is `C`. -/
theorem blk_map_C (c : ι → ℕ) (xs ys : κ → ℕ) :
    FullN Fr c xs ys (X : ℚ[X])
      = Blk ((blkA (R := ℚ) Fr c : Matrix ι ι ℚ).map Polynomial.C) ((blkB (R := ℚ) Fr c ys : Matrix ι κ ℚ).map C)
          ((blkC (R := ℚ) Fr c xs : Matrix κ ι ℚ).map C) ((RXY Fr xs ys).map C) X := by
  rfl

/-- **Schur step.**  If `det R_{X'Y'} ≠ 0` then `det Full(X) = det R_{X'Y'} · P(X)`
(equality in `ℚ[X]`); in particular `Full(X)` has degree `|ι|` with leading coefficient
`det R_{X'Y'}`.  (`Qt = den · det Full(X)` is therefore a nonzero multiple of the monic `P`.) -/
theorem det_fullN_eq (c : ι → ℕ) (xs ys : κ → ℕ) (hD : (RXY Fr xs ys).det ≠ 0) :
    (FullN Fr c xs ys (X : ℚ[X])).det = Polynomial.C (RXY Fr xs ys).det * schurP Fr c xs ys := by
  have hu : IsUnit ((RXY Fr xs ys).map (Polynomial.C : ℚ →+* ℚ[X])).det := by
    rw [← map_det' (Polynomial.C : ℚ →+* ℚ[X])]
    exact Polynomial.isUnit_C.2 hD.isUnit
  rw [blk_map_C, det_blk_schur _ _ _ _ hu, ← map_det' (Polynomial.C : ℚ →+* ℚ[X])]
  have hinv : ((RXY Fr xs ys).map (Polynomial.C : ℚ →+* ℚ[X]))⁻¹
      = ((RXY Fr xs ys)⁻¹).map (Polynomial.C : ℚ →+* ℚ[X]) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hD.isUnit, Matrix.map_one _ (map_zero _)
      (map_one _)]
  rw [hinv, schurP, schurM]
  congr 2
  rw [add_comm]
  simp [Matrix.map_sub, Matrix.map_mul]

/-- Evaluation of the Schur identity in a `ℚ`-algebra field. -/
theorem map_fullN {K : Type*} [Field K] [Algebra ℚ K] (c : ι → ℕ) (xs ys : κ → ℕ) (x : K) :
    (FullN Fr c xs ys (X : ℚ[X])).map (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] K)
      = FullN Fr c xs ys x := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem det_fullN_eq_aeval {K : Type*} [Field K] [Algebra ℚ K] (c : ι → ℕ) (xs ys : κ → ℕ)
    (hD : (RXY Fr xs ys).det ≠ 0) (x : K) :
    (FullN Fr c xs ys x).det
      = algebraMap ℚ K (RXY Fr xs ys).det * Polynomial.aeval x (schurP Fr c xs ys) := by
  rw [← map_fullN Fr c xs ys x]
  have h2 : (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] K) (FullN Fr c xs ys (X : ℚ[X])).det
      = ((FullN Fr c xs ys (X : ℚ[X])).map (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] K)).det :=
    map_det' (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] K).toRingHom _
  rw [← h2, det_fullN_eq Fr c xs ys hD]
  simp

/-- **Minor expansion** (unconditional): with `t` added only at the common diagonal,
`det Full(x+t) = ∑_{S ⊆ ι} t^{|ι|-|S|} det Full_S(x)`, `Full_S` = rows `S ∪ X'`, columns `S ∪ Y'`. -/
theorem det_fullN_expansion {K : Type*} [Field K] [Algebra ℚ K] (c : ι → ℕ) (xs ys : κ → ℕ)
    (x t : K) :
    (FullN Fr c xs ys (x + t)).det
      = ∑ S ∈ (univ : Finset ι).powerset, t ^ (Fintype.card ι - S.card) *
          (FullN Fr (fun a : S => c a.1) xs ys x).det := by
  have h := det_blk_expansion (blkA Fr c : Matrix ι ι K) (blkB Fr c ys) (blkC Fr c xs)
    (blkD Fr xs ys) x t
  unfold FullN
  rw [h]
  exact Finset.sum_congr rfl (fun S _ => rfl)

end Over

end CatalanCore.Rect
