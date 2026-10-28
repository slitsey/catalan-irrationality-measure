module

public import CatalanCore.Uniform.Content.UFMember.SchurFam
public import CatalanCore.Rect.Full
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

/-!
# UF member package, obligations O1–O2: the scaled-gauge lift of the hybrid matrix

For the hybrid matrix `FullN Fr c xs ys X` (core `c`, border rows `xs`, border columns `ys`) the
scaled gauge is `Ψ = FullN.map (scaleU p)` (`X ↦ X/p²`).  If every Loewner value `p² Mn(a,b)` on
the (row node, column node) pairs is `p`-integral (the pole-square bound, `hint`), then

* `sLift`: `p² Ψ = Kc + diag_core(X)` with `Kc` the constant matrix of the values (O1,
  `sLift_hB`);
* the core block `Q = Kc_CC + X·1` reduces to a characteristic matrix, so `det Q` is monic modulo
  `p` and primitive (O2, `sLift_core_det`).
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanCore.Uniform.Content.UFMember

variable {p : ℕ} [Fact p.Prime] (Fr : Frame) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Row node of the hybrid matrix. -/
def rowNode (c : ι → ℕ) (xs : κ → ℕ) : ι ⊕ κ → ℕ := Sum.elim c xs

/-- Column node of the hybrid matrix. -/
def colNode (c : ι → ℕ) (ys : κ → ℕ) : ι ⊕ κ → ℕ := Sum.elim c ys

/-- The hybrid matrix as constants plus the core diagonal. -/
theorem fullN_eq_const_add (c : ι → ℕ) (xs ys : κ → ℕ) :
    FullN Fr c xs ys (X : ℚ[X]) =
      Matrix.of (fun i j => Polynomial.C (Fr.Mn (rowNode c xs i) (colNode c ys j))) +
        Matrix.fromBlocks ((X : ℚ[X]) • (1 : Matrix ι ι ℚ[X])) 0 0 0 := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, rowNode, colNode, Matrix.one_apply,
      Polynomial.algebraMap_apply, add_comm]

variable {Fr}

/-- The constant integral values `p² Mn` (O1). -/
noncomputable def sConst (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p) :=
  Matrix.of fun i j => ⟨(p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j), hint i j⟩

/-- The integral lift of `p² Ψ` in the scaled gauge. -/
noncomputable def sLift (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X] :=
  (sConst c xs ys hint).map Polynomial.C +
    Matrix.fromBlocks ((X : (LocRing p)[X]) • (1 : Matrix ι ι (LocRing p)[X])) 0 0 0

/-- **O1.** `toQ (sLift) = p² · Ψ`. -/
theorem sLift_hB (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p)
    (i j : ι ⊕ κ) :
    toQ p (sLift c xs ys hint i j) =
      Polynomial.C ((p : ℚ) ^ 2) * ((FullN Fr c xs ys (X : ℚ[X])).map (scaleU p)) i j := by
  have hp : ((p : ℚ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [fullN_eq_const_add, Matrix.map_apply]
  rcases i with a | a <;> rcases j with b | b
  · by_cases hab : a = b
    · subst hab
      simp [sLift, sConst, scaleU, toQ, mul_add, ← mul_assoc]
      rw [← Polynomial.C_eq_natCast, ← C_pow, ← C_mul, mul_inv_cancel₀ hp, C_1]
    · simp [sLift, sConst, scaleU, toQ, Matrix.one_apply, hab, ← C_mul]
  · simp [sLift, sConst, scaleU, toQ, ← C_mul]
  · simp [sLift, sConst, scaleU, toQ, ← C_mul]
  · simp [sLift, sConst, scaleU, toQ, ← C_mul]

/-- **O2.** The core block of the lift has a primitive (monic modulo `p`) determinant. -/
theorem sLift_core_det (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p) :
    phiP p (sLift c xs ys hint).toBlocks₁₁.det ≠ 0 := by
  set K0 : Matrix ι ι (ZMod p) := Matrix.of fun a b => redQ p (sConst c xs ys hint (Sum.inl a)
    (Sum.inl b))
  have hmap : (sLift c xs ys hint).toBlocks₁₁.map (Polynomial.mapRingHom (redQ p)) =
      charmatrix (-K0) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [sLift, K0, Matrix.toBlocks₁₁, charmatrix_apply, Matrix.one_apply, add_comm]
    · simp [sLift, K0, Matrix.toBlocks₁₁, charmatrix_apply, Matrix.one_apply, hab]
  have hdet : Polynomial.mapRingHom (redQ p) (sLift c xs ys hint).toBlocks₁₁.det =
      (-K0).charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]; rfl
  unfold phiP
  rw [RingHom.comp_apply, hdet, Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))]
  exact (Matrix.charpoly_monic _).ne_zero

end CatalanCore.Uniform.Content.UFMember
