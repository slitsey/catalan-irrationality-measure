module

public import CatalanCore.Uniform.Content.UFFamily.Det

@[expose] public section

/-!
# UF families: `fibZ` from LU certificates (lane H10)

`fibZ m T` (the bordered determinant of integer data) equals the determinant of the bordered
`(m+1) × (m+1)` matrix `borderedN T` (`border_det`, needs `det M ≠ 0`); with `Det.luOK_det` a pair of
triangular matrices `(LB, UB)` with `LB · borderedN T = UB` certifies the value
(`fibZ_eq_of_lu`), at `O(m³)` kernel cost instead of the `O(m!)` Laplace expansion `detN`.
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFFamily

open CatalanCore.Uniform.Content.UFWedge

/-- The bordered matrix of integer data on `ℕ` indices. -/
def borderedN {m : ℕ} (T : IntFib m) (i j : ℕ) : ℤ :=
  if i < m then (if j < m then T.Mf i j else T.uf i) else (if j < m then T.sf j else T.z)

theorem fibA_eq_det_fromBlocks {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (s u : Fin m → ℤ) (z : ℤ)
    (hM : M.det ≠ 0) :
    (Matrix.fromBlocks M (Matrix.replicateCol Unit u) (Matrix.replicateRow Unit s)
      (Matrix.of fun _ _ => z)).det = fibA M s u z := by
  set K : Matrix (Fin m ⊕ Unit) (Fin m ⊕ Unit) ℤ :=
    Matrix.fromBlocks 1 (Matrix.replicateCol Unit (-(M.adjugate *ᵥ u))) 0
      (Matrix.of fun _ _ => M.det) with hK
  have hprod : Matrix.fromBlocks M (Matrix.replicateCol Unit u) (Matrix.replicateRow Unit s)
      (Matrix.of fun _ _ => z) * K =
      Matrix.fromBlocks M 0 (Matrix.replicateRow Unit s) (Matrix.of fun _ _ => fibA M s u z) := by
    rw [hK, Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · ext i j
      have hv : M *ᵥ (M.adjugate *ᵥ u) = M.det • u := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
      have h : ∑ k, M i k * (M.adjugate *ᵥ u) k = M.det * u i := congrFun hv i
      simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.zero_apply, Pi.neg_apply,
        mul_neg, Finset.sum_neg_distrib, Matrix.of_apply, Fintype.sum_unique, Matrix.add_apply,
        Matrix.mulVec, dotProduct] at h ⊢
      linarith
    · simp
    · ext i j
      simp only [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
        Matrix.add_apply, Matrix.of_apply, Fintype.sum_unique, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, Matrix.mulVec, dotProduct, fibA, Finset.mul_sum]
      ring
  have hdK : K.det = M.det := by
    rw [hK, Matrix.det_fromBlocks_zero₂₁]
    simp
  have h1 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hdK, Matrix.det_fromBlocks_zero₁₂] at h1
  have hd : (Matrix.of fun (_ : Unit) (_ : Unit) => fibA M s u z).det = fibA M s u z := by
    simp
  rw [hd] at h1
  exact mul_right_cancel₀ hM (by rw [h1]; ring)

/-- The `(m+1) × (m+1)` bordered matrix has determinant `fibZ` (for `det M ≠ 0`). -/
theorem border_det {m : ℕ} (T : IntFib m)
    (hM : (Matrix.of fun a b : Fin m => T.Mf a b).det ≠ 0) :
    (Matrix.of fun a b : Fin (m + 1) => borderedN T a b).det = fibZ m T := by
  rw [fibZ_eq]
  rw [← fibA_eq_det_fromBlocks _ _ _ _ hM]
  let e : Fin (m + 1) ≃ Fin m ⊕ Unit := finSuccEquivLast.trans (Equiv.optionEquivSumPUnit (Fin m))
  rw [← Matrix.det_submatrix_equiv_self e.symm]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp [e, borderedN, Matrix.fromBlocks, Fin.val_castSucc, a.2, b.2]
  · simp [e, borderedN, Matrix.fromBlocks, a.2]
  · simp [e, borderedN, Matrix.fromBlocks, b.2]
  · simp [e, borderedN, Matrix.fromBlocks]

/-- **Value of `fibZ` from LU certificates** (`O(m³)` kernel cost). -/
theorem fibZ_eq_of_lu {m : ℕ} (T : IntFib m) (LM UM LB UB : ℕ → ℕ → ℤ)
    (hM : luOK m T.Mf LM UM = true) (hB : luOK (m + 1) (borderedN T) LB UB = true)
    (hU : prodN m (fun i => UM i i) ≠ 0) :
    fibZ m T * prodN (m + 1) (fun i => LB i i) = prodN (m + 1) (fun i => UB i i) := by
  have h1 := luOK_det m T.Mf LM UM hM
  have hdet : (Matrix.of fun a b : Fin m => T.Mf a b).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact hU h1.symm
  rw [← border_det T hdet]
  exact luOK_det (m + 1) (borderedN T) LB UB hB

/-- A certified value: `fibZ = a` when `a · ∏ L = ∏ U` and `∏ L ≠ 0`. -/
theorem fibZ_eq_val {m : ℕ} (T : IntFib m) (LM UM LB UB : ℕ → ℕ → ℤ) (a : ℤ)
    (hM : luOK m T.Mf LM UM = true) (hB : luOK (m + 1) (borderedN T) LB UB = true)
    (hU : prodN m (fun i => UM i i) ≠ 0) (hL : prodN (m + 1) (fun i => LB i i) ≠ 0)
    (ha : a * prodN (m + 1) (fun i => LB i i) = prodN (m + 1) (fun i => UB i i)) :
    fibZ m T = a :=
  mul_right_cancel₀ hL ((fibZ_eq_of_lu T LM UM LB UB hM hB hU).trans ha.symm)

end CatalanCore.Uniform.Content.UFFamily
