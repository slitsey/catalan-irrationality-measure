module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Bordered Cauchy-Gram form and its dual (DO Lemma 2.1)

Over a field `F`, with `G : A × g`, `X Y : A × m` (columns = Cauchy columns in the application):

* `bordered z G X Y = [[z + G Gᵀ, Y], [Xᵀ, 0]]`   (the matrix `B(z)` of DO Prop 1.3),
* `gramHat G X Y = [G X]ᵀ [G Y]`                     (`Γ̂`, an `(g+m) × (g+m)` matrix),
* `dual z G X Y = z · diag(I_g, 0_m) + Γ̂`            (`D(z)`).

`bordered_det_eq_zero_iff` (Lemma 2.1, determinant form, for `z ≠ 0`): `det B(z) = 0 ↔ det D(z) = 0`;
more precisely `det B(z) = (-1)^m z^{|A|-g-m} det D(z)` (as `det`s, see `det_bordered_dual`).
-/

@[expose] public section

open Matrix

namespace CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F] {A g m : Type*}
  [Fintype A] [DecidableEq A] [Fintype g] [DecidableEq g] [Fintype m] [DecidableEq m]

/-- `B(z) = [[z + G Gᵀ, Y], [Xᵀ, 0]]`. -/
def bordered (z : F) (G : Matrix A g F) (X Y : Matrix A m F) : Matrix (A ⊕ m) (A ⊕ m) F :=
  fromBlocks (z • (1 : Matrix A A F) + G * Gᵀ) Y Xᵀ 0

/-- `Γ̂ = [G X]ᵀ [G Y]`, indexed by `g ⊕ m` (rows from `G ∪ X`, columns from `G ∪ Y`). -/
def gramHat (G : Matrix A g F) (X Y : Matrix A m F) : Matrix (g ⊕ m) (g ⊕ m) F :=
  (fromCols G X)ᵀ * fromCols G Y

/-- `E = diag(I_g, 0_m)`. -/
def Eblk (g m : Type*) [Fintype g] [DecidableEq g] [Fintype m] [DecidableEq m] (F : Type*)
    [Field F] : Matrix (g ⊕ m) (g ⊕ m) F :=
  fromBlocks 1 0 0 0

/-- `D(z) = z E + Γ̂`. -/
def dual (z : F) (G : Matrix A g F) (X Y : Matrix A m F) : Matrix (g ⊕ m) (g ⊕ m) F :=
  z • Eblk g m F + gramHat G X Y

omit [DecidableEq A] [Fintype g] [DecidableEq g] [Fintype m] [DecidableEq m] in
lemma gramHat_eq (G : Matrix A g F) (X Y : Matrix A m F) :
    gramHat G X Y = fromBlocks (Gᵀ * G) (Gᵀ * Y) (Xᵀ * G) (Xᵀ * Y) := by
  rw [gramHat, transpose_fromCols, fromRows_mul_fromCols]

/-- The `(A ⊕ (g ⊕ m))`-indexed matrix used to compare `B(z)` and `D(z)`. -/
def bigMat (z : F) (G : Matrix A g F) (X Y : Matrix A m F) :
    Matrix (A ⊕ (g ⊕ m)) (A ⊕ (g ⊕ m)) F :=
  fromBlocks (z • (1 : Matrix A A F)) (fromCols G Y) (fromRows Gᵀ Xᵀ)
    (fromBlocks (-1) 0 0 0)

lemma det_bigMat_dual {z : F} (hz : z ≠ 0) (G : Matrix A g F) (X Y : Matrix A m F) :
    (bigMat z G X Y).det =
      z ^ Fintype.card A * (-z⁻¹) ^ (Fintype.card g + Fintype.card m) * (dual z G X Y).det := by
  have hinv : Invertible (z • (1 : Matrix A A F)) :=
    ⟨z⁻¹ • 1, by simp [smul_smul, hz], by simp [smul_smul, hz]⟩
  rw [bigMat, det_fromBlocks₁₁]
  have hi : ⅟(z • (1 : Matrix A A F)) = z⁻¹ • 1 := by
    apply invOf_eq_right_inv
    simp [smul_smul, hz]
  rw [hi, det_smul, det_one, mul_one]
  have hS : fromBlocks (-1 : Matrix g g F) 0 0 0 - fromRows Gᵀ Xᵀ * (z⁻¹ • (1 : Matrix A A F)) *
      fromCols G Y = (-z⁻¹) • dual z G X Y := by
    rw [dual, gramHat_eq, Eblk, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      fromRows_mul_fromCols]
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, Matrix.smul_apply, hz, mul_add, sub_eq_add_neg, mul_comm] <;>
      (try field_simp) <;> (try (split_ifs <;> simp))
  rw [hS, det_smul, Fintype.card_sum]
  ring

/-- Reindexing `A ⊕ (g ⊕ m) ≃ (A ⊕ m) ⊕ g`. -/
def bigEquiv (A g m : Type*) : A ⊕ (g ⊕ m) ≃ (A ⊕ m) ⊕ g where
  toFun
    | Sum.inl a => Sum.inl (Sum.inl a)
    | Sum.inr (Sum.inl i) => Sum.inr i
    | Sum.inr (Sum.inr j) => Sum.inl (Sum.inr j)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl a
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr i => Sum.inr (Sum.inl i)
  left_inv := by rintro (a | i | j) <;> rfl
  right_inv := by rintro ((a | j) | i) <;> rfl

lemma det_bigMat_bordered (z : F) (G : Matrix A g F) (X Y : Matrix A m F) :
    (bigMat z G X Y).det = (-1) ^ Fintype.card g * (bordered z G X Y).det := by
  have h : (bigMat z G X Y).submatrix (bigEquiv A g m).symm (bigEquiv A g m).symm =
      fromBlocks (fromBlocks (z • (1 : Matrix A A F)) Y Xᵀ 0) (fromRows G 0) (fromCols Gᵀ 0)
        (-1 : Matrix g g F) := by
    ext (((a | j) | i)) (((b | k) | l)) <;> simp [bigMat, bigEquiv, Matrix.one_apply]
  rw [← Matrix.det_submatrix_equiv_self (bigEquiv A g m).symm, h]
  have : Invertible (-1 : Matrix g g F) := ⟨-1, by simp, by simp⟩
  rw [det_fromBlocks₂₂]
  have hi : ⅟(-1 : Matrix g g F) = -1 := invOf_eq_right_inv (by simp)
  rw [hi]
  have e : (fromBlocks (z • (1 : Matrix A A F)) Y Xᵀ 0 : Matrix (A ⊕ m) (A ⊕ m) F) -
      fromRows G 0 * (-1 : Matrix g g F) * fromCols Gᵀ 0 = bordered z G X Y := by
    rw [bordered, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul]
    ext (a | i) (b | j) <;> simp [Matrix.mul_apply]
  rw [e, det_neg, det_one]
  simp [Matrix.det_neg]

/-- **Lemma 2.1 (determinant form).** For `z ≠ 0`:
`z^{g+m}·det B(z) = (-1)^m z^{|A|} det D(z)`. -/
lemma det_bordered_dual {z : F} (hz : z ≠ 0) (G : Matrix A g F) (X Y : Matrix A m F) :
    (-1) ^ Fintype.card g * (bordered z G X Y).det =
      z ^ Fintype.card A * (-z⁻¹) ^ (Fintype.card g + Fintype.card m) * (dual z G X Y).det := by
  rw [← det_bigMat_bordered, det_bigMat_dual hz]

/-- **Lemma 2.1.** For `z ≠ 0`, `B(z)` is singular iff `D(z)` is. -/
theorem bordered_det_eq_zero_iff {z : F} (hz : z ≠ 0) (G : Matrix A g F) (X Y : Matrix A m F) :
    (bordered z G X Y).det = 0 ↔ (dual z G X Y).det = 0 := by
  have h := det_bordered_dual hz G X Y
  have h1 : ((-1 : F) ^ Fintype.card g) ≠ 0 := pow_ne_zero _ (by simp)
  have h2 : z ^ Fintype.card A * (-z⁻¹) ^ (Fintype.card g + Fintype.card m) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hz)))
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.1 h.symm).resolve_left h2
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.1 h).resolve_left h1

omit [DecidableEq A] [Fintype A] in
lemma det_antiTri_ne_zero {n : Type*} [Fintype n] [DecidableEq n] (U V E : Matrix n n F)
    (hU : U.det ≠ 0) (hV : V.det ≠ 0) : (fromBlocks 0 U V E).det ≠ 0 := by
  have h : fromBlocks (0 : Matrix n n F) U V E =
      (fromBlocks U 0 E V).submatrix id (Equiv.sumComm n n) := by
    ext (i | i) (j | j) <;> simp
  rw [h, Matrix.det_permute' (Equiv.sumComm n n) (fromBlocks U 0 E V),
    det_fromBlocks_zero₁₂]
  have hs : ((Equiv.Perm.sign (Equiv.sumComm n n) : ℤˣ) : F) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm n n)) with h | h <;> simp [h]
  exact mul_ne_zero hs (mul_ne_zero hU hV)

/-- **Boundary value (DO §1).** If `|g| + |m| = |A|`, i.e. `e : g ⊕ m ≃ A`, and the two square
Cauchy-type determinants `det[G Y]`, `det[G X]` are nonzero, then `B(0) ≠ 0`. -/
theorem det_bordered_zero_ne_zero (G : Matrix A g F) (X Y : Matrix A m F) (e : g ⊕ m ≃ A)
    (hY : ((fromCols G Y).submatrix e id).det ≠ 0) (hX : ((fromCols G X).submatrix e id).det ≠ 0) :
    (bordered 0 G X Y).det ≠ 0 := by
  intro h0
  have hb := det_bigMat_bordered (0 : F) G X Y
  rw [h0, mul_zero] at hb
  set e' : (g ⊕ m) ⊕ (g ⊕ m) ≃ A ⊕ (g ⊕ m) := Equiv.sumCongr e (Equiv.refl _) with he'
  have h : (bigMat (0 : F) G X Y).submatrix e' e' =
      fromBlocks 0 ((fromCols G Y).submatrix e id) ((fromRows Gᵀ Xᵀ).submatrix id e)
        (fromBlocks (-1) 0 0 0) := by
    ext (i | i) (j | j) <;> simp [bigMat, he']
  have hV : ((fromRows Gᵀ Xᵀ).submatrix id e).det ≠ 0 := by
    have : (fromRows Gᵀ Xᵀ).submatrix id e = ((fromCols G X).submatrix e id)ᵀ := by
      ext i j; rcases i with i | i <;> simp [Matrix.transpose_apply]
    rw [this, det_transpose]; exact hX
  have := det_antiTri_ne_zero _ _ (fromBlocks (-1 : Matrix g g F) 0 0 0) hY hV
  rw [← h, Matrix.det_submatrix_equiv_self] at this
  exact this hb

end CatalanFrames.LambdaHybrid.NV
