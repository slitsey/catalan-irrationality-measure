module

public import CatalanFrames.LambdaHybrid.NV.Bordered
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# The Schur step of DO Proposition 1.3 (pure algebra)

Index types: `A` (low nodes `a < K`), `c` (the high nodes in `C`), `m` (the borders `X'`, `Y'`).
The reduced matrix (after scaling the high rows/columns by `ℓ`) is
`Zmat = [[X - Aa, -¼Wc, -¼Wy], [-¼Wcᵀ, -I, 0], [-¼Wxᵀ, 0, 0]]` on `(A ⊕ c) ⊕ m`.

Hypothesis `16 Aa = Wc Wcᵀ + G Gᵀ + Wx Wxᵀ + Wy Wyᵀ + h` (Lemma 1.2 with `W_all` split along
`C_high ⊔ absent ⊔ X' ⊔ Y'`) gives
`det Zmat = (-1)^{|c|+|m|} (-16)^{-|A|} det B(h - 16 X)`
with `B = bordered (h - 16 X) G Wx Wy`.
-/

@[expose] public section

open Matrix

namespace CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F] {A c m g : Type*}
  [Fintype A] [DecidableEq A] [Fintype c] [DecidableEq c] [Fintype m] [DecidableEq m]
  [Fintype g] [DecidableEq g]

/-- The reduced matrix on `(A ⊕ c) ⊕ m`. -/
def Zmat (x : F) (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) :
    Matrix ((A ⊕ c) ⊕ m) ((A ⊕ c) ⊕ m) F :=
  fromBlocks (fromBlocks (x • (1 : Matrix A A F) - Aa) ((-(1 / 4 : F)) • Wc)
      ((-(1 / 4 : F)) • Wcᵀ) (-1))
    (fromRows ((-(1 / 4 : F)) • Wy) 0) (fromCols ((-(1 / 4 : F)) • Wxᵀ) 0) 0

/-- Reindexing `(A ⊕ c) ⊕ m ≃ (A ⊕ m) ⊕ c`. -/
def zEquiv (A c m : Type*) : (A ⊕ c) ⊕ m ≃ (A ⊕ m) ⊕ c where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr j) => Sum.inr j
    | Sum.inr i => Sum.inl (Sum.inr i)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr i) => Sum.inr i
    | Sum.inr j => Sum.inl (Sum.inr j)
  left_inv := by rintro ((a | j) | i) <;> rfl
  right_inv := by rintro ((a | i) | j) <;> rfl

theorem det_Zmat (h2 : (2 : F) ≠ 0) (x h : F) (Aa : Matrix A A F) (Wc : Matrix A c F)
    (Wx Wy : Matrix A m F) (G : Matrix A g F)
    (hA : (16 : F) • Aa = Wc * Wcᵀ + G * Gᵀ + Wx * Wxᵀ + Wy * Wyᵀ + h • 1) :
    (Zmat x Aa Wc Wx Wy).det =
      (-1) ^ (Fintype.card c + Fintype.card m) * ((-16 : F) ^ Fintype.card A)⁻¹ *
        (bordered (h - 16 * x) G Wx Wy).det := by
  have h16 : (16 : F) ≠ 0 := by
    have : (16 : F) = 2 * 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hAa : Aa = (1 / 16 : F) • (Wc * Wcᵀ + G * Gᵀ + Wx * Wxᵀ + Wy * Wyᵀ + h • 1) := by
    rw [← hA, smul_smul]; simp [h16]
  -- step 1: reindex
  rw [← Matrix.det_submatrix_equiv_self (zEquiv A c m).symm]
  have hZ : (Zmat x Aa Wc Wx Wy).submatrix (zEquiv A c m).symm (zEquiv A c m).symm =
      fromBlocks (fromBlocks (x • (1 : Matrix A A F) - Aa) ((-(1 / 4 : F)) • Wy)
        ((-(1 / 4 : F)) • Wxᵀ) 0)
        (fromRows ((-(1 / 4 : F)) • Wc) 0) (fromCols ((-(1 / 4 : F)) • Wcᵀ) 0) (-1) := by
    ext ((a | i) | j) ((b | k) | l) <;> simp [Zmat, zEquiv]
  rw [hZ]
  have : Invertible (-1 : Matrix c c F) := ⟨-1, by simp, by simp⟩
  rw [det_fromBlocks₂₂]
  have hi : ⅟(-1 : Matrix c c F) = -1 := invOf_eq_right_inv (by simp)
  rw [hi]
  have hUV : fromRows ((-(1 / 4 : F)) • Wc) 0 * (-1 : Matrix c c F) *
      fromCols ((-(1 / 4 : F)) • Wcᵀ) 0 =
      fromBlocks (-((1 / 16 : F) • (Wc * Wcᵀ))) (0 : Matrix A m F) (0 : Matrix m A F)
        (0 : Matrix m m F) := by
    have this : (-(1 / 4 : F)) * (-(1 / 4 : F)) = 1 / 16 := by field_simp; norm_num
    rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, fromRows_mul_fromCols]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, this]
    ext (i | i) (j | j) <;> simp
  rw [hUV]
  set Y : F := h - 16 * x with hY
  have hS : fromBlocks (x • (1 : Matrix A A F) - Aa) ((-(1 / 4 : F)) • Wy)
        ((-(1 / 4 : F)) • Wxᵀ) 0 - fromBlocks (-((1 / 16 : F) • (Wc * Wcᵀ))) (0 : Matrix A m F)
        (0 : Matrix m A F) (0 : Matrix m m F) =
      fromBlocks (x • (1 : Matrix A A F) - Aa + (1 / 16 : F) • (Wc * Wcᵀ)) ((-(1 / 4 : F)) • Wy)
        ((-(1 / 4 : F)) • Wxᵀ) 0 := by
    ext (i | i) (j | j) <;> simp
  have hmain : fromBlocks (x • (1 : Matrix A A F) - Aa + (1 / 16 : F) • (Wc * Wcᵀ))
        ((-(1 / 4 : F)) • Wy) ((-(1 / 4 : F)) • Wxᵀ) 0 =
      fromBlocks (1 : Matrix A A F) ((1 / 4 : F) • Wx) (0 : Matrix m A F) (1 : Matrix m m F) *
        (fromBlocks (((-(1 / 16 : F)) • (1 : Matrix A A F))) 0 0 ((-(1 / 4 : F)) • (1 : Matrix m m F))
          * bordered Y G Wx Wy *
          fromBlocks (1 : Matrix A A F) 0 0 ((4 : F) • (1 : Matrix m m F))) *
      fromBlocks (1 : Matrix A A F) 0 ((1 / 4 : F) • Wyᵀ) (1 : Matrix m m F) := by
    simp only [bordered, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, smul_add,
        Matrix.transpose_smul, smul_zero, add_zero, zero_add, Matrix.mul_zero]
      try rw [hAa]
      try simp only [hY]
      try (first | module | (match_scalars <;> (try field_simp) <;> (try ring)))
  rw [hS, hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
  have e1 : ((-16 : F) ^ Fintype.card A)⁻¹ = (-(1 / 16 : F)) ^ Fintype.card A := by
    rw [← inv_pow]; congr 1; field_simp
  rw [e1]
  simp only [det_smul, det_one, det_neg, Matrix.det_one, one_pow, mul_one, one_mul, pow_add]
  have e2 : (-(1 / 4 : F)) ^ Fintype.card m * 4 ^ Fintype.card m = (-1) ^ Fintype.card m := by
    rw [← mul_pow]; congr 1; field_simp
  linear_combination ((-1 : F) ^ Fintype.card c * (-(1 / 16 : F)) ^ Fintype.card A * (bordered Y G Wx Wy).det) * e2

end CatalanFrames.LambdaHybrid.NV
