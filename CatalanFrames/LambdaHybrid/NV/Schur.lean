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

/-- The reduced matrix on `(A ⊕ c) ⊕ m`, with cross coefficient `t` and high diagonal `d`
(`t = -1/4`, `d = -1` for λ). -/
def Zmat (x t d : F) (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) :
    Matrix ((A ⊕ c) ⊕ m) ((A ⊕ c) ⊕ m) F :=
  fromBlocks (fromBlocks (x • (1 : Matrix A A F) - Aa) (t • Wc) (t • Wcᵀ) (d • (1 : Matrix c c F)))
    (fromRows (t • Wy) 0) (fromCols (t • Wxᵀ) 0) 0

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

/-- **Prop 1.3, Schur step, with frame constants.**  `κ` is the harmonic-identity scale
(`A = κ (W_all W_allᵀ + h)`), `t² = -d κ`. -/
theorem det_Zmat (x t d κ h : F) (ht : t ≠ 0) (hd : d ≠ 0) (hκ : κ ≠ 0) (htk : t * t = -d * κ)
    (Aa : Matrix A A F) (Wc : Matrix A c F) (Wx Wy : Matrix A m F) (G : Matrix A g F)
    (hA : Aa = κ • (Wc * Wcᵀ + G * Gᵀ + Wx * Wxᵀ + Wy * Wyᵀ + h • 1)) :
    (Zmat x t d Aa Wc Wx Wy).det =
      d ^ (Fintype.card c + Fintype.card m) * (-κ) ^ Fintype.card A *
        (bordered (h - x / κ) G Wx Wy).det := by
  rw [← Matrix.det_submatrix_equiv_self (zEquiv A c m).symm]
  have hZ : (Zmat x t d Aa Wc Wx Wy).submatrix (zEquiv A c m).symm (zEquiv A c m).symm =
      fromBlocks (fromBlocks (x • (1 : Matrix A A F) - Aa) (t • Wy) (t • Wxᵀ) 0)
        (fromRows (t • Wc) 0) (fromCols (t • Wcᵀ) 0) (d • (1 : Matrix c c F)) := by
    ext ((a | i) | j) ((b | k) | l) <;> simp [Zmat, zEquiv]
  rw [hZ]
  have : Invertible (d • (1 : Matrix c c F)) := ⟨d⁻¹ • 1, by simp [smul_smul, hd], by simp [smul_smul, hd]⟩
  rw [det_fromBlocks₂₂]
  have hi : ⅟(d • (1 : Matrix c c F)) = d⁻¹ • 1 := invOf_eq_right_inv (by simp [smul_smul, hd])
  rw [hi]
  have htd : t * d⁻¹ * t = -κ := by
    field_simp; linear_combination htk
  have hUV : fromRows (t • Wc) 0 * (d⁻¹ • (1 : Matrix c c F)) * fromCols (t • Wcᵀ) 0 =
      fromBlocks ((-κ) • (Wc * Wcᵀ)) (0 : Matrix A m F) (0 : Matrix m A F) (0 : Matrix m m F) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, fromRows_mul_fromCols]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : d⁻¹ * (t * t) = -κ := by rw [← htd]; ring
    ext (i | i) (j | j) <;> simp [Matrix.smul_apply, ← mul_assoc, this]
  rw [hUV]
  set Y : F := h - x / κ with hY
  have hS : fromBlocks (x • (1 : Matrix A A F) - Aa) (t • Wy) (t • Wxᵀ) 0 -
      fromBlocks ((-κ) • (Wc * Wcᵀ)) (0 : Matrix A m F) (0 : Matrix m A F) (0 : Matrix m m F) =
      fromBlocks (x • (1 : Matrix A A F) - Aa + κ • (Wc * Wcᵀ)) (t • Wy) (t • Wxᵀ) 0 := by
    ext (i | i) (j | j) <;> simp
  have hmain : fromBlocks (x • (1 : Matrix A A F) - Aa + κ • (Wc * Wcᵀ)) (t • Wy) (t • Wxᵀ) 0 =
      fromBlocks (1 : Matrix A A F) ((-(κ / t)) • Wx) (0 : Matrix m A F) (1 : Matrix m m F) *
        (fromBlocks ((-κ) • (1 : Matrix A A F)) 0 0 (t • (1 : Matrix m m F))
          * bordered Y G Wx Wy *
          fromBlocks (1 : Matrix A A F) 0 0 ((-(t / κ)) • (1 : Matrix m m F))) *
      fromBlocks (1 : Matrix A A F) 0 ((-(κ / t)) • Wyᵀ) (1 : Matrix m m F) := by
    simp only [bordered, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, smul_add,
        Matrix.transpose_smul, smul_zero, add_zero, zero_add, Matrix.mul_zero]
      try rw [hA]
      try simp only [hY]
      try (first | module | (match_scalars <;> (try field_simp) <;> (try ring)))
  rw [hS, hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
  simp only [det_smul, det_one, det_neg, Matrix.det_one, one_pow, mul_one, one_mul]
  have e2 : t ^ Fintype.card m * (-(t / κ)) ^ Fintype.card m = d ^ Fintype.card m := by
    rw [← mul_pow]; congr 1; field_simp; linear_combination -htk
  rw [pow_add]
  linear_combination (d ^ Fintype.card c * (-κ) ^ Fintype.card A * (bordered Y G Wx Wy).det) * e2

end CatalanFrames.LambdaHybrid.NV
