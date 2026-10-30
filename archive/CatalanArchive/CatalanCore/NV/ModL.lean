module

public import CatalanCore.Basic.ZModGood
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Generic mod-`ℓ` reduction calculus for nonvanishing

Shared by the λ, λ′ and P6 nonvanishing proofs:

* `scaleDiag`, `det_scaleDiag`: diagonal scaling `D (r I + M) D` and its determinant;
* `finSumEquiv`, `finSum3Equiv`: the block reindexing `Fin a ⊕ Fin b ≃ Fin (a+b)` (and three blocks);
* `schur_zero`, `schur_zero_diag`: if a bordered block matrix is singular, so is its Schur complement
  (identity or invertible-diagonal lower block; apply twice for three block levels);
* `reduce_det_eq_zero`: a rational scaled matrix with zero determinant reduces mod `ℓ` to a singular
  block matrix.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

section Scaling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- the scaled matrix `D (r I + M) D` with `D = diag d`, written entrywise. -/
def scaleDiag (d : ι → R) (r : R) (M : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of fun a b => d a * d b * ((if a = b then r else 0) + M a b)

lemma scaleDiag_eq (d : ι → R) (r : R) (M : Matrix ι ι R) :
    scaleDiag d r M = Matrix.diagonal d * (r • (1 : Matrix ι ι R) + M) * Matrix.diagonal d := by
  ext a b
  simp only [scaleDiag, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **`det_scaled`**: `det (D (r I + M) D) = (∏ d)² det (r I + M)`. -/
lemma det_scaleDiag (d : ι → R) (r : R) (M : Matrix ι ι R) :
    (scaleDiag d r M).det = (∏ a, d a) ^ 2 * (r • (1 : Matrix ι ι R) + M).det := by
  rw [scaleDiag_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

/-- If `P = det (r I + M)` vanishes, so does every diagonal scaling. -/
lemma det_scaleDiag_eq_zero (d : ι → R) (r : R) (M : Matrix ι ι R)
    (h : (r • (1 : Matrix ι ι R) + M).det = 0) : (scaleDiag d r M).det = 0 := by
  rw [det_scaleDiag, h, mul_zero]

end Scaling

section Blocks

/-- Reindexing `Fin K ⊕ Fin m ≃ Fin h` for `K + m = h`. -/
def finSumEquiv (K m h : ℕ) (hKm : K + m = h) : Fin K ⊕ Fin m ≃ Fin h :=
  finSumFinEquiv.trans (finCongr hKm)

@[simp] lemma finSumEquiv_inl (K m h : ℕ) (hKm : K + m = h) (a : Fin K) :
    ((finSumEquiv K m h hKm (Sum.inl a) : Fin h) : ℕ) = a := by
  simp [finSumEquiv]

@[simp] lemma finSumEquiv_inr (K m h : ℕ) (hKm : K + m = h) (c : Fin m) :
    ((finSumEquiv K m h hKm (Sum.inr c) : Fin h) : ℕ) = K + c := by
  simp [finSumEquiv]

/-- Reindexing `Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin h` for `a + (b + c) = h` (three block levels). -/
def finSum3Equiv (a b c h : ℕ) (habc : a + (b + c) = h) : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin h :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans (finSumFinEquiv.trans (finCongr habc))

@[simp] lemma finSum3Equiv_inl (a b c h : ℕ) (habc : a + (b + c) = h) (i : Fin a) :
    ((finSum3Equiv a b c h habc (Sum.inl i) : Fin h) : ℕ) = i := by
  simp [finSum3Equiv]

@[simp] lemma finSum3Equiv_inr_inl (a b c h : ℕ) (habc : a + (b + c) = h) (i : Fin b) :
    ((finSum3Equiv a b c h habc (Sum.inr (Sum.inl i)) : Fin h) : ℕ) = a + i := by
  simp [finSum3Equiv]

@[simp] lemma finSum3Equiv_inr_inr (a b c h : ℕ) (habc : a + (b + c) = h) (i : Fin c) :
    ((finSum3Equiv a b c h habc (Sum.inr (Sum.inr i)) : Fin h) : ℕ) = a + (b + i) := by
  simp [finSum3Equiv]

variable {F : Type*} [Field F] {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Schur complement with identity lower block:
`det [[X, B], [Bᵀ, 1]] = det (X - B Bᵀ)`. -/
lemma det_fromBlocks_one_transpose (X : Matrix α α F) (B : Matrix α β F) :
    (Matrix.fromBlocks X B Bᵀ 1).det = (X - B * Bᵀ).det := by
  rw [Matrix.det_fromBlocks_one₂₂]

/-- A singular bordered matrix `[[X, B], [Bᵀ, 1]]` has singular Schur complement `X - B Bᵀ`. -/
lemma schur_zero (X : Matrix α α F) (B : Matrix α β F)
    (h : (Matrix.fromBlocks X B Bᵀ 1).det = 0) : (X - B * Bᵀ).det = 0 := by
  rwa [det_fromBlocks_one_transpose] at h

/-- Schur complement with an invertible lower block `D`:
`det [[X, B], [C, D]] = det D · det (X - B D⁻¹ C)`. -/
lemma det_fromBlocks_schur (X : Matrix α α F) (B : Matrix α β F) (C : Matrix β α F)
    (D : Matrix β β F) (hD : D.det ≠ 0) :
    (Matrix.fromBlocks X B C D).det = D.det * (X - B * D⁻¹ * C).det := by
  have : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.2 hD)
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]

/-- A singular block matrix with invertible lower block has singular Schur complement. -/
lemma schur_zero_diag (X : Matrix α α F) (B : Matrix α β F) (C : Matrix β α F)
    (D : Matrix β β F) (hD : D.det ≠ 0)
    (h : (Matrix.fromBlocks X B C D).det = 0) : (X - B * D⁻¹ * C).det = 0 := by
  rw [det_fromBlocks_schur X B C D hD] at h
  exact (mul_eq_zero.1 h).resolve_left hD

end Blocks

section Reduce
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Reduction glue.**  A rational matrix `N` (indexed by `Fin h`) of the form
`D (r I + M) D` whose `r I + M` has vanishing determinant (the rational polynomial `P_h(r) = 0`)
reduces, for any entrywise-good block form `y` (indexed by `ι`, e.g. `Fin K ⊕ Fin m`), to a singular
matrix over `ZMod ℓ`. -/
lemma reduce_det_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ} (e : ι ≃ Fin h)
    (d : Fin h → ℚ) (r : ℚ) (M : Matrix (Fin h) (Fin h) ℚ)
    (y : Matrix ι ι (ZMod ℓ))
    (hy : ∀ i j, Good ℓ (scaleDiag d r M (e i) (e j)) (y i j))
    (hP : (r • (1 : Matrix (Fin h) (Fin h) ℚ) + M).det = 0) : y.det = 0 :=
  det_eq_zero_of_good e _ y hy (det_scaleDiag_eq_zero d r M hP)

end Reduce

end CatalanCore
