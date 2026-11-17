module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Block
public import CatalanCore.Arith.Hybrid.RankGLE

@[expose] public section

/-! # `CatalanCore.Content.HalfIntDet`: equality form of content Lemma 2.2 (half-integer potentials), ledger LC06. -/

section
/-!
# `CatalanCore.Content.HalfIntDet`: the equality form of content Lemma 2.2 (half-integer potentials)

Let `G` be a matrix over `ℚ` on an index set `ιA ⊕ ιB` and suppose `ℓ^c · G_xy = ℓ^{e_x} Z_xy ℓ^{f_y}`
with `Z` a matrix over `ℤ_(ℓ)`, the exponents natural numbers (these encode the potentials
`π_x ∈ ½ℤ`: `e_x + f_y - c = π_x + π_y` for `x, y` in the same class, and `+½` on `A × B`).
If the reduction of `Z` mod `ℓ` is block upper triangular (its `B × A` block vanishes; the `A × B`
block is arbitrary) with nonsingular diagonal blocks, then `det G ≠ 0`.  In the notation of the
content note, `v(det G) = Σ(e + f) - c·|ι|` exactly (`det_scale`), and the condition is
`det N̄_AA · det N̄_BB ≠ 0`.
-/

open Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Content

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Scaling of the determinant by row and column powers of `ℓ`. -/
theorem det_scale {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℚ)
    (Z : Matrix ι ι (LocRing ℓ)) (c : ℕ) (ex ey : ι → ℕ)
    (h : ∀ x y, (ℓ : ℚ) ^ c * G x y = (ℓ : ℚ) ^ ex x * ((Z x y : LocRing ℓ) : ℚ) * (ℓ : ℚ) ^ ey y) :
    (ℓ : ℚ) ^ (c * Fintype.card ι) * G.det =
      (ℓ : ℚ) ^ (∑ x, ex x + ∑ y, ey y) * ((Z.det : LocRing ℓ) : ℚ) := by
  have hmat : ((ℓ : ℚ) ^ c) • G = diagonal (fun x => (ℓ : ℚ) ^ ex x) *
      ((LocRing ℓ).subtype.mapMatrix Z) * diagonal (fun y => (ℓ : ℚ) ^ ey y) := by
    ext x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h x y]
    simp only [Subring.subtype_apply]
  have := congrArg Matrix.det hmat
  have e2 : ((LocRing ℓ).subtype.mapMatrix Z).det = ((Z.det : LocRing ℓ) : ℚ) := by
    rw [← RingHom.map_det]; rfl
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, det_diagonal, det_diagonal, e2,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at this
  rw [pow_mul, this, pow_add]
  ring

variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- **Equality form of Lemma 2.2**: block upper triangular reduction with nonsingular diagonal
blocks gives `det G ≠ 0`. -/
theorem det_ne_zero_of_block (G : Matrix (ιA ⊕ ιB) (ιA ⊕ ιB) ℚ)
    (Z : Matrix (ιA ⊕ ιB) (ιA ⊕ ιB) (LocRing ℓ)) (c : ℕ) (ex ey : ιA ⊕ ιB → ℕ)
    (h : ∀ x y, (ℓ : ℚ) ^ c * G x y = (ℓ : ℚ) ^ ex x * ((Z x y : LocRing ℓ) : ℚ) * (ℓ : ℚ) ^ ey y)
    (hBA : ∀ y x, redQ ℓ (Z (Sum.inr y) (Sum.inl x)) = 0)
    (hAA : (Matrix.of fun x x' => redQ ℓ (Z (Sum.inl x) (Sum.inl x'))).det ≠ 0)
    (hBB : (Matrix.of fun y y' => redQ ℓ (Z (Sum.inr y) (Sum.inr y'))).det ≠ 0) :
    G.det ≠ 0 := by
  have hZ : (redQ ℓ).mapMatrix Z =
      fromBlocks (Matrix.of fun x x' => redQ ℓ (Z (Sum.inl x) (Sum.inl x')))
        (Matrix.of fun x y => redQ ℓ (Z (Sum.inl x) (Sum.inr y))) 0
        (Matrix.of fun y y' => redQ ℓ (Z (Sum.inr y) (Sum.inr y'))) := by
    ext (x | y) (x' | y')
    · rfl
    · rfl
    · simp [hBA]
    · rfl
  have hdet : redQ ℓ Z.det ≠ 0 := by
    rw [RingHom.map_det, hZ, det_fromBlocks_zero₂₁]
    exact mul_ne_zero hAA hBB
  have hZq : ((Z.det : LocRing ℓ) : ℚ) ≠ 0 := by
    intro h0
    apply hdet
    have : Z.det = 0 := Subtype.ext h0
    rw [this, map_zero]
  intro hG
  have hs := det_scale G Z c ex ey h
  rw [hG, mul_zero] at hs
  have hl : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  exact mul_ne_zero (pow_ne_zero _ hl) hZq hs.symm

end CatalanCore.Content

end
