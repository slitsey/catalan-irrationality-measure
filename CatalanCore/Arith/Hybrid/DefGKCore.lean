module

public import CatalanCore.Arith.Hybrid.LemmaE.BlockScale

@[expose] public section

/-!
# GK / vector-partner T-route (no Neumann expansion)

`tcore_vec`: for the clean block `A = Full₁₁` with `p² A` integral of unit determinant, and *vector*
partners `α : κ × ι`, `β : ι × κ` (instead of the selection maps `cz, cy` of `T_decomp`):

* defect rows `L = C - α A` and columns `L' = B - A β` with all entries in `p⁻¹ ℤ_(p)[X]`,
* second difference `D - α B - C β + α A β` with entries in `ℤ_(p)[X]`

give `GLE p (2 r) (det Full)`, `r = |ι|`.  The defect term is `(p L) adj(p²A) (p L')`, integral
without any expansion of `A⁻¹`.  This turns GK's second-order Neumann computation into the
first-order identity `Σ g_i g_j (L_i - L_j) = 0` for the vectors `α = ρ Q⁻¹`, `β = Q⁻¹ ρ'`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

section Decomp

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- `T_decomp` with arbitrary (vector) partner matrices. -/
theorem T_decomp_gen (A N : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) (g : R) (hAN : A * N = g • 1) (hNA : N * A = g • 1)
    (Sr : Matrix κ ι R) (Sc : Matrix ι κ R) :
    g • D - C * N * B =
      g • (D - Sr * B - C * Sc + Sr * A * Sc) - (C - Sr * A) * N * (B - A * Sc) := by
  have e1 : C * N * (A * Sc) = g • (C * Sc) := by
    rw [Matrix.mul_assoc C N, ← Matrix.mul_assoc N A, hNA]; simp
  have e2 : Sr * A * N * B = g • (Sr * B) := by
    rw [Matrix.mul_assoc Sr A N, hAN]; simp
  have e3 : Sr * A * N * (A * Sc) = g • (Sr * A * Sc) := by
    rw [Matrix.mul_assoc (Sr * A) N, ← Matrix.mul_assoc N A, hNA]; simp
  simp only [Matrix.sub_mul, Matrix.mul_sub, e1, e2, e3, smul_sub, smul_add]
  abel

end Decomp

section Core

variable (p : ℕ) [Fact p.Prime]

lemma int1_mul_Cp {f : ℚ[X]} (hf : gn p f ≤ p) : Int1 p (f * C ((p : ℚ) ^ 1)) := by
  unfold Int1
  rw [gn_mul, gn_C, pow_one, padicNorm.padicNorm_p_of_prime]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  push_cast
  calc gn p f * (p : ℝ)⁻¹ ≤ p * (p : ℝ)⁻¹ := by gcongr
    _ = 1 := by field_simp

lemma int1_Cp_mul {f : ℚ[X]} (hf : gn p f ≤ p) : Int1 p (C ((p : ℚ) ^ 1) * f) := by
  rw [mul_comm]; exact int1_mul_Cp p hf

lemma matmul_int1 {a b c : Type*} [Fintype b] {M : Matrix a b ℚ[X]} {N : Matrix b c ℚ[X]}
    (hM : ∀ i j, Int1 p (M i j)) (hN : ∀ i j, Int1 p (N i j)) (i : a) (j : c) :
    Int1 p ((M * N) i j) := by
  rw [Matrix.mul_apply]
  apply Int1.sum
  intro k _
  exact (hM i k).mul (hN k j)

variable {p}

/-- **Vector-partner T-route.** -/
theorem tcore_vec {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p (fun _ : ι => 1) Full.toBlocks₁₁ i j))
    (hprim : gn p (Atil p (fun _ : ι => 1) Full.toBlocks₁₁).det = 1)
    (α : Matrix κ ι ℚ[X]) (β : Matrix ι κ ℚ[X])
    (hL : ∀ z c, gn p ((Full.toBlocks₂₁ - α * Full.toBlocks₁₁) z c) ≤ p)
    (hL' : ∀ c y, gn p ((Full.toBlocks₁₂ - Full.toBlocks₁₁ * β) c y) ≤ p)
    (hΔ : ∀ z y, Int1 p ((Full.toBlocks₂₂ - α * Full.toBlocks₁₂ - Full.toBlocks₂₁ * β +
      α * Full.toBlocks₁₁ * β) z y)) :
    GLE p (2 * Fintype.card ι) Full.det := by
  classical
  set A := Full.toBlocks₁₁ with hA
  have h := tcore_scaled p Full (fun _ : ι => 1) (Atil p (fun _ : ι => 1) A) hI hI
    (fun i j => Cng.refl _) hprim 0 ?_
  · simpa using h
  · intro z y
    set d : ι → ℕ := fun _ => 1
    set g := (Atil p d A).det with hg
    have hAN := AN_eq p d A
    have hNA := NA_eq p d A
    have key := T_decomp_gen A (Nmat p d A) Full.toBlocks₁₂ Full.toBlocks₂₁ Full.toBlocks₂₂ g
      hAN hNA α β
    unfold Tscaled
    rw [key]
    rw [(gle_iff_gn p 0 _)]
    simp only [pow_zero]
    show Int1 p _
    rw [Matrix.sub_apply]
    apply Int1.sub
    · rw [Matrix.smul_apply, smul_eq_mul]
      refine Int1.mul ?_ (hΔ z y)
      show gn p g ≤ 1
      rw [hg, hprim]
    · have hadj : ∀ i j, Int1 p ((Atil p d A).adjugate i j) := adj_int1 hI
      have e : (Full.toBlocks₂₁ - α * A) * Nmat p d A * (Full.toBlocks₁₂ - A * β) =
          ((Full.toBlocks₂₁ - α * A) * scl p d) * (Atil p d A).adjugate *
            (scl p d * (Full.toBlocks₁₂ - A * β)) := by
        simp only [Nmat, Matrix.mul_assoc]
      rw [e]
      have h1 : ∀ i j, Int1 p (((Full.toBlocks₂₁ - α * A) * scl p d) i j) := by
        intro i j
        simp only [scl, Matrix.mul_diagonal]
        exact int1_mul_Cp p (hL i j)
      have h2 : ∀ i j, Int1 p ((scl p d * (Full.toBlocks₁₂ - A * β)) i j) := by
        intro i j
        simp only [scl, Matrix.diagonal_mul]
        exact int1_Cp_mul p (hL' i j)
      exact matmul_int1 p (fun i j => matmul_int1 p h1 hadj i j) h2 z y

end Core

end CatalanCore.Arith.Hybrid.LemmaE
