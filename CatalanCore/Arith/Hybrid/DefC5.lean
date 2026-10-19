module

public import CatalanCore.Linalg.RankCount
public import CatalanCore.Arith.Hybrid.RankGLE

@[expose] public section

/-!
# Theorem C5 (deficit `L - m`): the linear-algebra core

Setting (GJ §1, Theorems C5/C7), over `K = 𝔽_p(X)`.  The reduction `B̄` of the matrix under the
D2 potentials has rows/columns `(U ⊕ X) ⊕ P` / `(U ⊕ Y) ⊕ P`: `U` the unpaired low block
(`|U| = L`), `P = 𝒫` the invertible block `Mp` (pairs and `B1`), `X`, `Y` the zone rows and columns.
After eliminating `𝒫` the Schur complement is `[[s₀ I_U, G_Y'], [G_X', 0]]` (DQ Lemma 3.1 gives
the scalar block `s₀ I`; the zone × zone block vanishes since the high rows meet `Mp⁻¹` only in
distinct diagonal slots).  A *low* zone row is `σ e_{c_z}` with `c_z ∈ U`, and `c_x ≠ c_y` for low
`x, y`.  Then the zone × zone block of the second Schur complement has a zero block
`LX × LY`, and Frobenius–König gives `rank B̄ ≤ |P| + |U| + (m - |LX|) + (m - |LY|)`, i.e.
`corank ≥ |LX| + |LY| - m = L - m`.
-/

open Matrix CatalanCore.Linalg

namespace CatalanCore.Arith.Hybrid

section Core

variable {K : Type*} [Field K] {U P X Y : Type*}
  [Fintype U] [Fintype P] [Fintype X] [Fintype Y]
  [DecidableEq U] [DecidableEq P] [DecidableEq X] [DecidableEq Y]

/-- **Theorem C5, rank count.** -/
theorem rank_BbarC5_le (T : Matrix (U ⊕ X) (U ⊕ Y) K) (Up : Matrix (U ⊕ X) P K)
    (Wp : Matrix P (U ⊕ Y) K) (Mp : Matrix P P K) [Invertible Mp] (s0 : K) (hs0 : s0 ≠ 0)
    (Gx : Matrix X U K) (Gy : Matrix U Y K)
    (hSchur : T - Up * ⅟Mp * Wp = fromBlocks (s0 • (1 : Matrix U U K)) Gy Gx 0)
    (LX : Finset X) (LY : Finset Y) (cX : X → U) (cY : Y → U) (σ : K)
    (hGx : ∀ x ∈ LX, ∀ u, Gx x u = if u = cX x then σ else 0)
    (hGy : ∀ y ∈ LY, ∀ u, Gy u y = if u = cY y then σ else 0)
    (hc : ∀ x ∈ LX, ∀ y ∈ LY, cX x ≠ cY y) :
    (fromBlocks T Up Wp Mp).rank ≤ Fintype.card P + Fintype.card U +
      ((Fintype.card X - LX.card) + (Fintype.card Y - LY.card)) := by
  classical
  have h1 := rank_fromBlocks_schur_le T Up Wp Mp
  rw [hSchur] at h1
  let _ : Invertible (s0 • (1 : Matrix U U K)) :=
    ⟨s0⁻¹ • 1, by simp [smul_smul, hs0], by simp [smul_smul, hs0]⟩
  have h2 := rank_fromBlocks_schur₁₁_le (s0 • (1 : Matrix U U K)) Gy Gx 0
  have hinv : ⅟(s0 • (1 : Matrix U U K)) = s0⁻¹ • 1 := rfl
  rw [hinv] at h2
  have hZ : (0 - Gx * (s0⁻¹ • (1 : Matrix U U K)) * Gy : Matrix X Y K) =
      (-s0⁻¹) • (Gx * Gy) := by
    simp [Matrix.mul_smul, Matrix.smul_mul, neg_smul]
  rw [hZ] at h2
  have h3 : ((-s0⁻¹) • (Gx * Gy)).rank ≤ (Fintype.card X - LX.card) + (Fintype.card Y - LY.card) := by
    apply rank_le_of_zero_block _ LX LY
    intro x hx y hy
    simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    have : ∀ u, Gx x u * Gy u y = 0 := by
      intro u
      rw [hGx x hx u, hGy y hy u]
      by_cases h : u = cX x
      · have : u ≠ cY y := fun h' => hc x hx y hy (h.symm.trans h')
        simp [this]
      · simp [h]
    simp [this]
  omega

end Core

end CatalanCore.Arith.Hybrid
