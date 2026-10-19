module

public import CatalanCore.Linalg.RankCount
public import CatalanCore.Arith.Hybrid.RankGLE

@[expose] public section

/-!
# Theorem B (deficit `r + m - p` for `r < p < r + m`): the linear-algebra core

This file contains the pure linear algebra of the rank count of Theorem B (GJ §1): once the
reduction `B̄ = (p^u Full p^v) mod p` of the matrix under the D4 potentials has the block form
established by the entry computations, `rank B̄ ≤ r + d` with `d = p - r`.

Setting (over a field `K = 𝔽_p(X)`): `B0` = block of level 0 (`k` indices), `B1` = block of
level `-1/j` (invertible diagonal `π`), `X`, `Y` = the zone rows and columns, `D` = index set of
`E(u, i) = 1/(u+i)`, `i ≤ d`.  The Schur complement on `B0` is `s₀ I - κ E Eᵀ`; a zone row `x` is
either *low* (row `-λ E(·, i_x)`, `i_x ∈ D`) or *high* (single entry `σ` at `c_x ∈ B0`).
Low `X`-indices and low `Y`-indices use disjoint `i`'s, and high `c_x` differ from high `c_y`.
-/

open Matrix CatalanCore.Linalg

namespace CatalanCore.Arith.Hybrid

section Core

variable {K : Type*} [Field K] {B0 B1 X Y D : Type*}
  [Fintype B0] [Fintype B1] [Fintype X] [Fintype Y] [Fintype D]
  [DecidableEq B0] [DecidableEq B1] [DecidableEq X] [DecidableEq Y] [DecidableEq D]

/-- The matrix `M = [[S, G_Y], [G_X, 0]]` of the proof, with `S = s₀ I - κ E Eᵀ`. -/
def McoreB (s0 κ : K) (E : Matrix B0 D K) (Gx : Matrix X B0 K) (Gy : Matrix B0 Y K) :
    Matrix (B0 ⊕ X) (B0 ⊕ Y) K :=
  fromBlocks (s0 • (1 : Matrix B0 B0 K) - κ • (E * Eᵀ)) Gy Gx 0

/-- **Rank count of Theorem B.**  `rank M ≤ |B0| + |D|`. -/
theorem rank_McoreB_le (s0 κ lam σ : K) (hs0 : s0 ≠ 0) (E : Matrix B0 D K)
    (Gx : Matrix X B0 K) (Gy : Matrix B0 Y K)
    (lowX : X → Prop) (lowY : Y → Prop) [DecidablePred lowX] [DecidablePred lowY] (iX : X → D) (iY : Y → D) (cX : X → B0) (cY : Y → B0)
    (hGx : ∀ x u, Gx x u = if lowX x then -lam * E u (iX x) else (if u = cX x then σ else 0))
    (hGy : ∀ u y, Gy u y = if lowY y then -lam * E u (iY y) else (if u = cY y then σ else 0))
    (hdisj : ∀ x y, lowX x → lowY y → iX x ≠ iY y)
    (hc : ∀ x y, ¬ lowX x → ¬ lowY y → cX x ≠ cY y) :
    (McoreB s0 κ E Gx Gy).rank ≤ Fintype.card B0 + Fintype.card D := by
  classical
  -- the high parts
  let Gx2 : Matrix X B0 K := Matrix.of fun x u => if lowX x then 0 else (if u = cX x then σ else 0)
  let Gy2 : Matrix B0 Y K := Matrix.of fun u y => if lowY y then 0 else (if u = cY y then σ else 0)
  let M2 : Matrix (B0 ⊕ X) (B0 ⊕ Y) K := fromBlocks (s0 • (1 : Matrix B0 B0 K)) Gy2 Gx2 0
  let YT : D → Prop := fun i => ∃ y, lowY y ∧ iY y = i
  let a : D → B0 ⊕ X → K := fun i => Sum.elim (fun u => if YT i then E u i else -κ * E u i)
    (fun x => if lowX x ∧ iX x = i then -lam else 0)
  let b : D → B0 ⊕ Y → K := fun i => Sum.elim (fun w => if YT i then -κ * E w i else E w i)
    (fun y => if lowY y ∧ iY y = i then -lam else 0)
  have hdx : ∀ x, lowX x → ¬ YT (iX x) := by
    rintro x hx ⟨y, hy, h⟩
    exact hdisj x y hx hy h.symm
  have hsplit : McoreB s0 κ E Gx Gy = M2 + ∑ i : D, Matrix.vecMulVec (a i) (b i) := by
    ext (i | i) (j | j)
    · -- (B0, B0)
      simp only [McoreB, M2, fromBlocks_apply₁₁, Matrix.add_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, a, b, Sum.elim_inl, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
      have : ∀ t : D, (if YT t then E i t else -κ * E i t) * (if YT t then -κ * E j t else E j t) =
          -κ * (E i t * E j t) := by
        intro t; split_ifs <;> ring
      simp only [this, ← Finset.mul_sum]
      ring
    · -- (B0, Y)
      simp only [McoreB, M2, fromBlocks_apply₁₂, Matrix.add_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, a, b, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, Gy2]
      rw [hGy]
      by_cases hy : lowY j
      · have hsum : ∑ t : D, (if YT t then E i t else -κ * E i t) *
            (if lowY j ∧ iY j = t then -lam else 0) = E i (iY j) * (-lam) := by
          rw [Finset.sum_eq_single (iY j)]
          · have h1 : lowY j ∧ iY j = iY j := ⟨hy, rfl⟩
            have h2 : YT (iY j) := ⟨j, hy, rfl⟩
            rw [if_pos h1, if_pos h2]
          · intro t _ ht
            have hne : ¬ (lowY j ∧ iY j = t) := by rintro ⟨_, h⟩; exact ht h.symm
            rw [if_neg hne, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum, if_pos hy, if_pos hy]; ring
      · have hsum : ∑ t : D, (if YT t then E i t else -κ * E i t) *
            (if lowY j ∧ iY j = t then -lam else 0) = 0 := by
          refine Finset.sum_eq_zero fun t _ => ?_
          have hne : ¬ (lowY j ∧ iY j = t) := by rintro ⟨h, _⟩; exact hy h
          rw [if_neg hne, mul_zero]
        rw [hsum, if_neg hy, if_neg hy]; ring
    · -- (X, B0)
      simp only [McoreB, M2, fromBlocks_apply₂₁, Matrix.add_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, a, b, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, Gx2]
      rw [hGx]
      by_cases hx : lowX i
      · have hsum : ∑ t : D, (if lowX i ∧ iX i = t then -lam else 0) *
            (if YT t then -κ * E j t else E j t) = -lam * E j (iX i) := by
          rw [Finset.sum_eq_single (iX i)]
          · have h1 : lowX i ∧ iX i = iX i := ⟨hx, rfl⟩
            rw [if_pos h1, if_neg (hdx i hx)]
          · intro t _ ht
            have hne : ¬ (lowX i ∧ iX i = t) := by rintro ⟨_, h⟩; exact ht h.symm
            rw [if_neg hne, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum, if_pos hx, if_pos hx]; ring
      · have hsum : ∑ t : D, (if lowX i ∧ iX i = t then -lam else 0) *
            (if YT t then -κ * E j t else E j t) = 0 := by
          refine Finset.sum_eq_zero fun t _ => ?_
          have hne : ¬ (lowX i ∧ iX i = t) := by rintro ⟨h, _⟩; exact hx h
          rw [if_neg hne, zero_mul]
        rw [hsum, if_neg hx, if_neg hx]; ring
    · -- (X, Y)
      simp only [McoreB, M2, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, a, b, Sum.elim_inr, Matrix.zero_apply]
      rw [zero_add]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases h1 : lowX i ∧ iX i = t
      · by_cases h2 : lowY j ∧ iY j = t
        · exact absurd (h1.2.trans h2.2.symm) (hdisj i j h1.1 h2.1)
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  have hrank2 : M2.rank ≤ Fintype.card B0 := by
    let Pm : Matrix (B0 ⊕ X) B0 K := Matrix.of fun a u =>
      Sum.elim (fun u' => if u' = u then 1 else 0) (fun x => s0⁻¹ * Gx2 x u) a
    let Qm : Matrix B0 (B0 ⊕ Y) K := Matrix.of fun u b =>
      Sum.elim (fun w => if u = w then s0 else 0) (fun y => Gy2 u y) b
    have hM2 : M2 = Pm * Qm := by
      ext (i | i) (j | j)
      · simp [M2, Pm, Qm, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply]
      · simp [M2, Pm, Qm, Matrix.mul_apply]
      · simp [M2, Pm, Qm, Matrix.mul_apply]
        field_simp
      · simp only [M2, Pm, Qm, Matrix.mul_apply, fromBlocks_apply₂₂, Matrix.zero_apply,
          Matrix.of_apply, Sum.elim_inr]
        symm
        refine Finset.sum_eq_zero fun u _ => ?_
        by_cases h1 : lowX i
        · simp [Gx2, h1]
        · by_cases h2 : lowY j
          · simp [Gy2, h2]
          · by_cases h3 : u = cX i
            · have : u ≠ cY j := fun h => hc i j h1 h2 (h3.symm.trans h)
              simp [Gy2, h2, this]
            · simp [Gx2, h1, h3]
    rw [hM2]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  rw [hsplit]
  refine (rank_add_le' _ _).trans (add_le_add hrank2 ?_)
  simpa using rank_sum_vecMulVec_le (Finset.univ : Finset D) a b

/-- The reduction `B̄` of Theorem B: rows `B0 ⊕ X` and `B1`, columns `B0 ⊕ Y` and `B1`;
`B0×B1 = V`, `B1×B1 = π I`, `B1×zone = 0`. -/
def BbarB (A0 : Matrix B0 B0 K) (V : Matrix B0 B1 K) (π : K) (Gx : Matrix X B0 K)
    (Gy : Matrix B0 Y K) : Matrix ((B0 ⊕ X) ⊕ B1) ((B0 ⊕ Y) ⊕ B1) K :=
  fromBlocks (fromBlocks A0 Gy Gx 0)
    (Matrix.of fun a b => Sum.elim (fun u => V u b) (fun _ => (0 : K)) a)
    (Matrix.of fun b a => Sum.elim (fun u => V u b) (fun _ => (0 : K)) a)
    (π • (1 : Matrix B1 B1 K))

/-- **Theorem B, rank count.**  `rank B̄ ≤ |B1| + |B0| + |D|`, that is `r + d`. -/
theorem rank_BbarB_le (A0 : Matrix B0 B0 K) (V : Matrix B0 B1 K) (π s0 κ lam σ : K)
    (hπ : π ≠ 0) (hs0 : s0 ≠ 0) (E : Matrix B0 D K)
    (hS : A0 - π⁻¹ • (V * Vᵀ) = s0 • (1 : Matrix B0 B0 K) - κ • (E * Eᵀ))
    (Gx : Matrix X B0 K) (Gy : Matrix B0 Y K)
    (lowX : X → Prop) (lowY : Y → Prop) [DecidablePred lowX] [DecidablePred lowY]
    (iX : X → D) (iY : Y → D) (cX : X → B0) (cY : Y → B0)
    (hGx : ∀ x u, Gx x u = if lowX x then -lam * E u (iX x) else (if u = cX x then σ else 0))
    (hGy : ∀ u y, Gy u y = if lowY y then -lam * E u (iY y) else (if u = cY y then σ else 0))
    (hdisj : ∀ x y, lowX x → lowY y → iX x ≠ iY y)
    (hc : ∀ x y, ¬ lowX x → ¬ lowY y → cX x ≠ cY y) :
    (BbarB A0 V π Gx Gy).rank ≤ Fintype.card B1 + Fintype.card B0 + Fintype.card D := by
  classical
  let _ : Invertible (π • (1 : Matrix B1 B1 K)) :=
    ⟨π⁻¹ • 1, by simp [smul_smul, hπ], by simp [smul_smul, hπ]⟩
  have h1 := rank_fromBlocks_schur_le (fromBlocks A0 Gy Gx 0)
    (Matrix.of fun a b => Sum.elim (fun u => V u b) (fun _ => (0 : K)) a)
    (Matrix.of fun b a => Sum.elim (fun u => V u b) (fun _ => (0 : K)) a)
    (π • (1 : Matrix B1 B1 K))
  have hschur : (fromBlocks A0 Gy Gx 0 -
      (Matrix.of fun a b => Sum.elim (fun u => V u b) (fun _ => (0 : K)) a) *
        ⅟(π • (1 : Matrix B1 B1 K)) *
      (Matrix.of fun b a => Sum.elim (fun u => V u b) (fun _ => (0 : K)) a)) =
      McoreB s0 κ E Gx Gy := by
    have hinv : ⅟(π • (1 : Matrix B1 B1 K)) = π⁻¹ • 1 := rfl
    rw [hinv]; unfold McoreB; rw [← hS]
    ext (i | i) (j | j)
    · simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]
  rw [hschur] at h1
  have h2 := rank_McoreB_le s0 κ lam σ hs0 E Gx Gy lowX lowY iX iY cX cY hGx hGy hdisj hc
  unfold BbarB
  omega

end Core

end CatalanCore.Arith.Hybrid
