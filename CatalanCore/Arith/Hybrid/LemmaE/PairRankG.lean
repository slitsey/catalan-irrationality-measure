module

public import CatalanCore.Arith.Hybrid.LemmaE.PairRank

@[expose] public section

/-!
# Lemma E, class `p ≡ 3 (4)`: the abstract rank count

* `pairMatG`/`pairInvG`: a "diagonal plus pairs" matrix with point-dependent constants
  `d c` (diagonal), `e c` (coupling to the partner `τ c`) and its explicit inverse
  (`d(τc)/Δ`, `-e/Δ`, `Δ = d c · d(τ c) - e c²`; `(d c)⁻¹` at fixed points).
* `rank_blocks_zero_schur`: `rank (fromBlocks A B C 0) ≤ |A|` if `B = A V`, `C V = 0`.
* `rank_E3_abs`: lower-triangular `A = [[M0, 0],[N1, D1]]` (`M0` invertible, `D1` invertible) with
  border `B`, `C` and a solution `V` of `A V = B`, `C V = 0`: the whole matrix has rank `≤ |Pt| + |Wt|`.
  No Neumann series: only the explicit solution `V` of two linear systems is used.
-/

open Matrix CatalanCore.Linalg

namespace CatalanCore.Arith.Hybrid

section PairG

variable {K : Type*} [Field K] {P : Type*} [Fintype P] [DecidableEq P]

def pairMatG (τ : P → P) (d e : P → K) : Matrix P P K :=
  Matrix.of fun c c' => if c' = c then d c else if c' = τ c then e c else 0

def pairInvG (τ : P → P) (d e : P → K) : Matrix P P K :=
  Matrix.of fun c c' => if c' = c then
      (if τ c = c then (d c)⁻¹ else d (τ c) / (d c * d (τ c) - e c ^ 2))
    else if c' = τ c then -e c / (d c * d (τ c) - e c ^ 2) else 0

variable (τ : P → P) (d e : P → K)

lemma pairInvG_self_fix (c : P) (h : τ c = c) : pairInvG τ d e c c = (d c)⁻¹ := by
  simp [pairInvG, h]

lemma pairInvG_self_nf (c : P) (h : τ c ≠ c) :
    pairInvG τ d e c c = d (τ c) / (d c * d (τ c) - e c ^ 2) := by
  simp [pairInvG, h]

lemma pairInvG_tau (c : P) (h : τ c ≠ c) :
    pairInvG τ d e c (τ c) = -e c / (d c * d (τ c) - e c ^ 2) := by
  simp [pairInvG, h]

lemma pairInvG_oth (c c'' : P) (h1 : c'' ≠ c) (h2 : c'' ≠ τ c) : pairInvG τ d e c c'' = 0 := by
  simp [pairInvG, h1, h2]

theorem pairMatG_mul_pairInvG (hτ : ∀ c, τ (τ c) = c) (hes : ∀ c, e (τ c) = e c)
    (hfix : ∀ c, τ c = c → d c ≠ 0) (hΔ : ∀ c, τ c ≠ c → d c * d (τ c) - e c ^ 2 ≠ 0) :
    pairMatG τ d e * pairInvG τ d e = 1 := by
  ext c c''
  rw [Matrix.mul_apply]
  have key : ∀ c', pairMatG τ d e c c' * pairInvG τ d e c' c'' =
      (if c' = c then d c * pairInvG τ d e c c''
       else if c' = τ c then e c * pairInvG τ d e (τ c) c'' else 0) := by
    intro c'
    by_cases h1 : c' = c
    · subst h1; simp [pairMatG]
    · by_cases h2 : c' = τ c
      · subst h2; simp [pairMatG, h1]
      · simp [pairMatG, h1, h2]
  simp only [key]
  rw [sum_two τ (fun _ => d c * pairInvG τ d e c c'') (fun _ => e c * pairInvG τ d e (τ c) c'') c]
  by_cases hf : τ c = c
  · simp only [hf, if_true, add_zero]
    by_cases h3 : c'' = c
    · subst h3; rw [pairInvG_self_fix τ d e c'' hf]
      simp [mul_inv_cancel₀ (hfix _ hf)]
    · rw [pairInvG_oth τ d e c c'' h3 (by rw [hf]; exact h3)]
      simp [Matrix.one_apply, Ne.symm h3]
  · have hΔc := hΔ c hf
    have hτ2 : τ (τ c) ≠ τ c := by rw [hτ]; exact Ne.symm hf
    have hΔt : d (τ c) * d (τ (τ c)) - e (τ c) ^ 2 = d c * d (τ c) - e c ^ 2 := by
      rw [hτ, hes]; ring
    simp only [hf, if_false]
    by_cases h3 : c'' = c
    · subst h3
      have h4 : pairInvG τ d e (τ c'') c'' = -e c'' / (d c'' * d (τ c'') - e c'' ^ 2) := by
        have := pairInvG_tau τ d e (τ c'') hτ2
        rw [hτ, hes, mul_comm (d (τ c''))] at this
        exact this
      rw [pairInvG_self_nf τ d e c'' hf, h4]
      simp only [Matrix.one_apply, if_true]
      field_simp
      ring
    · by_cases h4 : c'' = τ c
      · subst h4
        have h5 : pairInvG τ d e (τ c) (τ c) = d c / (d c * d (τ c) - e c ^ 2) := by
          rw [pairInvG_self_nf τ d e (τ c) hτ2, hτ, hes, mul_comm (d (τ c))]
        rw [pairInvG_tau τ d e c hf, h5]
        simp only [Matrix.one_apply, if_neg (Ne.symm hf)]
        field_simp
        ring
      · rw [pairInvG_oth τ d e c c'' h3 h4,
          pairInvG_oth τ d e (τ c) c'' h4 (by rw [hτ]; exact h3)]
        simp [Matrix.one_apply, Ne.symm h3]

end PairG

section RankZero

variable {K : Type*} [Field K] {n X Y : Type*} [Fintype n] [Fintype X] [Fintype Y]
  [DecidableEq n] [DecidableEq X] [DecidableEq Y]

theorem rank_blocks_zero_schur (A : Matrix n n K) [Invertible A] (B : Matrix n Y K)
    (C : Matrix X n K) (V : Matrix n Y K) (hAV : A * V = B) (hCV : C * V = 0) :
    (fromBlocks A B C (0 : Matrix X Y K)).rank ≤ Fintype.card n := by
  have h := rank_fromBlocks_schur₁₁_le A B C (0 : Matrix X Y K)
  have : (0 : Matrix X Y K) - C * ⅟A * B = 0 := by
    rw [← hAV, ← Matrix.mul_assoc, Matrix.mul_assoc C, invOf_mul_self, Matrix.mul_one, hCV]
    simp
  rw [this, Matrix.rank_zero] at h
  omega

variable {Pt Wt : Type*} [Fintype Pt] [Fintype Wt] [DecidableEq Pt] [DecidableEq Wt]

/-- **Abstract rank count for class 3**: `A = [[M0, 0], [N1, D1]]`, border `B`, `C`, `D = 0`,
with explicit solutions `V = (V1; V2)` of `A V = B`, `C V = 0`. -/
theorem rank_E3_abs (Mat : Matrix ((Pt ⊕ Wt) ⊕ X) ((Pt ⊕ Wt) ⊕ X) K)
    [Invertible (Matrix.of fun c c' : Pt => Mat (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c')))]
    [Invertible (Matrix.of fun w w' : Wt => Mat (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w')))]
    (hA12 : ∀ c w, Mat (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inr w)) = 0)
    (hD : ∀ x y, Mat (Sum.inr x) (Sum.inr y) = 0)
    (V1 : Pt → X → K) (V2 : Wt → X → K)
    (h1 : ∀ c y, ∑ c', Mat (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c')) * V1 c' y =
      Mat (Sum.inl (Sum.inl c)) (Sum.inr y))
    (h2 : ∀ w y, ∑ c', Mat (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inl c')) * V1 c' y +
      ∑ w', Mat (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w')) * V2 w' y =
      Mat (Sum.inl (Sum.inr w)) (Sum.inr y))
    (h3 : ∀ x y, ∑ c', Mat (Sum.inr x) (Sum.inl (Sum.inl c')) * V1 c' y +
      ∑ w', Mat (Sum.inr x) (Sum.inl (Sum.inr w')) * V2 w' y = 0) :
    Mat.rank ≤ Fintype.card Pt + Fintype.card Wt := by
  set M0 : Matrix Pt Pt K := Matrix.of fun c c' => Mat (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c'))
    with hM0
  set D1 : Matrix Wt Wt K := Matrix.of fun w w' => Mat (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w'))
    with hD1
  set N1 : Matrix Wt Pt K := Matrix.of fun w c => Mat (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inl c))
    with hN1
  have hA : Mat.toBlocks₁₁ = fromBlocks M0 0 N1 D1 := by
    ext (c | w) (c' | w')
    · simp [Matrix.toBlocks₁₁, hM0]
    · simp [Matrix.toBlocks₁₁, hA12]
    · simp [Matrix.toBlocks₁₁, hN1]
    · simp [Matrix.toBlocks₁₁, hD1]
  letI : Invertible (fromBlocks M0 0 N1 D1) := Matrix.fromBlocksZero₁₂Invertible M0 N1 D1
  letI : Invertible Mat.toBlocks₁₁ := by rw [hA]; infer_instance
  have hfb := Matrix.fromBlocks_toBlocks Mat
  have hD0 : Mat.toBlocks₂₂ = 0 := by
    ext x y; simp [Matrix.toBlocks₂₂, hD]
  let V : Matrix (Pt ⊕ Wt) X K := Matrix.of fun i y => Sum.elim (fun c => V1 c y) (fun w => V2 w y) i
  have hAV : Mat.toBlocks₁₁ * V = Mat.toBlocks₁₂ := by
    ext (c | w) y
    · simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.of_apply,
        Matrix.toBlocks₁₂, V, Sum.elim_inl, Sum.elim_inr, hA12, zero_mul, Finset.sum_const_zero,
        add_zero]
      exact h1 c y
    · simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.of_apply,
        Matrix.toBlocks₁₂, V, Sum.elim_inl, Sum.elim_inr]
      exact h2 w y
  have hCV : Mat.toBlocks₂₁ * V = 0 := by
    ext x y
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.of_apply, V,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]
    exact h3 x y
  have := rank_blocks_zero_schur Mat.toBlocks₁₁ Mat.toBlocks₁₂ Mat.toBlocks₂₁ V hAV hCV
  rw [← hD0] at this
  rw [hfb] at this
  simpa using this

end RankZero

end CatalanCore.Arith.Hybrid
