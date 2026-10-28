module

public import CatalanCore.Uniform.Content.UFMember.Minor3
public import CatalanCore.Uniform.Content.UFMember.Wit
public import CatalanCore.Uniform.Content.UFMember.Gauge
public import CatalanCore.Uniform.Content.Member.LPD

@[expose] public section

/-!
# UF member package: three-level (Smith-layer) witnesses and their members

`ThreeLevelWit p M b` is the Lean form of the level-2 Smith certificate of
`smith-deletion/THEOREM.md` for `A = p² M` (all weights `1`): primitive changes `L, P` and
row/column sets `s ⊆ t` with (H1)-(H5) of `Minor3`.  For the full matrix it gives

  `denexp_p(det M) ≤ 2h - (|t| + |s| + (|s| - b))`

(`t` = border rows `m`, `s` = `σ_J`, `b` = retained-pole count `s_J`: the price
`2|C| + m - (σ + (σ - s))`), and for EVERY minor with `k` deleted rows and columns the same
price plus `k` (`gle_submatrix_debit`), i.e. Theorem SD with debit `k`.

`ufMember3_gle` applies this to a deletion member of the hybrid matrix; `ufMember3_gle_scaled`
does the same when the witness lives in the scaled gauge `Ψ = Φ(U/p²)` (the gauge of the paper),
transferring back with `Gauge.gle_submatrix_of_scaleU`.
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFMember

variable {p : ℕ} [Fact p.Prime]

/-- A three-level witness for `det M` (weights `1`, i.e. the lift of `p² M`). -/
structure ThreeLevelWit (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ[X]) (b : ℕ) where
  Bl : Matrix ι ι (LocRing p)[X]
  hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ 2) * M i j
  L : Matrix ι ι (LocRing p)[X]
  P : Matrix ι ι (LocRing p)[X]
  hL : phiP p L.det ≠ 0
  hP : phiP p P.det ≠ 0
  t : Finset ι
  s : Finset ι
  hst : s ⊆ t
  H1 : ∀ i ∈ t, ∀ j, C ((p : ℕ) : LocRing p) ∣ (L * Bl * P) i j
  H2 : ∀ i ∈ s, ∀ j, C ((p : ℕ) : LocRing p) ^ 2 ∣ (L * Bl * P) i j
  H3 : ∀ i, ∀ j ∈ s, C ((p : ℕ) : LocRing p) ∣ (L * Bl * P) i j
  H4 : ∀ i ∈ t, ∀ j ∈ s, C ((p : ℕ) : LocRing p) ^ 2 ∣ (L * Bl * P) i j
  N₂ : Matrix s s (LocRing p)[X]
  H5 : ∀ i j : s, (L * Bl * P) i j = C ((p : ℕ) : LocRing p) ^ 2 * N₂ i j
  hb : (N₂.map (phiP p)).rank ≤ b

namespace ThreeLevelWit

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {M : Matrix ι ι ℚ[X]} {b : ℕ}

/-- The full-matrix price `2h - (|t| + |s| + (|s| - b))`. -/
def price (W : ThreeLevelWit p M b) : ℕ :=
  2 * Fintype.card ι - (W.t.card + (W.s.card + (W.s.card - b)))

/-- **Minors of a three-level witness.** -/
theorem gle_submatrix (W : ThreeLevelWit p M b) (e₁ e₂ : κ → ι) :
    GLE p (2 * Fintype.card κ - ((W.t.card + Fintype.card κ - Fintype.card ι) +
      ((W.s.card + Fintype.card κ - Fintype.card ι) +
        ((W.s.card + Fintype.card κ - Fintype.card ι) - b)))) (M.submatrix e₁ e₂).det := by
  have hdvd := three_level_dvd_det_submatrix (phiP p) (Polynomial.prime_C_iff.2 (prime_p p))
    (phiP_eq_zero_iff p) (UFMember.phiP_lift p) W.Bl W.L W.P W.hL W.hP W.t W.s W.hst W.H1 W.H2
    W.H3 W.H4 W.N₂ W.H5 b W.hb e₁ e₂
  have h := gle_det_of_scaled_dvd p (M.submatrix e₁ e₂) (W.Bl.submatrix e₁ e₂)
    (fun _ => 1) (fun _ => 1) (fun i j => by rw [Matrix.submatrix_apply, W.hB]; norm_num) _ hdvd
  simpa [Finset.sum_const, Finset.card_univ, two_mul] using h

/-- **The full matrix.** -/
theorem gle (W : ThreeLevelWit p M b) : GLE p W.price M.det := by
  have h := W.gle_submatrix (κ := ι) id id
  have e : M.submatrix id id = M := by ext i j; rfl
  rw [e] at h
  refine h.mono ?_
  unfold price
  omega

/-- **Theorem SD (level 2, Lean form): a deletion costs at most `k`.** -/
theorem gle_submatrix_debit (W : ThreeLevelWit p M b) (e₁ e₂ : κ → ι)
    (hk : Fintype.card κ ≤ Fintype.card ι) :
    GLE p (W.price + (Fintype.card ι - Fintype.card κ)) (M.submatrix e₁ e₂).det := by
  refine (W.gle_submatrix e₁ e₂).mono ?_
  unfold price
  omega

end ThreeLevelWit

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Smith layer for a deletion member** (original gauge). -/
theorem ufMember3_gle (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι) {b : ℕ}
    (W : ThreeLevelWit p (FullN Fr common xs ys (X : ℚ[X])) b) :
    GLE p (W.price + (Fintype.card ι - S.card))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  rw [fullN_member_eq_submatrix]
  have hS : S.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ S
  have h := W.gle_submatrix_debit (memberEmbedding S) (memberEmbedding S)
    (by simp only [Fintype.card_sum, Fintype.card_coe]; omega)
  refine h.mono ?_
  simp only [Fintype.card_sum, Fintype.card_coe]
  omega

/-- **Smith layer for a deletion member, scaled gauge `X = U/p²`** (the gauge of the paper). -/
theorem ufMember3_gle_scaled (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    {b : ℕ} (W : ThreeLevelWit p ((FullN Fr common xs ys (X : ℚ[X])).map (scaleU p)) b) :
    GLE p (W.price + (Fintype.card ι - S.card))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  rw [fullN_member_eq_submatrix]
  apply gle_submatrix_of_scaleU
  have hS : S.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ S
  have h := W.gle_submatrix_debit (memberEmbedding S) (memberEmbedding S)
    (by simp only [Fintype.card_sum, Fintype.card_coe]; omega)
  refine h.mono ?_
  simp only [Fintype.card_sum, Fintype.card_coe]
  omega

end CatalanCore.Uniform.Content.UFMember
