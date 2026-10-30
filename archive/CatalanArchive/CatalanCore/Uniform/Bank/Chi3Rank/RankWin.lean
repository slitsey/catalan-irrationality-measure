import CatalanCore.Uniform.Bank.Chi3Rank.RankContent
set_option Elab.async false

/-! # Class sums of the rank-refined weight (lane H, H16)

At scales `r = 4 m` the weight `Wn2 = min (Wsharp, eExp2)` is covered, in addition to the pieces of
B3c, by the rank pieces

* class `1 (6)`: `7/2 - 2θ` on `[5/8, 2/3]`, `5/2 - θ/2` on `[2/3, 3/4]`, `1 + 3θ/2` on `[3/4, 5/6]`;
* class `5 (6)`: `5/2 - θ/2` on `[1/2, 3/5]`, `1 + 2θ` on `[3/5, 5/8]`;

which lowers the class integrals by `1/64` and `1/320`, so
`Λ' = Λ - 3/320 = 4733759984905769/1155228423148800`. -/

open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.P6 CatalanFrames.P6Hybrid CatalanFrames.P6Hybrid.Quarter
  CatalanFrames.P6Hybrid.Quarter.Periodic CatalanCore.Uniform.Bank.Chi3Content

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

namespace CatalanCore.Uniform.Bank.Chi3Rank

/-- Admissible scales: the quarter band with `r = 4 m`. -/
def AdmR (r m : ℕ) : Prop := Quarter.Adm r m ∧ r = 4 * m

/-- Lower bound for the scale: all primes of the rank windows exceed `N0`. -/
def R0 : ℕ := 1000000

noncomputable def Wn2 (r m p : ℕ) : ℕ := min (Wsharp r m p) (eExp2 r m p)

theorem Wn2_le_Wn (r m p : ℕ) : Wn2 r m p ≤ Chi3Content.Wn r m p :=
  min_le_min_left _ (eExp2_le r m p)

theorem Wn2_le_sharp (r m p : ℕ) : Wn2 r m p ≤ Wsharp r m p := min_le_left _ _

theorem Wn2_le_e (r m p : ℕ) : Wn2 r m p ≤ eExp2 r m p := min_le_right _ _

theorem rankExp_le_bound1 (base r m p : ℕ)
    (h : p.Prime ∧ r = 4 * m ∧ N0 < p ∧ r ≤ 2 * p ∧ p < r ∧ p % 6 = 1) :
    rankExp base r m p ≤ rankBound1 r m p := by
  unfold rankExp
  rw [if_pos h]
  exact min_le_right _ _

theorem rankExp_le_bound5 (base r m p : ℕ)
    (h : p.Prime ∧ r = 4 * m ∧ N0 < p ∧ r ≤ 2 * p ∧ p % 6 = 5) :
    rankExp base r m p ≤ rankBound5 r m p := by
  have h1 : ¬ (p.Prime ∧ r = 4 * m ∧ N0 < p ∧ r ≤ 2 * p ∧ p < r ∧ p % 6 = 1) := by
    intro ⟨_, _, _, _, _, h6⟩; omega
  unfold rankExp
  rw [if_neg h1, if_pos h]
  exact min_le_right _ _

theorem covers_sub {c : ZMod 6} {w : ℕ → ℝ} {r : ℕ} {P P' : Piece} (hs : P.s ≤ P'.s)
    (ht : P'.t ≤ P.t) (hα : P'.α = P.α) (hβ : P'.β = P.β) (hC : P'.C = P.C)
    (h : Covers c w r P) : Covers c w r P' := by
  intro p h1 h2 h3 h4
  have e1 : ⌊P.s * r⌋₊ ≤ ⌊P'.s * r⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))
  have e2 : ⌊P'.t * r⌋₊ ≤ ⌊P.t * r⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))
  have := h p (lt_of_le_of_lt e1 h1) (le_trans h2 e2) h3 h4
  rwa [hα, hβ, hC]

/-! ### The rank pieces -/

noncomputable def P1a : Piece := mkPiece 1 2 5 8 9 0 100 4
noncomputable def P1b : Piece := mkPiece 5 8 2 3 7 (-4) 200 2
noncomputable def P1c : Piece := mkPiece 2 3 3 4 5 (-1) 200 2
noncomputable def P1d : Piece := mkPiece 3 4 5 6 2 3 200 2
noncomputable def P1e : Piece := mkPiece 5 6 15 16 9 0 100 4

noncomputable def P5a : Piece := mkPiece 1 2 3 5 5 (-1) 200 2
noncomputable def P5b : Piece := mkPiece 3 5 5 8 1 2 100 1
noncomputable def P5c : Piece := mkPiece 5 8 3 4 9 0 100 4
noncomputable def P5d : Piece := mkPiece 3 4 5 6 9 0 100 4

theorem cov_P1b {r m : ℕ} (hr4 : r = 4 * m) (hr : R0 ≤ r) :
    Covers (1 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P1b := by
  intro p h1 h2 hpp hpc
  unfold P1b at h1 h2 ⊢
  rw [floor_mk_s] at h1
  rw [floor_mk_t] at h2
  have h6 : p % 6 = 1 := cls_one hpc
  have hN : N0 < p := by unfold N0 R0 at *; omega
  have hb := (Wn2_le_e r m p).trans (rankExp_le_bound1 _ r m p
    ⟨hpp, hr4, hN, by omega, by omega, h6⟩)
  unfold rankBound1 at hb
  have key : 2 * Wn2 r m p + 4 * p ≤ 7 * r + 200 := by omega
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  simp only [mkPiece]; push_cast; linarith

theorem cov_P1c {r m : ℕ} (hr4 : r = 4 * m) (hr : R0 ≤ r) :
    Covers (1 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P1c := by
  intro p h1 h2 hpp hpc
  unfold P1c at h1 h2 ⊢
  rw [floor_mk_s] at h1
  rw [floor_mk_t] at h2
  have h6 : p % 6 = 1 := cls_one hpc
  have hN : N0 < p := by unfold N0 R0 at *; omega
  have hb := (Wn2_le_e r m p).trans (rankExp_le_bound1 _ r m p
    ⟨hpp, hr4, hN, by omega, by omega, h6⟩)
  unfold rankBound1 at hb
  have key : 2 * Wn2 r m p + p ≤ 5 * r + 200 := by omega
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  simp only [mkPiece]; push_cast; linarith

theorem cov_P1d {r m : ℕ} (hr4 : r = 4 * m) (hr : R0 ≤ r) :
    Covers (1 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P1d := by
  intro p h1 h2 hpp hpc
  unfold P1d at h1 h2 ⊢
  rw [floor_mk_s] at h1
  rw [floor_mk_t] at h2
  have h6 : p % 6 = 1 := cls_one hpc
  have hN : N0 < p := by unfold N0 R0 at *; omega
  have hb := (Wn2_le_e r m p).trans (rankExp_le_bound1 _ r m p
    ⟨hpp, hr4, hN, by omega, by omega, h6⟩)
  unfold rankBound1 at hb
  have key2 : 2 * Wn2 r m p ≤ 2 * r + 3 * p + 200 := by omega
  have := (Nat.cast_le (α := ℝ)).2 key2
  push_cast at this
  simp only [mkPiece]; push_cast; linarith

theorem cov_P5a {r m : ℕ} (hr4 : r = 4 * m) (hr : R0 ≤ r) :
    Covers (5 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P5a := by
  intro p h1 h2 hpp hpc
  unfold P5a at h1 h2 ⊢
  rw [floor_mk_s] at h1
  rw [floor_mk_t] at h2
  have h6 : p % 6 = 5 := cls_five hpc
  have hN : N0 < p := by unfold N0 R0 at *; omega
  have hb := (Wn2_le_e r m p).trans (rankExp_le_bound5 _ r m p
    ⟨hpp, hr4, hN, by omega, h6⟩)
  unfold rankBound5 at hb
  have key : 2 * Wn2 r m p + p ≤ 5 * r + 200 := by omega
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  simp only [mkPiece]; push_cast; linarith

theorem cov_P5b {r m : ℕ} (hr4 : r = 4 * m) (hr : R0 ≤ r) :
    Covers (5 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P5b := by
  intro p h1 h2 hpp hpc
  unfold P5b at h1 h2 ⊢
  rw [floor_mk_s] at h1
  rw [floor_mk_t] at h2
  have h6 : p % 6 = 5 := cls_five hpc
  have hN : N0 < p := by unfold N0 R0 at *; omega
  have hb := (Wn2_le_e r m p).trans (rankExp_le_bound5 _ r m p
    ⟨hpp, hr4, hN, by omega, h6⟩)
  unfold rankBound5 at hb
  have key : Wn2 r m p ≤ r + 2 * p + 100 := by omega
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  simp only [mkPiece]; push_cast; linarith

end CatalanCore.Uniform.Bank.Chi3Rank
