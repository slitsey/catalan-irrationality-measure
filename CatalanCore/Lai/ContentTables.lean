module

public import CatalanCore.Content.PartialSums
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# `CatalanCore.Lai.ContentTables`: the cells of Theorem C01 (rows LC25, LC26)

Paper: `N9-LAI-CONTENT-EXACT-2026-11-16.md`, Theorem C01, steps 1-5.

* `c01Num r q t` : the law's integrand `Num` in the cell `q = ⌊6x⌋`, `t = {6x}`, from the class masses
  `A, B, C, D` (a definition, not a table);
* `c01_piece_ident` (**LC25**): on each of the 22 pieces `Num = c₀(q) + c₁(q) x`, symbolic in `q`;
* `c01_cells_sum` (**LC26**): for `m ≥ 1` the 22 cell integrals `∫ Num/x³ dx` at `q = 6m + r`
  (`r < 6`) sum to `∑_e d_e/(m + e)` over the 23 nodes (all `1/x_e²` coefficients cancel);
* `c01_nodeF_eq`: the summand `f(m) = -∑_e d_e/(m+e)` of `Content.PartialSums` is minus that sum.
-/

set_option linter.deprecated false

namespace CatalanCore.Lai

section C01

open Set MeasureTheory

/-- One piece of the law's integrand on `y ∈ (0, 1]`: for `q ≡ r (mod 6)` and `t = {6x} ∈ (lo, hi)`,
`Num = c₀(q) + c₁(q) x` with `c₀ = a + b q + q²/2` and `c₁ = g - 3 q`. -/
structure C01Piece where
  r : ℕ
  lo : ℝ
  hi : ℝ
  a : ℝ
  b : ℝ
  g : ℝ

/-- **The law's integrand in the cell `q = ⌊6x⌋`, `t = {6x}`** (content note `N9-LAI-CONTENT-EXACT`,
Theorem C01 steps 1-2). `r = q mod 6` fixes `ρ = q mod 3`, `q mod 2` and the parity of `λ = q + ρ - 3`;
the four class masses `A, B, C, D` are the residue fractions with `σ = 0, 3, 2, 5`; `N` is the pair of
non-tie classes (`{B, D}` for even `λ`, `{A, C}` for odd `λ`); `μ_c = (λ + 4 + [c ∈ N] - σ_c)/2`;
`Num = tot - 9x² + 3x - θ(1-θ) + x₁ + x₂` with `x = (q+t)/6`, `θ = ((q mod 2) + t)/2`,
`x₁ = |m_X - m_Y|/2`, `x₂ = (x₁ - m_N)₊`. Valid for every real `q` with the discrete data of `r`. -/
noncomputable def c01Num (r : ℕ) (q t : ℝ) : ℝ :=
  let ρ : ℝ := ((r % 3 : ℕ) : ℝ)
  let qb : ℝ := ((r % 2 : ℕ) : ℝ)
  let lam : ℝ := q + ρ - 3
  let c : ℝ := 1 - (ρ + t) / 3
  let mA : ℝ := if t < (3 - ρ) / 4 then t else c
  let mB : ℝ := if t < (3 - ρ) / 4 then 0 else t - c
  let mC : ℝ := if t < (3 - ρ) / 4 then c - t else 0
  let mD : ℝ := if t < (3 - ρ) / 4 then (ρ + t) / 3 else 1 - t
  let nA : ℝ := if (r + r % 3) % 2 = 1 then 0 else 1
  let nB : ℝ := 1 - nA
  let mN : ℝ := nB * (mB + mD) + nA * (mA + mC)
  let dif : ℝ := if (r + r % 3) % 2 = 1 then mA - mC else mB - mD
  let d : ℝ := (1 - mN) / 2
  let muA : ℝ := (lam + 4 + nA - 0) / 2
  let muB : ℝ := (lam + 4 + nB - 3) / 2
  let muC : ℝ := (lam + 4 + nA - 2) / 2
  let muD : ℝ := (lam + 4 + nB - 5) / 2
  let tot : ℝ := d * lam + mA * (muA ^ 2 + (0 - 5) * muA) + mB * (muB ^ 2 + (3 - 5) * muB) +
    mC * (muC ^ 2 + (2 - 5) * muC) + mD * (muD ^ 2 + (5 - 5) * muD)
  let x : ℝ := (q + t) / 6
  let th : ℝ := (qb + t) / 2
  let x1 : ℝ := |dif| / 2
  let x2 : ℝ := max (x1 - mN) 0
  tot - 9 * x ^ 2 + 3 * x - th * (1 - th) + x1 + x2

/-- The 22 pieces of the law's integrand on `y ∈ (0, 1]` (content note `N9-LAI-CONTENT-EXACT`, Theorem C01
step 3): `r = q mod 6`, the `t`-interval `(lo, hi)`, and `Num = c₀(q) + c₁(q) x` with
`c₀ = α + β q + q²/2`, `c₁ = γ - 3 q`. -/
noncomputable def c01Piece : ℕ → C01Piece
  | 0 => ⟨0, (0 : ℝ), ((3 : ℝ) / 4), (0 : ℝ), (2 : ℝ), (-18 : ℝ)⟩
  | 1 => ⟨0, ((3 : ℝ) / 4), ((6 : ℝ) / 7), (-2 : ℝ), ((-2 : ℝ) / 3), (-2 : ℝ)⟩
  | 2 => ⟨0, ((6 : ℝ) / 7), (1 : ℝ), (-4 : ℝ), (-3 : ℝ), (12 : ℝ)⟩
  | 3 => ⟨1, (0 : ℝ), ((1 : ℝ) / 2), ((-1 : ℝ) / 2), (2 : ℝ), (-15 : ℝ)⟩
  | 4 => ⟨1, ((1 : ℝ) / 2), ((5 : ℝ) / 7), ((-11 : ℝ) / 6), ((-2 : ℝ) / 3), (1 : ℝ)⟩
  | 5 => ⟨1, ((5 : ℝ) / 7), (1 : ℝ), ((-7 : ℝ) / 2), (-3 : ℝ), (15 : ℝ)⟩
  | 6 => ⟨2, (0 : ℝ), ((1 : ℝ) / 4), (0 : ℝ), ((5 : ℝ) / 2), (-15 : ℝ)⟩
  | 7 => ⟨2, ((1 : ℝ) / 4), ((2 : ℝ) / 5), ((-1 : ℝ) / 3), ((7 : ℝ) / 6), (-7 : ℝ)⟩
  | 8 => ⟨2, ((2 : ℝ) / 5), ((4 : ℝ) / 7), ((-2 : ℝ) / 3), ((1 : ℝ) / 3), (-2 : ℝ)⟩
  | 9 => ⟨2, ((4 : ℝ) / 7), ((2 : ℝ) / 3), (-2 : ℝ), (-2 : ℝ), (12 : ℝ)⟩
  | 10 => ⟨2, ((2 : ℝ) / 3), (1 : ℝ), (-3 : ℝ), ((-7 : ℝ) / 2), (21 : ℝ)⟩
  | 11 => ⟨3, (0 : ℝ), ((1 : ℝ) / 3), (1 : ℝ), ((9 : ℝ) / 2), (-33 : ℝ)⟩
  | 12 => ⟨3, ((1 : ℝ) / 3), ((3 : ℝ) / 7), ((1 : ℝ) / 2), (3 : ℝ), (-24 : ℝ)⟩
  | 13 => ⟨3, ((3 : ℝ) / 7), ((3 : ℝ) / 5), ((-1 : ℝ) / 2), ((2 : ℝ) / 3), (-10 : ℝ)⟩
  | 14 => ⟨3, ((3 : ℝ) / 5), ((3 : ℝ) / 4), (-1 : ℝ), ((-1 : ℝ) / 6), (-5 : ℝ)⟩
  | 15 => ⟨3, ((3 : ℝ) / 4), (1 : ℝ), (-2 : ℝ), ((-3 : ℝ) / 2), (3 : ℝ)⟩
  | 16 => ⟨4, (0 : ℝ), ((2 : ℝ) / 7), (0 : ℝ), (4 : ℝ), (-27 : ℝ)⟩
  | 17 => ⟨4, ((2 : ℝ) / 7), ((1 : ℝ) / 2), ((-2 : ℝ) / 3), ((5 : ℝ) / 3), (-13 : ℝ)⟩
  | 18 => ⟨4, ((1 : ℝ) / 2), (1 : ℝ), (-2 : ℝ), (-1 : ℝ), (3 : ℝ)⟩
  | 19 => ⟨5, (0 : ℝ), ((1 : ℝ) / 7), ((-1 : ℝ) / 2), (4 : ℝ), (-24 : ℝ)⟩
  | 20 => ⟨5, ((1 : ℝ) / 7), ((1 : ℝ) / 4), ((-5 : ℝ) / 6), ((5 : ℝ) / 3), (-10 : ℝ)⟩
  | 21 => ⟨5, ((1 : ℝ) / 4), (1 : ℝ), ((-3 : ℝ) / 2), (-1 : ℝ), (6 : ℝ)⟩
  | _ => ⟨0, 0, 0, 0, 0, 0⟩

/-- The 23 nodes `e` of the table of Theorem C01 (as rationals). -/
def c01Eq : ℕ → ℚ
  | 0 => (0 : ℚ)
  | 1 => ((1 : ℚ) / 8)
  | 2 => ((1 : ℚ) / 7)
  | 3 => ((1 : ℚ) / 6)
  | 4 => ((1 : ℚ) / 4)
  | 5 => ((2 : ℚ) / 7)
  | 6 => ((1 : ℚ) / 3)
  | 7 => ((3 : ℚ) / 8)
  | 8 => ((2 : ℚ) / 5)
  | 9 => ((3 : ℚ) / 7)
  | 10 => ((4 : ℚ) / 9)
  | 11 => ((1 : ℚ) / 2)
  | 12 => ((5 : ℚ) / 9)
  | 13 => ((4 : ℚ) / 7)
  | 14 => ((3 : ℚ) / 5)
  | 15 => ((5 : ℚ) / 8)
  | 16 => ((2 : ℚ) / 3)
  | 17 => ((5 : ℚ) / 7)
  | 18 => ((3 : ℚ) / 4)
  | 19 => ((5 : ℚ) / 6)
  | 20 => ((6 : ℚ) / 7)
  | 21 => ((7 : ℚ) / 8)
  | 22 => (1 : ℚ)
  | _ => 0

/-- The weights `d_e` of the table of Theorem C01. -/
def c01Dq : ℕ → ℚ
  | 0 => (-12 : ℚ)
  | 1 => (8 : ℚ)
  | 2 => (7 : ℚ)
  | 3 => (-12 : ℚ)
  | 4 => (8 : ℚ)
  | 5 => (7 : ℚ)
  | 6 => ((-27 : ℚ) / 2)
  | 7 => (4 : ℚ)
  | 8 => ((5 : ℚ) / 2)
  | 9 => (7 : ℚ)
  | 10 => ((9 : ℚ) / 2)
  | 11 => (-30 : ℚ)
  | 12 => ((9 : ℚ) / 2)
  | 13 => (7 : ℚ)
  | 14 => ((5 : ℚ) / 2)
  | 15 => (4 : ℚ)
  | 16 => ((-27 : ℚ) / 2)
  | 17 => (7 : ℚ)
  | 18 => (8 : ℚ)
  | 19 => (-12 : ℚ)
  | 20 => (7 : ℚ)
  | 21 => (8 : ℚ)
  | 22 => (-3 : ℚ)
  | _ => 0


theorem c01_piece_0 (q t : ℝ) (h1 : (c01Piece 0).lo < t) (h2 : t < (c01Piece 0).hi) :
    c01Num (c01Piece 0).r q t =
      ((c01Piece 0).a + (c01Piece 0).b * q + q ^ 2 / 2) + ((c01Piece 0).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_1 (q t : ℝ) (h1 : (c01Piece 1).lo < t) (h2 : t < (c01Piece 1).hi) :
    c01Num (c01Piece 1).r q t =
      ((c01Piece 1).a + (c01Piece 1).b * q + q ^ 2 / 2) + ((c01Piece 1).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_2 (q t : ℝ) (h1 : (c01Piece 2).lo < t) (h2 : t < (c01Piece 2).hi) :
    c01Num (c01Piece 2).r q t =
      ((c01Piece 2).a + (c01Piece 2).b * q + q ^ 2 / 2) + ((c01Piece 2).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_3 (q t : ℝ) (h1 : (c01Piece 3).lo < t) (h2 : t < (c01Piece 3).hi) :
    c01Num (c01Piece 3).r q t =
      ((c01Piece 3).a + (c01Piece 3).b * q + q ^ 2 / 2) + ((c01Piece 3).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_4 (q t : ℝ) (h1 : (c01Piece 4).lo < t) (h2 : t < (c01Piece 4).hi) :
    c01Num (c01Piece 4).r q t =
      ((c01Piece 4).a + (c01Piece 4).b * q + q ^ 2 / 2) + ((c01Piece 4).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_5 (q t : ℝ) (h1 : (c01Piece 5).lo < t) (h2 : t < (c01Piece 5).hi) :
    c01Num (c01Piece 5).r q t =
      ((c01Piece 5).a + (c01Piece 5).b * q + q ^ 2 / 2) + ((c01Piece 5).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_6 (q t : ℝ) (h1 : (c01Piece 6).lo < t) (h2 : t < (c01Piece 6).hi) :
    c01Num (c01Piece 6).r q t =
      ((c01Piece 6).a + (c01Piece 6).b * q + q ^ 2 / 2) + ((c01Piece 6).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_7 (q t : ℝ) (h1 : (c01Piece 7).lo < t) (h2 : t < (c01Piece 7).hi) :
    c01Num (c01Piece 7).r q t =
      ((c01Piece 7).a + (c01Piece 7).b * q + q ^ 2 / 2) + ((c01Piece 7).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_8 (q t : ℝ) (h1 : (c01Piece 8).lo < t) (h2 : t < (c01Piece 8).hi) :
    c01Num (c01Piece 8).r q t =
      ((c01Piece 8).a + (c01Piece 8).b * q + q ^ 2 / 2) + ((c01Piece 8).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_9 (q t : ℝ) (h1 : (c01Piece 9).lo < t) (h2 : t < (c01Piece 9).hi) :
    c01Num (c01Piece 9).r q t =
      ((c01Piece 9).a + (c01Piece 9).b * q + q ^ 2 / 2) + ((c01Piece 9).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_10 (q t : ℝ) (h1 : (c01Piece 10).lo < t) (h2 : t < (c01Piece 10).hi) :
    c01Num (c01Piece 10).r q t =
      ((c01Piece 10).a + (c01Piece 10).b * q + q ^ 2 / 2) + ((c01Piece 10).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_11 (q t : ℝ) (h1 : (c01Piece 11).lo < t) (h2 : t < (c01Piece 11).hi) :
    c01Num (c01Piece 11).r q t =
      ((c01Piece 11).a + (c01Piece 11).b * q + q ^ 2 / 2) + ((c01Piece 11).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_12 (q t : ℝ) (h1 : (c01Piece 12).lo < t) (h2 : t < (c01Piece 12).hi) :
    c01Num (c01Piece 12).r q t =
      ((c01Piece 12).a + (c01Piece 12).b * q + q ^ 2 / 2) + ((c01Piece 12).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_13 (q t : ℝ) (h1 : (c01Piece 13).lo < t) (h2 : t < (c01Piece 13).hi) :
    c01Num (c01Piece 13).r q t =
      ((c01Piece 13).a + (c01Piece 13).b * q + q ^ 2 / 2) + ((c01Piece 13).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_14 (q t : ℝ) (h1 : (c01Piece 14).lo < t) (h2 : t < (c01Piece 14).hi) :
    c01Num (c01Piece 14).r q t =
      ((c01Piece 14).a + (c01Piece 14).b * q + q ^ 2 / 2) + ((c01Piece 14).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_15 (q t : ℝ) (h1 : (c01Piece 15).lo < t) (h2 : t < (c01Piece 15).hi) :
    c01Num (c01Piece 15).r q t =
      ((c01Piece 15).a + (c01Piece 15).b * q + q ^ 2 / 2) + ((c01Piece 15).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_16 (q t : ℝ) (h1 : (c01Piece 16).lo < t) (h2 : t < (c01Piece 16).hi) :
    c01Num (c01Piece 16).r q t =
      ((c01Piece 16).a + (c01Piece 16).b * q + q ^ 2 / 2) + ((c01Piece 16).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_17 (q t : ℝ) (h1 : (c01Piece 17).lo < t) (h2 : t < (c01Piece 17).hi) :
    c01Num (c01Piece 17).r q t =
      ((c01Piece 17).a + (c01Piece 17).b * q + q ^ 2 / 2) + ((c01Piece 17).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_18 (q t : ℝ) (h1 : (c01Piece 18).lo < t) (h2 : t < (c01Piece 18).hi) :
    c01Num (c01Piece 18).r q t =
      ((c01Piece 18).a + (c01Piece 18).b * q + q ^ 2 / 2) + ((c01Piece 18).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_19 (q t : ℝ) (h1 : (c01Piece 19).lo < t) (h2 : t < (c01Piece 19).hi) :
    c01Num (c01Piece 19).r q t =
      ((c01Piece 19).a + (c01Piece 19).b * q + q ^ 2 / 2) + ((c01Piece 19).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_20 (q t : ℝ) (h1 : (c01Piece 20).lo < t) (h2 : t < (c01Piece 20).hi) :
    c01Num (c01Piece 20).r q t =
      ((c01Piece 20).a + (c01Piece 20).b * q + q ^ 2 / 2) + ((c01Piece 20).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

theorem c01_piece_21 (q t : ℝ) (h1 : (c01Piece 21).lo < t) (h2 : t < (c01Piece 21).hi) :
    c01Num (c01Piece 21).r q t =
      ((c01Piece 21).a + (c01Piece 21).b * q + q ^ 2 / 2) + ((c01Piece 21).g - 3 * q) * ((q + t) / 6) := by
  simp only [c01Piece] at h1 h2 ⊢
  simp only [c01Num, abs_eq_max_neg, max_def]
  norm_num
  split_ifs <;> first | (exfalso; linarith) | ring

/-- **LC25.** The 22 piece identities `Num = c₀(q) + c₁(q) x`, symbolic in `q`. -/
theorem c01_piece_ident (j : ℕ) (hj : j < 22) (q t : ℝ) (h1 : (c01Piece j).lo < t)
    (h2 : t < (c01Piece j).hi) :
    c01Num (c01Piece j).r q t =
      ((c01Piece j).a + (c01Piece j).b * q + q ^ 2 / 2) + ((c01Piece j).g - 3 * q) * ((q + t) / 6) := by
  interval_cases j
  · exact c01_piece_0 q t h1 h2
  · exact c01_piece_1 q t h1 h2
  · exact c01_piece_2 q t h1 h2
  · exact c01_piece_3 q t h1 h2
  · exact c01_piece_4 q t h1 h2
  · exact c01_piece_5 q t h1 h2
  · exact c01_piece_6 q t h1 h2
  · exact c01_piece_7 q t h1 h2
  · exact c01_piece_8 q t h1 h2
  · exact c01_piece_9 q t h1 h2
  · exact c01_piece_10 q t h1 h2
  · exact c01_piece_11 q t h1 h2
  · exact c01_piece_12 q t h1 h2
  · exact c01_piece_13 q t h1 h2
  · exact c01_piece_14 q t h1 h2
  · exact c01_piece_15 q t h1 h2
  · exact c01_piece_16 q t h1 h2
  · exact c01_piece_17 q t h1 h2
  · exact c01_piece_18 q t h1 h2
  · exact c01_piece_19 q t h1 h2
  · exact c01_piece_20 q t h1 h2
  · exact c01_piece_21 q t h1 h2


/-- The `t`-intervals of the 22 pieces lie in `[0, 1]`, are nonempty, and `r < 6`. -/
theorem c01_piece_bounds (j : ℕ) (hj : j < 22) :
    0 ≤ (c01Piece j).lo ∧ (c01Piece j).lo < (c01Piece j).hi ∧ (c01Piece j).hi ≤ 1 ∧
      (c01Piece j).r < 6 := by
  interval_cases j <;> simp only [c01Piece] <;> norm_num

/-- `∫_{xa}^{xb} (c₀ + c₁ x)/x³ dx = [-c₀/(2x²) - c₁/x]`. -/
theorem integral_cell (c0 c1 xa xb : ℝ) (h0 : 0 < xa) (hab : xa ≤ xb) :
    ∫ x in xa..xb, (c0 + c1 * x) / x ^ 3 =
      (-c0 / (2 * xb ^ 2) - c1 / xb) - (-c0 / (2 * xa ^ 2) - c1 / xa) := by
  have hpos : ∀ x ∈ uIcc xa xb, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact lt_of_lt_of_le h0 hx.1
  have hderiv : ∀ x ∈ uIcc xa xb,
      HasDerivAt (fun x : ℝ => -c0 / (2 * x ^ 2) - c1 / x) ((c0 + c1 * x) / x ^ 3) x := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have h1 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul 2)
    have h2 := (hasDerivAt_const x (-c0)).div h1 (by positivity)
    have h3 := (hasDerivAt_const x c1).div (hasDerivAt_id x) hx0.ne'
    have h4 : HasDerivAt (fun x : ℝ => -c0 / (2 * x ^ 2) - c1 / x)
        ((0 * (2 * x ^ 2) - -c0 * (2 * (2 * x))) / (2 * x ^ 2) ^ 2 - (0 * x - c1 * 1) / x ^ 2) x :=
      h2.sub h3
    refine h4.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (c0 + c1 * x) / x ^ 3) volume xa xb := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    have := hpos x hx
    positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The cell integral of piece `j` at `q = 6m + r`: `∫ Num/x³ dx` over the `x`-interval of the piece. -/
noncomputable def c01CellInt (m j : ℕ) : ℝ :=
  ∫ x in ((m : ℝ) + ((c01Piece j).r + (c01Piece j).lo) / 6)..((m : ℝ) + ((c01Piece j).r + (c01Piece j).hi) / 6),
    c01Num (c01Piece j).r (6 * m + (c01Piece j).r) (6 * x - (6 * m + (c01Piece j).r)) / x ^ 3

/-- The endpoint term: with `q = 6x - t`, `-c₀/(2x²) - c₁/x = 9 - (3b + g)/x - (a - b t + t²/2)/(2x²)`. -/
noncomputable def c01End (P : C01Piece) (x t : ℝ) : ℝ :=
  9 - (3 * P.b + P.g) / x - (P.a - P.b * t + t ^ 2 / 2) / (2 * x ^ 2)

theorem endpoint_alg (a b g q t x : ℝ) (hx : x ≠ 0) (hq : q = 6 * x - t) :
    -(a + b * q + q ^ 2 / 2) / (2 * x ^ 2) - (g - 3 * q) / x =
      9 - (3 * b + g) / x - (a - b * t + t ^ 2 / 2) / (2 * x ^ 2) := by
  subst hq
  field_simp
  ring

theorem c01_cell_eval (m j : ℕ) (hm : 1 ≤ m) (hj : j < 22) :
    c01CellInt m j =
      c01End (c01Piece j) ((m : ℝ) + ((c01Piece j).r + (c01Piece j).hi) / 6) (c01Piece j).hi -
        c01End (c01Piece j) ((m : ℝ) + ((c01Piece j).r + (c01Piece j).lo) / 6) (c01Piece j).lo := by
  obtain ⟨hlo0, hlohi, hhi1, hr6⟩ := c01_piece_bounds j hj
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ (c01Piece j).r := Nat.cast_nonneg _
  have hxa0 : 0 < (m : ℝ) + ((c01Piece j).r + (c01Piece j).lo) / 6 := by linarith
  have hab : (m : ℝ) + ((c01Piece j).r + (c01Piece j).lo) / 6 ≤
      (m : ℝ) + ((c01Piece j).r + (c01Piece j).hi) / 6 := by linarith
  have hcongr : c01CellInt m j = ∫ x in ((m : ℝ) + ((c01Piece j).r + (c01Piece j).lo) / 6)..
        ((m : ℝ) + ((c01Piece j).r + (c01Piece j).hi) / 6),
      (((c01Piece j).a + (c01Piece j).b * (6 * m + (c01Piece j).r) + (6 * m + (c01Piece j).r) ^ 2 / 2) +
        ((c01Piece j).g - 3 * (6 * m + (c01Piece j).r)) * x) / x ^ 3 := by
    unfold c01CellInt
    refine intervalIntegral.integral_congr_uIoo (fun x hx => ?_)
    rw [uIoo_of_le hab] at hx
    have ht1 : (c01Piece j).lo < 6 * x - (6 * m + (c01Piece j).r) := by linarith [hx.1]
    have ht2 : 6 * x - (6 * m + (c01Piece j).r) < (c01Piece j).hi := by linarith [hx.2]
    rw [c01_piece_ident j hj _ _ ht1 ht2]
    congr 1
    ring
  rw [hcongr, integral_cell _ _ _ _ hxa0 hab]
  unfold c01End
  have hxb0 : (m : ℝ) + ((c01Piece j).r + (c01Piece j).hi) / 6 ≠ 0 := by
    have : 0 < (m : ℝ) + ((c01Piece j).r + (c01Piece j).hi) / 6 := by linarith
    exact this.ne'
  rw [endpoint_alg _ _ _ _ (c01Piece j).hi _ hxb0 (by ring),
    endpoint_alg _ _ _ _ (c01Piece j).lo _ hxa0.ne' (by ring)]

theorem c01Dq_sum : ∑ i ∈ Finset.range 23, c01Dq i = 0 := by
  simp [Finset.sum_range_succ, c01Dq]
  norm_num

theorem c01_moment : ∑ i ∈ Finset.range 23, c01Dq i * c01Eq i = 9 / 2 := by
  simp [Finset.sum_range_succ, c01Dq, c01Eq]
  norm_num

set_option maxHeartbeats 1600000 in
/-- **LC26.** For every `m ≥ 1` the 22 cell integrals of the law's integrand at `q = 6m + r`
(`r < 6`) sum to `∑_e d_e / (m + e)` over the 23 nodes (every `1/x_e²` coefficient cancels). -/
theorem c01_cells_sum (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range 22, c01CellInt m j =
      ∑ i ∈ Finset.range 23, (c01Dq i : ℝ) / ((m : ℝ) + (c01Eq i : ℝ)) := by
  rw [Finset.sum_congr rfl (fun j hj => c01_cell_eval m j hm (Finset.mem_range.1 hj))]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c01End, c01Piece, c01Dq, c01Eq]
  push_cast
  ring

/-- `Fin 23` form of `c01_cells_sum`. -/
theorem c01_cells_sum_fin (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range 22, c01CellInt m j =
      ∑ i : Fin 23, (c01Dq i : ℝ) / ((m : ℝ) + (c01Eq i : ℝ)) := by
  rw [c01_cells_sum m hm, Finset.sum_range]

/-- The law's contribution of the cells `q = 6m + r` is `f(m) = -Σ_e d_e/(m+e)`, the summand of
`Content.PartialSums` (`S_M = Σ_{1 ≤ m < M} f(m)`): `f m = -(Σ_j ∫_{cell j} Num/x³)`. -/
theorem c01_nodeF_eq (m : ℕ) (hm : 1 ≤ m) :
    ((CatalanCore.Content.PartialSums.nodeF (fun i : Fin 23 => c01Eq i)
        (fun i : Fin 23 => c01Dq i) m : ℚ) : ℝ) = -∑ j ∈ Finset.range 22, c01CellInt m j := by
  rw [c01_cells_sum_fin m hm]
  unfold CatalanCore.Content.PartialSums.nodeF
  push_cast
  rfl

end C01

end CatalanCore.Lai

#print axioms CatalanCore.Lai.c01_piece_ident
#print axioms CatalanCore.Lai.c01_cells_sum
#print axioms CatalanCore.Lai.c01_cells_sum_fin
#print axioms CatalanCore.Lai.c01_nodeF_eq
#print axioms CatalanCore.Lai.c01Dq_sum
#print axioms CatalanCore.Lai.c01_moment
