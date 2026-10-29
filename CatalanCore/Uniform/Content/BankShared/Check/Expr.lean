import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option Elab.async false

/-! # The expression class of explicit layer prices and its homogenisation (lane C1L)

C1/PAPER.md §2.1.  A layer price is an integer expression in `r, p, m, k` built from constants, `+`,
multiplication by constants, truncated subtraction, `min`, `max`, the distance `δ_p(X)` of `X` to `pℤ`,
and the exact quotients `p ⌊r/p⌋`, `r mod p` (`Expr`, evaluated by `Expr.evalN`).

* `Expr.evalR c R P M K`: the real version (constants kept when `c = true`, dropped otherwise), with
  `δ_P(X) = P · latDist (X / P)`, `latDist x = min (fract x) (1 - fract x)`;
* `evalN_cast`: at `p > 0` the integer value is the real value with constants;
* **Lemma 1** `evalR_err`: changing `m` by at most `1/2` and `k` by at most `ε`, and dropping the constants,
  changes the value by at most `Expr.err ε e`;
* `evalR_hom`: without constants the real version is positively homogeneous of degree one;
* `evalN_le_prof`: `τ(r, p, m, k) ≤ r · prof (p / r) + E(τ)`, `prof θ = τ̂(1, θ, α, κθ)`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check

/-- Expressions of the class `𝔈` in the variables `r, p, m, k`. -/
inductive Expr where
  | vr
  | vp
  | vm
  | vk
  | cst (c : ℕ)
  | add (a b : Expr)
  | smul (c : ℕ) (a : Expr)
  | tsub (a b : Expr)
  | mn (a b : Expr)
  | mx (a b : Expr)
  | dist (a : Expr)
  | ap
  | sp

/-- The distance of a real number to `ℤ`. -/
noncomputable def latDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

namespace Expr

/-- The integer value at `(r, p, m, k)`. -/
def evalN (r p m k : ℕ) : Expr → ℕ
  | vr => r
  | vp => p
  | vm => m
  | vk => k
  | cst c => c
  | add a b => evalN r p m k a + evalN r p m k b
  | smul c a => c * evalN r p m k a
  | tsub a b => evalN r p m k a - evalN r p m k b
  | mn a b => min (evalN r p m k a) (evalN r p m k b)
  | mx a b => max (evalN r p m k a) (evalN r p m k b)
  | dist a => min (evalN r p m k a % p) (p - evalN r p m k a % p)
  | ap => p * (r / p)
  | sp => r % p

/-- The real version at real `(R, P, M, K)`; constants are kept iff `c`. -/
noncomputable def evalR (c : Bool) (R P M K : ℝ) : Expr → ℝ
  | vr => R
  | vp => P
  | vm => M
  | vk => K
  | cst n => if c then (n : ℝ) else 0
  | add a b => evalR c R P M K a + evalR c R P M K b
  | smul n a => (n : ℝ) * evalR c R P M K a
  | tsub a b => max (evalR c R P M K a - evalR c R P M K b) 0
  | mn a b => min (evalR c R P M K a) (evalR c R P M K b)
  | mx a b => max (evalR c R P M K a) (evalR c R P M K b)
  | dist a => P * latDist (evalR c R P M K a / P)
  | ap => P * (⌊R / P⌋₊ : ℝ)
  | sp => R - P * (⌊R / P⌋₊ : ℝ)

/-- The error constant of Lemma 1 (`E(m) = 1/2`, `E(k) = ε`). -/
def err (ε : ℚ) : Expr → ℚ
  | vr => 0
  | vp => 0
  | vm => 1 / 2
  | vk => ε
  | cst n => n
  | add a b => err ε a + err ε b
  | smul n a => n * err ε a
  | tsub a b => err ε a + err ε b
  | mn a b => max (err ε a) (err ε b)
  | mx a b => max (err ε a) (err ε b)
  | dist a => err ε a
  | ap => 0
  | sp => 0

end Expr

/-- The homogenised profile `τ̂(θ) = τ(1, θ, α, κθ)` with the constants dropped. -/
noncomputable def prof (α κ : ℚ) (θ : ℝ) (e : Expr) : ℝ :=
  e.evalR false 1 θ (α : ℝ) ((κ : ℝ) * θ)

/-! ### The distance to `ℤ` -/

theorem latDist_le (x : ℝ) (n : ℤ) : latDist x ≤ |x - n| := by
  unfold latDist
  have hf : Int.fract x = x - ⌊x⌋ := (Int.self_sub_floor x).symm
  rcases le_or_gt n ⌊x⌋ with h | h
  · have h1 : (n : ℝ) ≤ ⌊x⌋ := by exact_mod_cast h
    have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by rw [hf]; linarith)
  · have h0 : ⌊x⌋ + 1 ≤ n := Int.add_one_le_of_lt h
    have h1 : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast h0
    push_cast at h1
    have h2 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_right _ _).trans (by rw [hf]; linarith)

theorem latDist_exists (x : ℝ) : ∃ n : ℤ, latDist x = |x - n| := by
  unfold latDist
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hf : Int.fract x = x - ⌊x⌋ := (Int.self_sub_floor x).symm
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · refine ⟨⌊x⌋, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by linarith), hf]
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [min_eq_right h]
    push_cast
    rw [abs_of_nonpos (by linarith), hf]
    ring

theorem latDist_lip (x y : ℝ) : |latDist x - latDist y| ≤ |x - y| := by
  obtain ⟨n, hn⟩ := latDist_exists y
  obtain ⟨n', hn'⟩ := latDist_exists x
  have h1 : latDist x ≤ |x - y| + latDist y := by
    calc latDist x ≤ |x - n| := latDist_le x n
      _ ≤ |x - y| + |y - n| := abs_sub_le x y n
      _ = _ := by rw [hn]
  have h2 : latDist y ≤ |x - y| + latDist x := by
    calc latDist y ≤ |y - n'| := latDist_le y n'
      _ ≤ |y - x| + |x - n'| := abs_sub_le y x n'
      _ = _ := by rw [hn', abs_sub_comm]
  rw [abs_le]
  constructor <;> linarith

/-- Near an integer `n` (within `1/2`) the distance to `ℤ` is the distance to `n`. -/
theorem latDist_eq (x : ℝ) (n : ℤ) (h : |x - n| ≤ 1 / 2) : latDist x = |x - n| := by
  obtain ⟨n', hn'⟩ := latDist_exists x
  have hle := latDist_le x n
  by_cases hnn : n = n'
  · subst hnn; exact hn'
  · have h1 : (1 : ℝ) ≤ |(n : ℝ) - n'| := by
      have h3 : (1 : ℤ) ≤ |n - n'| := Int.one_le_abs (sub_ne_zero.2 hnn)
      have h4 : ((1 : ℤ) : ℝ) ≤ ((|n - n'| : ℤ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      exact h4
    have h2 : |(n : ℝ) - n'| ≤ |x - n| + |x - n'| := by
      calc |(n : ℝ) - n'| ≤ |(n : ℝ) - x| + |x - n'| := abs_sub_le _ _ _
        _ = _ := by rw [abs_sub_comm (n : ℝ) x]
    rw [hn'] at hle ⊢
    exact le_antisymm hle (by linarith)

/-- `p · latDist (x / p) = min (x mod p) (p - x mod p)` for naturals. -/
theorem latDist_natCast_div (x p : ℕ) (hp : 0 < p) :
    (p : ℝ) * latDist ((x : ℝ) / p) = ((min (x % p) (p - x % p) : ℕ) : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hlt : x % p < p := Nat.mod_lt x hp
  have hdiv : (x : ℝ) = p * (x / p : ℕ) + (x % p : ℕ) := by
    have := Nat.div_add_mod x p
    exact_mod_cast this.symm
  have hf : Int.fract ((x : ℝ) / p) = ((x % p : ℕ) : ℝ) / p := by
    rw [Int.fract_eq_iff]
    refine ⟨by positivity, ?_, ⟨((x / p : ℕ) : ℤ), ?_⟩⟩
    · rw [div_lt_one hp']; exact_mod_cast hlt
    · rw [Int.cast_natCast, hdiv, div_sub_div_same, add_sub_cancel_right,
        mul_div_cancel_left₀ _ hp'.ne']
  unfold latDist
  rw [hf, mul_min_of_nonneg _ _ hp'.le, Nat.cast_min, Nat.cast_sub hlt.le]
  congr 1
  · field_simp
  · field_simp

/-! ### Integer and real values -/

theorem natCast_tsub (a b : ℕ) : ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  rcases le_total b a with h | h
  · have h' : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_left (by linarith)]
  · have h' : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_right (by linarith)]

theorem evalN_cast {r p m k : ℕ} (hp : 0 < p) (e : Expr) :
    (e.evalN r p m k : ℝ) = e.evalR true r p m k := by
  induction e with
  | vr => rfl
  | vp => rfl
  | vm => rfl
  | vk => rfl
  | cst n => simp [Expr.evalN, Expr.evalR]
  | add a b iha ihb => simp only [Expr.evalN, Expr.evalR]; push_cast; rw [iha, ihb]
  | smul n a iha => simp only [Expr.evalN, Expr.evalR]; push_cast; rw [iha]
  | tsub a b iha ihb => simp only [Expr.evalN, Expr.evalR]; rw [natCast_tsub, iha, ihb]
  | mn a b iha ihb => simp only [Expr.evalN, Expr.evalR]; rw [Nat.cast_min, iha, ihb]
  | mx a b iha ihb => simp only [Expr.evalN, Expr.evalR]; rw [Nat.cast_max, iha, ihb]
  | dist a iha =>
    simp only [Expr.evalN, Expr.evalR]
    rw [← iha]
    exact (latDist_natCast_div _ _ hp).symm
  | ap =>
    simp only [Expr.evalN, Expr.evalR]
    rw [Nat.floor_div_eq_div, Nat.cast_mul]
  | sp =>
    simp only [Expr.evalN, Expr.evalR]
    rw [Nat.floor_div_eq_div]
    have h := Nat.mod_add_div r p
    have h' : ((r % p : ℕ) : ℝ) + (p : ℝ) * ((r / p : ℕ) : ℝ) = r := by exact_mod_cast h
    linarith

/-! ### Lemma 1 (homogenisation error) -/

/-- **Lemma 1.**  Perturbing `m` by at most `1/2` and `k` by at most `ε` and dropping the constants changes
the value of `e` by at most `err ε e`. -/
theorem evalR_err (ε : ℚ) {R P M M' K K' : ℝ} (hP : 0 < P) (hM : |M - M'| ≤ 1 / 2)
    (hK : |K - K'| ≤ ε) (e : Expr) :
    |e.evalR true R P M K - e.evalR false R P M' K'| ≤ (e.err ε : ℝ) := by
  induction e with
  | vr => simp [Expr.evalR, Expr.err]
  | vp => simp [Expr.evalR, Expr.err]
  | vm => simp only [Expr.evalR, Expr.err]; push_cast; exact hM
  | vk => simp only [Expr.evalR, Expr.err]; exact hK
  | cst n => simp [Expr.evalR, Expr.err]
  | add a b iha ihb =>
    simp only [Expr.evalR, Expr.err]; push_cast
    rw [abs_le] at iha ihb ⊢
    constructor <;> linarith [iha.1, iha.2, ihb.1, ihb.2]
  | smul n a iha =>
    simp only [Expr.evalR, Expr.err]; push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_left iha (Nat.cast_nonneg n)
  | tsub a b iha ihb =>
    simp only [Expr.evalR, Expr.err]; push_cast
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [abs_le] at iha ihb ⊢
    constructor <;> linarith [iha.1, iha.2, ihb.1, ihb.2]
  | mn a b iha ihb =>
    simp only [Expr.evalR, Expr.err]; push_cast
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le_max iha ihb)
  | mx a b iha ihb =>
    simp only [Expr.evalR, Expr.err]; push_cast
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le_max iha ihb)
  | dist a iha =>
    simp only [Expr.evalR, Expr.err]
    set A := a.evalR true R P M K
    set A' := a.evalR false R P M' K'
    have h := latDist_lip (A / P) (A' / P)
    rw [← mul_sub, abs_mul, abs_of_pos hP]
    calc P * |latDist (A / P) - latDist (A' / P)| ≤ P * |A / P - A' / P| :=
          mul_le_mul_of_nonneg_left h hP.le
      _ = |A - A'| := by
          rw [← sub_div, abs_div, abs_of_pos hP]; field_simp
      _ ≤ _ := iha
  | ap => simp [Expr.evalR, Expr.err]
  | sp => simp [Expr.evalR, Expr.err]

/-! ### Homogeneity -/

theorem evalR_hom (α κ : ℝ) {R P : ℝ} (hR : 0 < R) (e : Expr) :
    e.evalR false R P (α * R) (κ * P) = R * e.evalR false 1 (P / R) α (κ * (P / R)) := by
  have hR0 : R ≠ 0 := hR.ne'
  induction e with
  | vr => simp [Expr.evalR]
  | vp => simp only [Expr.evalR]; field_simp
  | vm => simp only [Expr.evalR]; ring
  | vk => simp only [Expr.evalR]; field_simp
  | cst n => simp [Expr.evalR]
  | add a b iha ihb => simp only [Expr.evalR]; rw [iha, ihb]; ring
  | smul n a iha => simp only [Expr.evalR]; rw [iha]; ring
  | tsub a b iha ihb =>
    simp only [Expr.evalR]; rw [iha, ihb, ← mul_sub, mul_max_of_nonneg _ _ hR.le, mul_zero]
  | mn a b iha ihb => simp only [Expr.evalR]; rw [iha, ihb, mul_min_of_nonneg _ _ hR.le]
  | mx a b iha ihb => simp only [Expr.evalR]; rw [iha, ihb, mul_max_of_nonneg _ _ hR.le]
  | dist a iha =>
    simp only [Expr.evalR]
    rw [iha]
    have e1 : a.evalR false 1 (P / R) α (κ * (P / R)) / (P / R) =
        R * a.evalR false 1 (P / R) α (κ * (P / R)) / P := by
      rw [div_div_eq_mul_div, mul_comm]
    rw [e1]
    field_simp
  | ap =>
    simp only [Expr.evalR]
    rw [one_div_div]
    field_simp
  | sp =>
    simp only [Expr.evalR]
    rw [one_div_div]
    field_simp

/-- **Lemma 1, scaled form.**  `τ(r, p, m, k) ≤ r · prof α κ (p / r) τ + E(τ)` when `|m - α r| ≤ 1/2` and
`|k - κ p| ≤ ε`. -/
theorem evalN_le_prof (ε α κ : ℚ) {r p m k : ℕ} (hr : 0 < r) (hp : 0 < p)
    (hm : |(m : ℝ) - α * r| ≤ 1 / 2) (hk : |(k : ℝ) - κ * p| ≤ ε) (e : Expr) :
    (e.evalN r p m k : ℝ) ≤ r * prof α κ ((p : ℝ) / r) e + (e.err ε : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 := evalR_err ε hp' hm hk e (R := (r : ℝ))
  have h2 := evalR_hom (α : ℝ) (κ : ℝ) hr' e (P := (p : ℝ))
  rw [evalN_cast hp e]
  unfold prof
  have h1' := (abs_le.1 h1).2
  linarith [h1', h2]

end CatalanCore.Uniform.Content.BankShared.Check
