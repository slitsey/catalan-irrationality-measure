module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Node sums `Σ_m Σ_e d_e/(m+e)`: partial sums bounded by rational arithmetic (generic)

`LC27` (the rational form of Theorem C01, `C01R`) and `LC28` (tail lemma).  Let `(e_i, d_i)` be
any finite node table with `0 ≤ e_i ≤ 1` and `Σ d_i = 0`, and

  `f m = -Σ_i d_i/(m + e_i)`,   `S M = Σ_{1 ≤ m < M} f m`.

`partial_sum_le` bounds `S M` for every `M ≥ 1` by `R`, from: the finitely many exact positivity
checks `f m ≥ 0` for `m < m₁`, a prefix bound `S M₀ ≤ Ŝ`, and the rational comparison
`Ŝ + T ≤ R`, where `T` is the explicit tail constant (`tailConst`).  No `ψ`, no logarithm, no
integral: every step is an inequality between rational functions.

The tail lemma (LC28) is in telescoping form: for `m ≥ 1`
* `m^{-k} ≤ [(m-½)^{1-k} - (m+½)^{1-k}]/(k-1)` (`k = 2, 4, 6, 7`, the midpoint bound),
* `m^{-k} ≥ [m^{1-k} - (m+1)^{1-k}]/(k-1)` (all `k ≥ 2`, the monotone bound).
-/

namespace CatalanCore.Content.PartialSums

/-! ### Elementary telescoping bounds -/

/-- Monotone lower bound: `[x^{-j} - (x+1)^{-j}]/j ≤ x^{-(j+1)}` (Bernoulli). -/
lemma lo_tel (j : ℕ) (hj : 1 ≤ j) (x : ℚ) (hx : 0 < x) :
    ((x ^ j)⁻¹ - ((x + 1) ^ j)⁻¹) / j ≤ (x ^ (j + 1))⁻¹ := by
  have hA : 0 < x ^ j := pow_pos hx j
  have hB : 0 < (x + 1) ^ j := pow_pos (by linarith) j
  have hjq : (0 : ℚ) < j := by exact_mod_cast hj
  have hxp : (0 : ℚ) < x + 1 := by linarith
  have h := one_add_mul_le_pow (a := -1 / (x + 1)) (by
    have h0 : (0 : ℚ) < 1 / (x + 1) := by positivity
    have h1 : 1 / (x + 1) ≤ 1 := by rw [div_le_one hxp]; linarith
    have h2 : -1 / (x + 1) = -(1 / (x + 1)) := by ring
    linarith) j
  have e : (1 + -1 / (x + 1)) = x / (x + 1) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ hB] at h
  have h3 : (x ^ j)⁻¹ - ((x + 1) ^ j)⁻¹ = ((x + 1) ^ j - x ^ j) / (x ^ j * (x + 1) ^ j) := by
    field_simp
  have h2 : (x + 1) ^ j - x ^ j ≤ (x + 1) ^ j * (j / (x + 1)) := by
    have : (1 + (j : ℚ) * (-1 / (x + 1))) * (x + 1) ^ j =
        (x + 1) ^ j - (x + 1) ^ j * (j / (x + 1)) := by ring
    linarith
  have h6 : (j : ℚ) / (x + 1) ≤ j / x := div_le_div_of_nonneg_left hjq.le hx (by linarith)
  have h7 : (x + 1) ^ j - x ^ j ≤ (x + 1) ^ j * (j / x) :=
    h2.trans (by gcongr)
  rw [h3, div_div, div_le_iff₀ (by positivity)]
  have h5 : (x ^ (j + 1))⁻¹ * (x ^ j * (x + 1) ^ j * j) = (x + 1) ^ j * (j / x) := by
    rw [pow_succ]; field_simp
  rw [h5]
  exact h7

/-- A polynomial inequality gives the midpoint upper bound. -/
lemma up_of_poly (j : ℕ) (hj : 1 ≤ j) (x : ℚ) (hx : 1 ≤ x)
    (h : (j : ℚ) * ((x - 1 / 2) * (x + 1 / 2)) ^ j ≤ x ^ (j + 1) * ((x + 1 / 2) ^ j - (x - 1 / 2) ^ j)) :
    (x ^ (j + 1))⁻¹ ≤ (((x - 1 / 2) ^ j)⁻¹ - ((x + 1 / 2) ^ j)⁻¹) / j := by
  have hu : 0 < x - 1 / 2 := by linarith
  have hv : 0 < x + 1 / 2 := by linarith
  have hjq : (0 : ℚ) < j := by exact_mod_cast hj
  have hxp : 0 < x := by linarith
  rw [inv_sub_inv (pow_pos hu j).ne' (pow_pos hv j).ne', div_div, le_div_iff₀ (by positivity),
    inv_mul_le_iff₀ (by positivity)]
  rw [mul_pow] at h
  linarith [h]

lemma up2 (x : ℚ) (hx : 1 ≤ x) :
    (x ^ 2)⁻¹ ≤ (((x - 1 / 2) ^ 1)⁻¹ - ((x + 1 / 2) ^ 1)⁻¹) / (1 : ℕ) := by
  have := up_of_poly 1 le_rfl x hx (by nlinarith)
  simpa using this

lemma up4 (x : ℚ) (hx : 1 ≤ x) :
    (x ^ 4)⁻¹ ≤ (((x - 1 / 2) ^ 3)⁻¹ - ((x + 1 / 2) ^ 3)⁻¹) / (3 : ℕ) := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  exact up_of_poly 3 (by norm_num) x hx (by
    have : x ^ (3 + 1) * ((x + 1 / 2) ^ 3 - (x - 1 / 2) ^ 3) - (3 : ℕ) * ((x - 1 / 2) * (x + 1 / 2)) ^ 3
        = 3 / 64 - 9 / 16 * x ^ 2 + 5 / 2 * (x ^ 2) ^ 2 := by push_cast; ring
    nlinarith [this, mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hx2), sq_nonneg (x ^ 2)])

lemma up6 (x : ℚ) (hx : 1 ≤ x) :
    (x ^ 6)⁻¹ ≤ (((x - 1 / 2) ^ 5)⁻¹ - ((x + 1 / 2) ^ 5)⁻¹) / (5 : ℕ) := by
  have hy : 1 ≤ x ^ 2 := by nlinarith
  set y := x ^ 2 with hydef
  exact up_of_poly 5 (by norm_num) x hx (by
    have : x ^ (5 + 1) * ((x + 1 / 2) ^ 5 - (x - 1 / 2) ^ 5) - (5 : ℕ) * ((x - 1 / 2) * (x + 1 / 2)) ^ 5
        = 5 / 1024 - 25 / 256 * y + 25 / 32 * y ^ 2 - 49 / 16 * y ^ 3 + 35 / 4 * y ^ 4 := by
      rw [hydef]; push_cast; ring
    have h3 : y ^ 3 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
    have h2 : y ≤ y ^ 2 := by nlinarith
    have h1 : 0 ≤ y ^ 3 := by positivity
    nlinarith [this, h3, h2, h1])

lemma up7 (x : ℚ) (hx : 1 ≤ x) :
    (x ^ 7)⁻¹ ≤ (((x - 1 / 2) ^ 6)⁻¹ - ((x + 1 / 2) ^ 6)⁻¹) / (6 : ℕ) := by
  have hy : 1 ≤ x ^ 2 := by nlinarith
  set y := x ^ 2 with hydef
  exact up_of_poly 6 (by norm_num) x hx (by
    have : x ^ (6 + 1) * ((x + 1 / 2) ^ 6 - (x - 1 / 2) ^ 6) - (6 : ℕ) * ((x - 1 / 2) * (x + 1 / 2)) ^ 6
        = -3 / 2048 + 9 / 256 * y - 45 / 128 * y ^ 2 + 15 / 8 * y ^ 3 - 21 / 4 * y ^ 4
            + 14 * y ^ 5 := by
      rw [hydef]; push_cast; ring
    have hpoly : 0 ≤ -3 / 2048 + 9 / 256 * y - 45 / 128 * y ^ 2 + 15 / 8 * y ^ 3 - 21 / 4 * y ^ 4
            + 14 * y ^ 5 := by
      have h5 : y ^ 4 ≤ y ^ 5 := pow_le_pow_right₀ hy (by norm_num)
      have h4 : y ^ 3 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
      have h3 : y ^ 2 ≤ y ^ 3 := pow_le_pow_right₀ hy (by norm_num)
      have h2 : y ≤ y ^ 2 := by nlinarith
      nlinarith [h5, h4, h3, h2]
    linarith [this, hpoly])

/-! ### The node table -/

section Node

variable {ι : Type*} [Fintype ι] (e d : ι → ℚ)

/-- `f m = -Σ_i d_i/(m + e_i)`. -/
def nodeF (m : ℕ) : ℚ := -∑ i, d i / ((m : ℚ) + e i)

/-- `S M = Σ_{1 ≤ m < M} f m`. -/
def partialS (M : ℕ) : ℚ := ∑ m ∈ Finset.Ico 1 M, nodeF e d m

/-- Moments `Σ d_i e_i^j`. -/
def mom (j : ℕ) : ℚ := ∑ i, d i * e i ^ j

/-- Absolute moments `Σ |d_i| e_i^j`. -/
def absmom (j : ℕ) : ℚ := ∑ i, |d i| * e i ^ j

/-- The expansion coefficients `a_k = (-1)^k Σ d e^{k-1}` (`k = 2, …, 6`). -/
def a2 : ℚ := mom e d 1
def a3 : ℚ := -mom e d 2
def a4 : ℚ := mom e d 3
def a5 : ℚ := -mom e d 4
def a6 : ℚ := mom e d 5

/-- The telescoping potential; the tail constant is `Φ M₀`. -/
def Phi (x : ℚ) : ℚ :=
  a2 e d * ((x - 1 / 2) ^ 1)⁻¹ / (1 : ℕ) + a3 e d * ((x ^ 2)⁻¹) / (2 : ℕ)
    + a4 e d * ((x - 1 / 2) ^ 3)⁻¹ / (3 : ℕ) + a5 e d * ((x ^ 4)⁻¹) / (4 : ℕ)
    + a6 e d * ((x - 1 / 2) ^ 5)⁻¹ / (5 : ℕ) + absmom e d 6 * ((x - 1 / 2) ^ 6)⁻¹ / (6 : ℕ)

variable {e d}

lemma absmom_nonneg (he0 : ∀ i, 0 ≤ e i) (j : ℕ) : 0 ≤ absmom e d j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (pow_nonneg (he0 i) _)

/-- The six-term expansion of `f` (finite geometric identity, `Σ d = 0`). -/
lemma nodeF_expand (hd : ∑ i, d i = 0) (he0 : ∀ i, 0 ≤ e i) (m : ℕ) (hm : 1 ≤ m) :
    nodeF e d m = a2 e d * ((m : ℚ) ^ 2)⁻¹ + a3 e d * ((m : ℚ) ^ 3)⁻¹ + a4 e d * ((m : ℚ) ^ 4)⁻¹
      + a5 e d * ((m : ℚ) ^ 5)⁻¹ + a6 e d * ((m : ℚ) ^ 6)⁻¹
      - ∑ i, d i * e i ^ 6 / ((m : ℚ) ^ 6 * ((m : ℚ) + e i)) := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have key : ∀ i, d i / ((m : ℚ) + e i) =
      d i * (m : ℚ)⁻¹ - (d i * e i) * ((m : ℚ) ^ 2)⁻¹ + (d i * e i ^ 2) * ((m : ℚ) ^ 3)⁻¹
        - (d i * e i ^ 3) * ((m : ℚ) ^ 4)⁻¹ + (d i * e i ^ 4) * ((m : ℚ) ^ 5)⁻¹
        - (d i * e i ^ 5) * ((m : ℚ) ^ 6)⁻¹ + d i * e i ^ 6 / ((m : ℚ) ^ 6 * ((m : ℚ) + e i)) := by
    intro i
    have : (m : ℚ) + e i ≠ 0 := by have := he0 i; positivity
    field_simp
    ring
  unfold nodeF
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hd]
  simp only [a2, a3, a4, a5, a6, mom]
  ring

/-- The remainder is at most `A m^{-7}`. -/
lemma rem_le (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    -∑ i, d i * e i ^ 6 / ((m : ℚ) ^ 6 * ((m : ℚ) + e i)) ≤ absmom e d 6 * ((m : ℚ) ^ 7)⁻¹ := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  rw [absmom, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 := he0 i
  have hden : (0 : ℚ) < (m : ℚ) ^ 6 * ((m : ℚ) + e i) := by positivity
  have hle : (m : ℚ) ^ 7 ≤ (m : ℚ) ^ 6 * ((m : ℚ) + e i) := by
    rw [pow_succ _ 6]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc -(d i * e i ^ 6 / ((m : ℚ) ^ 6 * ((m : ℚ) + e i)))
      ≤ |d i * e i ^ 6 / ((m : ℚ) ^ 6 * ((m : ℚ) + e i))| := neg_le_abs _
    _ = |d i| * e i ^ 6 / ((m : ℚ) ^ 6 * ((m : ℚ) + e i)) := by
        rw [abs_div, abs_mul, abs_of_pos hden, abs_of_nonneg (pow_nonneg h0 6)]
    _ ≤ |d i| * e i ^ 6 / (m : ℚ) ^ 7 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hle
    _ = |d i| * e i ^ 6 * ((m : ℚ) ^ 7)⁻¹ := by rw [div_eq_mul_inv]

/-- The telescoping bound `f m ≤ Φ m - Φ (m+1)` (`m ≥ 1`, sign pattern of the `a_k`). -/
lemma nodeF_le_tel (hd : ∑ i, d i = 0) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (ha2 : 0 ≤ a2 e d) (ha3 : a3 e d ≤ 0) (ha4 : 0 ≤ a4 e d) (ha5 : a5 e d ≤ 0)
    (ha6 : 0 ≤ a6 e d) (m : ℕ) (hm : 1 ≤ m) :
    nodeF e d m ≤ Phi e d m - Phi e d ((m + 1 : ℕ) : ℚ) := by
  have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hs : ((m + 1 : ℕ) : ℚ) - 1 / 2 = (m : ℚ) + 1 / 2 := by push_cast; ring
  have hs' : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  rw [nodeF_expand hd he0 m hm]
  have hA := absmom_nonneg (d := d) he0 6
  have r := rem_le (d := d) he0 he1 m hm
  have t2 := mul_le_mul_of_nonneg_left (up2 m hm1) ha2
  have t3 := mul_le_mul_of_nonpos_left (lo_tel 2 (by norm_num) m (by linarith)) ha3
  have t4 := mul_le_mul_of_nonneg_left (up4 m hm1) ha4
  have t5 := mul_le_mul_of_nonpos_left (lo_tel 4 (by norm_num) m (by linarith)) ha5
  have t6 := mul_le_mul_of_nonneg_left (up6 m hm1) ha6
  have t7 := mul_le_mul_of_nonneg_left (up7 m hm1) hA
  unfold Phi
  rw [hs, hs']
  norm_num at t2 t3 t4 t5 t6 t7 ⊢
  linarith

/-- `Φ x ≥ 0` for `x ≥ 1`. -/
lemma Phi_nonneg (he0 : ∀ i, 0 ≤ e i)
    (ha2 : 0 ≤ a2 e d) (ha3 : a3 e d ≤ 0) (ha4 : 0 ≤ a4 e d) (ha5 : a5 e d ≤ 0)
    (ha6 : 0 ≤ a6 e d) (hΦ : -a3 e d / 2 - a5 e d / 4 ≤ a2 e d) (x : ℚ) (hx : 1 ≤ x) :
    0 ≤ Phi e d x := by
  have hA := absmom_nonneg (d := d) he0 6
  have hx0 : 0 < x := by linarith
  have hu : 0 < x - 1 / 2 := by linarith
  have i1 : x⁻¹ ≤ ((x - 1 / 2) ^ 1)⁻¹ := by
    rw [pow_one]; exact inv_anti₀ hu (by linarith)
  have i2 : (x ^ 2)⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 (by nlinarith)
  have i4 : (x ^ 4)⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 (by nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x])
  have p3 : 0 ≤ a4 e d * ((x - 1 / 2) ^ 3)⁻¹ / (3 : ℕ) := by positivity
  have p5 : 0 ≤ a6 e d * ((x - 1 / 2) ^ 5)⁻¹ / (5 : ℕ) := by positivity
  have p6 : 0 ≤ absmom e d 6 * ((x - 1 / 2) ^ 6)⁻¹ / (6 : ℕ) := by positivity
  have q1 : a2 e d * x⁻¹ ≤ a2 e d * ((x - 1 / 2) ^ 1)⁻¹ := mul_le_mul_of_nonneg_left i1 ha2
  have q2 : a3 e d * x⁻¹ ≤ a3 e d * (x ^ 2)⁻¹ := mul_le_mul_of_nonpos_left i2 ha3
  have q4 : a5 e d * x⁻¹ ≤ a5 e d * (x ^ 4)⁻¹ := mul_le_mul_of_nonpos_left i4 ha5
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.2 hx0.le
  have main : 0 ≤ (a2 e d + a3 e d / 2 + a5 e d / 4) * x⁻¹ :=
    mul_nonneg (by linarith) hinv
  unfold Phi
  norm_num at p3 p5 p6 q1 q2 q4 main ⊢
  nlinarith [p3, p5, p6, q1, q2, q4, main]

/-- Telescoping sum over `Ico M₀ N`. -/
lemma tail_tel (hd : ∑ i, d i = 0) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (ha2 : 0 ≤ a2 e d) (ha3 : a3 e d ≤ 0) (ha4 : 0 ≤ a4 e d) (ha5 : a5 e d ≤ 0)
    (ha6 : 0 ≤ a6 e d) (M₀ : ℕ) (hM₀ : 1 ≤ M₀) :
    ∀ N, M₀ ≤ N → ∑ m ∈ Finset.Ico M₀ N, nodeF e d m ≤ Phi e d M₀ - Phi e d N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    have := nodeF_le_tel hd he0 he1 ha2 ha3 ha4 ha5 ha6 N (le_trans hM₀ hN)
    linarith

/-- `f ≥ S₁/m² - B/m³`: positivity of `f` for large `m`. -/
lemma nodeF_ge (hd : ∑ i, d i = 0) (he0 : ∀ i, 0 ≤ e i) (m : ℕ) (hm : 1 ≤ m) :
    mom e d 1 * ((m : ℚ) ^ 2)⁻¹ - absmom e d 2 * ((m : ℚ) ^ 3)⁻¹ ≤ nodeF e d m := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have key : ∀ i, d i / ((m : ℚ) + e i) =
      d i * (m : ℚ)⁻¹ - (d i * e i) * ((m : ℚ) ^ 2)⁻¹ + d i * e i ^ 2 / ((m : ℚ) ^ 2 * ((m : ℚ) + e i)) := by
    intro i
    have : (m : ℚ) + e i ≠ 0 := by have := he0 i; positivity
    field_simp
    ring
  have hb : ∑ i, d i * e i ^ 2 / ((m : ℚ) ^ 2 * ((m : ℚ) + e i)) ≤ absmom e d 2 * ((m : ℚ) ^ 3)⁻¹ := by
    rw [absmom, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 := he0 i
    have hden : (0 : ℚ) < (m : ℚ) ^ 2 * ((m : ℚ) + e i) := by positivity
    have hle : (m : ℚ) ^ 3 ≤ (m : ℚ) ^ 2 * ((m : ℚ) + e i) := by
      rw [pow_succ _ 2]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc d i * e i ^ 2 / ((m : ℚ) ^ 2 * ((m : ℚ) + e i))
        ≤ |d i * e i ^ 2 / ((m : ℚ) ^ 2 * ((m : ℚ) + e i))| := le_abs_self _
      _ = |d i| * e i ^ 2 / ((m : ℚ) ^ 2 * ((m : ℚ) + e i)) := by
          rw [abs_div, abs_mul, abs_of_pos hden, abs_of_nonneg (pow_nonneg h0 2)]
      _ ≤ |d i| * e i ^ 2 / (m : ℚ) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hle
      _ = |d i| * e i ^ 2 * ((m : ℚ) ^ 3)⁻¹ := by rw [div_eq_mul_inv]
  unfold nodeF
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hd]
  simp only [mom, pow_one]
  linarith

/-- Exact finite checks for `m < m₁`, plus `B ≤ m₁ S₁`, give `f ≥ 0` for every `m ≥ 1`. -/
lemma nodeF_nonneg (hd : ∑ i, d i = 0) (he0 : ∀ i, 0 ≤ e i) (m₁ : ℕ)
    (hsmall : ∀ m : ℕ, 1 ≤ m → m < m₁ → 0 ≤ nodeF e d m)
    (hbig : absmom e d 2 ≤ (m₁ : ℚ) * mom e d 1) (hS1 : 0 ≤ mom e d 1) :
    ∀ m : ℕ, 1 ≤ m → 0 ≤ nodeF e d m := by
  intro m hm
  by_cases h : m < m₁
  · exact hsmall m hm h
  · push_neg at h
    have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
    have h1 : (m₁ : ℚ) ≤ m := by exact_mod_cast h
    have hg := nodeF_ge hd he0 m hm
    have : 0 ≤ mom e d 1 * ((m : ℚ) ^ 2)⁻¹ - absmom e d 2 * ((m : ℚ) ^ 3)⁻¹ := by
      have e3 : ((m : ℚ) ^ 3)⁻¹ = ((m : ℚ) ^ 2)⁻¹ * (m : ℚ)⁻¹ := by
        rw [← mul_inv, ← pow_succ]
      have h2 : absmom e d 2 * ((m : ℚ) ^ 3)⁻¹ ≤ mom e d 1 * ((m : ℚ) ^ 2)⁻¹ := by
        calc absmom e d 2 * ((m : ℚ) ^ 3)⁻¹ ≤ (mom e d 1 * m) * ((m : ℚ) ^ 3)⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc absmom e d 2 ≤ (m₁ : ℚ) * mom e d 1 := hbig
                _ ≤ (m : ℚ) * mom e d 1 := mul_le_mul_of_nonneg_right h1 hS1
                _ = mom e d 1 * m := mul_comm _ _
          _ = mom e d 1 * ((m : ℚ) ^ 2)⁻¹ := by field_simp
      linarith
    linarith

lemma partialS_mono (hpos : ∀ m : ℕ, 1 ≤ m → 0 ≤ nodeF e d m) {M N : ℕ} (h : M ≤ N) :
    partialS e d M ≤ partialS e d N := by
  unfold partialS
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right h) ?_
  intro m hm _
  exact hpos m (Finset.mem_Ico.1 hm).1

/-- **LC27, theorem side (rational form of Theorem C01).**  Every partial sum `S M` is at most
`R`, given: the sign pattern of the expansion coefficients, `f ≥ 0` (finite checks plus the large
`m` bound), a prefix bound `S M₀ ≤ Ŝ`, and the rational comparison `Ŝ + Φ M₀ ≤ R`. -/
theorem partial_sum_le (hd : ∑ i, d i = 0) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (ha2 : 0 ≤ a2 e d) (ha3 : a3 e d ≤ 0) (ha4 : 0 ≤ a4 e d) (ha5 : a5 e d ≤ 0)
    (ha6 : 0 ≤ a6 e d) (hΦ : -a3 e d / 2 - a5 e d / 4 ≤ a2 e d)
    (hpos : ∀ m : ℕ, 1 ≤ m → 0 ≤ nodeF e d m)
    (M₀ : ℕ) (hM₀ : 1 ≤ M₀) (S R : ℚ) (hS : partialS e d M₀ ≤ S) (hR : S + Phi e d M₀ ≤ R) :
    ∀ M : ℕ, 1 ≤ M → partialS e d M ≤ R := by
  intro M hM
  have hM₀q : (1 : ℚ) ≤ M₀ := by exact_mod_cast hM₀
  have hΦ0 := Phi_nonneg (d := d) he0 ha2 ha3 ha4 ha5 ha6 hΦ M₀ hM₀q
  by_cases hMM : M ≤ M₀
  · calc partialS e d M ≤ partialS e d M₀ := partialS_mono hpos hMM
      _ ≤ S := hS
      _ ≤ R := by linarith
  · push_neg at hMM
    have hMq : (1 : ℚ) ≤ M := by exact_mod_cast hM
    have hΦM := Phi_nonneg (d := d) he0 ha2 ha3 ha4 ha5 ha6 hΦ M hMq
    have hsplit : partialS e d M = partialS e d M₀ + ∑ m ∈ Finset.Ico M₀ M, nodeF e d m := by
      unfold partialS
      rw [Finset.sum_Ico_consecutive _ hM₀ hMM.le]
    have ht := tail_tel hd he0 he1 ha2 ha3 ha4 ha5 ha6 M₀ hM₀ M hMM.le
    rw [hsplit]
    linarith

end Node

end CatalanCore.Content.PartialSums
