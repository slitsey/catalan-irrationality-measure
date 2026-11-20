module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Pfaff–Saalschütz summation for balanced terminating `₃F₂` (rational parameters)

For `α β γ : ℚ`, `n : ℕ`, `γ > 0` and `n ≤ α + β − γ` (this makes every Pochhammer denominator
positive and covers all parameter shapes of the Wilson–Hankel computation):

`∑_{k ≤ n} (−n)_k (α)_k (β)_k / (k! (γ)_k (1+α+β−γ−n)_k) = (γ−α)_n (γ−β)_n / ((γ)_n (γ−α−β)_n)`.

Proof: Zeilberger recurrence in `n` with the rational certificate
`G(n, k+1) = −(α+k)(β+k) T(n, k)`:
`(γ+n)(n−A) T(n+1, k) − (γ−α+n)(γ−β+n) T(n, k) = G(n,k+1) − G(n,k)`, `A = α+β−γ`.
No formal Euler transformation is used; the only automation is `field_simp; ring`.
-/

namespace CatalanCore.NT

/-- Rising factorial `(x)_k = x (x+1) ⋯ (x+k−1)`. -/
def poch (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => poch x k * (x + k)

@[simp] theorem poch_zero (x : ℚ) : poch x 0 = 1 := rfl

theorem poch_succ (x : ℚ) (k : ℕ) : poch x (k + 1) = poch x k * (x + k) := rfl

theorem poch_succ' (x : ℚ) (m : ℕ) : poch x (m + 1) = x * poch (x + 1) m := by
  induction m with
  | zero => simp [poch]
  | succ m ih =>
    rw [poch_succ, ih, poch_succ (x + 1) m]
    push_cast
    ring

theorem poch_pos {x : ℚ} (hx : 0 < x) (k : ℕ) : 0 < poch x k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [poch_succ]
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    exact mul_pos ih (by linarith)

/-- The summand `T(n, k)` of the balanced `₃F₂`. -/
def saalTerm (α β γ : ℚ) (n k : ℕ) : ℚ :=
  poch (-(n : ℚ)) k * poch α k * poch β k /
    ((k.factorial : ℚ) * poch γ k * poch (1 + α + β - γ - n) k)

/-- The sum over `k ≤ n`. -/
def saalSum (α β γ : ℚ) (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), saalTerm α β γ n k

/-- The closed form. -/
def saalRhs (α β γ : ℚ) (n : ℕ) : ℚ :=
  poch (γ - α) n * poch (γ - β) n / (poch γ n * poch (γ - α - β) n)

theorem saalTerm_zero (α β γ : ℚ) (n : ℕ) : saalTerm α β γ n 0 = 1 := by
  simp [saalTerm]

/-- Ratio in `k`, unconditionally (inverses of products are products of inverses). -/
theorem saalTerm_succ_k (α β γ : ℚ) (n m : ℕ) :
    saalTerm α β γ n (m + 1) = saalTerm α β γ n m *
      (((m : ℚ) - n) * (α + m) * (β + m) /
        (((m : ℚ) + 1) * (γ + m) * (1 + α + β - γ - n + m))) := by
  unfold saalTerm
  simp only [poch_succ, Nat.factorial_succ]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Shift `n → n + 1` together with `k → k + 1`. -/
theorem saalTerm_succ_n (α β γ : ℚ) (n m : ℕ) :
    saalTerm α β γ (n + 1) (m + 1) = saalTerm α β γ n m *
      (-((n : ℚ) + 1) * (α + m) * (β + m) /
        (((m : ℚ) + 1) * (γ + m) * (α + β - γ - n))) := by
  unfold saalTerm
  have h1 : poch (-((n + 1 : ℕ) : ℚ)) (m + 1) = -((n : ℚ) + 1) * poch (-(n : ℚ)) m := by
    rw [poch_succ']
    push_cast
    congr 2
    ring
  have h2 : poch (1 + α + β - γ - ((n + 1 : ℕ) : ℚ)) (m + 1) =
      (α + β - γ - n) * poch (1 + α + β - γ - n) m := by
    rw [poch_succ']
    push_cast
    congr 1
    · ring
    · congr 1
      ring
  rw [h1, h2]
  simp only [poch_succ, Nat.factorial_succ]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem saalTerm_succ_n_zero (α β γ : ℚ) (n : ℕ) :
    saalTerm α β γ (n + 1) 0 = 1 := saalTerm_zero _ _ _ _

/-- The certificate identity: for `m < n`-type parameters (nonvanishing denominators),
`a T(n+1, m+1) + b T(n, m+1) = −(α+m+1)(β+m+1) T(n, m+1) + (α+m)(β+m) T(n, m)`. -/
theorem saal_tele (α β γ : ℚ) (n m : ℕ) (hm : ((m : ℚ) + 1) ≠ 0) (hg : γ + m ≠ 0)
    (hA : α + β - γ - n ≠ 0) (hL : 1 + α + β - γ - n + m ≠ 0) :
    (γ + n) * ((n : ℚ) - (α + β - γ)) * saalTerm α β γ (n + 1) (m + 1) +
      (-((γ - α + n) * (γ - β + n))) * saalTerm α β γ n (m + 1) =
    -((α + m + 1) * (β + m + 1)) * saalTerm α β γ n (m + 1) +
      (α + m) * (β + m) * saalTerm α β γ n m := by
  rw [saalTerm_succ_n, saalTerm_succ_k]
  have key : (γ + n) * ((n : ℚ) - (α + β - γ)) *
        (-((n : ℚ) + 1) * (α + m) * (β + m) / (((m : ℚ) + 1) * (γ + m) * (α + β - γ - n))) +
      (-((γ - α + n) * (γ - β + n))) *
        (((m : ℚ) - n) * (α + m) * (β + m) /
          (((m : ℚ) + 1) * (γ + m) * (1 + α + β - γ - n + m))) +
      ((α + m + 1) * (β + m + 1)) *
        (((m : ℚ) - n) * (α + m) * (β + m) /
          (((m : ℚ) + 1) * (γ + m) * (1 + α + β - γ - n + m))) -
      (α + m) * (β + m) = 0 := by
    field_simp
    ring
  linear_combination saalTerm α β γ n m * key

/-- Boundary term. -/
theorem saal_boundary (α β γ : ℚ) (n : ℕ) (hg : γ + n ≠ 0) (hA : α + β - γ - n ≠ 0) :
    (γ + n) * ((n : ℚ) - (α + β - γ)) * saalTerm α β γ (n + 1) (n + 1) =
      (α + n) * (β + n) * saalTerm α β γ n n := by
  rw [saalTerm_succ_n]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have key : (γ + n) * ((n : ℚ) - (α + β - γ)) *
        (-((n : ℚ) + 1) * (α + n) * (β + n) / (((n : ℚ) + 1) * (γ + n) * (α + β - γ - n))) =
      (α + n) * (β + n) := by
    field_simp
    ring
  linear_combination saalTerm α β γ n n * key

/-- Partial sums telescope. -/
theorem saal_partial (α β γ : ℚ) (n : ℕ) (hγ : 0 < γ) (hA : ((n + 1 : ℕ) : ℚ) ≤ α + β - γ)
    (M : ℕ) (hM : M ≤ n) :
    (γ + n) * ((n : ℚ) - (α + β - γ)) *
        ∑ k ∈ Finset.range (M + 1), saalTerm α β γ (n + 1) k +
      (-((γ - α + n) * (γ - β + n))) * ∑ k ∈ Finset.range (M + 1), saalTerm α β γ n k =
    -((α + M) * (β + M)) * saalTerm α β γ n M := by
  push_cast at hA
  induction M with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, saalTerm_zero, Nat.cast_zero,
      add_zero, mul_one]
    have : (γ + n) * ((n : ℚ) - (α + β - γ)) + -((γ - α + n) * (γ - β + n)) = -(α * β) := by
      ring
    linear_combination this
  | succ M ih =>
    have hMn : M ≤ n := by omega
    have ih' := ih hMn
    have hMq : (M : ℚ) + 1 ≤ n := by exact_mod_cast hM
    have hMn0 : (0 : ℚ) ≤ M := Nat.cast_nonneg M
    have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => saalTerm α β γ n k)]
    have ht := saal_tele α β γ n M (by positivity) (by linarith)
      (by linarith) (by linarith)
    push_cast
    linear_combination ih' + ht

/-- The Zeilberger recurrence. -/
theorem saal_recur (α β γ : ℚ) (n : ℕ) (hγ : 0 < γ) (hA : ((n + 1 : ℕ) : ℚ) ≤ α + β - γ) :
    (γ + n) * ((n : ℚ) - (α + β - γ)) * saalSum α β γ (n + 1) +
      (-((γ - α + n) * (γ - β + n))) * saalSum α β γ n = 0 := by
  have hP := saal_partial α β γ n hγ hA n le_rfl
  have hB := saal_boundary α β γ n (by positivity) (by push_cast at hA; linarith)
  unfold saalSum
  rw [Finset.sum_range_succ (fun k => saalTerm α β γ (n + 1) k) (n + 1)]
  linear_combination hP + hB

theorem saalRhs_succ (α β γ : ℚ) (n : ℕ) :
    saalRhs α β γ (n + 1) = saalRhs α β γ n *
      ((γ - α + n) * (γ - β + n) / ((γ + n) * ((n : ℚ) - (α + β - γ)))) := by
  unfold saalRhs
  rw [poch_succ, poch_succ, poch_succ, poch_succ]
  simp only [div_eq_mul_inv, mul_inv]
  have : γ - α - β + n = (n : ℚ) - (α + β - γ) := by ring
  rw [this]
  ring

/-- **Pfaff–Saalschütz** (terminating, balanced). -/
theorem saalschutz (α β γ : ℚ) (n : ℕ) (hγ : 0 < γ) (hA : (n : ℚ) ≤ α + β - γ) :
    ∑ k ∈ Finset.range (n + 1),
        poch (-(n : ℚ)) k * poch α k * poch β k /
          ((k.factorial : ℚ) * poch γ k * poch (1 + α + β - γ - n) k) =
      poch (γ - α) n * poch (γ - β) n / (poch γ n * poch (γ - α - β) n) := by
  show saalSum α β γ n = saalRhs α β γ n
  induction n with
  | zero => simp [saalSum, saalRhs, saalTerm]
  | succ n ih =>
    have hn : (n : ℚ) ≤ α + β - γ := by
      push_cast at hA; linarith
    have ih' := ih hn
    have hr := saal_recur α β γ n hγ hA
    have hne : (γ + n) * ((n : ℚ) - (α + β - γ)) ≠ 0 := by
      have h1 : γ + n ≠ 0 := by positivity
      have h2 : (n : ℚ) - (α + β - γ) ≠ 0 := by push_cast at hA; linarith
      exact mul_ne_zero h1 h2
    rw [saalRhs_succ, ← ih', ← mul_div_assoc, eq_div_iff hne]
    linear_combination hr

end CatalanCore.NT
