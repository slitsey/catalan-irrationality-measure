module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Window products

For a commutative ring `R` and naturals `n c`:
* `QQ n c = ∏_{a,b<n} (c+a+b)` (a Cauchy denominator for consecutive nodes),
* `SS n c = ∏_{t<n} (c+t)^(t+1)`,
* `PP n c = ∏_{j<n} (c+n+j)^(n-1-j)`.
The identity `QQ n c = SS n c * PP n c` shows that, after cancelling the weighted product `PP`,
only the integers `c, …, c+n-1` survive.
-/

@[expose] public section

open Finset

namespace CatalanCore

variable {R : Type*} [CommRing R]

/-- `∏_{a,b<n} (c+a+b)`. -/
def QQ (R : Type*) [CommRing R] (n c : ℕ) : R :=
  ∏ a ∈ range n, ∏ b ∈ range n, ((c + a + b : ℕ) : R)

/-- `∏_{t<n} (c+t)^(t+1)`. -/
def SS (R : Type*) [CommRing R] (n c : ℕ) : R := ∏ t ∈ range n, ((c + t : ℕ) : R) ^ (t + 1)

/-- `∏_{j<n} (c+n+j)^(n-1-j)`. -/
def PP (R : Type*) [CommRing R] (n c : ℕ) : R :=
  ∏ j ∈ range n, ((c + n + j : ℕ) : R) ^ (n - 1 - j)

lemma QQ_succ (n c : ℕ) :
    QQ R (n + 1) c = QQ R n c * (∏ b ∈ range n, ((c + n + b : ℕ) : R)) ^ 2 * ((c + n + n : ℕ) : R) := by
  unfold QQ
  rw [prod_range_succ]
  simp only [prod_range_succ, prod_mul_distrib]
  have e : ∏ a ∈ range n, ((c + a + n : ℕ) : R) = ∏ b ∈ range n, ((c + n + b : ℕ) : R) :=
    prod_congr rfl fun a _ => by rw [Nat.add_right_comm]
  rw [e]
  ring

lemma SS_succ (n c : ℕ) : SS R (n + 1) c = SS R n c * ((c + n : ℕ) : R) ^ (n + 1) := by
  unfold SS; rw [prod_range_succ]

lemma PP_succ (n c : ℕ) :
    PP R (n + 1) c * ((c + n : ℕ) : R) ^ (n + 1) =
      PP R n c * (∏ b ∈ range n, ((c + n + b : ℕ) : R)) ^ 2 * ((c + n + n : ℕ) : R) := by
  set g : ℕ → R := fun i => ((c + n + i : ℕ) : R) with hg
  have h1 : PP R (n + 1) c = ∏ j ∈ range n, g (j + 1) ^ (n - j) := by
    unfold PP
    rw [prod_range_succ]
    have : n + 1 - 1 - n = 0 := by omega
    rw [this, pow_zero, mul_one]
    refine prod_congr rfl fun j _ => ?_
    have e1 : c + (n + 1) + j = c + n + (j + 1) := by omega
    have e2 : n + 1 - 1 - j = n - j := by omega
    simp only [hg, e1, e2]
  have h0 : PP R n c = ∏ i ∈ range n, g i ^ (n - 1 - i) := rfl
  have h2 : ∏ i ∈ range (n + 1), g i ^ (n + 1 - i) = g 0 ^ (n + 1) * ∏ j ∈ range n, g (j + 1) ^ (n - j) := by
    rw [prod_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    ring
  have h3 : ∏ i ∈ range (n + 1), g i ^ (n + 1 - i) =
      (∏ i ∈ range n, g i ^ (n - 1 - i)) * (∏ i ∈ range n, g i) ^ 2 * g n := by
    rw [prod_range_succ]
    have : n + 1 - n = 1 := by omega
    rw [this, pow_one, ← prod_pow, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [← pow_add]
    congr 1
    omega
  have hg0 : g 0 = ((c + n : ℕ) : R) := by simp [hg]
  have hgn : g n = ((c + n + n : ℕ) : R) := rfl
  rw [h1, ← hg0, mul_comm, ← h2, h3, h0]

/-- The window identity. -/
theorem QQ_eq (n c : ℕ) : QQ R n c = SS R n c * PP R n c := by
  induction n with
  | zero => simp [QQ, SS, PP]
  | succ n ih =>
    rw [QQ_succ, ih, SS_succ]
    linear_combination (-(SS R n c)) * PP_succ (R := R) n c

/-- Re-indexing the triangular weight product. -/
theorem prod_prod_range_eq {M : Type*} [CommMonoid M] (K : ℕ) (f : ℕ → M) :
    ∏ k ∈ range K, ∏ j ∈ range k, f j = ∏ j ∈ range K, f j ^ (K - 1 - j) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [prod_range_succ, ih, prod_range_succ]
    have : K + 1 - 1 - K = 0 := by omega
    rw [this, pow_zero, mul_one, ← prod_mul_distrib]
    refine prod_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have : K + 1 - 1 - j = K - 1 - j + 1 := by omega
    rw [this, pow_succ]

end CatalanCore
