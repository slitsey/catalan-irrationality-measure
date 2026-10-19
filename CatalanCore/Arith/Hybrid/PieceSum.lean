module

public import CatalanCore.NT.Interval
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# Upper Riemann sums for prime sums over a linear piece

`clsSum M c w A B = ∑_{A < p ≤ B, p prime, p ≡ c (M)} w p · log p`.

`piece_sum` : if `w p ≤ α r + β p + C` for the primes of class `c` with `s r < p ≤ t r`, and the
linear function `α + β θ` is `≥ 0` at `s, t`, then eventually in `r`
`clsSum M c w ⌊s r⌋ ⌊t r⌋ ≤ r² (∫_s^t (α + β θ) dθ / φ(M) + ε)`.
Only the two-sided PNT on intervals (`theta_interval_abs_le`) is used; the modulus `M` is a
parameter (λ: `M = 4`; P6: `M = 6`).
-/

open Finset Filter Topology CatalanCore.NT

namespace CatalanCore.Arith.Hybrid

/-- Weighted prime sum over a window and a class mod `M`. -/
noncomputable def clsSum (M : ℕ) (c : ZMod M) (w : ℕ → ℝ) (A B : ℕ) : ℝ :=
  ∑ p ∈ (Ioc A B).filter (fun p : ℕ => p.Prime ∧ (p : ZMod M) = c), w p * Real.log p

variable {M : ℕ}

lemma clsSum_eq (c : ZMod M) (w : ℕ → ℝ) (A B : ℕ) :
    clsSum M c w A B = ∑ p ∈ Ioc A B, if p.Prime ∧ (p : ZMod M) = c then w p * Real.log p else 0 := by
  unfold clsSum; rw [Finset.sum_filter]

lemma clsSum_add (c : ZMod M) (w : ℕ → ℝ) {A B D : ℕ} (h1 : A ≤ B) (h2 : B ≤ D) :
    clsSum M c w A B + clsSum M c w B D = clsSum M c w A D := by
  simp only [clsSum_eq]
  exact Finset.sum_Ioc_consecutive _ h1 h2

lemma clsSum_chain (c : ZMod M) (w : ℕ → ℝ) (A : ℕ → ℕ) (hA : Monotone A) (n : ℕ) :
    clsSum M c w (A 0) (A n) = ∑ i ∈ range n, clsSum M c w (A i) (A (i + 1)) := by
  induction n with
  | zero => simp [clsSum]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, clsSum_add c w (hA (Nat.zero_le k)) (hA (Nat.le_succ k))]

lemma clsSum_le_cell (c : ZMod M) (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) {K : ℝ}
    (h : ∀ p, A < p → p ≤ B → p.Prime → (p : ZMod M) = c → w p ≤ K) :
    clsSum M c w A B ≤ K * (thetaClassN M c B - thetaClassN M c A) := by
  rw [thetaClassN_sub M c hAB, Finset.mul_sum]
  unfold clsSum
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := by simpa using hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp2.one_lt.le)
  exact mul_le_mul_of_nonneg_right (h p hp1.1 hp1.2 hp2 hp3) hlog

/-- Midpoint sum of a linear function over a uniform grid. -/
lemma mid_sum (α β s t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, (α + β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) + |β| * ((t - s) / n) / 2) *
        ((t - s) / n) =
      α * (t - s) + β * (t ^ 2 - s ^ 2) / 2 + |β| * (t - s) * ((t - s) / n) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have key : ∀ k : ℕ, ∑ i ∈ range k, ((i : ℝ) + 1 / 2) = (k : ℝ) ^ 2 / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have e : ∀ i : ℕ, (α + β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) + |β| * ((t - s) / n) / 2) *
        ((t - s) / n) = (α + β * s + |β| * ((t - s) / n) / 2) * ((t - s) / n) +
          β * ((t - s) / n) ^ 2 * ((i : ℝ) + 1 / 2) := by
    intro i; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

end CatalanCore.Arith.Hybrid
