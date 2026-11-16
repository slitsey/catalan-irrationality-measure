module

public import CatalanCore.Zeta5.Potential.Basic

/-!
# Z5-POTENTIAL, part 6: evaluators for the closed forms (rational arithmetic only)

Structural recursion over the coefficient list (no well-founded recursion, no `List.mapIdx`),
over `ℚ`, with one transfer lemma each back to the real sums of `Closed`:

* `energyAux m cs`: `Σ c_i²/(2(m+i))` (the energy sum of ZD14);
* `tailAux q m p cs`: `Σ c_i q^{m+i}/(m+i)` with running power `p = q^m` (the cosh branch of ZD13,
  `q = e^{-w}` rational);
* `chebAux σ x k up u cs`: `Σ c_i T_{k+i}(x)/(k+i)` by the three-term recurrence on the scaled
  states `u_k = σ^k T_k(x)` (`u_{k+1} = 2xσ u_k - σ² u_{k-1}`), with the scaled coefficients
  `c_k/σ^k` in the list; `σ = 1` is the plain recurrence, a power of two (or its inverse) removes the
  2-adic structure of the states (lean-efficient §1/§3.8).  The only transcendental inputs of the
  closed forms are `log(b/4)` and, outside the support, `log r`: they are read from the shared
  checked log tables by the cell checker and never appear here.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Zeta5.Potential

/-- Energy sum `Σ_{i<len} c_i² / (2(m+i))` over the coefficient list `cs = [c_m, c_{m+1}, …]`
(structural recursion on the list). -/
def energyAux : ℕ → List ℚ → ℚ
  | _, [] => 0
  | k, c :: cs => c ^ 2 / (2 * (k : ℚ)) + energyAux (k + 1) cs

theorem energyAux_cast (c : ℕ → ℝ) (cs : List ℚ) :
    ∀ (m : ℕ), (∀ i (hi : i < cs.length), c (m + i) = ((cs[i] : ℚ) : ℝ)) →
      ((energyAux m cs : ℚ) : ℝ) =
        ∑ i ∈ Finset.range cs.length, c (m + i) ^ 2 / (2 * ((m + i : ℕ) : ℝ)) := by
  induction cs with
  | nil => intro m _; simp [energyAux]
  | cons a cs ih =>
    intro m h
    rw [energyAux, List.length_cons, Finset.sum_range_succ']
    push_cast
    have h0 := h 0 (by simp)
    have := ih (m + 1) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rw [show m + 1 + i = m + (i + 1) by ring]; simpa using this)
    rw [this, add_comm]
    simp only [Nat.add_zero, List.getElem_cons_zero, Nat.cast_add] at h0 ⊢
    rw [h0]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show m + 1 + i = m + (i + 1) by ring]
      ring_nf
    · ring

/-- Geometric-weight tail `Σ c_i q^{m+i}/(m+i)` with running power `p = q^m`. -/
def tailAux (q : ℚ) : ℕ → ℚ → List ℚ → ℚ
  | _, _, [] => 0
  | k, p, c :: cs => c * p / (k : ℚ) + tailAux q (k + 1) (p * q) cs

theorem tailAux_cast (q : ℚ) (c : ℕ → ℝ) (cs : List ℚ) :
    ∀ (m : ℕ) (p : ℚ), p = q ^ m → (∀ i (hi : i < cs.length), c (m + i) = ((cs[i] : ℚ) : ℝ)) →
      ((tailAux q m p cs : ℚ) : ℝ) =
        ∑ i ∈ Finset.range cs.length, c (m + i) * (q : ℝ) ^ (m + i) / ((m + i : ℕ) : ℝ) := by
  induction cs with
  | nil => intro m p _ _; simp [tailAux]
  | cons a cs ih =>
    intro m p hp h
    rw [tailAux, List.length_cons, Finset.sum_range_succ']
    push_cast
    have h0 := h 0 (by simp)
    have := ih (m + 1) (p * q) (by rw [hp]; ring) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rw [show m + 1 + i = m + (i + 1) by ring]; simpa using this)
    rw [this, add_comm]
    simp only [Nat.add_zero, List.getElem_cons_zero, Nat.cast_add] at h0 ⊢
    rw [h0, hp]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show m + 1 + i = m + (i + 1) by ring]
      push_cast; ring_nf
    · push_cast; ring

/-- Chebyshev tail `Σ c_i T_{m+1+i}(x)/(m+1+i)` by the three-term recurrence on the scaled states
`u_k = σ^k T_k(x)`: `u_{k+1} = 2 x σ u_k - σ² u_{k-1}`.  `cs` holds the scaled coefficients
`c_k / σ^k`. -/
def chebAux (σ x : ℚ) : ℕ → ℚ → ℚ → List ℚ → ℚ
  | _, _, _, [] => 0
  | k, up, u, c :: cs => c * u / (k : ℚ) + chebAux σ x (k + 1) u (2 * x * σ * u - σ ^ 2 * up) cs

/-- `T_n(x)` with a natural-number index. -/
noncomputable def chebN (x : ℝ) (n : ℕ) : ℝ := (Chebyshev.T ℝ (n : ℤ)).eval x

theorem chebN_add_two (x : ℝ) (n : ℕ) : chebN x (n + 2) = 2 * x * chebN x (n + 1) - chebN x n := by
  unfold chebN
  have := Chebyshev.T_add_two ℝ (n : ℤ)
  have h2 := congrArg (fun p => p.eval x) this
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at h2
  have e1 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have e2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  rw [e1, e2]
  exact h2

theorem chebAux_cast (σ x : ℚ) (c : ℕ → ℝ) (cs : List ℚ) :
    ∀ (m : ℕ) (up u : ℚ),
      (up : ℝ) = (σ : ℝ) ^ m * chebN (x : ℝ) m →
      (u : ℝ) = (σ : ℝ) ^ (m + 1) * chebN (x : ℝ) (m + 1) →
      (∀ i (hi : i < cs.length), ((cs[i] : ℚ) : ℝ) * (σ : ℝ) ^ (m + 1 + i) = c (m + 1 + i)) →
      ((chebAux σ x (m + 1) up u cs : ℚ) : ℝ) =
        ∑ i ∈ Finset.range cs.length, c (m + 1 + i) * chebN (x : ℝ) (m + 1 + i) /
          ((m + 1 + i : ℕ) : ℝ) := by
  induction cs with
  | nil => intro m up u _ _ _; simp [chebAux]
  | cons a cs ih =>
    intro m up u hup hu h
    rw [chebAux, List.length_cons, Finset.sum_range_succ']
    push_cast
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hnext : ((2 * x * σ * u - σ ^ 2 * up : ℚ) : ℝ) =
        (σ : ℝ) ^ (m + 1 + 1) * chebN (x : ℝ) (m + 1 + 1) := by
      rw [chebN_add_two]
      push_cast
      rw [hu, hup]
      ring
    have := ih (m + 1) u (2 * x * σ * u - σ ^ 2 * up) hu hnext (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rw [show m + 1 + 1 + i = m + 1 + (i + 1) by ring]; simpa using this)
    rw [this, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show m + 1 + 1 + i = m + 1 + (i + 1) by ring]
      push_cast; ring_nf
    · rw [hu, ← h0]
      simp only [Nat.add_zero]
      field_simp
      ring

end CatalanCore.Zeta5.Potential
