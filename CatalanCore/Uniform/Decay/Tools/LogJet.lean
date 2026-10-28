module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
@[expose] public section

/-!
# Order-`m` logarithmic jet remainder (generic in `m`)

For `‖z‖ ≤ r < 1` and `m ≥ 1`:
`‖log (1 - z) + ∑_{k<m} z^k/k‖ ≤ r^m / (m (1 - r))`   (the `k = 0` term is `0`).

Weighted form: for a term `P s^j log (1 - q s)` with `‖s‖ ≤ h`, `r = ‖q‖ h < 1`,
the order-`n` jet remainder is at most `‖P‖ h^j r^(n-j) / ((n-j)(1-r))` (`j < n`).
The jet of a sum over `j < n` is bounded by the sum of these bounds.
-/

namespace CatalanCore.Uniform.Decay.Tools

open Finset

/-- Truncated logarithm jet: `∑_{k<m} z^k/k`, approximating `-log (1 - z)`. -/
noncomputable def logJet (m : ℕ) (z : ℂ) : ℂ := ∑ k ∈ range m, z ^ k / (k : ℂ)

/-- Tail bound for the complex logarithm jet of any order `m ≥ 1`. -/
theorem norm_log_add_logJet_le {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ‖Complex.log (1 - z) + logJet m z‖ ≤ r ^ m / ((m : ℝ) * (1 - r)) := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz hr
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hz
  have hs := Complex.hasSum_taylorSeries_neg_log hz1
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => z ^ n / (n : ℂ)) m hs.summable
  rw [hs.tsum_eq] at hsplit
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- tail summand bound
  have hg : HasSum (fun k : ℕ => r ^ (k + m) / (m : ℝ))
      (r ^ m / ((m : ℝ) * (1 - r))) := by
    have := (hasSum_geometric_of_lt_one hr0 hr).mul_left (r ^ m / (m : ℝ))
    convert this using 1
    · ext k; rw [pow_add]; ring
    · field_simp
  have htail : ‖∑' k : ℕ, z ^ (k + m) / ((k + m : ℕ) : ℂ)‖ ≤ r ^ m / ((m : ℝ) * (1 - r)) := by
    refine tsum_of_norm_bounded hg (fun k => ?_)
    rw [norm_div, norm_pow, Complex.norm_natCast]
    have hkm : (m : ℝ) ≤ ((k + m : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    calc ‖z‖ ^ (k + m) / ((k + m : ℕ) : ℝ) ≤ ‖z‖ ^ (k + m) / (m : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hm0 hkm
      _ ≤ r ^ (k + m) / (m : ℝ) := by
          gcongr
  have heq : Complex.log (1 - z) + logJet m z = -∑' k : ℕ, z ^ (k + m) / ((k + m : ℕ) : ℂ) := by
    unfold logJet
    have h := hsplit
    -- h : ∑ k<m, f k + ∑' k, f (k+m) = -log (1 - z)
    linear_combination h
  rw [heq, norm_neg]
  exact htail

/-- Real form: `|log (1 - x) + ∑_{k<m} x^k/k| ≤ r^m/(m(1-r))` for `|x| ≤ r < 1`. -/
theorem abs_log_add_logJet_le {x r : ℝ} (hx : |x| ≤ r) (hr : r < 1) {m : ℕ} (hm : 1 ≤ m) :
    |Real.log (1 - x) + ∑ k ∈ range m, x ^ k / (k : ℝ)| ≤ r ^ m / ((m : ℝ) * (1 - r)) := by
  have h := norm_log_add_logJet_le (z := (x : ℂ)) (r := r) (by simpa using hx) hr hm
  have hx1 : |x| < 1 := lt_of_le_of_lt hx hr
  have hpos : 0 < 1 - x := by linarith [(abs_lt.mp hx1).2]
  have hc : Complex.log (1 - (x : ℂ)) = ((Real.log (1 - x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_log hpos.le]
  have : Complex.log (1 - (x : ℂ)) + logJet m (x : ℂ)
      = (((Real.log (1 - x) + ∑ k ∈ range m, x ^ k / (k : ℝ) : ℝ)) : ℂ) := by
    rw [hc]; unfold logJet; push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Jet of `P s^j log (1 - q s)` of total order `n` (`j < n`): `-P s^j ∑_{k<n-j} (qs)^k/k`. -/
noncomputable def termJet (n j : ℕ) (P q s : ℂ) : ℂ := - (P * s ^ j * logJet (n - j) (q * s))

/-- Remainder bound for one term, any order `n`, any index `j < n`. -/
theorem norm_term_remainder_le {P q s : ℂ} {h : ℝ} (hs : ‖s‖ ≤ h) (hr : ‖q‖ * h < 1)
    {n j : ℕ} (hj : j < n) :
    ‖P * s ^ j * Complex.log (1 - q * s) - termJet n j P q s‖ ≤
      ‖P‖ * h ^ j * ((‖q‖ * h) ^ (n - j) / (((n - j : ℕ) : ℝ) * (1 - ‖q‖ * h))) := by
  have hh : 0 ≤ h := le_trans (norm_nonneg _) hs
  have hqs : ‖q * s‖ ≤ ‖q‖ * h := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)
  have key := norm_log_add_logJet_le hqs hr (m := n - j) (by omega)
  have e : P * s ^ j * Complex.log (1 - q * s) - termJet n j P q s
      = (P * s ^ j) * (Complex.log (1 - q * s) + logJet (n - j) (q * s)) := by
    unfold termJet; ring
  rw [e, norm_mul, norm_mul, norm_pow]
  have h1 : ‖P‖ * ‖s‖ ^ j ≤ ‖P‖ * h ^ j := by
    gcongr
  calc ‖P‖ * ‖s‖ ^ j * ‖Complex.log (1 - q * s) + logJet (n - j) (q * s)‖
      ≤ ‖P‖ * h ^ j * (((‖q‖ * h) ^ (n - j)) / (((n - j : ℕ) : ℝ) * (1 - ‖q‖ * h))) := by
        apply mul_le_mul h1 key (norm_nonneg _) (by positivity)

/-- The full order-`n` jet of `∑_{j<n} P_j s^j log (1 - q s)`. -/
noncomputable def jet (n : ℕ) (P : ℕ → ℂ) (q s : ℂ) : ℂ :=
  ∑ j ∈ range n, termJet n j (P j) q s

/-- The remainder bound `∑_{j<n} |P_j| h^j r^(n-j)/((n-j)(1-r))`. -/
noncomputable def jetBound (n : ℕ) (P : ℕ → ℂ) (q : ℂ) (h : ℝ) : ℝ :=
  ∑ j ∈ range n, ‖P j‖ * h ^ j *
    ((‖q‖ * h) ^ (n - j) / (((n - j : ℕ) : ℝ) * (1 - ‖q‖ * h)))

/-- Generic order-`n` logarithmic jet remainder for `∑_{j<n} P_j s^j log (1 - q s)`. -/
theorem norm_jet_remainder_le (n : ℕ) (P : ℕ → ℂ) {q s : ℂ} {h : ℝ} (hs : ‖s‖ ≤ h)
    (hr : ‖q‖ * h < 1) :
    ‖(∑ j ∈ range n, P j * s ^ j) * Complex.log (1 - q * s) - jet n P q s‖ ≤
      jetBound n P q h := by
  have e : (∑ j ∈ range n, P j * s ^ j) * Complex.log (1 - q * s) - jet n P q s
      = ∑ j ∈ range n, (P j * s ^ j * Complex.log (1 - q * s) - termJet n j (P j) q s) := by
    unfold jet; rw [Finset.sum_mul, Finset.sum_sub_distrib]
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  exact norm_term_remainder_le hs hr (Finset.mem_range.mp hj)

end CatalanCore.Uniform.Decay.Tools
