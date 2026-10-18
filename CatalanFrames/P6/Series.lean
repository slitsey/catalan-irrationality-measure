module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.PSeries

/-!
# `L(2, χ₋₃)` as an explicit series (WP9)

`L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)² - 1/(3k+2)²)`, written out as a `tsum` (no Mathlib Dirichlet
character), in exactly the shape used by the Challenge statement:

`∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)`.

`chi3L2` is a local abbreviation for that expression (`chi3L2_def` is `rfl`); the final Challenge
file inlines it.  The summands are summable, and the series splits into its two parts.
-/

@[expose] public section

namespace CatalanFrames.P6

/-- `L(2, χ₋₃)` as a series.  The Challenge file writes the right-hand side inline. -/
noncomputable def chi3L2 : ℝ :=
  ∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)

theorem chi3L2_def : chi3L2 =
    ∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2) := rfl

/-- `∑ 1/n²` over `ℕ` (the `n = 0` term is `0`) is summable. -/
theorem summable_inv_sq : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  simp

/-- `∑ 1/(3k+r)²` is summable, for any `r`. -/
theorem summable_inv_sq_three (r : ℕ) :
    Summable (fun k : ℕ => 1 / ((3 * k + r : ℕ) : ℝ) ^ 2) := by
  have hinj : Function.Injective (fun k : ℕ => 3 * k + r) := by
    intro a b h; simp at h; omega
  exact summable_inv_sq.comp_injective hinj

theorem summable_chi3L2 :
    Summable (fun k : ℕ => 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2) :=
  (summable_inv_sq_three 1).sub (summable_inv_sq_three 2)

/-- `L = a - b` with `a = ∑ 1/(3k+1)²`, `b = ∑ 1/(3k+2)²`. -/
theorem chi3L2_eq_sub : chi3L2 =
    (∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2) - ∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2 :=
  (summable_inv_sq_three 1).tsum_sub (summable_inv_sq_three 2)

end CatalanFrames.P6
