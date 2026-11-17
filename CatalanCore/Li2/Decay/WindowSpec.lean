module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

@[expose] public section
set_option Elab.async false

namespace CatalanCore.Li2.Decay

open Filter

/-- The real dilogarithm series; its summability is an analytic assembly obligation. -/
noncomputable def li2 (z : ℝ) : ℝ :=
  ∑' k : ℕ, z ^ (k + 1) / ((k : ℝ) + 1) ^ 2

/-- Uniform decay on an exponentially small real window, at scale n. -/
def WindowDecay (Q : ℕ → ℝ → ℝ) (ξ D ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
    |t| ≤ Real.exp (-ρ * (n : ℝ)) →
    |Q n (ξ + t)| ≤ Real.exp (-(D - ε) * (n : ℝ) ^ 2)

/-- A weaker rate needs no new window estimate. -/
theorem WindowDecay.mono {Q : ℕ → ℝ → ℝ} {ξ D D' ρ : ℝ}
    (h : WindowDecay Q ξ D ρ) (hD : D' ≤ D) : WindowDecay Q ξ D' ρ := by
  intro ε hε
  exact (h ε hε).mono fun n hn t ht =>
    (hn t ht).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (sub_le_sub_right hD ε))
        (sq_nonneg (n : ℝ))))

#print axioms WindowDecay.mono

end CatalanCore.Li2.Decay
