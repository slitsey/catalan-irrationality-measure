/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P000.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.Definition

set_option backward.privateInPublic true

@[expose] public section

section
/-! The original real series, with a rational parameter. All definitions
are total; convergence only uses the displayed strict absolute-value bound. -/
namespace CatalanCore.Li2.Port.Unified.ParameterFamily
noncomputable section

 def r (lam : ℚ) : ℝ :=
  ∑' k : ℕ, (lam : ℝ) ^ (k+1) / ((k : ℝ)+1)^2

 theorem term_abs_bound (lam : ℚ) (k : ℕ) :
    |(lam : ℝ) ^ (k+1) / ((k : ℝ)+1)^2| ≤ |(lam : ℝ)|^(k+1) := by
  rw [abs_div, abs_pow, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (k:ℝ)+1)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (1 : ℝ) ≤ ((k : ℝ)+1)^2 := by nlinarith
  exact div_le_self (by positivity) hd

 theorem summable_abs_r (lam : ℚ) (hlam : |(lam : ℝ)| < 1) :
    Summable (fun k : ℕ => |(lam : ℝ)^(k+1) / ((k : ℝ)+1)^2|) := by
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (term_abs_bound lam)
  simpa only [pow_succ] using
    (summable_geometric_of_lt_one (abs_nonneg (lam : ℝ)) hlam).mul_right |(lam : ℝ)|

 theorem summable_r (lam : ℚ) (hlam : |(lam : ℝ)| < 1) :
    Summable (fun k : ℕ => (lam : ℝ)^(k+1) / ((k : ℝ)+1)^2) :=
  summable_abs_iff.mp (summable_abs_r lam hlam)

 theorem r_negHalf : r (-1/2) = CatalanCore.Li2.Port.Li2.li2NegHalf := by
  norm_num [r, CatalanCore.Li2.Port.Li2.li2NegHalf]

end
end CatalanCore.Li2.Port.Unified.ParameterFamily

end


end
