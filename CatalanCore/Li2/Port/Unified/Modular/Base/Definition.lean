/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/Definition.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

set_option backward.privateInPublic true

@[expose] public section

/-! The real value at -1/2 is defined by its series, with absolute convergence. -/
open scoped BigOperators
namespace CatalanCore.Li2.Port.Li2

noncomputable def li2NegHalf : ℝ :=
  ∑' k : ℕ, (-1 / 2 : ℝ) ^ (k+1) / ((k : ℝ)+1)^2

theorem li2_term_abs_bound (k : ℕ) :
    |(-1 / 2 : ℝ) ^ (k+1) / ((k : ℝ)+1)^2| ≤ (1/2 : ℝ)^(k+1) := by
  rw [abs_div, abs_pow, abs_pow]
  norm_num
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (1 : ℝ) ≤ ((k : ℝ)+1)^2 := by nlinarith
  exact div_le_self (by positivity) hd

theorem summable_abs_li2NegHalf :
    Summable (fun k : ℕ => |(-1/2 : ℝ)^(k+1) / ((k : ℝ)+1)^2|) := by
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) li2_term_abs_bound
  simpa only [pow_succ, one_div] using
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_right (1/2 : ℝ)

theorem summable_li2NegHalf :
    Summable (fun k : ℕ => (-1/2 : ℝ)^(k+1) / ((k : ℝ)+1)^2) :=
  summable_abs_iff.mp summable_abs_li2NegHalf

end CatalanCore.Li2.Port.Li2

end
