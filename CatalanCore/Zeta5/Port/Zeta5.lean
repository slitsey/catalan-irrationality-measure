module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Zeta5.lean (Moritz Firsching); changes: module conversion (module/public import/expose), imports renamed to CatalanCore.Zeta5.Port. -/

/-!
# `ζ(5)` as a real number
-/

namespace Apery

/-- `ζ(5)` as a real number. -/
noncomputable def zeta5 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 5

/-- Mathlib's `riemannZeta 5` is the real number `zeta5`. -/
theorem riemannZeta_five : riemannZeta 5 = (zeta5 : ℂ) := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  rw [Nat.cast_ofNat] at h
  rw [h, zeta5, Complex.ofReal_tsum]
  push_cast
  rfl

end Apery
