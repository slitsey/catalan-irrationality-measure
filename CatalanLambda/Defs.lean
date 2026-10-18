import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

open Finset Matrix

namespace CatalanLambda

/-- Entries of `M0`, indexed by naturals. -/
noncomputable def M0n (a b : ℕ) : ℚ :=
  if a = b then -∑ k ∈ Icc 1 a, (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 1) ^ 2)
  else -(1 / (4 * ((max a b : ℕ) - (min a b : ℕ) : ℚ))) *
    ∑ k ∈ Ioc (min a b) (max a b), 1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1))

/-- The `h × h` rational matrix `M0`. -/
noncomputable def M0 (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := Matrix.of fun a b => M0n a b

/-- `P_h(r) = det (r I + M0)`, i.e. the value at `r` of the polynomial `P_h(X) = det (X I + M0)`. -/
noncomputable def P (h : ℕ) (r : ℚ) : ℚ := (r • (1 : Matrix (Fin h) (Fin h) ℚ) + M0 h).det

/-- `P_h(X)` as a polynomial. -/
noncomputable def Ppoly (h : ℕ) : Polynomial ℚ := (-(M0 h)).charpoly

example : M0 1 = 0 := by
  ext a b; fin_cases a; fin_cases b; simp [M0, M0n]

example : M0n 0 1 = -(1/4) * (1/12) := by
  norm_num [M0n, Finset.sum_Ioc_succ_top]

example : P 1 3 = 3 := by
  simp [P, M0, M0n]

end CatalanLambda
