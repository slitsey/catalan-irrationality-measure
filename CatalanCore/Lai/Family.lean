module

public import CatalanCore.Lai.Construction
public import CatalanCore.Frame.Spec
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Lai's polynomial families (ledger LA06-LA08)

The plane family `laiPlaneFam a b` approximates `aζ(3) + bζ(4)` and the ratio family `laiRatioFam`
approximates `ζ(3)/ζ(4)` (so `ζ(3)/π⁴ = (ζ(3)/ζ(4))/90`).  Both are `PolyFamily` with index type `ℕ`,
`deg n = 3n`, `Adm n := 1 ≤ n`, and scale `n` (`id`).

* `Q n` is the specialisation of the homogeneous determinant `laiJ n` (Lai (2.5)): at `(a, b, X)` for the
  plane, at `(1, -X, 0)` for the ratio (the variable `X` is the ratio `y`).
* LA08: `q^{3n} Q_n(p/q) = J_n(qa, qb, p)` (plane) and `q^{3n} Q_n(p/q) = J_n(q, -p, 0)` (ratio), so integrality
  of the scaled values is a statement about the *multivariate* polynomial `laiJ n`.
* `evalR` at `const + t` is `J_n` at the shifted third coordinate; at `t = 0` it is the determinant of the
  series forms (2.3) (`laiJ_eval_det`).
-/

open Polynomial Finset
open scoped Nat

namespace CatalanCore.Lai

section Constants

/-- `ζ(4) = π⁴/90`. -/
theorem zeta4_eq_pi : zeta4 = Real.pi ^ 4 / 90 := by
  unfold zeta4
  calc ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 4 = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 := by
        simpa using hasSum_zeta_four.summable.tsum_eq_zero_add.symm
    _ = _ := hasSum_zeta_four.tsum_eq

theorem summable_zeta (s : ℕ) (hs : 2 ≤ s) : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) :=
  DoublePole.summable_zetaTerm s hs

theorem two_terms_le_zeta (s : ℕ) (hs : 2 ≤ s) :
    1 + 1 / 2 ^ s ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s := by
  have h := (summable_zeta s hs).sum_le_tsum (range 2) (fun k _ => by positivity)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- `ζ(3) ≤ 5/4`. -/
theorem zeta3_le : zeta3 ≤ 5 / 4 := by
  unfold zeta3
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) fun N => ?_
  have key : ∀ N : ℕ, ∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 3 ≤
      5 / 4 - 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h1 : 1 / (((N + 1 : ℕ) : ℝ) + 1) ^ 3 ≤
          1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) - 1 / (2 * (((N + 1 : ℕ) : ℝ) + 1) * (((N + 1 : ℕ) : ℝ) + 2)) := by
        push_cast
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hN hN, mul_nonneg (mul_nonneg hN hN) hN, mul_nonneg (mul_nonneg hN hN) (mul_nonneg hN hN)]
      linarith
  rcases N with _ | N
  · norm_num
  · have := key N
    have hpos : (0 : ℝ) < 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by positivity
    linarith

theorem zeta3_ge : 9 / 8 ≤ zeta3 := by
  have := two_terms_le_zeta 3 (by norm_num)
  unfold zeta3
  norm_num at this ⊢
  linarith

theorem zeta4_ge : 17 / 16 ≤ zeta4 := by
  have := two_terms_le_zeta 4 (by norm_num)
  unfold zeta4
  norm_num at this ⊢
  linarith

theorem zeta4_le : zeta4 ≤ 1094 / 1000 := by
  rw [zeta4_eq_pi]
  have h1 : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  have h2 : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ Real.pi_pos.le h1 4
  norm_num at h2 ⊢
  linarith

theorem zeta3_pos : 0 < zeta3 := by linarith [zeta3_ge]

theorem zeta4_pos : 0 < zeta4 := by linarith [zeta4_ge]

/-- **LA06.**  `y* = ζ(3)/ζ(4) ∈ (1, 6/5)`. -/
theorem ystar_bounds : 1 < zeta3 / zeta4 ∧ zeta3 / zeta4 < 6 / 5 := by
  have h3 := zeta3_ge
  have h3' := zeta3_le
  have h4 := zeta4_ge
  have h4' := zeta4_le
  constructor
  · rw [lt_div_iff₀ zeta4_pos]; linarith
  · rw [div_lt_iff₀ zeta4_pos]; linarith

end Constants

section Families

open CatalanCore

/-- The plane family: `Q_n(X) = J_n(a, b, X)`. -/
noncomputable def laiPlaneFam (a b : ℤ) : PolyFamily where
  const := (a : ℝ) * zeta3 + (b : ℝ) * zeta4
  ι := ℕ
  deg := fun n => 3 * n
  Adm := fun n => 1 ≤ n
  Q := fun n => MvPolynomial.aeval ![Polynomial.C (a : ℚ), Polynomial.C (b : ℚ), Polynomial.X] (laiJ n)

/-- The ratio family: `Q_n(y) = J_n(1, -y, 0)`, approximating `y* = ζ(3)/ζ(4)`. -/
noncomputable def laiRatioFam : PolyFamily where
  const := zeta3 / zeta4
  ι := ℕ
  deg := fun n => 3 * n
  Adm := fun n => 1 ≤ n
  Q := fun n => MvPolynomial.aeval ![1, -Polynomial.X, 0] (laiJ n)

theorem natDegree_plane_Q (a b : ℤ) (n : ℕ) : ((laiPlaneFam a b).Q n).natDegree ≤ 3 * n := by
  refine natDegree_aeval_le (isHomogeneous_laiJ n) _ fun i => ?_
  fin_cases i <;> simp

theorem natDegree_ratio_Q (n : ℕ) : (laiRatioFam.Q n).natDegree ≤ 3 * n := by
  refine natDegree_aeval_le (isHomogeneous_laiJ n) _ fun i => ?_
  fin_cases i <;> simp

theorem plane_evalQ (a b : ℤ) (n : ℕ) (x : ℚ) :
    (laiPlaneFam a b).evalQ n x = MvPolynomial.eval ![(a : ℚ), (b : ℚ), x] (laiJ n) := by
  unfold PolyFamily.evalQ
  show Polynomial.eval x (MvPolynomial.aeval _ (laiJ n)) = _
  rw [eval_aeval]
  have hv : (fun i => Polynomial.eval x (![Polynomial.C (a : ℚ), Polynomial.C (b : ℚ), Polynomial.X] i)) =
      ![(a : ℚ), (b : ℚ), x] := by
    funext i; fin_cases i <;> simp
  rw [hv]

theorem ratio_evalQ (n : ℕ) (x : ℚ) :
    laiRatioFam.evalQ n x = MvPolynomial.eval ![(1 : ℚ), -x, 0] (laiJ n) := by
  unfold PolyFamily.evalQ
  show Polynomial.eval x (MvPolynomial.aeval _ (laiJ n)) = _
  rw [eval_aeval]
  have hv : (fun i => Polynomial.eval x (![1, -Polynomial.X, 0] i)) = ![(1 : ℚ), -x, 0] := by
    funext i; fin_cases i <;> simp
  rw [hv]

/-- **LA08 (plane).**  `q^{3n} Q_n(p/q) = J_n(qa, qb, p)` for every nonzero integer `q`. -/
theorem plane_scaled (a b : ℤ) (n : ℕ) (p q : ℤ) (hq : (q : ℚ) ≠ 0) :
    (q : ℚ) ^ (3 * n) * (laiPlaneFam a b).evalQ n ((p : ℚ) / q) =
      MvPolynomial.eval ![(q : ℚ) * a, (q : ℚ) * b, (p : ℚ)] (laiJ n) := by
  rw [plane_evalQ]
  have h := eval_smul_of_isHomogeneous (isHomogeneous_laiJ n) (q : ℚ) ![(a : ℚ), (b : ℚ), (p : ℚ) / q]
  have hv : (fun i => (q : ℚ) * ![(a : ℚ), (b : ℚ), (p : ℚ) / q] i) = ![(q : ℚ) * a, (q : ℚ) * b, (p : ℚ)] := by
    funext i; fin_cases i <;> simp [mul_div_cancel₀ _ hq]
  rw [hv] at h
  exact h.symm

/-- **LA08 (ratio).**  `q^{3n} Q_n(p/q) = J_n(q, -p, 0)` for every nonzero integer `q`. -/
theorem ratio_scaled (n : ℕ) (p q : ℤ) (hq : (q : ℚ) ≠ 0) :
    (q : ℚ) ^ (3 * n) * laiRatioFam.evalQ n ((p : ℚ) / q) =
      MvPolynomial.eval ![(q : ℚ), -(p : ℚ), 0] (laiJ n) := by
  rw [ratio_evalQ]
  have h := eval_smul_of_isHomogeneous (isHomogeneous_laiJ n) (q : ℚ) ![(1 : ℚ), -((p : ℚ) / q), 0]
  have hv : (fun i => (q : ℚ) * ![(1 : ℚ), -((p : ℚ) / q), 0] i) = ![(q : ℚ), -(p : ℚ), 0] := by
    funext i; fin_cases i
    · simp
    · simp [mul_div_cancel₀ _ hq]
    · simp
  rw [hv] at h
  exact h.symm

/-- Real evaluation of the plane family: `Q_n(x) = J_n(a, b, x)`. -/
theorem plane_evalR (a b : ℤ) (n : ℕ) (x : ℝ) :
    (laiPlaneFam a b).evalR n x = MvPolynomial.aeval ![(a : ℝ), (b : ℝ), x] (laiJ n) := by
  unfold PolyFamily.evalR
  have h := congrArg (fun T => T (laiJ n))
    (MvPolynomial.comp_aeval (R := ℚ) (σ := Fin 3) (B := ℝ) (S₁ := ℚ[X])
      (f := ![Polynomial.C (a : ℚ), Polynomial.C (b : ℚ), Polynomial.X]) (Polynomial.aeval x))
  simp only [AlgHom.comp_apply] at h
  change (Polynomial.aeval x) (MvPolynomial.aeval _ (laiJ n)) = _
  rw [h]
  have hv : (fun i => Polynomial.aeval x (![Polynomial.C (a : ℚ), Polynomial.C (b : ℚ), Polynomial.X] i)) =
      ![(a : ℝ), (b : ℝ), x] := by
    funext i; fin_cases i <;> simp
  rw [hv]

/-- Real evaluation of the ratio family: `Q_n(y) = J_n(1, -y, 0)`. -/
theorem ratio_evalR (n : ℕ) (x : ℝ) :
    laiRatioFam.evalR n x = MvPolynomial.aeval ![(1 : ℝ), -x, 0] (laiJ n) := by
  unfold PolyFamily.evalR
  have h := congrArg (fun T => T (laiJ n))
    (MvPolynomial.comp_aeval (R := ℚ) (σ := Fin 3) (B := ℝ) (S₁ := ℚ[X])
      (f := ![1, -Polynomial.X, 0]) (Polynomial.aeval x))
  simp only [AlgHom.comp_apply] at h
  change (Polynomial.aeval x) (MvPolynomial.aeval _ (laiJ n)) = _
  rw [h]
  have hv : (fun i => Polynomial.aeval x ((![1, -Polynomial.X, 0] : Fin 3 → ℚ[X]) i)) = ![(1 : ℝ), -x, 0] := by
    funext i; fin_cases i <;> simp
  rw [hv]

/-- At the constant, the plane family's value is the Hankel determinant of the series forms (2.3). -/
theorem plane_evalR_const (a b : ℤ) (n : ℕ) :
    (laiPlaneFam a b).evalR n (laiPlaneFam a b).const =
      ((∏ i ∈ range (3 * n), ((i ! : ℝ)) ^ 2)⁻¹) *
        (Matrix.of fun i j : Fin (3 * n) =>
          -3 * (a : ℝ) * ∑' m : ℕ, deriv (laiFun n (Polynomial.X ^ ((i : ℕ) + j))) ((m : ℝ) + 1) +
            (b : ℝ) * ∑' m : ℕ, deriv (deriv (laiFun n (Polynomial.X ^ ((i : ℕ) + j)))) ((m : ℝ) + 1)).det := by
  rw [plane_evalR]
  exact laiJ_eval_det n (a : ℝ) (b : ℝ)

end Families

end CatalanCore.Lai
