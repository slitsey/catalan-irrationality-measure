module

public import Mathlib.Algebra.Polynomial.Coeff
public import Lean.Elab.Tactic.Omega

/-!
# The boundary term in shifting a contact polynomial

Truncation before multiplying by the common row factor is essential. The
shift introduces exactly one boundary coefficient, uniformly over any ring.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial

noncomputable def contactTrunc {R : Type*} [Semiring R] (L : ℕ) (F : R[X]) : R[X] :=
  ∑ j ∈ Finset.range L, monomial j (F.coeff j)

theorem coeff_contactTrunc {R : Type*} [Semiring R] (L n : ℕ) (F : R[X]) :
    (contactTrunc L F).coeff n = if n < L then F.coeff n else 0 := by
  classical
  simp [contactTrunc, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]

theorem contactTrunc_X_boundary {R : Type*} [Semiring R] {L : ℕ}
    (hL : 0 < L) (F : R[X]) :
    contactTrunc L (X * F) + monomial L (F.coeff (L - 1)) =
      X * contactTrunc L F := by
  classical
  ext n
  cases n with
  | zero =>
      simp [coeff_contactTrunc, coeff_monomial, Nat.ne_of_gt hL]
  | succ k =>
      rw [coeff_add, coeff_contactTrunc, coeff_X_mul, coeff_X_mul,
        coeff_contactTrunc, coeff_monomial]
      by_cases hk : k + 1 < L
      · simp [hk, show k < L by omega, show L ≠ k + 1 by omega]
      · by_cases heq : L = k + 1
        · subst L
          simp
        · simp [hk, heq, show ¬k < L by omega]

end CatalanMeasure.Parametric
