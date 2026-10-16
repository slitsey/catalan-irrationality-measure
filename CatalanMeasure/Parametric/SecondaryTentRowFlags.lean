module
public import CatalanMeasure.Parametric.SecondaryTentRowPolynomial
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

/-- Exact cancellation of both ramified branch factors in the natural
`(H_U,H_V)` reconstruction numerator. The inputs are the polynomial
quotients supplied by the U/V flags, whose total x-degree is `N+n` on
both sides. Thus they can use one common homogeneous degree. -/
theorem secondaryTent_row_UV_flag_factorization {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (N n m p : ℕ) (U V : K[X])
    (hp : p=2*n+1) (hU : U.natDegree ≤ m) (hV : V.natDegree ≤ m) :
    (X-1)^p * secondaryTentRowInput (N+n+m) ((X-1)^N * ((X+1)^n * U)) +
      (X+1)^p * secondaryTentRowInput (N+n+m) ((X-1)^(N+n) * V) =
    (X-1)^(p+2*N-1) * (X+1)^(p-1) *
      ((X-1) * secondaryTentRowInput m U + (X+1) * secondaryTentRowInput m V) := by
  have hlin : ((X+1 : K[X])^n * U).natDegree ≤ n+m := by
    exact natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_pow_le.trans (by simp)) hU)
  have hsum : N+n+m = N+(n+m) := by omega
  rw [hsum, secondaryTent_rowInput_X_sub_one_pow_mul h2 N (n+m) _ hlin,
    secondaryTent_rowInput_X_add_one_pow_mul h2 n m U hU]
  rw [← hsum, secondaryTent_rowInput_X_sub_one_pow_mul h2 (N+n) m V hV]
  have hp₀ : p-1=2*n := by omega
  have hp₂ : p+2*N-1=2*(N+n) := by omega
  rw [hp₂, hp₀, hp]
  simp only [Nat.mul_add, pow_add, pow_one]
  ring

end
end CatalanMeasure.Parametric
