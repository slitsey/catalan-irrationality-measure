module
public import CatalanArchive.CatalanMeasure.Parametric.U3ChebyshevFrobenius
public import CatalanMeasure.Parametric.ChebyshevDifferences
@[expose] public section

/-!
# The doubled Chebyshev Frobenius identity (identity K6)

Over any commutative ring, `U_{m-1} T_n - T_m U_{n-1} = U_{m-n-1}`.  In
characteristic `p` (odd prime) with `m = 2p` this becomes
`2 X^p (X^2-1)^((p-1)/2) T_n - (2 X^(2p) - 1) U_{n-1} = U_{2p-n-1}`,
the algebraic core of identity K6 in Lemma U6.
-/

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

/-- `U_{m-1} T_n - T_m U_{n-1} = U_{m-n-1}` over any commutative ring. -/
theorem chebyshev_U_T_sub (R : Type*) [CommRing R] (m n : ℤ) :
    Chebyshev.U R (m - 1) * Chebyshev.T R n - Chebyshev.T R m * Chebyshev.U R (n - 1) =
      Chebyshev.U R (m - n - 1) := by
  set G : ℤ → R[X] := fun n =>
    Chebyshev.U R (m - 1) * Chebyshev.T R n - Chebyshev.T R m * Chebyshev.U R (n - 1) -
      Chebyshev.U R (m - n - 1) with hG
  have hrec : ∀ n : ℤ, G (n + 2) = 2 * X * G (n + 1) - G n := by
    intro n
    have t1 := Chebyshev.T_add_two R n
    have u1 := Chebyshev.U_add_two R (n - 1)
    have u3 := Chebyshev.U_sub_two R (m - n - 1)
    rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at u1
    have e1 : m - (n + 2) - 1 = m - n - 1 - 2 := by ring
    have e2 : m - (n + 1) - 1 = m - n - 1 - 1 := by ring
    have e3 : n + 1 - 1 = n := by ring
    have e4 : n + 2 - 1 = n + 1 := by ring
    simp only [hG, e1, e2, e3, e4]
    linear_combination (Chebyshev.U R (m - 1)) * t1 - (Chebyshev.T R m) * u1 - u3
  have h0 : G 0 = 0 := by
    simp [hG, Chebyshev.T_zero, Chebyshev.U_neg_one]
  have h1 : G 1 = 0 := by
    have c3 := Chebyshev.T_eq_U_sub_X_mul_U R m
    have c2 := Chebyshev.U_add_one R (m - 1)
    rw [show m - 1 + 1 = m by ring] at c2
    simp only [hG, Chebyshev.T_one, Chebyshev.U_zero, sub_self]
    linear_combination (-1 : R[X]) * c3 + (-1 : R[X]) * c2
  have key : ∀ k : ℤ, G k = 0 := by
    intro k
    refine Chebyshev.induct (fun k => G k = 0) h0 h1 ?_ ?_ k
    · intro n h1' h0'
      have := hrec n
      simp only [h1', h0', mul_zero, sub_zero] at this
      exact this
    · intro n h0' h1'
      have := hrec (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 2 = -(n : ℤ) + 1 by ring,
        show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at this
      simp only [h0', h1', mul_zero, zero_sub] at this
      exact neg_eq_zero.mp this.symm
  have := key n
  simp only [hG] at this
  linear_combination this

section
variable (p : ℕ) [hp : Fact p.Prime]

theorem zmod_chebyshev_T_two_mul_prime (hp2 : p ≠ 2) :
    Chebyshev.T (ZMod p) (2 * (p : ℤ)) = 2 * X ^ (2 * p) - 1 := by
  rw [Chebyshev.T_mul, Chebyshev.T_two, zmod_chebyshev_T_prime p hp2]
  simp only [sub_comp, mul_comp, ofNat_comp, pow_comp, X_comp, one_comp]
  rw [← pow_mul, mul_comm p 2]; simp

theorem zmod_chebyshev_U_two_mul_prime (hp2 : p ≠ 2) :
    Chebyshev.U (ZMod p) (2 * (p : ℤ) - 1) = 2 * X ^ p * (X ^ 2 - 1) ^ ((p - 1) / 2) := by
  have h := chebyshev_U_difference (ZMod p) (p : ℤ) p
  rw [show (p : ℤ) + (p : ℤ) - 1 = 2 * (p : ℤ) - 1 by ring,
    show (p : ℤ) - (p : ℤ) - 1 = -1 by ring, Chebyshev.U_neg_one,
    zmod_chebyshev_T_prime p hp2, zmod_chebyshev_U_prime p hp2] at h
  rw [sub_zero] at h
  rw [h]

/-- Identity K6, in characteristic `p`. -/
theorem zmod_chebyshev_K6 (hp2 : p ≠ 2) (o : ℤ) :
    2 * X ^ p * (X ^ 2 - 1) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) o -
        (2 * X ^ (2 * p) - 1) * Chebyshev.U (ZMod p) (o - 1) =
      Chebyshev.U (ZMod p) (2 * (p : ℤ) - o - 1) := by
  have i := chebyshev_U_T_sub (ZMod p) (2 * (p : ℤ)) o
  rw [zmod_chebyshev_U_two_mul_prime p hp2, zmod_chebyshev_T_two_mul_prime p hp2] at i
  exact i

end

end
end CatalanMeasure.Parametric
