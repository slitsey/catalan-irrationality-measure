module

public import CatalanCore.Rect.CharZeroNV.Interpolation

@[expose] public section

/-! # The P6 increment has no rational primitive for the forward difference

The normalized increment is `(1-X)/incrementDen`. This instance is valid over
every characteristic-zero field, independently of the border dimensions.
-/

open Polynomial CatalanCore.Rect.CharZeroNV

namespace CatalanArchive.CatalanFrames.P6Hybrid.CharZeroNV

variable {K : Type*} [Field K] [CharZero K]

noncomputable def incrementDen : K[X] :=
  216 * (X + 1) * (X + C (1 / 3)) * (X + C (1 / 2))

theorem isolatedPole : IsolatedIntegerPole (incrementDen : K[X]) (1 - X) where
  pole := by simp [incrementDen]
  residue := by norm_num
  nonneg n := by
    have hn : (n : K) + 1 ≠ 0 := by exact_mod_cast (show (n : ℤ) + 1 ≠ 0 by omega)
    have h3 : (n : K) + 1 / 3 ≠ 0 := by
      intro hz
      have hz' : (3 : K) * n + 1 = 0 := by linear_combination 3 * hz
      have : (3 : ℤ) * n + 1 = 0 := by exact_mod_cast hz'
      omega
    have h2 : (n : K) + 1 / 2 ≠ 0 := by
      intro hz
      have hz' : (2 : K) * n + 1 = 0 := by linear_combination 2 * hz
      have : (2 : ℤ) * n + 1 = 0 := by exact_mod_cast hz'
      omega
    simpa [incrementDen] using mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (216 : K) ≠ 0) hn) h3) h2
  negative n := by
    have hn : -((n : K) + 2) + 1 ≠ 0 := by
      intro hz
      have : (n : K) + 1 = 0 := by linear_combination -hz
      have : (n : ℤ) + 1 = 0 := by exact_mod_cast this
      omega
    have h3 : -((n : K) + 2) + 1 / 3 ≠ 0 := by
      intro hz
      have hz' : (3 : K) * n + 5 = 0 := by linear_combination -3 * hz
      have : (3 : ℤ) * n + 5 = 0 := by exact_mod_cast hz'
      omega
    have h2 : -((n : K) + 2) + 1 / 2 ≠ 0 := by
      intro hz
      have hz' : (2 : K) * n + 3 = 0 := by linear_combination -2 * hz
      have : (2 : ℤ) * n + 3 = 0 := by exact_mod_cast hz'
      omega
    simpa [incrementDen] using mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (216 : K) ≠ 0) hn) h3) h2

theorem no_rational_antidifference (a b : K[X]) (hb : b ≠ 0) :
    incrementDen * (shift a * b - a * shift b) ≠ (1 - X) * b * shift b :=
  no_antidifference isolatedPole a b hb

noncomputable def data (U : K) : IncrementData (incrementDen : K[X]) (1 - X) :=
  quotientData incrementDen (1 - X) isolatedPole.nonneg U

theorem den_degree : (incrementDen : K[X]).natDegree ≤ 3 := by
  unfold incrementDen
  compute_degree

/-- The degree drop forced by a putative two-dimensional hybrid kernel is
impossible for the actual normalized P6 increments, at every border ratio. -/
theorem no_short_interpolant (U : K) (r m : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ r + m)
    (q p : K[X]) (hq : q.natDegree ≤ r + m - 2) (hp : p.natDegree ≤ r + m - 2)
    (hint : Interpolates (data U) (r + 2 * m) r q p) : p = 0 := by
  apply no_short_pair (data U) isolatedPole den_degree (by compute_degree)
    (r + 2 * m) r (r + m - 2) hr (by omega) (by omega) q p hq hp hint

/-- After division by the common-node factor, even value interpolation alone
is impossible at the reduced border degree. -/
theorem no_border_interpolant (U : K) (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (q p : K[X]) (hq : q.natDegree ≤ m - 1) (hp : p.natDegree ≤ m - 1)
    (hint : ∀ i < r + 2 * m, q.eval (i : K) = (data U).f i * p.eval (i : K)) :
    p = 0 := by
  apply no_value_pair (data U) isolatedPole den_degree (by compute_degree)
    (r + 2 * m) (m - 1) (by omega) q p hq hp hint

end CatalanArchive.CatalanFrames.P6Hybrid.CharZeroNV
