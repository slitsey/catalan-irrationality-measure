module

public import CatalanCore.Rect.CharZeroNV.Interpolation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # The Hermite interpolation space has dimension at most one

The input polynomial maps may be the two barycentric coordinates of a matrix
kernel. No reduction of their common factors is needed.
-/

open Polynomial Module

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma finrank_le_one_of_two_coordinates {V : Type*} [AddCommGroup V] [Module K V]
    (a b : V →ₗ[K] K)
    (hjoint : ∀ v, a v = 0 → b v = 0 → v = 0)
    (hwedge : ∀ v w, a v * b w - a w * b v = 0) : finrank K V ≤ 1 := by
  have hi : Function.Injective a ∨ Function.Injective b := by
    by_cases ha : ∃ w, a w ≠ 0
    · obtain ⟨w, hw⟩ := ha
      left
      apply (LinearMap.ker_eq_bot).mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      apply hjoint v hv
      have hh := hwedge v w
      simp only [hv, zero_mul, zero_sub, neg_eq_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hw
    · right
      apply (LinearMap.ker_eq_bot).mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      exact hjoint v (by simpa using not_exists.mp ha v) hv
  rcases hi with hi | hi
  · simpa using a.finrank_le_finrank_of_injective hi
  · simpa using b.finrank_le_finrank_of_injective hi

theorem finrank_interpolation_le_one {V : Type*} [AddCommGroup V] [Module K V]
    {D A : K[X]} (data : IncrementData D A) (hpole : IsolatedIntegerPole D A)
    (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1)
    (r m : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ r + m)
    (p q : V →ₗ[K] K[X]) (hinj : Function.Injective p)
    (hp : ∀ v, (p v).natDegree ≤ r + m - 1)
    (hq : ∀ v, (q v).natDegree ≤ r + m - 1)
    (hint : ∀ v, Interpolates data (r + 2 * m) r (q v) (p v)) :
    finrank K V ≤ 1 := by
  let a : V →ₗ[K] K := (lcoeff K (r + m - 1)).comp p
  let b : V →ₗ[K] K := (lcoeff K (r + m - 1)).comp q
  apply finrank_le_one_of_two_coordinates a b
  · intro v ha hb
    have hp' := natDegree_le_pred (hp v) ha
    have hq' := natDegree_le_pred (hq v) hb
    have hz : p v = 0 := no_short_pair data hpole hD hA
      (r + 2 * m) r (r + m - 2) hr (by omega) (by omega)
      (q v) (p v) (by simpa [Nat.sub_sub] using hq')
      (by simpa [Nat.sub_sub] using hp') (hint v)
    exact hinj (by simpa using hz)
  · intro v w
    have he := cross_product_eq_zero data (r + 2 * m) r (r + m - 1)
      (by omega) (by omega) (q v) (p v) (q w) (p w)
      (hq v) (hp v) (hq w) (hp w) (hint v) (hint w)
    have hc := congrArg (fun z : K[X] => z.coeff ((r + m - 1) + (r + m - 1))) he
    rw [coeff_sub, coeff_mul_add_eq_of_natDegree_le (hq v) (hp w),
      coeff_mul_add_eq_of_natDegree_le (hq w) (hp v), coeff_zero] at hc
    change (p v).coeff _ * (q w).coeff _ - (p w).coeff _ * (q v).coeff _ = 0
    linear_combination -hc

end CatalanCore.Rect.CharZeroNV
