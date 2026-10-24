module

public import CatalanArchive.CatalanMeasure.ContentRecycledIntegerLower

@[expose] public section

#print axioms CatalanMeasure.int_dvd_after_content_gcd
#print axioms CatalanMeasure.content_recycled_dvd_integer_sum
#print axioms CatalanMeasure.exists_int_eq_content_recycled_pow_mul_aeval
#print axioms CatalanMeasure.one_le_content_recycled_pow_mul_abs_aeval
#print axioms CatalanMeasure.content_recycled_lower_bound

open Polynomial

/-- Content supported away from the recycled factor retains the full bound. -/
example (Q F : ℤ[X]) {C D : ℕ} (hC : 0 < C)
    (hQ : Q = Polynomial.C (C : ℤ) * F) (hD : F.natDegree ≤ D)
    (a : ℤ) {b B : ℕ} (hb : 0 < b) (hBb : B ∣ b)
    (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i)
    (hg : Nat.gcd C (B ^ D) = 1)
    (hne : aeval ((a : ℝ) / b) F ≠ 0) :
    1 ≤ ((b : ℝ) / B) ^ D * |aeval ((a : ℝ) / b) F| := by
  simpa only [hg, Nat.cast_one, one_mul] using
    CatalanMeasure.one_le_content_recycled_pow_mul_abs_aeval
      Q F hC hQ hD a hb hBb hcoeff hne

/-- The exact integer surviving-divisor API has no degree or reduced-fraction condition. -/
example (Q F : ℤ[X]) (a : ℤ) {C b B D : ℕ}
    (hQ : Q = Polynomial.C (C : ℤ) * F) (hB : 0 < B)
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i) :
    ((B ^ D / Nat.gcd C (B ^ D) : ℕ) : ℤ) ∣
      ∑ i ∈ Finset.range (D + 1), F.coeff i * a ^ i * (b : ℤ) ^ (D - i) :=
  CatalanMeasure.content_recycled_dvd_integer_sum Q F a hQ hB hBb hcoeff
