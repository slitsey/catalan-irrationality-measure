module

public import CatalanMeasure.RecycledIntegerLower
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

/-!
# Recycling after dividing common coefficient content

If `Q = C * F` with `F` integral, the recycled factor `B ^ D` can
overlap the removed content. The exact loss is `gcd C (B ^ D)`.
-/

open Polynomial

namespace CatalanMeasure

/-- Cancel the part of an integer content factor which meets a divisor. -/
theorem int_dvd_after_content_gcd {K C : ℕ} {z : ℤ} (hK : 0 < K)
    (h : (K : ℤ) ∣ (C : ℤ) * z) :
    ((K / Nat.gcd C K : ℕ) : ℤ) ∣ z := by
  have hn : K ∣ C * z.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natCast_dvd.mp h
  have hd : K ∣ Nat.gcd K C * z.natAbs := dvd_gcd_mul_of_dvd_mul hn
  have hg : 0 < Nat.gcd C K :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right C K) hK
  apply Int.natCast_dvd.mpr
  apply (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right C K) hg).mpr
  simpa only [Nat.gcd_comm] using hd

/-- The exact surviving recycled divisor in the integer evaluation sum. -/
theorem content_recycled_dvd_integer_sum (Q F : ℤ[X]) (a : ℤ) {C b B D : ℕ}
    (hQ : Q = Polynomial.C (C : ℤ) * F) (hB : 0 < B)
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i) :
    ((B ^ D / Nat.gcd C (B ^ D) : ℕ) : ℤ) ∣
      ∑ i ∈ Finset.range (D + 1), F.coeff i * a ^ i * (b : ℤ) ^ (D - i) := by
  have hs :
      (∑ i ∈ Finset.range (D + 1), Q.coeff i * a ^ i * (b : ℤ) ^ (D - i)) =
        (C : ℤ) *
          ∑ i ∈ Finset.range (D + 1), F.coeff i * a ^ i * (b : ℤ) ^ (D - i) := by
    rw [hQ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.coeff_C_mul]
    ring
  apply int_dvd_after_content_gcd (pow_pos hB D)
  rw [← hs]
  simpa only [Nat.cast_pow] using recycled_dvd_integer_sum Q a hBb hcoeff

/-- Bezout combines the canonical recycled integer and the ordinary integer
    evaluation of `F`, charging exactly the content/recycling overlap. -/
theorem exists_int_eq_content_recycled_pow_mul_aeval (Q F : ℤ[X]) {C D : ℕ}
    (hQ : Q = Polynomial.C (C : ℤ) * F) (hD : F.natDegree ≤ D)
    (a : ℤ) {b B : ℕ} (hb : 0 < b) (hBb : B ∣ b)
    (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i) :
    ∃ m : ℤ,
      (Nat.gcd C (B ^ D) : ℝ) * ((b : ℝ) / B) ^ D *
        aeval ((a : ℝ) / b) F = m := by
  have hDQ : Q.natDegree ≤ D := by
    rw [hQ]
    exact (Polynomial.natDegree_C_mul_le _ _).trans hD
  obtain ⟨m, hm⟩ := exists_int_eq_recycled_pow_mul_aeval Q hDQ a hb hBb hcoeff
  obtain ⟨z, hz⟩ := exists_int_eq_pow_mul_aeval F hD a hb
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBb hb
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have heval : aeval ((a : ℝ) / b) Q =
      (C : ℝ) * aeval ((a : ℝ) / b) F := by
    rw [hQ]
    simp
  have hcm : (C : ℝ) * ((b : ℝ) / B) ^ D *
      aeval ((a : ℝ) / b) F = m := by
    calc
      _ = ((b : ℝ) / B) ^ D * aeval ((a : ℝ) / b) Q := by rw [heval]; ring
      _ = m := hm
  have hkz : (B : ℝ) ^ D * ((b : ℝ) / B) ^ D *
      aeval ((a : ℝ) / b) F = z := by
    calc
      _ = (b : ℝ) ^ D * aeval ((a : ℝ) / b) F := by
        rw [div_pow]
        field_simp
      _ = z := hz
  let u : ℤ := Nat.gcdA C (B ^ D)
  let v : ℤ := Nat.gcdB C (B ^ D)
  have hbez : (Nat.gcd C (B ^ D) : ℝ) =
      (C : ℝ) * (u : ℝ) + (B : ℝ) ^ D * (v : ℝ) := by
    exact_mod_cast Nat.gcd_eq_gcd_ab C (B ^ D)
  refine ⟨u * m + v * z, ?_⟩
  push_cast
  calc
    _ = (u : ℝ) * ((C : ℝ) * ((b : ℝ) / B) ^ D * aeval ((a : ℝ) / b) F) +
        (v : ℝ) * ((B : ℝ) ^ D * ((b : ℝ) / B) ^ D * aeval ((a : ℝ) / b) F) := by
      rw [hbez]
      ring
    _ = _ := by rw [hcm, hkz]

/-- Content-aware recycled lower bound; no coprimality of `a,b` is needed. -/
theorem one_le_content_recycled_pow_mul_abs_aeval (Q F : ℤ[X]) {C D : ℕ}
    (hC : 0 < C) (hQ : Q = Polynomial.C (C : ℤ) * F)
    (hD : F.natDegree ≤ D) (a : ℤ) {b B : ℕ} (hb : 0 < b)
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i)
    (hne : aeval ((a : ℝ) / b) F ≠ 0) :
    1 ≤ (Nat.gcd C (B ^ D) : ℝ) * ((b : ℝ) / B) ^ D *
      |aeval ((a : ℝ) / b) F| := by
  obtain ⟨m, hm⟩ :=
    exists_int_eq_content_recycled_pow_mul_aeval Q F hQ hD a hb hBb hcoeff
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBb hb
  have hg : 0 < Nat.gcd C (B ^ D) := Nat.gcd_pos_of_pos_left _ hC
  have hpos : (0 : ℝ) < (Nat.gcd C (B ^ D) : ℝ) * ((b : ℝ) / B) ^ D := by
    positivity
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply mul_ne_zero (ne_of_gt hpos) hne
    simpa only [Int.cast_zero] using hm
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm0
  calc
    (1 : ℝ) ≤ |(m : ℝ)| := h1
    _ = |(Nat.gcd C (B ^ D) : ℝ) * ((b : ℝ) / B) ^ D *
        aeval ((a : ℝ) / b) F| := by rw [hm]
    _ = _ := by rw [abs_mul, abs_of_pos hpos]

/-- The usual reciprocal formulation with the overlap factor exposed. -/
theorem content_recycled_lower_bound (Q F : ℤ[X]) {C D : ℕ}
    (hC : 0 < C) (hQ : Q = Polynomial.C (C : ℤ) * F)
    (hD : F.natDegree ≤ D) (a : ℤ) {b B : ℕ} (hb : 0 < b)
    (hBb : B ∣ b) (hcoeff : ∀ i ≤ D, (B : ℤ) ^ i ∣ Q.coeff i)
    (hne : aeval ((a : ℝ) / b) F ≠ 0) :
    1 / ((Nat.gcd C (B ^ D) : ℝ) * ((b : ℝ) / B) ^ D) ≤
      |aeval ((a : ℝ) / b) F| := by
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBb hb
  have hg : 0 < Nat.gcd C (B ^ D) := Nat.gcd_pos_of_pos_left _ hC
  have hpos : (0 : ℝ) < (Nat.gcd C (B ^ D) : ℝ) * ((b : ℝ) / B) ^ D := by
    positivity
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    one_le_content_recycled_pow_mul_abs_aeval Q F hC hQ hD a hb hBb hcoeff hne

end CatalanMeasure
