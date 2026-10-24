module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentReconstruction
public import Mathlib.FieldTheory.RatFunc.Basic
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

/-- The ordinary polynomial obtained by clearing the denominator of the
substitution `x = (z²+1)/(2z)`, with the prescribed homogeneous degree `n`.
For the inverse Cartier inputs, `n = p-1`. -/
def secondaryTentRowHom {K : Type*} [CommSemiring K] (n : ℕ) (I A B : K[X]) : K[X] :=
  ∑ k ∈ Finset.range (n + 1), C (I.coeff k) * A ^ k * B ^ (n - k)

def secondaryTentRowInput {K : Type*} [CommSemiring K] (n : ℕ) (I : K[X]) : K[X] :=
  secondaryTentRowHom n I (X ^ 2 + 1) (2 * X)

theorem secondaryTent_rowHom_add {K : Type*} [CommSemiring K]
    (n : ℕ) (I J A B : K[X]) :
    secondaryTentRowHom n (I + J) A B =
      secondaryTentRowHom n I A B + secondaryTentRowHom n J A B := by
  simp [secondaryTentRowHom, add_mul, Finset.sum_add_distrib]

theorem secondaryTent_rowHom_smul {K : Type*} [CommSemiring K]
    (n : ℕ) (c : K) (I A B : K[X]) :
    secondaryTentRowHom n (c • I) A B = c • secondaryTentRowHom n I A B := by
  simp [secondaryTentRowHom, Finset.smul_sum, mul_assoc, ← C_mul']

/-- Exact rational interpretation of denominator clearing. This is an
identity in any target field, so it also applies to the rational function
field; it does not use equality from finitely many point evaluations. -/
theorem secondaryTent_rowHom_eval₂ {K L : Type*} [CommSemiring K] [Field L]
    (f : K →+* L) (n : ℕ) (I A B : K[X]) (z : L)
    (hI : I.natDegree ≤ n) (hB : B.eval₂ f z ≠ 0) :
    (secondaryTentRowHom n I A B).eval₂ f z =
      I.eval₂ f (A.eval₂ f z / B.eval₂ f z) * (B.eval₂ f z) ^ n := by
  rw [secondaryTentRowHom, eval₂_finsetSum]
  rw [Polynomial.eval₂_eq_sum_range' f (Nat.lt_succ_iff.mpr hI), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  simp only [eval₂_mul, eval₂_C, eval₂_pow]
  rw [div_pow, pow_sub₀ _ hB hkn]
  field_simp

theorem secondaryTent_rowInput_eval {K : Type*} [Field K]
    (n : ℕ) (I : K[X]) (z : K) (hI : I.natDegree ≤ n) (h2 : (2 : K) ≠ 0)
    (hz : z ≠ 0) :
    (secondaryTentRowInput n I).eval z =
      I.eval ((z ^ 2 + 1) / (2 * z)) * (2 * z) ^ n := by
  have h := secondaryTent_rowHom_eval₂ (RingHom.id K) n I (X ^ 2 + 1) (2 * X) z hI
    (by simpa using mul_ne_zero h2 hz)
  simp only [eval₂_id] at h
  simpa only [secondaryTentRowInput, eval_add, eval_pow, eval_X, eval_one,
    eval_mul, eval_ofNat] using h

/-- Every degree-`n` input gives a genuine polynomial of degree at most `2n`. -/
theorem secondaryTent_rowInput_natDegree {K : Type*} [CommSemiring K]
    (n : ℕ) (I : K[X]) : (secondaryTentRowInput n I).natDegree ≤ 2 * n := by
  unfold secondaryTentRowInput secondaryTentRowHom
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hA : (X ^ 2 + 1 : K[X]).natDegree ≤ 2 := by
    simpa using (natDegree_add_le (X ^ 2 : K[X]) 1).trans
      (max_le (natDegree_pow_le_of_le 2 (natDegree_X_le)) (by simp))
  have hB : (2 * X : K[X]).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (2 : K[X])) (q := X)).trans
      (by simpa using (natDegree_X_le (R := K)))
  have ht := natDegree_mul_le (p := C (I.coeff k) * (X ^ 2 + 1) ^ k)
    (q := (2 * X : K[X]) ^ (n-k))
  have hu := natDegree_mul_le (p := C (I.coeff k)) (q := (X ^ 2 + 1 : K[X]) ^ k)
  have ha := natDegree_pow_le_of_le k hA
  have hb := natDegree_pow_le_of_le (n-k) hB
  simp only [natDegree_C, zero_add] at hu
  omega

/-- Multiplication of bounded inputs becomes multiplication of their
denominator-cleared ordinary polynomials. The proof passes through the
injective polynomial inclusion in the rational function field. -/
theorem secondaryTent_rowHom_mul {K : Type*} [Field K]
    (m n : ℕ) (I J A B : K[X]) (hI : I.natDegree ≤ m) (hJ : J.natDegree ≤ n)
    (hB : B ≠ 0) :
    secondaryTentRowHom (m+n) (I*J) A B =
      secondaryTentRowHom m I A B * secondaryTentRowHom n J A B := by
  let f := algebraMap K (RatFunc K)
  let z := algebraMap K[X] (RatFunc K) X
  have he (P : K[X]) : P.eval₂ f z = algebraMap K[X] (RatFunc K) P := by
    exact Polynomial.eval₂_algebraMap_X P (IsScalarTower.toAlgHom K K[X] (RatFunc K))
  have hb : B.eval₂ f z ≠ 0 := by
    rw [he]
    exact RatFunc.algebraMap_ne_zero hB
  apply RatFunc.algebraMap_injective K
  rw [← he, map_mul, ← he, ← he]
  rw [secondaryTent_rowHom_eval₂ f (m+n) (I*J) A B z
    (natDegree_mul_le.trans (Nat.add_le_add hI hJ)) hb,
    secondaryTent_rowHom_eval₂ f m I A B z hI hb,
    secondaryTent_rowHom_eval₂ f n J A B z hJ hb, eval₂_mul, pow_add]
  ring

theorem secondaryTent_rowInput_mul {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (m n : ℕ) (I J : K[X]) (hI : I.natDegree ≤ m) (hJ : J.natDegree ≤ n) :
    secondaryTentRowInput (m+n) (I*J) =
      secondaryTentRowInput m I * secondaryTentRowInput n J := by
  apply secondaryTent_rowHom_mul m n I J _ _ hI hJ
  exact mul_ne_zero (by simpa only [← C_ofNat, ne_eq, C_eq_zero] using h2) X_ne_zero

@[simp] theorem secondaryTent_rowInput_X_pow {K : Type*} [CommSemiring K] (a : ℕ) :
    secondaryTentRowInput a (X ^ a : K[X]) = (X ^ 2 + 1) ^ a := by
  classical
  unfold secondaryTentRowInput secondaryTentRowHom
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [coeff_X_pow, hba]
  · simp

@[simp] theorem secondaryTent_rowInput_one {K : Type*} [CommSemiring K] :
    secondaryTentRowInput 0 (1 : K[X]) = 1 := by
  simp [secondaryTentRowInput, secondaryTentRowHom]

theorem secondaryTent_rowInput_one_degree {K : Type*} [CommSemiring K] (n : ℕ) :
    secondaryTentRowInput n (1 : K[X]) = (2 * X) ^ n := by
  classical
  unfold secondaryTentRowInput secondaryTentRowHom
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [coeff_one, hk0]
  · simp

/-- The input degree bound pays a literal power of `z` at the lower
endpoint. This is also the source of the boundary seed's `deg G + 1`
pole bound after division by `z^p`. -/
theorem secondaryTent_rowInput_padding {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (m n : ℕ) (I : K[X]) (hmn : m ≤ n)
    (hI : I.natDegree ≤ m) :
    secondaryTentRowInput n I = (2*X)^(n-m) * secondaryTentRowInput m I := by
  have h := secondaryTent_rowInput_mul h2 m (n-m) I 1 hI (by simp)
  simpa [secondaryTent_rowInput_one_degree, Nat.add_sub_of_le hmn, mul_comm] using h

theorem secondaryTent_rowInput_lower_factor {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (m n : ℕ) (I : K[X]) (hmn : m ≤ n)
    (hI : I.natDegree ≤ m) :
    (X : K[X]) ^ (n-m) ∣ secondaryTentRowInput n I := by
  rw [secondaryTent_rowInput_padding h2 m n I hmn hI, mul_pow]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem secondaryTent_rowInput_X_sub_one {K : Type*} [CommRing K] :
    secondaryTentRowInput 1 (X - 1 : K[X]) = (X - 1) ^ 2 := by
  simp [secondaryTentRowInput, secondaryTentRowHom, Finset.sum_range_succ, coeff_one]
  ring

/-- The eta0 input contributes a double `(z-1)` zero for each `(x-1)`
factor, exactly the ramification multiplicity used in denominator payment. -/
theorem secondaryTent_rowInput_X_sub_one_pow {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (b : ℕ) :
    secondaryTentRowInput b ((X - 1 : K[X]) ^ b) = (X - 1) ^ (2*b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, secondaryTent_rowInput_mul h2 b 1]
    · rw [ih, secondaryTent_rowInput_X_sub_one, ← pow_add]
      congr 1
    · simpa using (natDegree_pow_le_of_le b
        (show (X - 1 : K[X]).natDegree ≤ 1 from by simpa using natDegree_X_sub_C_le (1:K)))
    · simpa using natDegree_X_sub_C_le (1:K)

theorem secondaryTent_rowInput_X_pow_mul {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (a m : ℕ) (f : K[X]) (hf : f.natDegree ≤ m) :
    secondaryTentRowInput (a+m) (X ^ a * f) =
      (X ^ 2 + 1) ^ a * secondaryTentRowInput m f := by
  rw [secondaryTent_rowInput_mul h2 a m _ _ (by simp) hf,
    secondaryTent_rowInput_X_pow]

theorem secondaryTent_rowInput_X_sub_one_pow_mul {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (b m : ℕ) (f : K[X]) (hf : f.natDegree ≤ m) :
    secondaryTentRowInput (b+m) ((X-1) ^ b * f) =
      (X-1) ^ (2*b) * secondaryTentRowInput m f := by
  rw [secondaryTent_rowInput_mul h2 b m _ _
    (by simpa using (natDegree_pow_le_of_le b
      (show (X - 1 : K[X]).natDegree ≤ 1 from by simpa using natDegree_X_sub_C_le (1:K)))) hf,
    secondaryTent_rowInput_X_sub_one_pow h2]

theorem secondaryTent_rowInput_X_add_one {K : Type*} [CommSemiring K] :
    secondaryTentRowInput 1 (X + 1 : K[X]) = (X + 1) ^ 2 := by
  simp [secondaryTentRowInput, secondaryTentRowHom, Finset.sum_range_succ, coeff_one]
  ring

theorem secondaryTent_rowInput_X_add_one_pow {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (b : ℕ) :
    secondaryTentRowInput b ((X + 1 : K[X]) ^ b) = (X + 1) ^ (2*b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, secondaryTent_rowInput_mul h2 b 1]
    · rw [ih, secondaryTent_rowInput_X_add_one, ← pow_add]
      congr 1
    · exact natDegree_pow_le.trans (by simp)
    · simp

theorem secondaryTent_rowInput_X_add_one_pow_mul {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (b m : ℕ) (f : K[X]) (hf : f.natDegree ≤ m) :
    secondaryTentRowInput (b+m) ((X+1) ^ b * f) =
      (X+1) ^ (2*b) * secondaryTentRowInput m f := by
  rw [secondaryTent_rowInput_mul h2 b m _ _
    (natDegree_pow_le.trans (by simp)) hf,
    secondaryTent_rowInput_X_add_one_pow h2]

/-- The literal `g+a=p` cancellation at the two quadratic poles. -/
theorem secondaryTent_rowInput_quadratic_payment {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (g a m : ℕ) (f : K[X]) (hf : f.natDegree ≤ m) :
    (X ^ 2 + 1) ^ g * secondaryTentRowInput (a+m) (X ^ a * f) =
      (X ^ 2 + 1) ^ (g+a) * secondaryTentRowInput m f := by
  rw [secondaryTent_rowInput_X_pow_mul h2 a m f hf, ← mul_assoc, ← pow_add]

end
end CatalanMeasure.Parametric
