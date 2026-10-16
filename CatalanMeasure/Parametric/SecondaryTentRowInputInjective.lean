module
public import CatalanMeasure.Parametric.SecondaryTentRowPolynomial
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentRowInputLinear {K : Type*} [CommSemiring K] (n : ℕ) :
    K[X] →ₗ[K] K[X] where
  toFun := secondaryTentRowInput n
  map_add' I J := secondaryTent_rowHom_add n I J _ _
  map_smul' c I := secondaryTent_rowHom_smul n c I _ _

private theorem secondaryTent_rowInput_term_degree {K : Type*} [CommSemiring K]
    (n k : ℕ) (c : K) (hk : k ≤ n) :
    (C c * (X^2+1)^k * (2*X : K[X])^(n-k)).natDegree ≤ n+k := by
  have hA : (X ^ 2 + 1 : K[X]).natDegree ≤ 2 := by
    simpa using (natDegree_add_le (X ^ 2 : K[X]) 1).trans
      (max_le (natDegree_pow_le_of_le 2 (natDegree_X_le)) (by simp))
  have hB : (2 * X : K[X]).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (2 : K[X])) (q := X)).trans
      (by simpa using (natDegree_X_le (R := K)))
  have ht := natDegree_mul_le (p := C c * (X^2+1)^k)
    (q := (2*X : K[X])^(n-k))
  have hu := natDegree_mul_le (p := C c) (q := (X^2+1 : K[X])^k)
  have ha := natDegree_pow_le_of_le k hA
  have hb := natDegree_pow_le_of_le (n-k) hB
  simp only [natDegree_C, zero_add] at hu
  omega

/-- The high coefficient of the actual homogenized input records its
leading coefficient. In characteristic two the displayed multiplier can
vanish; the injectivity result therefore explicitly assumes `2≠0`. -/
theorem secondaryTent_rowInput_top_coeff {K : Type*} [CommRing K] [Nontrivial K]
    (n : ℕ) (I : K[X]) (hI : I.natDegree ≤ n) :
    (secondaryTentRowInput n I).coeff (n+I.natDegree) =
      I.leadingCoeff * (2:K)^(n-I.natDegree) := by
  classical
  let m := I.natDegree
  have hmn : m ≤ n := hI
  unfold secondaryTentRowInput secondaryTentRowHom
  rw [finsetSum_coeff, Finset.sum_eq_single m]
  · have hidx : n+m = 2*m+(n-m) := by omega
    have hpow : (2*X : K[X])^(n-m) = C ((2:K)^(n-m)) * X^(n-m) := by
      rw [mul_pow, ← C_ofNat, ← C_pow]
    have hterm : C (I.coeff m) * (X^2+1)^m * (2*X : K[X])^(n-m) =
        C (I.coeff m * (2:K)^(n-m)) * (X^2+1)^m * X^(n-m) := by
      rw [hpow, C_mul]
      ring
    rw [hterm, hidx, coeff_mul_X_pow, coeff_C_mul]
    have hA : (X^2+1 : K[X]).natDegree = 2 := by
      simpa using (natDegree_X_pow_add_C (n := 2) (r := (1:K)))
    have hAc : (X^2+1 : K[X]).leadingCoeff = 1 := by
      exact (by simpa using (monic_X_pow_add_C (1:K) (by decide : 2 ≠ 0)))
    have hp := coeff_pow_mul_natDegree (X^2+1 : K[X]) m
    have hc : ((X^2+1 : K[X])^m).coeff (2*m) = 1 := by
      simpa [hA, hAc, Nat.mul_comm] using hp
    rw [hc, mul_one]
    rfl
  · intro k hk hkm
    rcases lt_or_gt_of_ne hkm with hlt | hgt
    · apply coeff_eq_zero_of_natDegree_lt
      exact (secondaryTent_rowInput_term_degree n k (I.coeff k)
        (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).trans_lt
        (by omega)
    · have hc : I.coeff k = 0 := coeff_eq_zero_of_natDegree_lt hgt
      simp [hc]
  · intro h
    exact (h (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hmn)).elim

/-- Denominator clearing does not lose an input polynomial of degree at
most `n`, including over finite prime fields. -/
theorem secondaryTent_rowInput_eq_zero_iff {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (n : ℕ) (I : K[X]) (hI : I.natDegree ≤ n) :
    secondaryTentRowInput n I = 0 ↔ I = 0 := by
  constructor
  · intro h
    by_contra hi
    have hc := congrArg (fun P : K[X] => P.coeff (n+I.natDegree)) h
    rw [secondaryTent_rowInput_top_coeff n I hI, coeff_zero] at hc
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hi) (pow_ne_zero _ h2) hc
  · rintro rfl
    exact (secondaryTentRowInputLinear n).map_zero

theorem secondaryTent_rowInput_injective_bounded {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (n : ℕ) (I J : K[X])
    (hI : I.natDegree ≤ n) (hJ : J.natDegree ≤ n)
    (h : secondaryTentRowInput n I = secondaryTentRowInput n J) : I = J := by
  apply sub_eq_zero.mp
  apply (secondaryTent_rowInput_eq_zero_iff h2 n (I-J)
    ((natDegree_sub_le I J).trans (max_le hI hJ))).mp
  change (secondaryTentRowInputLinear n) (I-J) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

end
end CatalanMeasure.Parametric
