module
public import CatalanMeasure.Parametric.SecondaryTentRowSeedPair
public import CatalanMeasure.Parametric.SecondaryTentRowInputInjective
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

private theorem secondaryTent_cubic_degree {K : Type*} [CommSemiring K]
    (a b c d : K) :
    (C a*X^0+C b*X^1+C c*X^2+C d*X^3 : K[X]).natDegree ≤ 3 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      exact max_le ((natDegree_C_mul_X_pow_le a 0).trans (by omega))
        ((natDegree_C_mul_X_pow_le b 1).trans (by omega))
    · exact (natDegree_C_mul_X_pow_le c 2).trans (by omega)
  · exact natDegree_C_mul_X_pow_le d 3

theorem secondaryTent_row_natural_P_degree {K : Type*} [CommRing K]
    (c : Fin 7 → K) : (secondaryTentRowNaturalP c).natDegree ≤ 3 :=
  secondaryTent_cubic_degree _ _ _ _

theorem secondaryTent_row_natural_Q_degree {K : Type*} [CommRing K]
    (c : Fin 7 → K) : (secondaryTentRowNaturalQ c).natDegree ≤ 3 :=
  secondaryTent_cubic_degree _ _ _ _

theorem secondaryTent_rowInput_pow {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (d k : ℕ) (I : K[X]) (hI : I.natDegree ≤ d) :
    secondaryTentRowInput (d*k) (I^k) = (secondaryTentRowInput d I)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ, secondaryTent_rowInput_mul h2 (d*k) d _ _
      (natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hI)) hI,
      ih, pow_succ]

/-- Exact Frobenius lifting of the universal seven-channel polynomial
source identity. No rational residues, Cartier, or finite evaluations are
assumed in this polynomial equality. -/
theorem secondaryTent_row_natural_t_junction_frobenius {p : ℕ} [Fact p.Prime]
    (c : Fin 7 → ZMod p) :
    (X-1)^p * (secondaryTentRowInput 3 (secondaryTentRowNaturalP c))^p +
      (X+1)^p * (secondaryTentRowInput 3 (secondaryTentRowNaturalQ c))^p =
      (8*X)^p * (secondaryTentRowTNumerator c)^p := by
  have hfrob (A B : (ZMod p)[X]) : (A+B)^p=A^p+B^p := by
    have h := (Polynomial.expand (ZMod p) p).map_add A B
    change Polynomial.expand (ZMod p) p (A+B) =
      Polynomial.expand (ZMod p) p A + Polynomial.expand (ZMod p) p B at h
    simpa only [ZMod.expand_card] using h
  have h := congrArg (fun P : (ZMod p)[X] => P^p) (secondaryTent_row_natural_t_junction c)
  simpa only [hfrob, mul_pow, mul_assoc] using h

/-- The full polynomial inverse reconstruction and actual t-seed packet
have the same ordinary numerator. This lifts the fixed-degree source
junction through every input polynomial, pth power, and finite sum. -/
theorem secondaryTent_row_packet_source_junction {p : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p) ≠ 0) {ι : Type*} [Fintype ι]
    (c : ι → (Fin 7 → ZMod p)) (I : ι → (ZMod p)[X])
    (hI : ∀ i, (I i).natDegree ≤ p-1) :
    (X-1)^p * secondaryTentRowInput (3*p+(p-1))
        (∑ i, (secondaryTentRowNaturalP (c i))^p * I i) +
      (X+1)^p * secondaryTentRowInput (3*p+(p-1))
        (∑ i, (secondaryTentRowNaturalQ (c i))^p * I i) =
      (8*X)^p * ∑ i, secondaryTentRowInput (p-1) (I i) *
        (secondaryTentRowTNumerator (c i))^p := by
  have hsum (A : ι → (ZMod p)[X]) (hA : ∀ i, (A i).natDegree ≤ 3) :
      secondaryTentRowInput (3*p+(p-1)) (∑ i, (A i)^p*I i) =
        ∑ i, (secondaryTentRowInput 3 (A i))^p*secondaryTentRowInput (p-1) (I i) := by
    change (secondaryTentRowInputLinear (3*p+(p-1))) (∑ i, (A i)^p*I i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change secondaryTentRowInput (3*p+(p-1)) ((A i)^p*I i) = _
    rw [secondaryTent_rowInput_mul h2 (3*p) (p-1) _ _
      (natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left p (hA i)))
      (hI i), secondaryTent_rowInput_pow h2 3 p (A i) (hA i)]
  rw [hsum _ (fun i => secondaryTent_row_natural_P_degree (c i)),
    hsum _ (fun i => secondaryTent_row_natural_Q_degree (c i)),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hj := secondaryTent_row_natural_t_junction_frobenius (c i)
  linear_combination secondaryTentRowInput (p-1) (I i) * hj

end
end CatalanMeasure.Parametric
