module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowEndpointSource
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowDegree
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentRowTopInput {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]
    (c : ι → (Fin 7 → K)) (I : ι → K[X]) : K[X] := ∑ i, c i 2 • I i

/-- The source packet's unique degree-six channel is precisely the single
shared infinity input from the human proof. -/
theorem secondaryTent_row_packet_top_split {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] (n : ℕ) (c : ι → (Fin 7 → ZMod p))
    (I : ι → (ZMod p)[X]) :
    (∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTNumerator (c i))^p) =
      X^(6*p)*secondaryTentRowInput n (secondaryTentRowTopInput c I) +
        ∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTRemainder (c i))^p := by
  have hfrob (A B : (ZMod p)[X]) : (A+B)^p=A^p+B^p := by
    have h := (Polynomial.expand (ZMod p) p).map_add A B
    change Polynomial.expand (ZMod p) p (A+B) =
      Polynomial.expand (ZMod p) p A + Polynomial.expand (ZMod p) p B at h
    simpa only [ZMod.expand_card] using h
  have ht (i : ι) : (secondaryTentRowTNumerator (c i))^p =
      C (c i 2)*X^(6*p)+(secondaryTentRowTRemainder (c i))^p := by
    rw [secondaryTent_row_t_top_split,hfrob,mul_pow,← C_pow,ZMod.pow_card,← pow_mul]
  have hS : secondaryTentRowInput n (secondaryTentRowTopInput c I) =
      ∑ i, C (c i 2)*secondaryTentRowInput n (I i) := by
    change (secondaryTentRowInputLinear n) (∑ i, c i 2 • I i) = _
    rw [map_sum]
    simp only [map_smul,C_mul']
    rfl
  rw [hS,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ht]
  ring

/-- Direct K degree bound. The boundary seed is included: its numerator
also has degree at most six and the same degree-six coefficient. -/
theorem secondaryTent_row_direct_packet_degree {p : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) {ι : Type*} [Fintype ι]
    (N n m : ℕ) (c : ι → (Fin 7 → ZMod p)) (I : ι → (ZMod p)[X])
    (hnp : n+1=p) (hmn : m≤n) (hcap : m+8*N+2=2*p)
    (hS : (secondaryTentRowTopInput c I).natDegree≤m) :
    ((8*X)^p * ∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTNumerator (c i))^p).natDegree+
      8*N+3≤10*p := by
  have hT := secondaryTent_rowInput_natDegree_le h2 n m (secondaryTentRowTopInput c I) hmn hS
  have hR : (∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTRemainder (c i))^p).natDegree≤2*n+5*p := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hI := secondaryTent_rowInput_natDegree n (I i)
    have hr := natDegree_pow_le_of_le p (secondaryTent_row_t_remainder_degree (c i))
    have hh := natDegree_mul_le (p := secondaryTentRowInput n (I i))
      (q := (secondaryTentRowTRemainder (c i))^p)
    omega
  have hTop := natDegree_mul_le (p := (X : (ZMod p)[X])^(6*p))
    (q := secondaryTentRowInput n (secondaryTentRowTopInput c I))
  rw [natDegree_X_pow] at hTop
  have hSum := natDegree_add_le
    ((X : (ZMod p)[X])^(6*p)*secondaryTentRowInput n (secondaryTentRowTopInput c I))
    (∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTRemainder (c i))^p)
  have hEight : (8*X : (ZMod p)[X]).natDegree≤1 := by
    simpa using (natDegree_mul_le (p := (8 : (ZMod p)[X])) (q := X)).trans
      (by simpa using (natDegree_X_le (R := ZMod p)))
  have hFront := natDegree_pow_le_of_le p hEight
  rw [secondaryTent_row_packet_top_split]
  have hMul := natDegree_mul_le (p := (8*X : (ZMod p)[X])^p)
    (q := (X^(6*p)*secondaryTentRowInput n (secondaryTentRowTopInput c I) +
      ∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTRemainder (c i))^p))
  omega

end
end CatalanMeasure.Parametric
