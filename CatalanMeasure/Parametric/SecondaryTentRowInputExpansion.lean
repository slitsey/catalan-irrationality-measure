module
public import CatalanMeasure.Parametric.SecondaryTentRowNaturalPacket
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentRowInputPolynomial {K : Type*} [CommSemiring K]
    (p : ℕ) (c : Fin p → (Fin 5 → K)) (i : Fin 5) : K[X] :=
  ∑ e : Fin p, C (c e i)*X^e.val

theorem secondaryTent_row_input_polynomial_coeff {K : Type*} [CommSemiring K]
    (p : ℕ) (c : Fin p → (Fin 5 → K)) (i : Fin 5) (e : Fin p) :
    (secondaryTentRowInputPolynomial p c i).coeff e.val = c e i := by
  classical
  unfold secondaryTentRowInputPolynomial
  rw [finsetSum_coeff,Finset.sum_eq_single e]
  · simp [coeff_C_mul_X_pow]
  · intro j hj hje
    have hjv : j.val≠e.val := fun h => hje (Fin.ext h)
    simp [coeff_C_mul_X_pow,hjv,Ne.symm hjv]
  · simp

theorem secondaryTent_row_input_polynomial_degree {K : Type*} [CommSemiring K]
    {p : ℕ} (hp : 0<p) (c : Fin p → (Fin 5 → K)) (i : Fin 5) :
    (secondaryTentRowInputPolynomial p c i).natDegree≤p-1 := by
  unfold secondaryTentRowInputPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  exact (natDegree_C_mul_X_pow_le _ e.val).trans (by have h := e.isLt; omega)

/-- Expanding the concrete coefficient packets by differential channel
gives precisely the polynomial inputs used in the human reconstruction. -/
theorem secondaryTent_row_interleave_input_expansion {p : ℕ} [Fact p.Prime]
    (L : (Fin 5 → ZMod p) →ₗ[ZMod p] (ZMod p)[X])
    (c : Fin p → (Fin 5 → ZMod p)) :
    secondaryTentInterleave p (fun e => L (c e)) =
      ∑ i : Fin 5, (L (Pi.single i 1))^p*secondaryTentRowInputPolynomial p c i := by
  classical
  have hdecomp (e : Fin p) : L (c e)=∑ i : Fin 5, c e i • L (Pi.single i 1) := by
    have hv : (c e) = ∑ i : Fin 5, c e i • Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    calc
      L (c e)=L (∑ i : Fin 5, c e i • Pi.single i 1) := congrArg L hv
      _ = _ := by rw [map_sum]; simp only [map_smul]
  have he (e : Fin p) : Polynomial.expand (ZMod p) p (L (c e)) =
      ∑ i : Fin 5, c e i • (L (Pi.single i 1))^p := by
    have h := congrArg (Polynomial.expand (ZMod p) p).toLinearMap (hdecomp e)
    rw [map_sum] at h
    simp only [map_smul] at h
    change Polynomial.expand (ZMod p) p (L (c e)) =
      ∑ i : Fin 5, c e i • Polynomial.expand (ZMod p) p (L (Pi.single i 1)) at h
    simpa only [map_smul,ZMod.expand_card] using h
  unfold secondaryTentInterleave secondaryTentRowInputPolynomial
  simp_rw [he,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← C_mul']
  ring

/-- The actual fixed-seed natural packet equals the five-channel source
packet proved in RowSourceJunction. -/
theorem secondaryTent_row_fixed_input_source_junction {p : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (c : Fin p → (Fin 5 → ZMod p)) :
    secondaryTentRowFixedNaturalPacket p c =
      (8*X)^p * ∑ i : Fin 5,
        secondaryTentRowInput (p-1) (secondaryTentRowInputPolynomial p c i) *
        (secondaryTentRowTNumerator
          ((secondaryTentSeedCoefficients.map (Int.castRingHom (ZMod p))).mulVec (Pi.single i 1)))^p := by
  let L₁ : (Fin 5 → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    (LinearMap.fst (ZMod p) (ZMod p)[X] (ZMod p)[X]).comp secondaryTentRowFixedSeedPair
  let L₂ : (Fin 5 → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    (LinearMap.snd (ZMod p) (ZMod p)[X] (ZMod p)[X]).comp secondaryTentRowFixedSeedPair
  have h₁ := secondaryTent_row_interleave_input_expansion L₁ c
  have h₂ := secondaryTent_row_interleave_input_expansion L₂ c
  unfold secondaryTentRowFixedNaturalPacket secondaryTentRowNaturalNumerator
  change (X-1)^p * secondaryTentRowInput (4*p-1) (secondaryTentInterleave p (fun e => L₁ (c e))) +
    (X+1)^p * secondaryTentRowInput (4*p-1) (secondaryTentInterleave p (fun e => L₂ (c e))) = _
  rw [h₁,h₂]
  have hdeg : 4*p-1=3*p+(p-1) := by have h := (Fact.out : p.Prime).pos; omega
  rw [hdeg]
  exact secondaryTent_row_packet_source_junction h2
    (fun i => (secondaryTentSeedCoefficients.map (Int.castRingHom (ZMod p))).mulVec (Pi.single i 1))
    (secondaryTentRowInputPolynomial p c)
    (secondaryTent_row_input_polynomial_degree (Fact.out : p.Prime).pos c)

end
end CatalanMeasure.Parametric
