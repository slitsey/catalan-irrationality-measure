module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentParametersInput
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowActualCoefficients
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial Matrix
open scoped BigOperators
noncomputable section

def secondaryTentInputsNaturalULinear (p : ℕ) [Fact p.Prime] :
    (Fin 5 → (ZMod p)[X]) →ₗ[ZMod p] (ZMod p)[X] where
  toFun I := ∑ i : Fin 5, (secondaryTentRowNaturalP (secondaryTentRowActualSeedColumn i))^p * I i
  map_add' I J := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' t I := by simp [Polynomial.smul_eq_C_mul,Finset.mul_sum,mul_assoc,mul_left_comm]

def secondaryTentInputsNaturalVLinear (p : ℕ) [Fact p.Prime] :
    (Fin 5 → (ZMod p)[X]) →ₗ[ZMod p] (ZMod p)[X] where
  toFun I := ∑ i : Fin 5, (secondaryTentRowNaturalQ (secondaryTentRowActualSeedColumn i))^p * I i
  map_add' I J := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' t I := by simp [Polynomial.smul_eq_C_mul,Finset.mul_sum,mul_assoc,mul_left_comm]

def secondaryTentInputsAlpha2Linear (p : ℕ) [Fact p.Prime] :
    (Fin 5 → (ZMod p)[X]) →ₗ[ZMod p] (ZMod p)[X] where
  toFun I := secondaryTentRowTopInput (secondaryTentRowActualSeedColumn (K := ZMod p)) I
  map_add' I J := by simp [secondaryTentRowTopInput,smul_add,Finset.sum_add_distrib]
  map_smul' t I := by simp [secondaryTentRowTopInput,Finset.smul_sum,smul_smul,mul_comm]

def secondaryTentParameterNaturalULinear (p N g boundary a b : ℕ) [Fact p.Prime] :=
  (secondaryTentInputsNaturalULinear p).comp (secondaryTentParameterInputsLinear p N g boundary a b)

def secondaryTentParameterNaturalVLinear (p N g boundary a b : ℕ) [Fact p.Prime] :=
  (secondaryTentInputsNaturalVLinear p).comp (secondaryTentParameterInputsLinear p N g boundary a b)

def secondaryTentParameterAlpha2Linear (p N g boundary a b : ℕ) [Fact p.Prime] :=
  (secondaryTentInputsAlpha2Linear p).comp (secondaryTentParameterInputsLinear p N g boundary a b)

def secondaryTentParameterPacketLinear (p N g boundary a b : ℕ) [Fact p.Prime] :=
  (secondaryTentRowFixedNaturalPacketLinear p).comp
    ((secondaryTentInputsCoefficientsLinear p).comp (secondaryTentParameterInputsLinear p N g boundary a b))

def secondaryTentParameterActualRowLinear (p N g boundary a b : ℕ) [Fact p.Prime] :=
  (secondaryTentActualRowLinear N p a).comp
    ((secondaryTentInputsCoefficientsLinear p).comp (secondaryTentParameterInputsLinear p N g boundary a b))

/-- Degree-bounded inputs are recovered exactly from their coefficient
packets, so all source formulae refer to the same concrete polynomials. -/
theorem secondaryTent_inputs_coefficients_roundtrip {p : ℕ} [Fact p.Prime]
    (I : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree<p) (i : Fin 5) :
    secondaryTentRowInputPolynomial p (secondaryTentInputsCoefficientsLinear p I) i=I i := by
  have hp := (Fact.out : p.Prime).pos
  ext k
  by_cases hk : k<p
  · have h := secondaryTent_row_input_polynomial_coeff p
      (secondaryTentInputsCoefficientsLinear p I) i ⟨k,hk⟩
    exact h
  · have hd := secondaryTent_row_input_polynomial_degree (Fact.out : p.Prime).pos
      (secondaryTentInputsCoefficientsLinear p I) i
    rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt ((hI i).trans_le (by omega))]

theorem secondaryTent_inputs_natural_U_expansion {p : ℕ} [Fact p.Prime]
    (I : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree<p) :
    secondaryTentInterleave p (fun e =>
      (secondaryTentRowFixedSeedPair (secondaryTentInputsCoefficientsLinear p I e)).1) =
      secondaryTentInputsNaturalULinear p I := by
  let L : (Fin 5 → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    (LinearMap.fst (ZMod p) (ZMod p)[X] (ZMod p)[X]).comp secondaryTentRowFixedSeedPair
  have h := secondaryTent_row_interleave_input_expansion L (secondaryTentInputsCoefficientsLinear p I)
  simp_rw [secondaryTent_inputs_coefficients_roundtrip I hI] at h
  exact h

theorem secondaryTent_inputs_natural_V_expansion {p : ℕ} [Fact p.Prime]
    (I : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree<p) :
    secondaryTentInterleave p (fun e =>
      (secondaryTentRowFixedSeedPair (secondaryTentInputsCoefficientsLinear p I e)).2) =
      secondaryTentInputsNaturalVLinear p I := by
  let L : (Fin 5 → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    (LinearMap.snd (ZMod p) (ZMod p)[X] (ZMod p)[X]).comp secondaryTentRowFixedSeedPair
  have h := secondaryTent_row_interleave_input_expansion L (secondaryTentInputsCoefficientsLinear p I)
  simp_rw [secondaryTent_inputs_coefficients_roundtrip I hI] at h
  exact h

theorem secondaryTent_inputs_natural_packet_expansion {p : ℕ} [Fact p.Prime]
    (I : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree<p) :
    secondaryTentRowFixedNaturalPacket p (secondaryTentInputsCoefficientsLinear p I) =
      secondaryTentRowNaturalNumerator p (4*p-1)
        (secondaryTentInputsNaturalULinear p I) (secondaryTentInputsNaturalVLinear p I) := by
  unfold secondaryTentRowFixedNaturalPacket
  rw [secondaryTent_inputs_natural_U_expansion I hI,secondaryTent_inputs_natural_V_expansion I hI]

theorem secondaryTent_inputs_natural_degree {p : ℕ} [Fact p.Prime]
    (I : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree<p) :
    (secondaryTentInputsNaturalULinear p I).natDegree≤4*p-1 ∧
      (secondaryTentInputsNaturalVLinear p I).natDegree≤4*p-1 := by
  rw [← secondaryTent_inputs_natural_U_expansion I hI,← secondaryTent_inputs_natural_V_expansion I hI]
  constructor
  · apply secondaryTent_row_interleave_cubic_degree (Fact.out : p.Prime).pos
    intro e
    exact secondaryTent_row_natural_P_degree _
  · apply secondaryTent_row_interleave_cubic_degree (Fact.out : p.Prime).pos
    intro e
    exact secondaryTent_row_natural_Q_degree _

theorem secondaryTent_natural_P_at_zero {K : Type*} [Field K] (c : Fin 7 → K) :
    (secondaryTentRowNaturalP c).eval 0=c 4 := by simp [secondaryTentRowNaturalP]

theorem secondaryTent_natural_Q_at_zero {K : Type*} [Field K] (c : Fin 7 → K) :
    (secondaryTentRowNaturalQ c).eval 0= -c 5 := by simp [secondaryTentRowNaturalQ]

theorem secondaryTent_natural_Q_at_one {K : Type*} [Field K] (c : Fin 7 → K) :
    (secondaryTentRowNaturalQ c).eval 1=c 3 := by
  simp [secondaryTentRowNaturalQ]
  ring

theorem secondaryTent_seed_gamma_zero {K : Type*} [Field K] (i : Fin 5) (hi : i≠1) :
    secondaryTentRowActualSeedColumn (K := K) i 4=0 := by
  classical
  fin_cases i <;> norm_num [secondaryTentRowActualSeedColumn,Matrix.mulVec_single_one,
    secondaryTentSeedCoefficients] at *

theorem secondaryTent_seed_zeta_zero {K : Type*} [Field K] (i : Fin 5) (hi : i≠2) :
    secondaryTentRowActualSeedColumn (K := K) i 5=0 := by
  classical
  fin_cases i <;> norm_num [secondaryTentRowActualSeedColumn,Matrix.mulVec_single_one,
    secondaryTentSeedCoefficients] at *

/-- The literal fixed gamma/zeta columns make both x=0 flags automatic
from just the two kernel input factors; other seed numerators have an
x factor whose pth power pays every a≤p. -/
theorem secondaryTent_inputs_natural_zero_flags {p : ℕ} [Fact p.Prime]
    (a : ℕ) (ha : a≤p) (I : Fin 5 → (ZMod p)[X])
    (hI₁ : X^a ∣ I 1) (hI₂ : X^a ∣ I 2) :
    X^a ∣ secondaryTentInputsNaturalULinear p I ∧ X^a ∣ secondaryTentInputsNaturalVLinear p I := by
  constructor
  · change X^a ∣ ∑ i : Fin 5, (secondaryTentRowNaturalP (secondaryTentRowActualSeedColumn i))^p * I i
    apply Finset.dvd_sum
    intro i hi
    by_cases hi₁ : i=1
    · subst i
      exact dvd_mul_of_dvd_right hI₁ _
    · have hz : X ∣ secondaryTentRowNaturalP (secondaryTentRowActualSeedColumn (K := ZMod p) i) := by
        apply X_dvd_iff.mpr
        rw [coeff_zero_eq_eval_zero]
        have hh := secondaryTent_natural_P_at_zero (secondaryTentRowActualSeedColumn (K := ZMod p) i)
        simpa [secondaryTent_seed_gamma_zero i hi₁] using hh
      exact dvd_mul_of_dvd_left ((pow_dvd_pow X ha).trans (pow_dvd_pow_of_dvd hz p)) _
  · change X^a ∣ ∑ i : Fin 5, (secondaryTentRowNaturalQ (secondaryTentRowActualSeedColumn i))^p * I i
    apply Finset.dvd_sum
    intro i hi
    by_cases hi₂ : i=2
    · subst i
      exact dvd_mul_of_dvd_right hI₂ _
    · have hz : X ∣ secondaryTentRowNaturalQ (secondaryTentRowActualSeedColumn (K := ZMod p) i) := by
        apply X_dvd_iff.mpr
        rw [coeff_zero_eq_eval_zero]
        have hh := secondaryTent_natural_Q_at_zero (secondaryTentRowActualSeedColumn (K := ZMod p) i)
        simpa [secondaryTent_seed_zeta_zero i hi₂] using hh
      exact dvd_mul_of_dvd_left ((pow_dvd_pow X ha).trans (pow_dvd_pow_of_dvd hz p)) _

theorem secondaryTent_parameter_natural_zero_flags {p N g boundary a b : ℕ} [Fact p.Prime]
    (ha : a≤p) (v : SecondaryTentParameters (ZMod p) N g boundary) :
    X^a ∣ secondaryTentParameterNaturalULinear p N g boundary a b v ∧
      X^a ∣ secondaryTentParameterNaturalVLinear p N g boundary a b v := by
  apply secondaryTent_inputs_natural_zero_flags a ha
  · change X^a ∣ X^a*secondaryTentCoefficientPolynomial g v.2.1
    exact dvd_mul_right _ _
  · change X^a ∣ X^a*secondaryTentCoefficientPolynomial g v.2.2.1
    exact dvd_mul_right _ _

theorem secondaryTent_parameter_natural_degree {p N g boundary a b : ℕ} [Fact p.Prime]
    (hN : 0<N) (hg : 0<g) (ha : a+g=p) (hb : b+3*N=p) (hboundary : boundary≤p)
    (v : SecondaryTentParameters (ZMod p) N g boundary) :
    (secondaryTentParameterNaturalULinear p N g boundary a b v).natDegree≤4*p-1 ∧
      (secondaryTentParameterNaturalVLinear p N g boundary a b v).natDegree≤4*p-1 :=
  secondaryTent_inputs_natural_degree _ (secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v)

theorem secondaryTent_parameter_natural_packet_expansion {p N g boundary a b : ℕ} [Fact p.Prime]
    (hN : 0<N) (hg : 0<g) (ha : a+g=p) (hb : b+3*N=p) (hboundary : boundary≤p)
    (v : SecondaryTentParameters (ZMod p) N g boundary) :
    secondaryTentParameterPacketLinear p N g boundary a b v =
      secondaryTentRowNaturalNumerator p (4*p-1)
        (secondaryTentParameterNaturalULinear p N g boundary a b v)
        (secondaryTentParameterNaturalVLinear p N g boundary a b v) := by
  exact secondaryTent_inputs_natural_packet_expansion _
    (secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v)

theorem secondaryTent_parameter_packet_shared_degree {p N g boundary a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hN : 0<N) (hg : 0<g) (ha : a+g=p) (hb : b+3*N=p)
    (hboundary : boundary≤p) (m : ℕ) (hm : m≤p-1) (hcap : m+8*N+2=2*p)
    (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hS : (secondaryTentParameterAlpha2Linear p N g boundary a b v).natDegree≤m) :
    (secondaryTentParameterPacketLinear p N g boundary a b v).natDegree+8*N+3≤10*p := by
  let I := secondaryTentParameterInputs p N g boundary a b v
  have hI : ∀ i, (I i).natDegree<p := secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v
  have hrep : secondaryTentRowInputPolynomial p (secondaryTentInputsCoefficientsLinear p I)=I := by
    funext i
    exact secondaryTent_inputs_coefficients_roundtrip I hI i
  have hs : (secondaryTentRowTopInput (secondaryTentRowActualSeedColumn (K := ZMod p))
      (secondaryTentRowInputPolynomial p (secondaryTentInputsCoefficientsLinear p I))).natDegree≤m := by
    rw [hrep]
    exact hS
  exact secondaryTent_actual_row_shared_degree_flag h2 N m (secondaryTentInputsCoefficientsLinear p I) hm hcap hs

/-- The concrete finite-dimensional parameter map to the actual full row
is injective under the literal total-divisor/shared-cap flags. The proof
uses the proved Newton-input, coefficient, packet, and quotient injections. -/
theorem secondaryTent_parameter_actual_row_injective_on_flags {p N g boundary a b : ℕ}
    [Fact p.Prime] (h2 : (2:ZMod p)≠0) (hunit : (3445975817256960:ZMod p)≠0)
    (hN : 0<N) (hg : 0<g) (hNp : N≤p) (ha : a+g=p) (hb : b+3*N=p)
    (hboundary : boundary≤p) (hodd : Odd p) (hpN : 2*p≤24*N) (hgp : g+4*p=27*N)
    (v w : SecondaryTentParameters (ZMod p) N g boundary)
    (hv : (secondaryTentParameterPacketLinear p N g boundary a b v).natDegree+8*N+3≤10*p)
    (hw : (secondaryTentParameterPacketLinear p N g boundary a b w).natDegree+8*N+3≤10*p)
    (hdv : secondaryTentRowTotalDivisor N p a ∣ secondaryTentParameterPacketLinear p N g boundary a b v)
    (hdw : secondaryTentRowTotalDivisor N p a ∣ secondaryTentParameterPacketLinear p N g boundary a b w)
    (heq : secondaryTentParameterActualRowLinear p N g boundary a b v =
      secondaryTentParameterActualRowLinear p N g boundary a b w) : v=w := by
  have hc := secondaryTent_actual_row_injective_on_flags h2 hunit N p a g hN
    (Fact.out : p.Prime).pos hodd hpN ha hgp
    (secondaryTentInputsCoefficientsLinear p (secondaryTentParameterInputs p N g boundary a b v))
    (secondaryTentInputsCoefficientsLinear p (secondaryTentParameterInputs p N g boundary a b w))
    hv hw hdv hdw heq
  apply secondaryTent_parameter_inputs_injective hNp
  exact secondaryTent_inputs_coefficients_injective_on_degree _ _
    (secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v)
    (secondaryTent_parameter_inputs_degree hN hg ha hb hboundary w) hc

end
end CatalanMeasure.Parametric
