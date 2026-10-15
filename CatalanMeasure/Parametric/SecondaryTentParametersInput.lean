module
public import CatalanMeasure.Parametric.SecondaryTentResponsePolynomial
public import CatalanMeasure.Parametric.SecondaryTentRowNaturalPacket
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentCoefficientPolynomial {K : Type*} [Field K] (n : ℕ)
    (c : Fin n → K) : K[X] := ∑ i : Fin n, C (c i)*X^i.val

def secondaryTentCoefficientPolynomialLinear {K : Type*} [Field K] (n : ℕ) :
    (Fin n → K) →ₗ[K] K[X] where
  toFun := secondaryTentCoefficientPolynomial n
  map_add' := by
    intro c d
    simp [secondaryTentCoefficientPolynomial, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r c
    simp [secondaryTentCoefficientPolynomial, Polynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_assoc]

theorem secondaryTent_coefficient_polynomial_coeff {K : Type*} [Field K]
    (n : ℕ) (c : Fin n → K) (i : Fin n) :
    (secondaryTentCoefficientPolynomial n c).coeff i.val = c i := by
  classical
  rw [secondaryTentCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [coeff_C_mul, coeff_X_pow, Ne.symm hval]
  · simp

theorem secondaryTent_coefficient_polynomial_injective {K : Type*} [Field K] (n : ℕ) :
    Function.Injective (secondaryTentCoefficientPolynomial (K := K) n) := by
  intro c d h
  funext i
  have hh := congrArg (fun Q : K[X] => Q.coeff i.val) h
  simpa only [secondaryTent_coefficient_polynomial_coeff] using hh

theorem secondaryTent_coefficient_polynomial_degree {K : Type*} [Field K]
    {n : ℕ} (hn : 0 < n) (c : Fin n → K) :
    (secondaryTentCoefficientPolynomial n c).natDegree < n := by
  have hb : (secondaryTentCoefficientPolynomial n c).natDegree ≤ n-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  omega

def secondaryTentResponseInputLinear (p N : ℕ) [Fact p.Prime] :
    (Fin N → ZMod p) →ₗ[ZMod p] (ZMod p)[X] where
  toFun := secondaryTentResponseInput p N
  map_add' := by
    intro c d
    simp [secondaryTentResponseInput, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r c
    simp [secondaryTentResponseInput, Polynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_assoc]

def secondaryTentResponsePolynomialLinear (p N : ℕ) [Fact p.Prime] :
    (Fin N → ZMod p) →ₗ[ZMod p] (ZMod p)[X] where
  toFun := secondaryTentResponsePolynomial p N
  map_add' := by
    intro c d
    simp [secondaryTentResponsePolynomial, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r c
    simp [secondaryTentResponsePolynomial, Polynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_assoc]

/-- Literal five input polynomials on the exact finite-dimensional parameter
space. The last block is zero-dimensional on the negative side. -/
def secondaryTentParameterInputs (p N g boundary a b : ℕ) [Fact p.Prime]
    (v : SecondaryTentParameters (ZMod p) N g boundary) : Fin 5 → (ZMod p)[X] :=
  ![secondaryTentResponseInput p N v.1,
    X^a * secondaryTentCoefficientPolynomial g v.2.1,
    X^a * secondaryTentCoefficientPolynomial g v.2.2.1,
    X^b * secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1,
    secondaryTentCoefficientPolynomial boundary v.2.2.2.2]

def secondaryTentParameterInputsLinear (p N g boundary a b : ℕ) [Fact p.Prime] :
    SecondaryTentParameters (ZMod p) N g boundary →ₗ[ZMod p]
      (Fin 5 → (ZMod p)[X]) where
  toFun := secondaryTentParameterInputs p N g boundary a b
  map_add' := by
    intro v w
    funext i
    fin_cases i <;>
      simp [secondaryTentParameterInputs, secondaryTentResponseInput,
        secondaryTentCoefficientPolynomial, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    funext i
    fin_cases i <;>
      simp [secondaryTentParameterInputs, secondaryTentResponseInput,
        secondaryTentCoefficientPolynomial, Polynomial.smul_eq_C_mul,
        Finset.mul_sum, mul_assoc, mul_left_comm]

theorem secondaryTent_parameter_inputs_injective {p N g boundary a b : ℕ}
    [Fact p.Prime] (hNp : N ≤ p) :
    Function.Injective (secondaryTentParameterInputs p N g boundary a b) := by
  intro v w h
  have h0 := secondaryTent_response_input_injective hNp
    (congrFun h (0 : Fin 5))
  have h1 := secondaryTent_coefficient_polynomial_injective g
    (mul_left_cancel₀ (pow_ne_zero a (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
      (congrFun h (1 : Fin 5)))
  have h2 := secondaryTent_coefficient_polynomial_injective g
    (mul_left_cancel₀ (pow_ne_zero a (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
      (congrFun h (2 : Fin 5)))
  have h3 := secondaryTent_coefficient_polynomial_injective (3*N)
    (mul_left_cancel₀ (pow_ne_zero b (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
      (congrFun h (3 : Fin 5)))
  have h4 := secondaryTent_coefficient_polynomial_injective boundary
    (congrFun h (4 : Fin 5))
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))

theorem secondaryTent_parameter_inputs_degree {p N g boundary a b : ℕ}
    [hp : Fact p.Prime] (hN : 0 < N) (hg : 0 < g)
    (ha : a+g=p) (hb : b+3*N=p) (hboundary : boundary ≤ p)
    (v : SecondaryTentParameters (ZMod p) N g boundary) (i : Fin 5) :
    (secondaryTentParameterInputs p N g boundary a b v i).natDegree < p := by
  have hkernel (c : Fin g → ZMod p) :
      (X^a * secondaryTentCoefficientPolynomial g c).natDegree < p := by
    have hd := natDegree_mul_le (p := (X^a : (ZMod p)[X]))
      (q := secondaryTentCoefficientPolynomial g c)
    rw [natDegree_X_pow] at hd
    have hc := secondaryTent_coefficient_polynomial_degree hg c
    omega
  have hE (c : Fin (3*N) → ZMod p) :
      (X^b * secondaryTentCoefficientPolynomial (3*N) c).natDegree < p := by
    have hd := natDegree_mul_le (p := (X^b : (ZMod p)[X]))
      (q := secondaryTentCoefficientPolynomial (3*N) c)
    rw [natDegree_X_pow] at hd
    have hc := secondaryTent_coefficient_polynomial_degree (by omega : 0<3*N) c
    omega
  have hB : (secondaryTentCoefficientPolynomial boundary v.2.2.2.2).natDegree < p := by
    by_cases hb0 : boundary=0
    · subst boundary
      simpa [secondaryTentCoefficientPolynomial] using hp.out.pos
    · exact (secondaryTent_coefficient_polynomial_degree (by omega) _).trans_le hboundary
  fin_cases i
  · exact secondaryTent_response_input_degree _
  · exact hkernel _
  · exact hkernel _
  · exact hE _
  · exact hB

def secondaryTentInputsCoefficientsLinear (p : ℕ) [Fact p.Prime] :
    (Fin 5 → (ZMod p)[X]) →ₗ[ZMod p] (Fin p → Fin 5 → ZMod p) where
  toFun I e i := (I i).coeff e.val
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

theorem secondaryTent_inputs_coefficients_injective_on_degree {p : ℕ} [Fact p.Prime]
    (I J : Fin 5 → (ZMod p)[X]) (hI : ∀ i, (I i).natDegree < p)
    (hJ : ∀ i, (J i).natDegree < p)
    (h : secondaryTentInputsCoefficientsLinear p I = secondaryTentInputsCoefficientsLinear p J) :
    I=J := by
  funext i
  ext k
  by_cases hk : k<p
  · exact congrFun (congrFun h ⟨k,hk⟩) i
  · rw [coeff_eq_zero_of_natDegree_lt ((hI i).trans_le (by omega)),
      coeff_eq_zero_of_natDegree_lt ((hJ i).trans_le (by omega))]

end
end CatalanMeasure.Parametric
