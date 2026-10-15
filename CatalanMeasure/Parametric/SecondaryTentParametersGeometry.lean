module
public import CatalanMeasure.Parametric.SecondaryTentParametersConstraints
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

theorem secondaryTent_parameter_seed_beta_boundary {p : ℕ} [Fact p.Prime] :
    secondaryTentParameterSeedBeta p 4=0 := by
  norm_num [secondaryTentParameterSeedBeta, secondaryTentRowActualSeedColumn,
    Matrix.mulVec_single_one, secondaryTentSeedCoefficients]

theorem secondaryTent_parameter_beta_sum {p N g boundary a b : ℕ} [Fact p.Prime]
    (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hβ : C (secondaryTentParameterSeedBeta p 1)*secondaryTentParameterInputs p N g boundary a b v 1+
      C (secondaryTentParameterSeedBeta p 2)*secondaryTentParameterInputs p N g boundary a b v 2+
      C (secondaryTentParameterSeedBeta p 3)*secondaryTentParameterInputs p N g boundary a b v 3=0) :
    (∑ i : Fin 5, C ((secondaryTentRowNaturalQ (secondaryTentRowActualSeedColumn i)).eval 1)*
      secondaryTentParameterInputs p N g boundary a b v i) =
      C (secondaryTentParameterSeedBeta p 0)*secondaryTentResponseInput p N v.1 := by
  simp_rw [secondaryTent_natural_Q_at_one]
  change (∑ i : Fin 5, C (secondaryTentParameterSeedBeta p i)*
    secondaryTentParameterInputs p N g boundary a b v i) = _
  simp only [Fin.sum_univ_succ, Fin.isValue, secondaryTent_parameter_seed_beta_boundary,
    map_zero, zero_mul, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have hzero : secondaryTentParameterInputs p N g boundary a b v 0 =
      secondaryTentResponseInput p N v.1 := rfl
  rw [hzero]
  change C (secondaryTentParameterSeedBeta p 0)*secondaryTentResponseInput p N v.1 +
    (C (secondaryTentParameterSeedBeta p 1)*secondaryTentParameterInputs p N g boundary a b v 1 +
      (C (secondaryTentParameterSeedBeta p 2)*secondaryTentParameterInputs p N g boundary a b v 2 +
        (C (secondaryTentParameterSeedBeta p 3)*secondaryTentParameterInputs p N g boundary a b v 3 +
          C (secondaryTentParameterSeedBeta p 4)*secondaryTentParameterInputs p N g boundary a b v 4))) = _
  rw [secondaryTent_parameter_seed_beta_boundary]
  simp only [map_zero, zero_mul, add_zero]
  linear_combination hβ

theorem secondaryTent_parameter_natural_V_flag {p N half g boundary a b : ℕ} [Fact p.Prime]
    (hN : 0<N) (hNp : N≤p) (hm : N+half≤p-N)
    (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hβ : C (secondaryTentParameterSeedBeta p 1)*secondaryTentParameterInputs p N g boundary a b v 1+
      C (secondaryTentParameterSeedBeta p 2)*secondaryTentParameterInputs p N g boundary a b v 2+
      C (secondaryTentParameterSeedBeta p 3)*secondaryTentParameterInputs p N g boundary a b v 3=0) :
    (X-1)^(N+half) ∣ secondaryTentParameterNaturalVLinear p N g boundary a b v := by
  exact secondaryTent_beta_flag_pays_V
    (fun i => secondaryTentRowNaturalQ (secondaryTentRowActualSeedColumn i))
    (secondaryTentParameterInputs p N g boundary a b v)
    (secondaryTentResponseInput p N v.1) (secondaryTentParameterSeedBeta p 0)
    (by omega) hm (secondaryTent_response_input_factor hN hNp v.1)
    (secondaryTent_parameter_beta_sum v hβ)

theorem secondaryTent_parameter_alpha_degree {p N g boundary a b : ℕ} [Fact p.Prime]
    (hN : 0<N) (hg : 0<g) (ha : a+g=p) (hb : b+3*N=p) (hboundary : boundary≤p)
    (v : SecondaryTentParameters (ZMod p) N g boundary) :
    (secondaryTentParameterAlpha2Linear p N g boundary a b v).natDegree<p := by
  have hI := secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v
  have hp := (Fact.out : p.Prime).pos
  apply lt_of_le_of_lt (b := p-1) _ (by omega)
  change (∑ i : Fin 5, secondaryTentRowActualSeedColumn i 2 •
    secondaryTentParameterInputs p N g boundary a b v i).natDegree≤p-1
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [← C_mul']
  exact (natDegree_C_mul_le _ _).trans (by have hh := hI i; omega)

theorem secondaryTent_parameter_shared_cap {p N g boundary a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hN : 0<N) (hg : 0<g) (ha : a+g=p) (hb : b+3*N=p)
    (hboundary : boundary≤p) (hlo : 8*N+2≤2*p) (hhi : p≤8*N)
    (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hflag : secondaryTentPolynomialWindowLinear (2*p-8*N-1) (8*N-p+1)
      (secondaryTentParameterAlpha2Linear p N g boundary a b v)=0) :
    (secondaryTentParameterPacketLinear p N g boundary a b v).natDegree+8*N+3≤10*p := by
  have hcount : p-(2*p-8*N-1)=8*N-p+1 := by omega
  have htail := secondaryTent_polynomial_tail_flag (p := p) (m := 2*p-8*N-1)
    (by omega : 0<2*p-8*N-1) (by omega : 2*p-8*N-1≤p)
    (secondaryTentParameterAlpha2Linear p N g boundary a b v)
    (secondaryTent_parameter_alpha_degree hN hg ha hb hboundary v)
    (by rw [hcount]; exact hflag)
  exact secondaryTent_parameter_packet_shared_degree h2 hN hg ha hb hboundary
    (2*p-8*N-2) (by omega) (by omega) v (by omega)

/-- Every factor in the actual row divisor is paid by a literal natural
input flag. The endpoint assumption is supplied separately on each side. -/
theorem secondaryTent_parameter_total_divisor {p N half g boundary a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hN : 0<N) (hg : 0<g) (ha : a+g=p) (hb : b+3*N=p)
    (hboundary : boundary≤p) (hodd : p=2*half+1) (hm : N+half≤p-N)
    (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hβ : C (secondaryTentParameterSeedBeta p 1)*secondaryTentParameterInputs p N g boundary a b v 1+
      C (secondaryTentParameterSeedBeta p 2)*secondaryTentParameterInputs p N g boundary a b v 2+
      C (secondaryTentParameterSeedBeta p 3)*secondaryTentParameterInputs p N g boundary a b v 3=0)
    (hu₁ : secondaryTentPolynomialWindowLinear 0 N
      (secondaryTentPolynomialTranslateLinear (1:ZMod p)
        (secondaryTentParameterNaturalULinear p N g boundary a b v))=0)
    (hu₂ : secondaryTentPolynomialWindowLinear 0 half
      (secondaryTentPolynomialTranslateLinear (-1:ZMod p)
        (secondaryTentParameterNaturalULinear p N g boundary a b v))=0)
    (hz : X^(24*N-2*p) ∣ secondaryTentParameterPacketLinear p N g boundary a b v) :
    secondaryTentRowTotalDivisor N p a ∣ secondaryTentParameterPacketLinear p N g boundary a b v := by
  have hdeg := secondaryTent_parameter_natural_degree hN hg ha hb hboundary v
  have hzero := secondaryTent_parameter_natural_zero_flags (b := b) (by omega : a≤p) v
  have hV := secondaryTent_parameter_natural_V_flag hN (by omega) hm v hβ
  have hU₁ : (X-1)^N ∣ secondaryTentParameterNaturalULinear p N g boundary a b v := by
    simpa using secondaryTent_polynomial_shift_flag (1:ZMod p) _ hu₁
  have hU₂ : (X+1)^half ∣ secondaryTentParameterNaturalULinear p N g boundary a b v := by
    simpa using secondaryTent_polynomial_shift_flag (-1:ZMod p) _ hu₂
  rw [secondaryTent_parameter_natural_packet_expansion hN hg ha hb hboundary] at hz ⊢
  exact secondaryTent_row_natural_total_flags h2 N half p a (24*N-2*p) (4*p-1)
    (4*p-1-a) (4*p-1-N-half) _ _ hodd (by omega) (by omega)
    hdeg.1 hdeg.2 hzero.1 hzero.2 hU₁ hU₂ hV hz

theorem secondaryTent_positive_parameter_geometry {p N half δ g a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hN : 0<N) (hδ : 0<δ) (hg : 0<g)
    (hp : p=6*N+δ) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hhi : p≤8*N) (hpN : 2*p≤24*N)
    (v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentPositiveCosts N p half)
      (secondaryTentPositiveParameterConstraints p N half δ g a b))) :
    secondaryTentRowTotalDivisor N p a ∣ secondaryTentParameterPacketLinear p N g (4*δ) a b v.val ∧
    (secondaryTentParameterPacketLinear p N g (4*δ) a b v.val).natDegree+8*N+3≤10*p := by
  have hf₀ := secondaryTent_constraint_kernel_flag _
    (secondaryTentPositiveParameterConstraints p N half δ g a b) v 0
  have hf₁ := secondaryTent_constraint_kernel_flag _
    (secondaryTentPositiveParameterConstraints p N half δ g a b) v 1
  have hf₂ := secondaryTent_constraint_kernel_flag _
    (secondaryTentPositiveParameterConstraints p N half δ g a b) v 2
  have hf₃ := secondaryTent_constraint_kernel_flag _
    (secondaryTentPositiveParameterConstraints p N half δ g a b) v 3
  change secondaryTentPolynomialWindowLinear 0 (3*N)
    (secondaryTentParameterPositiveBetaLinear p N g (4*δ) δ
      (secondaryTentParameterSeedBeta p 1) (secondaryTentParameterSeedBeta p 2)
      (secondaryTentParameterSeedBeta p 3) v.val)=0 at hf₀
  have hβ := secondaryTent_parameter_positive_beta_pays (a := a) (b := b) hN hg (by omega) (by omega)
    (secondaryTentParameterSeedBeta p 1) (secondaryTentParameterSeedBeta p 2)
    (secondaryTentParameterSeedBeta p 3) v.val hf₀
  have hboundary : 4*δ≤p := by omega
  have hI := secondaryTent_parameter_inputs_degree hN hg ha hb hboundary v.val
  have hz : X^(24*N-2*p) ∣ secondaryTentParameterPacketLinear p N g (4*δ) a b v.val := by
    change X^(24*N-2*p) ∣ secondaryTentRowFixedNaturalPacket p
      (secondaryTentInputsCoefficientsLinear p (secondaryTentParameterInputs p N g (4*δ) a b v.val))
    apply secondaryTent_actual_row_positive_lower_flag h2 N δ (4*δ-1) _ hp (by omega) (by omega) hpN
    rw [secondaryTent_inputs_coefficients_roundtrip _ hI]
    change (secondaryTentCoefficientPolynomial (4*δ) v.val.2.2.2.2).natDegree≤4*δ-1
    have hh := secondaryTent_coefficient_polynomial_degree (by omega : 0<4*δ) v.val.2.2.2.2
    omega
  constructor
  · exact secondaryTent_parameter_total_divisor h2 hN hg ha hb hboundary hodd (by omega)
      v.val hβ hf₁ hf₂ hz
  · exact secondaryTent_parameter_shared_cap h2 hN hg ha hb hboundary (by omega) hhi v.val hf₃

theorem secondaryTent_negative_parameter_geometry {p N half d g a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hN : 0<N) (hg : 0<g)
    (hp : p+d=6*N) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hlo : 8*N+2≤2*p) (hhi : p≤8*N)
    (v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentNegativeCosts N p half g d)
      (secondaryTentNegativeParameterConstraints p N half g d a b))) :
    secondaryTentRowTotalDivisor N p a ∣ secondaryTentParameterPacketLinear p N g 0 a b v.val ∧
    (secondaryTentParameterPacketLinear p N g 0 a b v.val).natDegree+8*N+3≤10*p := by
  have hf₀ := secondaryTent_constraint_kernel_flag _
    (secondaryTentNegativeParameterConstraints p N half g d a b) v 0
  have hf₁ := secondaryTent_constraint_kernel_flag _
    (secondaryTentNegativeParameterConstraints p N half g d a b) v 1
  have hf₂ := secondaryTent_constraint_kernel_flag _
    (secondaryTentNegativeParameterConstraints p N half g d a b) v 2
  have hf₃ := secondaryTent_constraint_kernel_flag _
    (secondaryTentNegativeParameterConstraints p N half g d a b) v 3
  have hf₄ := secondaryTent_constraint_kernel_flag _
    (secondaryTentNegativeParameterConstraints p N half g d a b) v 4
  change secondaryTentPolynomialWindowLinear 0 g
    (secondaryTentParameterNegativeBetaLinear p N g 0 d
      (secondaryTentParameterSeedBeta p 1) (secondaryTentParameterSeedBeta p 2)
      (secondaryTentParameterSeedBeta p 3) v.val)=0 at hf₀
  have hβ := secondaryTent_parameter_negative_beta_pays (a := a) (b := b) hN (by omega) (by omega)
    (secondaryTentParameterSeedBeta p 1) (secondaryTentParameterSeedBeta p 2)
    (secondaryTentParameterSeedBeta p 3) v.val hf₀
  have hI := secondaryTent_parameter_inputs_degree hN hg ha hb (by omega : 0≤p) v.val
  have hz : X^(24*N-2*p) ∣ secondaryTentParameterPacketLinear p N g 0 a b v.val := by
    change X^(24*N-2*p) ∣ secondaryTentRowFixedNaturalPacket p
      (secondaryTentInputsCoefficientsLinear p (secondaryTentParameterInputs p N g 0 a b v.val))
    apply secondaryTent_actual_row_negative_lower_flag h2 N d _ hp
    · rw [secondaryTent_inputs_coefficients_roundtrip _ hI]
      simp [secondaryTentParameterInputs, secondaryTentCoefficientPolynomial]
    · intro j
      exact congrFun hf₄ j
  constructor
  · exact secondaryTent_parameter_total_divisor h2 hN hg ha hb (by omega) hodd (by omega)
      v.val hβ hf₁ hf₂ hz
  · exact secondaryTent_parameter_shared_cap h2 hN hg ha hb (by omega) hlo hhi v.val hf₃

def secondaryTentPositiveActualRowLinear (p N half δ g a b : ℕ) [Fact p.Prime] :=
  (secondaryTentParameterActualRowLinear p N g (4*δ) a b).comp
    (LinearMap.ker (secondaryTentConstraintMap (secondaryTentPositiveCosts N p half)
      (secondaryTentPositiveParameterConstraints p N half δ g a b))).subtype

def secondaryTentNegativeActualRowLinear (p N half g d a b : ℕ) [Fact p.Prime] :=
  (secondaryTentParameterActualRowLinear p N g 0 a b).comp
    (LinearMap.ker (secondaryTentConstraintMap (secondaryTentNegativeCosts N p half g d)
      (secondaryTentNegativeParameterConstraints p N half g d a b))).subtype

theorem secondaryTent_positive_actual_row_injective {p N half δ g a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hunit : (3445975817256960:ZMod p)≠0)
    (hN : 0<N) (hδ : 0<δ) (hg : 0<g)
    (hp : p=6*N+δ) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hhi : p≤8*N) (hpN : 2*p≤24*N) :
    Function.Injective (secondaryTentPositiveActualRowLinear p N half δ g a b) := by
  intro v w heq
  apply Subtype.ext
  have hv := secondaryTent_positive_parameter_geometry h2 hN hδ hg hp hodd hgp ha hb hhi hpN v
  have hw := secondaryTent_positive_parameter_geometry h2 hN hδ hg hp hodd hgp ha hb hhi hpN w
  exact secondaryTent_parameter_actual_row_injective_on_flags h2 hunit hN hg (by omega)
    ha hb (by omega) (by exact ⟨half,by omega⟩) hpN hgp v.val w.val hv.2 hw.2 hv.1 hw.1 heq

theorem secondaryTent_negative_actual_row_injective {p N half g d a b : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (hunit : (3445975817256960:ZMod p)≠0)
    (hN : 0<N) (hg : 0<g)
    (hp : p+d=6*N) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hlo : 8*N+2≤2*p) (hhi : p≤8*N) :
    Function.Injective (secondaryTentNegativeActualRowLinear p N half g d a b) := by
  intro v w heq
  apply Subtype.ext
  have hv := secondaryTent_negative_parameter_geometry h2 hN hg hp hodd hgp ha hb hlo hhi v
  have hw := secondaryTent_negative_parameter_geometry h2 hN hg hp hodd hgp ha hb hlo hhi w
  exact secondaryTent_parameter_actual_row_injective_on_flags h2 hunit hN hg (by omega)
    ha hb (by omega) (by exact ⟨half,by omega⟩) (by omega) hgp v.val w.val hv.2 hw.2 hv.1 hw.1 heq

end
end CatalanMeasure.Parametric
