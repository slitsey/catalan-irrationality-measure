module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentParametersBeta
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentParametersNatural
public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def secondaryTentParameterSeedBeta (p : ℕ) [Fact p.Prime] (i : Fin 5) : ZMod p :=
  secondaryTentRowActualSeedColumn i 3

def secondaryTentParameterResponseScalar (p N : ℕ) [Fact p.Prime] : ZMod p :=
  -8*(2:ZMod p)^(26*N-1)*(747824613120:ZMod p)

def secondaryTentParameterResponsePolynomialLinear (p N g boundary : ℕ) [Fact p.Prime] :
    SecondaryTentParameters (ZMod p) N g boundary →ₗ[ZMod p] (ZMod p)[X] where
  toFun v := C (secondaryTentParameterResponseScalar p N)*secondaryTentResponsePolynomial p N v.1
  map_add' := by
    intro v w
    simp [secondaryTentResponsePolynomial, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    have hh : secondaryTentResponsePolynomial p N (r • v.1) =
      r • secondaryTentResponsePolynomial p N v.1 :=
      (secondaryTentResponsePolynomialLinear p N).map_smul r v.1
    change C (secondaryTentParameterResponseScalar p N)*
      secondaryTentResponsePolynomial p N (r • v.1) =
      r • (C (secondaryTentParameterResponseScalar p N)*secondaryTentResponsePolynomial p N v.1)
    rw [hh]
    simp only [Polynomial.smul_eq_C_mul]
    ring

def secondaryTentParameterExtraResponseLinear (p N g boundary a b j e : ℕ) [Fact p.Prime] :
    SecondaryTentParameters (ZMod p) N g boundary →ₗ[ZMod p] ZMod p where
  toFun v := (∑ r : Fin (20*N),
    palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j)*
      secondaryTentParameterActualRowLinear p N g boundary a b v r) -
    (secondaryTentParameterResponsePolynomialLinear p N g boundary v).eval (e:ZMod p)
  map_add' := by
    intro v w
    simp [map_add, mul_add, Finset.sum_add_distrib, sub_add_sub_comm]
  map_smul' := by
    intro t v
    simp [map_smul, smul_eq_mul, Finset.mul_sum, Polynomial.smul_eq_C_mul,
      mul_assoc, mul_left_comm, mul_sub]

/-- All four upper-side flags are explicit linear coefficient maps on the
actual five input blocks. Their target dimensions are the human proof costs. -/
def secondaryTentPositiveParameterConstraints (p N half δ g a b : ℕ) [Fact p.Prime] :
    ∀ i : Fin 4, SecondaryTentParameters (ZMod p) N g (4*δ) →ₗ[ZMod p]
      (Fin (secondaryTentPositiveCosts N p half i) → ZMod p) := by
  refine Fin.cons ?_ (Fin.cons ?_ (Fin.cons ?_ (Fin.cons ?_ (fun i => Fin.elim0 i))))
  · exact (secondaryTentPolynomialWindowLinear 0 (3*N)).comp
      (secondaryTentParameterPositiveBetaLinear p N g (4*δ) δ
        (secondaryTentParameterSeedBeta p 1) (secondaryTentParameterSeedBeta p 2)
        (secondaryTentParameterSeedBeta p 3))
  · exact (secondaryTentPolynomialWindowLinear 0 N).comp
      ((secondaryTentPolynomialTranslateLinear (1:ZMod p)).comp
        (secondaryTentParameterNaturalULinear p N g (4*δ) a b))
  · exact (secondaryTentPolynomialWindowLinear 0 half).comp
      ((secondaryTentPolynomialTranslateLinear (-1:ZMod p)).comp
        (secondaryTentParameterNaturalULinear p N g (4*δ) a b))
  · exact (secondaryTentPolynomialWindowLinear (2*p-8*N-1) (8*N-p+1)).comp
      (secondaryTentParameterAlpha2Linear p N g (4*δ) a b)

/-- The lower side adds actual K-coefficient zeros and the literal extra
J=4 raw-column responses. Thus no generic macro-surjectivity is assumed. -/
def secondaryTentNegativeParameterConstraints (p N half g d a b : ℕ) [Fact p.Prime] :
    ∀ i : Fin 6, SecondaryTentParameters (ZMod p) N g 0 →ₗ[ZMod p]
      (Fin (secondaryTentNegativeCosts N p half g d i) → ZMod p) := by
  refine Fin.cons ?_ (Fin.cons ?_ (Fin.cons ?_ (Fin.cons ?_
    (Fin.cons ?_ (Fin.cons ?_ (fun i => Fin.elim0 i))))))
  · exact (secondaryTentPolynomialWindowLinear 0 g).comp
      (secondaryTentParameterNegativeBetaLinear p N g 0 d
        (secondaryTentParameterSeedBeta p 1) (secondaryTentParameterSeedBeta p 2)
        (secondaryTentParameterSeedBeta p 3))
  · exact (secondaryTentPolynomialWindowLinear 0 N).comp
      ((secondaryTentPolynomialTranslateLinear (1:ZMod p)).comp
        (secondaryTentParameterNaturalULinear p N g 0 a b))
  · exact (secondaryTentPolynomialWindowLinear 0 half).comp
      ((secondaryTentPolynomialTranslateLinear (-1:ZMod p)).comp
        (secondaryTentParameterNaturalULinear p N g 0 a b))
  · exact (secondaryTentPolynomialWindowLinear (2*p-8*N-1) (8*N-p+1)).comp
      (secondaryTentParameterAlpha2Linear p N g 0 a b)
  · exact (secondaryTentPolynomialWindowLinear (2*p) (4*d)).comp
      (secondaryTentParameterPacketLinear p N g 0 a b)
  · exact LinearMap.pi fun e : Fin (4*d) =>
      secondaryTentParameterExtraResponseLinear p N g 0 a b (4*p+e.val) e.val

theorem secondaryTent_constraint_kernel_flag {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι]
    (cost : ι → ℕ) (B : ∀ i, V →ₗ[K] (Fin (cost i) → K))
    (v : LinearMap.ker (secondaryTentConstraintMap cost B)) (i : ι) : B i v.val=0 := by
  have hv := LinearMap.mem_ker.mp v.property
  exact congrFun hv i

end
end CatalanMeasure.Parametric
