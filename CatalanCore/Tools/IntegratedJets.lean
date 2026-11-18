module
public import CatalanCore.Tools.Jets.Heine
public import CatalanCore.Tools.Jets.Collisions
public import CatalanCore.Tools.Jets.Bound
public import Mathlib.MeasureTheory.Integral.Pi
@[expose] public section
set_option Elab.async false
open MeasureTheory Polynomial
open scoped BigOperators
namespace CatalanCore.Tools.IntegratedJets

noncomputable def tensorIntegrand {α : Type*} (M : ℕ)
    (Ψ : α → ℂ[X] →ₗ[ℂ] ℂ) (P : MvPolynomial (Fin M) ℂ)
    (x : Fin M → α) : ℂ :=
  ∑ d ∈ P.support, P.coeff d * ∏ i : Fin M, Ψ (x i) (Polynomial.X^(d i))

theorem tensor_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) (Ψ : α → ℂ[X] →ₗ[ℂ] ℂ)
    (hint : ∀ k : ℕ, Integrable (fun x => Ψ x (Polynomial.X^k)) μ)
    (hΦ : ∀ k : ℕ, Φ (Polynomial.X^k)=∫ x, Ψ x (Polynomial.X^k) ∂μ)
    (P : MvPolynomial (Fin M) ℂ) :
  Integrable (tensorIntegrand M Ψ P) (Measure.pi (fun _ : Fin M => μ)) ∧
  CatalanCore.Tools.Jets.tensor M Φ P=
    ∫ x, tensorIntegrand M Ψ P x ∂Measure.pi (fun _ : Fin M => μ) := by
  classical
  have hi (d : Fin M →₀ ℕ) : Integrable
      (fun x : Fin M → α => P.coeff d*∏ i : Fin M, Ψ (x i) (Polynomial.X^(d i)))
      (Measure.pi (fun _ : Fin M => μ)) :=
    (Integrable.fintype_prod (fun i : Fin M => hint (d i))).const_mul _
  constructor
  · exact integrable_finset_sum _ (fun d hd => hi d)
  · unfold Jets.tensor tensorIntegrand
    rw [integral_finset_sum _ (fun d hd => hi d)]
    apply Finset.sum_congr rfl
    intro d hd
    have hfub := integral_fintype_prod_eq_prod (μ := fun _ : Fin M => μ)
      (fun i : Fin M => fun x : α => Ψ x (Polynomial.X^(d i)))
    rw [integral_const_mul,hfub]
    simp only [← hΦ]

theorem heine_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) (Ψ : α → ℂ[X] →ₗ[ℂ] ℂ)
    (hint : ∀ k : ℕ, Integrable (fun x => Ψ x (Polynomial.X^k)) μ)
    (hΦ : ∀ k : ℕ, Φ (Polynomial.X^k)=∫ x, Ψ x (Polynomial.X^k) ∂μ) :
    Matrix.det (fun i j : Fin M => Φ (Polynomial.X^(i.val+j.val)))=
      (M.factorial:ℂ)⁻¹*∫ x, tensorIntegrand M Ψ (Jets.vandSq M) x
        ∂Measure.pi (fun _ : Fin M => μ) := by
  rw [Jets.heine_functional,(tensor_integral μ M Φ Ψ hint hΦ (Jets.vandSq M)).2]
end CatalanCore.Tools.IntegratedJets
#print axioms CatalanCore.Tools.IntegratedJets.tensor_integral
#print axioms CatalanCore.Tools.IntegratedJets.heine_integral

namespace CatalanCore.Tools.IntegratedJets
open CatalanCore.Tools.Jets
attribute [local instance] Classical.propDecidable

noncomputable def jetFactor {M : ℕ} (J : Finset (Fin M)) (a b : Fin M → ℂ)
    (d : Fin M →₀ ℕ) (i : Fin M) : MvPolynomial (Fin M) ℂ :=
  if i ∈ J then MvPolynomial.C (a i)*MvPolynomial.X i^(d i)+
    MvPolynomial.C (b i)*MvPolynomial.C (d i:ℂ)*MvPolynomial.X i^(d i-1)
  else MvPolynomial.X i^(d i)

theorem pderiv_prod_zero {M : ℕ} (i : Fin M) (s : Finset (Fin M))
    (f : Fin M → MvPolynomial (Fin M) ℂ) (h : ∀ j ∈ s, MvPolynomial.pderiv i (f j)=0) :
    MvPolynomial.pderiv i (∏ j ∈ s, f j)=0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj,MvPolynomial.pderiv_mul,h j (by simp),
      ih (fun k hk => h k (by simp [hk]))]
    simp

theorem jetFactor_pderiv_other {M : ℕ} (J : Finset (Fin M)) (a b : Fin M → ℂ)
    (d : Fin M →₀ ℕ) (i j : Fin M) (hji : j ≠ i) :
    MvPolynomial.pderiv i (jetFactor J a b d j)=0 := by
  unfold jetFactor
  split_ifs <;> simp [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X_of_ne hji]

theorem jetPoly_monomial (M : ℕ) (J : Finset (Fin M)) (a b : Fin M → ℂ)
    (d : Fin M →₀ ℕ) (c : ℂ) :
    jetPoly J a b (MvPolynomial.monomial d c)=MvPolynomial.C c*∏ i : Fin M, jetFactor J a b d i := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [jetPoly,Finset.powerset_empty,Finset.sum_singleton,Finset.sdiff_self,
      Finset.prod_empty,one_mul,one_smul,partials,Finset.toList_empty,List.foldl_nil]
    simp only [jetFactor,Finset.notMem_empty,↓reduceIte]
    rw [prod_monomial]
    have he : degreeVec (fun i : Fin M => d i)=d := by ext i; simp
    rw [he,MvPolynomial.C_mul_monomial,mul_one]
  | @insert i J hi ih =>
    rw [jetPoly_insert M J i hi,ih]
    have hprod (S : Finset (Fin M)) :
        (∏ j : Fin M, jetFactor S a b d j)=jetFactor S a b d i*∏ j ∈ Finset.univ.erase i, jetFactor S a b d j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have hsame : (∏ j ∈ Finset.univ.erase i, jetFactor (insert i J) a b d j)=
        ∏ j ∈ Finset.univ.erase i, jetFactor J a b d j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [jetFactor,Finset.mem_insert,or_iff_right (Finset.mem_erase.mp hj).1]
    have hzero : MvPolynomial.pderiv i (∏ j ∈ Finset.univ.erase i, jetFactor J a b d j)=0 :=
      pderiv_prod_zero i _ _ (fun j hj => jetFactor_pderiv_other J a b d i j (Finset.mem_erase.mp hj).1)
    rw [hprod J,hprod (insert i J),hsame]
    simp only [jetOp,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
      Derivation.coeFn_coe,MvPolynomial.smul_eq_C_mul]
    have hfi : jetFactor J a b d i=MvPolynomial.X i^(d i) := by simp [jetFactor,hi]
    have hfi2 : jetFactor (insert i J) a b d i=
        MvPolynomial.C (a i)*MvPolynomial.X i^(d i)+
        MvPolynomial.C (b i)*MvPolynomial.C (d i:ℂ)*MvPolynomial.X i^(d i-1) := by simp [jetFactor]
    rw [hfi,hfi2,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_mul,
      hzero,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X_self]
    simp only [mul_one,mul_zero,add_zero]
    have hcast : (d i : MvPolynomial (Fin M) ℂ)=MvPolynomial.C (d i:ℂ) := by simp
    rw [hcast]
    ring

theorem mixedJet_monomial (M : ℕ) (J : Finset (Fin M)) (a b x : Fin M → ℂ)
    (d : Fin M →₀ ℕ) (c : ℂ) :
    mixedJet J a b x (MvPolynomial.monomial d c)=c*∏ i : Fin M,
      if i ∈ J then a i*x i^(d i)+b i*(d i:ℂ)*x i^(d i-1) else x i^(d i) := by
  rw [← eval_jetPoly,jetPoly_monomial]
  simp [jetFactor,map_prod,apply_ite]
end CatalanCore.Tools.IntegratedJets
#print axioms CatalanCore.Tools.IntegratedJets.mixedJet_monomial


namespace CatalanCore.Tools.IntegratedJets
open CatalanCore.Tools.Jets

theorem jetPoly_finset_sum {α : Type*} (M : ℕ) (J : Finset (Fin M)) (a b : Fin M → ℂ)
    (s : Finset α) (f : α → MvPolynomial (Fin M) ℂ) :
    jetPoly J a b (∑ u ∈ s, f u)=∑ u ∈ s, jetPoly J a b (f u) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [jetPoly,partials]
  | @insert i J hi ih =>
    rw [jetPoly_insert M J i hi,ih,map_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [jetPoly_insert M J i hi]

theorem mixedJet_expansion (M : ℕ) (J : Finset (Fin M)) (a b x : Fin M → ℂ)
    (P : MvPolynomial (Fin M) ℂ) :
    mixedJet J a b x P=∑ d ∈ P.support, P.coeff d*∏ i : Fin M,
      if i ∈ J then a i*x i^(d i)+b i*(d i:ℂ)*x i^(d i-1) else x i^(d i) := by
  classical
  have hsum : jetPoly J a b P=∑ d ∈ P.support, jetPoly J a b (MvPolynomial.monomial d (P.coeff d)) := by
    calc
      _=jetPoly J a b (∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)) :=
        congrArg (jetPoly J a b) P.as_sum
      _=_ := jetPoly_finset_sum M J a b P.support _
  rw [← eval_jetPoly,hsum,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [eval_jetPoly,mixedJet_monomial]
end CatalanCore.Tools.IntegratedJets
#print axioms CatalanCore.Tools.IntegratedJets.mixedJet_expansion
