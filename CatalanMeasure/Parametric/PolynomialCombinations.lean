module
public import CatalanMeasure.Parametric.KernelEmbeddingRank
public import CatalanMeasure.Parametric.PrimeDigitSampling
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Matrix
open scoped BigOperators
noncomputable section

def polynomialCombination {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (c : Fin g → K) : K[X] :=∑ d,c d • F d

theorem polynomialCombination_coeff {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (c : Fin g → K) (i : ℕ) :
    (polynomialCombination F c).coeff i=∑ d,c d*(F d).coeff i :=by
  simp [polynomialCombination]

theorem polynomialCombination_congr {K : Type*} [Field K] {g : ℕ}
    (F G : Fin g → K[X]) (c : Fin g → K) (hFG : ∀ d,F d=G d) :
    polynomialCombination F c=polynomialCombination G c :=by
  unfold polynomialCombination
  apply Finset.sum_congr rfl
  intro d hd
  rw [hFG d]

theorem polynomialCombination_sub {K : Type*} [Field K] {g : ℕ}
    (F G : Fin g → K[X]) (c : Fin g → K) :
    polynomialCombination (fun d =>F d-G d) c=polynomialCombination F c-polynomialCombination G c :=by
  simp [polynomialCombination,smul_sub,Finset.sum_sub_distrib]

def polynomialCoefficientMap {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (start count : ℕ) : (Fin g → K) →ₗ[K] (Fin count → K) :=
  (Matrix.of fun t d =>(F d).coeff (start+t.val)).mulVecLin

theorem polynomialCoefficientMap_apply {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (c : Fin g → K) (start count : ℕ) (t : Fin count) :
    polynomialCoefficientMap F start count c t=(polynomialCombination F c).coeff (start+t.val) :=by
  simp only [polynomialCoefficientMap,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,
    Matrix.of_apply,polynomialCombination_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem polynomialCombination_coeff_zero {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (c : Fin g → K) (i : ℕ) (hF : ∀ d,(F d).coeff i=0) :
    (polynomialCombination F c).coeff i=0 :=by
  simp [polynomialCombination_coeff,hF]

theorem polynomialCombination_kernel_support {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (c : Fin g → K) (start upper count : ℕ)
    (hupper : ∀ d i,upper ≤ i → (F d).coeff i=0)
    (hcount : upper-start=count) (hc : polynomialCoefficientMap F start count c=0) :
    ∀ i,start ≤ i → (polynomialCombination F c).coeff i=0 :=by
  intro i hi
  by_cases hu : upper ≤ i
  · exact polynomialCombination_coeff_zero F c i (fun d =>hupper d i hu)
  · let t : Fin count :=⟨i-start,by omega⟩
    have hh :=congrFun hc t
    rw [polynomialCoefficientMap_apply] at hh
    have he : start+t.val=i :=by dsimp only [t]; omega
    simpa only [he,Pi.zero_apply] using hh

theorem polynomialCombination_mul_left {K : Type*} [Field K] {g : ℕ}
    (F : Fin g → K[X]) (c : Fin g → K) (P : K[X]) :
    P*polynomialCombination F c=polynomialCombination (fun d =>P*F d) c :=by
  unfold polynomialCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.smul_eq_C_mul,Polynomial.smul_eq_C_mul]
  ring

theorem primeDigitSample_combination {p g : ℕ} [Fact p.Prime] (H ell : ℕ)
    (f : ℕ → ZMod p) (F : Fin g → (ZMod p)[X]) (c : Fin g → ZMod p) :
    primeDigitSample H p ell f (polynomialCombination F c)=
      ∑ d,c d*primeDigitSample H p ell f (F d) :=by
  unfold primeDigitSample
  simp_rw [polynomialCombination_coeff,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

theorem primeDigitPair_combination {p g : ℕ} [Fact p.Prime] (H j : ℕ)
    (F G : Fin g → (ZMod p)[X]) (c : Fin g → ZMod p) :
    primeDigitPair H p j (polynomialCombination F c) (polynomialCombination G c)=
      ∑ d,c d*primeDigitPair H p j (F d) (G d) :=by
  unfold primeDigitPair
  rw [polynomialCombination_mul_left,primeDigitSample_combination,primeDigitSample_combination,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end
end CatalanMeasure.Parametric
