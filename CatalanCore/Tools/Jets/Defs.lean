module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Finset.Powerset

@[expose] public section
set_option Elab.async false
open Polynomial
open scoped BigOperators

namespace CatalanCore.Tools.Jets

noncomputable def vandSq (M : ℕ) : MvPolynomial (Fin M) ℂ :=
  ∏ i : Fin M, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X i-MvPolynomial.X j)^2

noncomputable def tensor (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ)
    (p : MvPolynomial (Fin M) ℂ) : ℂ :=
  ∑ d ∈ p.support, p.coeff d * ∏ i : Fin M, Φ (Polynomial.X^(d i))

/-- Linearization reuses the standard monomial coefficient equivalence. -/
noncomputable def tensorLinear (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) :
    MvPolynomial (Fin M) ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ
    (fun d : Fin M →₀ ℕ => ∏ i : Fin M, Φ (Polynomial.X^(d i)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem tensorLinear_apply (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ)
    (p : MvPolynomial (Fin M) ℂ) : tensorLinear M Φ p=tensor M Φ p := by
  classical
  simp [tensorLinear, tensor, Finsupp.linearCombination_apply,
    MvPolynomial.sum_def, smul_eq_mul]

theorem tensor_add (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ)
    (p q : MvPolynomial (Fin M) ℂ) :
    tensor M Φ (p+q)=tensor M Φ p+tensor M Φ q := by
  simpa only [tensorLinear_apply] using (tensorLinear M Φ).map_add p q

theorem tensor_smul (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ)
    (c : ℂ) (p : MvPolynomial (Fin M) ℂ) :
    tensor M Φ (c • p)=c*tensor M Φ p := by
  simpa only [tensorLinear_apply, smul_eq_mul] using (tensorLinear M Φ).map_smul c p

theorem tensor_monomial (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ)
    (d : Fin M →₀ ℕ) (c : ℂ) :
    tensor M Φ (MvPolynomial.monomial d c)=c*∏ i : Fin M, Φ (Polynomial.X^(d i)) := by
  rw [← tensorLinear_apply]
  change Finsupp.linearCombination ℂ
    (fun e : Fin M →₀ ℕ => ∏ i : Fin M, Φ (Polynomial.X^(e i))) (Finsupp.single d c) = _
  simp [Finsupp.linearCombination_single, smul_eq_mul]

noncomputable def partials {M : ℕ} (S : Finset (Fin M))
    (p : MvPolynomial (Fin M) ℂ) : MvPolynomial (Fin M) ℂ :=
  S.toList.foldl (fun q i => MvPolynomial.pderiv i q) p

noncomputable def mixedJet {M : ℕ} (Jlat : Finset (Fin M))
    (a b x : Fin M → ℂ) (p : MvPolynomial (Fin M) ℂ) : ℂ :=
  ∑ S ∈ Jlat.powerset, (∏ i ∈ Jlat \ S, a i)*(∏ i ∈ S, b i)*
    MvPolynomial.eval x (partials S p)

noncomputable def jetAt {M : ℕ} (a b x : Fin M → ℂ)
    (p : MvPolynomial (Fin M) ℂ) : ℂ := mixedJet Finset.univ a b x p

noncomputable def evalPair {M : ℕ} (i j : Fin M) (x : ℂ)
    (p : MvPolynomial (Fin M) ℂ) : MvPolynomial (Fin M) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k => if k=i ∨ k=j then MvPolynomial.C x else MvPolynomial.X k) p

structure ConfluentConfig (M : ℕ) where
  x : Fin M → ℂ
  pairs : Finset (Fin M × Fin M)
  ordered : ∀ p ∈ pairs, p.1 < p.2
  disjoint : ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2
  diagonal : ∀ i j, i ≠ j →
    (x i=x j ↔ (i,j) ∈ pairs ∨ (j,i) ∈ pairs)

def ConfluentConfig.paired {M : ℕ} (c : ConfluentConfig M) (i j : Fin M) : Prop :=
  (i,j) ∈ c.pairs ∨ (j,i) ∈ c.pairs

def ConfluentConfig.pairCount {M : ℕ} (c : ConfluentConfig M) : ℕ := c.pairs.card

noncomputable def ConfluentConfig.reducedVand {M : ℕ} (c : ConfluentConfig M) : ℂ :=
  ∏ i : Fin M, ∏ j ∈ Finset.Ioi i, if (i,j) ∈ c.pairs then 1 else (c.x i-c.x j)^2

noncomputable def ConfluentConfig.redLog {M : ℕ} (c : ConfluentConfig M) : ℝ :=
  (∑ i : Fin M, ∑ j ∈ Finset.Ioi i,
    if (i,j) ∈ c.pairs then 0 else 2*Real.log ‖c.x i-c.x j‖) + c.pairs.card*Real.log 2

#print axioms tensorLinear_apply
#print axioms tensor_monomial

end CatalanCore.Tools.Jets