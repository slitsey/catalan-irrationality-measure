module

public import CatalanCore.Tools.Jets.Defs
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Tactic.Ring

@[expose] public section
set_option Elab.async false
open Polynomial
open scoped BigOperators
namespace CatalanCore.Tools.Jets

noncomputable def degreeVec {M : ℕ} (d : Fin M → ℕ) : Fin M →₀ ℕ :=
  Finsupp.indicator Finset.univ (fun i _ => d i)

@[simp] theorem degreeVec_apply {M : ℕ} (d : Fin M → ℕ) (i : Fin M) :
    degreeVec d i=d i := by simp [degreeVec]

theorem prod_monomial (M : ℕ) (d : Fin M → ℕ) :
    (∏ i : Fin M, (MvPolynomial.X i : MvPolynomial (Fin M) ℂ)^d i)=
      MvPolynomial.monomial (degreeVec d) 1 := by
  classical
  simpa [degreeVec] using (MvPolynomial.prod_X_pow (R := ℂ) d Finset.univ)

noncomputable def anti (M : ℕ) : MvPolynomial (Fin M) ℂ :=
  (Matrix.vandermonde (fun i : Fin M => (MvPolynomial.X i : MvPolynomial (Fin M) ℂ))).det

def signC {M : ℕ} (σ : Equiv.Perm (Fin M)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

theorem vandSq_eq_anti_sq (M : ℕ) : vandSq M=anti M^2 := by
  classical
  rw [anti, Matrix.det_vandermonde]
  unfold vandSq
  simp only [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem anti_expand (M : ℕ) :
    anti M=∑ σ : Equiv.Perm (Fin M), signC σ •
      MvPolynomial.monomial (degreeVec (fun i => (σ i).val)) 1 := by
  classical
  rw [anti, ← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
  rw [prod_monomial, MvPolynomial.smul_eq_C_mul]
  congr 1

theorem tensor_sum {α : Type*} (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ)
    (s : Finset α) (f : α → MvPolynomial (Fin M) ℂ) :
    tensor M Φ (∑ a ∈ s, f a)=∑ a ∈ s, tensor M Φ (f a) := by
  simpa only [tensorLinear_apply] using (map_sum (tensorLinear M Φ) f s)

theorem tensor_terms (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) (σ τ : Equiv.Perm (Fin M)) :
    tensor M Φ ((signC σ • MvPolynomial.monomial (degreeVec (fun i => (σ i).val)) 1)*
      (signC τ • MvPolynomial.monomial (degreeVec (fun i => (τ i).val)) 1)) =
      (signC σ*signC τ)*∏ i : Fin M, Φ (Polynomial.X^((σ i).val+(τ i).val)) := by
  rw [smul_mul_smul_comm, tensor_smul, MvPolynomial.monomial_mul_monomial,
    tensor_monomial]
  simp only [mul_one, one_mul, Finsupp.add_apply, degreeVec_apply]

theorem signC_mul {M : ℕ} (σ τ : Equiv.Perm (Fin M)) :
    signC (σ*τ)=signC σ*signC τ := by simp [signC, Equiv.Perm.sign_mul]

theorem signC_sq {M : ℕ} (σ : Equiv.Perm (Fin M)) : signC σ*signC σ=1 := by
  dsimp [signC]
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem relative_term (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) (σ γ : Equiv.Perm (Fin M)) :
    (signC σ*signC (γ*σ))*
      (∏ i : Fin M, Φ (Polynomial.X^((σ i).val+((γ*σ) i).val))) =
      signC γ*∏ i : Fin M, Φ (Polynomial.X^(i.val+(γ i).val)) := by
  rw [signC_mul]
  have hs : signC σ*(signC γ*signC σ)=signC γ := by
    calc
      _=signC γ*(signC σ*signC σ) := by ring
      _=signC γ := by rw [signC_sq, mul_one]
  rw [hs]
  congr 1
  simpa only [Equiv.Perm.mul_apply] using
    (Equiv.prod_comp σ (fun i : Fin M => Φ (Polynomial.X^(i.val+(γ i).val))))

theorem momentDet_expand (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) :
    (∑ γ : Equiv.Perm (Fin M), signC γ*∏ i : Fin M,
      Φ (Polynomial.X^(i.val+(γ i).val))) =
      Matrix.det (fun i j : Fin M => Φ (Polynomial.X^(i.val+j.val))) := by
  classical
  let H : Matrix (Fin M) (Fin M) ℂ :=
    fun i j => Φ (Polynomial.X^(i.val+j.val))
  have h := (Matrix.det_apply' H.transpose).symm
  exact h.trans (Matrix.det_transpose H)

theorem tensor_vandSq (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) :
    tensor M Φ (vandSq M)=(M.factorial:ℂ)*
      Matrix.det (fun i j : Fin M => Φ (Polynomial.X^(i.val+j.val))) := by
  classical
  rw [vandSq_eq_anti_sq, pow_two, anti_expand]
  simp_rw [Finset.sum_mul, Finset.mul_sum, tensor_sum, tensor_terms]
  have hinner (σ : Equiv.Perm (Fin M)) :
      (∑ τ : Equiv.Perm (Fin M), (signC σ*signC τ)*
        ∏ i : Fin M, Φ (Polynomial.X^((σ i).val+(τ i).val))) =
      Matrix.det (fun i j : Fin M => Φ (Polynomial.X^(i.val+j.val))) := by
    calc
      _=∑ γ : Equiv.Perm (Fin M), (signC σ*signC (γ*σ))*
          ∏ i : Fin M, Φ (Polynomial.X^((σ i).val+((γ*σ) i).val)) :=
        (Equiv.sum_comp (Equiv.mulRight σ) _).symm
      _=∑ γ : Equiv.Perm (Fin M), signC γ*∏ i : Fin M,
          Φ (Polynomial.X^(i.val+(γ i).val)) := by
        apply Finset.sum_congr rfl
        intro γ _
        exact relative_term M Φ σ γ
      _=_ := momentDet_expand M Φ
  simp_rw [hinner]
  simp [Fintype.card_perm]

theorem heine_functional (M : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ) :
    Matrix.det (fun i j : Fin M => Φ (Polynomial.X^(i.val+j.val))) =
      (M.factorial:ℂ)⁻¹*tensor M Φ (vandSq M) := by
  rw [tensor_vandSq]
  have hf : (M.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]

#print axioms heine_functional
end CatalanCore.Tools.Jets
