module
public import CatalanMeasure.Parametric.SecondaryTentRowPolynomial
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

/-- Ordinary polynomial left after paying the quadratic and beta
denominators in the literal six-channel `t` representation. `R` contains
the three denominator-free channels; `F` is the homogenized small eta0
input; `B,C` are the homogenized small kernel inputs. -/
def secondaryTentRowBulkNumerator {K : Type*} [CommRing K]
    (p g b : ℕ) (β : K) (R F B C : K[X]) : K[X] :=
  (X^2+1)^g * R + (X^2+1)^g * X^p * Polynomial.C β *
    (X-1)^(2*b-p) * F + X^p * B + X^(2*p) * C

/-- A polynomial identity certifying simultaneous cancellation of the
actual quadratic seed denominators and the residual eta0 beta denominator.
The other beta channels have already been killed by their polynomial flag.
The hypotheses are precisely `g+a=p` and `p≤2(p-N)`. -/
theorem secondaryTent_row_bulk_denominators_paid {K : Type*} [CommRing K]
    (p g a b : ℕ) (β : K) (R F B C : K[X])
    (hga : g+a=p) (hpb : p ≤ 2*b) :
    (X^2+1)^p * (X-1)^p * secondaryTentRowBulkNumerator p g b β R F B C =
      (X^2+1)^g *
        ((X^2+1)^p * (X-1)^p * R +
         (X^2+1)^p * X^p * (Polynomial.C β * (X-1)^(2*b) * F) +
         (X-1)^p * (X^p * ((X^2+1)^a * B) + X^(2*p) * ((X^2+1)^a * C))) := by
  have hb : (X-1 : K[X])^(2*b) = (X-1)^p * (X-1)^(2*b-p) := by
    rw [← pow_add, Nat.add_sub_of_le hpb]
  have hq : (X^2+1 : K[X])^p = (X^2+1)^g * (X^2+1)^a := by
    rw [← pow_add, hga]
  unfold secondaryTentRowBulkNumerator
  rw [hb, hq]
  ring

theorem secondaryTent_rowInput_beta_cancel {K : Type*} [CommRing K]
    (n : ℕ) (β₁ β₂ βE : K) (I₁ I₂ IE : K[X])
    (hβ : β₁ • I₁ + β₂ • I₂ + βE • IE = 0) :
    β₁ • secondaryTentRowInput n I₁ + β₂ • secondaryTentRowInput n I₂ +
      βE • secondaryTentRowInput n IE = 0 := by
  have h := congrArg (secondaryTentRowInput n) hβ
  unfold secondaryTentRowInput at h ⊢
  rw [secondaryTent_rowHom_add, secondaryTent_rowHom_add,
    secondaryTent_rowHom_smul, secondaryTent_rowHom_smul,
    secondaryTent_rowHom_smul] at h
  simpa only [secondaryTentRowHom, coeff_zero, map_zero, zero_mul,
    Finset.sum_const_zero] using h

/-- On the positive side the beta flag is the small degree `<3N`
bracket, after removing the common `X^(p-3N)` factor. -/
theorem secondaryTent_row_positive_beta_flag {K : Type*} [CommRing K]
    (c t : ℕ) (β₁ β₂ βE : K) (f₁ f₂ h : K[X])
    (hβ : X^t * (β₁ • f₁ + β₂ • f₂) + βE • h = 0) :
    β₁ • (X^(c+t)*f₁) + β₂ • (X^(c+t)*f₂) + βE • (X^c*h) = 0 := by
  have h := congrArg (fun P : K[X] => X^c * P) hβ
  simp only [Polynomial.smul_eq_C_mul, mul_zero] at h ⊢
  rw [pow_add]
  linear_combination h

/-- On the negative side the beta flag has degree `<g`, with the etaE
input shifted by `X^(4d)` after removing `X^a`. -/
theorem secondaryTent_row_negative_beta_flag {K : Type*} [CommRing K]
    (a t : ℕ) (β₁ β₂ βE : K) (f₁ f₂ h : K[X])
    (hβ : β₁ • f₁ + β₂ • f₂ + X^t * (βE • h) = 0) :
    β₁ • (X^a*f₁) + β₂ • (X^a*f₂) + βE • (X^(a+t)*h) = 0 := by
  have h := congrArg (fun P : K[X] => X^a * P) hβ
  simp only [Polynomial.smul_eq_C_mul, mul_zero] at h ⊢
  rw [pow_add]
  linear_combination h

end
end CatalanMeasure.Parametric
