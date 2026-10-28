module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# UF moments, step (a): the second-order resolvent expansion of a one-node moment

For a core matrix `Q = D + π E` (`D` the exact own-fiber block part, `E` the cross-fiber part, which
carries one factor `π = p`), a response `x` with `Q x = Y`, and a border row `σ = s + π s'`
(`s` own-fiber part), the one-node moment `y_t - σ · x` satisfies EXACTLY

  `y_t - σ·x = (y_t - s·D⁻¹Y) - π (s'·D⁻¹Y - s·D⁻¹ E D⁻¹ Y) + π² Rem`.

No unit hypothesis on `Q` is needed (only `D` is inverted).
-/

open Matrix

namespace CatalanCore.Uniform.Content.UFMoments

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The response is the own-fiber response minus `π` times its cross correction. -/
theorem resp_eq (π : R) (D E : Matrix ι ι R) (hD : IsUnit D.det) (Y x : ι → R)
    (hx : D *ᵥ x + π • (E *ᵥ x) = Y) :
    x = D⁻¹ *ᵥ Y - π • (D⁻¹ *ᵥ (E *ᵥ x)) := by
  rw [← hx, mulVec_add, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hD, one_mulVec]
  abel

/-- **Second-order expansion of a one-node moment.** -/
theorem moment_second_order (π : R) (D E : Matrix ι ι R) (hD : IsUnit D.det)
    (Y x : ι → R) (hx : D *ᵥ x + π • (E *ᵥ x) = Y) (s s' : ι → R) (yt : R) :
    yt - (s + π • s') ⬝ᵥ x =
      (yt - s ⬝ᵥ (D⁻¹ *ᵥ Y)) - π * (s' ⬝ᵥ (D⁻¹ *ᵥ Y) - s ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ Y)))) +
        π ^ 2 * (s' ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ x)) -
          s ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ (E *ᵥ x))))) := by
  have h1 := resp_eq π D E hD Y x hx
  have h2 : x = D⁻¹ *ᵥ Y - π • (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ Y))) +
      (π * π) • (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ (E *ᵥ x)))) := by
    conv_lhs => rw [h1]
    conv_lhs => rw [h1]
    simp only [mulVec_sub, mulVec_smul, smul_sub, mul_smul]
    abel
  have e1 : s ⬝ᵥ x = s ⬝ᵥ (D⁻¹ *ᵥ Y) - π * (s ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ Y)))) +
      (π * π) * (s ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ (E *ᵥ x))))) := by
    conv_lhs => rw [h2]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have e2 : s' ⬝ᵥ x = s' ⬝ᵥ (D⁻¹ *ᵥ Y) - π * (s' ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ x))) := by
    conv_lhs => rw [h1]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul, e1, e2]
  ring

end CatalanCore.Uniform.Content.UFMoments
