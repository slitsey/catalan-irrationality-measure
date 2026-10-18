import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Complex.Basic

/-!
# The Andréief identity and the absolute-value Andréief bound

For a σ-finite measure `m`, a density `w` and functions `f i, g j` with all `w f_i g_j` integrable,
`∫_{X^k} ∏ w(z_l) det[f_i(z_l)] det[g_j(z_l)] = k! det[∫ w f_i g_j]`.
-/

open MeasureTheory Matrix Finset

namespace CatalanLambda.Decay

section
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- Combinatorial core: `∑_σ ∑_τ s(σ) s(τ) ∏_l A (σ l) (τ l) = k! det A`. -/
lemma sum_sign_sign_prod (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) * ∏ l, A (σ l) (τ l)
      = (k.factorial : ℂ) * A.det := by
  have hdet : A.det = ∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : ℂ) * ∏ i, A i (π i) := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    simp [Units.smul_def]
  have key : ∀ σ : Equiv.Perm (Fin k),
      ∑ τ : Equiv.Perm (Fin k),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) * ∏ l, A (σ l) (τ l)
        = A.det := by
    intro σ
    rw [hdet]
    rw [← Equiv.sum_comp (Equiv.mulRight σ⁻¹)
      (fun π : Equiv.Perm (Fin k) => ((Equiv.Perm.sign π : ℤ) : ℂ) * ∏ i, A i (π i))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : ∏ l, A (σ l) (τ l) = ∏ i, A i ((Equiv.mulRight σ⁻¹ τ) i) := by
      rw [← Equiv.prod_comp σ (fun i => A i ((Equiv.mulRight σ⁻¹ τ) i))]
      simp
    rw [this]
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  simp_rw [key]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm]

end

/-- **Andréief identity** (continuous Cauchy–Binet). -/
theorem andreief_identity {X : Type*} [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    {k : ℕ} (w : X → ℂ) (f g : Fin k → X → ℂ)
    (h : ∀ i j, Integrable (fun z => w z * f i z * g j z) m) :
    ∫ z : Fin k → X, (∏ l, w (z l)) * (Matrix.of fun i l => f i (z l)).det
        * (Matrix.of fun j l => g j (z l)).det ∂(Measure.pi fun _ => m)
      = (k.factorial : ℂ) * (Matrix.of fun i j => ∫ z, w z * f i z * g j z ∂m).det := by
  classical
  set s : Equiv.Perm (Fin k) → ℂ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) with hs
  have hexp : ∀ z : Fin k → X, (∏ l, w (z l)) * (Matrix.of fun i l => f i (z l)).det
        * (Matrix.of fun j l => g j (z l)).det
      = ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
          (s σ * s τ) * ∏ l, (w (z l) * f (σ l) (z l) * g (τ l) (z l)) := by
    intro z
    rw [Matrix.det_apply, Matrix.det_apply]
    simp only [Matrix.of_apply, Units.smul_def, zsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Finset.prod_mul_distrib, hs]
    ring
  have hint : ∀ σ τ : Equiv.Perm (Fin k), Integrable
      (fun z : Fin k → X => ∏ l, (w (z l) * f (σ l) (z l) * g (τ l) (z l)))
      (Measure.pi fun _ => m) := fun σ τ =>
    Integrable.fintype_prod (f := fun l (x : X) => w x * f (σ l) x * g (τ l) x)
      (fun l => h (σ l) (τ l))
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _
    (fun τ _ => (hint σ τ).const_mul _))]
  simp_rw [integral_finsetSum _ (fun τ _ => (hint _ τ).const_mul _)]
  simp_rw [integral_const_mul]
  have hp : ∀ σ τ : Equiv.Perm (Fin k),
      ∫ z : Fin k → X, ∏ l, (w (z l) * f (σ l) (z l) * g (τ l) (z l)) ∂(Measure.pi fun _ => m)
        = ∏ l, ∫ x, w x * f (σ l) x * g (τ l) x ∂m := fun σ τ =>
    integral_fintype_prod_eq_prod (f := fun l (x : X) => w x * f (σ l) x * g (τ l) x)
  simp_rw [hp]
  exact sum_sign_sign_prod (Matrix.of fun i j => ∫ z, w z * f i z * g j z ∂m)

/-- **Absolute-value Andréief bound.** -/
theorem norm_det_le_andreief {X : Type*} [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    {k : ℕ} (w : X → ℂ) (f g : Fin k → X → ℂ)
    (h : ∀ i j, Integrable (fun z => w z * f i z * g j z) m) :
    ‖(Matrix.of fun i j => ∫ z, w z * f i z * g j z ∂m).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → X, (∏ l, ‖w (z l)‖)
          * ‖(Matrix.of fun i l => f i (z l)).det‖
          * ‖(Matrix.of fun j l => g j (z l)).det‖ ∂(Measure.pi fun _ => m) := by
  have hid := andreief_identity m w f g h
  have hpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h1 : ‖(Matrix.of fun i j => ∫ z, w z * f i z * g j z ∂m).det‖
      = (1 / (k.factorial : ℝ)) * ‖∫ z : Fin k → X, (∏ l, w (z l))
          * (Matrix.of fun i l => f i (z l)).det
          * (Matrix.of fun j l => g j (z l)).det ∂(Measure.pi fun _ => m)‖ := by
    rw [hid, norm_mul]
    have : ‖(k.factorial : ℂ)‖ = (k.factorial : ℝ) := by simp
    rw [this]
    field_simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [norm_prod]

end CatalanLambda.Decay
