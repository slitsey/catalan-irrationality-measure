module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial
noncomputable section

theorem polynomial_derivative_affine_identity (p H : ℂ[X]) (a b scale : ℂ)
    (heval : ∀ z : ℂ, p.eval z = H.eval (a * z + b) / scale) (z : ℂ) :
    p.derivative.eval z = (a / scale) * H.derivative.eval (a * z + b) := by
  have hh : HasDerivAt (fun w : ℂ => H.eval (a * w + b) / scale)
      (H.derivative.eval (a * z + b) * a / scale) z := by
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (((H.hasDerivAt (a * z + b)).comp z (((hasDerivAt_id z).const_mul a).add_const b)).div_const scale)
  have hf : (fun w : ℂ => H.eval (a * w + b) / scale) = p.eval :=
    funext (fun w => (heval w).symm)
  rw [hf] at hh
  have hd := (p.hasDerivAt z).unique hh
  exact hd.trans (by ring)

theorem polynomial_derivative_affine_norm_le (p H : ℂ[X]) (a b scale : ℂ)
    (heval : ∀ z : ℂ, p.eval z = H.eval (a * z + b) / scale)
    (z : ℂ) {M : ℝ} (hM : ‖H.derivative.eval (a * z + b)‖ ≤ M) :
    ‖p.derivative.eval z‖ ≤ (‖a‖ / ‖scale‖) * M := by
  rw [polynomial_derivative_affine_identity p H a b scale heval z, norm_mul, norm_div]
  exact mul_le_mul_of_nonneg_left hM (by positivity)

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.polynomial_derivative_affine_identity
#print axioms CatalanMeasure.GenD.Analytic.polynomial_derivative_affine_norm_le
