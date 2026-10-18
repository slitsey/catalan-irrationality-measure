module

public import CatalanCore.Frame.Spec
public import CatalanFrames.Lambda.Frame

/-!
# `Frame.P h r = (Ppoly h).eval r` and evaluation of `Ppoly` in any `ℚ`-algebra

Generic in the frame (left to WP7 by WP0); kept here because `CatalanCore/Frame` is frozen.
-/

@[expose] public section

open Polynomial CatalanCore

namespace CatalanCore.Frame

variable (Fr : Frame)

/-- Evaluation of `Ppoly` in a commutative `ℚ`-algebra is the determinant of the evaluated matrix. -/
theorem aeval_Ppoly {K : Type} [CommRing K] [Algebra ℚ K] (h : ℕ) (x : K) :
    aeval x (Fr.Ppoly h) =
      (Matrix.of fun a b : Fin h => (if a = b then x else 0) + algebraMap ℚ K (Fr.Mn a b)).det := by
  unfold Frame.Ppoly
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases hab : a = b <;> simp [hab]

/-- **`Frame.P h r = (Ppoly h).eval r`.** -/
theorem P_eq_eval (h : ℕ) (r : ℚ) : Fr.P h r = (Fr.Ppoly h).eval r := by
  have := aeval_Ppoly Fr h r
  rw [Polynomial.coe_aeval_eq_eval] at this
  rw [this]
  unfold Frame.P Frame.M Frame.MRect
  congr 1
  ext a b
  by_cases hab : a = b <;> simp [hab]

/-- Real evaluation of `Ppoly` as the determinant of the real matrix `x I + M`. -/
theorem aeval_Ppoly_real (h : ℕ) (x : ℝ) :
    aeval x (Fr.Ppoly h) = (x • (1 : Matrix (Fin h) (Fin h) ℝ) + (Fr.M h).map (Rat.cast : ℚ → ℝ)).det := by
  rw [aeval_Ppoly]
  congr 1
  ext a b
  by_cases hab : a = b <;> simp [hab, Frame.M, Frame.MRect]

end CatalanCore.Frame

namespace CatalanFrames.Lambda

/-- `lamFrame.M h` is the legacy matrix `M0 h`. -/
theorem M_eq (h : ℕ) : lamFrame.M h = CatalanLambda.M0 h := by
  ext a b
  simp [Frame.M, Frame.MRect, CatalanLambda.M0, Mn_eq]

theorem P_eq (h : ℕ) (r : ℚ) : lamFrame.P h r = CatalanLambda.P h r := by
  unfold Frame.P CatalanLambda.P; rw [M_eq]

end CatalanFrames.Lambda
