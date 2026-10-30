module
public import CatalanCore.Uniform.Content.StreamCertificate
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content
open Matrix
/-- Row-wise denominator clearing avoids taking one enormous lcm over all
source covectors. Every surviving row unit is explicit in the source adapter. -/
theorem row_cleared_image_rank_le (K : Type*) [Field K] {m n d r : Nat}
    (B : Matrix (Fin m) (Fin n) Int) (V : Matrix (Fin n) (Fin d) Int)
    (C : Matrix (Fin m) (Fin r) Int) (T : Matrix (Fin r) (Fin d) Int)
    (A : Matrix (Fin m) (Fin n) K) (D : Matrix (Fin m) (Fin m) K)
    (hA : A=D*castMatrix K B) (h : B*V=C*T) : (A*castMatrix K V).rank≤r := by
  have hf : A*castMatrix K V=(D*castMatrix K C)*castMatrix K T := by
    rw [hA,Matrix.mul_assoc,←castMatrix_mul,h,castMatrix_mul,←Matrix.mul_assoc]
  rw [hf]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
end CatalanCore.Uniform.Content
