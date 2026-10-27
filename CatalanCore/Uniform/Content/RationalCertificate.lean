module
public import CatalanCore.Uniform.Content.RowCertificate
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content
open Matrix
variable (K : Type*) [Field K]
/-- Specialize a rational source coefficient only after its individual
fixed denominator has been excluded; no Q→F_p ring map is postulated. -/
def specializeRational (q : Rat) : K := (q.num : K)/(q.den : K)

theorem rational_clear (q : Rat) (D B : Int)
    (hc : D*q.num=B*(q.den : Int)) (hd : (q.den : K)≠0) :
    (D : K)*specializeRational K q=(B : K) := by
  have hi : (D : K)*(q.num : K)=(B : K)*(q.den : K) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using congrArg (fun z : Int => (z : K)) hc
  rw [specializeRational,←mul_div_assoc]
  exact (div_eq_iff hd).mpr hi

/-- Checked integer normalization of every original rational source row. -/
theorem rational_rows_normalize {m n : Nat} (Q : Matrix (Fin m) (Fin n) Rat)
    (B : Matrix (Fin m) (Fin n) Int) (D : Fin m → Int)
    (hc : ∀ i j, D i*(Q i j).num=B i j*((Q i j).den : Int))
    (hd : ∀ i j, ((Q i j).den : K)≠0) (hD : ∀ i, (D i : K)≠0) :
    (fun i j => specializeRational K (Q i j))=
      Matrix.diagonal (fun i => (D i : K)⁻¹)*castMatrix K B := by
  ext i j
  simp only [Matrix.diagonal_mul,castMatrix]
  apply (mul_left_cancel₀ (hD i))
  rw [←mul_assoc,mul_inv_cancel₀ (hD i),one_mul]
  exact rational_clear K (Q i j) (D i) (B i j) (hc i j) (hd i j)
end CatalanCore.Uniform.Content

