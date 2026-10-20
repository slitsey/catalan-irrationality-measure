module
public import CatalanCore.Arith.Hybrid.LemmaE.ModelPartners
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
namespace Cng
lemma mul_left_integral {a f g : ℚ[X]} (ha : Int1 p a) (h : Cng p f g) :
    Cng p (a*f) (a*g) := by
  unfold Cng at *
  rw [← mul_sub, gn_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (gn_nonneg p _) ha) h
lemma cancel_primitive {a f g : ℚ[X]} (ha : gn p a=1) :
    Cng p (a*f) (a*g) ↔ Cng p f g := by
  unfold Cng
  rw [← mul_sub, gn_mul, ha, one_mul]
end Cng
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma col_cng_of_mul (M : Matrix I I ℚ[X])
    (hM : ∀ i j, Int1 p (M i j)) (hd : gn p M.det=1)
    (v w : I → ℚ[X]) (h : ∀ i, Cng p ((M*ᵥv) i) ((M*ᵥw) i)) :
    ∀ i, Cng p (v i) (w i) := by
  intro i
  have H : Cng p ((M.adjugate*ᵥ(M*ᵥv)) i) ((M.adjugate*ᵥ(M*ᵥw)) i) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Cng.sum (fun j _ => (h j).mul_left_integral (adj_int1 hM i j))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul] at H
  have H' : Cng p (M.det * v i) (M.det * w i) := by simpa [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply] using H
  exact (Cng.cancel_primitive hd).mp H'
lemma row_cng_of_mul (M : Matrix I I ℚ[X])
    (hM : ∀ i j, Int1 p (M i j)) (hd : gn p M.det=1)
    (v w : I → ℚ[X]) (h : ∀ i, Cng p ((v ᵥ* M) i) ((w ᵥ* M) i)) :
    ∀ i, Cng p (v i) (w i) := by
  apply col_cng_of_mul M.transpose (fun i j => hM j i) (by simpa using hd) v w
  simpa only [Matrix.mulVec_transpose] using h
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.row_cng_of_mul
