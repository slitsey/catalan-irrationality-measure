module
public import CatalanCore.Arith.Hybrid.LemmaE.PrimitiveSolve
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma vecMul_restrict (M : Matrix I I ℚ[X]) (v : I→ℚ[X]) (e : J→I)
    (he : Function.Injective e) (hv : ∀i, i∉Set.range e→v i=0) (j : J) :
    ((v ∘ e) ᵥ* M.submatrix e e) j = (v ᵥ* M) (e j) := by
  apply Fintype.sum_of_injective e he
  · intro i hi
    simp only [hv i hi, zero_mul]
  · intro i
    rfl

lemma mulVec_restrict (M : Matrix I I ℚ[X]) (v : I→ℚ[X]) (e : J→I)
    (he : Function.Injective e) (hv : ∀i, i∉Set.range e→v i=0) (j : J) :
    (M.submatrix e e *ᵥ (v ∘ e)) j = (M *ᵥ v) (e j) := by
  apply Fintype.sum_of_injective e he
  · intro i hi
    simp only [hv i hi, mul_zero]
  · intro i
    rfl

/-- Primitive chain equations identify partners even when their two leading matrices differ
by integral coefficient congruences. -/
theorem row_partners_cng (M N : Matrix J J ℚ[X])
    (hM : ∀i j,Int1 p (M i j)) (hd : gn p M.det=1)
    (v w : J→ℚ[X]) (hw : ∀i,Int1 p (w i))
    (hMN : ∀i j,Cng p (N i j) (M i j))
    (hsource : ∀i,Cng p ((v ᵥ* M) i) ((w ᵥ* N) i)) :
    ∀i,Cng p (v i) (w i) := by
  apply row_cng_of_mul M hM hd v w
  intro i
  apply (hsource i).trans
  simp only [Matrix.vecMul, dotProduct]
  exact Cng.sum (fun j _ => (hMN j i).mul_left_integral (hw j))

end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.row_partners_cng
