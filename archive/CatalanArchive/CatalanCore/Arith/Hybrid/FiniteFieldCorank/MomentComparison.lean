module
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.Moments
public import CatalanArchive.CatalanCore.Linalg.CauchyPolynomial
@[expose] public section
open Polynomial Matrix Finset
namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank
open CatalanCore.Linalg.CauchyPolynomial
variable {k : Type*} [Field k] [DecidableEq k] {K n : ℕ}

theorem compressed_eq_moment (low : Fin K → k) (hinj : Function.Injective low)
    (BX BY : k[X]) (hBX : BX.natDegree+n≤K) (hBY : BY.natDegree+n≤K)
    (s : Finset k) (eps : k → k) (hs : ∀ y∈s, ∀ a, y≠low a) (z : k) :
    (residueBasis low BY n).transpose * (cauchyGram low s eps - z • (1 : Matrix (Fin K) (Fin K) k)) *
      residueBasis low BX n =
    momentMatrix ((univ.image low) ∪ s)
      (fun y => if y∈univ.image low then -z*(BX*BY).eval y/((denom low).derivative.eval y)^2
        else eps y*(BX*BY).eval y/(denom low).eval y^2) n := by
  have hd : Disjoint (univ.image low) s := by
    apply disjoint_left.2
    intro y hy hy'
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    exact hs _ hy' a rfl
  ext i j
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [gram_high_entry low hinj BX BY hBX hBY s eps hs i j, gram_low_entry]
  unfold momentMatrix
  rw [sum_union hd]
  have hlow : (∑ y∈univ.image low,
      (if y∈univ.image low then -z*(BX*BY).eval y/((denom low).derivative.eval y)^2
       else eps y*(BX*BY).eval y/(denom low).eval y^2)*y^(i.val+j.val)) =
      -z * ∑ a, (BX.eval (low a)*BY.eval (low a)*nodeWeight low a^2)*low a^(i.val+j.val) := by
    rw [Finset.sum_image (fun a ha b hb hab => hinj hab)]
    simp only [mem_image_of_mem _ (mem_univ _), ite_true, eval_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [show nodeWeight low a = ((denom low).derivative.eval (low a))⁻¹ from
      Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ a)]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [hlow]
  have hhigh : (∑ y∈s,
      (if y∈univ.image low then -z*(BX*BY).eval y/((denom low).derivative.eval y)^2
       else eps y*(BX*BY).eval y/(denom low).eval y^2)*y^(i.val+j.val)) =
      ∑ y∈s,(eps y*BX.eval y*BY.eval y/(denom low).eval y^2)*y^(i.val+j.val) := by
    apply sum_congr rfl
    intro y hy
    have hn : y∉univ.image low := fun h => disjoint_left.1 hd h hy
    simp only [hn, ite_false, eval_mul]
    ring
  rw [hhigh]
  ring
end CatalanCore.Arith.Hybrid.FiniteFieldCorank
