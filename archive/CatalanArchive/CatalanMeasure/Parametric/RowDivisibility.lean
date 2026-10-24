module
public import CatalanMeasure.Parametric.ResidueFactorization
public import Mathlib.LinearAlgebra.Matrix.Block
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- Independent zero-residue rows save one prime factor each. -/
theorem selected_zero_rows_valuation {p n : ℕ} [hp : Fact p.Prime]
    (M : Matrix (Fin n) (Fin n) ℚ) (S : Finset (Fin n))
    (hM : ∀ i j,((M i j).den : ZMod p)≠0)
    (hzero : ∀ i ∈ S,∀ j,palindromicRatResidue p (M i j)=0)
    (hdet : M.det≠0) : (S.card:ℤ) ≤ padicValRat p M.det := by
  classical
  have hpq : (p:ℚ)≠0 :=by exact_mod_cast hp.out.ne_zero
  let D : Matrix (Fin n) (Fin n) ℚ :=diagonal (fun i => if i∈S then (p:ℚ)⁻¹ else 1)
  let B : Matrix (Fin n) (Fin n) ℚ :=D*M
  have hentry (i j) : ((B i j).den : ZMod p)≠0 :=by
    dsimp only [B,D]
    rw [diagonal_mul]
    by_cases hi : i∈S
    · rw [ite_eq_left hi,mul_comm,← div_eq_mul_inv]
      exact rational_div_prime_den_ne_zero_of_residue_zero (hM i j) (hzero i hi j)
    · simpa [hi] using hM i j
  have hD : D.det=(p:ℚ)⁻¹^S.card :=by
    simp [D,Matrix.det_diagonal,Finset.prod_ite_mem_eq]
  have hv : 0 ≤ padicValRat p B.det :=by
    simpa only [mul_zero,neg_zero] using prime_det_valuation_lower B 0 (by omega)
      (fun i j =>rational_valuation_nonneg_of_den_ne_zero (hentry i j))
  change 0 ≤ padicValRat p (D*M).det at hv
  rw [Matrix.det_mul,hD,padicValRat.mul (pow_ne_zero _ (inv_ne_zero hpq)) hdet,
    padicValRat.pow,padicValRat.inv,padicValRat.self hp.out.one_lt] at hv
  omega

/-- A determinant-one row transformation converts row residue dependencies
into a saving over the naive double-pole denominator. -/
theorem row_elimination_valuation_lower {p n : ℕ} [hp : Fact p.Prime]
    (M T : Matrix (Fin n) (Fin n) ℚ) (S : Finset (Fin n))
    (hT : T.det=1)
    (hentry : ∀ i j,(((T*((p:ℚ)^2 • M)) i j).den : ZMod p)≠0)
    (hzero : ∀ i ∈ S,∀ j,palindromicRatResidue p ((T*((p:ℚ)^2 • M)) i j)=0) :
    -((2*n-S.card:ℕ):ℤ) ≤ padicValRat p M.det := by
  have hScard : S.card ≤ n :=by
    have hh :=Finset.card_le_card (Finset.subset_univ S)
    simpa only [Finset.card_univ,Fintype.card_fin] using hh
  by_cases hdet : M.det=0
  · rw [hdet,padicValRat.zero]
    omega
  have hpq : (p:ℚ)≠0 :=by exact_mod_cast hp.out.ne_zero
  have hBdet : (T*((p:ℚ)^2 • M)).det=(p:ℚ)^(2*n)*M.det :=by
    rw [Matrix.det_mul,hT,one_mul,Matrix.det_smul,Fintype.card_fin,← pow_mul]
  have hBnonzero : (T*((p:ℚ)^2 • M)).det≠0 :=by
    rw [hBdet]
    exact mul_ne_zero (pow_ne_zero _ hpq) hdet
  have hv :=selected_zero_rows_valuation (T*((p:ℚ)^2 • M)) S hentry hzero hBnonzero
  rw [hBdet,padicValRat.mul (pow_ne_zero _ hpq) hdet,padicValRat.pow,
    padicValRat.self hp.out.one_lt] at hv
  push_cast at hv ⊢
  omega

end
end CatalanMeasure.Parametric
