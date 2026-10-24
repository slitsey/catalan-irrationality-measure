module
public import CatalanArchive.CatalanMeasure.Parametric.GapNodes
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Polynomial.Chebyshev Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

private theorem gap_den_pos {a : ℝ} (ha0 : 0<a) (ha1 : a<1) : 0<1-a^2 := by
  have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0<1+a)
  nlinarith only [hh]

def gapArgument (a : ℝ) : ℝ[X] :=
  C (2/(1-a^2))*X^2-C ((1+a^2)/(1-a^2))

def gapPolynomial (a : ℝ) (N : ℕ) : ℝ[X] :=
  (T ℝ ((9*N:ℕ):ℤ)).comp (gapArgument a)

def gapLeadingFactor (a : ℝ) (N : ℕ) : ℝ :=
  2^(9*N-1)*(2/(1-a^2))^(9*N)

theorem gap_argument_at_positive {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (9*N)) :
    (gapArgument a).eval (gapPositiveNode a N i)=CatalanMeasure.chebX (9*N) i := by
  have hs := gap_positive_node_sq ha0 ha1 N i
  have hd : 1-a^2≠0 := (gap_den_pos ha0 ha1).ne'
  simp only [gapArgument,eval_sub,eval_mul,eval_C,eval_pow,eval_X]
  rw [hs]
  field_simp
  ring

theorem gap_argument_factor {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (9*N)) :
    gapArgument a-C (CatalanMeasure.chebX (9*N) i)=
      C (2/(1-a^2))*((X-C (gapPositiveNode a N i))*(X+C (gapPositiveNode a N i))) := by
  have hs := gap_positive_node_sq ha0 ha1 N i
  have hd : 1-a^2≠0 := (gap_den_pos ha0 ha1).ne'
  have hc : (1+a^2)/(1-a^2)+CatalanMeasure.chebX (9*N) i=
      (2/(1-a^2))*(gapPositiveNode a N i)^2 := by
    rw [hs]; field_simp; ring
  unfold gapArgument
  rw [sub_sub,← map_add, hc]
  simp only [map_mul,map_pow]
  ring

theorem gap_pair_product (a : ℝ) (N : ℕ) :
    (∏ i : Fin (9*N), (X-C (gapPositiveNode a N i))*(X+C (gapPositiveNode a N i)))=
      ∏ i : Fin (18*N), (X-C (gapNodes a N i)) := by
  rw [← (gapIndex N).prod_comp]
  rw [Fintype.prod_sum_type,Finset.prod_mul_distrib]
  apply congrArg₂ (· * ·)
  · apply prod_congr rfl
    intro i _
    simp [gapNodes]
  · apply prod_congr rfl
    intro i _
    simp [gapNodes]

theorem gap_polynomial_eq_nodal {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    {N : ℕ} (hN : 0<N) :
    gapPolynomial a N=C (gapLeadingFactor a N)*
      ∏ i : Fin (18*N), (X-C (gapNodes a N i)) := by
  unfold gapPolynomial
  rw [CatalanMeasure.T_eq_nodal (show 0<9*N by omega),C_mul_comp,Polynomial.prod_comp]
  simp only [sub_comp,X_comp,C_comp]
  simp_rw [gap_argument_factor ha0 ha1 N]
  rw [Finset.prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,← map_pow,
    gap_pair_product,← mul_assoc,← map_mul]
  rfl

theorem gap_leading_factor_pos {a : ℝ} (ha0 : 0<a) (ha1 : a<1) (N : ℕ) :
    0<gapLeadingFactor a N := by
  have hd := gap_den_pos ha0 ha1
  unfold gapLeadingFactor
  positivity

end
end CatalanMeasure.Parametric
