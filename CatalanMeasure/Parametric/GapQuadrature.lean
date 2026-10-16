module
public import CatalanMeasure.Parametric.GapNodal
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Polynomial.Chebyshev Finset OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem cheb_derivative_eval_ge {J : ℕ} (i : Fin J) :
    (J:ℝ) ≤ |(derivative (T ℝ (J:ℤ))).eval (CatalanMeasure.chebX J i)| := by
  have hJ : 0<J := by have := i.isLt; omega
  have hd := chebX_den_ge i
  have he := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := (univ:Finset (Fin J))) (v := CatalanMeasure.chebX J) (mem_univ i)
  rw [Lagrange.eval_nodal] at he
  rw [CatalanMeasure.T_eq_nodal hJ,derivative_C_mul,eval_mul,eval_C]
  rw [Lagrange.nodal_eq] at he
  rw [he,abs_mul,abs_of_pos (by positivity : (0:ℝ)<2^(J-1))]
  have hp : (0:ℝ)<2^(J-1) := by positivity
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hd

theorem gap_argument_at_node {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (18*N)) :
    ∃ j : Fin (9*N), (gapArgument a).eval (gapNodes a N i)=CatalanMeasure.chebX (9*N) j := by
  simp only [gapNodes,Function.comp_apply]
  cases h : (gapIndex N).symm i with
  | inl j => exact ⟨j,gap_argument_at_positive ha0 ha1 N j⟩
  | inr j =>
    refine ⟨j,?_⟩
    simpa only [Sum.elim_inr,gapArgument,eval_sub,eval_mul,eval_C,eval_pow,eval_X,neg_sq]
      using gap_argument_at_positive ha0 ha1 N j

theorem gap_polynomial_derivative_ge {a : ℝ} (ha0 : 0<a) (ha1 : a<1)
    (N : ℕ) (i : Fin (18*N)) :
    36*N*a/(1-a^2) ≤ |(derivative (gapPolynomial a N)).eval (gapNodes a N i)| := by
  have hd : 0<1-a^2 := by
    have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0<1+a)
    nlinarith only [hh]
  obtain ⟨j,hj⟩ := gap_argument_at_node ha0 ha1 N i
  have hT := cheb_derivative_eval_ge j
  have hn := (gap_nodes_bounds ha0 ha1 N i).2.le
  have he : (derivative (gapArgument a)).eval (gapNodes a N i)=
      4*gapNodes a N i/(1-a^2) := by
    simp [gapArgument,derivative_mul,derivative_pow]; ring
  rw [gapPolynomial,derivative_comp,eval_mul,eval_comp,hj,he,
    abs_mul,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4),abs_of_pos hd]
  calc
    _ = (4*a/(1-a^2))*(9*N:ℕ) := by push_cast; ring
    _ ≤ (4*|gapNodes a N i|/(1-a^2))*
        |(derivative (T ℝ ((9*N:ℕ):ℤ))).eval (CatalanMeasure.chebX (9*N) j)| :=
      mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hd.le)
        hT (by positivity) (by positivity)

/-- A cardinal polynomial times its nodal derivative and linear denominator
recovers any nonzero scalar multiple of the full nodal polynomial. -/
theorem quad_basis_mul_derivative_eq {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (i : Fin J) {P : ℝ[X]} {c : ℝ}
    (hP : P=C c*∏ j : Fin J, (X-C (τ j))) :
    quadBasis τ i*C ((derivative P).eval (τ i))*(X-C (τ i))=P := by
  classical
  let D : ℝ := ∏ j ∈ univ.erase i, (τ i-τ j)
  have hD : D≠0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (mem_erase.mp hj).1 (hτ h).symm)
  have he := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := (univ:Finset (Fin J))) (v := τ) (mem_univ i)
  rw [Lagrange.eval_nodal,Lagrange.nodal_eq] at he
  have hder : (derivative P).eval (τ i)=c*D := by
    rw [hP,derivative_C_mul,eval_mul,eval_C,he]
  rw [quadBasis_eq,hder,hP,prod_inv_distrib]
  change (C D⁻¹ * (∏ j ∈ univ.erase i, (X-C (τ j)))) * C (c*D) * (X-C (τ i))=_
  calc
    _ = C (D⁻¹*(c*D)) * ((∏ j ∈ univ.erase i, (X-C (τ j))) * (X-C (τ i))) := by
      simp only [map_mul]; ring
    _ = _ := by
      rw [show D⁻¹*(c*D)=c by field_simp]
      rw [prod_erase_mul _ _ (mem_univ i)]

theorem norm_cardinal_le_of_nodal {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (hmem : ∀ j, τ j ∈ Set.Ioo (-1:ℝ) 1)
    (i : Fin J) {P : ℝ[X]} {c d radius : ℝ}
    (hP : P=C c*∏ j : Fin J, (X-C (τ j)))
    (hd : 0<d) (hder : d ≤ |(derivative P).eval (τ i)|)
    (hr : 1<radius) (z : ℂ) (hz : ‖z‖=radius) :
    ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      ‖(P.map (algebraMap ℝ ℂ)).eval z‖/(d*(radius-1)) := by
  have he := congrArg (fun Q : ℝ[X] => (Q.map (algebraMap ℝ ℂ)).eval z)
    (quad_basis_mul_derivative_eq hτ i hP)
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_sub,Polynomial.map_X,
    eval_mul,eval_C,eval_sub,eval_X,Complex.coe_algebraMap] at he
  have hn := congrArg norm he
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  have hdist : radius-1 ≤ ‖z-(τ i:ℂ)‖ := by
    have hh := norm_sub_norm_le z (τ i:ℂ)
    rw [hz,Complex.norm_real,Real.norm_eq_abs] at hh
    have hi := abs_lt.mpr (hmem i)
    linarith only [hh,hi]
  apply (le_div_iff₀ (mul_pos hd (sub_pos.mpr hr))).mpr
  calc
    _ ≤ ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ *
        |(derivative P).eval (τ i)| * ‖z-(τ i:ℂ)‖ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hder hdist (sub_pos.mpr hr).le (abs_nonneg _)) (norm_nonneg _)
    _ = _ := hn

end
end CatalanMeasure.Parametric
