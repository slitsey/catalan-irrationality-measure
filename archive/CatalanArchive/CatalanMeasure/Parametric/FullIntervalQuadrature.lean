module

public import CatalanMeasure.Parametric.RadiusQuadrature
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCircle

/-!
# Full-interval Chebyshev interpolation

Uniform circle bounds for interpolation on the original roots of T_J.
These are polynomial P-only interpolation statements, not statements about
the actual mixed-sheet determinant.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Polynomial.Chebyshev Finset

noncomputable section

theorem chebX_den_ge {J : ℕ} (a : Fin J) :
    (J : ℝ) / 2 ^ (J - 1) ≤
      |∏ c ∈ univ.erase a, (CatalanMeasure.chebX J a - CatalanMeasure.chebX J c)| := by
  have h := CatalanMeasure.chebNode_den_ge a
  have he : (∏ c ∈ univ.erase a,
      (CatalanMeasure.chebNode J a - CatalanMeasure.chebNode J c)) =
      (∏ c ∈ univ.erase a,
        (CatalanMeasure.chebX J a - CatalanMeasure.chebX J c)) / 2 ^ (J - 1) := by
    rw [eq_div_iff (by positivity)]
    have hcard : (univ.erase a).card = J - 1 := by simp
    rw [← hcard, ← prod_const (2 : ℝ), ← prod_mul_distrib]
    apply prod_congr rfl
    intro c _
    simp only [CatalanMeasure.chebNode]
    ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (J - 1))] at h
  have h2 : (0 : ℝ) < 2 ^ (J - 1) := by positivity
  rw [← div_div, div_le_div_iff_of_pos_right h2] at h
  exact h

theorem chebX_nodal_eval_complex {J : ℕ} (hJ : 0 < J) (z : ℂ) :
    ∏ c : Fin J, (z - (CatalanMeasure.chebX J c : ℂ)) =
      (T ℂ (J : ℤ)).eval z / 2 ^ (J - 1) := by
  have hT : T ℂ (J : ℤ) = C ((2 : ℂ) ^ (J - 1)) *
      ∏ c : Fin J, (X - C ((CatalanMeasure.chebX J c : ℝ) : ℂ)) := by
    rw [← Chebyshev.map_T (algebraMap ℝ ℂ), CatalanMeasure.T_eq_nodal hJ,
      Polynomial.map_mul, Polynomial.map_prod]
    simp
  rw [hT, eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  field_simp

theorem norm_full_quadBasis_eval_radius_le {J : ℕ} (a : Fin J) (z : ℂ) {radius : ℝ}
    (hr : 1 < radius) (hz : ‖z‖ = radius) :
    ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebX J) a).map
      (algebraMap ℝ ℂ)).eval z‖ ≤
      ‖(T ℂ (J : ℤ)).eval z‖ / (J * (radius - 1)) := by
  have hJ : 0 < J := by have := a.isLt; omega
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [OAI.InternalCatalan.quadBasis_eq, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_prod, eval_mul, eval_C, eval_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    eval_sub, eval_X, eval_C]
  set D := ∏ c ∈ univ.erase a,
    (CatalanMeasure.chebX J a - CatalanMeasure.chebX J c) with hD
  have hDge := chebX_den_ge a
  have hD0 : 0 < |D| := lt_of_lt_of_le (by positivity) hDge
  have hnode : |CatalanMeasure.chebX J a| < 1 :=
    abs_lt.mpr (CatalanMeasure.chebX_mem a)
  have hdist : radius - 1 ≤ ‖z - (CatalanMeasure.chebX J a : ℂ)‖ := by
    have hh := norm_sub_norm_le z (CatalanMeasure.chebX J a : ℂ)
    rw [hz, Complex.norm_real, Real.norm_eq_abs] at hh
    linarith
  have hdpos : 0 < ‖z - (CatalanMeasure.chebX J a : ℂ)‖ :=
    lt_of_lt_of_le (sub_pos.mpr hr) hdist
  have hfull := chebX_nodal_eval_complex hJ z
  rw [← Finset.prod_erase_mul _ _ (mem_univ a)] at hfull
  have hmap : (algebraMap ℝ ℂ) (∏ c ∈ univ.erase a,
      (CatalanMeasure.chebX J a - CatalanMeasure.chebX J c)⁻¹) =
      ((D⁻¹ : ℝ) : ℂ) := by rw [hD, ← prod_inv_distrib]; simp
  rw [hmap, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
  have hprod : ‖∏ c ∈ univ.erase a, (z - (CatalanMeasure.chebX J c : ℂ))‖ =
      ‖(T ℂ (J : ℤ)).eval z‖ / 2 ^ (J - 1) /
      ‖z - (CatalanMeasure.chebX J a : ℂ)‖ := by
    have hh := congrArg norm hfull
    rw [norm_mul, norm_div, norm_pow, Complex.norm_ofNat] at hh
    rw [eq_div_iff hdpos.ne', hh]
  simp only [Complex.coe_algebraMap]
  rw [hprod]
  have hinvD : |D|⁻¹ ≤ 2 ^ (J - 1) / J := by
    rw [inv_le_comm₀ hD0 (by positivity), inv_div]
    exact hDge
  have hinvd : ‖z - (CatalanMeasure.chebX J a : ℂ)‖⁻¹ ≤ (radius - 1)⁻¹ :=
    (inv_le_inv₀ hdpos (sub_pos.mpr hr)).mpr hdist
  calc
    _ = |D|⁻¹ * ‖z - (CatalanMeasure.chebX J a : ℂ)‖⁻¹ *
        (‖(T ℂ (J : ℤ)).eval z‖ / 2 ^ (J - 1)) := by ring
    _ ≤ (2 ^ (J - 1) / J) * (radius - 1)⁻¹ *
        (‖(T ℂ (J : ℤ)).eval z‖ / 2 ^ (J - 1)) := by gcongr
    _ = ‖(T ℂ (J : ℤ)).eval z‖ / (J * (radius - 1)) := by field_simp

theorem norm_T_twenty_radius_le (J : ℕ) (z : ℂ)
    (hz : ‖z‖ = (TwentyCircle.twentyRadius : ℝ)) :
    ‖(T ℂ (J : ℤ)).eval z‖ ≤ (5 / 2 : ℝ) ^ J := by
  set a := ‖z - 1‖
  set b := ‖z + 1‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hpar := parallelogram_law_with_norm ℝ z (1 : ℂ)
  rw [hz, norm_one] at hpar
  have hs : ((a + b) / 2) ^ 2 ≤ (TwentyCircle.twentyRadius : ℝ) ^ 2 + 1 := by
    dsimp [a, b]
    nlinarith [sq_nonneg (a - b)]
  have hhalf : (a + b) / 2 ≤ (149 / 100 : ℝ) := by
    norm_num [TwentyCircle.twentyRadius] at hs
    nlinarith
  have hroot : Real.sqrt (((a + b) / 2) ^ 2 - 1) ≤ (101 / 100 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num [TwentyCircle.twentyRadius] at hs
    linarith
  exact (CatalanMeasure.norm_T_eval_le J z).trans
    (pow_le_pow_left₀ (by positivity) (by change (a + b) / 2 + _ ≤ _; linarith) J)

theorem twenty_full_filtered_basis_le (N : ℕ) (a : Fin (18 * N)) (z : ℂ)
    (hz : ‖z‖ = (TwentyCircle.twentyRadius : ℝ)) :
    ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebX (18 * N)) a *
      (1 - X) ^ (2 * N)).map (algebraMap ℝ ℂ)).eval z‖ ≤
      1000 * (60000000 : ℝ) ^ N := by
  have hN : 0 < N := by have := a.isLt; omega
  have hJR : (1 : ℝ) ≤ (18 * N : ℕ) := by exact_mod_cast (show 1 ≤ 18 * N by omega)
  have hb := norm_full_quadBasis_eval_radius_le a z
    (by norm_num [TwentyCircle.twentyRadius]) hz
  have hT := norm_T_twenty_radius_le (18 * N) z hz
  have hl : ‖((OAI.InternalCatalan.quadBasis (CatalanMeasure.chebX (18 * N)) a).map
      (algebraMap ℝ ℂ)).eval z‖ ≤ 1000 * (5 / 2 : ℝ) ^ (18 * N) := by
    apply hb.trans
    have hd : (0 : ℝ) < (18 * N : ℕ) *
        ((TwentyCircle.twentyRadius : ℝ) - 1) :=
      mul_pos (by exact_mod_cast (show 0 < 18 * N by omega))
        (by norm_num [TwentyCircle.twentyRadius])
    apply (div_le_iff₀ hd).mpr
    have he : 1000 * ((18 * N : ℕ) * ((TwentyCircle.twentyRadius : ℝ) - 1)) =
        (18 * N : ℕ) := by norm_num [TwentyCircle.twentyRadius]; ring
    calc
      _ ≤ (5 / 2 : ℝ) ^ (18 * N) := hT
      _ ≤ (18 * N : ℕ) * (5 / 2 : ℝ) ^ (18 * N) :=
        le_mul_of_one_le_left (by positivity) hJR
      _ = _ := by norm_num [TwentyCircle.twentyRadius]; ring
  have hm : ‖(1 : ℂ) - z‖ ≤ (2001 / 1000 : ℝ) := by
    have hh := norm_sub_le (1 : ℂ) z
    rw [norm_one, hz] at hh
    norm_num [TwentyCircle.twentyRadius] at hh ⊢
    exact hh
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, eval_mul, eval_pow, eval_sub, eval_one, eval_X, norm_mul, norm_pow]
  calc
    _ ≤ (1000 * (5 / 2 : ℝ) ^ (18 * N)) * (2001 / 1000 : ℝ) ^ (2 * N) := by
      exact mul_le_mul hl (pow_le_pow_left₀ (by positivity) hm _) (by positivity) (by positivity)
    _ = 1000 * ((5 / 2 : ℝ) ^ 18 * (2001 / 1000 : ℝ) ^ 2) ^ N := by
      rw [mul_pow, pow_mul, pow_mul]; ring
    _ ≤ 1000 * (60000000 : ℝ) ^ N := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_left₀ (by positivity)
      norm_num

theorem fullIntervalCircleK_le_exp : (60000000 : ℝ) ≤ Real.exp 18 := by
  have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  rw [show (18 : ℝ) = (18 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  exact (by norm_num : (60000000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 18).trans
    (pow_le_pow_left₀ (by norm_num) he 18)

end

end CatalanMeasure.Parametric
