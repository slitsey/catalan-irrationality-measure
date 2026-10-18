module

public import CatalanLambda.Decay.RayFTC
public import CatalanLambda.Decay.Contour
public import CatalanLambda.Mirror.Reflect

@[expose] public section

/-!
# Mirror constant: the contour identity

For `N0 ≥ 1`, `x* = -N0 + 3/8` (the midpoint of the gap `(-N0, -N0 + 3/4)` between the poles of `Ē`),
`φ ∈ (π/2, π)` and `Γ` the two rays `x* + r e^{±iφ}` traversed downward,
`16 · T̄_{ab} = - ∑_{m < N0} atomTermB a b m - u_{N0}(a) u_{N0}(b) + (1/2πi) ∫_Γ Ē (z-a)⁻¹ (z-b)⁻¹ dz`.
(The term `e_{-N0}` straddles `x*`; its west pole contributes `u_{N0}(a) u_{N0}(b)`.)
-/

open Complex MeasureTheory Filter Topology Set

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (g3 contL_sub_g3 rayI rayPt contL kap2 kap2_pos rayPt_sub_ne
  norm_inv_rayPt_le integrableOn_invsq contL_tri_east contL_tri_west
  rayI_add_smul phiC phiC_gt phiC_lt)

/-- The vertex `x* = -N0 + 3/8`. -/
noncomputable def xstarB (N0 : ℕ) : ℝ := -(N0 : ℝ) + 3 / 8

lemma etermB_eq_g3 (n : ℤ) (a b : ℕ) (z : ℂ) :
    etermB z n * ((z - a)⁻¹ * (z - b)⁻¹)
      = g3 ((n : ℝ) + 3 / 4) a b z - g3 (n : ℝ) a b z := by
  unfold etermB g3
  push_cast
  simp only [one_div]
  ring

/-- Both poles of `e_n` to the right of `x*` (`n ≥ -N0 + 1`): no contribution. -/
theorem contL_etermB_east_gen {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (N0 a b : ℕ) (hN : 1 ≤ N0) (n : ℤ) (hn : -(N0 : ℤ) + 1 ≤ n) :
    contL (xstarB N0) φ (fun z => etermB z n * ((z - a)⁻¹ * (z - b)⁻¹)) = 0 := by
  have hn' : -(N0 : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hN' : (1 : ℝ) ≤ N0 := by exact_mod_cast hN
  have hx : xstarB N0 = -(N0 : ℝ) + 3 / 8 := rfl
  have hfun : (fun z : ℂ => etermB z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((n : ℝ) + 3 / 4) a b z - g3 (n : ℝ) a b z := by
    funext z; exact etermB_eq_g3 n a b z
  rw [hfun, contL_sub_g3 _ _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_east _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_east _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  ring

/-- Both poles of `e_{-(m+1)}` to the left of `x*` (`m ≥ N0`): the atom term. -/
theorem contL_etermB_west_gen {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (N0 a b m : ℕ) (hN : 1 ≤ N0) (hm : N0 ≤ m) :
    contL (xstarB N0) φ (fun z => etermB z (-((m : ℤ) + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = -(2 * Real.pi * I) * (atomTermB a b m : ℝ) := by
  have hm' : (N0 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hN' : (1 : ℝ) ≤ N0 := by exact_mod_cast hN
  have hx : xstarB N0 = -(N0 : ℝ) + 3 / 8 := rfl
  have hfun : (fun z : ℂ => etermB z (-((m : ℤ) + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((((-((m : ℤ) + 1) : ℤ)) : ℝ) + 3 / 4) a b z
          - g3 ((((-((m : ℤ) + 1) : ℤ)) : ℝ)) a b z := by
    funext z; exact etermB_eq_g3 _ a b z
  have e1 : ((((-((m : ℤ) + 1) : ℤ)) : ℝ)) = -(m : ℝ) - 1 := by push_cast; ring
  rw [hfun, e1]
  rw [contL_sub_g3 _ _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_west _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_west _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  have hR : (1 / (((-(m : ℝ) - 1 + 3 / 4) - a) * ((-(m : ℝ) - 1 + 3 / 4) - b))
      - 1 / (((-(m : ℝ) - 1) - a) * ((-(m : ℝ) - 1) - b))) = atomTermB a b m := by
    have e1 : (-(m : ℝ) - 1 + 3 / 4 - a) * (-(m : ℝ) - 1 + 3 / 4 - b)
        = ((a : ℝ) + m + 1 / 4) * ((b : ℝ) + m + 1 / 4) := by ring
    have e2 : (-(m : ℝ) - 1 - a) * (-(m : ℝ) - 1 - b) = ((a : ℝ) + m + 1) * ((b : ℝ) + m + 1) := by ring
    rw [e1, e2, atomTermB_eq]
  have key := congrArg (fun t : ℝ => (t : ℂ)) hR
  push_cast at key ⊢
  linear_combination (-(2 * (Real.pi : ℂ) * I)) * key

/-- The straddling term `e_{-N0}`: east pole `-N0 + 3/4`, west pole `-N0`. -/
theorem contL_etermB_mid_gen {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (N0 a b : ℕ) (hN : 1 ≤ N0) :
    contL (xstarB N0) φ (fun z => etermB z (-(N0 : ℤ)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = (2 * Real.pi * I) * ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hN' : (1 : ℝ) ≤ N0 := by exact_mod_cast hN
  have hx : xstarB N0 = -(N0 : ℝ) + 3 / 8 := rfl
  have hfun : (fun z : ℂ => etermB z (-(N0 : ℤ)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((((-(N0 : ℤ)) : ℤ) : ℝ) + 3 / 4) a b z
          - g3 ((((-(N0 : ℤ)) : ℤ) : ℝ)) a b z := by
    funext z; exact etermB_eq_g3 _ a b z
  have e1 : ((((-(N0 : ℤ)) : ℤ) : ℝ)) = -(N0 : ℝ) := by push_cast; ring
  rw [hfun, e1]
  rw [contL_sub_g3 _ _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_east _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_west _ _ _ _ _ hφ1 hφ2 (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  have hR : (1 / (((-(N0 : ℝ)) - a) * ((-(N0 : ℝ)) - b))) = 1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) := by
    have e2 : (-(N0 : ℝ) - a) * (-(N0 : ℝ) - b) = ((a : ℝ) + N0) * ((b : ℝ) + N0) := by ring
    rw [e2]
  have key := congrArg (fun t : ℝ => (t : ℂ)) hR
  push_cast at key ⊢
  linear_combination (-(-(2 * (Real.pi : ℂ) * I))) * key

lemma xstarB_ne_int (N0 : ℕ) (n : ℤ) : (n : ℝ) ≠ xstarB N0 := by
  intro h
  have h8 : (8 * (n : ℝ)) = -8 * (N0 : ℝ) + 3 := by unfold xstarB at h; linarith
  have : (8 * n : ℤ) = -8 * (N0 : ℤ) + 3 := by exact_mod_cast h8
  omega

lemma xstarB_ne_int_add (N0 : ℕ) (n : ℤ) : (n : ℝ) + 3 / 4 ≠ xstarB N0 := by
  intro h
  have h8 : (8 * (n : ℝ)) = -8 * (N0 : ℝ) - 3 := by unfold xstarB at h; linarith
  have : (8 * n : ℤ) = -8 * (N0 : ℤ) - 3 := by exact_mod_cast h8
  omega

lemma etermB_eq_mul (z : ℂ) (n : ℤ) (h1 : z - (((n : ℝ) + 3 / 4 : ℝ) : ℂ) ≠ 0)
    (h0 : z - ((n : ℝ) : ℂ) ≠ 0) :
    etermB z n = (3 / 4 : ℂ) * ((z - (((n : ℝ) + 3 / 4 : ℝ) : ℂ))⁻¹ * (z - ((n : ℝ) : ℂ))⁻¹) := by
  unfold etermB
  push_cast at h1 h0 ⊢
  have h1' : z - (n : ℂ) - 3 / 4 ≠ 0 := by
    intro h; apply h1; linear_combination h
  have h0' : z - (n : ℂ) ≠ 0 := h0
  have h1'' : z - ((n : ℂ) + 3 / 4) ≠ 0 := h1
  have e : z - (n : ℂ) - 3 / 4 = z - ((n : ℂ) + 3 / 4) := by ring
  rw [e]
  have hBA : z - (n : ℂ) = (z - ((n : ℂ) + 3 / 4)) + 3 / 4 := by ring
  generalize z - ((n : ℂ) + 3 / 4) = A at *
  generalize z - (n : ℂ) = B at *
  subst hBA
  simp only [one_div] at *
  rw [inv_sub_inv h1'' h0, div_eq_mul_inv, mul_inv]
  ring

lemma norm_etermB_ray_le (N0 : ℕ) (n : ℤ) {θ r : ℝ} (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖etermB (rayPt (xstarB N0) θ r) n‖ ≤ ‖etermB ((xstarB N0 : ℝ) : ℂ) n‖ / Real.sqrt (kap2 θ) ^ 2 := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  set x := xstarB N0
  have hq1 := xstarB_ne_int_add N0 n
  have hq0 := xstarB_ne_int N0 n
  have d1 : 0 < |x - ((n : ℝ) + 3 / 4)| := abs_pos.2 (sub_ne_zero.2 hq1.symm)
  have d0 : 0 < |x - (n : ℝ)| := abs_pos.2 (sub_ne_zero.2 hq0.symm)
  rw [etermB_eq_mul _ n (rayPt_sub_ne hq1 hs hr) (rayPt_sub_ne hq0 hs hr)]
  have hx1 : ((x : ℝ) : ℂ) - (((n : ℝ) + 3 / 4 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.2 hq1.symm
  have hx0 : ((x : ℝ) : ℂ) - ((n : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.2 hq0.symm
  rw [etermB_eq_mul _ n hx1 hx0]
  simp only [norm_mul, norm_inv]
  have e1 : ‖((x : ℝ) : ℂ) - (((n : ℝ) + 3 / 4 : ℝ) : ℂ)‖ = |x - ((n : ℝ) + 3 / 4)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have e0 : ‖((x : ℝ) : ℂ) - ((n : ℝ) : ℂ)‖ = |x - (n : ℝ)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e1, e0]
  have h1 := norm_inv_rayPt_le (x := x) (θ := θ) ((n : ℝ) + 3 / 4) hq1 hs hr
  have h0 := norm_inv_rayPt_le (x := x) (θ := θ) (n : ℝ) hq0 hs hr
  simp only [norm_inv] at h1 h0
  have hb1 : 1 / (K * (|x - ((n : ℝ) + 3 / 4)| + r)) ≤ 1 / (K * |x - ((n : ℝ) + 3 / 4)|) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hb0 : 1 / (K * (|x - (n : ℝ)| + r)) ≤ 1 / (K * |x - (n : ℝ)|) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h1' := h1.trans hb1
  have h0' := h0.trans hb0
  have n4 : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by simp
  rw [n4]
  have := mul_le_mul h1' h0' (by positivity) (by positivity)
  calc 3 / 4 * (‖(rayPt x θ r - (((n : ℝ) + 3 / 4 : ℝ) : ℂ))‖⁻¹ * ‖(rayPt x θ r - ((n : ℝ) : ℂ))‖⁻¹)
      ≤ 3 / 4 * ((1 / (K * |x - ((n : ℝ) + 3 / 4)|)) * (1 / (K * |x - (n : ℝ)|))) := by gcongr
    _ = 3 / 4 * (|x - ((n : ℝ) + 3 / 4)|⁻¹ * |x - (n : ℝ)|⁻¹) / K ^ 2 := by
        field_simp

lemma xstarB_ne_nat (N0 a : ℕ) (hN : 1 ≤ N0) : (a : ℝ) ≠ xstarB N0 := by
  unfold xstarB
  have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : (1 : ℝ) ≤ N0 := by exact_mod_cast hN
  intro h; linarith

lemma three_eighths_leB (N0 a : ℕ) (hN : 1 ≤ N0) : (3 / 8 : ℝ) ≤ |xstarB N0 - a| := by
  unfold xstarB
  have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : (1 : ℝ) ≤ N0 := by exact_mod_cast hN
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

lemma norm_inv_ray_nat_leB (N0 a : ℕ) (hN : 1 ≤ N0) {θ r : ℝ} (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖(rayPt (xstarB N0) θ r - (a : ℝ))⁻¹‖ ≤ 1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  refine (norm_inv_rayPt_le (a : ℝ) (xstarB_ne_nat N0 a hN) hs hr).trans ?_
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [three_eighths_leB N0 a hN])

/-- **Interchange of sum and ray integral**: `∑_n ∫_ray e_n v_a v_b = ∫_ray Ē v_a v_b`. -/
theorem rayI_E_hasSumB (N0 a b : ℕ) (hN : 1 ≤ N0) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI (xstarB N0) θ (fun z => etermB z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI (xstarB N0) θ (fun z => ECB z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := xstarB N0 with hxdef
  have hsum : Summable (fun n : ℤ => ‖etermB (x : ℂ) n‖ / K ^ 2) :=
    (summable_norm_iff.2 (summable_etermB (x : ℂ))).div_const _
  unfold rayI
  refine hasSum_integral_of_dominated_convergence
    (fun n r => (‖etermB (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2))) ?_ ?_ ?_ ?_ ?_
  · intro n
    unfold rayPt etermB
    exact (by fun_prop : Measurable fun r : ℝ =>
      ((1 / (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (n : ℂ) - 3 / 4)
        - 1 / (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (n : ℂ)))
        * ((((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (a : ℝ))⁻¹
          * (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (b : ℝ))⁻¹)) * exp ((θ : ℂ) * I)
      ).aestronglyMeasurable
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : 0 ≤ r := le_of_lt hr
    rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_etermB_ray_le N0 n hs hr'
    have h2 := norm_inv_ray_nat_leB N0 a hN hs hr'
    have h3 := norm_inv_ray_nat_leB N0 b hN hs hr'
    have hpos : 0 < K * (3 / 8 + r) := by positivity
    calc ‖etermB (rayPt x θ r) n‖ * (‖(rayPt x θ r - (a : ℂ))⁻¹‖ * ‖(rayPt x θ r - (b : ℂ))⁻¹‖)
        ≤ (‖etermB (x : ℂ) n‖ / K ^ 2) * ((1 / (K * (3 / 8 + r))) * (1 / (K * (3 / 8 + r)))) := by
          apply mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = _ := by field_simp
  · exact Eventually.of_forall fun r => hsum.mul_right _
  · have hI := (integrableOn_invsq (3 / 8) (by norm_num)).const_mul (1 / K ^ 2)
    have : (fun r : ℝ => ∑' n : ℤ, (‖etermB (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2)))
        = fun r => (∑' n : ℤ, ‖etermB (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2)) := by
      funext r; exact tsum_mul_right
    rw [this]
    exact hI.const_mul _
  · refine Eventually.of_forall fun r => ?_
    exact ((summable_etermB _).hasSum.mul_right _).mul_right _

/-- The contour integral of `Ē v_a v_b`. -/
theorem contL_E_eq_genB {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (N0 a b : ℕ) (hN : 1 ≤ N0) :
    contL (xstarB N0) φ (fun z => ECB z * ((z - a)⁻¹ * (z - b)⁻¹))
      = (2 * Real.pi * I) * ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ)
        - (2 * Real.pi * I) * ((∑' m : ℕ, atomTermB a b (m + N0) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hφ1, hφ2]
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hU := rayI_E_hasSumB N0 a b hN hsφ
  have hL := rayI_E_hasSumB N0 a b hN hsφ'
  have hC := hL.sub hU
  let i : ℕ → ℤ := fun m' => -((m' : ℤ) + N0)
  have hi : Function.Injective i := by
    intro m1 m2 h
    simp only [i] at h
    omega
  have hzero : ∀ n : ℤ, n ∉ Set.range i →
      contL (xstarB N0) φ (fun z => etermB z n * ((z - a)⁻¹ * (z - b)⁻¹)) = 0 := by
    intro n hn
    apply contL_etermB_east_gen hφ1 hφ2 N0 a b hN
    by_contra h
    push_neg at h
    apply hn
    refine ⟨(-n - N0).toNat, ?_⟩
    simp only [i]
    omega
  have hreal : HasSum (fun m' : ℕ => atomTermB a b (m' + N0)) (∑' m : ℕ, atomTermB a b (m + N0)) :=
    ((summable_nat_add_iff N0).2 (summable_atomTermB a b)).hasSum
  have hcomp : HasSum (fun m' : ℕ => -(2 * Real.pi * I) * ((atomTermB a b (m' + N0) : ℝ) : ℂ))
      (-(2 * Real.pi * I) * ((∑' m : ℕ, atomTermB a b (m + N0) : ℝ) : ℂ)) :=
    (Complex.hasSum_ofReal.2 hreal).mul_left _
  have hT0 : HasSum (fun n : ℤ => contL (xstarB N0) φ
      (fun z => etermB z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      ((2 * Real.pi * I) * ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ)
        + -(2 * Real.pi * I) * ((∑' m : ℕ, atomTermB a b (m + N0) : ℝ) : ℂ)) := by
    rw [← hi.hasSum_iff hzero]
    rw [← hasSum_nat_add_iff' 1]
    have hg0 : contL (xstarB N0) φ
        (fun z => etermB z (i 0) * ((z - a)⁻¹ * (z - b)⁻¹))
        = (2 * Real.pi * I) * ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ) := by
      have : i 0 = -(N0 : ℤ) := by simp [i]
      rw [this]
      exact contL_etermB_mid_gen hφ1 hφ2 N0 a b hN
    simp only [Finset.range_one, Finset.sum_singleton, Function.comp]
    have hfun : ∀ m' : ℕ, contL (xstarB N0) φ
        (fun z => etermB z (i (m' + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
        = -(2 * Real.pi * I) * ((atomTermB a b (m' + N0) : ℝ) : ℂ) := by
      intro m'
      have : i (m' + 1) = -(((m' + N0 : ℕ) : ℤ) + 1) := by simp [i]; ring
      rw [this]
      exact contL_etermB_west_gen hφ1 hφ2 N0 a b (m' + N0) hN (Nat.le_add_left _ _)
    have h2 : (2 * Real.pi * I) * ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ)
        + -(2 * Real.pi * I) * ((∑' m : ℕ, atomTermB a b (m + N0) : ℝ) : ℂ)
        - contL (xstarB N0) φ (fun z => etermB z (i 0) * ((z - a)⁻¹ * (z - b)⁻¹))
        = -(2 * Real.pi * I) * ((∑' m : ℕ, atomTermB a b (m + N0) : ℝ) : ℂ) := by
      rw [hg0]; ring
    rw [h2]
    exact hcomp.congr_fun (fun m' => by rw [hfun m'])
  have := hC.unique hT0
  unfold contL
  rw [this]; ring

/-- **The contour identity.** -/
theorem contour_identity_genB {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (N0 a b : ℕ) (hN : 1 ≤ N0) :
    ((16 * TbarEnt a b : ℝ) : ℂ)
      = -((∑ m ∈ Finset.range N0, atomTermB a b m : ℝ) : ℂ)
        - ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ)
        + (2 * Real.pi * I)⁻¹ *
          contL (xstarB N0) φ (fun z => ECB z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
  rw [contL_E_eq_genB hφ1 hφ2 N0 a b hN]
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have := Real.pi_pos
    simp [Real.pi_ne_zero]
  have hs := (summable_atomTermB a b).sum_add_tsum_nat_add N0
  have hT := T_eq_atomsB a b
  rw [← hs] at hT
  have : ((16 * TbarEnt a b : ℝ) : ℂ) = ((-(∑ m ∈ Finset.range N0, atomTermB a b m
      + ∑' m : ℕ, atomTermB a b (m + N0)) : ℝ) : ℂ) := by rw [hT]
  rw [this]
  push_cast
  field_simp
  ring

lemma normFB (N0 a b : ℕ) (hN : 1 ≤ N0) (n : ℤ) {θ r : ℝ} (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖(etermB (rayPt (xstarB N0) θ r) n
        * ((rayPt (xstarB N0) θ r - a)⁻¹ * (rayPt (xstarB N0) θ r - b)⁻¹)) * exp ((θ : ℂ) * I)‖
      ≤ (‖etermB ((xstarB N0 : ℝ) : ℂ) n‖ / Real.sqrt (kap2 θ) ^ 2)
        * ((1 / Real.sqrt (kap2 θ) ^ 2) * (1 / (3 / 8 + r) ^ 2)) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  have h1 := norm_etermB_ray_le N0 n hs hr
  have h2 := norm_inv_ray_nat_leB N0 a hN hs hr
  have h3 := norm_inv_ray_nat_leB N0 b hN hs hr
  have hpos : 0 < K * (3 / 8 + r) := by positivity
  calc ‖etermB (rayPt (xstarB N0) θ r) n‖ * (‖(rayPt (xstarB N0) θ r - (a : ℂ))⁻¹‖
        * ‖(rayPt (xstarB N0) θ r - (b : ℂ))⁻¹‖)
      ≤ (‖etermB ((xstarB N0 : ℝ) : ℂ) n‖ / K ^ 2) * ((1 / (K * (3 / 8 + r))) * (1 / (K * (3 / 8 + r)))) := by
        apply mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = _ := by field_simp

/-- The ray integrand of `Ē v_a v_b` is integrable on `(0, ∞)`. -/
theorem integrableOn_E_rayB (N0 a b : ℕ) (hN : 1 ≤ N0) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => (ECB (rayPt (xstarB N0) θ r)
      * ((rayPt (xstarB N0) θ r - a)⁻¹ * (rayPt (xstarB N0) θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (Ioi 0) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := xstarB N0 with hxdef
  have hsum : Summable (fun n : ℤ => ‖etermB (x : ℂ) n‖ / K ^ 2) :=
    (summable_norm_iff.2 (summable_etermB (x : ℂ))).div_const _
  have hlim : ∀ r : ℝ, HasSum (fun n : ℤ => (etermB (rayPt x θ r) n
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      ((ECB (rayPt x θ r) * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I)) :=
    fun r => ((summable_etermB _).hasSum.mul_right _).mul_right _
  have hmeas : ∀ n : ℤ, Measurable fun r : ℝ => (etermB (rayPt x θ r) n
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I) := by
    intro n
    unfold rayPt etermB
    fun_prop
  refine Integrable.mono' (g := fun r => (∑' n : ℤ, ‖etermB (x : ℂ) n‖ / K ^ 2)
      * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2))) ?_ ?_ ?_
  · exact ((integrableOn_invsq (3 / 8) (by norm_num)).const_mul (1 / K ^ 2)).const_mul _
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
      (f := fun s r => ∑ n ∈ s, (etermB (rayPt x θ r) n
        * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (fun s => (Finset.measurable_sum s (fun n _ => hmeas n)).aestronglyMeasurable)
      (Eventually.of_forall fun r => hlim r)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hb : HasSum (fun n : ℤ => (‖etermB (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2)))
        ((∑' n : ℤ, ‖etermB (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2))) :=
      hsum.hasSum.mul_right _
    exact HasSum.norm_le_of_bounded (hlim r) hb (fun n => normFB N0 a b hN n hs (le_of_lt hr))

end CatalanLambda.Mirror
