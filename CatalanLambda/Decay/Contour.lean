import CatalanLambda.Decay.RayFTC
import CatalanLambda.Decay.Atoms
import CatalanLambda.Decay.Reflect

/-!
# The contour identity

For `N0 : ℕ`, `x* = -N0 - 3/8`, `φ = 3π/5` and `Γ` the two rays `x* + r e^{±iφ}` traversed downward,
`16 · T_{ab} = - ∑_{m < N0} atomTerm a b m + (1/2πi) ∫_Γ E(z) (z-a)⁻¹ (z-b)⁻¹ dz`.
-/

open Complex MeasureTheory Filter Topology Set

namespace CatalanLambda.Decay

/-- The opening angle `φ = 3π/5`. -/
noncomputable def phiC : ℝ := 3 * Real.pi / 5

/-- The vertex `x* = -N0 - 3/8`. -/
noncomputable def xstar (N0 : ℕ) : ℝ := -(N0 : ℝ) - 3 / 8

lemma phiC_gt : Real.pi / 2 < phiC := by
  unfold phiC; linarith [Real.pi_pos]

lemma phiC_lt : phiC < Real.pi := by
  unfold phiC; linarith [Real.pi_pos]

/-- The integrand `g_p(z) = (z-p)⁻¹ (z-a)⁻¹ (z-b)⁻¹`. -/
noncomputable def g3 (p a b : ℝ) (z : ℂ) : ℂ := (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹

lemma contL_sub_g3 (p q a b x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p ≠ x) (hq : q ≠ x) (ha : a ≠ x) (hb : b ≠ x) :
    contL x φ (fun z => g3 p a b z - g3 q a b z) = contL x φ (g3 p a b) - contL x φ (g3 q a b) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hf : (fun z => g3 p a b z - g3 q a b z) = fun z => g3 p a b z + (-1 : ℂ) * g3 q a b z := by
    funext z; ring
  have hR : ∀ θ : ℝ, Real.sin θ ≠ 0 → rayI x θ (fun z => g3 p a b z - g3 q a b z)
      = rayI x θ (g3 p a b) - rayI x θ (g3 q a b) := by
    intro θ hs
    have i1 : IntegrableOn (fun r : ℝ => g3 p a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) :=
      integrableOn_ray3 p a b hp ha hb hs
    have i2 : IntegrableOn (fun r : ℝ => g3 q a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) :=
      integrableOn_ray3 q a b hq ha hb hs
    have hh := rayI_add_smul (x := x) (θ := θ) (g3 p a b) (g3 q a b) (-1) i1 i2
    rw [hf, hh]
    ring
  unfold contL
  rw [hR φ hsφ, hR (-φ) hsφ']
  ring

lemma eterm_eq_g3 (n : ℤ) (a b : ℕ) (z : ℂ) :
    eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)
      = g3 ((n : ℝ) + 1 / 4) a b z - g3 (n : ℝ) a b z := by
  unfold eterm g3
  push_cast
  simp only [one_div]
  ring

/-- Poles of `e_n` to the right of `x*` (`n ≥ -N0`): no contribution. -/
theorem contL_eterm_east (N0 a b : ℕ) (n : ℤ) (hn : -(N0 : ℤ) ≤ n) :
    contL (xstar N0) phiC (fun z => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)) = 0 := by
  have hn' : -(N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hx : xstar N0 = -(N0 : ℝ) - 3 / 8 := rfl
  have hfun : (fun z : ℂ => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((n : ℝ) + 1 / 4) a b z - g3 (n : ℝ) a b z := by
    funext z; exact eterm_eq_g3 n a b z
  rw [hfun, contL_sub_g3 _ _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_east _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_east _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  ring

/-- Poles of `e_{-(m+1)}` to the left of `x*` (`m ≥ N0`): the atom term. -/
theorem contL_eterm_west (N0 a b m : ℕ) (hm : N0 ≤ m) :
    contL (xstar N0) phiC (fun z => eterm z (-((m : ℤ) + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = -(2 * Real.pi * I) * (atomTerm a b m : ℝ) := by
  have hm' : (N0 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hx : xstar N0 = -(N0 : ℝ) - 3 / 8 := rfl
  have hfun : (fun z : ℂ => eterm z (-((m : ℤ) + 1)) * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => g3 ((((-((m : ℤ) + 1) : ℤ)) : ℝ) + 1 / 4) a b z
          - g3 ((((-((m : ℤ) + 1) : ℤ)) : ℝ)) a b z := by
    funext z; exact eterm_eq_g3 _ a b z
  have e1 : ((((-((m : ℤ) + 1) : ℤ)) : ℝ)) = -(m : ℝ) - 1 := by push_cast; ring
  rw [hfun, e1]
  rw [contL_sub_g3 _ _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith) (by rw [hx]; linarith)]
  unfold g3
  rw [contL_tri_west _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith),
    contL_tri_west _ _ _ _ _ phiC_gt phiC_lt (by rw [hx]; linarith) (by rw [hx]; linarith)
    (by rw [hx]; linarith)]
  have hR : (1 / (((-(m : ℝ) - 1 + 1 / 4) - a) * ((-(m : ℝ) - 1 + 1 / 4) - b))
      - 1 / (((-(m : ℝ) - 1) - a) * ((-(m : ℝ) - 1) - b))) = atomTerm a b m := by
    have e1 : (-(m : ℝ) - 1 + 1 / 4 - a) * (-(m : ℝ) - 1 + 1 / 4 - b)
        = ((a : ℝ) + m + 3 / 4) * ((b : ℝ) + m + 3 / 4) := by ring
    have e2 : (-(m : ℝ) - 1 - a) * (-(m : ℝ) - 1 - b) = ((a : ℝ) + m + 1) * ((b : ℝ) + m + 1) := by ring
    rw [e1, e2, atomTerm_eq]
  have key := congrArg (fun t : ℝ => (t : ℂ)) hR
  push_cast at key ⊢
  linear_combination (-(2 * (Real.pi : ℂ) * I)) * key


lemma xstar_ne_int (N0 : ℕ) (n : ℤ) : (n : ℝ) ≠ xstar N0 := by
  intro h
  have h8 : (8 * (n : ℝ)) = -8 * (N0 : ℝ) - 3 := by unfold xstar at h; linarith
  have : (8 * n : ℤ) = -8 * (N0 : ℤ) - 3 := by exact_mod_cast h8
  omega

lemma xstar_ne_int_add (N0 : ℕ) (n : ℤ) : (n : ℝ) + 1 / 4 ≠ xstar N0 := by
  intro h
  have h8 : (8 * (n : ℝ)) = -8 * (N0 : ℝ) - 5 := by unfold xstar at h; linarith
  have : (8 * n : ℤ) = -8 * (N0 : ℤ) - 5 := by exact_mod_cast h8
  omega

lemma eterm_eq_mul (z : ℂ) (n : ℤ) (h1 : z - (((n : ℝ) + 1 / 4 : ℝ) : ℂ) ≠ 0)
    (h0 : z - ((n : ℝ) : ℂ) ≠ 0) :
    eterm z n = (1 / 4 : ℂ) * ((z - (((n : ℝ) + 1 / 4 : ℝ) : ℂ))⁻¹ * (z - ((n : ℝ) : ℂ))⁻¹) := by
  unfold eterm
  push_cast at h1 h0 ⊢
  have h1' : z - (n : ℂ) - 1 / 4 ≠ 0 := by
    intro h; apply h1; linear_combination h
  have h0' : z - (n : ℂ) ≠ 0 := h0
  have h1'' : z - ((n : ℂ) + 1 / 4) ≠ 0 := h1
  have e : z - (n : ℂ) - 1 / 4 = z - ((n : ℂ) + 1 / 4) := by ring
  rw [e]
  have hBA : z - (n : ℂ) = (z - ((n : ℂ) + 1 / 4)) + 1 / 4 := by ring
  generalize z - ((n : ℂ) + 1 / 4) = A at *
  generalize z - (n : ℂ) = B at *
  subst hBA
  simp only [one_div] at *
  rw [inv_sub_inv h1'' h0, div_eq_mul_inv, mul_inv]
  ring

lemma norm_eterm_ray_le (N0 : ℕ) (n : ℤ) {θ r : ℝ} (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖eterm (rayPt (xstar N0) θ r) n‖ ≤ ‖eterm ((xstar N0 : ℝ) : ℂ) n‖ / Real.sqrt (kap2 θ) ^ 2 := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  set x := xstar N0
  have hq1 := xstar_ne_int_add N0 n
  have hq0 := xstar_ne_int N0 n
  have d1 : 0 < |x - ((n : ℝ) + 1 / 4)| := abs_pos.2 (sub_ne_zero.2 hq1.symm)
  have d0 : 0 < |x - (n : ℝ)| := abs_pos.2 (sub_ne_zero.2 hq0.symm)
  rw [eterm_eq_mul _ n (rayPt_sub_ne hq1 hs hr) (rayPt_sub_ne hq0 hs hr)]
  have hx1 : ((x : ℝ) : ℂ) - (((n : ℝ) + 1 / 4 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.2 hq1.symm
  have hx0 : ((x : ℝ) : ℂ) - ((n : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.2 hq0.symm
  rw [eterm_eq_mul _ n hx1 hx0]
  simp only [norm_mul, norm_inv]
  have e1 : ‖((x : ℝ) : ℂ) - (((n : ℝ) + 1 / 4 : ℝ) : ℂ)‖ = |x - ((n : ℝ) + 1 / 4)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have e0 : ‖((x : ℝ) : ℂ) - ((n : ℝ) : ℂ)‖ = |x - (n : ℝ)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e1, e0]
  have h1 := norm_inv_rayPt_le (x := x) (θ := θ) ((n : ℝ) + 1 / 4) hq1 hs hr
  have h0 := norm_inv_rayPt_le (x := x) (θ := θ) (n : ℝ) hq0 hs hr
  simp only [norm_inv] at h1 h0
  have hb1 : 1 / (K * (|x - ((n : ℝ) + 1 / 4)| + r)) ≤ 1 / (K * |x - ((n : ℝ) + 1 / 4)|) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hb0 : 1 / (K * (|x - (n : ℝ)| + r)) ≤ 1 / (K * |x - (n : ℝ)|) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h1' := h1.trans hb1
  have h0' := h0.trans hb0
  have n4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [n4]
  have := mul_le_mul h1' h0' (by positivity) (by positivity)
  calc 1 / 4 * (‖(rayPt x θ r - (((n : ℝ) + 1 / 4 : ℝ) : ℂ))‖⁻¹ * ‖(rayPt x θ r - ((n : ℝ) : ℂ))‖⁻¹)
      ≤ 1 / 4 * ((1 / (K * |x - ((n : ℝ) + 1 / 4)|)) * (1 / (K * |x - (n : ℝ)|))) := by gcongr
    _ = 1 / 4 * (|x - ((n : ℝ) + 1 / 4)|⁻¹ * |x - (n : ℝ)|⁻¹) / K ^ 2 := by
        field_simp


lemma xstar_ne_nat (N0 a : ℕ) : (a : ℝ) ≠ xstar N0 := by
  unfold xstar
  have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
  intro h; linarith

lemma three_eighths_le (N0 a : ℕ) : (3 / 8 : ℝ) ≤ |xstar N0 - a| := by
  unfold xstar
  have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

lemma norm_inv_ray_nat_le (N0 a : ℕ) {θ r : ℝ} (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖(rayPt (xstar N0) θ r - (a : ℝ))⁻¹‖ ≤ 1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  refine (norm_inv_rayPt_le (a : ℝ) (xstar_ne_nat N0 a) hs hr).trans ?_
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [three_eighths_le N0 a])

/-- **Interchange of sum and ray integral**: `∑_n ∫_ray e_n v_a v_b = ∫_ray E v_a v_b`. -/
theorem rayI_E_hasSum (N0 a b : ℕ) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI (xstar N0) θ (fun z => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI (xstar N0) θ (fun z => EC z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := xstar N0 with hxdef
  have hsum : Summable (fun n : ℤ => ‖eterm (x : ℂ) n‖ / K ^ 2) :=
    (summable_norm_iff.2 (summable_eterm (x : ℂ))).div_const _
  unfold rayI
  refine hasSum_integral_of_dominated_convergence
    (fun n r => (‖eterm (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2))) ?_ ?_ ?_ ?_ ?_
  · intro n
    unfold rayPt eterm
    exact (by fun_prop : Measurable fun r : ℝ =>
      ((1 / (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (n : ℂ) - 1 / 4)
        - 1 / (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (n : ℂ)))
        * ((((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (a : ℝ))⁻¹
          * (((x : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)) - (b : ℝ))⁻¹)) * exp ((θ : ℂ) * I)
      ).aestronglyMeasurable
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : 0 ≤ r := le_of_lt hr
    rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_eterm_ray_le N0 n hs hr'
    have h2 := norm_inv_ray_nat_le N0 a hs hr'
    have h3 := norm_inv_ray_nat_le N0 b hs hr'
    have hpos : 0 < K * (3 / 8 + r) := by positivity
    calc ‖eterm (rayPt x θ r) n‖ * (‖(rayPt x θ r - (a : ℂ))⁻¹‖ * ‖(rayPt x θ r - (b : ℂ))⁻¹‖)
        ≤ (‖eterm (x : ℂ) n‖ / K ^ 2) * ((1 / (K * (3 / 8 + r))) * (1 / (K * (3 / 8 + r)))) := by
          apply mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = _ := by field_simp
  · exact Eventually.of_forall fun r => hsum.mul_right _
  · have hI := (integrableOn_invsq (3 / 8) (by norm_num)).const_mul (1 / K ^ 2)
    have : (fun r : ℝ => ∑' n : ℤ, (‖eterm (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2)))
        = fun r => (∑' n : ℤ, ‖eterm (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2)) := by
      funext r; exact tsum_mul_right
    rw [this]
    exact hI.const_mul _
  · refine Eventually.of_forall fun r => ?_
    exact ((summable_eterm _).hasSum.mul_right _).mul_right _


/-- The contour integral of `E v_a v_b` equals minus `2πi` times the tail of the atom series. -/
theorem contL_E_eq (N0 a b : ℕ) :
    contL (xstar N0) phiC (fun z => EC z * ((z - a)⁻¹ * (z - b)⁻¹))
      = -(2 * Real.pi * I) * ((∑' m : ℕ, atomTerm a b (m + N0) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin phiC ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [phiC_gt, phiC_lt]
  have hsφ' : Real.sin (-phiC) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hU := rayI_E_hasSum N0 a b hsφ
  have hL := rayI_E_hasSum N0 a b hsφ'
  have hC := hL.sub hU
  let i : ℕ → ℤ := fun m' => -(((m' + N0 : ℕ) : ℤ) + 1)
  have hi : Function.Injective i := by
    intro m1 m2 h
    simp only [i] at h
    omega
  have hzero : ∀ n : ℤ, n ∉ Set.range i →
      contL (xstar N0) phiC (fun z => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)) = 0 := by
    intro n hn
    apply contL_eterm_east
    by_contra h
    push_neg at h
    apply hn
    refine ⟨(-n - 1 - N0).toNat, ?_⟩
    simp only [i]
    omega
  have hreal : HasSum (fun m' : ℕ => atomTerm a b (m' + N0)) (∑' m : ℕ, atomTerm a b (m + N0)) :=
    ((summable_nat_add_iff N0).2 (summable_atomTerm a b)).hasSum
  have hcomp : HasSum (fun m' : ℕ => -(2 * Real.pi * I) * ((atomTerm a b (m' + N0) : ℝ) : ℂ))
      (-(2 * Real.pi * I) * ((∑' m : ℕ, atomTerm a b (m + N0) : ℝ) : ℂ)) :=
    (Complex.hasSum_ofReal.2 hreal).mul_left _
  have hT : HasSum (fun n : ℤ => contL (xstar N0) phiC
      (fun z => eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (-(2 * Real.pi * I) * ((∑' m : ℕ, atomTerm a b (m + N0) : ℝ) : ℂ)) := by
    rw [← hi.hasSum_iff hzero]
    refine hcomp.congr_fun ?_
    intro m'
    exact contL_eterm_west N0 a b (m' + N0) (Nat.le_add_left _ _)
  exact hC.unique hT

/-- **The contour identity.**  With `x* = -N0 - 3/8`, `φ = 3π/5`, `Γ` the two rays `x* + r e^{±iφ}`
traversed downward (`contL`: lower ray outbound minus upper ray outbound),
`16 T_{ab} = - ∑_{m<N0} (u_{m+3/4}(a)u_{m+3/4}(b) - u_{m+1}(a)u_{m+1}(b)) + (1/2πi) ∫_Γ E v_a v_b dz`. -/
theorem contour_identity (N0 a b : ℕ) :
    ((16 * Tent a b : ℝ) : ℂ)
      = -((∑ m ∈ Finset.range N0, atomTerm a b m : ℝ) : ℂ)
        + (2 * Real.pi * I)⁻¹ *
          contL (xstar N0) phiC (fun z => EC z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
  rw [contL_E_eq]
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have := Real.pi_pos
    simp [Real.pi_ne_zero]
  have hs := (summable_atomTerm a b).sum_add_tsum_nat_add N0
  have hT := T_eq_atoms a b
  rw [← hs] at hT
  have : ((16 * Tent a b : ℝ) : ℂ) = ((-(∑ m ∈ Finset.range N0, atomTerm a b m
      + ∑' m : ℕ, atomTerm a b (m + N0)) : ℝ) : ℂ) := by rw [hT]
  rw [this]
  push_cast
  field_simp
  ring


lemma normF_le (N0 a b : ℕ) (n : ℤ) {θ r : ℝ} (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖(eterm (rayPt (xstar N0) θ r) n
        * ((rayPt (xstar N0) θ r - a)⁻¹ * (rayPt (xstar N0) θ r - b)⁻¹)) * exp ((θ : ℂ) * I)‖
      ≤ (‖eterm ((xstar N0 : ℝ) : ℂ) n‖ / Real.sqrt (kap2 θ) ^ 2)
        * ((1 / Real.sqrt (kap2 θ) ^ 2) * (1 / (3 / 8 + r) ^ 2)) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  have h1 := norm_eterm_ray_le N0 n hs hr
  have h2 := norm_inv_ray_nat_le N0 a hs hr
  have h3 := norm_inv_ray_nat_le N0 b hs hr
  have hpos : 0 < K * (3 / 8 + r) := by positivity
  calc ‖eterm (rayPt (xstar N0) θ r) n‖ * (‖(rayPt (xstar N0) θ r - (a : ℂ))⁻¹‖
        * ‖(rayPt (xstar N0) θ r - (b : ℂ))⁻¹‖)
      ≤ (‖eterm ((xstar N0 : ℝ) : ℂ) n‖ / K ^ 2) * ((1 / (K * (3 / 8 + r))) * (1 / (K * (3 / 8 + r)))) := by
        apply mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = _ := by field_simp

/-- The ray integrand of `E v_a v_b` is integrable on `(0, ∞)` (so `contL` is a genuine integral). -/
theorem integrableOn_E_ray (N0 a b : ℕ) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => (EC (rayPt (xstar N0) θ r)
      * ((rayPt (xstar N0) θ r - a)⁻¹ * (rayPt (xstar N0) θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (Ioi 0) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := xstar N0 with hxdef
  have hsum : Summable (fun n : ℤ => ‖eterm (x : ℂ) n‖ / K ^ 2) :=
    (summable_norm_iff.2 (summable_eterm (x : ℂ))).div_const _
  have hlim : ∀ r : ℝ, HasSum (fun n : ℤ => (eterm (rayPt x θ r) n
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      ((EC (rayPt x θ r) * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I)) :=
    fun r => ((summable_eterm _).hasSum.mul_right _).mul_right _
  have hmeas : ∀ n : ℤ, Measurable fun r : ℝ => (eterm (rayPt x θ r) n
      * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I) := by
    intro n
    unfold rayPt eterm
    fun_prop
  refine Integrable.mono' (g := fun r => (∑' n : ℤ, ‖eterm (x : ℂ) n‖ / K ^ 2)
      * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2))) ?_ ?_ ?_
  · exact ((integrableOn_invsq (3 / 8) (by norm_num)).const_mul (1 / K ^ 2)).const_mul _
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
      (f := fun s r => ∑ n ∈ s, (eterm (rayPt x θ r) n
        * ((rayPt x θ r - a)⁻¹ * (rayPt x θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (fun s => (Finset.measurable_sum s (fun n _ => hmeas n)).aestronglyMeasurable)
      (Eventually.of_forall fun r => hlim r)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hb : HasSum (fun n : ℤ => (‖eterm (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2)))
        ((∑' n : ℤ, ‖eterm (x : ℂ) n‖ / K ^ 2) * ((1 / K ^ 2) * (1 / (3 / 8 + r) ^ 2))) :=
      hsum.hasSum.mul_right _
    exact HasSum.norm_le_of_bounded (hlim r) hb (fun n => normF_le N0 a b n hs (le_of_lt hr))

end CatalanLambda.Decay
