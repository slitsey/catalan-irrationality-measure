module
public import CatalanCore.Li2.DecayCert.Segment
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter Topology
open scoped BigOperators
open CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert
noncomputable def ωarc : Measure ℝ := arc.map Real.cos

def momentPair (φ : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 2 / (φ - φ⁻¹))
  | n+1 =>
    let m := momentPair φ n
    let k : ℚ := n+1
    let ξ : ℚ := (φ+φ⁻¹)/2
    (m.2, ((2*k-1)*ξ*m.2-(k-1)*m.1)/(k*(ξ^2-1)))
def momentRec (φ : ℚ) (n : ℕ) : ℚ := (momentPair φ n).1

private theorem gap_pos (ξ : ℝ) (hξ : 1 < ξ) (θ : ℝ) : 0 < ξ-Real.cos θ :=
  sub_pos.mpr ((Real.cos_le_one θ).trans_lt hξ)
private theorem intPow (ξ : ℝ) (hξ : 1 < ξ) (n : ℕ) :
    Integrable (fun θ => ((ξ-Real.cos θ)^n)⁻¹) arc := by
  have hc : Continuous (fun θ => ((ξ-Real.cos θ)^n)⁻¹) :=
    ((continuous_const.sub Real.continuous_cos).pow n).inv₀
      (fun θ => pow_ne_zero _ (gap_pos ξ hξ θ).ne')
  apply integrable_arc_of_bound hc
  intro θ
  rw [abs_of_pos (inv_pos.mpr (pow_pos (gap_pos ξ hξ θ) n))]
  exact inv_anti₀ (pow_pos (sub_pos.mpr hξ) n)
    (pow_le_pow_left₀ (sub_pos.mpr hξ).le (sub_le_sub_left (Real.cos_le_one θ) ξ) n)

private theorem integral_pow_map (ξ : ℝ) (n : ℕ) :
    (∫ x, (ξ-x)^(-(n:ℤ)) ∂ωarc) = ∫ θ, ((ξ-Real.cos θ)^n)⁻¹ ∂arc := by
  simp only [zpow_neg, zpow_natCast]
  exact integral_map (μ := arc) (φ := Real.cos)
    (f := fun x : ℝ => ((ξ-x)^n)⁻¹) Real.continuous_cos.aemeasurable
    (((measurable_const.sub measurable_id).pow_const n).inv.aestronglyMeasurable)

private theorem first_moment (ξ : ℝ) (hξ : 1 < ξ) :
    (∫ θ, (ξ-Real.cos θ)⁻¹ ∂arc) = (Real.sqrt (ξ^2-1))⁻¹ := by
  have hc : jc (ξ:ℂ) = ξ := by
    unfold jc
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_add,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by linarith), abs_of_pos (by linarith)]
    ring
  have hd : jd (ξ:ℂ) = 1 := by
    unfold jd
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_add,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by linarith), abs_of_pos (by linarith)]
    ring
  have hcx : 1 < jc (ξ:ℂ) := by rw [hc]; exact hξ
  have hq : jq (ξ:ℂ) = (Real.sqrt (ξ^2-1):ℂ) := by
    have h := jphi_eq_add_jq hcx
    have hp : jphi (ξ:ℂ) = ((ξ+Real.sqrt (ξ^2-1):ℝ):ℂ) := by
      apply Complex.ext <;> simp [jphi, jR, hc, hd]
    rw [hp, Complex.ofReal_add] at h
    linear_combination -h
  have hi := integral_chebF_poisson hcx (fun _ => 1) 0
  simp only [chebF, zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
    Polynomial.Chebyshev.T_zero, Polynomial.eval_one, mul_one, Complex.ofReal_one,
    one_mul, Finset.range_zero, Finset.sum_empty] at hi
  have he : (fun θ : ℝ => jq (ξ:ℂ) / ((ξ:ℂ)-(Real.cos θ:ℂ))-1) =
      fun θ => (((Real.sqrt (ξ^2-1) * (ξ-Real.cos θ)⁻¹-1:ℝ):ℂ)) := by
    funext θ
    rw [hq]
    push_cast
    ring
  rw [he, integral_complex_ofReal] at hi
  have hire := congrArg Complex.re hi
  simp only [Complex.ofReal_re, Complex.zero_re] at hire
  have hip : Integrable (fun θ => (ξ-Real.cos θ)⁻¹) arc := by
    simpa only [pow_one] using intPow ξ hξ 1
  rw [integral_sub (hip.const_mul _) (integrable_const 1),
    integral_const_mul] at hire
  have hp : 0 < Real.sqrt (ξ^2-1) := Real.sqrt_pos.mpr (by nlinarith)
  simp only [pow_one, integral_const, probReal_univ, smul_eq_mul, mul_one] at hire
  exact eq_inv_of_mul_eq_one_left (by linarith)


private theorem moment_coefficient (ξ c s q a : ℝ) (hd : ξ-c ≠ 0) (hq : q ≠ 0)
    (htrig : s^2+c^2=1) :
    c*(q*(ξ-c))⁻¹+s*(-(a*q*s)/(q*(ξ-c))^2) =
      a*(ξ^2-1)*(q*(ξ-c)*(ξ-c))⁻¹ -
      (2*a-1)*ξ*(q*(ξ-c))⁻¹+(a-1)*q⁻¹ := by
  field_simp [hd, hq]
  ring_nf
  rw [show s^2=1-c^2 by linarith]
  ring

private theorem moment_derivative (ξ : ℝ) (hξ : 1 < ξ) (k : ℕ) (θ : ℝ) :
    HasDerivAt (fun t => Real.sin t*((ξ-Real.cos t)^(k+1))⁻¹)
      ((k+1:ℝ)*(ξ^2-1)*((ξ-Real.cos θ)^(k+2))⁻¹ -
        (2*(k+1:ℝ)-1)*ξ*((ξ-Real.cos θ)^(k+1))⁻¹ +
        (k:ℝ)*((ξ-Real.cos θ)^k)⁻¹) θ := by
  have hd := (hasDerivAt_const θ ξ).sub (Real.hasDerivAt_cos θ)
  have hi := (hd.pow (k+1)).inv (pow_ne_zero _ (gap_pos ξ hξ θ).ne')
  have hf := (Real.hasDerivAt_sin θ).mul hi
  have hfun : (fun t => Real.sin t*((ξ-Real.cos t)^(k+1))⁻¹) =
      Real.sin * (((fun t : ℝ => ξ)-Real.cos)^(k+1))⁻¹ := funext fun _ => rfl
  have hf' := hf.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => congrFun hfun y))
  apply hf'.congr_deriv
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, Pi.sub_apply,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, sub_neg_eq_add, zero_add]
  have he := moment_coefficient ξ (Real.cos θ) (Real.sin θ) ((ξ-Real.cos θ)^k)
    (k+1:ℝ) (gap_pos ξ hξ θ).ne' (pow_ne_zero _ (gap_pos ξ hξ θ).ne')
    (Real.sin_sq_add_cos_sq θ)
  simpa only [show k+2=k+1+1 by omega, pow_succ, add_sub_cancel_right] using he

private theorem integral_combination (f g h : ℝ → ℝ)
    (hf : Integrable f arc) (hg : Integrable g arc) (hh : Integrable h arc) (A B C : ℝ) :
    (∫ x, A*f x-B*g x+C*h x ∂arc) =
      A*(∫ x, f x ∂arc)-B*(∫ x, g x ∂arc)+C*(∫ x, h x ∂arc) := by
  have hab := integral_sub (μ := arc) (f := fun x => A*f x) (g := fun x => B*g x)
    (hf.const_mul A) (hg.const_mul B)
  have habc := integral_add (μ := arc) (f := fun x => A*f x-B*g x) (g := fun x => C*h x)
    ((hf.const_mul A).sub (hg.const_mul B)) (hh.const_mul C)
  rw [habc, hab, integral_const_mul, integral_const_mul, integral_const_mul]

private theorem moment_step (ξ : ℝ) (hξ : 1 < ξ) (k : ℕ) :
    (k+1:ℝ)*(ξ^2-1)*(∫ θ, ((ξ-Real.cos θ)^(k+2))⁻¹ ∂arc) =
      (2*(k+1:ℝ)-1)*ξ*(∫ θ, ((ξ-Real.cos θ)^(k+1))⁻¹ ∂arc) -
      (k:ℝ)*(∫ θ, ((ξ-Real.cos θ)^k)⁻¹ ∂arc) := by
  let F : ℝ → ℝ := fun θ => Real.sin θ * ((ξ-Real.cos θ)^(k+1))⁻¹
  let G : ℝ → ℝ := fun θ =>
    (k+1:ℝ)*(ξ^2-1)*((ξ-Real.cos θ)^(k+2))⁻¹ -
      (2*(k+1:ℝ)-1)*ξ*((ξ-Real.cos θ)^(k+1))⁻¹ +
      (k:ℝ)*((ξ-Real.cos θ)^k)⁻¹
  have hcont (n : ℕ) : Continuous (fun θ => ((ξ-Real.cos θ)^n)⁻¹) :=
    ((continuous_const.sub Real.continuous_cos).pow n).inv₀
      (fun θ => pow_ne_zero _ (gap_pos ξ hξ θ).ne')
  have hG : Continuous G := by
    exact (((hcont (k+2)).const_mul _).sub ((hcont (k+1)).const_mul _)).add
      ((hcont k).const_mul _)
  have hderiv : ∀ θ, HasDerivAt F (G θ) θ :=
    fun θ => moment_derivative ξ hξ k θ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (f' := G)
    (a := (0:ℝ)) (b := Real.pi) (fun θ _ => hderiv θ)
    (hG.intervalIntegrable _ _)
  have hzero : (∫ θ, G θ ∂arc) = 0 := by
    rw [integral_arc, intervalIntegral.integral_const_mul, hFTC]
    simp [F]
  have he := integral_combination
    (fun θ => ((ξ-Real.cos θ)^(k+2))⁻¹)
    (fun θ => ((ξ-Real.cos θ)^(k+1))⁻¹)
    (fun θ => ((ξ-Real.cos θ)^k)⁻¹)
    (intPow ξ hξ (k+2)) (intPow ξ hξ (k+1)) (intPow ξ hξ k)
    ((k+1:ℝ)*(ξ^2-1)) ((2*(k+1:ℝ)-1)*ξ) (k:ℝ)
  change (∫ θ, G θ ∂arc) = _ at he
  rw [hzero] at he
  linarith

theorem arcsine_stieltjes_rec (ξ : ℝ) (hξ : 1 < ξ) :
  let m : ℕ → ℝ := fun n => ∫ x, (ξ-x)^(-(n:ℤ)) ∂ωarc
  m 0=1 ∧ m 1=(Real.sqrt (ξ^2-1))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n →
      (n:ℝ)*(ξ^2-1)*m (n+1)=(2*(n:ℝ)-1)*ξ*m n-((n:ℝ)-1)*m (n-1) := by
  dsimp only
  simp_rw [integral_pow_map]
  refine ⟨by simp, ?_, ?_⟩
  · simpa only [pow_one] using first_moment ξ hξ
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, add_sub_cancel_right] using moment_step ξ hξ k


theorem arcsine_stieltjes_rat (φ : ℚ) (hφ : 1 < φ) (n : ℕ) :
  ∫ x, ((((φ:ℝ)+(φ:ℝ)⁻¹)/2)-x)^(-(n:ℤ)) ∂ωarc = (momentRec φ n:ℝ) := by
  have hf : 1 < (φ:ℝ) := by exact_mod_cast hφ
  have hf0 : (φ:ℝ) ≠ 0 := by linarith
  have hp : 0 < (φ:ℝ) := by linarith
  have hi : (φ:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hf
  let ξ : ℝ := ((φ:ℝ)+(φ:ℝ)⁻¹)/2
  let r : ℝ := ((φ:ℝ)-(φ:ℝ)⁻¹)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have he : ξ^2-1=r^2 := by
    dsimp [ξ, r]
    field_simp
    ring
  have hξ : 1 < ξ := by
    have hh := mul_inv_cancel₀ hf0
    dsimp only [ξ]
    nlinarith [mul_pos (sub_pos.mpr hf) (sub_pos.mpr hi)]
  have hsqrt : Real.sqrt (ξ^2-1)=r := by rw [he, Real.sqrt_sq hr.le]
  let m : ℕ → ℝ := fun j => ∫ x, (ξ-x)^(-(j:ℤ)) ∂ωarc
  have hm := arcsine_stieltjes_rec ξ hξ
  change m 0=1 ∧ m 1=(Real.sqrt (ξ^2-1))⁻¹ ∧
    ∀ j : ℕ, 1 ≤ j → (j:ℝ)*(ξ^2-1)*m (j+1)=
      (2*(j:ℝ)-1)*ξ*m j-((j:ℝ)-1)*m (j-1) at hm
  have hpair : ∀ j : ℕ,
      ((momentPair φ j).1:ℝ)=m j ∧ ((momentPair φ j).2:ℝ)=m (j+1) := by
    intro j
    induction j with
    | zero =>
      constructor
      · simpa only [momentPair, Rat.cast_one] using hm.1.symm
      · change ((2/(φ-φ⁻¹):ℚ):ℝ)=m 1
        push_cast
        rw [hm.2.1, hsqrt]
        dsimp [r]
        rw [inv_div]
    | succ j ih =>
      change ((momentPair φ j).2:ℝ)=m (j+1) ∧ _
      refine ⟨ih.2, ?_⟩
      simp only [momentPair]
      push_cast
      rw [ih.1, ih.2]
      change (((2*((j:ℝ)+1)-1)*ξ*m (j+1)-((j:ℝ)+1-1)*m j) /
        (((j:ℝ)+1)*(ξ^2-1))) = m (j+1+1)
      apply (div_eq_iff (mul_ne_zero (by positivity) (by nlinarith : ξ^2-1 ≠ 0))).mpr
      have h := hm.2.2 (j+1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, add_sub_cancel_right] at h
      nlinarith [h]
  simpa only [momentRec, m, ξ] using (hpair n).1.symm

#print axioms arcsine_stieltjes_rat
#print axioms first_moment
#print axioms arcsine_stieltjes_rec
end CatalanCore.Li2.DecayCert
