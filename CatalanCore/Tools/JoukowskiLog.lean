module
public import CatalanCore.Tools.Joukowski
public import CatalanMeasure.GenD.Cert.LogSeriesBand
public import CatalanMeasure.Cert.DenominatorBounds
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Complex Polynomial Filter Topology
open scoped BigOperators
open CatalanCore.Zeta5.Potential OAI.InternalCatalan
namespace CatalanCore.Tools.Joukowski
private theorem log_mul_real_positive (a q : ℂ) (ha : a ≠ 0)
    (hqim : q.im=0) (hqpos : 0 < q.re) :
    Complex.log (a*q)=Complex.log a+Complex.log q := by
  have he : q=(q.re:ℂ) := by apply Complex.ext <;> simp [hqim]
  rw [he, Complex.log_mul_ofReal q.re hqpos a ha, ← Complex.ofReal_log hqpos.le]
  ring

theorem complex_log_jphi {ζ : ℂ} (h : 1 < jc ζ) {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    Complex.log (ζ-(x:ℂ)) = Complex.log (jphi ζ/2) +
      Complex.log (1-2*(x:ℂ)*(jphi ζ)⁻¹+((jphi ζ)⁻¹)^2) := by
  let φ := jphi ζ
  let w := φ⁻¹
  let Q : ℝ → ℂ := fun y => 1-2*(y:ℂ)*w+w^2
  have hφ : φ ≠ 0 := jphi_ne_zero h
  have hw : ‖w‖ < 1 := by dsimp [w, φ]; rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (jphi_spec h).1
  have hfac (y : ℝ) : ζ-(y:ℂ)=(φ/2)*Q y := by
    have he := (jphi_spec h).2
    change (φ+φ⁻¹)/2=ζ at he
    rw [← he]
    dsimp [Q, w]
    field_simp
    ring
  have hslit (y : ℝ) (hy : |y| ≤ 1) : Q y ∈ Complex.slitPlane :=
    CatalanMeasure.GenD.Cert.LogSeriesBand.quad_mem_slitPlane hw hy
  have hφ2 : φ/2 ≠ 0 := div_ne_zero hφ (by norm_num)
  change Complex.log (ζ-(x:ℂ))=Complex.log (φ/2)+Complex.log (Q x)
  by_cases hreal : ζ.im=0
  · have himφ : φ.im=0 := by dsimp [φ, jphi]; simp [hreal]
    have himw : w.im=0 := by simp [w, Complex.inv_im, himφ]
    have himQ : (Q x).im=0 := by simp [Q, pow_two, himw]
    have hpos : 0 < (Q x).re := (hslit x (abs_le.mpr hx)).resolve_right (by simp [himQ])
    rw [hfac x]
    exact log_mul_real_positive _ _ hφ2 himQ hpos
  · have hm : 0 < |ζ.im| := abs_pos.mpr hreal
    have hm' : 0 < (1-‖w‖)^2 := sq_pos_of_pos (sub_pos.mpr hw)
    have ha (y : ℝ) (_ : |y| ≤ 1) : ζ-1*(y:ℂ) ∈ Complex.slitPlane := by
      right
      simpa using hreal
    have ha' (y : ℝ) (hy : |y| ≤ 1) : (1+w^2)-(2*w)*(y:ℂ) ∈ Complex.slitPlane := by
      convert hslit y hy using 1 <;> dsimp [Q] <;> ring
    have hma (y : ℝ) (_ : |y| ≤ 1) : |ζ.im| ≤ ‖ζ-1*(y:ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (ζ-1*(y:ℂ))
    have hma' (y : ℝ) (hy : |y| ≤ 1) : (1-‖w‖)^2 ≤ ‖(1+w^2)-(2*w)*(y:ℂ)‖ := by
      have hd := CatalanMeasure.Cert.quadratic_den_norm_lower hy hw.le
      convert hd using 1 <;> unfold barrierTailQuadraticDen <;> ring
    have hnum : (2*w)*ζ-1*(1+w^2)=0 := by
      have he := (jphi_spec h).2
      change (φ+φ⁻¹)/2=ζ at he
      rw [← he]
      dsimp [w]
      field_simp
      ring
    have hconst (y : ℝ) (hy : |y| ≤ 1) :
        Complex.log (ζ-(y:ℂ))-Complex.log (Q y) =
          Complex.log ζ-Complex.log (Q 0) := by
      have hd := CatalanMeasure.GenD.Cert.LogSeriesBand.log_affine_drift
        ζ 1 (1+w^2) (2*w) |ζ.im| ((1-‖w‖)^2) hm hm' ha ha' hma hma' hy
      rw [hnum, norm_zero, zero_div, zero_mul] at hd
      have he := norm_le_zero_iff.mp hd
      have hQy : (1+w^2)-(2*w)*(y:ℂ)=Q y := by dsimp [Q]; ring
      have hQ0 : 1+w^2=Q 0 := by simp [Q]
      rw [one_mul, hQy, hQ0] at he
      exact sub_eq_zero.mp he
    have hr : |w.re| ≤ 1 := (Complex.abs_re_le_norm w).trans hw.le
    have hQanchor : Q w.re=((1-‖w‖^2:ℝ):ℂ) := by
      rw [sq_norm_eq]
      apply Complex.ext <;> simp [Q, pow_two] <;> ring
    have hp : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have hanchor : Complex.log (ζ-(w.re:ℂ))-Complex.log (Q w.re) = Complex.log (φ/2) := by
      rw [hfac w.re, hQanchor, Complex.log_mul_ofReal _ hp _ hφ2,
        ← Complex.ofReal_log hp.le]
      ring
    have he := (hconst x (abs_le.mpr hx)).trans (hconst w.re hr).symm
    rw [hanchor] at he
    linear_combination he

private theorem integral_chebF_mul_seriesC (c : ℕ → ℝ) (N : ℕ) (a : ℕ → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (s : ℝ → ℂ)
    (hs : ∀ θ, HasSum (fun k => a k *
      (((Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (Real.cos θ):ℝ):ℂ)) (s θ)) :
    (∫ θ, (chebF c N (Real.cos θ):ℂ)*s θ ∂arc) =
      ∑ k ∈ Finset.range N, a k*(c (k+1):ℂ)/2 := by
  let W : ℝ := ∑ j ∈ Finset.range (N+1), |c j|
  let F : ℕ → ℝ → ℂ := fun k θ => (chebF c N (Real.cos θ):ℂ)*
    (a k*(((Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (Real.cos θ):ℝ):ℂ))
  have hFc (k : ℕ) : Continuous (F k) := by
    dsimp only [F]
    exact (Complex.continuous_ofReal.comp (continuous_chebF_cos c N)).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp
        ((Polynomial.continuous _).comp Real.continuous_cos)))
  have hFb (k : ℕ) (θ : ℝ) : ‖F k θ‖ ≤ W*‖a k‖ := by
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := abs_chebF_le c N (cos_mem θ)
    have h2 := energy_chebyshev_abs_le_one (k+1) (cos_mem θ)
    calc
      _ ≤ W*(‖a k‖*1) := mul_le_mul h1
        (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) (by positivity)
        (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      _ = _ := by ring
  have hFi (k : ℕ) : Integrable (F k) arc :=
    Integrable.mono' (integrable_const (W*‖a k‖)) (hFc k).aestronglyMeasurable
      (ae_of_all _ (hFb k))
  have hFsum : Summable (fun k => ∫ θ, ‖F k θ‖ ∂arc) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun θ => norm_nonneg _))
      (fun k => ?_) (ha.mul_left W)
    calc
      _ ≤ ∫ _θ, W*‖a k‖ ∂arc := integral_mono (hFi k).norm (integrable_const _) (hFb k)
      _ = _ := by simp
  have htsum := hasSum_integral_of_summable_integral_norm hFi hFsum
  have hmom (k : ℕ) : (∫ θ, F k θ ∂arc) =
      if k+1 ≤ N then a k*(c (k+1):ℂ)/2 else 0 := by
    have he : (fun θ => F k θ) = fun θ => a k*
        ((chebF c N (Real.cos θ)*(Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (Real.cos θ):ℝ):ℂ) := by
      funext θ
      dsimp only [F]
      push_cast
      ring
    rw [he, integral_const_mul, integral_complex_ofReal, integral_chebF_mul_T]
    by_cases hk : k+1 ≤ N
    · simp [hk]
      ring
    · simp [hk]
  have hfin : HasSum (fun k => ∫ θ, F k θ ∂arc)
      (∑ k ∈ Finset.range N, a k*(c (k+1):ℂ)/2) := by
    have hh : HasSum (fun k => ∫ θ, F k θ ∂arc)
        (∑ k ∈ Finset.range N, ∫ θ, F k θ ∂arc) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        rw [hmom k]
        have hkn : ¬ k+1 ≤ N := by simp only [Finset.mem_range] at hk; omega
        simp [hkn])
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmom k, if_pos (by simpa only [Finset.mem_range, Nat.lt_iff_add_one_le] using hk)]
  have he : (fun θ => ∑' k, F k θ) = fun θ => (chebF c N (Real.cos θ):ℂ)*s θ := by
    funext θ
    dsimp only [F]
    rw [tsum_mul_left, (hs θ).tsum_eq]
  rw [← he, ← htsum.tsum_eq, hfin.tsum_eq]


theorem integral_chebF_logC (c : ℕ → ℝ) (N : ℕ) {ζ : ℂ} (h : 1 < jc ζ) :
    (∫ θ, (chebF c N (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ)) ∂arc) =
      (c 0:ℂ)*Complex.log (jphi ζ/2) -
        ∑ k ∈ Finset.range N, (c (k+1):ℂ)*(jphi ζ)⁻¹^(k+1)/(k+1:ℕ) := by
  let w : ℂ := (jphi ζ)⁻¹
  let Q : ℝ → ℂ := fun x => 1-2*(x:ℂ)*w+w^2
  let a : ℕ → ℂ := fun k => -(2:ℂ)*w^(k+1)/(k+1:ℕ)
  have hw : ‖w‖ < 1 := by dsimp [w]; rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (jphi_spec h).1
  have ha : Summable (fun k => ‖a k‖) := by
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left (2*‖w‖))
    dsimp only [a]
    rw [norm_div, norm_mul, norm_neg, Complex.norm_two, norm_pow, Complex.norm_natCast]
    calc
      2*‖w‖^(k+1)/(k+1:ℕ) ≤ 2*‖w‖^(k+1) :=
        div_le_self (by positivity) (by exact_mod_cast Nat.succ_pos k)
      _ = _ := by rw [pow_succ]; ring
  have hs (θ : ℝ) : HasSum (fun k => a k*
      (((Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (Real.cos θ):ℝ):ℂ)) (Complex.log (Q (Real.cos θ))) := by
    have hh := (barrier_hasSum_chebyshev_log (abs_le.mpr (cos_mem θ)) hw).mul_left (-2)
    convert hh using 1
    · funext k
      dsimp only [a]
      ring
    · dsimp only [Q]
      ring
  have hint : Integrable (fun θ => (chebF c N (Real.cos θ):ℂ)*Complex.log (Q (Real.cos θ))) arc := by
    have hqc : ContinuousOn Q (Icc (-1:ℝ) 1) := by dsimp only [Q]; fun_prop
    have hqlog := hqc.clog (fun x hx =>
      CatalanMeasure.GenD.Cert.LogSeriesBand.quad_mem_slitPlane hw (abs_le.mpr hx))
    have hc : ContinuousOn (fun x => (chebF c N x:ℂ)*Complex.log (Q x)) (Icc (-1:ℝ) 1) :=
      (Complex.continuous_ofReal.comp (continuous_chebF c N)).continuousOn.mul hqlog
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact integrable_arc_C (hc.comp_continuous Real.continuous_cos (fun θ => cos_mem θ))
      (fun θ => hC _ (cos_mem θ))
  have hser : (∫ θ, (chebF c N (Real.cos θ):ℂ)*Complex.log (Q (Real.cos θ)) ∂arc) =
      -(∑ k ∈ Finset.range N, (c (k+1):ℂ)*w^(k+1)/(k+1:ℕ)) := by
    rw [integral_chebF_mul_seriesC c N a ha _ hs, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [a]
    ring
  have hfun : (fun θ : ℝ => (chebF c N (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ))) =
      fun θ => Complex.log (jphi ζ/2)*(chebF c N (Real.cos θ):ℂ) +
        (chebF c N (Real.cos θ):ℂ)*Complex.log (Q (Real.cos θ)) := by
    funext θ
    rw [complex_log_jphi h (cos_mem θ)]
    dsimp only [Q,w]
    ring
  have hi0 : Integrable (fun θ => Complex.log (jphi ζ/2)*(chebF c N (Real.cos θ):ℂ)) arc :=
    (integrable_chebF c N).ofReal.const_mul _
  rw [hfun, integral_add hi0 hint, integral_const_mul, integral_complex_ofReal, integral_chebF, hser]
  dsimp only [w]
  ring

#print axioms integral_chebF_logC
#print axioms integral_chebF_mul_seriesC
#print axioms complex_log_jphi
end CatalanCore.Tools.Joukowski
