module

public import CatalanCore.Decay.ComplexTaylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CatalanCore.Lai.DecayTrig

@[expose] public section

/-!
# Wedge cells of kinds A, G and R (Lai decay, LD18)

Generic in the three-pole field `Ψ̃` (`e r B K θ`), in the weights `w₁ w₂` of the two segment
potentials, in the segments `{M + h x : |x| ≤ 1}` carrying `f dω`, `f = Σ c_k T_k ≥ 0`, and in the
analytic curve `γ` along which the cell Taylor tower is taken.  Contents:

* the own potential of a segment on its support (`logPotC_segMeasure_support`, `_cos`) and on the
  real line through it beyond the endpoints (`logPotC_segMeasure_cosh`), as real cosine and
  exponential series;
* the own-potential towers `ownAT` (A cells, variable `φ`, `s = M + h cos φ`) and `ownGT`
  (G cells, variable `w`, `s = M + ε h cosh w`), with `IsTower`, the order-5 remainder and the
  identification with the potential (`logPotC_eq_ownAT`, `logPotC_eq_ownGT`);
* the arms `armA`, `armG`, `lineC` (derivative chains of the cell curves) and their norm bounds;
* `VCell`, `SegCell` (distance and remainder data of one cell) and the generic cell theorem
  `wedgeField_cell_sound` (V tower + own tower + cross tower from `Decay.ComplexTaylor` and
  `Tools.Joukowski`; enclosures of the point values and the remainder as hypotheses), then
  `cellA_sound`, `cellG_sound`, `cellR_sound` (the conclusion is `vAnal + w₁ U₁ + w₂ U₂ ≤ ℓ` on
  the cell, `vAnal = κ + Re Ψ̃`, the analytic continuation of `V`, equal to `vField` for
  `Im s > 0` by `vAnal_eq_vField`, so cells reaching past the vertex are covered);
* `wedgeTower_enc`: enclosure of the combined tower from enclosures of its three components;
* `ownAT_enc`, `ownGT_enc_rho`: rational enclosures of the own-tower point values at a dyadic
  centre `x = π n / 128` (from the checked table of `Lai.DecayTrig`, LD20) and at `x = -log ρ`
  (`ρ` rational).
-/

namespace CatalanCore.Lai.DecayCells

open MeasureTheory Set CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Cells
  CatalanMeasure.GenD.Signed.TaylorCell CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor
  OAI.InternalCatalan Polynomial

noncomputable section

/-! ### 1. The own potential on the support -/

/-- On the support, `x ∈ [-1, 1]`: `U^ν(M + h x) = -c₀ log |h| + c₀ log 2 + Σ c_k T_k(x)/k`. -/
theorem logPotC_segMeasure_support {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    logPotC (segMeasure M h c N) (M + h * (x : ℂ)) =
      -c 0 * Real.log ‖h‖ + c 0 * Real.log 2 +
        ∑ k ∈ Finset.range N, c (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
          ((k + 1 : ℕ) : ℝ) := by
  have hmeas : Measurable fun u : ℂ => Real.log ‖(M + h * (x : ℂ)) - u‖ :=
    Real.measurable_log.comp (by fun_prop)
  unfold logPotC
  rw [integral_segMeasure hpos hmeas]
  have hsplit : ∀ θ : ℝ, Real.cos θ ≠ x →
      Real.log ‖(M + h * (x : ℂ)) - (M + h * (Real.cos θ : ℂ))‖ =
        Real.log ‖h‖ + Real.log |x - Real.cos θ| := by
    intro θ hθ
    have e : (M + h * (x : ℂ)) - (M + h * (Real.cos θ : ℂ)) = h * ((x - Real.cos θ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.log_mul (norm_ne_zero_iff.2 hh) (abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hθ)))]
  obtain ⟨hint, hval⟩ := integral_chebF_log_inside c N hx
  have hae := ae_cos_ne x hx
  have h1 : ∫ θ, chebF c N (Real.cos θ) *
      Real.log ‖(M + h * (x : ℂ)) - (M + h * (Real.cos θ : ℂ))‖ ∂arc =
      ∫ θ, (Real.log ‖h‖ * chebF c N (Real.cos θ) +
        chebF c N (Real.cos θ) * Real.log |x - Real.cos θ|) ∂arc := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    rw [hsplit θ hθ]; ring
  rw [h1, integral_add ((integrable_chebF c N).const_mul _) hint, integral_const_mul,
    integral_chebF, hval]
  have e2 : ∀ k ∈ Finset.range N, (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) /
      ((k + 1 : ℕ) : ℝ) = c (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ) := fun k _ => by ring
  rw [Finset.sum_congr rfl e2]
  ring

/-- The angle form: `x = cos φ`, `T_k (cos φ) = cos (kφ)`. -/
theorem logPotC_segMeasure_cos {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (φ : ℝ) :
    logPotC (segMeasure M h c N) (M + h * (Real.cos φ : ℂ)) =
      -c 0 * Real.log ‖h‖ + c 0 * Real.log 2 +
        ∑ k ∈ Finset.range N, c (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * φ) /
          ((k + 1 : ℕ) : ℝ) := by
  rw [logPotC_segMeasure_support hh hpos (cos_mem φ)]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [Chebyshev.T_real_cos]
  push_cast
  rfl

/-! ### 2. The own potential beyond the endpoints (real line through the segment) -/

theorem norm_ofReal_sign_exp {s : ℝ} (hs : s = 1 ∨ s = -1) (w : ℝ) :
    ‖((s * Real.exp w : ℝ) : ℂ)‖ = Real.exp w := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  rcases hs with rfl | rfl <;> simp

theorem jJ_sign_exp {s : ℝ} (hs : s = 1 ∨ s = -1) (w : ℝ) :
    jJ ((s * Real.exp w : ℝ) : ℂ) = ((s * Real.cosh w : ℝ) : ℂ) := by
  have hne : Real.exp w ≠ 0 := (Real.exp_pos w).ne'
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hr : s * Real.cosh w = (s * Real.exp w + (s * Real.exp w)⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    nlinarith [hss]
  unfold jJ
  rw [hr]
  push_cast
  ring

/-- The potential at `M + ε h cosh w`, `w > 0`, `ε = ±1`. -/
theorem logPotC_segMeasure_cosh {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℝ} (hs : s = 1 ∨ s = -1) {w : ℝ}
    (hw : 0 < w) :
    logPotC (segMeasure M h c N) (M + h * ((s * Real.cosh w : ℝ) : ℂ)) =
      -c 0 * Real.log ‖h‖ + c 0 * Real.log 2 - c 0 * w +
        ∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1) *
          Real.exp (-(((k + 1 : ℕ) : ℝ) * w)) / ((k + 1 : ℕ) : ℝ) := by
  have hn : 1 < ‖((s * Real.exp w : ℝ) : ℂ)‖ := by
    rw [norm_ofReal_sign_exp hs]; have := Real.add_one_lt_exp hw.ne'; linarith
  have hζ : ((M + h * ((s * Real.cosh w : ℝ) : ℂ)) - M) / h = jJ ((s * Real.exp w : ℝ) : ℂ) := by
    rw [jJ_sign_exp hs]; field_simp; ring
  have hjc : 1 < jc (((M + h * ((s * Real.cosh w : ℝ) : ℂ)) - M) / h) := by
    rw [hζ]; exact one_lt_jc_jJ hn
  rw [logPotC_segMeasure hh hpos hjc, hζ, jphi_jJ hn]
  rw [jR_jJ hn.le, norm_ofReal_sign_exp hs]
  have hl : Real.log (Real.exp w / 2) = w - Real.log 2 := by
    rw [Real.log_div (Real.exp_pos w).ne' (by norm_num), Real.log_exp]
  rw [hl]
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hpow : ∀ k : ℕ, ((((s * Real.exp w : ℝ) : ℂ) ^ (k + 1))⁻¹).re =
      s ^ (k + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * w)) := by
    intro k
    have e1 : (((s * Real.exp w : ℝ) : ℂ) ^ (k + 1))⁻¹ =
        ((s ^ (k + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * w)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
      congr 1
      rw [mul_pow, ← Real.exp_nat_mul, Real.exp_neg]
      have hsk : s ^ (k + 1) * s ^ (k + 1) = 1 := by rw [← mul_pow, hss, one_pow]
      have hsk0 : s ^ (k + 1) ≠ 0 := by rcases hs with rfl | rfl <;> simp
      have hex : Real.exp (((k + 1 : ℕ) : ℝ) * w) ≠ 0 := (Real.exp_pos _).ne'
      field_simp
      nlinarith [hsk]
    rw [e1, Complex.ofReal_re]
  have e2 : ∀ k ∈ Finset.range N, c (k + 1) * ((((s * Real.exp w : ℝ) : ℂ) ^ (k + 1))⁻¹).re /
      ((k + 1 : ℕ) : ℝ) = c (k + 1) * s ^ (k + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * w)) /
      ((k + 1 : ℕ) : ℝ) := fun k _ => by rw [hpow k]; ring
  rw [Finset.sum_congr rfl e2]
  ring


/-! ### 3. The own-potential towers -/

/-- The A tower: `x ↦ K0 + Σ_k (w_{k+1}/κ) cos (κ x)`, `κ = k + 1`, and its derivatives
(`cos (κ x + jπ/2)`). -/
def ownAT (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  (if j = 0 then K0 else 0) + ∑ k ∈ Finset.range N,
    w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
      Real.cos (((k + 1 : ℕ) : ℝ) * x + (j : ℝ) * (Real.pi / 2))

theorem hasDerivAt_ownAT (K0 : ℝ) (w : ℕ → ℝ) (N j : ℕ) (x : ℝ) :
    HasDerivAt (ownAT K0 w N j) (ownAT K0 w N (j + 1) x) x := by
  have hk : ∀ k ∈ Finset.range N, HasDerivAt
      (fun x => w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
        Real.cos (((k + 1 : ℕ) : ℝ) * x + (j : ℝ) * (Real.pi / 2)))
      (w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (j + 1) *
        Real.cos (((k + 1 : ℕ) : ℝ) * x + ((j + 1 : ℕ) : ℝ) * (Real.pi / 2))) x := by
    intro k _
    have h1 : HasDerivAt (fun x => ((k + 1 : ℕ) : ℝ) * x + (j : ℝ) * (Real.pi / 2))
        (((k + 1 : ℕ) : ℝ)) x := by
      simpa using ((hasDerivAt_id' x).const_mul (((k + 1 : ℕ) : ℝ))).add_const
        ((j : ℝ) * (Real.pi / 2))
    have h2 := h1.cos.const_mul (w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j)
    refine h2.congr_deriv ?_
    have : Real.cos (((k + 1 : ℕ) : ℝ) * x + ((j + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
        - Real.sin (((k + 1 : ℕ) : ℝ) * x + (j : ℝ) * (Real.pi / 2)) := by
      rw [← Real.cos_add_pi_div_two]; congr 1; push_cast; ring
    rw [this]; ring
  have hs := HasDerivAt.fun_sum hk
  have hc : HasDerivAt (fun _ : ℝ => if j = 0 then K0 else 0) 0 x := hasDerivAt_const _ _
  have h := hc.fun_add hs
  unfold ownAT
  refine h.congr_deriv ?_
  simp

theorem continuous_ownAT (K0 : ℝ) (w : ℕ → ℝ) (N j : ℕ) : Continuous (ownAT K0 w N j) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_ownAT K0 w N j x).continuousAt

theorem isTower_ownAT (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (c r : ℝ) :
    IsTower (ownAT K0 w N) c r 5 where
  cont j _ := (continuous_ownAT K0 w N j).continuousOn
  der j _ x _ := hasDerivAt_ownAT K0 w N j x

/-- The remainder bound `|ownAT 5| ≤ Σ |w_{k+1}| κ⁴`. -/
theorem abs_ownAT5_le (K0 : ℝ) (w : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    |ownAT K0 w N 5 x| ≤ ∑ k ∈ Finset.range N, |w (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 := by
  unfold ownAT
  simp only [show (5 : ℕ) ≠ 0 by norm_num, if_false, zero_add]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_of_pos hk]
  have := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * x + ((5 : ℕ) : ℝ) * (Real.pi / 2))
  have e : |w (k + 1)| / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 5 =
      |w (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 := by field_simp
  rw [e]
  exact mul_le_of_le_one_right (by positivity) this

/-- The potential of the segment on the circle through its support, as the A tower at `j = 0`. -/
theorem logPotC_eq_ownAT {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (x : ℝ) :
    logPotC (segMeasure M h c N) (M + h * (Real.cos x : ℂ)) =
      ownAT (-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) c N 0 x := by
  rw [logPotC_segMeasure_cos hh hpos]
  unfold ownAT
  simp only [if_true, Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The G tower: `K0 - c0 x` plus `Σ_k (w_{k+1} s^κ/κ) e^{-κ x}` (`s = ±1`) and its derivatives. -/
def ownGT (K0 c0 s : ℝ) (w : ℕ → ℝ) (N : ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  (if j = 0 then K0 - c0 * x else if j = 1 then -c0 else 0) + ∑ k ∈ Finset.range N,
    w (k + 1) * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ) * (-((k + 1 : ℕ) : ℝ)) ^ j *
      Real.exp (-(((k + 1 : ℕ) : ℝ) * x))

theorem hasDerivAt_ownGT (K0 c0 s : ℝ) (w : ℕ → ℝ) (N j : ℕ) (x : ℝ) :
    HasDerivAt (ownGT K0 c0 s w N j) (ownGT K0 c0 s w N (j + 1) x) x := by
  have hk : ∀ k ∈ Finset.range N, HasDerivAt
      (fun x => w (k + 1) * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ) * (-((k + 1 : ℕ) : ℝ)) ^ j *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * x)))
      (w (k + 1) * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ) * (-((k + 1 : ℕ) : ℝ)) ^ (j + 1) *
        Real.exp (-(((k + 1 : ℕ) : ℝ) * x))) x := by
    intro k _
    have h1 : HasDerivAt (fun x => -(((k + 1 : ℕ) : ℝ) * x)) (-((k + 1 : ℕ) : ℝ)) x :=
      (((hasDerivAt_id' x).const_mul (((k + 1 : ℕ) : ℝ))).neg).congr_deriv (by ring)
    have h2 := h1.exp.const_mul
      (w (k + 1) * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ) * (-((k + 1 : ℕ) : ℝ)) ^ j)
    refine h2.congr_deriv ?_
    rw [pow_succ]; ring
  have hs := HasDerivAt.fun_sum hk
  have hl : HasDerivAt (fun x : ℝ => if j = 0 then K0 - c0 * x else if j = 1 then -c0 else 0)
      (if j + 1 = 0 then K0 - c0 * x else if j + 1 = 1 then -c0 else 0) x := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using ((hasDerivAt_id' x).const_mul c0).const_sub K0
    · by_cases h1 : j = 1
      · subst h1; simpa using hasDerivAt_const x (-c0)
      · have h2 : j + 1 ≠ 1 := by omega
        have h3 : j + 1 ≠ 0 := by omega
        have h4 : j ≠ 0 := by omega
        simpa [h1, h2, h3, h4] using hasDerivAt_const x (0 : ℝ)
  have h := hl.fun_add hs
  unfold ownGT
  exact h

theorem continuous_ownGT (K0 c0 s : ℝ) (w : ℕ → ℝ) (N j : ℕ) : Continuous (ownGT K0 c0 s w N j) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_ownGT K0 c0 s w N j x).continuousAt

theorem isTower_ownGT (K0 c0 s : ℝ) (w : ℕ → ℝ) (N : ℕ) (c r : ℝ) :
    IsTower (ownGT K0 c0 s w N) c r 5 where
  cont j _ := (continuous_ownGT K0 c0 s w N j).continuousOn
  der j _ x _ := hasDerivAt_ownGT K0 c0 s w N j x

/-- The remainder bound `|ownGT 5 x| ≤ Σ |w_{k+1}| κ⁴ E_k` when `e^{-κ x} ≤ E_k`, `|s| = 1`. -/
theorem abs_ownGT5_le (K0 c0 s : ℝ) (hs : |s| = 1) (w : ℕ → ℝ) (N : ℕ) (x : ℝ) (E : ℕ → ℝ)
    (hE : ∀ k < N, Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) ≤ E k) :
    |ownGT K0 c0 s w N 5 x| ≤ ∑ k ∈ Finset.range N, |w (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 * E k := by
  unfold ownGT
  simp only [show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num, if_false, zero_add]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hkN : k < N := Finset.mem_range.1 hk
  rw [abs_mul, abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_of_pos hk0, hs,
    one_pow, mul_one, Real.abs_exp]
  have e : |w (k + 1)| / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 5 =
      |w (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (hE k hkN) (by positivity)

theorem T_eval_sign {s : ℝ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (Chebyshev.T ℝ (n : ℤ)).eval s = s ^ n := by
  rcases hs with rfl | rfl
  · simp [Chebyshev.T_eval_one]
  · have := Chebyshev.T_real_cos (n := (n : ℤ)) (θ := Real.pi)
    rw [Real.cos_pi] at this
    rw [this]
    push_cast
    exact Real.cos_nat_mul_pi n

/-- The potential beyond the endpoint along `M + s h cosh w`, `w ≥ 0`, as the G tower at `j = 0`. -/
theorem logPotC_eq_ownGT {M h : ℂ} (hh : h ≠ 0) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {s : ℝ} (hs : s = 1 ∨ s = -1) {x : ℝ}
    (hx : 0 ≤ x) :
    logPotC (segMeasure M h c N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) =
      ownGT (-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (c 0) s c N 0 x := by
  have hform : ownGT (-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (c 0) s c N 0 x =
      -c 0 * Real.log ‖h‖ + c 0 * Real.log 2 - c 0 * x +
        ∑ k ∈ Finset.range N, c (k + 1) * s ^ (k + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) /
          ((k + 1 : ℕ) : ℝ) := by
    unfold ownGT
    simp only [if_true, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hform]
  rcases hx.eq_or_lt with h0 | hpos'
  · subst h0
    have hs1 : s ∈ Icc (-1 : ℝ) 1 := by rcases hs with rfl | rfl <;> constructor <;> norm_num
    have := logPotC_segMeasure_support (M := M) hh hpos hs1
    simp only [Real.cosh_zero, mul_one, mul_zero, sub_zero, Real.exp_zero]
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [T_eval_sign hs (k + 1)]
    simp <;> ring
  · rw [logPotC_segMeasure_cosh hh hpos hs hpos']

/-! ### 4. Arms: the curves of the A and G cells -/

/-- The A arm: `γ i x = [i = 0] M + h cos (x + iπ/2)`, the derivative chain of `x ↦ M + h cos x`. -/
def armA (M h : ℂ) (i : ℕ) (x : ℝ) : ℂ :=
  (if i = 0 then M else 0) + h * ((Real.cos (x + (i : ℝ) * (Real.pi / 2)) : ℝ) : ℂ)

theorem armA_zero (M h : ℂ) (x : ℝ) : armA M h 0 x = M + h * (Real.cos x : ℂ) := by
  simp [armA]

theorem hasDerivAt_armA (M h : ℂ) (i : ℕ) (x : ℝ) :
    HasDerivAt (armA M h i) (armA M h (i + 1) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.cos (y + (i : ℝ) * (Real.pi / 2)))
      (-Real.sin (x + (i : ℝ) * (Real.pi / 2))) x := by
    simpa using ((hasDerivAt_id' x).add_const ((i : ℝ) * (Real.pi / 2))).cos
  have h2 := (h1.ofReal_comp).const_mul h
  have h3 := (hasDerivAt_const x (if i = 0 then M else 0)).add h2
  have e : armA M h i = fun y : ℝ => (if i = 0 then M else 0) +
      h * ((Real.cos (y + (i : ℝ) * (Real.pi / 2)) : ℝ) : ℂ) := rfl
  rw [e]
  refine h3.congr_deriv ?_
  have : Real.cos (x + ((i + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
      - Real.sin (x + (i : ℝ) * (Real.pi / 2)) := by
    rw [← Real.cos_add_pi_div_two]; congr 1; push_cast; ring
  simp only [armA, this]
  simp

theorem continuous_armA (M h : ℂ) (i : ℕ) : Continuous (armA M h i) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_armA M h i x).continuousAt

theorem norm_armA_le (M h : ℂ) {i : ℕ} (hi : 1 ≤ i) (x : ℝ) : ‖armA M h i x‖ ≤ ‖h‖ := by
  have hi0 : i ≠ 0 := by omega
  unfold armA
  rw [if_neg hi0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)

theorem armA_im_pos {M h : ℂ} (hM : |h.im| < M.im) (x : ℝ) : 0 < (M + h * (Real.cos x : ℂ)).im := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    add_zero]
  have := Real.abs_cos_le_one x
  have h1 : |h.im * Real.cos x| ≤ |h.im| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) this
  linarith [neg_abs_le (h.im * Real.cos x)]

/-- `cosh`/`sinh` chain for the G arm. -/
def coshT (i : ℕ) (x : ℝ) : ℝ := if i % 2 = 0 then Real.cosh x else Real.sinh x

theorem hasDerivAt_coshT (i : ℕ) (x : ℝ) : HasDerivAt (coshT i) (coshT (i + 1) x) x := by
  by_cases hi : i % 2 = 0
  · have h1 : (i + 1) % 2 ≠ 0 := by omega
    have : coshT i = Real.cosh := by funext y; simp [coshT, hi]
    rw [this]
    simpa [coshT, h1] using Real.hasDerivAt_cosh x
  · have h1 : (i + 1) % 2 = 0 := by omega
    have : coshT i = Real.sinh := by funext y; simp [coshT, hi]
    rw [this]
    simpa [coshT, h1] using Real.hasDerivAt_sinh x

/-- The G arm: `γ i x = [i = 0] M + s h coshT i x`, the chain of `x ↦ M + s h cosh x`. -/
def armG (M h : ℂ) (s : ℝ) (i : ℕ) (x : ℝ) : ℂ :=
  (if i = 0 then M else 0) + h * ((s * coshT i x : ℝ) : ℂ)

theorem armG_zero (M h : ℂ) (s x : ℝ) : armG M h s 0 x = M + h * ((s * Real.cosh x : ℝ) : ℂ) := by
  simp [armG, coshT]

theorem hasDerivAt_armG (M h : ℂ) (s : ℝ) (i : ℕ) (x : ℝ) :
    HasDerivAt (armG M h s i) (armG M h s (i + 1) x) x := by
  have h1 := (hasDerivAt_coshT i x).const_mul s
  have h2 := (h1.ofReal_comp).const_mul h
  have h3 := (hasDerivAt_const x (if i = 0 then M else 0)).add h2
  have e : armG M h s i = fun y : ℝ => (if i = 0 then M else 0) +
      h * ((s * coshT i y : ℝ) : ℂ) := rfl
  rw [e]
  refine h3.congr_deriv ?_
  simp [armG]

theorem continuous_armG (M h : ℂ) (s : ℝ) (i : ℕ) : Continuous (armG M h s i) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_armG M h s i x).continuousAt

theorem abs_coshT_le {i : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : |coshT i x| ≤ Real.cosh y := by
  have hc : Real.cosh x ≤ Real.cosh y :=
    Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]; exact hxy)
  have hs : |Real.sinh x| ≤ Real.cosh x := by
    rw [Real.sinh_eq, Real.cosh_eq, abs_le]
    constructor <;> nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
  unfold coshT
  split_ifs
  · rw [abs_of_pos (Real.cosh_pos x)]; exact hc
  · exact hs.trans hc

theorem norm_armG_le (M h : ℂ) {s : ℝ} (hs : |s| = 1) {i : ℕ} (hi : 1 ≤ i) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : ‖armG M h s i x‖ ≤ ‖h‖ * Real.cosh y := by
  have hi0 : i ≠ 0 := by omega
  unfold armG
  rw [if_neg hi0, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hs, one_mul]
  exact mul_le_mul_of_nonneg_left (abs_coshT_le hx hxy) (norm_nonneg _)

theorem armG_im_pos {M h : ℂ} {s : ℝ} (hs : |s| = 1) {y : ℝ} (hM : |h.im| * Real.cosh y < M.im)
    {x : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : 0 < (M + h * ((s * Real.cosh x : ℝ) : ℂ)).im := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    add_zero]
  have h1 : |h.im * (s * Real.cosh x)| ≤ |h.im| * Real.cosh y := by
    rw [abs_mul, abs_mul, hs, one_mul, abs_of_pos (Real.cosh_pos x)]
    exact mul_le_mul_of_nonneg_left (Real.cosh_le_cosh.2 (by
      rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]; exact hxy)) (abs_nonneg _)
  linarith [neg_abs_le (h.im * (s * Real.cosh x))]

/-- A straight line `γ 0 x = p + d x`, `γ 1 = d`, `γ i = 0` (`i ≥ 2`), for the vertical ray of the
R cells. -/
def lineC (p d : ℂ) (i : ℕ) (x : ℝ) : ℂ :=
  if i = 0 then p + d * (x : ℂ) else if i = 1 then d else 0

theorem hasDerivAt_lineC (p d : ℂ) (i : ℕ) (x : ℝ) :
    HasDerivAt (lineC p d i) (lineC p d (i + 1) x) x := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have e : lineC p d 0 = fun y : ℝ => p + d * (y : ℂ) := by funext y; simp [lineC]
    have h1 := ((hasDerivAt_id' x).ofReal_comp).const_mul d
    have h2 := h1.const_add p
    rw [e]
    simpa [lineC] using h2
  · by_cases h1 : i = 1
    · subst h1
      have e : lineC p d 1 = fun _ : ℝ => d := by funext y; simp [lineC]
      rw [e]
      simpa [lineC] using hasDerivAt_const x d
    · have h2 : i + 1 ≠ 1 := by omega
      have h3 : i + 1 ≠ 0 := by omega
      have h4 : i ≠ 0 := by omega
      have e : lineC p d i = fun _ : ℝ => (0 : ℂ) := by funext y; simp [lineC, h1, h4]
      rw [e]
      simpa [lineC, h2, h3, h4] using hasDerivAt_const x (0 : ℂ)

theorem continuous_lineC (p d : ℂ) (i : ℕ) : Continuous (lineC p d i) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_lineC p d i x).continuousAt

/-! ### 5. Cell distance data -/

theorem pole_cell_bounds {γ : ℕ → ℝ → ℂ} (hγd : ∀ i < 5, ∀ x, HasDerivAt (γ i) (γ (i + 1) x) x)
    {a ρ S : ℝ} (hS : ∀ x ∈ Icc (a - ρ) (a + ρ), ‖γ 1 x‖ ≤ S) (p : ℂ) {x : ℝ}
    (hx : x ∈ Icc (a - ρ) (a + ρ)) :
    ‖γ 0 a - p‖ - S * ρ ≤ ‖γ 0 x - p‖ ∧ ‖γ 0 x - p‖ ≤ ‖γ 0 a - p‖ + S * ρ := by
  have hd : ∀ y, HasDerivAt (γ 0) (γ 1 y) y := fun y => hγd 0 (by norm_num) y
  refine ⟨norm_sub_pole_ge hd hS hx p, ?_⟩
  have hb := norm_curve_sub_le hd hS hx
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
  have hxr : |x - a| ≤ ρ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ‖γ 0 x - p‖ ≤ ‖γ 0 a - p‖ + ‖γ 0 x - γ 0 a‖ := by
    have := norm_add_le (γ 0 a - p) (γ 0 x - γ 0 a)
    rw [show γ 0 a - p + (γ 0 x - γ 0 a) = γ 0 x - p by ring] at this
    exact this
  nlinarith [mul_le_mul_of_nonneg_left hxr hS0]

theorem abs_log_le_of_bounds {t d D L : ℝ} (hd : 0 < d) (h1 : d ≤ t) (h2 : t ≤ D)
    (hL1 : -L ≤ Real.log d) (hL2 : Real.log D ≤ L) : |Real.log t| ≤ L := by
  have ht : 0 < t := lt_of_lt_of_le hd h1
  have a1 := Real.log_le_log hd h1
  have a2 := Real.log_le_log ht h2
  rw [abs_le]
  constructor <;> linarith

/-- The data of the V part of a cell at the centre value `z = γ 0 a`: pole-distance lower bounds
`d₁ d₂ d₃` (poles `0`, `B`, `-K`), log bounds, and the remainder `TV`. -/
structure VCell (e r B K θ : ℝ) (z : ℂ) (Ym : ℕ → ℝ) (ρ TV : ℝ) where
  d1 : ℝ
  d2 : ℝ
  d3 : ℝ
  L1 : ℝ
  L2 : ℝ
  L3 : ℝ
  hd1 : 0 < d1
  hd2 : 0 < d2
  hd3 : 0 < d3
  hdc1 : d1 ≤ ‖z‖ - Ym 1 * ρ
  hdc2 : d2 ≤ ‖(B : ℂ) - z‖ - Ym 1 * ρ
  hdc3 : d3 ≤ ‖z + K‖ - Ym 1 * ρ
  hLa1 : -L1 ≤ Real.log d1
  hLb1 : Real.log (‖z‖ + Ym 1 * ρ) ≤ L1
  hLa2 : -L2 ≤ Real.log d2
  hLb2 : Real.log (‖(B : ℂ) - z‖ + Ym 1 * ρ) ≤ L2
  hLa3 : -L3 ≤ Real.log d3
  hLb3 : Real.log (‖z + K‖ + Ym 1 * ρ) ≤ L3
  hTV : fdbBound (psiDm e r θ d1 d2 d3 L1 L2 L3) Ym ≤ TV

/-- The data of a segment-potential part of a cell: distance lower bound `dlo` and remainder. -/
structure SegCell (z : ℂ) (Ym : ℕ → ℝ) (ρ : ℝ) (M h : ℂ) (c0 : ℝ) (T : ℝ) where
  dlo : ℝ
  hdlo0 : 0 < dlo
  hdlo : dlo ≤ ‖h‖ * (jc ((z - M) / h) - 1) - Ym 1 * ρ
  hT : fdbBound (fun k => ((k - 1).factorial : ℝ) * c0 / dlo ^ k) Ym ≤ T

/-- The analytic form `κ + Re Ψ̃` of the field `V` (equal to `vField` for `Im s > 0`, W1(i)); it is
what a cell bounds, so cells reaching past the vertex are covered. -/
def vAnal (e r B K θ : ℝ) (s : ℂ) : ℝ :=
  (r * (K * Real.log K - K) - e * (B * Real.log B - B)) + (psiT e r B K θ s).re

theorem vAnal_eq_vField (e r B K θ : ℝ) {s : ℂ} (hs : 0 < s.im) :
    vAnal e r B K θ s = vField e r B K θ s := (vField_eq_psi e r B K θ hs).symm

/-! ### 6. The generic cell theorem -/

/-- **LD18, the generic cell theorem.**  Along an analytic curve `γ` in the upper half plane, the
field `V + w₁ U₁ + w₂ U₂` (`V` the three-pole field, `U₁` an arbitrary real function with an
order-5 tower `f₁`, `U₂` the potential of the segment `(M₂, h₂, c₂)`) is at most `ℓ` on the cell
`[a - ρ, a + ρ]` as soon as the rational Taylor-model check `wedgeCellOk` passes for enclosures
`tq ± te` of the five point values of the combined tower and a remainder `TR`. -/
theorem wedgeField_cell_sound (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r)
    {γ : ℕ → ℝ → ℂ} (hγd : ∀ i < 5, ∀ x, HasDerivAt (γ i) (γ (i + 1) x) x)
    (hγc : Continuous (γ 5)) {a ρ : ℝ} {Ym : ℕ → ℝ}
    (hY : ∀ x ∈ Icc (a - ρ) (a + ρ), ∀ i, 1 ≤ i → i ≤ 5 → ‖γ i x‖ ≤ Ym i)
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (γ 0 x))
    {TV T1 T2 : ℝ} (hV : VCell e r B K θ (γ 0 a) Ym ρ TV)
    {U₁ : ℝ → ℝ} {f₁ : ℕ → ℝ → ℝ} (hf₁ : IsTower f₁ a ρ 5)
    (hU₁ : ∀ x ∈ Icc (a - ρ) (a + ρ), U₁ x = f₁ 0 x)
    (hT1 : ∀ x ∈ Icc (a - ρ) (a + ρ), |f₁ 5 x| ≤ T1)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x) (hX : SegCell (γ 0 a) Ym ρ M₂ h₂ (c₂ 0) T2)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B)) γ) f₁
        (potT M₂ h₂ c₂ N₂ γ) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * T1 + |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ),
      vAnal e r B K θ (γ 0 x) + w₁ * U₁ x +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (γ 0 x) ≤ (ℓ : ℝ) := by
  set κV : ℝ := r * (K * Real.log K - K) - e * (B * Real.log B - B) with hκV
  have hS : ∀ x ∈ Icc (a - ρ) (a + ρ), ‖γ 1 x‖ ≤ Ym 1 := fun x hx =>
    hY x hx 1 le_rfl (by norm_num)
  have hVt := isTower_vTower e r B K θ κV hγd hγc hdom
  have hdl : ∀ x ∈ Icc (a - ρ) (a + ρ), hX.dlo ≤ ‖h₂‖ * (jc ((γ 0 x - M₂) / h₂) - 1) :=
    fun x hx => dlo_cell hh₂ (fun y => hγd 0 (by norm_num) y) hS hX.hdlo hx
  have hreg : ∀ x ∈ Icc (a - ρ) (a + ρ), 1 < jc ((γ 0 x - M₂) / h₂) := fun x hx =>
    one_lt_jc_of_dlo hh₂ hX.hdlo0 (hdl x hx)
  have hXt := isTower_potT hh₂ hpos₂ hγd hγc hreg
  have hf := isTower_wedgeTower (w₁ := w₁) (w₂ := w₂) hVt hf₁ hXt
  have hTRx : ∀ x ∈ Icc (a - ρ) (a + ρ),
      |wedgeTower (vTower e r B K θ κV γ) f₁ (potT M₂ h₂ c₂ N₂ γ) w₁ w₂ 5 x| ≤ (TR : ℝ) := by
    intro x hx
    obtain ⟨p1l, p1u⟩ := pole_cell_bounds hγd hS 0 hx
    obtain ⟨p2l, p2u⟩ := pole_cell_bounds hγd hS (B : ℂ) hx
    obtain ⟨p3l, p3u⟩ := pole_cell_bounds hγd hS (-(K : ℂ)) hx
    simp only [sub_zero, sub_neg_eq_add] at p1l p1u p3l p3u
    rw [norm_sub_rev (γ 0 a) (B : ℂ), norm_sub_rev (γ 0 x) (B : ℂ)] at p2l p2u
    have hv := abs_vTower5_le e r B K θ κV he hr hV.hd1 hV.hd2 hV.hd3
      (hV.hdc1.trans p1l) (hV.hdc2.trans p2l) (hV.hdc3.trans p3l)
      (abs_log_le_of_bounds hV.hd1 (hV.hdc1.trans p1l) p1u hV.hLa1 hV.hLb1)
      (abs_log_le_of_bounds hV.hd2 (hV.hdc2.trans p2l) p2u hV.hLa2 hV.hLb2)
      (abs_log_le_of_bounds hV.hd3 (hV.hdc3.trans p3l) p3u hV.hLa3 hV.hLb3) (hY x hx)
    have hc := abs_potT5_le hh₂ hpos₂ (hreg x hx) hX.hdlo0 (hdl x hx) (hY x hx)
    have hw := abs_wedgeTower5_le (w₁ := w₁) (w₂ := w₂) hv (hT1 x hx) hc
    have hT2 := hX.hT
    have hTV := hV.hTV
    have hm : |w₂| * fdbBound (fun k => ((k - 1).factorial : ℝ) * c₂ 0 / hX.dlo ^ k) Ym ≤
        |w₂| * T2 := mul_le_mul_of_nonneg_left hT2 (abs_nonneg _)
    linarith
  have hrq' : (rq : ℝ) = ρ := hrq
  have key := wedgeCellOk_sound hf hrq' hTenc hTRx hok
  intro x hx
  have h0 := key x hx
  have e0 : wedgeTower (vTower e r B K θ κV γ) f₁ (potT M₂ h₂ c₂ N₂ γ) w₁ w₂ 0 x =
      vAnal e r B K θ (γ 0 x) + w₁ * U₁ x +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (γ 0 x) := by
    unfold wedgeTower
    rw [hU₁ x hx]
    simp [vTower, reTower, potT, hκV, vAnal]
  rw [← e0]
  exact h0


/-! ### 7. Enclosures of the combined tower from the three components -/

theorem wedgeTower_enc {fV f₁ f₂ : ℕ → ℝ → ℝ} {a : ℝ} (w₁ w₂ : ℚ)
    {tqV teV tq1 te1 tq2 te2 : ℕ → ℚ} {j : ℕ}
    (hV : |fV j a - (tqV j : ℝ)| ≤ (teV j : ℝ)) (h1 : |f₁ j a - (tq1 j : ℝ)| ≤ (te1 j : ℝ))
    (h2 : |f₂ j a - (tq2 j : ℝ)| ≤ (te2 j : ℝ)) :
    |wedgeTower fV f₁ f₂ (w₁ : ℝ) (w₂ : ℝ) j a -
        ((tqV j + w₁ * tq1 j + w₂ * tq2 j : ℚ) : ℝ)| ≤
      ((teV j + |w₁| * te1 j + |w₂| * te2 j : ℚ) : ℝ) := by
  unfold wedgeTower
  push_cast
  have e : fV j a + (w₁ : ℝ) * f₁ j a + (w₂ : ℝ) * f₂ j a -
      ((tqV j : ℝ) + (w₁ : ℝ) * (tq1 j : ℝ) + (w₂ : ℝ) * (tq2 j : ℝ)) =
      (fV j a - (tqV j : ℝ)) + (w₁ : ℝ) * (f₁ j a - (tq1 j : ℝ)) +
        (w₂ : ℝ) * (f₂ j a - (tq2 j : ℝ)) := by ring
  rw [e]
  have a1 : |(w₁ : ℝ) * (f₁ j a - (tq1 j : ℝ))| ≤ |(w₁ : ℝ)| * (te1 j : ℝ) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have a2 : |(w₂ : ℝ) * (f₂ j a - (tq2 j : ℝ))| ≤ |(w₂ : ℝ)| * (te2 j : ℝ) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc _ ≤ |(fV j a - (tqV j : ℝ)) + (w₁ : ℝ) * (f₁ j a - (tq1 j : ℝ))| +
        |(w₂ : ℝ) * (f₂ j a - (tq2 j : ℝ))| := abs_add_le _ _
    _ ≤ |fV j a - (tqV j : ℝ)| + |(w₁ : ℝ) * (f₁ j a - (tq1 j : ℝ))| +
        |(w₂ : ℝ) * (f₂ j a - (tq2 j : ℝ))| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

/-! ### 8. The three kinds of cell -/

/-- **A cells** (on the support, `s = M + h cos φ`): own potential by the cosine series. -/
theorem cellA_sound (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {M h : ℂ} (hh : h ≠ 0)
    {cf : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF cf N x) {a ρ : ℝ}
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (M + h * (Real.cos x : ℂ)))
    {TV T2 : ℝ} (hV : VCell e r B K θ (armA M h 0 a) (fun _ => ‖h‖) ρ TV)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x)
    (hX : SegCell (armA M h 0 a) (fun _ => ‖h‖) ρ M₂ h₂ (c₂ 0) T2)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B))
          (armA M h))
        (ownAT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) cf N)
        (potT M₂ h₂ c₂ N₂ (armA M h)) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * (∑ k ∈ Finset.range N, |cf (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4) +
      |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ),
      vAnal e r B K θ (M + h * (Real.cos x : ℂ)) +
        w₁ * logPotC (segMeasure M h cf N) (M + h * (Real.cos x : ℂ)) +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * (Real.cos x : ℂ)) ≤ (ℓ : ℝ) := by
  have key := wedgeField_cell_sound e r B K θ w₁ w₂ he hr (γ := armA M h)
    (fun i _ x => hasDerivAt_armA M h i x) (continuous_armA M h 5) (a := a) (ρ := ρ)
    (Ym := fun _ => ‖h‖) (fun x _ i hi _ => norm_armA_le M h hi x)
    (fun x hx => by rw [armA_zero]; exact hdom x hx) hV
    (U₁ := fun x => logPotC (segMeasure M h cf N) (M + h * (Real.cos x : ℂ)))
    (f₁ := ownAT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) cf N)
    (isTower_ownAT _ cf N a ρ) (fun x _ => logPotC_eq_ownAT hh hpos x)
    (fun x _ => abs_ownAT5_le _ cf N x) hh₂ hpos₂ hX hrq hTenc hTR hok
  intro x hx
  have := key x hx
  rw [armA_zero] at this
  exact this

/-- **G cells** (beyond an endpoint of the support, `s = M + ε h cosh w`, `w ≥ 0`): own potential
by the exponential series. -/
theorem cellG_sound (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) {M h : ℂ} (hh : h ≠ 0)
    {cf : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF cf N x) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {a ρ whi : ℝ} (ha : 0 ≤ a - ρ) (hwhi : a + ρ ≤ whi)
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (M + h * ((s * Real.cosh x : ℝ) : ℂ)))
    {TV T2 : ℝ}
    (hV : VCell e r B K θ (armG M h s 0 a) (fun _ => ‖h‖ * Real.cosh whi) ρ TV)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x)
    (hX : SegCell (armG M h s 0 a) (fun _ => ‖h‖ * Real.cosh whi) ρ M₂ h₂ (c₂ 0) T2)
    {E : ℕ → ℝ} (hE : ∀ k < N, Real.exp (-(((k + 1 : ℕ) : ℝ) * (a - ρ))) ≤ E k)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B))
          (armG M h s))
        (ownGT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) (cf 0) s cf N)
        (potT M₂ h₂ c₂ N₂ (armG M h s)) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * (∑ k ∈ Finset.range N, |cf (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 * E k) +
      |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ),
      vAnal e r B K θ (M + h * ((s * Real.cosh x : ℝ) : ℂ)) +
        w₁ * logPotC (segMeasure M h cf N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * ((s * Real.cosh x : ℝ) : ℂ)) ≤ (ℓ : ℝ) := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hx0 : ∀ x ∈ Icc (a - ρ) (a + ρ), 0 ≤ x := fun x hx => ha.trans hx.1
  have key := wedgeField_cell_sound e r B K θ w₁ w₂ he hr (γ := armG M h s)
    (fun i _ x => hasDerivAt_armG M h s i x) (continuous_armG M h s 5) (a := a) (ρ := ρ)
    (Ym := fun _ => ‖h‖ * Real.cosh whi)
    (fun x hx i hi _ => norm_armG_le M h habs hi (hx0 x hx) (hx.2.trans hwhi))
    (fun x hx => by rw [armG_zero]; exact hdom x hx) hV
    (U₁ := fun x => logPotC (segMeasure M h cf N) (M + h * ((s * Real.cosh x : ℝ) : ℂ)))
    (f₁ := ownGT (-cf 0 * Real.log ‖h‖ + cf 0 * Real.log 2) (cf 0) s cf N)
    (isTower_ownGT _ _ s cf N a ρ) (fun x hx => logPotC_eq_ownGT hh hpos hs (hx0 x hx))
    (fun x hx => abs_ownGT5_le _ _ s habs cf N x E (fun k hk =>
      (Real.exp_le_exp.2 (by nlinarith [hx.1, (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))])).trans
        (hE k hk)))
    hh₂ hpos₂ hX hrq hTenc hTR hok
  intro x hx
  have := key x hx
  rw [armG_zero] at this
  exact this

/-- **R cells** (the vertical ray `γ x = p + d x`, `‖d‖ = 1`): both potentials are segment
potentials off their segments. -/
theorem cellR_sound (e r B K θ w₁ w₂ : ℝ) (he : 0 ≤ e) (hr : 0 ≤ r) (p d : ℂ) (hd : ‖d‖ = 1)
    {a ρ : ℝ} {TV T1 T2 : ℝ}
    (hdom : ∀ x ∈ Icc (a - ρ) (a + ρ), psiDom B K (p + d * (x : ℂ)))
    (hV : VCell e r B K θ (lineC p d 0 a) (fun i => if i = 1 then 1 else 0) ρ TV)
    {M₁ h₁ : ℂ} (hh₁ : h₁ ≠ 0) {c₁ : ℕ → ℝ} {N₁ : ℕ}
    (hpos₁ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₁ N₁ x)
    (hX₁ : SegCell (lineC p d 0 a) (fun i => if i = 1 then 1 else 0) ρ M₁ h₁ (c₁ 0) T1)
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x)
    (hX₂ : SegCell (lineC p d 0 a) (fun i => if i = 1 then 1 else 0) ρ M₂ h₂ (c₂ 0) T2)
    {tq te : ℕ → ℚ} {TR rq ℓ : ℚ} (hrq : (rq : ℝ) = ρ)
    (hTenc : ∀ j ≤ 4,
      |wedgeTower (vTower e r B K θ (r * (K * Real.log K - K) - e * (B * Real.log B - B))
          (lineC p d))
        (potT M₁ h₁ c₁ N₁ (lineC p d))
        (potT M₂ h₂ c₂ N₂ (lineC p d)) w₁ w₂ j a - (tq j : ℝ)| ≤ (te j : ℝ))
    (hTR : TV + |w₁| * T1 + |w₂| * T2 ≤ (TR : ℝ))
    (hok : wedgeCellOk tq te TR rq ℓ = true) :
    ∀ x ∈ Icc (a - ρ) (a + ρ),
      vAnal e r B K θ (p + d * (x : ℂ)) +
        w₁ * logPotC (segMeasure M₁ h₁ c₁ N₁) (p + d * (x : ℂ)) +
        w₂ * logPotC (segMeasure M₂ h₂ c₂ N₂) (p + d * (x : ℂ)) ≤ (ℓ : ℝ) := by
  have hγd : ∀ i < 5, ∀ x, HasDerivAt (lineC p d i) (lineC p d (i + 1) x) x :=
    fun i _ x => hasDerivAt_lineC p d i x
  have hY : ∀ x ∈ Icc (a - ρ) (a + ρ), ∀ i, 1 ≤ i → i ≤ 5 →
      ‖lineC p d i x‖ ≤ (fun i : ℕ => if i = 1 then (1 : ℝ) else 0) i := by
    intro x _ i hi _
    by_cases h1 : i = 1
    · subst h1; simp [lineC, hd]
    · have h0 : i ≠ 0 := by omega
      simp [lineC, h1, h0]
  have hS : ∀ x ∈ Icc (a - ρ) (a + ρ), ‖lineC p d 1 x‖ ≤ 1 := fun x hx => by
    simpa using hY x hx 1 le_rfl (by norm_num)
  have hdl : ∀ x ∈ Icc (a - ρ) (a + ρ), hX₁.dlo ≤ ‖h₁‖ * (jc ((lineC p d 0 x - M₁) / h₁) - 1) :=
    fun x hx => dlo_cell hh₁ (fun y => hγd 0 (by norm_num) y) (S := 1) hS
      (by simpa using hX₁.hdlo) hx
  have hreg : ∀ x ∈ Icc (a - ρ) (a + ρ), 1 < jc ((lineC p d 0 x - M₁) / h₁) := fun x hx =>
    one_lt_jc_of_dlo hh₁ hX₁.hdlo0 (hdl x hx)
  have key := wedgeField_cell_sound e r B K θ w₁ w₂ he hr (γ := lineC p d) hγd
    (continuous_lineC p d 5) (a := a) (ρ := ρ) (Ym := fun i => if i = 1 then 1 else 0) hY
    (fun x hx => by simpa [lineC] using hdom x hx) hV
    (U₁ := fun x => logPotC (segMeasure M₁ h₁ c₁ N₁) (lineC p d 0 x))
    (f₁ := potT M₁ h₁ c₁ N₁ (lineC p d))
    (isTower_potT hh₁ hpos₁ hγd (continuous_lineC p d 5) hreg)
    (fun x _ => by simp [potT])
    (fun x hx => (abs_potT5_le hh₁ hpos₁ (hreg x hx) hX₁.hdlo0 (hdl x hx) (hY x hx)).trans
      hX₁.hT)
    hh₂ hpos₂ hX₂ hrq hTenc hTR hok
  intro x hx
  simpa [lineC] using key x hx


/-! ### 9. Point values of the own towers at table centres (enclosures for the data side) -/

theorem cast_ite_q (p : Prop) [Decidable p] (a b : ℚ) :
    (((if p then a else b : ℚ)) : ℝ) = if p then (a : ℝ) else (b : ℝ) := by
  split_ifs <;> rfl

open CatalanCore.Lai.DecayTrig in
/-- The rational point value of the A tower at a table centre `x = π n / 128`, with `cos` taken from
the checked table (`cosTm`): `cos (κ x + jπ/2) = cos (π (κ n + 64 j) / 128)`. -/
def ownATq (K0q : ℚ) (wq : ℕ → ℚ) (N j n : ℕ) : ℚ :=
  (if j = 0 then K0q else 0) + ∑ k ∈ Finset.range N,
    wq (k + 1) / ((k + 1 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) ^ j * cosTm ((k + 1) * n + 64 * j)

open CatalanCore.Lai.DecayTrig in
/-- The error bound of `ownATq`. -/
def ownATe (eK : ℚ) (wq : ℕ → ℚ) (N j : ℕ) : ℚ :=
  (if j = 0 then eK else 0) + ∑ k ∈ Finset.range N,
    |wq (k + 1) / ((k + 1 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ) ^ j| * trigE

open CatalanCore.Lai.DecayTrig in
/-- **LD20 consumer.**  At a dyadic centre `x = π n / 128` the A tower is enclosed by `ownATq`, with
error `ownATe`, from an enclosure `K0q ± eK` of the constant and exact rational weights. -/
theorem ownAT_enc {K0 : ℝ} {K0q eK : ℚ} (hK0 : |K0 - (K0q : ℝ)| ≤ (eK : ℝ)) {w : ℕ → ℝ}
    {wq : ℕ → ℚ} (N : ℕ) (hw : ∀ k < N, (wq (k + 1) : ℝ) = w (k + 1)) (j n : ℕ) :
    |ownAT K0 w N j (Real.pi * (n : ℝ) / 128) - ((ownATq K0q wq N j n : ℚ) : ℝ)| ≤
      ((ownATe eK wq N j : ℚ) : ℝ) := by
  have hterm : ∀ k ∈ Finset.range N,
      |w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          Real.cos (((k + 1 : ℕ) : ℝ) * (Real.pi * (n : ℝ) / 128) + (j : ℝ) * (Real.pi / 2)) -
        (wq (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          (cosTm ((k + 1) * n + 64 * j) : ℝ)| ≤
      |(wq (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j| * (trigE : ℝ) := by
    intro k hk
    have hkN := Finset.mem_range.1 hk
    rw [← hw k hkN]
    have hc : |Real.cos (Real.pi * (((k + 1) * n + 64 * j : ℕ) : ℝ) / 128) -
        (cosTm ((k + 1) * n + 64 * j) : ℝ)| ≤ (trigE : ℝ) := (trig_enc_nat _).1
    have e : Real.cos (((k + 1 : ℕ) : ℝ) * (Real.pi * (n : ℝ) / 128) + (j : ℝ) * (Real.pi / 2)) =
        Real.cos (Real.pi * (((k + 1) * n + 64 * j : ℕ) : ℝ) / 128) := by
      congr 1; push_cast; ring
    rw [e, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have hK : |(if j = 0 then K0 else 0) - (((if j = 0 then K0q else 0 : ℚ)) : ℝ)| ≤
      (((if j = 0 then eK else 0 : ℚ)) : ℝ) := by
    by_cases hj : j = 0 <;> simp [hj, hK0]
  unfold ownAT ownATq ownATe
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_abs, cast_ite_q, Rat.cast_zero, Rat.cast_neg]
  have e : ((if j = 0 then K0 else 0) + ∑ k ∈ Finset.range N,
        w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          Real.cos (((k + 1 : ℕ) : ℝ) * (Real.pi * (n : ℝ) / 128) + (j : ℝ) * (Real.pi / 2))) -
      ((if j = 0 then (K0q : ℝ) else 0) + ∑ k ∈ Finset.range N,
        (wq (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          (cosTm ((k + 1) * n + 64 * j) : ℝ)) =
      ((if j = 0 then K0 else 0) - (if j = 0 then (K0q : ℝ) else 0)) + ∑ k ∈ Finset.range N,
        (w (k + 1) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          Real.cos (((k + 1 : ℕ) : ℝ) * (Real.pi * (n : ℝ) / 128) + (j : ℝ) * (Real.pi / 2)) -
        (wq (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j *
          (cosTm ((k + 1) * n + 64 * j) : ℝ)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  have hK' : |(if j = 0 then K0 else 0) - (if j = 0 then (K0q : ℝ) else 0)| ≤
      (if j = 0 then (eK : ℝ) else 0) := by
    by_cases hj : j = 0 <;> simp [hj, hK0]
  calc _ ≤ |(if j = 0 then K0 else 0) - (if j = 0 then (K0q : ℝ) else 0)| +
        |∑ k ∈ Finset.range N, _| := abs_add_le _ _
    _ ≤ (if j = 0 then (eK : ℝ) else 0) + ∑ k ∈ Finset.range N,
        |(wq (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ j| * (trigE : ℝ) :=
      add_le_add hK' ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm))
    _ = _ := rfl

/-- The rational point value of the G tower at `x = -log ρ` (`ρ` rational, so `e^{-κ x} = ρ^κ`
exactly), from an enclosure `lq ± el` of `log ρ`. -/
def ownGTq (K0q c0q sq : ℚ) (wq : ℕ → ℚ) (N j : ℕ) (ρq lq : ℚ) : ℚ :=
  (if j = 0 then K0q + c0q * lq else if j = 1 then -c0q else 0) + ∑ k ∈ Finset.range N,
    wq (k + 1) * sq ^ (k + 1) / ((k + 1 : ℕ) : ℚ) * (-((k + 1 : ℕ) : ℚ)) ^ j * ρq ^ (k + 1)

theorem ownGT_enc_rho {K0 c0 s : ℝ} {K0q eK c0q sq ρq lq el : ℚ} {w : ℕ → ℝ} {wq : ℕ → ℚ} (N : ℕ)
    (hK0 : |K0 - (K0q : ℝ)| ≤ (eK : ℝ)) (hc0 : (c0q : ℝ) = c0) (hs : (sq : ℝ) = s)
    (hw : ∀ k < N, (wq (k + 1) : ℝ) = w (k + 1)) (hρ : 0 < (ρq : ℝ))
    (hl : |Real.log (ρq : ℝ) - (lq : ℝ)| ≤ (el : ℝ)) (j : ℕ) :
    |ownGT K0 c0 s w N j (-Real.log (ρq : ℝ)) - ((ownGTq K0q c0q sq wq N j ρq lq : ℚ) : ℝ)| ≤
      (if j = 0 then (eK : ℝ) + |c0| * (el : ℝ) else 0) := by
  have hexp : ∀ k : ℕ, Real.exp (-(((k + 1 : ℕ) : ℝ) * -Real.log (ρq : ℝ))) = (ρq : ℝ) ^ (k + 1) := by
    intro k
    rw [show -(((k + 1 : ℕ) : ℝ) * -Real.log (ρq : ℝ)) = ((k + 1 : ℕ) : ℝ) * Real.log (ρq : ℝ) by
      ring, Real.exp_nat_mul, Real.exp_log hρ]
  have hsum : ∑ k ∈ Finset.range N, w (k + 1) * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
        (-((k + 1 : ℕ) : ℝ)) ^ j * Real.exp (-(((k + 1 : ℕ) : ℝ) * -Real.log (ρq : ℝ))) =
      ∑ k ∈ Finset.range N, (wq (k + 1) : ℝ) * (sq : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
        (-((k + 1 : ℕ) : ℝ)) ^ j * (ρq : ℝ) ^ (k + 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hexp k, hw k (Finset.mem_range.1 hk), hs]
  unfold ownGT ownGTq
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_abs, cast_ite_q, Rat.cast_zero, Rat.cast_neg]
  rw [hsum, ← hc0]
  generalize (∑ k ∈ Finset.range N, (wq (k + 1) : ℝ) * (sq : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) *
    (-((k + 1 : ℕ) : ℝ)) ^ j * (ρq : ℝ) ^ (k + 1)) = S
  by_cases hj : j = 0
  · subst hj
    simp only [if_true]
    have e : (K0 - (c0q : ℝ) * -Real.log (ρq : ℝ) + S) - ((K0q : ℝ) + (c0q : ℝ) * (lq : ℝ) + S) =
        (K0 - K0q) + (c0q : ℝ) * (Real.log (ρq : ℝ) - lq) := by ring
    rw [e]
    calc _ ≤ |K0 - (K0q : ℝ)| + |(c0q : ℝ) * (Real.log (ρq : ℝ) - lq)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add hK0 (mul_le_mul_of_nonneg_left hl (abs_nonneg _))
  · simp only [hj, if_false]
    by_cases h1 : j = 1
    · simp [h1]
    · simp [h1]

end

end CatalanCore.Lai.DecayCells
