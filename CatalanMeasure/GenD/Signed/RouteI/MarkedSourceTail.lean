module

public import CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section
set_option Elab.async false

/-!
# C5 `MarkedSourceTail`: C53 source soundness, generic in the source data

For an admissible source and a finite signed profile bound to it (`Profile.OK`), the physical
difference `Dphys S x` is at most `chebSum p dP (2|x|-1) + tail` on the sign-`σ` part of `rowDom`
(`Dphys_le_chebSum`), hence `SourceMajorant S σ p dP tail` (`sourceMajorant_of_profile`).

No boundary Fourier series is used. The certificate only needs finite truncations:

* The only series is Clausen's, `∫₀^v log|2 sin(w/2)| dw = -∑ sin(n v)/n²`
  (`Cl_eq`, Taylor inside the disc plus dominated convergence, absolutely convergent). Its partial
  sums give `GN_bound`, the kernel `κ_N(d) = 1/max(1,Nd)` of the truncation tail.
* Direct kernel: integration by parts in `θ`, `s = cos²(θ/2)`, `Y(θ) = s + 1/s`, gives
  `seg_direct`; summing over the profile the boundary terms collapse to the atoms and
  `dir_stream` is the signed bounded-variation tail `(2/N) dirV`.
* Every other kernel is `log‖1 - 2 q z + q²‖` on a curve with `Yq (q τ) = κ τ` (`QCurve`), truncated
  by Mathlib's Taylor remainder (`qker_trunc`). Reflection uses the composed S19 beta tail
  (`refl_seg`, `betaT`); the opposite direct, opposite reflection and column curves use
  a radius `qm` per segment (`analytic_seg`), certified by the Joukowski lemmas `qm_D`, `qm_O`, `qm_C`.
  The column curve is real-radical (`qC`).
* `moment_re`, `int_log1p`, `int_logq`, `cheb_moment` turn every coefficient into an exact endpoint
  primitive; only real parts of the log seeds enter (`Mq_re`, `Lplus_re`, `Lqprim_re`, `QS`).

Finite layer: `dirV_le_of_bins` (half-open bins, closed form `binUp` via `b(s)`),
`conv_guard` (packed convolution, no carry, one guard mask), `dirV_le_of_packed`,
`integral_log_sub_eq_Phi` (`Φ`), the ledger `rec1_err`, `rec2_err`, `recT_err`, `evE_sub_le`,
`l1dist_strm_le`, `idealL_eq`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

noncomputable section

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval

/-! ### The Clausen primitive of the boundary kernel -/

/-- The boundary kernel `log|2 sin(w/2)|` (at the zeros of the sine, a null set, the value is
irrelevant). -/
def lsin (w : ℝ) : ℝ := Real.log (Real.sin (w / 2)) + Real.log 2

theorem log_sin_half_int (a b : ℝ) :
    IntervalIntegrable (fun w => Real.log (Real.sin (w / 2))) volume a b := by
  have h3 := (intervalIntegrable_log_sin (a := a / 2) (b := b / 2)).comp_mul_left (c := 1 / 2)
  have e2 : (a / 2) / (1 / 2 : ℝ) = a := by ring
  have e3 : (b / 2) / (1 / 2 : ℝ) = b := by ring
  rw [e2, e3] at h3
  refine h3.congr ?_
  intro w _
  simp only [Function.comp]
  congr 2
  ring

theorem lsin_int (a b : ℝ) : IntervalIntegrable lsin volume a b :=
  (log_sin_half_int a b).add intervalIntegrable_const

/-- The Clausen primitive. -/
def Cl (v : ℝ) : ℝ := ∫ w in (0 : ℝ)..v, lsin w

/-- Regularised kernel. -/
def reg (r w : ℝ) : ℝ := (1 / 2) * Real.log (1 - 2 * r * Real.cos w + r ^ 2)

theorem reg_arg (r w : ℝ) :
    1 - 2 * r * Real.cos w + r ^ 2 = (1 - r) ^ 2 + 4 * r * Real.sin (w / 2) ^ 2 := by
  have h : Real.cos w = 1 - 2 * Real.sin (w / 2) ^ 2 := by
    have := Real.cos_two_mul (w / 2)
    have e : 2 * (w / 2) = w := by ring
    rw [e] at this
    rw [this]
    have := Real.sin_sq_add_cos_sq (w / 2)
    nlinarith
  rw [h]; ring

theorem reg_arg_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (w : ℝ) :
    0 < 1 - 2 * r * Real.cos w + r ^ 2 := by
  rw [reg_arg]
  have : 0 < (1 - r) ^ 2 := by
    have : 0 < 1 - r := by linarith
    positivity
  positivity

theorem reg_hasSum {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (w : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1))
      (-(reg r w)) := by
  set z : ℂ := (r : ℂ) * Complex.exp (w * Complex.I) with hz
  have hzn : ‖z‖ = r := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I]
    simp [abs_of_nonneg h0]
  have hs := Complex.hasSum_taylorSeries_neg_log (z := z) (by rw [hzn]; exact h1)
  have hs1 := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n : ℂ)) 1).mpr hs
  have hre := Complex.hasSum_re hs1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero, sub_zero]
    at hre
  have hterm : ∀ n : ℕ, ((z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))).re =
      r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1) := by
    intro n
    have e1 : z ^ (n + 1) = ((r ^ (n + 1) : ℝ) : ℂ) *
        Complex.exp ((((n : ℝ) + 1) * w : ℝ) * Complex.I) := by
      rw [hz, mul_pow, ← Complex.exp_nat_mul]
      push_cast
      congr 2
      ring
    have e2 : (((n + 1 : ℕ) : ℂ)) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hlog : (-(Complex.log (1 - z))).re = -(reg r w) := by
    rw [Complex.neg_re, Complex.log_re]
    congr 1
    have hn : ‖(1 : ℂ) - z‖ ^ 2 = 1 - 2 * r * Real.cos w + r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have e1 : z.re = r * Real.cos w := by
        rw [hz, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      have e2 : z.im = r * Real.sin w := by
        rw [hz, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, e1, e2]
      have := Real.sin_sq_add_cos_sq w
      nlinarith
    unfold reg
    rw [← hn, Real.log_pow]
    push_cast
    ring
  simp only [hterm, Complex.zero_re, sub_zero, hlog] at hre
  simpa using hre

theorem term_integral (r v : ℝ) (n : ℕ) :
    ∫ w in (0 : ℝ)..v, r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1) =
      r ^ (n + 1) * (Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : ∀ w, r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1) =
      (r ^ (n + 1) / ((n : ℝ) + 1)) * Real.cos (((n : ℝ) + 1) * w) := fun w => by ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hn,
    integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
  field_simp

theorem reg_integral {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (v : ℝ) :
    HasSum (fun n : ℕ => r ^ (n + 1) * (Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2))
      (∫ w in (0 : ℝ)..v, -(reg r w)) := by
  have hb : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one h0 h1).mul_left r
    refine this.congr ?_
    intro n; ring
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := v)
    (μ := volume) (f := fun w => -(reg r w))
    (F := fun (n : ℕ) w => r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1))
    (fun n _ => r ^ (n + 1)) ?_ ?_ ?_ ?_ ?_
  · simpa only [term_integral] using key
  · intro n
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · intro n
    refine Eventually.of_forall fun w _ => ?_
    rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg h0 _), abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have hc := Real.abs_cos_le_one (((n : ℝ) + 1) * w)
    have hp : (0 : ℝ) ≤ r ^ (n + 1) := pow_nonneg h0 _
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    calc r ^ (n + 1) * |Real.cos (((n : ℝ) + 1) * w)| / ((n : ℝ) + 1)
        ≤ r ^ (n + 1) * |Real.cos (((n : ℝ) + 1) * w)| :=
          div_le_self (by positivity) hn1
      _ ≤ r ^ (n + 1) := mul_le_of_le_one_right hp hc
  · exact Eventually.of_forall fun _ _ => hb
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun w _ => reg_hasSum h0 h1 w

theorem sin_half_zero_null : ∀ᵐ w : ℝ ∂(volume : Measure ℝ), Real.sin (w / 2) ≠ 0 := by
  have hc : ({w : ℝ | Real.sin (w / 2) = 0}).Countable := by
    refine (Set.countable_range (fun k : ℤ => 2 * ((k : ℝ) * π))).mono ?_
    intro w hw
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hw
    exact ⟨k, by simp only; rw [hk]; ring⟩
  have := hc.ae_notMem volume
  filter_upwards [this] with w hw
  exact hw

theorem reg_bound {r w : ℝ} (hr : 1 / 2 ≤ r) (h1 : r < 1) (hs : Real.sin (w / 2) ≠ 0) :
    |reg r w| ≤ |Real.log (Real.sin (w / 2))| + Real.log 2 := by
  set S := Real.sin (w / 2) with hS
  set A := 1 - 2 * r * Real.cos w + r ^ 2 with hA
  have hA2 : A = (1 - r) ^ 2 + 4 * r * S ^ 2 := reg_arg r w
  have hS2 : S ^ 2 ≤ 1 := by
    have := Real.sin_sq_add_cos_sq (w / 2)
    nlinarith [sq_nonneg (Real.cos (w / 2))]
  have hSpos : 0 < S ^ 2 := by positivity
  have hlow : S ^ 2 ≤ A := by nlinarith [sq_nonneg (1 - r)]
  have hup : A ≤ 4 := by nlinarith [sq_nonneg (1 - r)]
  have hlogS : Real.log (S ^ 2) = 2 * Real.log S := by
    rw [Real.log_pow]; push_cast; ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  have hl : 2 * Real.log S ≤ Real.log A := by
    rw [← hlogS]; exact Real.log_le_log hSpos hlow
  have hu : Real.log A ≤ 2 * Real.log 2 := by
    rw [← h4]; exact Real.log_le_log (lt_of_lt_of_le hSpos hlow) hup
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold reg
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log S)
    nlinarith
  · have := abs_nonneg (Real.log S)
    nlinarith

theorem reg_tendsto {w : ℝ} (hs : Real.sin (w / 2) ≠ 0) :
    Tendsto (fun r => reg r w) (𝓝[<] 1) (𝓝 (lsin w)) := by
  have hc : ContinuousAt (fun r : ℝ => reg r w) 1 := by
    unfold reg
    refine ContinuousAt.mul continuousAt_const (ContinuousAt.log (by fun_prop) ?_)
    rw [reg_arg]
    have : 0 < Real.sin (w / 2) ^ 2 := by positivity
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one, zero_add]
    positivity
  have hv : reg 1 w = lsin w := by
    unfold reg lsin
    rw [reg_arg]
    have e : (1 - 1 : ℝ) ^ 2 + 4 * 1 * Real.sin (w / 2) ^ 2 = (2 * Real.sin (w / 2)) ^ 2 := by ring
    rw [e, Real.log_pow, Real.log_mul (by norm_num) hs]
    push_cast
    ring
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem reg_integral_tendsto (v : ℝ) :
    Tendsto (fun r => ∫ w in (0 : ℝ)..v, reg r w) (𝓝[<] 1) (𝓝 (Cl v)) := by
  unfold Cl
  have hev : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo (1 / 2 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun w => |Real.log (Real.sin (w / 2))| + Real.log 2) ?_ ?_ ?_ ?_
  · filter_upwards [hev] with r hr
    refine Continuous.aestronglyMeasurable ?_
    unfold reg
    refine continuous_const.mul (Continuous.log (by fun_prop) ?_)
    intro w
    exact (reg_arg_pos (by linarith [hr.1]) hr.2 w).ne'
  · filter_upwards [hev] with r hr
    filter_upwards [sin_half_zero_null] with w hw _
    rw [Real.norm_eq_abs]
    exact reg_bound hr.1.le hr.2 hw
  · exact (log_sin_half_int 0 v).abs.add intervalIntegrable_const
  · filter_upwards [sin_half_zero_null] with w hw _
    exact reg_tendsto hw

theorem summable_inv_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  refine this.congr ?_
  intro n; simp

theorem abs_clterm_le (v : ℝ) (n : ℕ) :
    |Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2| ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

theorem clterm_summable (v : ℝ) :
    Summable (fun n : ℕ => Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2) :=
  Summable.of_norm_bounded summable_inv_sq (fun n => by
    rw [Real.norm_eq_abs]; exact abs_clterm_le v n)

/-- **Clausen's identity**, from the Taylor series on `|z| < 1` and dominated convergence:
no boundary series for the logarithm is used. -/
theorem Cl_eq (v : ℝ) :
    Cl v = -∑' n : ℕ, Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2 := by
  have hev : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo (1 / 2 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have ht : Tendsto (fun r : ℝ => ∑' n : ℕ,
      r ^ (n + 1) * (Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2)) (𝓝[<] 1)
      (𝓝 (∑' n : ℕ, Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2)) := by
    refine tendsto_tsum_of_dominated_convergence summable_inv_sq ?_ ?_
    · intro n
      have hc : ContinuousAt (fun r : ℝ =>
          r ^ (n + 1) * (Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2)) 1 := by fun_prop
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    · filter_upwards [hev] with r hr n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (by linarith [hr.1]) _)]
      have h1 : r ^ (n + 1) ≤ 1 := pow_le_one₀ (by linarith [hr.1]) hr.2.le
      calc _ ≤ 1 * |Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact abs_clterm_le v n
  have ht2 : Tendsto (fun r : ℝ => -∫ w in (0 : ℝ)..v, reg r w) (𝓝[<] 1) (𝓝 (-(Cl v))) :=
    (reg_integral_tendsto v).neg
  have heq : (fun r : ℝ => ∑' n : ℕ,
      r ^ (n + 1) * (Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2)) =ᶠ[𝓝[<] 1]
      fun r => -∫ w in (0 : ℝ)..v, reg r w := by
    filter_upwards [hev] with r hr
    rw [(reg_integral (by linarith [hr.1]) hr.2 v).tsum_eq, intervalIntegral.integral_neg]
  have := tendsto_nhds_unique (ht.congr' heq) ht2
  linarith

/-- The truncated primitive: `Cl v + sum_{n<=N} sin(nv)/n^2`. -/
def GN (N : ℕ) (v : ℝ) : ℝ :=
  Cl v + ∑ n ∈ Finset.range N, Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2

theorem GN_eq (N : ℕ) (v : ℝ) :
    GN N v = -∑' n : ℕ, Real.sin ((((n + N : ℕ) : ℝ) + 1) * v) / (((n + N : ℕ) : ℝ) + 1) ^ 2 := by
  unfold GN
  rw [Cl_eq, ← (clterm_summable v).sum_add_tsum_nat_add N]
  ring

theorem GN_abs_le_of_partial {N : ℕ} {v C : ℝ}
    (h : ∀ M : ℕ, |∑ n ∈ Finset.range M,
      Real.sin ((((n + N : ℕ) : ℝ) + 1) * v) / (((n + N : ℕ) : ℝ) + 1) ^ 2| ≤ C) :
    |GN N v| ≤ C := by
  rw [GN_eq, abs_neg]
  have hs : Summable (fun n : ℕ =>
      Real.sin ((((n + N : ℕ) : ℝ) + 1) * v) / (((n + N : ℕ) : ℝ) + 1) ^ 2) :=
    (summable_nat_add_iff N).mpr (clterm_summable v)
  exact le_of_tendsto (hs.hasSum.tendsto_sum_nat.abs) (Eventually.of_forall h)

theorem partial1 {N : ℕ} (hN : 1 ≤ N) (v : ℝ) (M : ℕ) :
    |∑ n ∈ Finset.range M,
      Real.sin ((((n + N : ℕ) : ℝ) + 1) * v) / (((n + N : ℕ) : ℝ) + 1) ^ 2| ≤
      1 / (N : ℝ) - 1 / ((N : ℝ) + M) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_clterm_le v (M + N)
    have hk : (0 : ℝ) < (N : ℝ) + M := by positivity
    have h2 : 1 / (((M + N : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((N : ℝ) + M) - 1 / ((N : ℝ) + (M + 1 : ℕ)) := by
      push_cast
      have e : (M : ℝ) + N + 1 = (N : ℝ) + M + 1 := by ring
      rw [e]
      set k := (N : ℝ) + M with hkd
      have e2 : (N : ℝ) + ((M : ℝ) + 1) = k + 1 := by rw [hkd]; ring
      rw [e2, div_sub_div _ _ hk.ne' (by positivity : k + 1 ≠ 0),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem partial2 (N : ℕ) {v : ℝ} (hs : Real.sin (v / 2) ≠ 0) (M : ℕ) :
    |∑ n ∈ Finset.range M,
      Real.sin ((((n + N : ℕ) : ℝ) + 1) * v) / (((n + N : ℕ) : ℝ) + 1) ^ 2| ≤
      1 / (((N : ℝ) + 1) ^ 2 * |Real.sin (v / 2)|) := by
  set S := Real.sin (v / 2) with hS
  let c : ℕ → ℝ := fun k => Real.cos (((k : ℝ) + 1 / 2) * v)
  have hsin : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * v) = (c k - c (k + 1)) / (2 * S) := by
    intro k
    have h1 : c k = Real.cos (((k : ℝ) + 1) * v - v / 2) := by
      simp only [c]; congr 1; ring
    have h2 : c (k + 1) = Real.cos (((k : ℝ) + 1) * v + v / 2) := by
      simp only [c]; push_cast; congr 1; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  -- Abel summation invariant
  have inv : ∀ M : ℕ, |(∑ n ∈ Finset.range M, (c (n + N) - c (n + N + 1)) /
        (((n + N : ℕ) : ℝ) + 1) ^ 2) + c (M + N) / (((M + N : ℕ) : ℝ) + 1) ^ 2 -
        c N / ((N : ℝ) + 1) ^ 2| ≤ 1 / ((N : ℝ) + 1) ^ 2 - 1 / (((M + N : ℕ) : ℝ) + 1) ^ 2 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      set k : ℝ := ((M + N : ℕ) : ℝ) + 1 with hk
      have hk0 : 0 < k := by positivity
      have e1 : (((M + 1 + N : ℕ) : ℝ) + 1) = k + 1 := by rw [hk]; push_cast; ring
      have e2 : c (M + 1 + N) = c (M + N + 1) := by congr 1; ring
      rw [e1, e2]
      have hc : |c (M + N + 1)| ≤ 1 := Real.abs_cos_le_one _
      have hd : 1 / (k + 1) ^ 2 ≤ 1 / k ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
      set X := (∑ n ∈ Finset.range M, (c (n + N) - c (n + N + 1)) /
        (((n + N : ℕ) : ℝ) + 1) ^ 2) + c (M + N) / k ^ 2 - c N / ((N : ℝ) + 1) ^ 2 with hX
      have hdecomp : (∑ n ∈ Finset.range M, (c (n + N) - c (n + N + 1)) /
          (((n + N : ℕ) : ℝ) + 1) ^ 2) + (c (M + N) - c (M + N + 1)) / k ^ 2 +
          c (M + N + 1) / (k + 1) ^ 2 - c N / ((N : ℝ) + 1) ^ 2 =
          X + c (M + N + 1) * (1 / (k + 1) ^ 2 - 1 / k ^ 2) := by
        rw [hX]; ring
      rw [hdecomp]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonpos (by linarith : 1 / (k + 1) ^ 2 - 1 / k ^ 2 ≤ 0)]
      have : |c (M + N + 1)| * -(1 / (k + 1) ^ 2 - 1 / k ^ 2) ≤
          1 * -(1 / (k + 1) ^ 2 - 1 / k ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by linarith)
      linarith
  have hsum : ∑ n ∈ Finset.range M,
      Real.sin ((((n + N : ℕ) : ℝ) + 1) * v) / (((n + N : ℕ) : ℝ) + 1) ^ 2 =
      (∑ n ∈ Finset.range M, (c (n + N) - c (n + N + 1)) /
        (((n + N : ℕ) : ℝ) + 1) ^ 2) / (2 * S) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hsin (n + N)]
    field_simp
  rw [hsum, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hSp : 0 < |S| := abs_pos.mpr hs
  have hT : |∑ n ∈ Finset.range M, (c (n + N) - c (n + N + 1)) /
        (((n + N : ℕ) : ℝ) + 1) ^ 2| ≤ 2 / ((N : ℝ) + 1) ^ 2 := by
    have h1 := inv M
    have hcM : |c (M + N) / (((M + N : ℕ) : ℝ) + 1) ^ 2| ≤ 1 / (((M + N : ℕ) : ℝ) + 1) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (((M + N : ℕ) : ℝ) + 1) ^ 2)]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
    have hcN : |c N / ((N : ℝ) + 1) ^ 2| ≤ 1 / ((N : ℝ) + 1) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((N : ℝ) + 1) ^ 2)]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
    rw [abs_le] at h1 hcM hcN ⊢
    have e : 2 / ((N : ℝ) + 1) ^ 2 = 1 / ((N : ℝ) + 1) ^ 2 + 1 / ((N : ℝ) + 1) ^ 2 := by ring
    rw [e]
    constructor <;> linarith [h1.1, h1.2, hcM.1, hcM.2, hcN.1, hcN.2]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hN1 : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  have := (le_div_iff₀ hN1).mp hT
  nlinarith

/-- `kappa_N(d) = 1 / max 1 (N d)`. -/
def kap (N : ℕ) (d : ℝ) : ℝ := 1 / max 1 ((N : ℝ) * d)

theorem kap_pos (N : ℕ) (d : ℝ) : 0 < kap N d := by
  unfold kap
  have : (0 : ℝ) < max 1 ((N : ℝ) * d) := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

theorem kap_anti (N : ℕ) {a b : ℝ} (h : a ≤ b) : kap N b ≤ kap N a := by
  unfold kap
  refine one_div_le_one_div_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- The two-regime bound on the truncated primitive. -/
theorem GN_bound {N : ℕ} (hN : 1 ≤ N) {v d : ℝ} (hd : d ≤ |Real.sin (v / 2)|) :
    |GN N v| ≤ kap N d / N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold kap
  by_cases h : (N : ℝ) * d ≤ 1
  · rw [max_eq_left h]
    refine GN_abs_le_of_partial fun M => (partial1 hN v M).trans ?_
    have : 0 ≤ 1 / ((N : ℝ) + M) := by positivity
    simp only [div_one]
    linarith
  · have h' : 1 < (N : ℝ) * d := lt_of_not_ge h
    rw [max_eq_right h'.le]
    have hdp : 0 < d := by
      by_contra hc
      have : (N : ℝ) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNp.le (not_lt.mp hc)
      linarith
    have hS : 0 < |Real.sin (v / 2)| := lt_of_lt_of_le hdp hd
    have hs : Real.sin (v / 2) ≠ 0 := abs_pos.mp hS
    refine GN_abs_le_of_partial fun M => (partial2 N hs M).trans ?_
    have e : 1 / ((N : ℝ) * d) / N = 1 / ((N : ℝ) ^ 2 * d) := by field_simp
    rw [e]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul h1 hd hdp.le (by positivity)

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### The cosine coordinate of the direct source -/

/-- Physical coordinate of the angle: `s = (1 + cos θ)/2 = cos²(θ/2)`. -/
def sth (θ : ℝ) : ℝ := Real.cos (θ / 2) ^ 2
/-- `Y = s + 1/s` as a function of the angle. -/
def Yth (θ : ℝ) : ℝ := sth θ + 1 / sth θ
/-- `dY/dθ`. -/
def bet (θ : ℝ) : ℝ := Real.sin (θ / 2) * (1 / Real.cos (θ / 2) ^ 3 - Real.cos (θ / 2))
/-- `d²Y/dθ²`. -/
def dbet (θ : ℝ) : ℝ :=
  (1 / 2) * (1 / Real.cos (θ / 2) ^ 2 - Real.cos (θ / 2) ^ 2 +
    3 * Real.sin (θ / 2) ^ 2 / Real.cos (θ / 2) ^ 4 + Real.sin (θ / 2) ^ 2)

theorem cos_half_pos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : 0 < Real.cos (θ / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩

theorem sin_half_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : 0 ≤ Real.sin (θ / 2) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])

theorem sth_pos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : 0 < sth θ := by
  have := cos_half_pos h0 h1
  unfold sth; positivity

theorem sth_le_one (θ : ℝ) : sth θ ≤ 1 := by
  unfold sth
  have := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [sq_nonneg (Real.sin (θ / 2))]

theorem two_sth_sub (θ : ℝ) : 2 * sth θ - 1 = Real.cos θ := by
  unfold sth
  have := Real.cos_two_mul (θ / 2)
  have e : 2 * (θ / 2) = θ := by ring
  rw [e] at this
  rw [this]

theorem hasDeriv_cos_half (θ : ℝ) :
    HasDerivAt (fun x => Real.cos (x / 2)) (-Real.sin (θ / 2) / 2) θ := by
  have h := (Real.hasDerivAt_cos (θ / 2)).comp θ ((hasDerivAt_id θ).div_const 2)
  simpa [Function.comp_def, div_eq_mul_inv] using h

theorem hasDeriv_sin_half (θ : ℝ) :
    HasDerivAt (fun x => Real.sin (x / 2)) (Real.cos (θ / 2) / 2) θ := by
  have h := (Real.hasDerivAt_sin (θ / 2)).comp θ ((hasDerivAt_id θ).div_const 2)
  simpa [Function.comp_def, div_eq_mul_inv] using h

theorem hasDeriv_Yth {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) : HasDerivAt Yth (bet θ) θ := by
  have h1 := hasDeriv_cos_half θ
  have h2 := h1.pow 2
  have h3 := h2.add ((hasDerivAt_const θ (1 : ℝ)).div h2 (pow_ne_zero 2 hc))
  have e : Yth = (fun x => Real.cos (x / 2) ^ 2) + (fun x => (1 : ℝ)) / (fun x => Real.cos (x / 2) ^ 2) := by
    funext x; simp [Yth, sth]
  rw [e]
  convert h3 using 1
  simp only [Pi.pow_apply]
  unfold bet
  field_simp
  ring

theorem hasDeriv_bet {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) : HasDerivAt bet (dbet θ) θ := by
  have h1 := hasDeriv_cos_half θ
  have h2 := hasDeriv_sin_half θ
  have h3 := h2.mul (((hasDerivAt_const θ (1 : ℝ)).div (h1.pow 3) (pow_ne_zero 3 hc)).sub h1)
  have e : bet = (fun x => Real.sin (x / 2)) *
      (((fun x => (1 : ℝ)) / (fun x => Real.cos (x / 2) ^ 3)) - fun x => Real.cos (x / 2)) := by
    funext x; simp [bet]
  rw [e]
  convert h3 using 1
  simp only [Pi.pow_apply, Pi.div_apply, Pi.sub_apply]
  unfold dbet
  field_simp
  ring

theorem bet_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : 0 ≤ bet θ := by
  have hc := cos_half_pos h0 h1
  have hs := sin_half_nonneg h0 h1
  have hc1 : Real.cos (θ / 2) ≤ 1 := Real.cos_le_one _
  unfold bet
  refine mul_nonneg hs ?_
  have : 1 ≤ 1 / Real.cos (θ / 2) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.cos (θ / 2) ^ 3 ≤ 1 := pow_le_one₀ hc.le hc1
    linarith
  linarith

theorem dbet_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : 0 ≤ dbet θ := by
  have hc := cos_half_pos h0 h1
  have hc1 : Real.cos (θ / 2) ≤ 1 := Real.cos_le_one _
  have hcc : Real.cos (θ / 2) ^ 2 ≤ 1 := pow_le_one₀ hc.le hc1
  have h1' : 1 ≤ 1 / Real.cos (θ / 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  unfold dbet
  have : 0 ≤ 3 * Real.sin (θ / 2) ^ 2 / Real.cos (θ / 2) ^ 4 := by positivity
  have : 0 ≤ Real.sin (θ / 2) ^ 2 := by positivity
  nlinarith

theorem continuousOn_bet : ContinuousOn bet (Ico 0 π) := fun θ hθ =>
  (hasDeriv_Yth (cos_half_pos hθ.1 hθ.2).ne' |>.continuousAt |> fun _ =>
    (hasDeriv_bet (cos_half_pos hθ.1 hθ.2).ne').continuousAt.continuousWithinAt)

theorem continuousOn_dbet : ContinuousOn dbet (Ico 0 π) := by
  intro θ hθ
  have hc := (cos_half_pos hθ.1 hθ.2).ne'
  have : ContinuousAt dbet θ := by
    unfold dbet
    fun_prop (disch := simp [hc])
  exact this.continuousWithinAt

/-- `physX` inverts `s + 1/s` on `(0,1]`. -/
theorem physX_inv {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) : YCell.physX (s + 1 / s) = s := by
  have hY : 0 ≤ s + 1 / s := by positivity
  have hd : 0 ≤ 1 / s - s := by
    have : 1 ≤ 1 / s := by rw [le_div_iff₀ h0]; linarith
    linarith
  have hsq : (s + 1 / s) ^ 2 - 4 = (1 / s - s) ^ 2 := by
    field_simp
    ring
  unfold YCell.physX
  rw [if_pos hY, hsq, Real.sqrt_sq hd]
  field_simp
  ring

theorem physX_mem {Y : ℝ} (hY : 2 ≤ Y) : 0 < YCell.physX Y ∧ YCell.physX Y ≤ 1 := by
  unfold YCell.physX
  rw [if_pos (by linarith)]
  have hr : 0 ≤ √(Y ^ 2 - 4) := Real.sqrt_nonneg _
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

/-- The angle of a source point `Y ≥ 2`. -/
def Th (Y : ℝ) : ℝ := Real.arccos (2 * YCell.physX Y - 1)

theorem Th_mem {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ Th Y ∧ Th Y < π := by
  obtain ⟨h0, h1⟩ := physX_mem hY
  refine ⟨Real.arccos_nonneg _, lt_of_le_of_ne (Real.arccos_le_pi _) ?_⟩
  intro h
  have := Real.arccos_eq_pi.mp h
  linarith

theorem sth_Th {Y : ℝ} (hY : 2 ≤ Y) : sth (Th Y) = YCell.physX Y := by
  obtain ⟨h0, h1⟩ := physX_mem hY
  have h := two_sth_sub (Th Y)
  unfold Th at h ⊢
  rw [Real.cos_arccos (by linarith) (by linarith)] at h
  linarith

theorem Yth_Th {Y : ℝ} (hY : 2 ≤ Y) : Yth (Th Y) = Y := by
  unfold Yth
  rw [sth_Th hY]
  exact (physX_spec (by rw [abs_of_nonneg (by linarith)]; exact hY)).2

theorem physX_Yth {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : YCell.physX (Yth θ) = sth θ :=
  physX_inv (sth_pos h0 h1) (sth_le_one θ)

theorem Yth_strictMonoOn : StrictMonoOn Yth (Ico 0 π) := by
  intro a ha b hb hab
  have ca := cos_half_pos ha.1 ha.2
  have cb := cos_half_pos hb.1 hb.2
  have hlt : Real.cos (b / 2) < Real.cos (a / 2) :=
    Real.strictAntiOn_cos ⟨by linarith [ha.1], by linarith [hb.2, Real.pi_pos]⟩
      ⟨by linarith [hb.1], by linarith [hb.2, Real.pi_pos]⟩ (by linarith)
  have sa := sth_pos ha.1 ha.2
  have sb := sth_pos hb.1 hb.2
  have hs : sth b < sth a := by
    unfold sth
    exact pow_lt_pow_left₀ hlt cb.le (by norm_num)
  have ha1 := sth_le_one a
  unfold Yth
  have e : sth b + 1 / sth b - (sth a + 1 / sth a) =
      (sth a - sth b) * (1 - sth a * sth b) / (sth a * sth b) := by
    field_simp
    ring
  have hpos : 0 < (sth a - sth b) * (1 - sth a * sth b) / (sth a * sth b) := by
    have h1 : sth a * sth b < 1 := by nlinarith
    have h2 : 0 < sth a - sth b := by linarith
    have h3 : 0 < 1 - sth a * sth b := by linarith
    positivity
  linarith

theorem Th_lt {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) : Th lo < Th hi := by
  by_contra hc
  have hle := not_lt.mp hc
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have := Yth_strictMonoOn.monotoneOn ⟨mh.1, mh.2⟩ ⟨ml.1, ml.2⟩ hle
  rw [Yth_Th (h2.trans hlt.le), Yth_Th h2] at this
  linarith

/-- Change of variables `Y = Y(θ)` for an arbitrary integrand (no continuity needed). -/
theorem subst_Y {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (g : ℝ → ℝ) :
    ∫ y in lo..hi, g y = ∫ θ in Th lo..Th hi, bet θ * g (Yth θ) := by
  have hab := Th_lt h2 hlt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hsub : Ioc (Th lo) (Th hi) ⊆ Ico 0 π := fun θ hθ =>
    ⟨ml.1.trans hθ.1.le, lt_of_le_of_lt hθ.2 mh.2⟩
  have himg : Yth '' Ioc (Th lo) (Th hi) = Ioc lo hi := by
    ext y
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have m := hsub hθ
      constructor
      · have := Yth_strictMonoOn ⟨ml.1, ml.2⟩ m hθ.1
        rwa [Yth_Th h2] at this
      · have := Yth_strictMonoOn.monotoneOn m ⟨mh.1, mh.2⟩ hθ.2
        rwa [Yth_Th (h2.trans hlt.le)] at this
    · intro hy
      have hy2 : 2 ≤ y := h2.trans hy.1.le
      have my := Th_mem hy2
      refine ⟨Th y, ⟨?_, ?_⟩, Yth_Th hy2⟩
      · exact Th_lt h2 hy.1
      · rcases hy.2.lt_or_eq with h | h
        · exact (Th_lt hy2 h).le
        · rw [h]
  have key := integral_image_eq_integral_abs_deriv_smul (s := Ioc (Th lo) (Th hi)) (f := Yth)
    (f' := bet) measurableSet_Ioc
    (fun x hx => (hasDeriv_Yth (cos_half_pos (hsub hx).1 (hsub hx).2).ne').hasDerivWithinAt)
    (Yth_strictMonoOn.injOn.mono hsub) g
  rw [himg] at key
  rw [intervalIntegral.integral_of_le hlt.le, key, intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
  have m := hsub hθ
  simp only [smul_eq_mul, abs_of_nonneg (bet_nonneg m.1 m.2)]

/-! ### The direct kernel and its truncated primitive -/

/-- The derivative of `GN`. -/
def EN (N : ℕ) (v : ℝ) : ℝ :=
  lsin v + ∑ n ∈ Finset.range N, Real.cos (((n : ℝ) + 1) * v) / ((n : ℝ) + 1)

theorem lsin_measurable : Measurable lsin := by
  unfold lsin
  fun_prop

theorem lsin_continuousAt {v : ℝ} (h : Real.sin (v / 2) ≠ 0) : ContinuousAt lsin v := by
  unfold lsin
  refine ContinuousAt.add (ContinuousAt.log (by fun_prop) h) continuousAt_const

theorem Cl_continuous : Continuous Cl := by
  unfold Cl
  exact intervalIntegral.continuous_primitive (fun a b => lsin_int a b) 0

theorem GN_continuous (N : ℕ) : Continuous (GN N) := by
  unfold GN
  refine Cl_continuous.add ?_
  fun_prop

theorem hasDeriv_GN (N : ℕ) {v : ℝ} (h : Real.sin (v / 2) ≠ 0) :
    HasDerivAt (GN N) (EN N v) v := by
  have h1 : HasDerivAt Cl (lsin v) v :=
    intervalIntegral.integral_hasDerivAt_right (lsin_int 0 v)
      (lsin_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (lsin_continuousAt h)
  have h2 : HasDerivAt (fun v => ∑ n ∈ Finset.range N,
      Real.sin (((n : ℝ) + 1) * v) / ((n : ℝ) + 1) ^ 2)
      (∑ n ∈ Finset.range N, Real.cos (((n : ℝ) + 1) * v) / ((n : ℝ) + 1)) v := by
    refine HasDerivAt.fun_sum fun n _ => ?_
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have := ((Real.hasDerivAt_sin (((n : ℝ) + 1) * v)).comp v
      ((hasDerivAt_id v).const_mul ((n : ℝ) + 1))).div_const (((n : ℝ) + 1) ^ 2)
    simp only [Function.comp_def, id] at this
    convert this using 1
    field_simp
  exact h1.add h2

theorem EN_int (N : ℕ) (a b : ℝ) : IntervalIntegrable (EN N) volume a b := by
  unfold EN
  refine (lsin_int a b).add (Continuous.intervalIntegrable ?_ a b)
  fun_prop

/-- The kernel identity at the level of the boundary kernels. -/
theorem log_sub_eq_lsin {θ φ : ℝ} (h1 : Real.sin ((θ + φ) / 2) ≠ 0)
    (h2 : Real.sin ((θ - φ) / 2) ≠ 0) :
    Real.log |sth φ - sth θ| = lsin (θ + φ) + lsin (θ - φ) - Real.log 4 := by
  have e : sth φ - sth θ = Real.sin ((θ + φ) / 2) * Real.sin ((θ - φ) / 2) := by
    unfold sth
    have ea : (θ + φ) / 2 = θ / 2 + φ / 2 := by ring
    have eb : (θ - φ) / 2 = θ / 2 - φ / 2 := by ring
    rw [ea, eb, Real.sin_add, Real.sin_sub]
    have a1 := Real.sin_sq_add_cos_sq (θ / 2)
    have a2 := Real.sin_sq_add_cos_sq (φ / 2)
    nlinarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  rw [e, Real.log_abs, Real.log_mul h1 h2, h4]
  unfold lsin
  ring

theorem cos_pair (θ φ : ℝ) (n : ℕ) :
    Real.cos (((n : ℝ) + 1) * (θ + φ)) / ((n : ℝ) + 1) +
      Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1) =
    2 / ((n : ℝ) + 1) * (basis (n + 1) (Real.cos θ) * basis (n + 1) (Real.cos φ)) := by
  have hb : ∀ x : ℝ, basis (n + 1) (Real.cos x) = Real.cos (((n : ℝ) + 1) * x) := by
    intro x
    unfold basis
    have := Polynomial.Chebyshev.T_real_cos x ((n + 1 : ℕ) : ℤ)
    simpa using this
  rw [hb, hb, mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  ring

/-- The sum of the two shifted derivatives is the truncated kernel remainder. -/
theorem EN_pair (N : ℕ) {θ φ : ℝ} (h1 : Real.sin ((θ + φ) / 2) ≠ 0)
    (h2 : Real.sin ((θ - φ) / 2) ≠ 0) :
    EN N (θ + φ) + EN N (θ - φ) = Real.log |sth φ - sth θ| + Real.log 4 +
      ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) *
        (basis (n + 1) (2 * sth θ - 1) * basis (n + 1) (2 * sth φ - 1)) := by
  rw [log_sub_eq_lsin h1 h2, two_sth_sub, two_sth_sub]
  unfold EN
  simp only [← cos_pair, Finset.sum_add_distrib]
  ring

/-- `H(θ) = G_N(θ+φ) + G_N(θ-φ)`. -/
def HN (N : ℕ) (φ θ : ℝ) : ℝ := GN N (θ + φ) + GN N (θ - φ)

theorem HN_abs_le {N : ℕ} (hN : 1 ≤ N) (θ φ : ℝ) :
    |HN N φ θ| ≤ 2 / N * kap N |sth φ - sth θ| := by
  have e : sth φ - sth θ = Real.sin ((θ + φ) / 2) * Real.sin ((θ - φ) / 2) := by
    unfold sth
    have ea : (θ + φ) / 2 = θ / 2 + φ / 2 := by ring
    have eb : (θ - φ) / 2 = θ / 2 - φ / 2 := by ring
    rw [ea, eb, Real.sin_add, Real.sin_sub]
    have a1 := Real.sin_sq_add_cos_sq (θ / 2)
    have a2 := Real.sin_sq_add_cos_sq (φ / 2)
    nlinarith
  have h1 : |sth φ - sth θ| ≤ |Real.sin ((θ + φ) / 2)| := by
    rw [e, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have h2 : |sth φ - sth θ| ≤ |Real.sin ((θ - φ) / 2)| := by
    rw [e, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
  have b1 := GN_bound hN h1
  have b2 := GN_bound hN h2
  unfold HN
  refine (abs_add_le _ _).trans ?_
  have : 2 / (N : ℝ) * kap N |sth φ - sth θ| =
      kap N |sth φ - sth θ| / N + kap N |sth φ - sth θ| / N := by ring
  rw [this]
  exact add_le_add b1 b2

/-- The remainder integrand of the direct kernel, in the source coordinate. -/
def Rdir (N : ℕ) (t y : ℝ) : ℝ :=
  Real.log |t - YCell.physX y| + Real.log 4 +
    ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) *
      (basis (n + 1) (2 * YCell.physX y - 1) * basis (n + 1) (2 * t - 1))

theorem sin_half_null_shift (c : ℝ) :
    ({θ : ℝ | Real.sin ((θ + c) / 2) = 0}).Countable := by
  refine (Set.countable_range (fun k : ℤ => 2 * ((k : ℝ) * π) - c)).mono ?_
  intro w hw
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hw
  refine ⟨k, ?_⟩
  simp only
  rw [hk]; ring

/-- **Segment integration by parts.** For a source segment `[lo,hi] ⊂ [2,∞)`, the truncated
remainder integrates to boundary values of `H β` minus the regular variation term. -/
theorem seg_direct {N : ℕ} {t φ lo hi : ℝ} (ht : t = sth φ) (h2 : 2 ≤ lo) (hlt : lo < hi) :
    ∫ y in lo..hi, Rdir N t y =
      HN N φ (Th hi) * bet (Th hi) - HN N φ (Th lo) * bet (Th lo) -
        ∫ θ in Th lo..Th hi, HN N φ θ * dbet θ := by
  have hab := Th_lt h2 hlt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hsub : Icc (Th lo) (Th hi) ⊆ Ico 0 π := fun θ hθ =>
    ⟨ml.1.trans hθ.1, lt_of_le_of_lt hθ.2 mh.2⟩
  have hcH : Continuous (HN N φ) := by
    unfold HN
    exact ((GN_continuous N).comp (by fun_prop)).add ((GN_continuous N).comp (by fun_prop))
  have hEint : IntervalIntegrable (fun θ => EN N (θ + φ) + EN N (θ - φ)) volume (Th lo) (Th hi) := by
    have a := (EN_int N (Th lo + φ) (Th hi + φ)).comp_add_right φ
    have b := (EN_int N (Th lo - φ) (Th hi - φ)).comp_sub_right φ
    simp only [add_sub_cancel_right, sub_add_cancel] at a b
    exact a.add b
  have hbetc : ContinuousOn bet (uIcc (Th lo) (Th hi)) := by
    rw [uIcc_of_le hab.le]; exact continuousOn_bet.mono hsub
  have hdbetc : ContinuousOn dbet (uIcc (Th lo) (Th hi)) := by
    rw [uIcc_of_le hab.le]; exact continuousOn_dbet.mono hsub
  have hint1 : IntervalIntegrable (fun θ => (EN N (θ + φ) + EN N (θ - φ)) * bet θ) volume
      (Th lo) (Th hi) := hEint.mul_continuousOn hbetc
  have hint2 : IntervalIntegrable (fun θ => HN N φ θ * dbet θ) volume (Th lo) (Th hi) :=
    (hcH.continuousOn.mul hdbetc).intervalIntegrable
  -- FTC off a countable set
  have hS : ({θ : ℝ | Real.sin ((θ + φ) / 2) = 0} ∪
      {θ : ℝ | Real.sin ((θ + -φ) / 2) = 0}).Countable :=
    (sin_half_null_shift φ).union (sin_half_null_shift (-φ))
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun θ => HN N φ θ * bet θ)
    (fun θ => (EN N (θ + φ) + EN N (θ - φ)) * bet θ + HN N φ θ * dbet θ) hab.le hS
    ((hcH.continuousOn.mono (subset_univ _)).mul (continuousOn_bet.mono hsub))
    (by
      intro θ hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      have hn1 : Real.sin ((θ + φ) / 2) ≠ 0 := fun h => hθ2 (Or.inl h)
      have hn2 : Real.sin ((θ - φ) / 2) ≠ 0 := fun h => hθ2 (Or.inr (by
        simpa [sub_eq_add_neg] using h))
      have hc := (cos_half_pos (hsub ⟨hθ1.1.le, hθ1.2.le⟩).1 (hsub ⟨hθ1.1.le, hθ1.2.le⟩).2).ne'
      have d1 : HasDerivAt (fun x => GN N (x + φ)) (EN N (θ + φ)) θ := by
        have := (hasDeriv_GN N hn1).comp_add_const θ φ
        simpa using this
      have d2 : HasDerivAt (fun x => GN N (x - φ)) (EN N (θ - φ)) θ := by
        have := (hasDeriv_GN N hn2).comp_sub_const θ φ
        simpa using this
      have d3 := (d1.add d2).mul (hasDeriv_bet hc)
      exact d3)
    (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  rw [subst_Y h2 hlt]
  have hcongr : ∫ θ in Th lo..Th hi, bet θ * Rdir N t (Yth θ) =
      ∫ θ in Th lo..Th hi, (EN N (θ + φ) + EN N (θ - φ)) * bet θ := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hS.ae_notMem volume] with θ hθ hmem
    rw [uIoc_of_le hab.le] at hmem
    have m := hsub ⟨hmem.1.le, hmem.2⟩
    have hn1 : Real.sin ((θ + φ) / 2) ≠ 0 := fun h => hθ (Or.inl h)
    have hn2 : Real.sin ((θ - φ) / 2) ≠ 0 := fun h => hθ (Or.inr (by
      simpa [sub_eq_add_neg] using h))
    rw [EN_pair N hn1 hn2]
    unfold Rdir
    rw [physX_Yth m.1 m.2, ht]
    ring
  rw [hcongr]
  linarith

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.Signed.ChebSquare

/-! ### The q-kernel: finite truncation of `log|1 - 2 q z + q²|`, `|q| < 1`, `z = cos φ` -/

theorem logTaylor_pair (q : ℂ) (φ : ℝ) (L : ℕ) :
    (Complex.logTaylor (L + 1) (-(q * Complex.exp (φ * Complex.I)))).re +
      (Complex.logTaylor (L + 1) (-(q * Complex.exp (-(φ * Complex.I))))).re =
    -(2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re * Real.cos (((n : ℝ) + 1) * φ) / ((n : ℝ) + 1)) := by
  induction L with
  | zero => simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
  | succ L ih =>
    rw [Complex.logTaylor_succ (n := L + 1)]
    simp only [Pi.add_apply]
    rw [Complex.add_re, Complex.add_re, Finset.sum_range_succ]
    have hh : ((-1 : ℂ) ^ (L + 1)) * ((-1 : ℂ) ^ (L + 1)) = 1 := by
      rw [← mul_pow]; simp
    have e : ∀ s : ℂ, ((-1 : ℂ) ^ (L + 1 + 1) * (-(q * s)) ^ (L + 1) / ((L + 1 : ℕ) : ℂ)) =
        -(q ^ (L + 1) * s ^ (L + 1) / ((L : ℂ) + 1)) := by
      intro s
      rw [neg_pow (q * s), mul_pow q s, pow_succ (-1 : ℂ) (L + 1)]
      push_cast
      linear_combination (-(q ^ (L + 1) * s ^ (L + 1) / ((L : ℂ) + 1))) * hh
    rw [e, e]
    set X : ℂ := ((L : ℂ) + 1) * φ with hX
    have s1 : Complex.exp (φ * Complex.I) ^ (L + 1) = Complex.exp (X * Complex.I) := by
      rw [← Complex.exp_nat_mul]; congr 1; rw [hX]; push_cast; ring
    have s2 : Complex.exp (-(φ * Complex.I)) ^ (L + 1) = Complex.exp (-X * Complex.I) := by
      rw [← Complex.exp_nat_mul]; congr 1; rw [hX]; push_cast; ring
    set c := Real.cos (((L : ℝ) + 1) * φ) with hc
    have hc' : (c : ℂ) = Complex.cos X := by
      rw [hc, hX]; push_cast; rfl
    have hs12 : Complex.exp (φ * Complex.I) ^ (L + 1) + Complex.exp (-(φ * Complex.I)) ^ (L + 1) =
        2 * (c : ℂ) := by
      rw [s1, s2, ← Complex.two_cos, hc']
    set P := q ^ (L + 1) with hP
    have hcomb : (P * Complex.exp (φ * Complex.I) ^ (L + 1) / ((L : ℂ) + 1)).re +
        (P * Complex.exp (-(φ * Complex.I)) ^ (L + 1) / ((L : ℂ) + 1)).re =
        2 * (P.re * c / ((L : ℝ) + 1)) := by
      rw [← Complex.add_re, ← add_div, ← mul_add, hs12]
      have : P * (2 * (c : ℂ)) / ((L : ℂ) + 1) = ((2 * c / ((L : ℝ) + 1) : ℝ) : ℂ) * P := by
        push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      ring
    simp only [Complex.neg_re]
    linarith

theorem basis_cos (n : ℕ) (x : ℝ) : basis n (Real.cos x) = Real.cos ((n : ℝ) * x) := by
  unfold basis
  have := Polynomial.Chebyshev.T_real_cos x (n : ℤ)
  simpa using this

/-- **Finite truncation of the q-kernel**, with Mathlib's Taylor remainder: no series at all. -/
theorem qker_trunc {q : ℂ} (hq : ‖q‖ < 1) (φ : ℝ) (L : ℕ) :
    |Real.log ‖1 - 2 * q * (Real.cos φ : ℂ) + q ^ 2‖ +
      2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re * basis (n + 1) (Real.cos φ) / ((n : ℝ) + 1)| ≤
    2 * (‖q‖ ^ (L + 1) * (1 - ‖q‖)⁻¹ / ((L : ℝ) + 1)) := by
  set w := Complex.exp (φ * Complex.I) with hw
  set w' := Complex.exp (-(φ * Complex.I)) with hw'
  set A := -(q * w) with hA
  set B := -(q * w') with hB
  have nw : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have nw' : ‖w'‖ = 1 := by
    rw [hw']
    have : -((φ : ℂ) * Complex.I) = ((-φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have nA : ‖A‖ = ‖q‖ := by rw [hA, norm_neg, norm_mul, nw, mul_one]
  have nB : ‖B‖ = ‖q‖ := by rw [hB, norm_neg, norm_mul, nw', mul_one]
  have hww : w * w' = 1 := by
    rw [hw, hw', ← Complex.exp_add]; simp
  have h2c : 2 * (Real.cos φ : ℂ) = w + w' := by
    rw [hw, hw', Complex.ofReal_cos, Complex.two_cos]
    simp
  have hprod : 1 - 2 * q * (Real.cos φ : ℂ) + q ^ 2 = (1 + A) * (1 + B) := by
    have : 2 * q * (Real.cos φ : ℂ) = q * (2 * (Real.cos φ : ℂ)) := by ring
    rw [this, h2c, hA, hB]
    linear_combination (-(q ^ 2)) * hww
  have ne : ∀ z : ℂ, ‖z‖ < 1 → 1 + z ≠ 0 := by
    intro z hz h0
    have : z = -1 := by linear_combination h0
    rw [this] at hz
    simp at hz
  have hA1 := ne A (by rw [nA]; exact hq)
  have hB1 := ne B (by rw [nB]; exact hq)
  have bA := Complex.norm_log_sub_logTaylor_le L (z := A) (by rw [nA]; exact hq)
  have bB := Complex.norm_log_sub_logTaylor_le L (z := B) (by rw [nB]; exact hq)
  rw [nA] at bA
  rw [nB] at bB
  have hsum := logTaylor_pair q φ L
  have hbasis : ∑ n ∈ Finset.range L, (q ^ (n + 1)).re * basis (n + 1) (Real.cos φ) / ((n : ℝ) + 1) =
      ∑ n ∈ Finset.range L, (q ^ (n + 1)).re * Real.cos (((n : ℝ) + 1) * φ) / ((n : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [basis_cos]
    push_cast
    rfl
  have hlog : Real.log ‖1 - 2 * q * (Real.cos φ : ℂ) + q ^ 2‖ =
      (Complex.log (1 + A)).re + (Complex.log (1 + B)).re := by
    rw [hprod, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hB1),
      Complex.log_re, Complex.log_re]
  rw [hlog, hbasis]
  have e : (Complex.log (1 + A)).re + (Complex.log (1 + B)).re +
      2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re * Real.cos (((n : ℝ) + 1) * φ) / ((n : ℝ) + 1) =
      (Complex.log (1 + A) - Complex.logTaylor (L + 1) A).re +
        (Complex.log (1 + B) - Complex.logTaylor (L + 1) B).re := by
    rw [Complex.sub_re, Complex.sub_re]
    linarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have c1 := (Complex.abs_re_le_norm _).trans bA
  have c2 := (Complex.abs_re_le_norm _).trans bB
  linarith

/-- `1 - r t` in the q coordinate, `r = 4 q/(1+q)²`, `z = 2 t - 1`. -/
theorem one_sub_rt {q r : ℂ} (h1 : 1 + q ≠ 0) (hr : r = 4 * q / (1 + q) ^ 2) (t : ℝ) :
    (1 + q) ^ 2 * (1 - r * (t : ℂ)) = 1 - 2 * q * ((2 * t - 1 : ℝ) : ℂ) + q ^ 2 := by
  rw [hr]
  push_cast
  field_simp
  ring

theorem qnum_ne {q : ℂ} (hq : ‖q‖ < 1) (φ : ℝ) :
    1 - 2 * q * (Real.cos φ : ℂ) + q ^ 2 ≠ 0 := by
  set w := Complex.exp (φ * Complex.I) with hw
  have nw : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have hwi : w * Complex.exp (-(φ * Complex.I)) = 1 := by
    rw [hw, ← Complex.exp_add]; simp
  have h2c : 2 * (Real.cos φ : ℂ) = w + Complex.exp (-(φ * Complex.I)) := by
    rw [hw, Complex.ofReal_cos, Complex.two_cos]
    simp
  have hprod : 1 - 2 * q * (Real.cos φ : ℂ) + q ^ 2 =
      (1 - q * w) * (1 - q * Complex.exp (-(φ * Complex.I))) := by
    have : 2 * q * (Real.cos φ : ℂ) = q * (2 * (Real.cos φ : ℂ)) := by ring
    rw [this, h2c]
    linear_combination (-(q ^ 2)) * hwi
  have nw' : ‖Complex.exp (-(φ * Complex.I))‖ = 1 := by
    have : -((φ : ℂ) * Complex.I) = ((-φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have ne : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := by
    intro z hz h0
    have : z = 1 := by linear_combination -h0
    rw [this] at hz
    simp at hz
  rw [hprod]
  exact mul_ne_zero (ne _ (by rw [norm_mul, nw, mul_one]; exact hq))
    (ne _ (by rw [norm_mul, nw', mul_one]; exact hq))

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval

/-! ### Exact q-primitives

`Yq q = r + 1/r` for `r = 4 q/(1+q)²`. Along any curve with `Yq (q τ) = κ τ` the moment `∫ qⁿ dτ`
is an endpoint difference of the rational-logarithmic primitive `Mq`. The primitive is linear in the
two log seeds with real (integer) coefficients. -/

/-- `r + 1/r` in the q coordinate. -/
def Yq (q : ℂ) : ℂ := 4 * q / (1 + q) ^ 2 + (1 + q) ^ 2 / (4 * q)

/-- `-dYq/dq`. -/
def fQ (q : ℂ) : ℂ := (1 / q ^ 2 - 1) / 4 + 4 / (1 + q) ^ 2 - 8 / (1 + q) ^ 3

def a1 (q Lp : ℂ) : ℕ → ℂ
  | 0 => Lp
  | n + 1 => q ^ (n + 1) / ((n : ℂ) + 1) - a1 q Lp n

def a2 (q Lp : ℂ) : ℕ → ℂ
  | 0 => -1 / (1 + q)
  | n + 1 => a1 q Lp n - a2 q Lp n

def a3 (q Lp : ℂ) : ℕ → ℂ
  | 0 => -1 / (2 * (1 + q) ^ 2)
  | n + 1 => a2 q Lp n - a3 q Lp n

def pw (q Lq : ℂ) : ℕ → ℂ
  | 0 => (-1 / q - q) / 4
  | 1 => (Lq - q ^ 2 / 2) / 4
  | n + 2 => (q ^ (n + 1) / ((n : ℂ) + 1) - q ^ (n + 3) / ((n : ℂ) + 3)) / 4

/-- The moment primitive: `d Mq = qⁿ fQ(q) dq`. -/
def Mq (q Lq Lp : ℂ) (n : ℕ) : ℂ := pw q Lq n - 8 * a3 q Lp n + 4 * a2 q Lp n

/-- Primitive of `fQ(q) log(1+q) dq`; `y = Yq q`. -/
def Lplus (y q Lq Lp : ℂ) : ℂ := -y * Lp - 4 / (1 + q) + 2 / (1 + q) ^ 2 + (Lq + q) / 4

/-- Primitive of `-fQ(q) log q dq`; `y = Yq q`. -/
def Lqprim (y q Lq : ℂ) : ℂ := y * Lq + 4 / (1 + q) + 1 / (4 * q) - Lq / 2 - q / 4

section Curve

variable {q Lq Lp : ℝ → ℂ} {q' : ℂ} {τ : ℝ}

theorem hasDeriv_a1 (hq : HasDerivAt q q' τ) (hLp : HasDerivAt Lp (q' / (1 + q τ)) τ)
    (h1 : 1 + q τ ≠ 0) (n : ℕ) :
    HasDerivAt (fun x => a1 (q x) (Lp x) n) (q τ ^ n / (1 + q τ) * q') τ := by
  induction n with
  | zero =>
    simp only [a1, pow_zero]
    convert hLp using 1
    field_simp
  | succ n ih =>
    simp only [a1]
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h := ((hq.fun_pow (n + 1)).div_const ((n : ℂ) + 1)).sub ih
    convert h using 1
    push_cast
    field_simp
    ring

theorem hasDeriv_a2 (hq : HasDerivAt q q' τ) (hLp : HasDerivAt Lp (q' / (1 + q τ)) τ)
    (h1 : 1 + q τ ≠ 0) (n : ℕ) :
    HasDerivAt (fun x => a2 (q x) (Lp x) n) (q τ ^ n / (1 + q τ) ^ 2 * q') τ := by
  induction n with
  | zero =>
    simp only [a2, pow_zero]
    have h := (hasDerivAt_const τ (-1 : ℂ)).fun_div (hq.const_add 1) h1
    convert h using 1
    field_simp
    ring
  | succ n ih =>
    simp only [a2]
    have h := (hasDeriv_a1 hq hLp h1 n).sub ih
    convert h using 1
    field_simp
    ring

theorem hasDeriv_a3 (hq : HasDerivAt q q' τ) (hLp : HasDerivAt Lp (q' / (1 + q τ)) τ)
    (h1 : 1 + q τ ≠ 0) (n : ℕ) :
    HasDerivAt (fun x => a3 (q x) (Lp x) n) (q τ ^ n / (1 + q τ) ^ 3 * q') τ := by
  induction n with
  | zero =>
    simp only [a3, pow_zero]
    have h := (hasDerivAt_const τ (-1 : ℂ)).fun_div
      (((hq.const_add 1).fun_pow 2).const_mul 2) (by simp [h1])
    convert h using 1
    simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
    field_simp
    ring
  | succ n ih =>
    simp only [a3]
    have h := (hasDeriv_a2 hq hLp h1 n).sub ih
    convert h using 1
    field_simp
    ring

theorem hasDeriv_pw (hq : HasDerivAt q q' τ) (hLq : HasDerivAt Lq (q' / q τ) τ)
    (h0 : q τ ≠ 0) (n : ℕ) :
    HasDerivAt (fun x => pw (q x) (Lq x) n) (q τ ^ n * ((1 / q τ ^ 2 - 1) / 4) * q') τ := by
  match n with
  | 0 =>
    simp only [pw, pow_zero]
    have h := (((hasDerivAt_const τ (-1 : ℂ)).fun_div hq h0).sub hq).div_const 4
    convert h using 1
    field_simp
    ring
  | 1 =>
    simp only [pw]
    have h := (hLq.sub ((hq.fun_pow 2).div_const 2)).div_const 4
    convert h using 1
    simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
    field_simp
  | n + 2 =>
    simp only [pw]
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn3 : ((n : ℂ) + 3) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 2)
    have h := (((hq.fun_pow (n + 1)).div_const ((n : ℂ) + 1)).sub
      ((hq.fun_pow (n + 3)).div_const ((n : ℂ) + 3))).div_const 4
    convert h using 1
    simp only [Nat.add_sub_cancel]
    have e1 : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
    have e3 : ((n + 3 : ℕ) : ℂ) = (n : ℂ) + 3 := by push_cast; ring
    have e4 : n + 3 - 1 = n + 2 := by omega
    rw [e1, e3, e4]
    field_simp
    ring

theorem hasDeriv_Mq (hq : HasDerivAt q q' τ) (hLq : HasDerivAt Lq (q' / q τ) τ)
    (hLp : HasDerivAt Lp (q' / (1 + q τ)) τ) (h0 : q τ ≠ 0) (h1 : 1 + q τ ≠ 0) (n : ℕ) :
    HasDerivAt (fun x => Mq (q x) (Lq x) (Lp x) n) (q τ ^ n * (fQ (q τ) * q')) τ := by
  have h := ((hasDeriv_pw hq hLq h0 n).sub ((hasDeriv_a3 hq hLp h1 n).const_mul 8)).add
    ((hasDeriv_a2 hq hLp h1 n).const_mul 4)
  unfold Mq
  convert h using 1
  unfold fQ
  field_simp
  ring

/-- Derivative of `Yq` along a curve. -/
theorem hasDeriv_Yq (hq : HasDerivAt q q' τ) (h0 : q τ ≠ 0) (h1 : 1 + q τ ≠ 0) :
    HasDerivAt (fun x => Yq (q x)) (-(fQ (q τ) * q')) τ := by
  have d1 := (hq.const_add 1).fun_pow 2
  have d2 := ((hq.const_mul 4).fun_div d1 (pow_ne_zero 2 h1)).add
    (d1.fun_div (hq.const_mul 4) (mul_ne_zero (by norm_num) h0))
  unfold Yq
  convert d2 using 1
  unfold fQ
  simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
  field_simp
  ring

end Curve

/-- The source curves. `q τ` runs in the punctured plane with `Yq (q τ) = κ τ`; `Lq`, `Lp` are
continuous branches of `log q`, `log (1+q)` whose real parts are the log norms. -/
structure QCurve (κ l h : ℝ) (q Lq Lp : ℝ → ℂ) : Prop where
  κ_ne : κ ≠ 0
  cq : ContinuousOn q (Icc l h)
  cLq : ContinuousOn Lq (Icc l h)
  cLp : ContinuousOn Lp (Icc l h)
  nz : ∀ τ ∈ Icc l h, q τ ≠ 0
  nz1 : ∀ τ ∈ Icc l h, 1 + q τ ≠ 0
  Yeq : ∀ τ ∈ Icc l h, Yq (q τ) = ((κ * τ : ℝ) : ℂ)
  der : ∀ τ ∈ Ioo l h, ∃ q' : ℂ, HasDerivAt q q' τ ∧ HasDerivAt Lq (q' / q τ) τ ∧
    HasDerivAt Lp (q' / (1 + q τ)) τ
  reLq : ∀ τ ∈ Icc l h, (Lq τ).re = Real.log ‖q τ‖
  reLp : ∀ τ ∈ Icc l h, (Lp τ).re = Real.log ‖1 + q τ‖

namespace QCurve

variable {κ l h : ℝ} {q Lq Lp : ℝ → ℂ}

theorem f_mul (C : QCurve κ l h q Lq Lp) {τ : ℝ} (hτ : τ ∈ Ioo l h) {q' : ℂ}
    (hq : HasDerivAt q q' τ) : fQ (q τ) * q' = -(κ : ℂ) := by
  have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2.le⟩
  have d := hasDeriv_Yq hq (C.nz τ hm) (C.nz1 τ hm)
  have d2 : HasDerivAt (fun x : ℝ => ((κ * x : ℝ) : ℂ)) (κ : ℂ) τ := by
    have := ((hasDerivAt_id τ).const_mul κ).ofReal_comp
    simpa using this
  have hev : (fun x => Yq (q x)) =ᶠ[𝓝 τ] fun x : ℝ => ((κ * x : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    exact C.Yeq x ⟨hx.1.le, hx.2.le⟩
  have := (d.congr_of_eventuallyEq hev.symm).unique d2
  linear_combination -this

theorem cont_a1 {S : Set ℝ} (hq : ContinuousOn q S) (hL : ContinuousOn Lp S) (n : ℕ) :
    ContinuousOn (fun x => a1 (q x) (Lp x) n) S := by
  induction n with
  | zero => simpa [a1] using hL
  | succ n ih =>
    simp only [a1]
    exact ((hq.pow _).div_const _).sub ih

theorem cont_a2 {S : Set ℝ} (hq : ContinuousOn q S) (hL : ContinuousOn Lp S)
    (h1 : ∀ x ∈ S, 1 + q x ≠ 0) (n : ℕ) : ContinuousOn (fun x => a2 (q x) (Lp x) n) S := by
  induction n with
  | zero =>
    simp only [a2]
    exact continuousOn_const.div (continuousOn_const.add hq) h1
  | succ n ih =>
    simp only [a2]
    exact (cont_a1 hq hL n).sub ih

theorem cont_a3 {S : Set ℝ} (hq : ContinuousOn q S) (hL : ContinuousOn Lp S)
    (h1 : ∀ x ∈ S, 1 + q x ≠ 0) (n : ℕ) : ContinuousOn (fun x => a3 (q x) (Lp x) n) S := by
  induction n with
  | zero =>
    simp only [a3]
    refine continuousOn_const.div (continuousOn_const.mul ((continuousOn_const.add hq).pow 2)) ?_
    intro x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (h1 x hx))
  | succ n ih =>
    simp only [a3]
    exact (cont_a2 hq hL h1 n).sub ih

theorem cont_pw {S : Set ℝ} (hq : ContinuousOn q S) (hL : ContinuousOn Lq S)
    (h0 : ∀ x ∈ S, q x ≠ 0) (n : ℕ) : ContinuousOn (fun x => pw (q x) (Lq x) n) S := by
  match n with
  | 0 =>
    simp only [pw]
    exact ((continuousOn_const.div hq h0).sub hq).div_const _
  | 1 =>
    simp only [pw]
    exact (hL.sub ((hq.pow 2).div_const _)).div_const _
  | n + 2 =>
    simp only [pw]
    exact (((hq.pow _).div_const _).sub ((hq.pow _).div_const _)).div_const _

theorem cont_Mq (C : QCurve κ l h q Lq Lp) (n : ℕ) :
    ContinuousOn (fun x => Mq (q x) (Lq x) (Lp x) n) (Icc l h) :=
  ((cont_pw C.cq C.cLq C.nz n).sub (continuousOn_const.mul (cont_a3 C.cq C.cLp C.nz1 n))).add
    (continuousOn_const.mul (cont_a2 C.cq C.cLp C.nz1 n))

theorem kc (C : QCurve κ l h q Lq Lp) : (κ : ℂ) ≠ 0 := by exact_mod_cast C.κ_ne

/-- **Exact endpoint primitive of the q-moment.** -/
theorem moment (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (n : ℕ) :
    ∫ τ in l..h, q τ ^ n =
      -(Mq (q h) (Lq h) (Lp h) n - Mq (q l) (Lq l) (Lp l) n) / κ := by
  have hint : IntervalIntegrable (fun τ => -(κ : ℂ) * q τ ^ n) volume l h :=
    (continuousOn_const.mul (C.cq.pow n)).intervalIntegrable_of_Icc hlh
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlh (cont_Mq C n)
    (fun τ hτ => by
      obtain ⟨q', d1, d2, d3⟩ := C.der τ hτ
      have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2.le⟩
      have d := hasDeriv_Mq d1 d2 d3 (C.nz τ hm) (C.nz1 τ hm) n
      rw [C.f_mul hτ d1] at d
      have e : q τ ^ n * -(κ : ℂ) = -(κ : ℂ) * q τ ^ n := by ring
      rw [e] at d
      exact d.hasDerivWithinAt) hint
  rw [intervalIntegral.integral_const_mul] at key
  have hk := C.kc
  field_simp
  linear_combination -key

theorem int_Lp (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) :
    ∫ τ in l..h, Lp τ =
      -(Lplus ((κ * h : ℝ) : ℂ) (q h) (Lq h) (Lp h) - Lplus ((κ * l : ℝ) : ℂ) (q l) (Lq l) (Lp l)) / κ := by
  have hint : IntervalIntegrable (fun τ => -(κ : ℂ) * Lp τ) volume l h :=
    (continuousOn_const.mul C.cLp).intervalIntegrable_of_Icc hlh
  have hcy : ContinuousOn (fun τ : ℝ => ((κ * τ : ℝ) : ℂ)) (Icc l h) := by fun_prop
  have hc : ContinuousOn (fun τ : ℝ => Lplus ((κ * τ : ℝ) : ℂ) (q τ) (Lq τ) (Lp τ)) (Icc l h) := by
    unfold Lplus
    refine (((hcy.neg.mul C.cLp).sub (continuousOn_const.div (continuousOn_const.add C.cq) C.nz1)).add
      (continuousOn_const.div ((continuousOn_const.add C.cq).pow 2)
        (fun x hx => pow_ne_zero 2 (C.nz1 x hx)))).add ((C.cLq.add C.cq).div_const _)
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlh hc
    (fun τ hτ => by
      obtain ⟨q', d1, d2, d3⟩ := C.der τ hτ
      have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2.le⟩
      have h0 := C.nz τ hm
      have h1 := C.nz1 τ hm
      have hy : HasDerivAt (fun x : ℝ => ((κ * x : ℝ) : ℂ)) (κ : ℂ) τ := by
        have := ((hasDerivAt_id τ).const_mul κ).ofReal_comp
        simpa using this
      have dq1 := d1.const_add 1
      have d := (((hy.fun_neg.fun_mul d3).fun_sub ((hasDerivAt_const τ (4 : ℂ)).fun_div dq1 h1)).fun_add
        ((hasDerivAt_const τ (2 : ℂ)).fun_div (dq1.fun_pow 2) (pow_ne_zero 2 h1))).fun_add
        ((d2.fun_add d1).div_const 4)
      refine HasDerivAt.hasDerivWithinAt ?_
      unfold Lplus
      convert d using 1
      have hY := C.Yeq τ hm
      simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
      rw [← hY]
      unfold Yq
      field_simp
      ring) hint
  rw [intervalIntegral.integral_const_mul] at key
  have hk := C.kc
  rw [eq_div_iff hk]
  linear_combination -key

theorem int_Lq (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) :
    ∫ τ in l..h, Lq τ =
      (Lqprim ((κ * h : ℝ) : ℂ) (q h) (Lq h) - Lqprim ((κ * l : ℝ) : ℂ) (q l) (Lq l)) / κ := by
  have hint : IntervalIntegrable (fun τ => (κ : ℂ) * Lq τ) volume l h :=
    (continuousOn_const.mul C.cLq).intervalIntegrable_of_Icc hlh
  have hcy : ContinuousOn (fun τ : ℝ => ((κ * τ : ℝ) : ℂ)) (Icc l h) := by fun_prop
  have hc : ContinuousOn (fun τ : ℝ => Lqprim ((κ * τ : ℝ) : ℂ) (q τ) (Lq τ)) (Icc l h) := by
    unfold Lqprim
    refine ((((hcy.mul C.cLq).add (continuousOn_const.div (continuousOn_const.add C.cq) C.nz1)).add
      (continuousOn_const.div (continuousOn_const.mul C.cq)
        (fun x hx => mul_ne_zero (by norm_num) (C.nz x hx)))).sub (C.cLq.div_const _)).sub
      (C.cq.div_const _)
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlh hc
    (fun τ hτ => by
      obtain ⟨q', d1, d2, d3⟩ := C.der τ hτ
      have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2.le⟩
      have h0 := C.nz τ hm
      have h1 := C.nz1 τ hm
      have hy : HasDerivAt (fun x : ℝ => ((κ * x : ℝ) : ℂ)) (κ : ℂ) τ := by
        have := ((hasDerivAt_id τ).const_mul κ).ofReal_comp
        simpa using this
      have dq1 := d1.const_add 1
      have d := ((((hy.fun_mul d2).fun_add ((hasDerivAt_const τ (4 : ℂ)).fun_div dq1 h1)).fun_add
        ((hasDerivAt_const τ (1 : ℂ)).fun_div (d1.const_mul 4) (mul_ne_zero (by norm_num) h0))).fun_sub
        (d2.div_const 2)).fun_sub (d1.div_const 4)
      refine HasDerivAt.hasDerivWithinAt ?_
      unfold Lqprim
      convert d using 1
      have hY := C.Yeq τ hm
      rw [← hY]
      unfold Yq
      field_simp
      ring) hint
  rw [intervalIntegral.integral_const_mul] at key
  have hk := C.kc
  rw [eq_div_iff hk]
  linear_combination key

theorem re_integral {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    ∫ τ in a..b, (f τ).re = (∫ τ in a..b, f τ).re :=
  Complex.reCLM.intervalIntegral_comp_comm hf

theorem moment_re (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (n : ℕ) :
    ∫ τ in l..h, (q τ ^ n).re =
      -((Mq (q h) (Lq h) (Lp h) n).re - (Mq (q l) (Lq l) (Lp l) n).re) / κ := by
  have hi : IntervalIntegrable (fun τ => q τ ^ n) volume l h :=
    (C.cq.pow n).intervalIntegrable_of_Icc hlh
  rw [re_integral hi, C.moment hlh n, Complex.div_ofReal_re, Complex.neg_re, Complex.sub_re]

theorem int_log1p (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) :
    ∫ τ in l..h, Real.log ‖1 + q τ‖ =
      -((Lplus ((κ * h : ℝ) : ℂ) (q h) (Lq h) (Lp h)).re -
        (Lplus ((κ * l : ℝ) : ℂ) (q l) (Lq l) (Lp l)).re) / κ := by
  have : ∫ τ in l..h, Real.log ‖1 + q τ‖ = ∫ τ in l..h, (Lp τ).re := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hlh] at hτ
    exact (C.reLp τ hτ).symm
  rw [this, re_integral (C.cLp.intervalIntegrable_of_Icc hlh), C.int_Lp hlh,
    Complex.div_ofReal_re, Complex.neg_re, Complex.sub_re]

theorem int_logq (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) :
    ∫ τ in l..h, Real.log ‖q τ‖ =
      ((Lqprim ((κ * h : ℝ) : ℂ) (q h) (Lq h)).re -
        (Lqprim ((κ * l : ℝ) : ℂ) (q l) (Lq l)).re) / κ := by
  have : ∫ τ in l..h, Real.log ‖q τ‖ = ∫ τ in l..h, (Lq τ).re := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hlh] at hτ
    exact (C.reLq τ hτ).symm
  rw [this, re_integral (C.cLq.intervalIntegrable_of_Icc hlh), C.int_Lq hlh,
    Complex.div_ofReal_re, Complex.sub_re]

end QCurve

/-! Only the real parts of the two log seeds enter (no argument evaluation). -/

theorem a1_re {q L L' : ℂ} (h : L.re = L'.re) (n : ℕ) : (a1 q L n).re = (a1 q L' n).re := by
  induction n with
  | zero => simpa [a1] using h
  | succ n ih => simp only [a1, Complex.sub_re, ih]

theorem a2_re {q L L' : ℂ} (h : L.re = L'.re) (n : ℕ) : (a2 q L n).re = (a2 q L' n).re := by
  induction n with
  | zero => simp [a2]
  | succ n ih => simp only [a2, Complex.sub_re, ih, a1_re h]

theorem a3_re {q L L' : ℂ} (h : L.re = L'.re) (n : ℕ) : (a3 q L n).re = (a3 q L' n).re := by
  induction n with
  | zero => simp [a3]
  | succ n ih => simp only [a3, Complex.sub_re, ih, a2_re h]

theorem pw_re {q L L' : ℂ} (h : L.re = L'.re) (n : ℕ) : (pw q L n).re = (pw q L' n).re := by
  match n with
  | 0 => simp [pw]
  | 1 =>
    simp only [pw, Complex.div_ofNat_re, Complex.sub_re, h]
  | n + 2 => simp [pw]

/-- `Re Mq` depends on the seeds only through their real parts. -/
theorem Mq_re {q Lq Lq' Lp Lp' : ℂ} (h1 : Lq.re = Lq'.re) (h2 : Lp.re = Lp'.re) (n : ℕ) :
    (Mq q Lq Lp n).re = (Mq q Lq' Lp' n).re := by
  unfold Mq
  have m8 : ∀ z : ℂ, ((8 : ℂ) * z).re = 8 * z.re := fun z => by simp
  have m4 : ∀ z : ℂ, ((4 : ℂ) * z).re = 4 * z.re := fun z => by simp
  simp only [Complex.add_re, Complex.sub_re, m8, m4, pw_re h1, a3_re h2, a2_re h2]

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### The real source curves -/

/-- `q = (1-√(1-r))/(1+√(1-r))`, so that `r = 4q/(1+q)²`. -/
def qr (r : ℝ) : ℝ := (1 - √(1 - r)) / (1 + √(1 - r))

theorem sq_den {r : ℝ} (h : r ≤ 1) : √(1 - r) ^ 2 = 1 - r := Real.sq_sqrt (by linarith)

theorem den_pos (r : ℝ) : 0 < 1 + √(1 - r) := by
  have := Real.sqrt_nonneg (1 - r); linarith

theorem one_add_qr (r : ℝ) : 1 + qr r = 2 / (1 + √(1 - r)) := by
  have := (den_pos r).ne'
  unfold qr
  field_simp
  ring

theorem one_add_qr_pos (r : ℝ) : 0 < 1 + qr r := by
  rw [one_add_qr]; have := den_pos r; positivity

theorem qr_ne {r : ℝ} (h1 : r ≤ 1) (h0 : r ≠ 0) : qr r ≠ 0 := by
  have hd := (den_pos r).ne'
  unfold qr
  refine div_ne_zero ?_ hd
  intro h
  have e : √(1 - r) = 1 := by linarith
  have := sq_den h1
  rw [e] at this
  apply h0
  linarith

theorem r_eq_q {r : ℝ} (h1 : r ≤ 1) : r = 4 * qr r / (1 + qr r) ^ 2 := by
  have hs := sq_den h1
  have hd := (den_pos r).ne'
  rw [one_add_qr]
  unfold qr
  field_simp
  linarith

theorem inv_r_eq_q {r : ℝ} (h1 : r ≤ 1) (h0 : r ≠ 0) : 1 / r = (1 + qr r) ^ 2 / (4 * qr r) := by
  have hq := qr_ne h1 h0
  have hp := (one_add_qr_pos r).ne'
  have e := r_eq_q h1
  rw [eq_div_iff (mul_ne_zero (by norm_num) hq)]
  have : r * (1 + qr r) ^ 2 = 4 * qr r := by
    rw [eq_div_iff (pow_ne_zero 2 hp)] at e
    exact e
  field_simp
  linarith

theorem abs_qr_lt {r : ℝ} (hlt : r < 1) : |qr r| < 1 := by
  have hs : 0 < √(1 - r) := Real.sqrt_pos.mpr (by linarith)
  have hd := den_pos r
  unfold qr
  rw [abs_div, abs_of_pos hd, div_lt_one hd, abs_lt]
  constructor <;> linarith

theorem Yq_ofReal (x : ℝ) :
    Yq (x : ℂ) = ((4 * x / (1 + x) ^ 2 + (1 + x) ^ 2 / (4 * x) : ℝ) : ℂ) := by
  unfold Yq; push_cast; rfl

theorem qr_continuousOn {r : ℝ → ℝ} {S : Set ℝ} (hc : ContinuousOn r S) :
    ContinuousOn (fun τ => qr (r τ)) S := by
  unfold qr
  have hs : ContinuousOn (fun τ => √(1 - r τ)) S := (continuousOn_const.sub hc).sqrt
  exact (continuousOn_const.sub hs).div (continuousOn_const.add hs) (fun τ _ => (den_pos _).ne')

theorem qr_differentiableAt {r : ℝ → ℝ} {τ : ℝ} (hd : DifferentiableAt ℝ r τ) (hlt : r τ < 1) :
    DifferentiableAt ℝ (fun x => qr (r x)) τ := by
  unfold qr
  have hne : (1 : ℝ) - r τ ≠ 0 := by linarith
  have hs : DifferentiableAt ℝ (fun x => √(1 - r x)) τ :=
    ((differentiableAt_const _).sub hd).sqrt hne
  exact ((differentiableAt_const _).sub hs).div ((differentiableAt_const _).add hs) (den_pos _).ne'

/-- The real curve through `r`, cast to `ℂ`. -/
def qc (r : ℝ → ℝ) (τ : ℝ) : ℂ := (qr (r τ) : ℝ)
def Lqc (r : ℝ → ℝ) (τ : ℝ) : ℂ := (Real.log (qr (r τ)) : ℝ)
def Lpc (r : ℝ → ℝ) (τ : ℝ) : ℂ := (Real.log (1 + qr (r τ)) : ℝ)

/-- Every real branch `r` with `r + 1/r = κ τ`, `r ≤ 1`, gives a `QCurve`. -/
theorem realCurve {κ l h : ℝ} {r : ℝ → ℝ} (hκ : κ ≠ 0) (hc : ContinuousOn r (Icc l h))
    (h0 : ∀ τ ∈ Icc l h, r τ ≠ 0) (h1 : ∀ τ ∈ Icc l h, r τ ≤ 1)
    (hlt : ∀ τ ∈ Ioo l h, r τ < 1) (hd : ∀ τ ∈ Ioo l h, DifferentiableAt ℝ r τ)
    (hY : ∀ τ ∈ Icc l h, r τ + 1 / r τ = κ * τ) :
    QCurve κ l h (qc r) (Lqc r) (Lpc r) := by
  have hq := qr_continuousOn hc
  have ofc : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc l h) →
      ContinuousOn (fun τ => ((f τ : ℝ) : ℂ)) (Icc l h) :=
    fun hf => Complex.continuous_ofReal.comp_continuousOn hf
  refine ⟨hκ, ofc hq, ofc (hq.log fun τ hτ => qr_ne (h1 τ hτ) (h0 τ hτ)),
    ofc ((continuousOn_const.add hq).log fun τ _ => (one_add_qr_pos _).ne'), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    simpa [qc] using qr_ne (h1 τ hτ) (h0 τ hτ)
  · intro τ hτ
    have := (one_add_qr_pos (r τ)).ne'
    unfold qc
    exact_mod_cast this
  · intro τ hτ
    unfold qc
    rw [Yq_ofReal, ← r_eq_q (h1 τ hτ), ← inv_r_eq_q (h1 τ hτ) (h0 τ hτ), hY τ hτ]
  · intro τ hτ
    have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2.le⟩
    have hdq := (qr_differentiableAt (hd τ hτ) (hlt τ hτ)).hasDerivAt
    set d := deriv (fun x => qr (r x)) τ with hdd
    refine ⟨(d : ℂ), hdq.ofReal_comp, ?_, ?_⟩
    · have := (hdq.log (qr_ne (h1 τ hm) (h0 τ hm))).ofReal_comp
      unfold Lqc qc
      convert this using 1
      push_cast
      rfl
    · have := ((hdq.const_add 1).log (one_add_qr_pos _).ne').ofReal_comp
      unfold Lpc qc
      convert this using 1
      push_cast
      rfl
  · intro τ _
    simp only [Lqc, qc, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  · intro τ _
    have e : (1 : ℂ) + ((qr (r τ) : ℝ) : ℂ) = ((1 + qr (r τ) : ℝ) : ℂ) := by push_cast; ring
    simp only [Lpc, qc, Complex.ofReal_re, e, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

theorem physX_differentiableAt {Y : ℝ} (hY : 2 < Y) : DifferentiableAt ℝ YCell.physX Y := by
  have hev : YCell.physX =ᶠ[𝓝 Y] fun y => 2 / (y + √(y ^ 2 - 4)) := by
    filter_upwards [lt_mem_nhds (by linarith : (0 : ℝ) < Y)] with y hy
    unfold YCell.physX
    rw [_root_.if_pos hy.le]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hne : Y ^ 2 - 4 ≠ 0 := by nlinarith
  have hs : DifferentiableAt ℝ (fun y => √(y ^ 2 - 4)) Y :=
    (((differentiableAt_id).pow 2).sub (differentiableAt_const _)).sqrt hne
  refine (differentiableAt_const _).div (differentiableAt_id.add hs) ?_
  have := Real.sqrt_nonneg (Y ^ 2 - 4)
  have hpos : 0 < Y + √(Y ^ 2 - 4) := by linarith
  exact hpos.ne'

theorem physX_lt_one {Y : ℝ} (hY : 2 < Y) : YCell.physX Y < 1 := by
  obtain ⟨h0, h1⟩ := physX_mem hY.le
  refine lt_of_le_of_ne h1 ?_
  intro h
  have := (physX_spec (Y := Y) (by rw [abs_of_nonneg (by linarith)]; exact hY.le)).2
  rw [h] at this
  norm_num at this
  linarith

theorem physX_add_inv {Y : ℝ} (hY : 2 ≤ Y) : YCell.physX Y + 1 / YCell.physX Y = Y :=
  (physX_spec (by rw [abs_of_nonneg (by linarith)]; exact hY)).2

/-- `r = u`: same-sign reflection. -/
def rR (Y : ℝ) : ℝ := YCell.physX Y
/-- `r = -u`: opposite-sign reflection. -/
def rO (Y : ℝ) : ℝ := -YCell.physX Y
/-- `r = -1/u`: opposite-sign direct kernel. -/
def rD (Y : ℝ) : ℝ := -(1 / YCell.physX Y)

theorem curveR {lo hi : ℝ} (h2 : 2 ≤ lo) : QCurve 1 lo hi (qc rR) (Lqc rR) (Lpc rR) := by
  have hm : ∀ τ ∈ Icc lo hi, 2 ≤ τ := fun τ hτ => h2.trans hτ.1
  refine realCurve one_ne_zero (physX_continuousOn (Or.inl h2))
    (fun τ hτ => (physX_mem (hm τ hτ)).1.ne') (fun τ hτ => (physX_mem (hm τ hτ)).2)
    (fun τ hτ => physX_lt_one (lt_of_le_of_lt h2 hτ.1))
    (fun τ hτ => physX_differentiableAt (lt_of_le_of_lt h2 hτ.1)) ?_
  intro τ hτ
  simp only [rR, one_mul]
  exact physX_add_inv (hm τ hτ)

theorem curveO {lo hi : ℝ} (h2 : 2 ≤ lo) : QCurve (-1) lo hi (qc rO) (Lqc rO) (Lpc rO) := by
  have hm : ∀ τ ∈ Icc lo hi, 2 ≤ τ := fun τ hτ => h2.trans hτ.1
  refine realCurve (by norm_num) (physX_continuousOn (Or.inl h2)).neg
    (fun τ hτ => neg_ne_zero.mpr (physX_mem (hm τ hτ)).1.ne') ?_ ?_ ?_ ?_
  · intro τ hτ
    have := (physX_mem (hm τ hτ)).1
    simp only [rO]; linarith
  · intro τ hτ
    have := (physX_mem (lt_of_le_of_lt h2 hτ.1).le).1
    simp only [rO]; linarith
  · intro τ hτ
    exact (physX_differentiableAt (lt_of_le_of_lt h2 hτ.1)).neg
  · intro τ hτ
    have := physX_add_inv (hm τ hτ)
    simp only [rO]
    rw [one_div, inv_neg, ← one_div]
    linarith

theorem curveD {lo hi : ℝ} (h2 : 2 ≤ lo) : QCurve (-1) lo hi (qc rD) (Lqc rD) (Lpc rD) := by
  have hm : ∀ τ ∈ Icc lo hi, 2 ≤ τ := fun τ hτ => h2.trans hτ.1
  refine realCurve (by norm_num)
    ((continuousOn_const.div (physX_continuousOn (Or.inl h2))
      (fun τ hτ => (physX_mem (hm τ hτ)).1.ne')).neg) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    have := (physX_mem (hm τ hτ)).1
    simp only [rD]
    exact neg_ne_zero.mpr (by positivity)
  · intro τ hτ
    have := (physX_mem (hm τ hτ)).1
    simp only [rD]
    have : 0 < 1 / YCell.physX τ := by positivity
    linarith
  · intro τ hτ
    have := (physX_mem (lt_of_le_of_lt h2 hτ.1).le).1
    simp only [rD]
    have : 0 < 1 / YCell.physX τ := by positivity
    linarith
  · intro τ hτ
    have hx := lt_of_le_of_lt h2 hτ.1
    exact ((differentiableAt_const _).div (physX_differentiableAt hx)
      (physX_mem hx.le).1.ne').neg
  · intro τ hτ
    have := physX_add_inv (hm τ hτ)
    have h0 := (physX_mem (hm τ hτ)).1.ne'
    simp only [rD]
    rw [one_div (-(1 / YCell.physX τ)), inv_neg, one_div (YCell.physX τ), inv_inv]
    rw [one_div] at this
    linarith

/-! ### The column curve: real radicals, no complex square root -/

def dC (c : ℝ) : ℝ := √(2 - 2 * c)
def aC (c : ℝ) : ℝ := √((dC c + 1 - c) / 2)
def bC (c : ℝ) : ℝ := √((dC c - 1 + c) / 2)
/-- `ς = √(1-r)` for `r = c + i √(1-c²)`. -/
def sC (c : ℝ) : ℂ := (aC c : ℂ) - (bC c : ℂ) * Complex.I
def qC (c : ℝ) : ℂ := (1 - sC c) / (1 + sC c)
def LqC (c : ℝ) : ℂ := Complex.log (qC c)
def LpC (c : ℝ) : ℂ := Complex.log (1 + qC c)
/-- The unit-circle root. -/
def rC (c : ℝ) : ℂ := 1 - sC c ^ 2

section Col
variable {c : ℝ}

theorem dC_sq (h1 : c < 1) : dC c ^ 2 = 2 - 2 * c := Real.sq_sqrt (by linarith)

theorem dC_pos (h1 : c < 1) : 0 < dC c := Real.sqrt_pos.mpr (by linarith)

theorem rad_a_pos (h1 : c < 1) : 0 < (dC c + 1 - c) / 2 := by
  have := dC_pos h1; linarith

theorem rad_b_pos (h0 : -1 < c) (h1 : c < 1) : 0 < (dC c - 1 + c) / 2 := by
  have hd := dC_pos h1
  have hs := dC_sq h1
  have : 1 - c < dC c := by nlinarith
  linarith

theorem aC_sq (h1 : c < 1) : aC c ^ 2 = (dC c + 1 - c) / 2 := Real.sq_sqrt (rad_a_pos h1).le
theorem bC_sq (h0 : -1 < c) (h1 : c < 1) : bC c ^ 2 = (dC c - 1 + c) / 2 :=
  Real.sq_sqrt (rad_b_pos h0 h1).le
theorem aC_pos (h1 : c < 1) : 0 < aC c := Real.sqrt_pos.mpr (rad_a_pos h1)
theorem bC_pos (h0 : -1 < c) (h1 : c < 1) : 0 < bC c := Real.sqrt_pos.mpr (rad_b_pos h0 h1)

/-- `(2ab)² = 1 - c²`. -/
theorem ab_sq (h0 : -1 < c) (h1 : c < 1) : (2 * aC c * bC c) ^ 2 = 1 - c ^ 2 := by
  have e : (2 * aC c * bC c) ^ 2 = 4 * aC c ^ 2 * bC c ^ 2 := by ring
  rw [e, aC_sq h1, bC_sq h0 h1]
  have := dC_sq h1
  nlinarith

theorem rC_re (h0 : -1 < c) (h1 : c < 1) : (rC c).re = c := by
  have ha := aC_sq h1
  have hb := bC_sq h0 h1
  simp [rC, sC, pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith

theorem rC_im : (rC c).im = 2 * aC c * bC c := by
  simp [rC, sC, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem rC_normSq (h0 : -1 < c) (h1 : c < 1) : Complex.normSq (rC c) = 1 := by
  rw [Complex.normSq_apply, rC_re h0 h1, rC_im]
  have := ab_sq h0 h1
  nlinarith

theorem one_add_sC_ne : 1 + sC c ≠ 0 ∨ True := Or.inr trivial

theorem sC_den_ne (h1 : c < 1) : 1 + sC c ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  have ha := aC_pos h1
  simp [sC] at this
  linarith

theorem sC_num_ne (h0 : -1 < c) (h1 : c < 1) : 1 - sC c ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  have hb := bC_pos h0 h1
  simp [sC] at this
  linarith

theorem one_add_qC (h1 : c < 1) : 1 + qC c = 2 / (1 + sC c) := by
  have := sC_den_ne h1
  unfold qC
  field_simp
  ring

theorem qC_ne (h0 : -1 < c) (h1 : c < 1) : qC c ≠ 0 :=
  div_ne_zero (sC_num_ne h0 h1) (sC_den_ne h1)

theorem one_add_qC_ne (h1 : c < 1) : 1 + qC c ≠ 0 := by
  rw [one_add_qC h1]
  exact div_ne_zero (by norm_num) (sC_den_ne h1)

theorem rC_eq_q (h1 : c < 1) : rC c = 4 * qC c / (1 + qC c) ^ 2 := by
  have := sC_den_ne h1
  rw [one_add_qC h1]
  unfold qC rC
  field_simp
  ring

theorem qC_im (h0 : -1 < c) (h1 : c < 1) : 0 < (qC c).im := by
  have hb := bC_pos h0 h1
  have ha := aC_pos h1
  have hN : 0 < Complex.normSq (1 + sC c) := Complex.normSq_pos.mpr (sC_den_ne h1)
  unfold qC
  rw [Complex.div_im]
  have e1 : (1 - sC c).im = bC c := by simp [sC]
  have e2 : (1 + sC c).im = -bC c := by simp [sC]
  have e3 : (1 - sC c).re = 1 - aC c := by simp [sC]
  have e4 : (1 + sC c).re = 1 + aC c := by simp [sC]
  rw [e1, e2, e3, e4]
  have : bC c * (1 + aC c) / Complex.normSq (1 + sC c) -
      (1 - aC c) * -bC c / Complex.normSq (1 + sC c) = 2 * bC c / Complex.normSq (1 + sC c) := by
    field_simp
    ring
  rw [this]
  positivity

theorem qC_norm_lt (h0 : -1 < c) (h1 : c < 1) : ‖qC c‖ < 1 := by
  have ha := aC_pos h1
  have hb := bC_pos h0 h1
  unfold qC
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (sC_den_ne h1))]
  have e : ‖1 - sC c‖ ^ 2 < ‖1 + sC c‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp [sC]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) e

theorem qC_slit (h0 : -1 < c) (h1 : c < 1) : qC c ∈ Complex.slitPlane :=
  Or.inr (qC_im h0 h1).ne'

theorem one_add_qC_slit (h0 : -1 < c) (h1 : c < 1) : 1 + qC c ∈ Complex.slitPlane := by
  refine Or.inr ?_
  simp only [Complex.add_im, Complex.one_im, zero_add]
  exact (qC_im h0 h1).ne'

theorem Yq_qC (h0 : -1 < c) (h1 : c < 1) : Yq (qC c) = ((2 * c : ℝ) : ℂ) := by
  have hr := rC_eq_q h1
  have hq := qC_ne h0 h1
  have hp := one_add_qC_ne h1
  have hN := rC_normSq h0 h1
  have hconj : rC c * (starRingEnd ℂ) (rC c) = 1 := by
    rw [Complex.mul_conj, hN]; simp
  have hr0 : rC c ≠ 0 := by
    intro h; rw [h] at hconj; simp at hconj
  have hinv : (1 + qC c) ^ 2 / (4 * qC c) = (starRingEnd ℂ) (rC c) := by
    have : (1 + qC c) ^ 2 / (4 * qC c) = 1 / rC c := by
      rw [hr]; field_simp
    rw [this, eq_comm, eq_div_iff hr0]
    rw [mul_comm]; exact hconj
  unfold Yq
  rw [← hr, hinv, Complex.add_conj, rC_re h0 h1]

end Col

theorem aC_continuousOn {S : Set ℝ} : ContinuousOn aC S := by
  unfold aC dC
  fun_prop

theorem bC_continuousOn {S : Set ℝ} : ContinuousOn bC S := by
  unfold bC dC
  fun_prop

theorem sC_continuousOn {S : Set ℝ} : ContinuousOn sC S := by
  unfold sC
  exact (Complex.continuous_ofReal.comp_continuousOn aC_continuousOn).sub
    ((Complex.continuous_ofReal.comp_continuousOn bC_continuousOn).mul continuousOn_const)

theorem sC_differentiableAt {c : ℝ} (h0 : -1 < c) (h1 : c < 1) : DifferentiableAt ℝ sC c := by
  have hd : DifferentiableAt ℝ dC c := by
    unfold dC
    exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).sqrt
      (by have hp : 0 < 2 - 2 * c := by linarith
          exact hp.ne')
  have ha : DifferentiableAt ℝ aC c := by
    unfold aC
    exact (((hd.add (differentiableAt_const _)).sub differentiableAt_id).div_const _).sqrt
      (by simpa using (rad_a_pos h1).ne')
  have hb : DifferentiableAt ℝ bC c := by
    unfold bC
    exact (((hd.sub (differentiableAt_const _)).add differentiableAt_id).div_const _).sqrt
      (by simpa using (rad_b_pos h0 h1).ne')
  have ha' : DifferentiableAt ℝ (fun x => (aC x : ℂ)) c := ha.hasDerivAt.ofReal_comp.differentiableAt
  have hb' : DifferentiableAt ℝ (fun x => (bC x : ℂ)) c := hb.hasDerivAt.ofReal_comp.differentiableAt
  unfold sC
  exact ha'.sub (hb'.mul (differentiableAt_const _))

/-- The column curve, `Yq (q c) = 2 c`. -/
theorem curveC {l h : ℝ} (h0 : -1 < l) (h1 : h < 1) : QCurve 2 l h qC LqC LpC := by
  have m0 : ∀ τ ∈ Icc l h, -1 < τ := fun τ hτ => lt_of_lt_of_le h0 hτ.1
  have m1 : ∀ τ ∈ Icc l h, τ < 1 := fun τ hτ => lt_of_le_of_lt hτ.2 h1
  have hq : ContinuousOn qC (Icc l h) := by
    unfold qC
    exact (continuousOn_const.sub sC_continuousOn).div (continuousOn_const.add sC_continuousOn)
      (fun τ hτ => sC_den_ne (m1 τ hτ))
  refine ⟨two_ne_zero, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hq.clog fun τ hτ => qC_slit (m0 τ hτ) (m1 τ hτ)
  · exact (continuousOn_const.add hq).clog fun τ hτ => one_add_qC_slit (m0 τ hτ) (m1 τ hτ)
  · exact fun τ hτ => qC_ne (m0 τ hτ) (m1 τ hτ)
  · exact fun τ hτ => one_add_qC_ne (m1 τ hτ)
  · exact fun τ hτ => Yq_qC (m0 τ hτ) (m1 τ hτ)
  · intro τ hτ
    have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2.le⟩
    have hs := sC_differentiableAt (m0 τ hm) (m1 τ hm)
    have hd : DifferentiableAt ℝ qC τ := by
      unfold qC
      exact ((differentiableAt_const _).sub hs).div ((differentiableAt_const _).add hs)
        (sC_den_ne (m1 τ hm))
    refine ⟨deriv qC τ, hd.hasDerivAt, ?_, ?_⟩
    · exact hd.hasDerivAt.clog_real (qC_slit (m0 τ hm) (m1 τ hm))
    · exact (hd.hasDerivAt.const_add 1).clog_real (one_add_qC_slit (m0 τ hm) (m1 τ hm))
  · exact fun τ _ => Complex.log_re _
  · exact fun τ _ => Complex.log_re _

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### The q-kernel streams on a curve -/

/-- `r` in the q coordinate. -/
def rq (q : ℂ) : ℂ := 4 * q / (1 + q) ^ 2

/-- The kernel `log ‖1 - r t‖`. -/
def KQ (q : ℂ) (t : ℝ) : ℝ := Real.log ‖1 - rq q * (t : ℂ)‖

/-- Remainder of the truncated expansion of `KQ`. -/
def eK (q : ℂ) (t : ℝ) (L : ℕ) : ℝ :=
  KQ q t + 2 * Real.log ‖1 + q‖ +
    2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re * basis (n + 1) (2 * t - 1) / ((n : ℝ) + 1)

theorem one_add_ne_of_norm_lt {q : ℂ} (hq : ‖q‖ < 1) : 1 + q ≠ 0 := by
  intro h0
  have : q = -1 := by linear_combination h0
  rw [this] at hq
  simp at hq

theorem cos_arccos_z {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) :
    Real.cos (Real.arccos (2 * t - 1)) = 2 * t - 1 := Real.cos_arccos ht.1 ht.2

theorem one_sub_rq_ne {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) :
    1 - rq q * (t : ℂ) ≠ 0 := by
  have h1 := one_add_ne_of_norm_lt hq
  have hn := qnum_ne hq (Real.arccos (2 * t - 1))
  rw [cos_arccos_z ht, ← one_sub_rt h1 rfl t] at hn
  exact right_ne_zero_of_mul hn

theorem KQ_add {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) :
    KQ q t + 2 * Real.log ‖1 + q‖ =
      Real.log ‖1 - 2 * q * ((2 * t - 1 : ℝ) : ℂ) + q ^ 2‖ := by
  have h1 := one_add_ne_of_norm_lt hq
  have h2 := one_sub_rq_ne hq ht
  have e := one_sub_rt (r := rq q) h1 rfl t
  rw [← e, norm_mul, norm_pow,
    Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr h1)) (norm_ne_zero_iff.mpr h2), Real.log_pow]
  unfold KQ
  push_cast
  ring

theorem eK_bound {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) (L : ℕ) :
    |eK q t L| ≤ 2 * (‖q‖ ^ (L + 1) * (1 - ‖q‖)⁻¹ / ((L : ℝ) + 1)) := by
  have h := qker_trunc hq (Real.arccos (2 * t - 1)) L
  rw [cos_arccos_z ht] at h
  unfold eK
  rw [KQ_add hq ht]
  exact h

section Curve

variable {κ l h : ℝ} {q Lq Lp : ℝ → ℂ}

theorem cont_log1 (C : QCurve κ l h q Lq Lp) :
    ContinuousOn (fun τ => Real.log ‖1 + q τ‖) (Icc l h) :=
  (continuousOn_const.add C.cq).norm.log fun τ hτ => norm_ne_zero_iff.mpr (C.nz1 τ hτ)

theorem cont_re (C : QCurve κ l h q Lq Lp) (n : ℕ) :
    ContinuousOn (fun τ => (q τ ^ n).re) (Icc l h) :=
  Complex.continuous_re.comp_continuousOn (C.cq.pow n)

/-- The remainder integrates term by term. -/
theorem eK_integral (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (t : ℝ) (L : ℕ)
    (hK : IntervalIntegrable (fun τ => KQ (q τ) t) volume l h) :
    ∫ τ in l..h, eK (q τ) t L =
      (∫ τ in l..h, KQ (q τ) t) + 2 * (∫ τ in l..h, Real.log ‖1 + q τ‖) +
        2 * ∑ n ∈ Finset.range L, (∫ τ in l..h, (q τ ^ (n + 1)).re) *
          basis (n + 1) (2 * t - 1) / ((n : ℝ) + 1) := by
  have I1 : IntervalIntegrable (fun τ => Real.log ‖1 + q τ‖) volume l h :=
    (cont_log1 C).intervalIntegrable_of_Icc hlh
  have I2 : ∀ n, IntervalIntegrable (fun τ => (q τ ^ n).re) volume l h :=
    fun n => (cont_re C n).intervalIntegrable_of_Icc hlh
  have I3 : ∀ n ∈ Finset.range L, IntervalIntegrable
      (fun τ => (q τ ^ (n + 1)).re * basis (n + 1) (2 * t - 1) / ((n : ℝ) + 1)) volume l h :=
    fun n _ => ((I2 (n + 1)).mul_const _).div_const _
  have I4 : IntervalIntegrable
      (fun τ => ∑ n ∈ Finset.range L, (q τ ^ (n + 1)).re * basis (n + 1) (2 * t - 1) /
        ((n : ℝ) + 1)) volume l h := by
    refine ContinuousOn.intervalIntegrable_of_Icc hlh ?_
    exact continuousOn_finsetSum _ fun n _ =>
      ((cont_re C (n + 1)).mul continuousOn_const).div_const _
  unfold eK
  rw [intervalIntegral.integral_add (hK.add (I1.const_mul 2)) (I4.const_mul 2),
    intervalIntegral.integral_add hK (I1.const_mul 2), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum I3]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const]

theorem rq_continuousOn (C : QCurve κ l h q Lq Lp) :
    ContinuousOn (fun τ => rq (q τ)) (Icc l h) := by
  unfold rq
  exact (continuousOn_const.mul C.cq).div ((continuousOn_const.add C.cq).pow 2)
    fun τ hτ => pow_ne_zero 2 (C.nz1 τ hτ)

theorem tail_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (L : ℕ) :
    2 * (a ^ (L + 1) * (1 - a)⁻¹ / ((L : ℝ) + 1)) ≤ 2 * (b ^ (L + 1) * (1 - b)⁻¹ / ((L : ℝ) + 1)) := by
  have h1 : a ^ (L + 1) ≤ b ^ (L + 1) := pow_le_pow_left₀ ha hab _
  have h2 : (1 - a)⁻¹ ≤ (1 - b)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have h3 : 0 ≤ (1 - a)⁻¹ := inv_nonneg.mpr (by linarith)
  have h4 : 0 ≤ b ^ (L + 1) := pow_nonneg (ha.trans hab) _
  have : a ^ (L + 1) * (1 - a)⁻¹ ≤ b ^ (L + 1) * (1 - b)⁻¹ := mul_le_mul h1 h2 h3 h4
  have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  gcongr

/-- **Analytic stream on a segment.** -/
theorem analytic_seg (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) {qm : ℝ} (hqm : qm < 1)
    (hb : ∀ τ ∈ Icc l h, ‖q τ‖ ≤ qm) {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) (L : ℕ) :
    |(∫ τ in l..h, KQ (q τ) t) + 2 * (∫ τ in l..h, Real.log ‖1 + q τ‖) +
        2 * ∑ n ∈ Finset.range L, (∫ τ in l..h, (q τ ^ (n + 1)).re) *
          basis (n + 1) (2 * t - 1) / ((n : ℝ) + 1)| ≤
      (h - l) * (2 * (qm ^ (L + 1) * (1 - qm)⁻¹ / ((L : ℝ) + 1))) := by
  have hK : IntervalIntegrable (fun τ => KQ (q τ) t) volume l h := by
    refine ContinuousOn.intervalIntegrable_of_Icc hlh ?_
    unfold KQ
    refine ((continuousOn_const.sub ((rq_continuousOn C).mul continuousOn_const)).norm).log ?_
    intro τ hτ
    exact norm_ne_zero_iff.mpr (one_sub_rq_ne ((hb τ hτ).trans_lt hqm) ht)
  rw [← eK_integral C hlh t L hK, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := h)
    (f := fun τ => eK (q τ) t L)
    (C := 2 * (qm ^ (L + 1) * (1 - qm)⁻¹ / ((L : ℝ) + 1))) ?_
  · rw [abs_of_nonneg (by linarith : 0 ≤ h - l)] at this
    linarith
  · intro τ hτ
    rw [uIoc_of_le hlh] at hτ
    have hm : τ ∈ Icc l h := ⟨hτ.1.le, hτ.2⟩
    have hb' := hb τ hm
    rw [Real.norm_eq_abs]
    exact (eK_bound (hb'.trans_lt hqm) ht L).trans (tail_mono (norm_nonneg _) hb' hqm L)

end Curve

/-! ### Real curves: the kernels -/

theorem qc_pow_re (r : ℝ → ℝ) (y : ℝ) (n : ℕ) : (qc r y ^ n).re = qr (r y) ^ n := by
  unfold qc
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem norm_one_add_qc (r : ℝ → ℝ) (y : ℝ) : ‖1 + qc r y‖ = 1 + qr (r y) := by
  have e : (1 : ℂ) + qc r y = ((1 + qr (r y) : ℝ) : ℂ) := by
    unfold qc
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_add_qr_pos _)]

theorem rq_qc {r : ℝ → ℝ} {y : ℝ} (h1 : r y ≤ 1) : rq (qc r y) = (r y : ℂ) := by
  have e := r_eq_q h1
  unfold rq qc
  conv_rhs => rw [e]
  push_cast
  rfl

theorem KQ_qc {r : ℝ → ℝ} {y : ℝ} (h1 : r y ≤ 1) (t : ℝ) :
    KQ (qc r y) t = Real.log |1 - r y * t| := by
  unfold KQ
  rw [rq_qc h1]
  have e : (1 : ℂ) - (r y : ℂ) * (t : ℂ) = ((1 - r y * t : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]

theorem qr_pos {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 0 < qr r := by
  have hs : √(1 - r) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  exact div_pos (by linarith) (den_pos r)

theorem qr_lt_one {r : ℝ} (h1 : r < 1) : qr r < 1 := by
  have hs : 0 < √(1 - r) := Real.sqrt_pos.mpr (by linarith)
  unfold qr
  rw [div_lt_one (den_pos r)]
  linarith

/-! ### Row kernels are integrable -/

theorem rowlog_int {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1) :
    IntervalIntegrable (fun y => Real.log |1 - YCell.physX y * t|) volume lo hi := by
  rcases h1.lt_or_eq with h1 | rfl
  · refine ContinuousOn.intervalIntegrable_of_Icc hlt.le ?_
    have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
    refine ContinuousOn.log (continuous_abs.comp_continuousOn
      (continuousOn_const.sub (hc.mul continuousOn_const))) ?_
    intro y hy
    obtain ⟨a, b⟩ := physX_mem (h2.trans hy.1)
    have : YCell.physX y * t < 1 := by nlinarith
    exact abs_ne_zero.mpr (by linarith)
  · have hK := rowK_integrable (c := ⟨lo, hi, 0, hlt, le_rfl⟩) (Or.inl h2) (x := 1) one_ne_zero
    simp only at hK
    refine (hK.const_mul (1 / 2)).congr ?_
    intro y _
    simp only [rowK, one_mul, mul_one]
    rw [abs_sub_comm 1 (YCell.physX y)]
    ring

theorem rowlog2_int {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1) :
    IntervalIntegrable (fun y => Real.log |t - YCell.physX y|) volume lo hi := by
  have hK := rowK_integrable (c := ⟨lo, hi, 0, hlt, le_rfl⟩) (Or.inl h2) (x := t) h0.ne'
  simp only at hK
  refine (hK.sub (rowlog_int h2 hlt h0 h1)).congr ?_
  intro y _
  simp only [rowK]
  rw [mul_comm t]
  ring

/-! ### The S19 beta tail of the same-sign reflection -/

def Hq (q : ℝ) : ℝ := 1 / (4 * q ^ 2 * (1 + q)) + 1 / (q * (1 + q) ^ 3)

def Fq (L : ℕ) (q : ℝ) : ℝ :=
  q ^ (L + 2) / ((L : ℝ) + 2) - 2 * q ^ (L + 3) / ((L : ℝ) + 3) + q ^ (L + 4) / ((L : ℝ) + 4)

/-- The composed beta tail on a segment with `a = q(hi) ≤ b = q(lo)`. -/
def betaT (L : ℕ) (a b : ℝ) : ℝ := 2 / ((L : ℝ) + 1) * Hq a * (Fq L b - Fq L a)

theorem hasDeriv_Fq (L : ℕ) (q : ℝ) : HasDerivAt (Fq L) (q ^ (L + 1) * (1 - q) ^ 2) q := by
  unfold Fq
  have h2 := (hasDerivAt_pow (L + 2) q).div_const ((L : ℝ) + 2)
  have h3 := ((hasDerivAt_pow (L + 3) q).const_mul 2).div_const ((L : ℝ) + 3)
  have h4 := (hasDerivAt_pow (L + 4) q).div_const ((L : ℝ) + 4)
  have := (h2.sub h3).add h4
  convert this using 1
  have a2 : ((L : ℝ) + 2) ≠ 0 := by positivity
  have a3 : ((L : ℝ) + 3) ≠ 0 := by positivity
  have a4 : ((L : ℝ) + 4) ≠ 0 := by positivity
  simp only [show L + 2 - 1 = L + 1 from rfl, show L + 3 - 1 = L + 2 from rfl,
    show L + 4 - 1 = L + 3 from rfl, Nat.cast_add, Nat.cast_ofNat]
  field_simp
  ring

theorem Hq_pos {q : ℝ} (h : 0 < q) : 0 < Hq q := by
  unfold Hq; positivity

theorem Hq_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Hq b ≤ Hq a := by
  unfold Hq
  have hb : 0 < b := ha.trans_le hab
  refine add_le_add ?_ ?_
  · apply one_div_le_one_div_of_le (by positivity)
    gcongr
  · apply one_div_le_one_div_of_le (by positivity)
    gcongr

theorem fQ_real {q : ℝ} (h : 0 < q) : fQ (q : ℂ) = (((1 - q) ^ 3 * Hq q : ℝ) : ℂ) := by
  have h0 : (q : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  have h1 : (1 : ℂ) + (q : ℂ) ≠ 0 := by
    have : (1 + q : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  unfold fQ Hq
  push_cast
  field_simp
  ring

theorem eK_int {κ l h : ℝ} {q Lq Lp : ℝ → ℂ} (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (t : ℝ)
    (L : ℕ) (hK : IntervalIntegrable (fun τ => KQ (q τ) t) volume l h) :
    IntervalIntegrable (fun τ => eK (q τ) t L) volume l h := by
  have I1 : IntervalIntegrable (fun τ => Real.log ‖1 + q τ‖) volume l h :=
    (cont_log1 C).intervalIntegrable_of_Icc hlh
  have I4 : IntervalIntegrable
      (fun τ => ∑ n ∈ Finset.range L, (q τ ^ (n + 1)).re * basis (n + 1) (2 * t - 1) /
        ((n : ℝ) + 1)) volume l h := by
    refine ContinuousOn.intervalIntegrable_of_Icc hlh ?_
    exact continuousOn_finsetSum _ fun n _ =>
      ((cont_re C (n + 1)).mul continuousOn_const).div_const _
  exact (hK.add (I1.const_mul 2)).add (I4.const_mul 2)

theorem KR_int {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1) :
    IntervalIntegrable (fun y => KQ (qc rR y) t) volume lo hi := by
  refine (rowlog_int h2 hlt h0 h1).congr ?_
  intro y hy
  rw [uIoc_of_le hlt.le] at hy
  have := (physX_mem (h2.trans hy.1.le)).2
  simp only [KQ_qc (r := rR) (y := y) this t, rR]

/-- **Same-sign reflection on a segment, with the composed beta tail.** -/
theorem refl_seg {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1) (L : ℕ) :
    |(∫ y in lo..hi, KQ (qc rR y) t) + 2 * (∫ y in lo..hi, Real.log ‖1 + qc rR y‖) +
        2 * ∑ n ∈ Finset.range L, (∫ y in lo..hi, (qc rR y ^ (n + 1)).re) *
          basis (n + 1) (2 * t - 1) / ((n : ℝ) + 1)| ≤
      betaT L (qr (rR hi)) (qr (rR lo)) := by
  have C : QCurve 1 lo hi (qc rR) (Lqc rR) (Lpc rR) := curveR h2
  have hK := KR_int h2 hlt h0 h1
  have ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [← eK_integral C hlt.le t L hK]
  have hint := (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).1 (eK_int C hlt.le t L hK)
  set q : ℝ → ℝ := fun y => qr (rR y) with hqdef
  have hq0 : ∀ y ∈ Icc lo hi, 0 < q y := fun y hy => by
    have m := physX_mem (h2.trans hy.1)
    exact qr_pos m.1 m.2
  have hq1 : ∀ y ∈ Ioo lo hi, q y < 1 := fun y hy =>
    qr_lt_one (physX_lt_one (lt_of_le_of_lt h2 hy.1))
  have hder : ∀ y ∈ Ioo lo hi, HasDerivAt q (deriv q y) y ∧
      (1 - q y) ^ 3 * Hq (q y) * deriv q y = -1 := by
    intro y hy
    have hy2 := lt_of_le_of_lt h2 hy.1
    have hd : HasDerivAt q (deriv q y) y :=
      (qr_differentiableAt (r := rR) (physX_differentiableAt hy2) (physX_lt_one hy2)).hasDerivAt
    refine ⟨hd, ?_⟩
    have hc : HasDerivAt (qc rR) ((deriv q y : ℝ) : ℂ) y := hd.ofReal_comp
    have key := C.f_mul hy hc
    have e : qc rR y = ((q y : ℝ) : ℂ) := rfl
    rw [e, fQ_real (hq0 y ⟨hy.1.le, hy.2.le⟩)] at key
    exact_mod_cast key
  have hP : ∀ y ∈ Ioo lo hi, 0 < (1 - q y) ^ 3 * Hq (q y) := fun y hy => by
    have a := Hq_pos (hq0 y ⟨hy.1.le, hy.2.le⟩)
    have b : 0 < 1 - q y := by linarith [hq1 y hy]
    positivity
  have hneg : ∀ y ∈ Ioo lo hi, deriv q y < 0 := fun y hy => by
    have a := hP y hy
    have b := (hder y hy).2
    by_contra hc
    have := mul_nonneg a.le (not_lt.mp hc)
    linarith
  have hqc : ContinuousOn q (Icc lo hi) :=
    qr_continuousOn (physX_continuousOn (Or.inl h2))
  have hanti : AntitoneOn q (Icc lo hi) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc lo hi) hqc ?_ ?_
    · rw [interior_Icc]
      exact fun y hy => (hder y hy).1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      exact fun y hy => (hneg y hy).le
  set a := q hi with ha
  have mhi : hi ∈ Icc lo hi := ⟨hlt.le, le_rfl⟩
  have mlo : lo ∈ Icc lo hi := ⟨le_rfl, hlt.le⟩
  have ha0 : 0 < a := hq0 hi mhi
  have hLp : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  set c := 2 / ((L : ℝ) + 1) * Hq a with hc
  have hc0 : 0 ≤ c := by
    have := Hq_pos ha0
    positivity
  set g : ℝ → ℝ := fun y => -(c * Fq L (q y)) with hg
  set g' : ℝ → ℝ := fun y => -(c * (q y ^ (L + 1) * (1 - q y) ^ 2 * deriv q y)) with hg'
  have gc : ContinuousOn g (Icc lo hi) := by
    refine ContinuousOn.neg (continuousOn_const.mul ?_)
    intro y hy
    exact (hasDeriv_Fq L (q y)).continuousAt.comp_continuousWithinAt (hqc y hy)
  have gd : ∀ y ∈ Ioo lo hi, HasDerivWithinAt g (g' y) (Ioi y) y := by
    intro y hy
    have d := ((hasDeriv_Fq L (q y)).comp y (hder y hy).1).const_mul c
    exact d.neg.hasDerivWithinAt
  have hbound : ∀ y ∈ Ioo lo hi, |eK (qc rR y) t L| ≤ g' y := by
    intro y hy
    have hm : y ∈ Icc lo hi := ⟨hy.1.le, hy.2.le⟩
    have q0 := hq0 y hm
    have q1 := hq1 y hy
    have hn : ‖qc rR y‖ = q y := by
      have e : qc rR y = ((q y : ℝ) : ℂ) := rfl
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q0]
    have hb := eK_bound (q := qc rR y) (by rw [hn]; exact q1) ht L
    rw [hn] at hb
    refine hb.trans ?_
    have hay : a ≤ q y := hanti hm mhi hy.2.le
    have hH := Hq_anti ha0 hay
    have hHy := Hq_pos q0
    have h1q : 0 < 1 - q y := by linarith
    have hdv : deriv q y = -(1 / ((1 - q y) ^ 3 * Hq (q y))) := by
      have := (hder y hy).2
      have hp := (hP y hy).ne'
      field_simp
      linarith
    have e : g' y = 2 * (q y ^ (L + 1) * (1 - q y)⁻¹ / ((L : ℝ) + 1)) * (Hq a / Hq (q y)) := by
      simp only [hg', hc]
      rw [hdv]
      field_simp
    rw [e]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [le_div_iff₀ hHy]
    linarith
  have u1 := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hlt.le gc gd hint
    (fun y hy => (le_abs_self _).trans (hbound y hy))
  have u2 := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hlt.le gc gd hint.neg
    (fun y hy => (neg_le_abs _).trans (hbound y hy))
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at u2
  have fin : g hi - g lo = betaT L a (q lo) := by
    simp only [hg, hc, betaT]
    ring
  rw [fin] at u1 u2
  exact abs_le.mpr ⟨by linarith, u1⟩

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### Exact direct moment primitives -/

/-- Primitive of `T_n`. -/
def kP : ℕ → ℝ → ℝ
  | 0, z => z
  | 1, z => z ^ 2 / 2
  | n + 2, z => basis (n + 3) z / (2 * ((n : ℝ) + 3)) - basis (n + 1) z / (2 * ((n : ℝ) + 1))

/-- Primitive of `T_n/(1+z)`. -/
def iP : ℕ → ℝ → ℝ
  | 0, z => Real.log (1 + z)
  | 1, z => z - Real.log (1 + z)
  | n + 2, z => 2 * kP (n + 1) z - 2 * iP (n + 1) z - iP n z

/-- Primitive of `T_n/(1+z)²`. -/
def jP : ℕ → ℝ → ℝ
  | 0, z => -1 / (1 + z)
  | 1, z => Real.log (1 + z) + 1 / (1 + z)
  | n + 2, z => 2 * iP (n + 1) z - 2 * jP (n + 1) z - jP n z

/-- The direct moment primitive. -/
def muP (n : ℕ) (z : ℝ) : ℝ := 2 * jP n z - kP n z / 2

theorem basis_add_two (n : ℕ) (z : ℝ) :
    basis (n + 2) z = 2 * z * basis (n + 1) z - basis n z := by
  unfold basis
  have h := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
  push_cast
  rw [h]
  simp

theorem basis_one' (z : ℝ) : basis 1 z = z := by
  simp [basis]

theorem hasDeriv_basis (n : ℕ) (z : ℝ) :
    HasDerivAt (basis (n + 1))
      (((n : ℝ) + 1) * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval z) z := by
  have h := (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).hasDerivAt z
  rw [Polynomial.Chebyshev.T_derivative_eq_U] at h
  have e : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by push_cast; ring
  rw [e] at h
  refine HasDerivAt.congr_deriv (f := basis (n + 1)) h ?_
  simp

theorem two_basis_eq_U (n : ℕ) (z : ℝ) :
    2 * basis (n + 2) z = (Polynomial.Chebyshev.U ℝ ((n + 2 : ℕ) : ℤ)).eval z -
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval z := by
  have h := Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ (n : ℤ)
  have := congrArg (Polynomial.eval z) h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at this
  unfold basis
  push_cast
  exact this

theorem hasDeriv_kP (n : ℕ) (z : ℝ) : HasDerivAt (fun x => kP n x) (basis n z) z := by
  match n with
  | 0 =>
    simp only [kP, basis_zero]
    exact hasDerivAt_id z
  | 1 =>
    simp only [kP, basis_one']
    exact (((hasDerivAt_id' z).fun_pow 2).div_const 2).congr_deriv (by norm_num)
  | n + 2 =>
    simp only [kP]
    have h3 := (hasDeriv_basis (n + 2) z).div_const (2 * (((n + 2 : ℕ) : ℝ) + 1))
    have h1 := (hasDeriv_basis n z).div_const (2 * ((n : ℝ) + 1))
    have hd := h3.sub h1
    have e : (((n + 2 : ℕ) : ℝ) + 1) = (n : ℝ) + 3 := by push_cast; ring
    rw [e] at hd
    convert hd using 1
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hn3 : ((n : ℝ) + 3) ≠ 0 := by positivity
    have := two_basis_eq_U n z
    field_simp
    linarith

theorem hasDeriv_iP {z : ℝ} (hz : 0 < 1 + z) :
    ∀ n, HasDerivAt (fun x => iP n x) (basis n z / (1 + z)) z
  | 0 => by
    simp only [iP, basis_zero]
    exact ((hasDerivAt_id' z).const_add 1).log hz.ne'
  | 1 => by
    simp only [iP, basis_one']
    have := (hasDerivAt_id' z).fun_sub (((hasDerivAt_id' z).const_add 1).log hz.ne')
    convert this using 1
    field_simp
    ring
  | n + 2 => by
    simp only [iP]
    have a := hasDeriv_iP hz n
    have b := hasDeriv_iP hz (n + 1)
    have c := hasDeriv_kP (n + 1) z
    have hd := ((c.const_mul 2).sub (b.const_mul 2)).sub a
    convert hd using 1
    rw [basis_add_two]
    field_simp
    ring

theorem hasDeriv_jP {z : ℝ} (hz : 0 < 1 + z) :
    ∀ n, HasDerivAt (fun x => jP n x) (basis n z / (1 + z) ^ 2) z
  | 0 => by
    simp only [jP, basis_zero]
    have := (hasDerivAt_const z (-1 : ℝ)).fun_div ((hasDerivAt_id' z).const_add 1) hz.ne'
    exact this.congr_deriv (by ring)
  | 1 => by
    simp only [jP, basis_one']
    have h1 := ((hasDerivAt_id' z).const_add 1).log hz.ne'
    have h2 := (hasDerivAt_const z (1 : ℝ)).fun_div ((hasDerivAt_id' z).const_add 1) hz.ne'
    have := h1.fun_add h2
    refine this.congr_deriv ?_
    field_simp
    ring
  | n + 2 => by
    simp only [jP]
    have a := hasDeriv_jP hz n
    have b := hasDeriv_jP hz (n + 1)
    have c := hasDeriv_iP hz (n + 1)
    have hd := ((c.const_mul 2).sub (b.const_mul 2)).sub a
    convert hd using 1
    rw [basis_add_two]
    field_simp
    ring

theorem hasDeriv_muP {z : ℝ} (hz : 0 < 1 + z) (n : ℕ) :
    HasDerivAt (fun x => muP n x) (basis n z * (2 / (1 + z) ^ 2 - 1 / 2)) z := by
  unfold muP
  have := ((hasDeriv_jP hz n).const_mul 2).sub ((hasDeriv_kP n z).div_const 2)
  convert this using 1
  ring

/-- The derivative of `X` in `Y`. -/
theorem physX_deriv {y : ℝ} (hy : 2 < y) :
    ∃ d, HasDerivAt YCell.physX d y ∧ d * (1 - 1 / YCell.physX y ^ 2) = 1 := by
  have hd := (physX_differentiableAt hy).hasDerivAt
  set d := deriv YCell.physX y
  have h0 := (physX_mem hy.le).1.ne'
  refine ⟨d, hd, ?_⟩
  have h1 := hd.add ((hasDerivAt_const y (1 : ℝ)).div hd h0)
  have hev : (YCell.physX + fun x => 1 / YCell.physX x) =ᶠ[𝓝 y] id := by
    filter_upwards [lt_mem_nhds hy] with x hx
    exact physX_add_inv hx.le
  have h2 := (h1.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_id y)
  have e : d * (1 - 1 / YCell.physX y ^ 2) =
      d + (0 * YCell.physX y - 1 * d) / YCell.physX y ^ 2 := by
    field_simp
    ring
  rw [e]
  exact h2

theorem basis_continuous (n : ℕ) : Continuous (basis n) := by
  unfold basis
  exact (Polynomial.Chebyshev.T ℝ (n : ℤ)).continuous

/-- `∫ T_n(2X-1) dY` is an endpoint difference of `muP`. -/
theorem cheb_moment {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (n : ℕ) :
    ∫ y in lo..hi, basis n (2 * YCell.physX y - 1) =
      muP n (2 * YCell.physX lo - 1) - muP n (2 * YCell.physX hi - 1) := by
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  have hz : ∀ y ∈ Icc lo hi, 0 < 1 + (2 * YCell.physX y - 1) := fun y hy => by
    have := (physX_mem (h2.trans hy.1)).1
    linarith
  have hzc : ContinuousOn (fun y => 2 * YCell.physX y - 1) (Icc lo hi) :=
    (continuousOn_const.mul hc).sub continuousOn_const
  have hF : ContinuousOn (fun y => -muP n (2 * YCell.physX y - 1)) (Icc lo hi) := by
    refine ContinuousOn.neg ?_
    intro y hy
    exact ContinuousAt.comp_continuousWithinAt (f := fun y => 2 * YCell.physX y - 1)
      (hasDeriv_muP (hz y hy) n).continuousAt (hzc y hy)
  have hint : IntervalIntegrable (fun y => basis n (2 * YCell.physX y - 1)) volume lo hi :=
    ((basis_continuous n).comp_continuousOn hzc).intervalIntegrable_of_Icc hlt.le
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le hF ?_ hint
  · rw [key]; ring
  · intro y hy
    have hm : y ∈ Icc lo hi := ⟨hy.1.le, hy.2.le⟩
    have hy2 : 2 < y := lt_of_le_of_lt h2 hy.1
    obtain ⟨d, hd, hd1⟩ := physX_deriv hy2
    have hX := (physX_mem hy2.le).1
    have hz' : HasDerivAt (fun x => 2 * YCell.physX x - 1) (2 * d) y :=
      (hd.const_mul 2).sub_const 1
    have h := ((hasDeriv_muP (hz y hm) n).comp y hz').fun_neg
    refine h.congr_deriv ?_
    have e : (1 + (2 * YCell.physX y - 1)) = 2 * YCell.physX y := by ring
    rw [e]
    have e2 : -(basis n (2 * YCell.physX y - 1) * (2 / (2 * YCell.physX y) ^ 2 - 1 / 2) * (2 * d)) =
        basis n (2 * YCell.physX y - 1) * (d * (1 - 1 / YCell.physX y ^ 2)) := by
      field_simp
      ring
    rw [e2, hd1, mul_one]

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### Signed piecewise-constant profiles -/

/-- A segment of constant density `rho` on `[lo,hi]`. -/
structure Seg where
  lo : ℝ
  hi : ℝ
  rho : ℝ

/-- Pairing of a profile with the differences of `F`. -/
def evS (P : List Seg) (F : ℝ → ℝ) : ℝ := (P.map fun g => g.rho * (F g.hi - F g.lo)).sum

/-- Pairing of atoms `(y, W)` with `F`. -/
def evE (E : List (ℝ × ℝ)) (F : ℝ → ℝ) : ℝ := (E.map fun e => e.2 * F e.1).sum

/-- `E` are the jumps of the profile `P`: `W(lo) += ρ`, `W(hi) -= ρ`, merged at equal abscissae. -/
def Atoms (P : List Seg) (E : List (ℝ × ℝ)) : Prop := ∀ F, evS P F = -evE E F

/-- Integral of `f` against the profile. -/
def pint (P : List Seg) (f : ℝ → ℝ) : ℝ := (P.map fun g => g.rho * ∫ y in g.lo..g.hi, f y).sum

/-- Variation-weighted sum of a per-segment error. -/
def absum (P : List Seg) (e : Seg → ℝ) : ℝ := (P.map fun g => |g.rho| * e g).sum

theorem abs_list_sum_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ a ∈ l, |f a| ≤ g a) :
    |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- The stream identity on a list: no hypotheses, only linearity. -/
theorem list_eq (P : List Seg) (K : ℝ → ℝ) (A : ℕ → ℝ → ℝ) (b : ℕ → ℝ) (L : ℕ) :
    pint P K - ∑ k ∈ Finset.range L, evS P (A k) * b k =
      (P.map fun g => g.rho * ((∫ y in g.lo..g.hi, K y) -
        ∑ k ∈ Finset.range L, (A k g.hi - A k g.lo) * b k)).sum := by
  induction P with
  | nil => simp [pint, evS]
  | cons g P ih =>
    simp only [pint, evS, List.map_cons, List.sum_cons] at ih ⊢
    have e : ∑ k ∈ Finset.range L,
        (g.rho * (A k g.hi - A k g.lo) + (P.map fun g => g.rho * (A k g.hi - A k g.lo)).sum) * b k =
        g.rho * ∑ k ∈ Finset.range L, (A k g.hi - A k g.lo) * b k +
          ∑ k ∈ Finset.range L, (P.map fun g => g.rho * (A k g.hi - A k g.lo)).sum * b k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, ← ih]
    ring

theorem list_approx (P : List Seg) (K : ℝ → ℝ) (A : ℕ → ℝ → ℝ) (b : ℕ → ℝ) (L : ℕ) (e : Seg → ℝ)
    (h : ∀ g ∈ P, |(∫ y in g.lo..g.hi, K y) -
      ∑ k ∈ Finset.range L, (A k g.hi - A k g.lo) * b k| ≤ e g) :
    |pint P K - ∑ k ∈ Finset.range L, evS P (A k) * b k| ≤ absum P e := by
  rw [list_eq]
  refine abs_list_sum_le _ _ _ fun g hg => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h g hg) (abs_nonneg _)

/-! ### The direct stream -/

/-- Direct endpoint primitives. -/
def Adir : ℕ → ℝ → ℝ
  | 0, y => -Real.log 4 * y
  | n + 1, y => 2 / ((n : ℝ) + 1) * muP (n + 1) (2 * YCell.physX y - 1)

theorem basisX_int {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (n : ℕ) :
    IntervalIntegrable (fun y => basis n (2 * YCell.physX y - 1)) volume lo hi := by
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  exact ((basis_continuous n).comp_continuousOn
    ((continuousOn_const.mul hc).sub continuousOn_const)).intervalIntegrable_of_Icc hlt.le

theorem seg_Rdir_eq {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1) (N : ℕ) :
    ∫ y in lo..hi, Rdir N t y = (∫ y in lo..hi, Real.log |t - YCell.physX y|) -
      ∑ k ∈ Finset.range (N + 1), (Adir k hi - Adir k lo) * basis k (2 * t - 1) := by
  have I1 := rowlog2_int h2 hlt h0 h1
  have I2 : ∀ n ∈ Finset.range N, IntervalIntegrable (fun y => 2 / ((n : ℝ) + 1) *
      (basis (n + 1) (2 * YCell.physX y - 1) * basis (n + 1) (2 * t - 1))) volume lo hi :=
    fun n _ => ((basisX_int h2 hlt (n + 1)).mul_const _).const_mul _
  have I3 : IntervalIntegrable (fun y => ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) *
      (basis (n + 1) (2 * YCell.physX y - 1) * basis (n + 1) (2 * t - 1))) volume lo hi := by
    have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
    refine ContinuousOn.intervalIntegrable_of_Icc hlt.le ?_
    refine continuousOn_finsetSum _ fun n _ => continuousOn_const.mul
      (ContinuousOn.mul ?_ continuousOn_const)
    exact (basis_continuous (n + 1)).comp_continuousOn
      ((continuousOn_const.mul hc).sub continuousOn_const)
  unfold Rdir
  rw [intervalIntegral.integral_add (I1.add intervalIntegrable_const) I3,
    intervalIntegral.integral_add I1 intervalIntegrable_const, intervalIntegral.integral_const,
    intervalIntegral.integral_finsetSum I2, Finset.sum_range_succ']
  have e : ∀ n ∈ Finset.range N, ∫ y in lo..hi, 2 / ((n : ℝ) + 1) *
      (basis (n + 1) (2 * YCell.physX y - 1) * basis (n + 1) (2 * t - 1)) =
      -((Adir (n + 1) hi - Adir (n + 1) lo) * basis (n + 1) (2 * t - 1)) := by
    intro n _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
      cheb_moment h2 hlt]
    simp only [Adir]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
  simp only [Adir, basis_zero, smul_eq_mul]
  ring

/-- The bounded-variation tail functional of the direct kernel. -/
def dirV (N : ℕ) (P : List Seg) (E : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (E.map fun e => |e.2| * (kap N |t - YCell.physX e.1| * bet (Th e.1))).sum +
    (P.map fun g => |g.rho| * ∫ θ in Th g.lo..Th g.hi, kap N |t - sth θ| * dbet θ).sum

theorem kap_continuous (N : ℕ) : Continuous (kap N) := by
  unfold kap
  refine continuous_const.div (by fun_prop) fun d => ?_
  exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'

theorem sth_continuous : Continuous sth := by
  unfold sth
  fun_prop

theorem HN_continuous (N : ℕ) (φ : ℝ) : Continuous (HN N φ) := by
  unfold HN
  exact ((GN_continuous N).comp (by fun_prop)).add ((GN_continuous N).comp (by fun_prop))

theorem seg_tail {N : ℕ} (hN : 1 ≤ N) {t φ lo hi : ℝ} (ht : t = sth φ) (h2 : 2 ≤ lo)
    (hlt : lo < hi) :
    |∫ θ in Th lo..Th hi, HN N φ θ * dbet θ| ≤
      2 / N * ∫ θ in Th lo..Th hi, kap N |t - sth θ| * dbet θ := by
  have hab := Th_lt h2 hlt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hsub : Icc (Th lo) (Th hi) ⊆ Ico 0 π := fun θ hθ =>
    ⟨ml.1.trans hθ.1, lt_of_le_of_lt hθ.2 mh.2⟩
  have cd : ContinuousOn dbet (Icc (Th lo) (Th hi)) := continuousOn_dbet.mono hsub
  have c1 : ContinuousOn (fun θ => HN N φ θ * dbet θ) (Icc (Th lo) (Th hi)) :=
    (HN_continuous N φ).continuousOn.mul cd
  have ck : Continuous fun θ => kap N |t - sth θ| :=
    (kap_continuous N).comp (continuous_abs.comp (continuous_const.sub sth_continuous))
  have c2 : ContinuousOn (fun θ => kap N |t - sth θ| * dbet θ) (Icc (Th lo) (Th hi)) :=
    ck.continuousOn.mul cd
  rw [← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs hab.le).trans ?_
  refine intervalIntegral.integral_mono_on hab.le
    (c1.abs.intervalIntegrable_of_Icc hab.le)
    ((continuousOn_const.mul c2).intervalIntegrable_of_Icc hab.le) ?_
  intro θ hθ
  have hm := hsub hθ
  rw [abs_mul, abs_of_nonneg (dbet_nonneg hm.1 hm.2), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (dbet_nonneg hm.1 hm.2)
  have := HN_abs_le hN θ φ
  rwa [← ht] at this

/-- **The direct stream** with the bounded-variation tail: no boundary series. -/
theorem dir_stream {N : ℕ} (hN : 1 ≤ N) {P : List Seg} {E : List (ℝ × ℝ)} (hA : Atoms P E)
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E, 2 ≤ e.1) {t : ℝ} (h0 : 0 < t)
    (h1 : t ≤ 1) :
    |pint P (fun y => Real.log |t - YCell.physX y|) -
        ∑ k ∈ Finset.range (N + 1), evS P (Adir k) * basis k (2 * t - 1)| ≤
      2 / N * dirV N P E t := by
  set φ := Real.arccos (2 * t - 1) with hφ
  have ht : t = sth φ := by
    have := two_sth_sub φ
    rw [hφ, Real.cos_arccos (by linarith) (by linarith), ← hφ] at this
    linarith
  set B : ℝ → ℝ := fun y => HN N φ (Th y) * bet (Th y) with hB
  rw [list_eq]
  have e1 : (P.map fun g => g.rho * ((∫ y in g.lo..g.hi, Real.log |t - YCell.physX y|) -
      ∑ k ∈ Finset.range (N + 1), (Adir k g.hi - Adir k g.lo) * basis k (2 * t - 1))) =
      P.map fun g => g.rho * (B g.hi - B g.lo) -
        g.rho * ∫ θ in Th g.lo..Th g.hi, HN N φ θ * dbet θ := by
    refine List.map_congr_left fun g hg => ?_
    obtain ⟨a, b⟩ := hP g hg
    rw [← seg_Rdir_eq a b h0 h1 N, seg_direct ht a b]
    simp only [hB]
    ring
  have e2 : ∀ l : List Seg, (l.map fun g => g.rho * (B g.hi - B g.lo) -
        g.rho * ∫ θ in Th g.lo..Th g.hi, HN N φ θ * dbet θ).sum =
      evS l B - (l.map fun g => g.rho * ∫ θ in Th g.lo..Th g.hi, HN N φ θ * dbet θ).sum := by
    intro l
    induction l with
    | nil => simp [evS]
    | cons g l ih =>
      simp only [evS, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring
  rw [e1, e2, hA B]
  have b1 : |evE E B| ≤ 2 / N *
      (E.map fun e => |e.2| * (kap N |t - YCell.physX e.1| * bet (Th e.1))).sum := by
    rw [← List.sum_map_mul_left]
    refine abs_list_sum_le _ _ _ fun e he => ?_
    have hy := hE e he
    have m := Th_mem hy
    have hb := bet_nonneg m.1 m.2
    simp only [hB]
    rw [abs_mul, abs_mul, abs_of_nonneg hb]
    have hH := HN_abs_le hN (Th e.1) φ
    rw [← ht, sth_Th hy] at hH
    have := mul_le_mul_of_nonneg_right hH hb
    calc |e.2| * (|HN N φ (Th e.1)| * bet (Th e.1))
        ≤ |e.2| * (2 / N * kap N |t - YCell.physX e.1| * bet (Th e.1)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have b2 : |(P.map fun g => g.rho * ∫ θ in Th g.lo..Th g.hi, HN N φ θ * dbet θ).sum| ≤ 2 / N *
      (P.map fun g => |g.rho| * ∫ θ in Th g.lo..Th g.hi, kap N |t - sth θ| * dbet θ).sum := by
    rw [← List.sum_map_mul_left]
    refine abs_list_sum_le _ _ _ fun g hg => ?_
    obtain ⟨a, b⟩ := hP g hg
    have := seg_tail hN ht a b
    rw [abs_mul]
    calc |g.rho| * |∫ θ in Th g.lo..Th g.hi, HN N φ θ * dbet θ|
        ≤ |g.rho| * (2 / N * ∫ θ in Th g.lo..Th g.hi, kap N |t - sth θ| * dbet θ) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  unfold dirV
  rw [mul_add]
  calc |-evE E B - _| ≤ |evE E B| + |(P.map fun g => g.rho *
        ∫ θ in Th g.lo..Th g.hi, HN N φ θ * dbet θ).sum| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_neg]
    _ ≤ _ := add_le_add b1 b2

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### Endpoint primitives with real seeds (no argument of a complex logarithm is evaluated) -/

theorem Lplus_re {y : ℝ} {q Lq Lq' Lp Lp' : ℂ} (h1 : Lq.re = Lq'.re) (h2 : Lp.re = Lp'.re) :
    (Lplus (y : ℂ) q Lq Lp).re = (Lplus (y : ℂ) q Lq' Lp').re := by
  unfold Lplus
  have e : ∀ z : ℂ, (-(y : ℂ) * z).re = -y * z.re := fun z => by simp
  have m : ∀ z : ℂ, (z / 4).re = z.re / 4 := fun z => by simp
  simp only [Complex.add_re, Complex.sub_re, e, m, h1, h2]

theorem Lqprim_re {y : ℝ} {q Lq Lq' : ℂ} (h1 : Lq.re = Lq'.re) :
    (Lqprim (y : ℂ) q Lq).re = (Lqprim (y : ℂ) q Lq').re := by
  unfold Lqprim
  have e : ∀ z : ℂ, ((y : ℂ) * z).re = y * z.re := fun z => by simp
  have m : ∀ z : ℂ, (z / 2).re = z.re / 2 := fun z => by simp
  simp only [Complex.add_re, Complex.sub_re, e, m, h1]

/-- The endpoint primitives of the q-stream of a curve with `Yq (q τ) = κ τ`. -/
def QS (κ : ℝ) (q : ℝ → ℂ) : ℕ → ℝ → ℝ
  | 0, y => 2 / κ * (Lplus ((κ * y : ℝ) : ℂ) (q y) ((Real.log ‖q y‖ : ℝ) : ℂ)
      ((Real.log ‖1 + q y‖ : ℝ) : ℂ)).re
  | n + 1, y => 2 / (((n : ℝ) + 1) * κ) *
      (Mq (q y) ((Real.log ‖q y‖ : ℝ) : ℂ) ((Real.log ‖1 + q y‖ : ℝ) : ℂ) (n + 1)).re

section Curve

variable {κ l h : ℝ} {q Lq Lp : ℝ → ℂ}

theorem QS_zero (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) :
    QS κ q 0 h - QS κ q 0 l = -2 * ∫ τ in l..h, Real.log ‖1 + q τ‖ := by
  have ml : l ∈ Icc l h := ⟨le_rfl, hlh⟩
  have mh : h ∈ Icc l h := ⟨hlh, le_rfl⟩
  have e : ∀ τ ∈ Icc l h, (Lplus ((κ * τ : ℝ) : ℂ) (q τ) ((Real.log ‖q τ‖ : ℝ) : ℂ)
      ((Real.log ‖1 + q τ‖ : ℝ) : ℂ)).re = (Lplus ((κ * τ : ℝ) : ℂ) (q τ) (Lq τ) (Lp τ)).re :=
    fun τ hτ => Lplus_re (by rw [Complex.ofReal_re, C.reLq τ hτ])
      (by rw [Complex.ofReal_re, C.reLp τ hτ])
  have hκ := C.κ_ne
  simp only [QS]
  rw [e h mh, e l ml, C.int_log1p hlh]
  field_simp

theorem QS_succ (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (n : ℕ) :
    QS κ q (n + 1) h - QS κ q (n + 1) l =
      -2 * (∫ τ in l..h, (q τ ^ (n + 1)).re) / ((n : ℝ) + 1) := by
  have ml : l ∈ Icc l h := ⟨le_rfl, hlh⟩
  have mh : h ∈ Icc l h := ⟨hlh, le_rfl⟩
  have e : ∀ τ ∈ Icc l h, (Mq (q τ) ((Real.log ‖q τ‖ : ℝ) : ℂ) ((Real.log ‖1 + q τ‖ : ℝ) : ℂ)
      (n + 1)).re = (Mq (q τ) (Lq τ) (Lp τ) (n + 1)).re :=
    fun τ hτ => Mq_re (by rw [Complex.ofReal_re, C.reLq τ hτ])
      (by rw [Complex.ofReal_re, C.reLp τ hτ]) _
  have hκ := C.κ_ne
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [QS]
  rw [e h mh, e l ml, C.moment_re hlh]
  field_simp

theorem QS_tail (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (L : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range L, (QS κ q (n + 1) h - QS κ q (n + 1) l) * basis (n + 1) x =
      -(2 * ∑ n ∈ Finset.range L, (∫ τ in l..h, (q τ ^ (n + 1)).re) * basis (n + 1) x /
        ((n : ℝ) + 1)) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [QS_succ C hlh]
  ring

theorem QS_sum (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h) (L : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (L + 1), (QS κ q k h - QS κ q k l) * basis k x =
      -(2 * ∑ n ∈ Finset.range L, (∫ τ in l..h, (q τ ^ (n + 1)).re) * basis (n + 1) x /
        ((n : ℝ) + 1)) + -2 * ∫ τ in l..h, Real.log ‖1 + q τ‖ := by
  rw [Finset.sum_range_succ', QS_tail C hlh, QS_zero C hlh, basis_zero, mul_one]

end Curve

/-- The analytic tail of one segment. -/
def anaT (qm : Seg → ℝ) (L : ℕ) (g : Seg) : ℝ :=
  (g.hi - g.lo) * (2 * (qm g ^ (L + 1) * (1 - qm g)⁻¹ / ((L : ℝ) + 1)))

/-- **Analytic stream on a profile.** -/
theorem ana_stream {κ : ℝ} {P : List Seg} {q Lq Lp : ℝ → ℂ}
    (hC : ∀ g ∈ P, QCurve κ g.lo g.hi q Lq Lp) (hP : ∀ g ∈ P, g.lo ≤ g.hi) {qm : Seg → ℝ}
    (hqm : ∀ g ∈ P, qm g < 1) (hb : ∀ g ∈ P, ∀ τ ∈ Icc g.lo g.hi, ‖q τ‖ ≤ qm g) {t : ℝ}
    (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) (L : ℕ) :
    |pint P (fun y => KQ (q y) t) -
        ∑ k ∈ Finset.range (L + 1), evS P (QS κ q k) * basis k (2 * t - 1)| ≤
      absum P (anaT qm L) := by
  refine list_approx P _ _ _ _ _ fun g hg => ?_
  rw [QS_sum (hC g hg) (hP g hg)]
  have := analytic_seg (hC g hg) (hP g hg) (hqm g hg) (hb g hg) ht L
  unfold anaT
  refine le_of_eq_of_le ?_ this
  congr 1
  ring

/-- **Same-sign reflection stream on a profile.** -/
theorem refl_stream {P : List Seg} (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) {t : ℝ} (h0 : 0 < t)
    (h1 : t ≤ 1) (L : ℕ) :
    |pint P (fun y => Real.log |1 - YCell.physX y * t|) -
        ∑ k ∈ Finset.range (L + 1), evS P (QS 1 (qc rR) k) * basis k (2 * t - 1)| ≤
      absum P (fun g => betaT L (qr (rR g.hi)) (qr (rR g.lo))) := by
  refine list_approx P _ _ _ _ _ fun g hg => ?_
  obtain ⟨a, b⟩ := hP g hg
  have C : QCurve 1 g.lo g.hi (qc rR) (Lqc rR) (Lpc rR) := curveR a
  rw [QS_sum C b.le]
  have e : ∫ y in g.lo..g.hi, Real.log |1 - YCell.physX y * t| =
      ∫ y in g.lo..g.hi, KQ (qc rR y) t := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le b.le] at hy
    have := (physX_mem (a.trans hy.1)).2
    simp only [KQ_qc (r := rR) (y := y) this t, rR]
  rw [e]
  have := refl_seg a b h0 h1 L
  refine le_of_eq_of_le ?_ this
  congr 1
  ring

theorem rO_le {y : ℝ} (h : 2 ≤ y) : rO y ≤ 1 := by
  have := (physX_mem h).1
  simp only [rO]; linarith

theorem rD_lt {y : ℝ} (h : 2 ≤ y) : rD y < 0 := by
  have := (physX_mem h).1
  simp only [rD]
  have : 0 < 1 / YCell.physX y := by positivity
  linarith

theorem KO_eq {y : ℝ} (h : 2 ≤ y) (t : ℝ) :
    KQ (qc rO y) t = Real.log |1 + YCell.physX y * t| := by
  rw [KQ_qc (rO_le h)]
  simp only [rO]
  congr 2
  ring

theorem norm_qc (r : ℝ → ℝ) (y : ℝ) : ‖qc r y‖ = |qr (r y)| := by
  unfold qc
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `log X` in the q coordinate of the opposite direct branch. -/
theorem logX_eq {y : ℝ} (h : 2 ≤ y) :
    Real.log (YCell.physX y) =
      2 * Real.log ‖1 + qc rD y‖ - Real.log 4 - Real.log ‖qc rD y‖ := by
  have hr := rD_lt h
  have hX := (physX_mem h).1
  have h1 : rD y ≤ 1 := by linarith
  have hq := qr_ne h1 hr.ne
  have hp := one_add_qr_pos (rD y)
  have hi := inv_r_eq_q h1 hr.ne
  have e0 : 1 / rD y = -YCell.physX y := by
    simp only [rD]
    field_simp
  rw [e0] at hi
  have e1 : YCell.physX y = (1 + qr (rD y)) ^ 2 / (4 * |qr (rD y)|) := by
    have := congrArg abs hi
    rw [abs_neg, abs_of_pos hX, abs_div, abs_mul, abs_of_pos (pow_pos hp 2),
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
    exact this
  have hqa : |qr (rD y)| ≠ 0 := abs_ne_zero.mpr hq
  rw [norm_one_add_qc, norm_qc]
  conv_lhs => rw [e1]
  rw [Real.log_div (pow_ne_zero 2 hp.ne') (mul_ne_zero (by norm_num) hqa), Real.log_pow,
    Real.log_mul (by norm_num) hqa]
  push_cast
  ring

/-- The opposite direct kernel in the q coordinate. -/
theorem KD_eq {y t : ℝ} (h : 2 ≤ y) (h0 : 0 < t) :
    Real.log |t + YCell.physX y| =
      KQ (qc rD y) t + 2 * Real.log ‖1 + qc rD y‖ - Real.log 4 - Real.log ‖qc rD y‖ := by
  have hX := (physX_mem h).1
  have h1 : rD y ≤ 1 := by linarith [rD_lt h]
  rw [KQ_qc h1]
  have e : 1 - rD y * t = (t + YCell.physX y) / YCell.physX y := by
    simp only [rD]
    field_simp
    ring
  have hp : 0 < t + YCell.physX y := by linarith
  rw [e, abs_of_pos (div_pos hp hX), abs_of_pos hp, Real.log_div hp.ne' hX.ne', logX_eq h]
  ring

theorem KQ_int {κ l h : ℝ} {q Lq Lp : ℝ → ℂ} (C : QCurve κ l h q Lq Lp) (hlh : l ≤ h)
    (hb : ∀ τ ∈ Icc l h, ‖q τ‖ < 1) {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable (fun τ => KQ (q τ) t) volume l h := by
  refine ContinuousOn.intervalIntegrable_of_Icc hlh ?_
  unfold KQ
  refine ((continuousOn_const.sub ((rq_continuousOn C).mul continuousOn_const)).norm).log ?_
  intro τ hτ
  exact norm_ne_zero_iff.mpr (one_sub_rq_ne (hb τ hτ) ht)

/-- Endpoint primitives of the opposite direct stream. -/
def AD : ℕ → ℝ → ℝ
  | 0, y => -Real.log 4 * y +
      (Lqprim ((((-1 : ℝ)) * y : ℝ) : ℂ) (qc rD y) ((Real.log ‖qc rD y‖ : ℝ) : ℂ)).re
  | n + 1, y => QS (-1) (qc rD) (n + 1) y

/-- **Opposite direct stream on a profile.** -/
theorem odir_stream {P : List Seg} (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) {qm : Seg → ℝ}
    (hqm : ∀ g ∈ P, qm g < 1) (hb : ∀ g ∈ P, ∀ τ ∈ Icc g.lo g.hi, ‖qc rD τ‖ ≤ qm g) {t : ℝ}
    (h0 : 0 < t) (h1 : t ≤ 1) (L : ℕ) :
    |pint P (fun y => Real.log |t + YCell.physX y|) -
        ∑ k ∈ Finset.range (L + 1), evS P (AD k) * basis k (2 * t - 1)| ≤
      absum P (anaT qm L) := by
  refine list_approx P _ _ _ _ _ fun g hg => ?_
  obtain ⟨a, b⟩ := hP g hg
  have C : QCurve (-1) g.lo g.hi (qc rD) (Lqc rD) (Lpc rD) := curveD a
  have ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hK := KQ_int C b.le (fun τ hτ => (hb g hg τ hτ).trans_lt (hqm g hg)) ht
  have I1 : IntervalIntegrable (fun τ => Real.log ‖1 + qc rD τ‖) volume g.lo g.hi :=
    (cont_log1 C).intervalIntegrable_of_Icc b.le
  have I2 : IntervalIntegrable (fun τ => Real.log ‖qc rD τ‖) volume g.lo g.hi :=
    (C.cq.norm.log fun τ hτ => norm_ne_zero_iff.mpr (C.nz τ hτ)).intervalIntegrable_of_Icc b.le
  have e : ∫ y in g.lo..g.hi, Real.log |t + YCell.physX y| =
      (∫ y in g.lo..g.hi, KQ (qc rD y) t) + 2 * (∫ y in g.lo..g.hi, Real.log ‖1 + qc rD y‖) -
        (g.hi - g.lo) * Real.log 4 - ∫ y in g.lo..g.hi, Real.log ‖qc rD y‖ := by
    have e1 : ∫ y in g.lo..g.hi, Real.log |t + YCell.physX y| =
        ∫ y in g.lo..g.hi, KQ (qc rD y) t + 2 * Real.log ‖1 + qc rD y‖ - Real.log 4 -
          Real.log ‖qc rD y‖ := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le b.le] at hy
      exact KD_eq (a.trans hy.1) h0
    rw [e1, intervalIntegral.integral_sub ((hK.add (I1.const_mul 2)).sub intervalIntegrable_const) I2,
      intervalIntegral.integral_sub (hK.add (I1.const_mul 2)) intervalIntegrable_const,
      intervalIntegral.integral_add hK (I1.const_mul 2), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
  have ml : g.lo ∈ Icc g.lo g.hi := ⟨le_rfl, b.le⟩
  have mh : g.hi ∈ Icc g.lo g.hi := ⟨b.le, le_rfl⟩
  have es : ∀ τ ∈ Icc g.lo g.hi,
      (Lqprim ((((-1 : ℝ)) * τ : ℝ) : ℂ) (qc rD τ) ((Real.log ‖qc rD τ‖ : ℝ) : ℂ)).re =
      (Lqprim ((((-1 : ℝ)) * τ : ℝ) : ℂ) (qc rD τ) (Lqc rD τ)).re :=
    fun τ hτ => Lqprim_re (by rw [Complex.ofReal_re, C.reLq τ hτ])
  have e0 : AD 0 g.hi - AD 0 g.lo =
      -(g.hi - g.lo) * Real.log 4 - ∫ y in g.lo..g.hi, Real.log ‖qc rD y‖ := by
    rw [C.int_logq b.le]
    simp only [AD]
    rw [es _ mh, es _ ml]
    ring
  have etail : ∑ n ∈ Finset.range L, (AD (n + 1) g.hi - AD (n + 1) g.lo) * basis (n + 1) (2 * t - 1) =
      ∑ n ∈ Finset.range L,
        (QS (-1) (qc rD) (n + 1) g.hi - QS (-1) (qc rD) (n + 1) g.lo) * basis (n + 1) (2 * t - 1) :=
    rfl
  rw [Finset.sum_range_succ', etail, QS_tail C b.le, e0, basis_zero, mul_one, e]
  have := analytic_seg C b.le (hqm g hg) (hb g hg) ht L
  unfold anaT
  refine le_of_eq_of_le ?_ this
  congr 1
  ring

/-! ### The column stream -/

theorem rq_qC {c : ℝ} (h1 : c < 1) : rq (qC c) = rC c := (rC_eq_q h1).symm

theorem KQ_col {c : ℝ} (t : ℝ) (h0 : -1 < c) (h1 : c < 1) : colK t c = 2 * KQ (qC c) t := by
  have hre := rC_re h0 h1
  have him := rC_im (c := c)
  have hs := ab_sq h0 h1
  have e : ‖1 - rC c * (t : ℂ)‖ ^ 2 = 1 - 2 * c * t + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him, mul_zero, sub_zero, add_zero,
      zero_sub]
    linear_combination t ^ 2 * hs
  unfold colK KQ
  rw [rq_qC h1, ← e, abs_of_nonneg (by positivity), Real.log_pow]
  push_cast
  ring

/-- **Column stream on a profile.** -/
theorem col_stream {P : List Seg} (hP : ∀ g ∈ P, -1 < g.lo ∧ g.lo ≤ g.hi ∧ g.hi < 1)
    {qm : Seg → ℝ} (hqm : ∀ g ∈ P, qm g < 1) (hb : ∀ g ∈ P, ∀ τ ∈ Icc g.lo g.hi, ‖qC τ‖ ≤ qm g)
    {t : ℝ} (ht : 2 * t - 1 ∈ Icc (-1 : ℝ) 1) (L : ℕ) :
    |pint P (colK t) -
        ∑ k ∈ Finset.range (L + 1), 2 * evS P (QS 2 qC k) * basis k (2 * t - 1)| ≤
      2 * absum P (anaT qm L) := by
  have h := ana_stream (κ := 2) (P := P) (q := qC) (Lq := LqC) (Lp := LpC)
    (fun g hg => curveC (hP g hg).1 (hP g hg).2.2) (fun g hg => (hP g hg).2.1) hqm hb ht L
  have e : pint P (colK t) = 2 * pint P (fun y => KQ (qC y) t) := by
    unfold pint
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun g hg => ?_
    obtain ⟨a, b, c⟩ := hP g hg
    have : ∫ y in g.lo..g.hi, colK t y = ∫ y in g.lo..g.hi, 2 * KQ (qC y) t := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le b] at hy
      exact KQ_col t (lt_of_lt_of_le a hy.1) (lt_of_le_of_lt hy.2 c)
    rw [this, intervalIntegral.integral_const_mul]
    ring
  have e2 : ∑ k ∈ Finset.range (L + 1), 2 * evS P (QS 2 qC k) * basis k (2 * t - 1) =
      2 * ∑ k ∈ Finset.range (L + 1), evS P (QS 2 qC k) * basis k (2 * t - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, e2, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-! ### Joukowski bounds: `‖q‖ ≤ qm` from the elementary coordinate -/

theorem joukowski {q : ℂ} (h0 : q ≠ 0) (h1 : 1 + q ≠ 0) :
    ‖1 / rq q‖ + ‖1 / rq q - 1‖ = (1 + ‖q‖ ^ 2) / (2 * ‖q‖) := by
  have e1 : 1 / rq q = (1 + q) ^ 2 / (4 * q) := by
    unfold rq
    field_simp
  have e2 : 1 / rq q - 1 = (1 - q) ^ 2 / (4 * q) := by
    rw [e1]
    field_simp
    ring
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hp : ‖1 + q‖ ^ 2 + ‖1 - q‖ ^ 2 = 2 + 2 * ‖q‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [e2, e1, norm_div, norm_div, norm_pow, norm_pow, norm_mul]
  simp only [Complex.norm_ofNat]
  field_simp
  linarith

theorem qnorm_le {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {qm A : ℝ} (hm0 : 0 < qm) (hm : qm < 1)
    (hA : (1 + qm ^ 2) / (2 * qm) ≤ A) (hJ : A ≤ (1 + ‖q‖ ^ 2) / (2 * ‖q‖)) : ‖q‖ ≤ qm := by
  by_contra hc
  have hlt := not_le.mp hc
  have hx : 0 < ‖q‖ := hm0.trans hlt
  have := hA.trans hJ
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
  have h1 : 0 < 1 - ‖q‖ * qm := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr hlt) h1]

theorem qnorm_real {r : ℝ} (hr : r < 0) {qm A : ℝ} (hm0 : 0 < qm) (hm : qm < 1)
    (hA : (1 + qm ^ 2) / (2 * qm) ≤ A) (hJ : A ≤ 1 - 2 / r) : ‖((qr r : ℝ) : ℂ)‖ ≤ qm := by
  have h1 : r ≤ 1 := by linarith
  have hq0 : qr r ≠ 0 := qr_ne h1 hr.ne
  have hn : ‖((qr r : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_qr_lt (by linarith)
  have hc0 : ((qr r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0
  refine qnorm_le hn hc0 hm0 hm hA (hJ.trans (le_of_eq ?_))
  rw [← joukowski hc0 (one_add_ne_of_norm_lt hn)]
  have e : rq ((qr r : ℝ) : ℂ) = (r : ℂ) := rq_qc (r := fun _ => r) (y := 0) h1
  rw [e]
  have e1 : (1 : ℂ) / (r : ℂ) = ((1 / r : ℝ) : ℂ) := by push_cast; rfl
  have e2 : (1 : ℂ) / (r : ℂ) - 1 = ((1 / r - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e2, e1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hn1 : 1 / r < 0 := div_neg_of_pos_of_neg one_pos hr
  rw [abs_of_neg hn1, abs_of_neg (by linarith)]
  ring

theorem physX_anti {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) :
    YCell.physX b ≤ YCell.physX a := by
  unfold YCell.physX
  rw [_root_.if_pos (by linarith), _root_.if_pos (by linarith)]
  have hs : √(a ^ 2 - 4) ≤ √(b ^ 2 - 4) := Real.sqrt_le_sqrt (by nlinarith)
  have h0 := Real.sqrt_nonneg (a ^ 2 - 4)
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- Opposite reflection: the bound from `X(lo)`. -/
theorem qm_O {lo hi qm : ℝ} (h2 : 2 ≤ lo) (hm0 : 0 < qm) (hm : qm < 1)
    (hA : (1 + qm ^ 2) / (2 * qm) ≤ 1 + 2 / YCell.physX lo) :
    ∀ τ ∈ Icc lo hi, ‖qc rO τ‖ ≤ qm := by
  intro τ hτ
  have hX := (physX_mem (h2.trans hτ.1)).1
  have hr : rO τ < 0 := by simp only [rO]; linarith
  refine qnorm_real hr hm0 hm hA ?_
  have ha := physX_anti h2 hτ.1
  have : 2 / YCell.physX lo ≤ 2 / YCell.physX τ :=
    div_le_div_of_nonneg_left (by norm_num) hX ha
  simp only [rO]
  rw [div_neg]
  linarith

/-- Opposite direct: the bound from `X(hi)`. -/
theorem qm_D {lo hi qm : ℝ} (h2 : 2 ≤ lo) (hm0 : 0 < qm) (hm : qm < 1)
    (hA : (1 + qm ^ 2) / (2 * qm) ≤ 1 + 2 * YCell.physX hi) :
    ∀ τ ∈ Icc lo hi, ‖qc rD τ‖ ≤ qm := by
  intro τ hτ
  have hy := h2.trans hτ.1
  have hX := (physX_mem hy).1
  refine qnorm_real (rD_lt hy) hm0 hm hA ?_
  have ha := physX_anti hy hτ.2
  have e : 2 / rD τ = -(2 * YCell.physX τ) := by
    simp only [rD]
    field_simp
  rw [e]
  linarith

/-- Column: the bound from `c = hi`. -/
theorem qm_C {lo hi qm : ℝ} (h0 : -1 < lo) (h1 : hi < 1) (hm0 : 0 < qm) (hm : qm < 1)
    (hA : (1 + qm ^ 2) / (2 * qm) ≤ 1 + dC hi) :
    ∀ τ ∈ Icc lo hi, ‖qC τ‖ ≤ qm := by
  intro τ hτ
  have a0 := lt_of_lt_of_le h0 hτ.1
  have a1 := lt_of_le_of_lt hτ.2 h1
  have hn := qC_norm_lt a0 a1
  have hq0 := qC_ne a0 a1
  refine qnorm_le hn hq0 hm0 hm hA ?_
  rw [← joukowski hq0 (one_add_qC_ne a1), rq_qC a1]
  have hN := rC_normSq a0 a1
  have hr1 : ‖rC τ‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hN
    nlinarith [norm_nonneg (rC τ), sq_nonneg (‖rC τ‖ - 1), sq_nonneg (‖rC τ‖ + 1)]
  have hr0 : rC τ ≠ 0 := norm_ne_zero_iff.mp (by rw [hr1]; norm_num)
  have e1 : ‖1 / rC τ‖ = 1 := by rw [norm_div, hr1]; simp
  have e2 : ‖1 / rC τ - 1‖ = dC τ := by
    have : 1 / rC τ - 1 = sC τ ^ 2 / rC τ := by
      field_simp
      unfold rC
      ring
    rw [this, norm_div, hr1, div_one, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    have ha := aC_sq a1
    have hb := bC_sq a0 a1
    simp only [sC, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      zero_sub, zero_add, sub_self, add_zero, mul_neg, neg_neg, neg_zero]
    nlinarith
  rw [e1, e2]
  have : dC hi ≤ dC τ := Real.sqrt_le_sqrt (by linarith [hτ.2])
  linarith

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### From the cells to the signed profile -/

/-- Pairing of cells with differences of `F`. -/
def evC (l : List YCell) (F : ℝ → ℝ) : ℝ :=
  (l.map fun c => c.w / (c.hi - c.lo) * (F c.hi - F c.lo)).sum

/-- A primitive of the row kernel on each side of the gap `(-2,2)`. -/
def rowP (x y : ℝ) : ℝ :=
  if 0 ≤ y then ∫ Y in (2 : ℝ)..y, rowK x Y else ∫ Y in (-2 : ℝ)..y, rowK x Y

/-- A primitive of the column kernel. -/
def colP (x c : ℝ) : ℝ := ∫ u in (0 : ℝ)..c, colK x u

theorem rowK_int_pos {x a b : ℝ} (hx : x ≠ 0) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (rowK x) volume a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact rowK_integrable (c := ⟨a, b, 0, h, le_rfl⟩) (Or.inl ha) hx
  · exact IntervalIntegrable.refl
  · exact (rowK_integrable (c := ⟨b, a, 0, h, le_rfl⟩) (Or.inl hb) hx).symm

theorem rowK_int_neg {x a b : ℝ} (hx : x ≠ 0) (ha : a ≤ -2) (hb : b ≤ -2) :
    IntervalIntegrable (rowK x) volume a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact rowK_integrable (c := ⟨a, b, 0, h, le_rfl⟩) (Or.inr hb) hx
  · exact IntervalIntegrable.refl
  · exact (rowK_integrable (c := ⟨b, a, 0, h, le_rfl⟩) (Or.inr ha) hx).symm

theorem rowP_pos {x lo hi : ℝ} (hx : x ≠ 0) (h2 : 2 ≤ lo) (hlh : lo ≤ hi) :
    rowP x hi - rowP x lo = ∫ Y in lo..hi, rowK x Y := by
  unfold rowP
  rw [_root_.if_pos (by linarith), _root_.if_pos (by linarith)]
  exact intervalIntegral.integral_interval_sub_left
    (rowK_int_pos hx le_rfl (h2.trans hlh)) (rowK_int_pos hx le_rfl h2)

theorem rowP_neg {x lo hi : ℝ} (hx : x ≠ 0) (h2 : hi ≤ -2) (hlh : lo ≤ hi) :
    rowP x hi - rowP x lo = ∫ Y in lo..hi, rowK x Y := by
  unfold rowP
  rw [_root_.if_neg (by linarith), _root_.if_neg (by linarith)]
  exact intervalIntegral.integral_interval_sub_left
    (rowK_int_neg hx le_rfl h2) (rowK_int_neg hx le_rfl (hlh.trans h2))

theorem avgL_row {l : List YCell} (h : ∀ c ∈ l, 2 ≤ c.lo ∨ c.hi ≤ -2) {x : ℝ} (hx : x ≠ 0) :
    avgL l (rowK x) = evC l (rowP x) := by
  unfold avgL evC
  congr 1
  refine List.map_congr_left fun c hc => ?_
  unfold YCell.avg
  rcases h c hc with h' | h'
  · rw [rowP_pos hx h' c.lo_lt.le]
  · rw [rowP_neg hx h' c.lo_lt.le]

theorem colK_int {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    IntervalIntegrable (colK x) volume a b := by
  have h0 : IntervalIntegrable (fun s => Real.log |(x + 1 / x) - s|) volume (2 * a) (2 * b) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (x + 1 / x) - 2 * a)
      (b := (x + 1 / x) - 2 * b)).comp_sub_left (x + 1 / x)
    simpa [Real.log_abs] using h
  have h2 := h0.comp_mul_left (c := 2)
  have e1 : 2 * a / 2 = a := by ring
  have e2 : 2 * b / 2 = b := by ring
  rw [e1, e2] at h2
  have h1 := h2.add (intervalIntegrable_const (c := Real.log |x|) (μ := volume) (a := a) (b := b))
  refine h1.congr_ae ?_
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({(1 + x ^ 2) / (2 * x)} : Set ℝ) :=
    (Set.countable_singleton _).ae_notMem volume
  filter_upwards [ae_restrict_of_ae (s := Ι a b) hae] with u hu
  have hu' : 1 - 2 * u * x + x ^ 2 ≠ 0 := by
    intro h0
    apply hu
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith
  have e : x + 1 / x - 2 * u = (1 - 2 * u * x + x ^ 2) / x := by
    field_simp
    ring
  rw [e, abs_div, Real.log_div (abs_ne_zero.mpr hu') (abs_ne_zero.mpr hx)]
  unfold colK
  ring

theorem colP_sub {x : ℝ} (hx : x ≠ 0) (lo hi : ℝ) :
    colP x hi - colP x lo = ∫ u in lo..hi, colK x u :=
  intervalIntegral.integral_interval_sub_left (colK_int hx _ _) (colK_int hx _ _)

theorem avgL_col (l : List YCell) {x : ℝ} (hx : x ≠ 0) :
    avgL l (colK x) = evC l (colP x) := by
  unfold avgL evC
  congr 1
  refine List.map_congr_left fun c _ => ?_
  unfold YCell.avg
  rw [colP_sub hx]

theorem physX_neg {y : ℝ} (hy : 0 < y) : YCell.physX (-y) = -YCell.physX y := by
  unfold YCell.physX
  rw [_root_.if_pos hy.le, _root_.if_neg (by linarith)]
  simp

theorem rowK_neg_neg (a : ℝ) {b : ℝ} (hb : 0 < b) : rowK (-a) (-b) = rowK a b := by
  unfold rowK
  rw [physX_neg hb]
  have e1 : -a - -YCell.physX b = -(a - YCell.physX b) := by ring
  have e2 : 1 - -a * -YCell.physX b = 1 - a * YCell.physX b := by ring
  rw [e1, e2, abs_neg]

theorem colK_neg_neg (a b : ℝ) : colK (-a) (-b) = colK a b := by
  unfold colK
  congr 2
  ring

theorem eps_row {ε x lo hi : ℝ} (hε : ε = 1 ∨ ε = -1) (hx : x ≠ 0) (h2 : 2 ≤ lo) (hlh : lo ≤ hi) :
    ε * rowP x (ε * hi) - ε * rowP x (ε * lo) = ∫ y in lo..hi, rowK x (ε * y) := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
    exact rowP_pos hx h2 hlh
  · have := rowP_neg (x := x) (lo := -hi) (hi := -lo) hx (by linarith) (by linarith)
    have e := intervalIntegral.integral_comp_neg (a := lo) (b := hi) (rowK x)
    simp only [neg_mul, one_mul]
    rw [e, ← this]
    ring

theorem eps_col {ε x lo hi : ℝ} (hε : ε = 1 ∨ ε = -1) (hx : x ≠ 0) :
    ε * colP x (ε * hi) - ε * colP x (ε * lo) = ∫ y in lo..hi, colK x (ε * y) := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
    exact colP_sub hx _ _
  · have := colP_sub hx (-hi) (-lo)
    have e := intervalIntegral.integral_comp_neg (a := lo) (b := hi) (colK x)
    simp only [neg_mul, one_mul]
    rw [e, ← this]
    ring

/-- Profile data of one sign: same-sign, opposite-sign and column segments with their atoms, and
the per-segment `q` radii of the three analytic streams. -/
structure Profile where
  Ps : List Seg
  Po : List Seg
  Pc : List Seg
  Es : List (ℝ × ℝ)
  Eo : List (ℝ × ℝ)
  Ec : List (ℝ × ℝ)
  qD : Seg → ℝ
  qO : Seg → ℝ
  qC : Seg → ℝ

/-- The linear binding of `W` to the source at sign `sg`, supports and radii. -/
structure Profile.OK (W : Profile) (S : CapSource) (sg : ℝ) : Prop where
  atoms_s : Atoms W.Ps W.Es
  atoms_o : Atoms W.Po W.Eo
  atoms_c : Atoms W.Pc W.Ec
  bind_row : ∀ F : ℝ → ℝ, evC (S.refRow 1) F - evC (S.refRow 0) F =
    evS W.Ps (fun y => sg * F (sg * y)) + evS W.Po (fun y => -sg * F (-sg * y))
  bind_col : ∀ F : ℝ → ℝ, evC (S.refCol 1) F - evC (S.refCol 0) F =
    evS W.Pc (fun y => sg * F (sg * y))
  supp_s : ∀ g ∈ W.Ps, 2 ≤ g.lo ∧ g.lo < g.hi
  supp_o : ∀ g ∈ W.Po, 2 ≤ g.lo ∧ g.lo < g.hi
  supp_c : ∀ g ∈ W.Pc, -1 < g.lo ∧ g.lo ≤ g.hi ∧ g.hi < 1
  atoms_y : ∀ e ∈ W.Es, 2 ≤ e.1
  rad_D : ∀ g ∈ W.Po, 0 < W.qD g ∧ W.qD g < 1 ∧
    (1 + W.qD g ^ 2) / (2 * W.qD g) ≤ 1 + 2 * YCell.physX g.hi
  rad_O : ∀ g ∈ W.Po, 0 < W.qO g ∧ W.qO g < 1 ∧
    (1 + W.qO g ^ 2) / (2 * W.qO g) ≤ 1 + 2 / YCell.physX g.lo
  rad_C : ∀ g ∈ W.Pc, 0 < W.qC g ∧ W.qC g < 1 ∧
    (1 + W.qC g ^ 2) / (2 * W.qC g) ≤ 1 + dC g.hi

theorem evS_congr {P : List Seg} {F : ℝ → ℝ} {f : ℝ → ℝ}
    (h : ∀ g ∈ P, F g.hi - F g.lo = ∫ y in g.lo..g.hi, f y) : evS P F = pint P f := by
  unfold evS pint
  congr 1
  refine List.map_congr_left fun g hg => ?_
  rw [h g hg]

/-- **Reduction.** The physical difference is a pairing of the profile with the three kernels. -/
theorem Dphys_eq {S : CapSource} (hS : S.Admissible) {W : Profile} {sg t : ℝ}
    (hsg : sg = 1 ∨ sg = -1) (hW : W.OK S sg) (h0 : 0 < t) :
    Dphys S (sg * t) =
      pint W.Ps (rowK t) + pint W.Po (rowK (-t)) - pint W.Pc (colK t) := by
  have hx : sg * t ≠ 0 := by
    rcases hsg with rfl | rfl <;> simp [h0.ne']
  have hneg : -sg = 1 ∨ -sg = -1 := by
    rcases hsg with rfl | rfl <;> simp
  have hs : ∀ y, 0 < y → rowK (sg * t) (sg * y) = rowK t y := by
    intro y hy
    rcases hsg with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact rowK_neg_neg t hy
  have ho : ∀ y, 0 < y → rowK (sg * t) (-sg * y) = rowK (-t) y := by
    intro y hy
    rcases hsg with rfl | rfl
    · simp only [one_mul, neg_mul]
      have := rowK_neg_neg (-t) hy
      rwa [neg_neg] at this
    · simp
  have hc : ∀ y, colK (sg * t) (sg * y) = colK t y := by
    intro y
    rcases hsg with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact colK_neg_neg t y
  have e1 : evS W.Ps (fun y => sg * rowP (sg * t) (sg * y)) = pint W.Ps (rowK t) := by
    refine evS_congr fun g hg => ?_
    obtain ⟨a, b⟩ := hW.supp_s g hg
    rw [eps_row hsg hx a b.le]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le b.le] at hy
    exact hs y (by linarith [hy.1])
  have e2 : evS W.Po (fun y => -sg * rowP (sg * t) (-sg * y)) = pint W.Po (rowK (-t)) := by
    refine evS_congr fun g hg => ?_
    obtain ⟨a, b⟩ := hW.supp_o g hg
    rw [eps_row hneg hx a b.le]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le b.le] at hy
    exact ho y (by linarith [hy.1])
  have e3 : evS W.Pc (fun y => sg * colP (sg * t) (sg * y)) = pint W.Pc (colK t) := by
    refine evS_congr fun g _ => ?_
    rw [eps_col hsg hx]
    exact intervalIntegral.integral_congr fun y _ => hc y
  unfold Dphys
  rw [avgL_row (fun c hc => hS.ref_away 1 c hc) hx, avgL_row (fun c hc => hS.ref_away 0 c hc) hx,
    avgL_col _ hx, avgL_col _ hx, hW.bind_row, hW.bind_col, e1, e2, e3]

theorem pint_split {P : List Seg} {f a b : ℝ → ℝ}
    (hP : ∀ g ∈ P, g.lo ≤ g.hi)
    (ha : ∀ g ∈ P, IntervalIntegrable a volume g.lo g.hi)
    (hb : ∀ g ∈ P, IntervalIntegrable b volume g.lo g.hi)
    (h : ∀ g ∈ P, ∀ y ∈ Icc g.lo g.hi, f y = a y + b y) :
    pint P f = pint P a + pint P b := by
  induction P with
  | nil => simp [pint]
  | cons g P ih =>
    have ih' := ih (fun d hd => hP d (List.mem_cons_of_mem _ hd))
      (fun d hd => ha d (List.mem_cons_of_mem _ hd))
      (fun d hd => hb d (List.mem_cons_of_mem _ hd))
      (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [pint, List.map_cons, List.sum_cons] at ih' ⊢
    have e : ∫ y in g.lo..g.hi, f y = (∫ y in g.lo..g.hi, a y) + ∫ y in g.lo..g.hi, b y := by
      rw [← intervalIntegral.integral_add (ha g List.mem_cons_self) (hb g List.mem_cons_self)]
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le (hP g List.mem_cons_self)] at hy
      exact h g List.mem_cons_self y hy
    rw [e, ih']
    ring

theorem rowlog3_int {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) :
    IntervalIntegrable (fun y => Real.log |1 + YCell.physX y * t|) volume lo hi := by
  refine ContinuousOn.intervalIntegrable_of_Icc hlt.le ?_
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  refine ContinuousOn.log (continuous_abs.comp_continuousOn
    (continuousOn_const.add (hc.mul continuousOn_const))) ?_
  intro y hy
  have := (physX_mem (h2.trans hy.1)).1
  have h3 : 0 < YCell.physX y * t := by positivity
  exact abs_ne_zero.mpr (by linarith)

theorem rowlog4_int {lo hi t : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) :
    IntervalIntegrable (fun y => Real.log |t + YCell.physX y|) volume lo hi := by
  refine ContinuousOn.intervalIntegrable_of_Icc hlt.le ?_
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  refine ContinuousOn.log (continuous_abs.comp_continuousOn (continuousOn_const.add hc)) ?_
  intro y hy
  have := (physX_mem (h2.trans hy.1)).1
  exact abs_ne_zero.mpr (by linarith)

/-- Sum of the five stream values at `b`. -/
def streamSum (W : Profile) (N Lr La : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), evS W.Ps (Adir k) * basis k x +
    ∑ k ∈ Finset.range (Lr + 1), evS W.Ps (QS 1 (qc rR) k) * basis k x +
    ∑ k ∈ Finset.range (La + 1),
      (evS W.Po (AD k) + evS W.Po (QS (-1) (qc rO) k) - 2 * evS W.Pc (QS 2 qC k)) * basis k x

/-- Sum of the deterministic tails. -/
def streamTail (W : Profile) (Lr La : ℕ) : ℝ :=
  absum W.Ps (fun g => betaT Lr (qr (rR g.hi)) (qr (rR g.lo))) +
    absum W.Po (anaT W.qD La) + absum W.Po (anaT W.qO La) + 2 * absum W.Pc (anaT W.qC La)

/-! ### The ideal stream in endpoint form, and the final bound -/

/-- A stream list from a coefficient function. -/
def strm (L : ℕ) (a : ℕ → ℝ) : List ℝ := (List.range L).map a

/-- The sign `σ` as a real. -/
def sgOf : Sign → ℝ
  | Sign.neg => -1
  | Sign.pos => 1

theorem sgOf_cases (σ : Sign) : sgOf σ = 1 ∨ sgOf σ = -1 := by
  cases σ <;> simp [sgOf]

theorem x_eq_sg_abs {x : ℝ} {σ : Sign} (hx : x ∈ CapSource.rowDom) (hs : signOf x = σ) :
    x = sgOf σ * |x| ∧ 0 < |x| ∧ |x| ≤ 1 := by
  subst hs
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · have : signOf x = Sign.neg := by simp [signOf, b]
    rw [this, abs_of_neg b]
    simp only [sgOf]
    exact ⟨by ring, by linarith, by linarith⟩
  · have : signOf x = Sign.pos := by simp [signOf, not_lt.mpr a.le]
    rw [this, abs_of_pos a]
    simp only [sgOf]
    exact ⟨by ring, a, b.le⟩

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### The spatial bins -/

/-- Distance of two bin indices. -/
def bdist (i j : ℕ) : ℕ := (i - j) + (j - i)

/-- The bin of `s ∈ [0,1]`. -/
def bidx (B : ℕ) (s : ℝ) : ℕ := min ⌊s * B⌋₊ (B - 1)

theorem bidx_lt {B : ℕ} (hB : 1 ≤ B) (s : ℝ) : bidx B s < B := by
  unfold bidx
  have := min_le_right ⌊s * (B : ℝ)⌋₊ (B - 1)
  omega

theorem bidx_spec {B : ℕ} (hB : 1 ≤ B) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (bidx B s : ℝ) ≤ s * B ∧ s * B ≤ bidx B s + 1 := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hsB : 0 ≤ s * B := by positivity
  have hf := Nat.floor_le hsB
  have hu := Nat.lt_floor_add_one (s * (B : ℝ))
  unfold bidx
  rcases le_total ⌊s * (B : ℝ)⌋₊ (B - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨hf, hu.le⟩
  · rw [min_eq_right h]
    have e : ((B - 1 : ℕ) : ℝ) + 1 = B := by
      have : B - 1 + 1 = B := by omega
      exact_mod_cast this
    have h' : ((B - 1 : ℕ) : ℝ) ≤ ⌊s * (B : ℝ)⌋₊ := by exact_mod_cast h
    refine ⟨h'.trans hf, ?_⟩
    rw [e]
    nlinarith

theorem bdist_lt {B i j : ℕ} (hi : i < B) (hj : j < B) : bdist i j < B := by
  unfold bdist
  omega

theorem bin_sep {B : ℕ} (hB : 1 ≤ B) {a b : ℝ} (a0 : 0 ≤ a) (a1 : a ≤ 1) (b0 : 0 ≤ b) (b1 : b ≤ 1) :
    ((bdist (bidx B a) (bidx B b) - 1 : ℕ) : ℝ) / B ≤ |a - b| := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨p1, p2⟩ := bidx_spec hB a0 a1
  obtain ⟨q1, q2⟩ := bidx_spec hB b0 b1
  rw [div_le_iff₀ hBp]
  set i := bidx B a
  set j := bidx B b
  unfold bdist
  rcases le_total i j with h | h
  · have e : j - i = (j - i - 1) + 1 ∨ j - i = 0 := by omega
    have e0 : i - j = 0 := by omega
    rw [e0, zero_add]
    rcases e with e | e
    · have c : ((j - i - 1 : ℕ) : ℝ) = (j : ℝ) - i - 1 := by
        have : j = i + (j - i - 1) + 1 := by omega
        have c : (j : ℝ) = i + ((j - i - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast this
        linarith
      rw [c]
      have : (b - a) * B ≤ |a - b| * B :=
        mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) hBp.le
      nlinarith
    · rw [e]
      simp only [Nat.zero_sub, Nat.cast_zero, zero_mul]
      positivity
  · have e : i - j = (i - j - 1) + 1 ∨ i - j = 0 := by omega
    have e0 : j - i = 0 := by omega
    rw [e0, add_zero]
    rcases e with e | e
    · have c : ((i - j - 1 : ℕ) : ℝ) = (i : ℝ) - j - 1 := by
        have : i = j + (i - j - 1) + 1 := by omega
        have c : (i : ℝ) = j + ((i - j - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast this
        linarith
      rw [c]
      have : (a - b) * B ≤ |a - b| * B :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hBp.le
      nlinarith
    · rw [e]
      simp only [Nat.zero_sub, Nat.cast_zero, zero_mul]
      positivity

/-- The kernel of the bin distance. -/
def kk (N B d : ℕ) : ℝ := kap N (((d - 1 : ℕ) : ℝ) / B)

theorem kap_le_kk {N B : ℕ} (hB : 1 ≤ B) {a b : ℝ} (a0 : 0 ≤ a) (a1 : a ≤ 1) (b0 : 0 ≤ b)
    (b1 : b ≤ 1) : kap N |a - b| ≤ kk N B (bdist (bidx B a) (bidx B b)) :=
  kap_anti N (bin_sep hB a0 a1 b0 b1)

/-- Mass of one segment in bin `j`. -/
def segBin (B j : ℕ) (g : Seg) : ℝ :=
  ∫ θ in Th g.lo..Th g.hi, if bidx B (sth θ) = j then dbet θ else 0

/-- Bin mass of the variation measure of the direct tail. -/
def binMass (B : ℕ) (P : List Seg) (E : List (ℝ × ℝ)) (j : ℕ) : ℝ :=
  (E.map fun e => if bidx B (YCell.physX e.1) = j then |e.2| * bet (Th e.1) else 0).sum +
    (P.map fun g => |g.rho| * segBin B j g).sum

theorem list_fin {α : Type*} (l : List α) (c : ℕ → ℝ) (f : ℕ → α → ℝ) (B : ℕ) :
    ∑ j ∈ Finset.range B, c j * (l.map (f j)).sum =
      (l.map fun a => ∑ j ∈ Finset.range B, c j * f j a).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

theorem list_sum_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem bidx_sth_measurable (B : ℕ) : Measurable fun θ => bidx B (sth θ) := by
  have h1 : Measurable fun θ => sth θ * (B : ℝ) :=
    (sth_continuous.mul continuous_const).measurable
  have h2 : Measurable fun n : ℕ => min n (B - 1) := measurable_from_top
  exact h2.comp (Nat.measurable_floor.comp h1)

theorem seg_ite_int {B : ℕ} (j : ℕ) {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) :
    IntervalIntegrable (fun θ => if bidx B (sth θ) = j then dbet θ else 0) volume
      (Th lo) (Th hi) := by
  have hab := Th_lt h2 hlt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hsub : Icc (Th lo) (Th hi) ⊆ Ico 0 π := fun θ hθ =>
    ⟨ml.1.trans hθ.1, lt_of_le_of_lt hθ.2 mh.2⟩
  have hd : IntervalIntegrable dbet volume (Th lo) (Th hi) :=
    (continuousOn_dbet.mono hsub).intervalIntegrable_of_Icc hab.le
  have hS : MeasurableSet {θ | bidx B (sth θ) = j} :=
    bidx_sth_measurable B (measurableSet_singleton j)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le] at hd ⊢
  have := hd.integrable.indicator hS
  refine IntegrableOn.congr_fun (f := Set.indicator {θ | bidx B (sth θ) = j} dbet) this ?_
    measurableSet_Ioc
  intro θ _
  by_cases h : bidx B (sth θ) = j <;> simp [Set.indicator, h]

/-- The seg term against the bin kernel. -/
theorem seg_bins {N B : ℕ} (hB : 1 ≤ B) {t : ℝ} (t0 : 0 ≤ t) (t1 : t ≤ 1) {lo hi : ℝ}
    (h2 : 2 ≤ lo) (hlt : lo < hi) (K : ℕ → ℝ) (hK : ∀ d < B, kk N B d ≤ K d) :
    ∫ θ in Th lo..Th hi, kap N |t - sth θ| * dbet θ ≤
      ∑ j ∈ Finset.range B, K (bdist (bidx B t) j) * segBin B j ⟨lo, hi, 0⟩ := by
  have hab := Th_lt h2 hlt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hsub : Icc (Th lo) (Th hi) ⊆ Ico 0 π := fun θ hθ =>
    ⟨ml.1.trans hθ.1, lt_of_le_of_lt hθ.2 mh.2⟩
  have I : ∀ j ∈ Finset.range B, IntervalIntegrable (fun θ => K (bdist (bidx B t) j) *
      (if bidx B (sth θ) = j then dbet θ else 0)) volume (Th lo) (Th hi) :=
    fun j _ => (seg_ite_int j h2 hlt).const_mul _
  simp only [segBin]
  have e : ∑ j ∈ Finset.range B, K (bdist (bidx B t) j) *
      ∫ θ in Th lo..Th hi, (if bidx B (sth θ) = j then dbet θ else 0) =
      ∫ θ in Th lo..Th hi, ∑ j ∈ Finset.range B, K (bdist (bidx B t) j) *
        (if bidx B (sth θ) = j then dbet θ else 0) := by
    rw [intervalIntegral.integral_finsetSum I]
    exact Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_const_mul _ _).symm
  rw [e]
  have ck : Continuous fun θ => kap N |t - sth θ| :=
    (kap_continuous N).comp (continuous_abs.comp (continuous_const.sub sth_continuous))
  refine intervalIntegral.integral_mono_on hab.le
    ((ck.continuousOn.mul (continuousOn_dbet.mono hsub)).intervalIntegrable_of_Icc hab.le)
    (by
      have := IntervalIntegrable.sum (Finset.range B) I
      refine this.congr ?_
      intro θ _
      simp [Finset.sum_apply]) ?_
  intro θ hθ
  have hm := hsub hθ
  have hb := bidx_lt hB (sth θ)
  have e2 : ∑ j ∈ Finset.range B, K (bdist (bidx B t) j) *
      (if bidx B (sth θ) = j then dbet θ else 0) =
      K (bdist (bidx B t) (bidx B (sth θ))) * dbet θ := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [hb]
  rw [e2]
  refine mul_le_mul_of_nonneg_right ?_ (dbet_nonneg hm.1 hm.2)
  exact (kap_le_kk hB t0 t1 (sth_pos hm.1 hm.2).le (sth_le_one θ)).trans
    (hK _ (bdist_lt (bidx_lt hB t) hb))

theorem segBin_irrel (B j : ℕ) (g : Seg) : segBin B j g = segBin B j ⟨g.lo, g.hi, 0⟩ := rfl

/-- The direct tail functional against the bins. -/
theorem dirV_le_binSum {N B : ℕ} (hB : 1 ≤ B) {P : List Seg} {E : List (ℝ × ℝ)}
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E, 2 ≤ e.1) {t : ℝ} (t0 : 0 ≤ t)
    (t1 : t ≤ 1) (K : ℕ → ℝ) (hK : ∀ d < B, kk N B d ≤ K d) :
    dirV N P E t ≤ ∑ j ∈ Finset.range B, K (bdist (bidx B t) j) * binMass B P E j := by
  unfold binMass dirV
  simp only [mul_add, Finset.sum_add_distrib]
  rw [list_fin E (fun j => K (bdist (bidx B t) j))
      (fun j e => if bidx B (YCell.physX e.1) = j then |e.2| * bet (Th e.1) else 0),
    list_fin P (fun j => K (bdist (bidx B t) j)) (fun j g => |g.rho| * segBin B j g)]
  refine add_le_add (list_sum_le _ _ _ fun e he => ?_) (list_sum_le _ _ _ fun g hg => ?_)
  · have hy := hE e he
    obtain ⟨x0, x1⟩ := physX_mem hy
    have hb := bidx_lt hB (YCell.physX e.1)
    have m := Th_mem hy
    have e2 : ∑ j ∈ Finset.range B, K (bdist (bidx B t) j) *
        (if bidx B (YCell.physX e.1) = j then |e.2| * bet (Th e.1) else 0) =
        K (bdist (bidx B t) (bidx B (YCell.physX e.1))) * (|e.2| * bet (Th e.1)) := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp [hb]
    rw [e2]
    have hk := (kap_le_kk (N := N) hB t0 t1 x0.le x1).trans (hK _ (bdist_lt (bidx_lt hB t) hb))
    have := mul_le_mul_of_nonneg_right hk
      (mul_nonneg (abs_nonneg e.2) (bet_nonneg m.1 m.2))
    calc |e.2| * (kap N |t - YCell.physX e.1| * bet (Th e.1))
        = kap N |t - YCell.physX e.1| * (|e.2| * bet (Th e.1)) := by ring
      _ ≤ _ := this
  · obtain ⟨a, b⟩ := hP g hg
    have := mul_le_mul_of_nonneg_left (seg_bins (N := N) hB t0 t1 a b K hK) (abs_nonneg g.rho)
    refine this.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [segBin]
    ring

/-! ### Closed form of the bin masses -/

/-- `b(s) = (1+s) ((1-s)/s)^{3/2}`. -/
def bb (s : ℝ) : ℝ := (1 + s) * ((1 - s) / s * √((1 - s) / s))

theorem bet_eq_bb {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : bet θ = bb (sth θ) := by
  have hc := cos_half_pos h0 h1
  have hs := sin_half_nonneg h0 h1
  have hq := Real.sin_sq_add_cos_sq (θ / 2)
  have e1 : (1 - sth θ) / sth θ = (Real.sin (θ / 2) / Real.cos (θ / 2)) ^ 2 := by
    unfold sth
    rw [div_pow]
    congr 1
    linarith
  have e2 : √((1 - sth θ) / sth θ) = Real.sin (θ / 2) / Real.cos (θ / 2) := by
    rw [e1, Real.sqrt_sq (by positivity)]
  unfold bb
  rw [e2, e1]
  unfold bet sth
  have hS : Real.sin (θ / 2) ^ 2 = 1 - Real.cos (θ / 2) ^ 2 := by linarith
  field_simp
  rw [show Real.sin (θ / 2) ^ 3 = Real.sin (θ / 2) * Real.sin (θ / 2) ^ 2 by ring, hS]
  ring

theorem sth_arccos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : sth (Real.arccos (2 * s - 1)) = s := by
  have := two_sth_sub (Real.arccos (2 * s - 1))
  rw [Real.cos_arccos (by linarith) (by linarith)] at this
  linarith

theorem sth_strictAnti : StrictAntiOn sth (Icc 0 π) := by
  intro a ha b hb hab
  have := Real.strictAntiOn_cos ha hb hab
  have e1 := two_sth_sub a
  have e2 := two_sth_sub b
  linarith

/-- Mass of one segment in bin `j`, in closed form. -/
theorem segBin_le {B j : ℕ} (hB : 1 ≤ B) (hj : j < B) {g : Seg} (h2 : 2 ≤ g.lo)
    (hlt : g.lo < g.hi) :
    segBin B j g ≤ max 0 (bb (max (YCell.physX g.hi) (j / B)) -
      bb (min (YCell.physX g.lo) (((j : ℝ) + 1) / B))) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  set lo := g.lo
  set hi := g.hi
  have hab := Th_lt h2 hlt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hsub : Icc (Th lo) (Th hi) ⊆ Ico 0 π := fun θ hθ =>
    ⟨ml.1.trans hθ.1, lt_of_le_of_lt hθ.2 mh.2⟩
  have hxl : sth (Th lo) = YCell.physX lo := sth_Th h2
  have hxh : sth (Th hi) = YCell.physX hi := sth_Th (h2.trans hlt.le)
  obtain ⟨xl0, xl1⟩ := physX_mem h2
  obtain ⟨xh0, xh1⟩ := physX_mem (h2.trans hlt.le)
  set sL := max (YCell.physX hi) ((j : ℝ) / B) with hsL
  set sU := min (YCell.physX lo) (((j : ℝ) + 1) / B) with hsU
  have sL0 : 0 < sL := lt_of_lt_of_le xh0 (le_max_left _ _)
  have hjB : ((j : ℝ) + 1) / B ≤ 1 := by
    rw [div_le_one hBp]
    exact_mod_cast hj
  have hjB' : (j : ℝ) / B ≤ 1 := by
    refine le_trans ?_ hjB
    gcongr
    linarith
  have sL1 : sL ≤ 1 := max_le xh1 hjB'
  have sU1 : sU ≤ 1 := (min_le_left _ _).trans xl1
  have sU0 : 0 < sU := lt_min xl0 (by positivity)
  -- the support of the integrand
  have hsupp : ∀ θ ∈ Icc (Th lo) (Th hi), bidx B (sth θ) = j → sL ≤ sth θ ∧ sth θ ≤ sU := by
    intro θ hθ hb
    have hm := hsub hθ
    obtain ⟨u1, u2⟩ := bidx_spec hB (sth_pos hm.1 hm.2).le (sth_le_one θ)
    rw [hb] at u1 u2
    have a1 : sth (Th hi) ≤ sth θ :=
      sth_strictAnti.antitoneOn ⟨hm.1, hm.2.le⟩ ⟨mh.1, mh.2.le⟩ hθ.2
    have a2 : sth θ ≤ sth (Th lo) :=
      sth_strictAnti.antitoneOn ⟨ml.1, ml.2.le⟩ ⟨hm.1, hm.2.le⟩ hθ.1
    rw [hxh] at a1
    rw [hxl] at a2
    refine ⟨max_le a1 ?_, le_min a2 ?_⟩
    · rw [div_le_iff₀ hBp]; exact u1
    · rw [le_div_iff₀ hBp]; exact u2
  unfold segBin
  by_cases hc : sL ≤ sU
  · refine le_trans ?_ (le_max_right _ _)
    set θa := Real.arccos (2 * sU - 1) with hθa
    set θb := Real.arccos (2 * sL - 1) with hθb
    have ea : sth θa = sU := sth_arccos sU0.le sU1
    have eb : sth θb = sL := sth_arccos sL0.le sL1
    have a0 : 0 ≤ θa := Real.arccos_nonneg _
    have b0 : 0 ≤ θb := Real.arccos_nonneg _
    have api : θa ≤ π := Real.arccos_le_pi _
    have bpi : θb ≤ π := Real.arccos_le_pi _
    have l1 : Th lo ≤ θa := by
      refine Real.arccos_le_arccos ?_
      have : sU ≤ YCell.physX lo := min_le_left _ _
      linarith
    have l2 : θa ≤ θb := Real.arccos_le_arccos (by linarith)
    have l3 : θb ≤ Th hi := by
      refine Real.arccos_le_arccos ?_
      have : YCell.physX hi ≤ sL := le_max_left _ _
      linarith
    have I : ∀ a b : ℝ, Th lo ≤ a → a ≤ b → b ≤ Th hi → IntervalIntegrable
        (fun θ => if bidx B (sth θ) = j then dbet θ else 0) volume a b := by
      intro a b ha hb hc
      refine (seg_ite_int (B := B) j h2 hlt).mono_set ?_
      rw [uIcc_of_le hab.le, uIcc_of_le hb]
      exact Icc_subset_Icc ha hc
    have I1 := I _ _ le_rfl l1 (l2.trans l3)
    have I2 := I _ _ l1 l2 l3
    have I3 := I _ _ (l1.trans l2) l3 le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals I1 (I2.trans I3),
      ← intervalIntegral.integral_add_adjacent_intervals I2 I3]
    have z1 : ∫ θ in Th lo..θa, (if bidx B (sth θ) = j then dbet θ else 0) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [(Set.countable_singleton θa).ae_notMem volume] with θ hne hθ
      rw [uIoc_of_le l1] at hθ
      have hlt' : θ < θa := lt_of_le_of_ne hθ.2 hne
      refine if_neg fun hb => ?_
      have := (hsupp θ ⟨hθ.1.le, hθ.2.trans (l2.trans l3)⟩ hb).2
      have h3 : sth θa < sth θ := sth_strictAnti
        ⟨ml.1.trans hθ.1.le, hlt'.le.trans api⟩ ⟨a0, api⟩ hlt'
      linarith
    have z3 : ∫ θ in θb..Th hi, (if bidx B (sth θ) = j then dbet θ else 0) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards with θ hθ
      rw [uIoc_of_le l3] at hθ
      refine if_neg fun hb => ?_
      have := (hsupp θ ⟨(l1.trans l2).trans hθ.1.le, hθ.2⟩ hb).1
      have h3 : sth θ < sth θb := sth_strictAnti
        ⟨b0, bpi⟩ ⟨b0.trans hθ.1.le, hθ.2.trans mh.2.le⟩ hθ.1
      linarith
    rw [z1, z3, zero_add, add_zero]
    have hsub2 : Icc θa θb ⊆ Ico 0 π := fun θ hθ =>
      hsub ⟨l1.trans hθ.1, hθ.2.trans l3⟩
    have hdc : ContinuousOn dbet (Icc θa θb) := continuousOn_dbet.mono hsub2
    have hdi : IntervalIntegrable dbet volume θa θb := hdc.intervalIntegrable_of_Icc l2
    have hmono : ∫ θ in θa..θb, (if bidx B (sth θ) = j then dbet θ else 0) ≤
        ∫ θ in θa..θb, dbet θ := by
      refine intervalIntegral.integral_mono_on l2 I2 hdi ?_
      intro θ hθ
      have hm := hsub2 hθ
      split_ifs
      · exact le_rfl
      · exact dbet_nonneg hm.1 hm.2
    have hft : ∫ θ in θa..θb, dbet θ = bet θb - bet θa := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hdi
      intro θ hθ
      rw [uIcc_of_le l2] at hθ
      have hm := hsub2 hθ
      exact hasDeriv_bet (cos_half_pos hm.1 hm.2).ne'
    have ma := hsub2 ⟨le_rfl, l2⟩
    have mb := hsub2 ⟨l2, le_rfl⟩
    rw [hft, bet_eq_bb mb.1 mb.2, bet_eq_bb ma.1 ma.2, ea, eb] at hmono
    exact hmono
  · refine le_trans (le_of_eq ?_) (le_max_left _ _)
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards with θ hθ
    rw [uIoc_of_le hab.le] at hθ
    refine if_neg fun hb => ?_
    obtain ⟨u, v⟩ := hsupp θ ⟨hθ.1.le, hθ.2⟩ hb
    exact hc (u.trans v)

/-- The upward bin mass: `b` at atoms, the decrease of `b` on each cell-bin overlap. -/
def binUp (B : ℕ) (P : List Seg) (E : List (ℝ × ℝ)) (j : ℕ) : ℝ :=
  (E.map fun e => if bidx B (YCell.physX e.1) = j then |e.2| * bb (YCell.physX e.1) else 0).sum +
    (P.map fun g => |g.rho| * max 0 (bb (max (YCell.physX g.hi) (j / B)) -
      bb (min (YCell.physX g.lo) (((j : ℝ) + 1) / B)))).sum

theorem binMass_le_binUp {B j : ℕ} (hB : 1 ≤ B) (hj : j < B) {P : List Seg} {E : List (ℝ × ℝ)}
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E, 2 ≤ e.1) :
    binMass B P E j ≤ binUp B P E j := by
  unfold binMass binUp
  refine add_le_add (le_of_eq ?_) (list_sum_le _ _ _ fun g hg => ?_)
  · congr 1
    refine List.map_congr_left fun e he => ?_
    have hy := hE e he
    have m := Th_mem hy
    rw [bet_eq_bb m.1 m.2, sth_Th hy]
  · exact mul_le_mul_of_nonneg_left (segBin_le hB hj (hP g hg).1 (hP g hg).2) (abs_nonneg _)

/-- **The bin guard.** Finite data bound the tail functional at every target point. -/
theorem dirV_le_of_bins {N B : ℕ} (hB : 1 ≤ B) {P : List Seg} {E : List (ℝ × ℝ)}
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E, 2 ≤ e.1)
    (K : ℕ → ℝ) (hK : ∀ d < B, kk N B d ≤ K d) (m : ℕ → ℝ) (hm : ∀ j < B, binUp B P E j ≤ m j)
    {Mx : ℝ} (hMx : ∀ i < B, ∑ j ∈ Finset.range B, K (bdist i j) * m j ≤ Mx) :
    ∀ t ∈ Ioc (0 : ℝ) 1, dirV N P E t ≤ Mx := by
  intro t ht
  refine (dirV_le_binSum hB hP hE ht.1.le ht.2 K hK).trans (le_trans ?_ (hMx _ (bidx_lt hB t)))
  refine Finset.sum_le_sum fun j hj => ?_
  have hjB := Finset.mem_range.mp hj
  refine mul_le_mul_of_nonneg_left ((binMass_le_binUp hB hjB hP hE).trans (hm j hjB)) ?_
  exact (kap_pos N _).le.trans (hK _ (bdist_lt (bidx_lt hB t) hjB))

end

section
open Real MeasureTheory Filter Set intervalIntegral Topology
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.Signed.ChebSquare

/-! ### The cell potential in closed form -/

/-- `Φ(z) = z (log|z| - 1)`. -/
def Phi (z : ℝ) : ℝ := z * (Real.log |z| - 1)

/-- The cell potential is an endpoint difference of `Φ`. -/
theorem integral_log_sub_eq_Phi (y l h : ℝ) :
    ∫ s in l..h, Real.log |y - s| = Phi (y - l) - Phi (y - h) := by
  have e1 : ∫ s in l..h, Real.log |y - s| = ∫ s in l..h, Real.log (y - s) :=
    intervalIntegral.integral_congr fun s _ => Real.log_abs _
  rw [e1, intervalIntegral.integral_comp_sub_left (fun u => Real.log u) y, integral_log]
  unfold Phi
  rw [Real.log_abs, Real.log_abs]
  ring

/-! ### The packed convolution guard -/

theorem land_step {w a x g : ℕ} (ha : a < 2 ^ (w + 1))
    (h : (a + 2 ^ (w + 1) * x) &&& (2 ^ w + 2 ^ (w + 1) * g) = 0) :
    a < 2 ^ w ∧ x &&& g = 0 := by
  have hw : 0 < 2 ^ w := Nat.two_pow_pos w
  have p1 : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := pow_succ 2 w
  have t1 : ∀ b y : ℕ, (b + 2 ^ (w + 1) * y) / 2 ^ w % 2 = b / 2 ^ w % 2 := by
    intro b y
    rw [p1, mul_assoc, Nat.add_mul_div_left _ _ hw, Nat.add_mul_mod_self_left]
  have hb : (2 ^ w + 2 ^ (w + 1) * g).testBit w = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, t1, Nat.div_self hw]
  constructor
  · by_contra hc
    have hle : 2 ^ w ≤ a := not_lt.mp hc
    have h1 : a / 2 ^ w = 1 := by
      refine Nat.div_eq_of_lt_le (by omega) ?_
      rw [p1] at ha
      omega
    have ht : (a + 2 ^ (w + 1) * x).testBit w = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, t1, h1]
    have := congrArg (fun n => n.testBit w) h
    simp [Nat.testBit_and, hb, ht] at this
  · have hR : 0 < 2 ^ (w + 1) := Nat.two_pow_pos _
    have s : (a + 2 ^ (w + 1) * x) >>> (w + 1) &&& (2 ^ w + 2 ^ (w + 1) * g) >>> (w + 1) = 0 := by
      rw [← Nat.shiftRight_and_distrib, h]
      simp
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at s
    have d1 : (a + 2 ^ (w + 1) * x) / 2 ^ (w + 1) = x := by
      rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt ha, zero_add]
    have d2 : (2 ^ w + 2 ^ (w + 1) * g) / 2 ^ (w + 1) = g := by
      rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (by rw [p1]; omega), zero_add]
    rw [d1, d2] at s
    exact s

/-- **The max-digit guard.** Bit `w` of every digit of `P + (2^w - 1 - M) U` is clear iff every
digit of `P` is at most `M`, because no digit carries. -/
theorem guard_digits (w : ℕ) {M : ℕ} (hM : M < 2 ^ w) (B : ℕ) (D : ℕ → ℕ)
    (hD : ∀ i < B, D i < 2 ^ w)
    (hg : ((∑ i ∈ Finset.range B, D i * (2 ^ (w + 1)) ^ i) +
        (2 ^ w - 1 - M) * ∑ i ∈ Finset.range B, (2 ^ (w + 1)) ^ i) &&&
      (2 ^ w * ∑ i ∈ Finset.range B, (2 ^ (w + 1)) ^ i) = 0) :
    ∀ i < B, D i ≤ M := by
  induction B generalizing D with
  | zero => intro i hi; omega
  | succ B ih =>
    have hpow : ∀ f : ℕ → ℕ, ∑ i ∈ Finset.range (B + 1), f i * (2 ^ (w + 1)) ^ i =
        f 0 + 2 ^ (w + 1) * ∑ i ∈ Finset.range B, f (i + 1) * (2 ^ (w + 1)) ^ i := by
      intro f
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ]
      ring
    have hU := hpow fun _ => 1
    simp only [one_mul] at hU
    set c := 2 ^ w - 1 - M with hc
    set U' := ∑ i ∈ Finset.range B, (2 ^ (w + 1)) ^ i with hU'
    set P' := ∑ i ∈ Finset.range B, D (i + 1) * (2 ^ (w + 1)) ^ i with hP'
    have e1 : (∑ i ∈ Finset.range (B + 1), D i * (2 ^ (w + 1)) ^ i) +
        c * ∑ i ∈ Finset.range (B + 1), (2 ^ (w + 1)) ^ i =
        (D 0 + c) + 2 ^ (w + 1) * (P' + c * U') := by
      rw [hpow D, hU]
      ring
    have e2 : 2 ^ w * ∑ i ∈ Finset.range (B + 1), (2 ^ (w + 1)) ^ i =
        2 ^ w + 2 ^ (w + 1) * (2 ^ w * U') := by
      rw [hU]
      ring
    rw [e1, e2] at hg
    have hD0 := hD 0 (by omega)
    have p1 : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := pow_succ 2 w
    have hc' : c < 2 ^ w := by omega
    obtain ⟨a, b⟩ := land_step (by omega) hg
    have rest := ih (fun i => D (i + 1)) (fun i hi => hD (i + 1) (by omega)) b
    intro i hi
    rcases i with _ | i
    · omega
    · exact rest i (by omega)

theorem sum_digits_lt {R : ℕ} (hR : 0 < R) (c : ℕ → ℕ) (hc : ∀ i, c i < R) (n : ℕ) :
    ∑ i ∈ Finset.range n, c i * R ^ i < R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := hc n
    have h1 : c n * R ^ n + R ^ n ≤ R ^ n * R := by
      have : (c n + 1) * R ^ n ≤ R * R ^ n := Nat.mul_le_mul_right _ this
      nlinarith
    omega

/-- Extraction of a middle block of digits. -/
theorem middle_digits {R : ℕ} (hR : 0 < R) (c : ℕ → ℕ) (hc : ∀ i, c i < R) (s b r : ℕ) :
    (∑ i ∈ Finset.range (s + (b + r)), c i * R ^ i) / R ^ s % R ^ b =
      ∑ i ∈ Finset.range b, c (s + i) * R ^ i := by
  have hs : 0 < R ^ s := pow_pos hR s
  have hb : 0 < R ^ b := pow_pos hR b
  rw [Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range (b + r), c (s + x) * R ^ (s + x) =
      R ^ s * ∑ x ∈ Finset.range (b + r), c (s + x) * R ^ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
  rw [e1, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt (sum_digits_lt hR c hc s), zero_add,
    Finset.sum_range_add]
  have e2 : ∑ x ∈ Finset.range r, c (s + (b + x)) * R ^ (b + x) =
      R ^ b * ∑ x ∈ Finset.range r, c (s + (b + x)) * R ^ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  exact sum_digits_lt hR (fun i => c (s + i)) (fun i => hc _) b

/-- Product of two packed sequences, digit by digit. -/
theorem pack_mul (R E B : ℕ) (a b : ℕ → ℕ) :
    (∑ e ∈ Finset.range E, a e * R ^ e) * (∑ j ∈ Finset.range B, b j * R ^ j) =
      ∑ s ∈ Finset.range (E + B),
        (∑ j ∈ Finset.range B, if j ≤ s ∧ s - j < E then a (s - j) * b j else 0) * R ^ s := by
  have e0 : ∀ s, (∑ j ∈ Finset.range B, if j ≤ s ∧ s - j < E then a (s - j) * b j else 0) * R ^ s =
      ∑ j ∈ Finset.range B, (if j ≤ s ∧ s - j < E then a (s - j) * b j else 0) * R ^ s :=
    fun s => Finset.sum_mul _ _ _
  simp only [e0]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjB := Finset.mem_range.mp hj
  have hsub : (Finset.range E).image (· + j) ⊆ Finset.range (E + B) := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    have := Finset.mem_range.mp he
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image (fun x _ y _ h => by simpa using h), Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    have := Finset.mem_range.mp he
    rw [if_pos ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel, pow_add]
    ring
  · intro s _ hs
    have hn : ¬(j ≤ s ∧ s - j < E) := by
      rintro ⟨u, v⟩
      apply hs
      exact Finset.mem_image.mpr ⟨s - j, Finset.mem_range.mpr v, by
        show s - j + j = s
        omega⟩
    rw [if_neg hn, zero_mul]

/-- **Packed convolution guard.** One product, one shift and mask, one bit test bound all `B`
convolution values. The kernel is packed at index `e` as `K (bdist e (B-1))`. -/
theorem conv_guard (w : ℕ) {B M Kmax : ℕ} (hB : 1 ≤ B) (K m : ℕ → ℕ) (hM : M < 2 ^ w)
    (hK : ∀ e < 2 * B, K (bdist e (B - 1)) ≤ Kmax)
    (hmass : Kmax * ∑ j ∈ Finset.range B, m j < 2 ^ w)
    (hg : (((∑ e ∈ Finset.range (2 * B), K (bdist e (B - 1)) * (2 ^ (w + 1)) ^ e) *
          (∑ j ∈ Finset.range B, m j * (2 ^ (w + 1)) ^ j)) / (2 ^ (w + 1)) ^ (B - 1) %
            (2 ^ (w + 1)) ^ B +
        (2 ^ w - 1 - M) * ∑ i ∈ Finset.range B, (2 ^ (w + 1)) ^ i) &&&
      (2 ^ w * ∑ i ∈ Finset.range B, (2 ^ (w + 1)) ^ i) = 0) :
    ∀ i < B, ∑ j ∈ Finset.range B, K (bdist i j) * m j ≤ M := by
  set R := 2 ^ (w + 1) with hRdef
  have hR : 0 < R := Nat.two_pow_pos _
  have p1 : R = 2 ^ w * 2 := pow_succ 2 w
  set a : ℕ → ℕ := fun e => K (bdist e (B - 1)) with ha
  set c : ℕ → ℕ := fun s => ∑ j ∈ Finset.range B,
    if j ≤ s ∧ s - j < 2 * B then a (s - j) * m j else 0 with hc
  have hcb : ∀ s, c s < 2 ^ w := by
    intro s
    refine lt_of_le_of_lt ?_ hmass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact Nat.mul_le_mul_right _ (hK _ h.2)
    · exact Nat.zero_le _
  have hcR : ∀ s, c s < R := fun s => by
    have := hcb s
    omega
  have hmid : (∑ e ∈ Finset.range (2 * B), a e * R ^ e) *
      (∑ j ∈ Finset.range B, m j * R ^ j) / R ^ (B - 1) % R ^ B =
      ∑ i ∈ Finset.range B, c (B - 1 + i) * R ^ i := by
    rw [pack_mul]
    have e : 2 * B + B = (B - 1) + (B + (B + 1)) := by omega
    rw [e]
    exact middle_digits hR c hcR (B - 1) B (B + 1)
  rw [hmid] at hg
  have key := guard_digits w hM B (fun i => c (B - 1 + i)) (fun i _ => hcb _) hg
  intro i hi
  refine le_trans (le_of_eq ?_) (key i hi)
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjB := Finset.mem_range.mp hj
  have hcond : j ≤ B - 1 + i ∧ B - 1 + i - j < 2 * B := by omega
  rw [if_pos hcond]
  have : bdist (B - 1 + i - j) (B - 1) = bdist i j := by
    unfold bdist
    omega
  simp only [ha, this]

/-- The bin guard from packed naturals: kernel `Kn/dK`, masses `mn/dm`, bound `M/(dK dm)`. -/
theorem dirV_le_of_packed {N B : ℕ} (hB : 1 ≤ B) {P : List Seg} {E : List (ℝ × ℝ)}
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E, 2 ≤ e.1)
    {Kn mn : ℕ → ℕ} {dK dm : ℝ} (hdK : 0 < dK) (hdm : 0 < dm) {M : ℕ}
    (hK : ∀ d < B, kk N B d ≤ (Kn d : ℝ) / dK)
    (hm : ∀ j < B, binUp B P E j ≤ (mn j : ℝ) / dm)
    (hconv : ∀ i < B, ∑ j ∈ Finset.range B, Kn (bdist i j) * mn j ≤ M) :
    ∀ t ∈ Ioc (0 : ℝ) 1, dirV N P E t ≤ (M : ℝ) / (dK * dm) := by
  refine dirV_le_of_bins hB hP hE (fun d => (Kn d : ℝ) / dK) hK (fun j => (mn j : ℝ) / dm) hm ?_
  intro i hi
  have h := hconv i hi
  have h' : (∑ j ∈ Finset.range B, (Kn (bdist i j) : ℝ) * mn j) ≤ M := by exact_mod_cast h
  have e : ∑ j ∈ Finset.range B, (Kn (bdist i j) : ℝ) / dK * ((mn j : ℝ) / dm) =
      (∑ j ∈ Finset.range B, (Kn (bdist i j) : ℝ) * mn j) / (dK * dm) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right h' (by positivity)

/-- A bin index certified by a rational enclosure. -/
theorem bidx_eq {B j : ℕ} (hB : 1 ≤ B) (hj : j < B) {s : ℝ} (h1 : (j : ℝ) / B ≤ s)
    (h2 : s < ((j : ℝ) + 1) / B) : bidx B s = j := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  rw [div_le_iff₀ hBp] at h1
  rw [lt_div_iff₀ hBp] at h2
  have hf : ⌊s * (B : ℝ)⌋₊ = j := by
    rw [Nat.floor_eq_iff ((Nat.cast_nonneg j).trans h1)]
    exact ⟨h1, h2⟩
  unfold bidx
  rw [hf]
  exact min_eq_left (by omega)

/-! ### The fixed-point ledger -/

/-- Accumulated error of `x (n+1) = u n - x n`. -/
theorem rec1_err {x y u v β δ : ℕ → ℝ} (hx : ∀ n, x (n + 1) = u n - x n)
    (hy : ∀ n, |y (n + 1) - (v n - y n)| ≤ δ n) (huv : ∀ n, |u n - v n| ≤ β n) (n : ℕ) :
    |x n - y n| ≤ |x 0 - y 0| + ∑ i ∈ Finset.range n, (β i + δ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, hx]
    have e : u n - x n - y (n + 1) =
        (u n - v n) - (x n - y n) - (y (n + 1) - (v n - y n)) := by ring
    rw [e]
    have a := abs_sub (u n - v n - (x n - y n)) (y (n + 1) - (v n - y n))
    have b := abs_sub (u n - v n) (x n - y n)
    linarith [huv n, hy n]

/-- Accumulated error of `x (n+2) = f n - 2 x (n+1) - x n`, a double root at `-1`. -/
theorem rec2_err {x y f g : ℕ → ℝ} {H : ℝ}
    (hx : ∀ n, x (n + 2) = f n - 2 * x (n + 1) - x n)
    (hy : ∀ n, |y (n + 2) - (g n - 2 * y (n + 1) - y n)| + |f n - g n| ≤ H) (n : ℕ) :
    |x n - y n| ≤ |x 0 - y 0| + n * (|x 0 - y 0| + |x 1 - y 1|) + n * (n - 1) / 2 * H := by
  set d : ℕ → ℝ := fun n => x n - y n with hd
  set u : ℕ → ℝ := fun n => (-1) ^ n * d n with hu
  have hH : 0 ≤ H := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hy 0)
  have habs : ∀ n, |u n| = |d n| := fun n => by simp [hu, abs_mul]
  have hdd : ∀ n, |u (n + 2) - u (n + 1) - (u (n + 1) - u n)| ≤ H := by
    intro n
    have e : u (n + 2) - u (n + 1) - (u (n + 1) - u n) =
        (-1) ^ n * (d (n + 2) + 2 * d (n + 1) + d n) := by
      simp only [hu, pow_succ]
      ring
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have e2 : d (n + 2) + 2 * d (n + 1) + d n =
        (f n - g n) - (y (n + 2) - (g n - 2 * y (n + 1) - y n)) := by
      simp only [hd, hx]
      ring
    rw [e2]
    have := abs_sub (f n - g n) (y (n + 2) - (g n - 2 * y (n + 1) - y n))
    linarith [hy n]
  have hv : ∀ n : ℕ, |u (n + 1) - u n| ≤ |u 1 - u 0| + n * H := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := abs_add_le (u (n + 2) - u (n + 1) - (u (n + 1) - u n)) (u (n + 1) - u n)
      have e : u (n + 2) - u (n + 1) - (u (n + 1) - u n) + (u (n + 1) - u n) =
          u (n + 1 + 1) - u (n + 1) := by ring
      rw [e] at this
      push_cast
      linarith [hdd n]
  have hu2 : ∀ n : ℕ, |u n| ≤ |u 0| + n * |u 1 - u 0| + n * (n - 1) / 2 * H := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := abs_add_le (u (n + 1) - u n) (u n)
      have e : u (n + 1) - u n + u n = u (n + 1) := by ring
      rw [e] at this
      have h3 := hv n
      push_cast
      nlinarith
  have h0 : |u 1 - u 0| ≤ |d 0| + |d 1| := by
    have := abs_sub (u 1) (u 0)
    rw [habs, habs] at this
    linarith
  have fin := hu2 n
  rw [habs, habs] at fin
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_le_mul_of_nonneg_left h0 hn
  have hd0 : d 0 = x 0 - y 0 := rfl
  have hd1 : d 1 = x 1 - y 1 := rfl
  have hdn : d n = x n - y n := rfl
  rw [hdn, hd0] at fin
  rw [hd0, hd1] at this
  linarith

/-- `|U_k(z)| ≤ k+1` on `[-1,1]`. -/
theorem abs_U_le {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (k : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (k : ℤ)).eval z| ≤ k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℝ (k : ℤ)
    have e : (Polynomial.Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval z =
        z * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval z + basis (k + 1) z := by
      unfold basis
      push_cast
      rw [h]
      simp
    rw [e]
    have hz1 : |z| ≤ 1 := abs_le.mpr hz
    have hb := abs_basis_le_one (k + 1) hz
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h3 : |z| * |(Polynomial.Chebyshev.U ℝ (k : ℤ)).eval z| ≤ 1 * ((k : ℝ) + 1) :=
      mul_le_mul hz1 ih (abs_nonneg _) zero_le_one
    push_cast
    linarith

/-- `V k = U_{k-1}(z)`. -/
def Vz (z : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval z

theorem Vz_add_two (z : ℝ) (k : ℕ) : Vz z (k + 2) = 2 * z * Vz z (k + 1) - Vz z k := by
  rcases k with _ | k
  · simp [Vz]
  · have h := Polynomial.Chebyshev.U_add_two ℝ (k : ℤ)
    simp only [Vz]
    push_cast
    rw [h]
    simp

theorem abs_Vz_le {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (k : ℕ) : |Vz z k| ≤ k := by
  rcases k with _ | k
  · simp [Vz]
  · simp only [Vz]
    push_cast
    exact abs_U_le hz k

/-- The impulse response of the Chebyshev recurrence. -/
theorem impulse {z : ℝ} {d η : ℕ → ℝ} (hd : ∀ n, d (n + 2) = 2 * z * d (n + 1) - d n + η n)
    (n : ℕ) :
    d (n + 1) = Vz z (n + 1) * d 1 - Vz z n * d 0 +
        ∑ i ∈ Finset.range n, Vz z (n - i) * η i ∧
      d (n + 2) = Vz z (n + 2) * d 1 - Vz z (n + 1) * d 0 +
        ∑ i ∈ Finset.range (n + 1), Vz z (n + 1 - i) * η i := by
  induction n with
  | zero =>
    have v1 : Vz z 1 = 1 := by simp [Vz]
    have v2 : Vz z 2 = 2 * z := by simp [Vz]
    refine ⟨by simp [v1, Vz], ?_⟩
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
    rw [hd 0, v1, v2]
    simp [Vz]
  | succ n ih =>
    obtain ⟨a, b⟩ := ih
    refine ⟨b, ?_⟩
    rw [hd (n + 1), b, a, Vz_add_two z (n + 1), Vz_add_two z n]
    rw [Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ n, Finset.sum_range_succ _ n]
    have e : ∑ i ∈ Finset.range n, Vz z (n + 1 + 1 - i) * η i =
        2 * z * ∑ i ∈ Finset.range n, Vz z (n + 1 - i) * η i -
          ∑ i ∈ Finset.range n, Vz z (n - i) * η i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin := Finset.mem_range.mp hi
      have e1 : n + 1 + 1 - i = (n - i) + 2 := by omega
      have e2 : n + 1 - i = (n - i) + 1 := by omega
      rw [e1, e2, Vz_add_two]
      ring
    rw [e]
    have v1 : Vz z 1 = 1 := by simp [Vz]
    have v2 : Vz z 2 = 2 * z := by simp [Vz]
    have s1 : n + 1 + 1 - n = 2 := by omega
    have s2 : n + 1 + 1 - (n + 1) = 1 := by omega
    have s3 : n + 1 - n = 1 := by omega
    rw [s1, s2, s3, v1, v2]
    ring

theorem sum_sub_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, ((n - i : ℕ) : ℝ) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have e : ∀ i ∈ Finset.range n, ((n + 1 - i : ℕ) : ℝ) = ((n - i : ℕ) : ℝ) + 1 := by
      intro i hi
      have := Finset.mem_range.mp hi
      have e : n + 1 - i = (n - i) + 1 := by omega
      rw [e]
      push_cast
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : n + 1 - n = 1 := by omega
    rw [this]
    push_cast
    ring

/-- **Chebyshev recurrence ledger**: local error `δ` accumulates to `n(n+1)δ/2`, no re-anchoring. -/
theorem recT_err {x y : ℕ → ℝ} {z δ : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hx : ∀ n, x (n + 2) = 2 * z * x (n + 1) - x n)
    (hy : ∀ n, |y (n + 2) - (2 * z * y (n + 1) - y n)| ≤ δ) (n : ℕ) :
    |x (n + 1) - y (n + 1)| ≤
      (n + 1) * |x 1 - y 1| + n * |x 0 - y 0| + (n : ℝ) * (n + 1) / 2 * δ := by
  set d : ℕ → ℝ := fun n => x n - y n with hdd
  set η : ℕ → ℝ := fun n => -(y (n + 2) - (2 * z * y (n + 1) - y n)) with hη
  have hd : ∀ n, d (n + 2) = 2 * z * d (n + 1) - d n + η n := by
    intro n
    simp only [hdd, hη, hx]
    ring
  have e := (impulse hd n).1
  have e2 : x (n + 1) - y (n + 1) = d (n + 1) := rfl
  rw [e2, e]
  have b1 : |Vz z (n + 1) * d 1| ≤ (n + 1) * |d 1| := by
    rw [abs_mul]
    have := abs_Vz_le hz (n + 1)
    push_cast at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have b2 : |Vz z n * d 0| ≤ n * |d 0| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_Vz_le hz n) (abs_nonneg _)
  have b3 : |∑ i ∈ Finset.range n, Vz z (n - i) * η i| ≤ (n : ℝ) * (n + 1) / 2 * δ := by
    rw [← sum_sub_cast, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul (abs_Vz_le hz _) ?_ (abs_nonneg _) (Nat.cast_nonneg _)
    simp only [hη, abs_neg]
    exact hy i
  have t1 := abs_add_le (Vz z (n + 1) * d 1 - Vz z n * d 0) (∑ i ∈ Finset.range n, Vz z (n - i) * η i)
  have t2 := abs_sub (Vz z (n + 1) * d 1) (Vz z n * d 0)
  have g1 : d 1 = x 1 - y 1 := rfl
  have g0 : d 0 = x 0 - y 0 := rfl
  rw [← g1, ← g0]
  linarith

/-! ### Enclosures of the ideal coefficients -/

theorem evE_sub_le (E : List (ℝ × ℝ)) (F G : ℝ → ℝ) (d : ℝ → ℝ)
    (h : ∀ e ∈ E, |F e.1 - G e.1| ≤ d e.1) :
    |evE E F - evE E G| ≤ (E.map fun e => |e.2| * d e.1).sum := by
  induction E with
  | nil => simp [evE]
  | cons e t ih =>
    have ih2 := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp only [evE, List.map_cons, List.sum_cons] at ih2 ⊢
    have e1 : e.2 * F e.1 + (t.map fun e => e.2 * F e.1).sum -
        (e.2 * G e.1 + (t.map fun e => e.2 * G e.1).sum) =
        e.2 * (F e.1 - G e.1) + ((t.map fun e => e.2 * F e.1).sum -
          (t.map fun e => e.2 * G e.1).sum) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih2)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h e List.mem_cons_self) (abs_nonneg _)

/-- The ideal list of the source as one coefficient stream. -/
def idealCoef (W : Profile) (N Lr La : ℕ) (k : ℕ) : ℝ :=
  ((if k < N + 1 then -evE W.Es (Adir k) else 0) +
    (if k < Lr + 1 then -evE W.Es (QS 1 (qc rR) k) else 0)) +
  (if k < La + 1 then -evE W.Eo (AD k) - evE W.Eo (QS (-1) (qc rO) k) +
    2 * evE W.Ec (QS 2 qC k) else 0)

end

#print axioms dirV_le_of_bins
#print axioms dirV_le_of_packed
#print axioms conv_guard
#print axioms integral_log_sub_eq_Phi
#print axioms recT_err
#print axioms rec2_err
#print axioms rec1_err

end

end CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
