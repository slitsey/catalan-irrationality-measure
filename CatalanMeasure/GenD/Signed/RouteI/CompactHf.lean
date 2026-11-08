module

public import CatalanMeasure.GenD.Signed.RouteI.CompactInstance
public import CatalanMeasure.GenD.Signed.RouteI.MomentSource
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section
set_option Elab.async false

/-!
# Route I `CompactHf`: the Near `hf`, from data-side facts

Plan row C4, `NearHf` of `CompactInstance` for an arbitrary `S : CapSource`, from finite
data-side facts. Generic and data-free (no `CapSource` instance is imported).

**Statement.** `nearHf S hS hd hε1 hε2 hmass : NearHf S (Trunc.finite 384)`, that is
`nearField (finite 384) y <= chebSum nearP D (affine (1/10) y) + nearEps` on `[1/10, 1]`.

**Data-side hypotheses** (`NearData S`, or `NearDataClosed S` with the moments written as the
finite cell sum of `reflMoment_closed`): for `k = 1..32`, `|reflMoment k - muL k| <= 10^-4` and
`|radCoef k - alL k| <= 10^-4`, and `sum_(k=33)^384 |radCoef k| <= 5 * 10^-3`, where `radCoef k` is the
aggregated radial coefficient `sum_e w_e coef_k r_e^k cos(k phase_e)`; plus the seed facts
`1/10 <= eps <= 3/20` and `63/100 <= gas mass`, which give `auxTail <= 1/5000` (`auxTail_small`).

**Proof.** (1) `nearField` is `(24/29) log y - (53/58) log(1+y^2) - kappa - R900 + radial + auxTail`
(`near_unfold`). (2) `R900 >= ` its degree-32 partial sum since the moments are nonnegative
(`R900_ge`); the radial series is cut at 32 and the rest is bounded by the absolute tail times
`|y|^n <= 1` (`poly_part`). (3) With `y = 11/20 + 9/20 u`, `log y = log X + 2 sum (-1)^i rho^(i+1)
T_(i+1)(u)/(i+1)` + a geometric remainder (`log_y_series`, from the Taylor remainder of
`Complex.log(1+rho e^(i t))`), `rho = (11 - sqrt 40)/9`, `X = (11 + sqrt 40)/40`; and
`log(1+y^2) = log(521/400) + log(1+z)`, `z = (198u + 81u^2)/521`, `|z| <= 279/521`, with the
alternating Taylor remainder (`log_z_lower`). Rational logarithms by `Real.abs_log_sub_add_sum_range_le`.
(4) The rational polynomial so obtained is carried to a Chebyshev list by Horner steps
(`mulU`, `hornerY`, `hornerZ`; soundness `rawQ_mulU`, `rawQ_hornerY`, `rawQ_hornerZ`) and compared
with the pinned `nearP` by `diffSum` (`abs_rawQ_sub_le`). (5) `final_check` is one kernel decision:
all the explicit errors plus `diffSum` are below `nearEps`. The departure from the paper:
the omitted R900 tail (`sum_(k>32) m_k/k = 0.024355`, which is essentially all of `nearEps`) is
dropped by sign instead of being charged, so the room is `nearEps - 0.0125` about 0.0118 (a tolerance of 10^-4 per coefficient); the
radial tail is the data-side hypothesis (true value 1.45e-4, allowed 5e-3).

kcost: `final_check` is about 2500 rational operations on 100-bit numbers (Horner over 33 and 15
steps, lists of at most 34 entries) plus one pass over 129 coefficients.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CompactHf

open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CompactInstance (nearP nearEps D)
open Set
open MeasureTheory intervalIntegral

/-! ### Chebyshev lists over `ℚ` -/

/-- Coefficientwise sum. -/
def addQ : List ℚ → List ℚ → List ℚ
  | [], b => b
  | a, [] => a
  | x :: s, y :: t => (x + y) :: addQ s t

/-- Scalar multiple. -/
def smulQ (s : ℚ) (a : List ℚ) : List ℚ := a.map (s * ·)

/-- `sum_i l_i T_(k+i)(x)`. -/
noncomputable def rawQ : List ℚ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: t, k, x => (a : ℝ) * basis k x + rawQ t (k + 1) x

theorem rawQ_addQ : ∀ (a b : List ℚ) (k : ℕ) (x : ℝ),
    rawQ (addQ a b) k x = rawQ a k x + rawQ b k x
  | [], b, k, x => by simp [addQ, rawQ]
  | a :: s, [], k, x => by simp [addQ, rawQ]
  | a :: s, b :: t, k, x => by
    simp only [addQ, rawQ, rawQ_addQ s t (k + 1) x]
    push_cast
    ring

theorem rawQ_smulQ (s : ℚ) : ∀ (a : List ℚ) (k : ℕ) (x : ℝ),
    rawQ (smulQ s a) k x = (s : ℝ) * rawQ a k x
  | [], k, x => by simp [smulQ, rawQ]
  | a :: t, k, x => by
    have := rawQ_smulQ s t (k + 1) x
    simp only [smulQ, List.map_cons, rawQ] at this ⊢
    rw [this]
    push_cast
    ring

/-- `x T_(k+1+i) = (T_(k+2+i) + T_(k+i))/2`: multiplication by `x` on a list based at `k+1`. -/
theorem x_mul_rawQ (x : ℝ) : ∀ (l : List ℚ) (k : ℕ),
    x * rawQ l (k + 1) x = 1 / 2 * rawQ l (k + 2) x + 1 / 2 * rawQ l k x
  | [], k => by simp [rawQ]
  | a :: t, k => by
    have ih := x_mul_rawQ x t (k + 1)
    have hb := basis_mul 1 (k + 1) x
    have h1 : basis 1 x = x := by simp [basis]
    have h2 : ((1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) = -(k : ℤ) := by push_cast; ring
    rw [h1, h2, Int.natAbs_neg, Int.natAbs_natCast] at hb
    simp only [rawQ]
    have e1 : 1 + (k + 1) = k + 2 := by omega
    rw [e1] at hb
    have : k + 1 + 1 = k + 2 := by omega
    have ih' : x * rawQ t (k + 1 + 1) x = 1 / 2 * rawQ t (k + 1 + 2) x + 1 / 2 * rawQ t (k + 1) x := ih
    calc x * ((a : ℝ) * basis (k + 1) x + rawQ t (k + 1 + 1) x)
        = (a : ℝ) * (x * basis (k + 1) x) + x * rawQ t (k + 1 + 1) x := by ring
      _ = _ := by
        rw [ih']
        have : x * basis (k + 1) x = 1 / 2 * (basis (k + 2) x + basis k x) := by linarith
        rw [this]
        ring

/-- Multiplication by `x` in the Chebyshev basis. -/
def mulU : List ℚ → List ℚ
  | [] => []
  | a :: t => addQ (addQ [0, a] (0 :: 0 :: smulQ (1 / 2) t)) (smulQ (1 / 2) t)

theorem rawQ_mulU (x : ℝ) : ∀ l : List ℚ, rawQ (mulU l) 0 x = x * rawQ l 0 x
  | [] => by simp [mulU, rawQ]
  | a :: t => by
    have h := x_mul_rawQ x t 0
    simp only [mulU, rawQ_addQ, rawQ_smulQ, rawQ]
    have h1 : basis 1 x = x := by simp [basis]
    simp only [zero_add, basis_zero] at h ⊢
    rw [h1]
    push_cast
    nlinarith [h]


/-! ### Horner evaluation in the Chebyshev basis -/

/-- `b_0 + y (b_1 + y (b_2 + ...))`. -/
def polyR (b : List ℚ) (y : ℝ) : ℝ := b.foldr (fun a acc => (a : ℝ) + y * acc) 0

theorem polyR_cons (a : ℚ) (t : List ℚ) (y : ℝ) : polyR (a :: t) y = (a : ℝ) + y * polyR t y := rfl

theorem rawQ_single (b : ℚ) (x : ℝ) : rawQ [b] 0 x = b := by simp [rawQ]

/-- `sum_k b_k y^k` with `y = 11/20 + 9/20 u`, as a Chebyshev list in `u`. -/
def hornerY : List ℚ → List ℚ
  | [] => []
  | b :: t => addQ [b] (addQ (smulQ (11 / 20) (hornerY t)) (smulQ (9 / 20) (mulU (hornerY t))))

theorem rawQ_hornerY (x : ℝ) : ∀ b : List ℚ,
    rawQ (hornerY b) 0 x = polyR b (11 / 20 + 9 / 20 * x)
  | [] => by simp [hornerY, rawQ, polyR]
  | b :: t => by
    have ih := rawQ_hornerY x t
    simp only [hornerY, rawQ_addQ, rawQ_smulQ, rawQ_single, rawQ_mulU, polyR_cons, ih]
    push_cast
    ring

/-- Multiplication by `z = (198 u + 81 u^2)/521`. -/
def zMul (acc : List ℚ) : List ℚ :=
  mulU (addQ (smulQ (198 / 521) acc) (smulQ (81 / 521) (mulU acc)))

theorem rawQ_zMul (x : ℝ) (acc : List ℚ) :
    rawQ (zMul acc) 0 x = (198 * x + 81 * x ^ 2) / 521 * rawQ acc 0 x := by
  simp only [zMul, rawQ_mulU, rawQ_addQ, rawQ_smulQ]
  push_cast
  ring

/-- `sum_n g_n z^n`, `z = (198 u + 81 u^2)/521`, as a Chebyshev list. -/
def hornerZ : List ℚ → List ℚ
  | [] => []
  | g :: t => addQ [g] (zMul (hornerZ t))

theorem rawQ_hornerZ (x : ℝ) : ∀ g : List ℚ,
    rawQ (hornerZ g) 0 x = polyR g ((198 * x + 81 * x ^ 2) / 521)
  | [] => by simp [hornerZ, rawQ, polyR]
  | g :: t => by
    have ih := rawQ_hornerZ x t
    simp only [hornerZ, rawQ_addQ, rawQ_single, rawQ_zMul, polyR_cons, ih]

theorem polyR_range (g : ℕ → ℚ) (y : ℝ) : ∀ n : ℕ,
    polyR ((List.range n).map g) y = ∑ i ∈ Finset.range n, (g i : ℝ) * y ^ i
  | 0 => by simp [polyR]
  | n + 1 => by
    have ih := polyR_range (fun i => g (i + 1)) y n
    rw [List.range_succ_eq_map, List.map_cons, polyR_cons, List.map_map]
    have : ((fun i => g i) ∘ Nat.succ) = fun i => g (i + 1) := rfl
    simp only [Function.comp_def] at ih ⊢
    rw [ih, Finset.sum_range_succ' _ n]
    simp [Finset.mul_sum, pow_succ]
    ring_nf

/-! ### Comparison with a pinned integer list -/

/-- `sum_j |p_j / D|`. -/
def dsum (D : ℚ) : List ℤ → ℚ
  | [] => 0
  | b :: t => |(b : ℚ) / D| + dsum D t

/-- `sum_j |g_j - p_j / D|` (structural in the first list). -/
def diffSum (D : ℚ) : List ℚ → List ℤ → ℚ
  | [], p => dsum D p
  | a :: s, [] => |a| + diffSum D s []
  | a :: s, b :: t => |a - (b : ℚ) / D| + diffSum D s t

theorem abs_rawSum_div_le (D : ℕ) : ∀ (p : List ℤ) (k : ℕ) (x : ℝ), x ∈ Icc (-1 : ℝ) 1 →
    |rawSum p k x / (D : ℝ)| ≤ ((dsum (D : ℚ) p : ℚ) : ℝ)
  | [], k, x, hx => by simp [rawSum, dsum]
  | b :: t, k, x, hx => by
    have ih := abs_rawSum_div_le D t (k + 1) x hx
    have hb := abs_basis_le_one k hx
    simp only [rawSum, dsum] at ih ⊢
    push_cast at ih ⊢
    rw [add_div]
    have h1 : |(b : ℝ) * basis k x / D| ≤ |(b : ℝ) / D| := by
      rw [abs_div, abs_div, abs_mul]
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      exact mul_le_of_le_one_right (abs_nonneg _) hb
    calc |(b : ℝ) * basis k x / D + rawSum t (k + 1) x / D| ≤
          |(b : ℝ) * basis k x / D| + |rawSum t (k + 1) x / D| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem abs_rawQ_sub_le (D : ℕ) : ∀ (g : List ℚ) (p : List ℤ) (k : ℕ) (x : ℝ),
    x ∈ Icc (-1 : ℝ) 1 →
    |rawQ g k x - rawSum p k x / (D : ℝ)| ≤ (diffSum (D : ℚ) g p : ℝ)
  | [], p, k, x, hx => by
    simpa [diffSum, rawQ] using abs_rawSum_div_le D p k x hx
  | a :: s, [], k, x, hx => by
    have ih := abs_rawQ_sub_le D s [] (k + 1) x hx
    have hb := abs_basis_le_one k hx
    simp only [diffSum, rawQ, rawSum, zero_div, sub_zero] at ih ⊢
    push_cast
    have h1 : |(a : ℝ) * basis k x| ≤ |(a : ℝ)| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hb
    calc |(a : ℝ) * basis k x + rawQ s (k + 1) x| ≤ |(a : ℝ) * basis k x| + |rawQ s (k + 1) x| :=
          abs_add_le _ _
      _ ≤ _ := by linarith
  | a :: s, b :: t, k, x, hx => by
    have ih := abs_rawQ_sub_le D s t (k + 1) x hx
    have hb := abs_basis_le_one k hx
    simp only [diffSum, rawQ, rawSum] at ih ⊢
    push_cast
    have e : (a : ℝ) * basis k x + rawQ s (k + 1) x -
        (((b : ℝ) * basis k x + rawSum t (k + 1) x) / D) =
        ((a : ℝ) - b / D) * basis k x + (rawQ s (k + 1) x - rawSum t (k + 1) x / D) := by ring
    rw [e]
    have h1 : |((a : ℝ) - b / D) * basis k x| ≤ |(a : ℝ) - b / D| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hb
    calc _ ≤ |((a : ℝ) - b / D) * basis k x| + |rawQ s (k + 1) x - rawSum t (k + 1) x / D| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

/-! ### Taylor remainder of `log (1+w)` -/

/-- `sum_(k<M) (-1)^k w^(k+1)/(k+1)`. -/
noncomputable def logPS (M : ℕ) (u : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * u ^ (k + 1) / ((k : ℂ) + 1)

theorem norm_log_one_add_sub_logPS_le (M : ℕ) {u : ℂ} {s : ℝ} (hu : ‖u‖ ≤ s) (hs : s < 1) :
    ‖Complex.log (1 + u) - logPS M u‖ ≤ s ^ (M + 1) / (((M : ℝ) + 1) * (1 - s)) := by
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu hs
  have hs0 : 0 ≤ s := (norm_nonneg u).trans hu
  have hS := Complex.hasSum_taylorSeries_log hu1
  set f : ℕ → ℂ := fun n => (-1) ^ (n + 1) * u ^ n / n with hf
  have hsum : ∑ i ∈ Finset.range (M + 1), f i = logPS M u := by
    rw [Finset.sum_range_succ']
    simp only [hf, logPS]
    have h0 : (-1 : ℂ) ^ (0 + 1) * u ^ 0 / ((0 : ℕ) : ℂ) = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    have : (-1 : ℂ) ^ (k + 1 + 1) = (-1) ^ k := by
      rw [pow_succ, pow_succ]; ring
    rw [this]
  have hdec := hS.summable.sum_add_tsum_nat_add (M + 1)
  rw [hS.tsum_eq, hsum] at hdec
  have hrest : Complex.log (1 + u) - logPS M u = ∑' i, f (i + (M + 1)) := by
    rw [← hdec]; ring
  rw [hrest]
  have hg : HasSum (fun i : ℕ => s ^ (M + 1) / ((M : ℝ) + 1) * s ^ i)
      (s ^ (M + 1) / ((M : ℝ) + 1) * (1 - s)⁻¹) :=
    (hasSum_geometric_of_lt_one hs0 hs).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun i => f (i + (M + 1))) (fun i => by
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_natCast]
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have h1 : ‖u‖ ^ (i + (M + 1)) ≤ s ^ (i + (M + 1)) := pow_le_pow_left₀ (norm_nonneg u) hu _
    have h2 : ((M : ℝ) + 1) ≤ ((i + (M + 1) : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    calc ‖u‖ ^ (i + (M + 1)) / ((i + (M + 1) : ℕ) : ℝ)
        ≤ s ^ (i + (M + 1)) / ((i + (M + 1) : ℕ) : ℝ) := by gcongr
      _ ≤ s ^ (i + (M + 1)) / ((M : ℝ) + 1) := by
          apply div_le_div_of_nonneg_left (by positivity) hM h2
      _ = s ^ (M + 1) / ((M : ℝ) + 1) * s ^ i := by ring)
  refine hb.trans (le_of_eq ?_)
  have : (1 - s) ≠ 0 := by linarith
  field_simp

/-! ### `log (1 + 2 rho cos t + rho^2)` as a cosine series -/

theorem w_pow_re (ρ θ : ℝ) (n : ℕ) :
    (((ρ : ℂ) * Complex.exp (θ * Complex.I)) ^ n).re = ρ ^ n * Real.cos (n * θ) := by
  have : ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ^ n =
      ((ρ ^ n : ℝ) : ℂ) * Complex.exp (((n * θ : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem log_cos_series {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (θ : ℝ) (M : ℕ) :
    |Real.log (1 + 2 * ρ * Real.cos θ + ρ ^ 2) -
        2 * ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * ρ ^ (i + 1) * Real.cos ((i + 1 : ℕ) * θ) /
          ((i : ℝ) + 1)| ≤ 2 * (ρ ^ (M + 1) / (((M : ℝ) + 1) * (1 - ρ))) := by
  set w : ℂ := (ρ : ℂ) * Complex.exp (θ * Complex.I) with hw
  have hwn : ‖w‖ = ρ := by
    rw [hw, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_pos h0]
  have hb := norm_log_one_add_sub_logPS_le M (u := w) (s := ρ) hwn.le h1
  have hre : |(Complex.log (1 + w) - logPS M w).re| ≤ ρ ^ (M + 1) / (((M : ℝ) + 1) * (1 - ρ)) :=
    (Complex.abs_re_le_norm _).trans hb
  have h1w : (1 + w).re = 1 + ρ * Real.cos θ := by
    rw [hw]; simp [Complex.exp_ofReal_mul_I_re]
  have h2w : (1 + w).im = ρ * Real.sin θ := by
    rw [hw]; simp [Complex.exp_ofReal_mul_I_im]
  have hsq : ‖1 + w‖ ^ 2 = 1 + 2 * ρ * Real.cos θ + ρ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h1w, h2w]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsqpos : 0 < ‖1 + w‖ ^ 2 := by
    rw [hsq]; nlinarith [Real.neg_one_le_cos θ]
  have hpos : 0 < ‖1 + w‖ :=
    lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at hsqpos; simp at hsqpos)
  have hlogre : (Complex.log (1 + w)).re = Real.log ‖1 + w‖ := Complex.log_re _
  have hlog2 : Real.log (1 + 2 * ρ * Real.cos θ + ρ ^ 2) = 2 * Real.log ‖1 + w‖ := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hps : (logPS M w).re = ∑ i ∈ Finset.range M,
      (-1 : ℝ) ^ i * ρ ^ (i + 1) * Real.cos ((i + 1 : ℕ) * θ) / ((i : ℝ) + 1) := by
    unfold logPS
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : (-1 : ℂ) ^ i * w ^ (i + 1) / ((i : ℂ) + 1) =
        (((-1 : ℝ) ^ i / ((i : ℝ) + 1) : ℝ) : ℂ) * w ^ (i + 1) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, hw, w_pow_re]
    ring
  have hre' : (Complex.log (1 + w) - logPS M w).re = Real.log ‖1 + w‖ -
      ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * ρ ^ (i + 1) * Real.cos ((i + 1 : ℕ) * θ) /
        ((i : ℝ) + 1) := by
    rw [Complex.sub_re, hlogre, hps]
  rw [hre'] at hre
  rw [hlog2]
  have : 2 * Real.log ‖1 + w‖ - 2 * ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * ρ ^ (i + 1) *
      Real.cos ((i + 1 : ℕ) * θ) / ((i : ℝ) + 1) = 2 * (Real.log ‖1 + w‖ -
      ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * ρ ^ (i + 1) * Real.cos ((i + 1 : ℕ) * θ) /
        ((i : ℝ) + 1)) := by ring
  rw [this, abs_mul, abs_two]
  linarith


/-! ### The Chebyshev series of `log y`, `y = 11/20 + 9/20 u` -/

/-- `rho = (11 - sqrt 40)/9`, the root of `rho + 1/rho = 22/9` in `(0,1)`. -/
noncomputable def rho : ℝ := (11 - Real.sqrt 40) / 9

theorem sqrt40_lo : (63245 / 10000 : ℝ) ≤ Real.sqrt 40 := by
  have h := Real.sqrt_le_sqrt (show ((63245 : ℝ) / 10000) ^ 2 ≤ 40 by norm_num)
  rwa [Real.sqrt_sq (by norm_num)] at h

theorem sqrt40_hi : Real.sqrt 40 ≤ 63246 / 10000 := by
  have h := Real.sqrt_le_sqrt (show (40 : ℝ) ≤ ((63246 : ℝ) / 10000) ^ 2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num)] at h

theorem rho_lo : (11 - 63246 / 10000 : ℝ) / 9 ≤ rho := by
  unfold rho; linarith [sqrt40_hi]

theorem rho_hi : rho ≤ (11 - 63245 / 10000 : ℝ) / 9 := by
  unfold rho; linarith [sqrt40_lo]

theorem rho_pos : 0 < rho := lt_of_lt_of_le (by norm_num) rho_lo

theorem rho_lt_one : rho < 1 := lt_of_le_of_lt rho_hi (by norm_num)

/-- `X = (11 + sqrt 40)/40 = (9/20)/(2 rho)`. -/
noncomputable def logConst : ℝ := (11 + Real.sqrt 40) / 40

theorem logConst_pos : 0 < logConst := by unfold logConst; positivity

theorem y_eq (u : ℝ) : 11 / 20 + 9 / 20 * u = logConst * (1 + 2 * rho * u + rho ^ 2) := by
  have h40 : Real.sqrt 40 ^ 2 = 40 := Real.sq_sqrt (by norm_num)
  unfold logConst rho
  linear_combination (-((Real.sqrt 40 - 11) / 3240 - 2 * u / 360)) * h40

theorem basis_cos (θ : ℝ) (n : ℕ) : basis n (Real.cos θ) = Real.cos ((n : ℝ) * θ) := by
  unfold basis
  simp

theorem log_y_series {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (M : ℕ) :
    |Real.log (11 / 20 + 9 / 20 * u) - (Real.log logConst +
        2 * ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * rho ^ (i + 1) * basis (i + 1) u /
          ((i : ℝ) + 1))| ≤ 2 * (rho ^ (M + 1) / (((M : ℝ) + 1) * (1 - rho))) := by
  set θ := Real.arccos u with hθ
  have hc : Real.cos θ = u := Real.cos_arccos hu.1 hu.2
  have hser := log_cos_series rho_pos rho_lt_one θ M
  have hpos : 0 < 1 + 2 * rho * u + rho ^ 2 := by
    nlinarith [hu.1, rho_pos, rho_lt_one]
  have hl : Real.log (11 / 20 + 9 / 20 * u) =
      Real.log logConst + Real.log (1 + 2 * rho * Real.cos θ + rho ^ 2) := by
    rw [hc, y_eq, Real.log_mul logConst_pos.ne' hpos.ne']
  have hb : ∀ i : ℕ, basis (i + 1) u = Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
    intro i; rw [← hc]; exact basis_cos θ (i + 1)
  simp only [hb]
  rw [hl]
  convert hser using 2
  ring

/-! ### Rational logarithms and the tail of `log (1+z)` -/

/-- `sum_(i<n) x^(i+1)/(i+1)`. -/
def SQ (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℚ) + 1)

/-- Remainder bound `|x|^(n+1)/(1-|x|)`. -/
def epsQ (x : ℚ) (n : ℕ) : ℚ := |x| ^ (n + 1) / (1 - |x|)

theorem log_rat_close (r : ℚ) (hr : |1 - r| < 1) (n : ℕ) :
    |Real.log (r : ℝ) + (SQ (1 - r) n : ℝ)| ≤ (epsQ (1 - r) n : ℝ) := by
  have hx : |((1 - r : ℚ) : ℝ)| < 1 := by exact_mod_cast hr
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have e : (1 : ℝ) - ((1 - r : ℚ) : ℝ) = r := by push_cast; ring
  rw [e] at h
  simp only [SQ, epsQ]
  push_cast
  push_cast at h
  rwa [add_comm] at h

theorem log_z_lower {z s : ℝ} (hz : |z| ≤ s) (hs : s < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * z ^ (i + 1) / ((i : ℝ) + 1) - s ^ (n + 1) / (1 - s) ≤
      Real.log (1 + z) := by
  have hz1 : |-z| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hz1 n
  have e : (1 : ℝ) - -z = 1 + z := by ring
  rw [e, abs_neg] at h
  have hsum : ∑ i ∈ Finset.range n, (-z) ^ (i + 1) / ((i : ℝ) + 1) =
      -∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * z ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow, pow_succ]
    ring
  rw [hsum] at h
  have hb : |z| ^ (n + 1) / (1 - |z|) ≤ s ^ (n + 1) / (1 - s) := by
    have h0 : 0 ≤ |z| := abs_nonneg z
    have h1 : 0 < 1 - s := by linarith
    have hs0 : 0 ≤ s := h0.trans hz
    apply div_le_div₀ (pow_nonneg hs0 _) (pow_le_pow_left₀ h0 hz _) h1 (by linarith)
  have := (abs_le.mp h).1
  linarith


/-! ### Closed form of the positive reflection moments -/

/-- The primitive of `vY^k` in the `vY` coordinate: `x^(k-1)/(k-1) - x^(k+1)/(k+1)`, and
`log x - x^2/2` for `k = 1`. -/
noncomputable def momK (k : ℕ) (x : ℝ) : ℝ :=
  if k = 1 then MomentSource.H1 x else x ^ (k - 1) / ((k : ℝ) - 1) - x ^ (k + 1) / ((k : ℝ) + 1)

theorem momK_comp_hasDerivAt (m : ℕ) {Y : ℝ} (hY : 2 < Y) :
    HasDerivAt (fun y => momK (m + 2) (MomentSource.vY y)) (-(MomentSource.vY Y ^ (m + 2))) Y := by
  have hv := MomentSource.vY_pos hY.le
  have hs : 0 < Real.sqrt (Y ^ 2 - 4) := Real.sqrt_pos.2 (by nlinarith)
  have h := MomentSource.vY_hasDerivAt hY
  have h2 := ((h.pow (m + 1)).div_const ((m + 1 : ℕ) : ℝ)).sub
    ((h.pow (m + 3)).div_const ((m + 3 : ℕ) : ℝ))
  have hfun : (fun y => momK (m + 2) (MomentSource.vY y)) =
      fun y => MomentSource.vY y ^ (m + 1) / ((m + 1 : ℕ) : ℝ) -
        MomentSource.vY y ^ (m + 3) / ((m + 3 : ℕ) : ℝ) := by
    funext y
    unfold momK
    simp only [show m + 2 ≠ 1 by omega, ite_false, show m + 2 - 1 = m + 1 by omega]
    push_cast
    ring_nf
  rw [hfun]
  refine h2.congr_deriv ?_
  have q := MomentSource.vY_quad hY.le
  have e := MomentSource.vY_sqrt_eq hY.le
  set v := MomentSource.vY Y with hvdef
  set s := Real.sqrt (Y ^ 2 - 4) with hsdef
  have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hm3 : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have key : (-v / s) * (1 - v ^ 2) = -v ^ 2 := by
    field_simp
    nlinarith [e, q]
  simp only [Nat.add_sub_cancel]
  have e1 : m + 3 - 1 = m + 2 := by omega
  rw [e1]
  calc (((m + 1 : ℕ) : ℝ) * v ^ m * (-v / s)) / ((m + 1 : ℕ) : ℝ) -
        (((m + 3 : ℕ) : ℝ) * v ^ (m + 2) * (-v / s)) / ((m + 3 : ℕ) : ℝ)
      = v ^ m * ((-v / s) * (1 - v ^ 2)) := by
        field_simp
        ring
    _ = -v ^ (m + 2) := by rw [key]; ring

theorem integral_vY_pow (m : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ Y in a..b, MomentSource.vY Y ^ (m + 2) =
      momK (m + 2) (MomentSource.vY a) - momK (m + 2) (MomentSource.vY b) := by
  have hc : ContinuousOn (fun y => momK (m + 2) (MomentSource.vY y)) (Set.Icc a b) := by
    have : (fun y => momK (m + 2) (MomentSource.vY y)) =
        fun y => MomentSource.vY y ^ (m + 1) / ((m + 1 : ℕ) : ℝ) -
          MomentSource.vY y ^ (m + 3) / ((m + 3 : ℕ) : ℝ) := by
      funext y
      unfold momK
      simp only [show m + 2 ≠ 1 by omega, ite_false, show m + 2 - 1 = m + 1 by omega]
      push_cast
      ring_nf
    rw [this]
    exact (((MomentSource.vY_continuous.pow _).div_const _).sub
      ((MomentSource.vY_continuous.pow _).div_const _)).continuousOn
  have hd : ∀ y ∈ Set.Ioo a b, HasDerivAt (fun y => momK (m + 2) (MomentSource.vY y))
      (-(MomentSource.vY y ^ (m + 2))) y :=
    fun y hy => momK_comp_hasDerivAt m (lt_of_le_of_lt ha hy.1)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    ((MomentSource.vY_continuous.pow (m + 2)).neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at this
  linarith

theorem integral_vY_pow' {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ Y in a..b, MomentSource.vY Y ^ k = momK k (MomentSource.vY a) - momK k (MomentSource.vY b) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · have : k = 1 := by omega
    subst this
    simp only [pow_one, momK, ite_true]
    exact MomentSource.integral_vY ha hab
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    exact integral_vY_pow m ha hab

/-- **Closed form of the reflection moment**: a finite sum over the positive gas cells. -/
theorem reflMoment_closed (S : CapSource) (hS : S.Admissible) {k : ℕ} (hk : 1 ≤ k) :
    S.reflMoment k = ((S.gas Sign.pos).map fun c =>
      c.w / (c.hi - c.lo) * (momK k (MomentSource.vY c.lo) - momK k (MomentSource.vY c.hi))).sum := by
  unfold CapSource.reflMoment physL
  congr 1
  refine List.map_congr_left (fun c hc => ?_)
  rw [MomentSource.phys_pos (hS.gas_pos c hc)]
  rw [integral_vY_pow' hk (hS.gas_pos c hc) c.lo_lt.le]

/-! ### Pinned data-side tables and the rational constants -/

/-- Positive-species reflection moments `m_k`, `k = 0..32` (index 0 is a placeholder zero), rounded to `10^-9`. -/
def muL : List ℚ :=
  [0 / 1000000000, 386664019 / 1000000000, 279394267 / 1000000000, 221161955 / 1000000000,
   184444759 / 1000000000, 158947522 / 1000000000, 140057980 / 1000000000, 125410082 / 1000000000,
   113662144 / 1000000000, 103993796 / 1000000000, 95873359 / 1000000000, 88939983 / 1000000000,
   82939426 / 1000000000, 77686940 / 1000000000, 73044746 / 1000000000, 68907805 / 1000000000,
   65194497 / 1000000000, 61840348 / 1000000000, 58793682 / 1000000000, 56012547 / 1000000000,
   53462494 / 1000000000, 51114947 / 1000000000, 48945976 / 1000000000, 46935382 / 1000000000,
   45065978 / 1000000000, 43323043 / 1000000000, 41693886 / 1000000000, 40167501 / 1000000000,
   38734292 / 1000000000, 37385852 / 1000000000, 36114778 / 1000000000, 34914527 / 1000000000,
   33779290 / 1000000000]

/-- Aggregated radial coefficients `sum_e w_e coef_k r_e^k cos(k phi_e)`, `k = 0..32`, rounded to `10^-9`, for the design-C auxiliary table (`trial-uC`, GD5; regenerated by `work/tools/g0/g2b/alnew.py`). -/
def alL : List ℚ :=
  [0 / 1000000000, 136089552 / 1000000000, -15346621 / 1000000000, -3386344 / 1000000000,
   3249341 / 1000000000, -381524 / 1000000000, -901385 / 1000000000, 546275 / 1000000000,
   165859 / 1000000000, -357083 / 1000000000, 77024 / 1000000000, 175818 / 1000000000,
   -135101 / 1000000000, -46792 / 1000000000, 113001 / 1000000000, -22789 / 1000000000,
   -69783 / 1000000000, 52603 / 1000000000, 23850 / 1000000000, -50468 / 1000000000,
   6620 / 1000000000, 36326 / 1000000000, -24672 / 1000000000, -14942 / 1000000000,
   26424 / 1000000000, -965 / 1000000000, -21528 / 1000000000, 12744 / 1000000000,
   10196 / 1000000000, -15151 / 1000000000, -1065 / 1000000000, 13725 / 1000000000,
   -6937 / 1000000000]


/-- Terms of the `log y` series. -/
def nY : ℕ := 16
/-- Terms of the `log (1+z)` series. -/
def nZ : ℕ := 14
/-- Terms of the series for rational logarithms. -/
def nL : ℕ := 20

/-- Enclosure of `rho`. -/
def rLo : ℚ := (11 - 63246 / 10000) / 9
def rHi : ℚ := (11 - 63245 / 10000) / 9
/-- Enclosure of `X = (11 + sqrt 40)/40`. -/
def XLo : ℚ := (11 + 63245 / 10000) / 40
def XHi : ℚ := (11 + 63246 / 10000) / 40

def A0lo : ℚ := -SQ (1 - XLo) nL - epsQ (1 - XLo) nL
def A0hi : ℚ := -SQ (1 - XHi) nL + epsQ (1 - XHi) nL
/-- Centre and radius of the enclosure of `log X`. -/
def C0 : ℚ := (A0lo + A0hi) / 2
def eC0 : ℚ := (A0hi - A0lo) / 2

/-- Coefficient `Lambda_(i+1)` of `T_(i+1)`. -/
def lamQ (i : ℕ) : ℚ := (-1) ^ i * (rLo ^ (i + 1) + rHi ^ (i + 1)) / ((i : ℚ) + 1)
/-- Its error. -/
def lamErr (i : ℕ) : ℚ := (rHi ^ (i + 1) - rLo ^ (i + 1)) / ((i : ℚ) + 1)
def errLam : ℚ := ∑ i ∈ Finset.range nY, lamErr i
def tailY : ℚ := rHi ^ (nY + 1) / (((nY : ℚ) + 1) * (1 - rHi))

def logyL : List ℚ := C0 :: (List.range nY).map lamQ

def gzFun (i : ℕ) : ℚ := if i = 0 then 0 else (-1) ^ (i - 1) / (i : ℚ)
def gzL : List ℚ := (List.range (nZ + 1)).map gzFun
def sZ : ℚ := 279 / 521
def tailZ : ℚ := sZ ^ (nZ + 1) / (1 - sZ)

def Clog1 : ℚ := -SQ (1 - 521 / 400) nL
def eL1 : ℚ := epsQ (1 - 521 / 400) nL

/-- The coefficient of `y^k` in `-R900 + radial`, `k <= 32`, and `-kappa` at `k = 0`. -/
def betaFun (k : ℕ) : ℚ :=
  if k = 0 then -14762657 / 100000000 else alL.getD k 0 - muL.getD k 0 / (k : ℚ)
def betaL : List ℚ := (List.range 33).map betaFun

/-- The rational Chebyshev polynomial that the pinned `nearP` is compared with. -/
def gTilde : List ℚ :=
  addQ (addQ (smulQ (24 / 29) logyL) (smulQ (-53 / 58) (addQ [Clog1] (hornerZ gzL))))
    (hornerY betaL)

/-- All error terms not in `diffSum`. -/
def Etot : ℚ :=
  24 / 29 * (eC0 + errLam + 2 * tailY) + 53 / 58 * (eL1 + tailZ) + 7 / 1000 + 1 / 200 + 1 / 5000

theorem final_check : Etot + diffSum (D : ℚ) gTilde nearP ≤ nearEps := by
  -- kcost: about 1 s estimated (Horner over 33 and 15 steps on lists of at most 34 rationals,
  -- about 2500 rational operations with 100-bit numerators, one pass over 129 coefficients).
  decide +kernel

/-! ### Rational logarithm enclosures -/

theorem logConst_le_hi : Real.log logConst ≤ A0hi := by
  have hX : logConst ≤ (XHi : ℝ) := by
    unfold logConst XHi; push_cast; linarith [sqrt40_hi]
  have h1 := Real.log_le_log logConst_pos hX
  have hr : |1 - XHi| < 1 := by unfold XHi; rw [abs_lt]; constructor <;> norm_num
  have h2 := log_rat_close XHi hr nL
  have := (abs_le.mp h2).2
  unfold A0hi
  push_cast
  linarith

theorem logConst_ge_lo : (A0lo : ℝ) ≤ Real.log logConst := by
  have hX : (XLo : ℝ) ≤ logConst := by
    unfold logConst XLo; push_cast; linarith [sqrt40_lo]
  have hXp : (0 : ℝ) < XLo := by unfold XLo; norm_num
  have h1 := Real.log_le_log hXp hX
  have hr : |1 - XLo| < 1 := by unfold XLo; rw [abs_lt]; constructor <;> norm_num
  have h2 := log_rat_close XLo hr nL
  have := (abs_le.mp h2).1
  unfold A0lo
  push_cast
  linarith

theorem log_521_ge : (Clog1 : ℝ) - eL1 ≤ Real.log ((521 / 400 : ℚ) : ℝ) := by
  have hr : |1 - (521 / 400 : ℚ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h2 := log_rat_close (521 / 400) hr nL
  have := (abs_le.mp h2).1
  unfold Clog1 eL1
  push_cast at this ⊢
  linarith

/-! ### Series terms -/

theorem rawQ_range (g : ℕ → ℚ) (x : ℝ) : ∀ (n k : ℕ),
    rawQ ((List.range n).map g) k x = ∑ i ∈ Finset.range n, (g i : ℝ) * basis (k + i) x
  | 0, k => by simp [rawQ]
  | n + 1, k => by
    have ih := rawQ_range (fun i => g (i + 1)) x n (k + 1)
    rw [List.range_succ_eq_map, List.map_cons, rawQ, List.map_map]
    simp only [Function.comp_def] at ih ⊢
    rw [ih, Finset.sum_range_succ' _ n]
    have e : ∀ i, k + 1 + i = k + (i + 1) := fun i => by omega
    simp only [e, add_zero]
    ring

theorem lam_term_le {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (i : ℕ) :
    2 * ((-1 : ℝ) ^ i * rho ^ (i + 1) * basis (i + 1) u / ((i : ℝ) + 1)) ≤
      (lamQ i : ℝ) * basis (i + 1) u + (lamErr i : ℝ) := by
  have hb := abs_basis_le_one (i + 1) hu
  have hk : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hlo : (rLo : ℝ) ^ (i + 1) ≤ rho ^ (i + 1) := by
    apply pow_le_pow_left₀ (by unfold rLo; push_cast; norm_num)
    unfold rLo; push_cast; exact rho_lo
  have hhi : rho ^ (i + 1) ≤ (rHi : ℝ) ^ (i + 1) := by
    apply pow_le_pow_left₀ rho_pos.le
    unfold rHi; push_cast; exact rho_hi
  set b := basis (i + 1) u with hbdef
  have hd : |2 * rho ^ (i + 1) - ((rLo : ℝ) ^ (i + 1) + (rHi : ℝ) ^ (i + 1))| ≤
      (rHi : ℝ) ^ (i + 1) - (rLo : ℝ) ^ (i + 1) := by
    rw [abs_le]; constructor <;> linarith
  have e : 2 * ((-1 : ℝ) ^ i * rho ^ (i + 1) * b / ((i : ℝ) + 1)) - (lamQ i : ℝ) * b =
      (-1 : ℝ) ^ i * (2 * rho ^ (i + 1) - ((rLo : ℝ) ^ (i + 1) + (rHi : ℝ) ^ (i + 1))) * b /
        ((i : ℝ) + 1) := by
    unfold lamQ; push_cast; ring
  have hle : (-1 : ℝ) ^ i * (2 * rho ^ (i + 1) - ((rLo : ℝ) ^ (i + 1) + (rHi : ℝ) ^ (i + 1))) * b /
        ((i : ℝ) + 1) ≤ (lamErr i : ℝ) := by
    rw [div_le_iff₀ hk]
    have h1 : |(-1 : ℝ) ^ i * (2 * rho ^ (i + 1) - ((rLo : ℝ) ^ (i + 1) + (rHi : ℝ) ^ (i + 1))) *
        b| ≤ (rHi : ℝ) ^ (i + 1) - (rLo : ℝ) ^ (i + 1) := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      calc _ ≤ |2 * rho ^ (i + 1) - ((rLo : ℝ) ^ (i + 1) + (rHi : ℝ) ^ (i + 1))| * 1 :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ ≤ _ := by linarith
    have h2 := (abs_le.mp h1).2
    unfold lamErr; push_cast
    have : ((rHi : ℝ) ^ (i + 1) - (rLo : ℝ) ^ (i + 1)) / ((i : ℝ) + 1) * ((i : ℝ) + 1) =
        (rHi : ℝ) ^ (i + 1) - (rLo : ℝ) ^ (i + 1) := by field_simp
    linarith
  linarith

theorem tail_mono (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ rHi) :
    r ^ (n + 1) / (((n : ℝ) + 1) * (1 - r)) ≤ (rHi : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (1 - rHi)) := by
  have hh : (rHi : ℝ) < 1 := by unfold rHi; push_cast; norm_num
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply div_le_div₀ (pow_nonneg (by unfold rHi; push_cast; norm_num) _)
    (pow_le_pow_left₀ hr0.le hr _) (by
    apply mul_pos hn; linarith) (by
    apply mul_le_mul_of_nonneg_left _ hn.le; linarith)

/-- The Chebyshev-side upper bound for `log y`. -/
theorem log_y_le {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    Real.log (11 / 20 + 9 / 20 * u) ≤ (C0 : ℝ) + (eC0 : ℝ) +
      ∑ i ∈ Finset.range nY, (lamQ i : ℝ) * basis (i + 1) u + errLam + 2 * (tailY : ℝ) := by
  have h := log_y_series hu nY
  have h1 := (abs_le.mp h).2
  have h2 := logConst_le_hi
  have h3 := logConst_ge_lo
  have hsum : 2 * ∑ i ∈ Finset.range nY, (-1 : ℝ) ^ i * rho ^ (i + 1) * basis (i + 1) u /
      ((i : ℝ) + 1) ≤ ∑ i ∈ Finset.range nY, (lamQ i : ℝ) * basis (i + 1) u + errLam := by
    rw [Finset.mul_sum]
    have : (errLam : ℝ) = ∑ i ∈ Finset.range nY, (lamErr i : ℝ) := by
      unfold errLam; push_cast; rfl
    rw [this, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => lam_term_le hu i)
  have ht := tail_mono nY rho_pos (by unfold rHi; push_cast; exact rho_hi)
  have hC : (A0hi : ℝ) = (C0 : ℝ) + (eC0 : ℝ) := by unfold C0 eC0; push_cast; ring
  unfold tailY
  push_cast
  linarith

/-! ### The source side -/

/-- Aggregated radial coefficient of `y^k` in the positive-species near field. -/
noncomputable def radCoef (S : CapSource) (k : ℕ) : ℝ :=
  ((S.aux Sign.pos).map fun e =>
    e.w * (S.coef k * S.rad e.rad ^ k * Real.cos ((k : ℝ) * e.phase))).sum

theorem list_sum_comm {α : Type*} (l : List α) (s : Finset ℕ) (g : α → ℕ → ℝ) :
    (l.map fun a => ∑ k ∈ s, g a k).sum = ∑ k ∈ s, (l.map fun a => g a k).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih, Finset.sum_add_distrib]

theorem near_unfold (S : CapSource) (y : ℝ) :
    S.nearField (Trunc.finite 384) y = 48 / 58 * Real.log y - 53 / 58 * Real.log (1 + y ^ 2) -
      kappa Sign.pos - S.reflPoly y + ∑ k ∈ Finset.range 384, radCoef S (k + 1) * y ^ (k + 1) +
      S.auxTail (Trunc.finite 384) Sign.pos := by
  have key : ((S.aux Sign.pos).map fun e => e.w * ∑ k ∈ Finset.range 384,
      S.coef (k + 1) * (S.rad e.rad * y) ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)).sum =
      ∑ k ∈ Finset.range 384, radCoef S (k + 1) * y ^ (k + 1) := by
    simp_rw [Finset.mul_sum]
    rw [list_sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold radCoef
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left (fun e _ => ?_)
    rw [mul_pow]
    ring
  unfold CapSource.nearField
  simp only [Trunc.sum]
  rw [key]

theorem reflPoly_ge (S : CapSource) (hS : S.Admissible) (hdeg : 31 ≤ S.reflDeg) {y : ℝ}
    (hy : 0 ≤ y) :
    ∑ k ∈ Finset.range 32, S.reflMoment (k + 1) * y ^ (k + 1) / ((k : ℝ) + 1) ≤
      S.reflPoly y := by
  unfold CapSource.reflPoly
  rw [show S.reflDeg + 1 = 32 + (S.reflDeg + 1 - 32) by omega, Finset.sum_range_add]
  have : 0 ≤ ∑ k ∈ Finset.range (S.reflDeg + 1 - 32), S.reflMoment (32 + k + 1) * y ^ (32 + k + 1) /
      (((32 + k : ℕ) : ℝ) + 1) := by
    refine Finset.sum_nonneg (fun k _ => ?_)
    have := CompactSource.reflMoment_nonneg S hS (32 + k + 1)
    positivity
  push_cast at this ⊢
  linarith

/-- Data-side hypotheses: moments, aggregated radial coefficients, radial tail. -/
structure NearData (S : CapSource) : Prop where
  moment : ∀ k, 1 ≤ k → k ≤ 32 → |S.reflMoment k - (muL.getD k 0 : ℚ)| ≤ 1 / 10000
  radial : ∀ k, 1 ≤ k → k ≤ 32 → |radCoef S k - (alL.getD k 0 : ℚ)| ≤ 1 / 10000
  tail : ∑ i ∈ Finset.range 352, |radCoef S (32 + i + 1)| ≤ 1 / 200

theorem poly_part (S : CapSource) (hS : S.Admissible) (hdeg : 31 ≤ S.reflDeg) (hd : NearData S)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -S.reflPoly y + ∑ k ∈ Finset.range 384, radCoef S (k + 1) * y ^ (k + 1) ≤
      polyR betaL y - (betaFun 0 : ℝ) + 7 / 1000 + 1 / 200 := by
  have h1 := reflPoly_ge S hS hdeg hy0
  rw [show (384 : ℕ) = 32 + 352 from rfl, Finset.sum_range_add]
  have htail : ∑ i ∈ Finset.range 352, radCoef S (32 + i + 1) * y ^ (32 + i + 1) ≤ 1 / 200 := by
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hd.tail
    have hp : y ^ (32 + i + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hp0 : 0 ≤ y ^ (32 + i + 1) := pow_nonneg hy0 _
    calc radCoef S (32 + i + 1) * y ^ (32 + i + 1) ≤ |radCoef S (32 + i + 1) * y ^ (32 + i + 1)| :=
          le_abs_self _
      _ = |radCoef S (32 + i + 1)| * y ^ (32 + i + 1) := by rw [abs_mul, abs_of_nonneg hp0]
      _ ≤ |radCoef S (32 + i + 1)| := mul_le_of_le_one_right (abs_nonneg _) hp
  have hpoly : polyR betaL y = (betaFun 0 : ℝ) + ∑ k ∈ Finset.range 32, (betaFun (k + 1) : ℝ) * y ^ (k + 1) := by
    unfold betaL
    rw [polyR_range betaFun y 33, Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    ring
  have hterm : ∀ k ∈ Finset.range 32,
      radCoef S (k + 1) * y ^ (k + 1) - S.reflMoment (k + 1) * y ^ (k + 1) / ((k : ℝ) + 1) ≤
        (betaFun (k + 1) : ℝ) * y ^ (k + 1) + 2 / 10000 := by
    intro k hk
    have hk32 : k + 1 ≤ 32 := by simpa using hk
    have hm := hd.moment (k + 1) (by omega) hk32
    have hr := hd.radial (k + 1) (by omega) hk32
    have hp : y ^ (k + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hp0 : 0 ≤ y ^ (k + 1) := pow_nonneg hy0 _
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hb : (betaFun (k + 1) : ℝ) = (alL.getD (k + 1) 0 : ℚ) - (muL.getD (k + 1) 0 : ℚ) / ((k : ℝ) + 1) := by
      have hne : k + 1 ≠ 0 := by omega
      simp only [betaFun, hne, ite_false]
      push_cast; ring
    have hm' : |S.reflMoment (k + 1) / ((k : ℝ) + 1) - (muL.getD (k + 1) 0 : ℚ) / ((k : ℝ) + 1)| ≤ 1 / 10000 := by
      rw [← sub_div, abs_div, abs_of_pos hk0, div_le_iff₀ hk0]
      have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      nlinarith [abs_nonneg (S.reflMoment (k + 1) - (muL.getD (k + 1) 0 : ℚ))]
    have hdiff : (radCoef S (k + 1) - S.reflMoment (k + 1) / ((k : ℝ) + 1)) - (betaFun (k + 1) : ℝ) ≤ 2 / 10000 := by
      rw [hb]
      have a1 := (abs_le.mp hr).2
      have a2 := (abs_le.mp hm').1
      linarith
    have : radCoef S (k + 1) * y ^ (k + 1) - S.reflMoment (k + 1) * y ^ (k + 1) / ((k : ℝ) + 1) -
        (betaFun (k + 1) : ℝ) * y ^ (k + 1) =
        ((radCoef S (k + 1) - S.reflMoment (k + 1) / ((k : ℝ) + 1)) - (betaFun (k + 1) : ℝ)) * y ^ (k + 1) := by
      ring
    have h5 : ((radCoef S (k + 1) - S.reflMoment (k + 1) / ((k : ℝ) + 1)) - (betaFun (k + 1) : ℝ)) * y ^ (k + 1) ≤ 2 / 10000 := by
      calc _ ≤ (2 / 10000 : ℝ) * y ^ (k + 1) := mul_le_mul_of_nonneg_right hdiff hp0
        _ ≤ 2 / 10000 := mul_le_of_le_one_right (by norm_num) hp
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have e : ∑ k ∈ Finset.range 32, S.reflMoment (k + 1) * y ^ (k + 1) / ((k : ℝ) + 1) =
      ∑ k ∈ Finset.range 32, S.reflMoment (k + 1) * y ^ (k + 1) / ((k : ℝ) + 1) := rfl
  push_cast at hsum
  linarith

/-! ### The Near hf -/

theorem auxTail_small (S : CapSource) (hS : S.Admissible)
    (hε1 : 1 / 10 ≤ S.eps) (hε2 : S.eps ≤ 3 / 20)
    (hmass : 63 / 100 ≤ massL (S.gas Sign.pos)) :
    S.auxTail (Trunc.finite 384) Sign.pos ≤ 1 / 5000 := by
  have hs0 := CompactSource.strength_nonneg S hS
  have hc0 := CompactSource.curvature_nonneg S hS
  obtain ⟨hs, hc⟩ := CompactInstance.strength_curvature_le S hS.eps_pos hε2
  have hM : S.auxMass Sign.pos ≤ 37 / 100 := by rw [hS.aux_pos_mass]; linarith
  have hM0 : 0 ≤ S.auxMass Sign.pos := by
    unfold CapSource.auxMass
    exact List.sum_nonneg (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact e.w_nonneg)
  have hq := CompactInstance.q_le S hε1
  have hq0 := CompactInstance.q_pos S
  set q := S.q with hqdef
  have hg0 : 0 < 1 - q := by linarith
  have hg : 1 / (1 - q) ≤ 25 := by
    rw [div_le_iff₀ hg0]; linarith
  have hg1 : 0 ≤ 1 / (1 - q) := by positivity
  have hpow : q ^ (384 + 1) ≤ (24 / 25) ^ 385 := pow_le_pow_left₀ hq0.le hq _
  have hpow' : ((24 : ℝ) / 25) ^ 385 ≤ (1 / 4) ^ 11 := by
    have h35 : ((24 : ℝ) / 25) ^ 35 ≤ 1 / 4 := by norm_num
    have h11 : (((24 : ℝ) / 25) ^ 35) ^ 11 ≤ (1 / 4) ^ 11 :=
      pow_le_pow_left₀ (by positivity) h35 11
    have e : ((24 : ℝ) / 25) ^ 385 = (((24 : ℝ) / 25) ^ 35) ^ 11 := by rw [← pow_mul]
    rw [e]
    exact h11
  have hne : ¬ (Sign.pos = Sign.neg) := by decide
  unfold CapSource.auxTail
  simp only [hne, ite_false, mul_one]
  push_cast
  have hB : ((1 / ((384 : ℝ) + 1) + S.strength) * (1 / (1 - q)) +
      S.curvature * (((384 : ℝ) + 1) * (1 / (1 - q)) + q * (1 / (1 - q)) ^ 2)) ≤ 2000 := by
    have e1 : (1 / ((384 : ℝ) + 1) + S.strength) * (1 / (1 - q)) ≤ (1 / 385 + 1 / 10) * 25 := by
      apply mul_le_mul _ hg hg1 (by norm_num)
      norm_num; linarith
    have e2 : S.curvature * (((384 : ℝ) + 1) * (1 / (1 - q)) + q * (1 / (1 - q)) ^ 2) ≤
        1 / 10 * (385 * 25 + 1 * 25 ^ 2) := by
      apply mul_le_mul hc _ (by positivity) (by norm_num)
      have a1 : (385 : ℝ) * (1 / (1 - q)) ≤ 385 * 25 := by linarith
      have a2 : q * (1 / (1 - q)) ^ 2 ≤ 1 * 25 ^ 2 := by
        apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
        exact pow_le_pow_left₀ hg1 hg 2
      linarith
    linarith
  have hB0 : 0 ≤ ((1 / ((384 : ℝ) + 1) + S.strength) * (1 / (1 - q)) +
      S.curvature * (((384 : ℝ) + 1) * (1 / (1 - q)) + q * (1 / (1 - q)) ^ 2)) := by positivity
  calc q ^ (384 + 1) * ((1 / ((384 : ℝ) + 1) + S.strength) * (1 / (1 - q)) +
        S.curvature * (((384 : ℝ) + 1) * (1 / (1 - q)) + q * (1 / (1 - q)) ^ 2)) *
        S.auxMass Sign.pos
      ≤ (1 / 4) ^ 11 * 2000 * (37 / 100) := by
        apply mul_le_mul (mul_le_mul (hpow.trans hpow') hB hB0 (by norm_num)) hM hM0
          (by norm_num)
    _ ≤ 1 / 5000 := by norm_num

/-- `z`-part: lower bound of `log (1 + y^2)`. -/
theorem log_sq_ge {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (Clog1 : ℝ) - eL1 + polyR gzL ((198 * u + 81 * u ^ 2) / 521) - tailZ ≤
      Real.log (1 + (11 / 20 + 9 / 20 * u) ^ 2) := by
  have hz : |(198 * u + 81 * u ^ 2) / 521| ≤ (sZ : ℝ) := by
    unfold sZ
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 521), div_le_iff₀ (by norm_num)]
    have h1 : |198 * u + 81 * u ^ 2| ≤ 198 * |u| + 81 * |u| ^ 2 := by
      calc _ ≤ |198 * u| + |81 * u ^ 2| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_pow]; norm_num
    have h2 : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
    push_cast
    nlinarith [abs_nonneg u]
  have hs1 : (sZ : ℝ) < 1 := by unfold sZ; norm_num
  have hl := log_z_lower hz hs1 nZ
  have hpoly : polyR gzL ((198 * u + 81 * u ^ 2) / 521) =
      ∑ i ∈ Finset.range nZ, (-1 : ℝ) ^ i * ((198 * u + 81 * u ^ 2) / 521) ^ (i + 1) /
        ((i : ℝ) + 1) := by
    unfold gzL
    rw [polyR_range gzFun _ (nZ + 1), Finset.sum_range_succ']
    simp only [gzFun, pow_zero, mul_one, ite_true, Rat.cast_zero, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    push_cast
    ring
  have hid : 1 + (11 / 20 + 9 / 20 * u) ^ 2 =
      ((521 / 400 : ℚ) : ℝ) * (1 + (198 * u + 81 * u ^ 2) / 521) := by
    push_cast; ring
  have hzpos : 0 < 1 + (198 * u + 81 * u ^ 2) / 521 := by
    have := (abs_le.mp hz).1
    have hs : (sZ : ℝ) < 1 := hs1
    linarith
  rw [hid, Real.log_mul (by norm_num) hzpos.ne']
  have h5 := log_521_ge
  rw [← hpoly] at hl
  unfold tailZ
  push_cast at hl ⊢
  linarith

/-- Chebyshev evaluation of the rational polynomial `gTilde`. -/
theorem rawQ_gTilde (x : ℝ) :
    rawQ gTilde 0 x = 24 / 29 * ((C0 : ℝ) + ∑ i ∈ Finset.range nY, (lamQ i : ℝ) * basis (i + 1) x) +
      (-53 / 58) * ((Clog1 : ℝ) + polyR gzL ((198 * x + 81 * x ^ 2) / 521)) +
      polyR betaL (11 / 20 + 9 / 20 * x) := by
  unfold gTilde
  simp only [rawQ_addQ, rawQ_smulQ, rawQ_single, rawQ_hornerZ, rawQ_hornerY]
  unfold logyL
  rw [rawQ, rawQ_range]
  simp only [basis_zero, mul_one]
  have e : ∀ i, 1 + i = i + 1 := fun i => by omega
  simp only [e]
  push_cast
  ring

theorem near_pointwise (S : CapSource) (hS : S.Admissible) (hdeg : 31 ≤ S.reflDeg)
    (hκ : kappa Sign.pos = 14762657 / 100000000) (hd : NearData S)
    (haux : S.auxTail (Trunc.finite 384) Sign.pos ≤ 1 / 5000)
    {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    S.nearField (Trunc.finite 384) (11 / 20 + 9 / 20 * u) ≤ rawQ gTilde 0 u + (Etot : ℝ) := by
  have hy0 : 0 ≤ 11 / 20 + 9 / 20 * u := by linarith [hu.1]
  have hy1 : 11 / 20 + 9 / 20 * u ≤ 1 := by linarith [hu.2]
  rw [near_unfold, hκ]
  have hp := poly_part S hS hdeg hd hy0 hy1
  have hly := log_y_le hu
  have hlq := log_sq_ge hu
  rw [rawQ_gTilde]
  have hb0 : (betaFun 0 : ℝ) = -14762657 / 100000000 := by unfold betaFun; simp
  rw [hb0] at hp
  unfold Etot
  push_cast
  nlinarith [hp, hly, hlq, haux]

/-- **`NearHf`**: the source Near field is below the pinned degree-128 majorant plus its tail,
from the data-side facts `NearData` and the seed bounds. -/
theorem nearHf (S : CapSource) (hS : S.Admissible) (hdeg : 31 ≤ S.reflDeg)
    (hκ : kappa Sign.pos = 14762657 / 100000000) (hd : NearData S)
    (hε1 : 1 / 10 ≤ S.eps) (hε2 : S.eps ≤ 3 / 20)
    (hmass : 63 / 100 ≤ massL (S.gas Sign.pos)) :
    CompactInstance.NearHf S (Trunc.finite 384) := by
  intro y hy
  have haux := auxTail_small S hS hε1 hε2 hmass
  have hu : CompactCap.affine (1 / 10) y ∈ Icc (-1 : ℝ) 1 :=
    CompactCap.affine_mem (by norm_num) hy.1 hy.2
  set u := CompactCap.affine (1 / 10) y with hudef
  have hyu : y = 11 / 20 + 9 / 20 * u := by
    rw [hudef]; unfold CompactCap.affine; field_simp; ring
  have h1 := near_pointwise S hS hdeg hκ hd haux hu
  rw [← hyu] at h1
  have h2 := abs_rawQ_sub_le D gTilde nearP 0 u hu
  have h3 := final_check
  have h4 : ((Etot + diffSum (D : ℚ) gTilde nearP : ℚ) : ℝ) ≤ (nearEps : ℝ) := by exact_mod_cast h3
  push_cast at h4
  have hcs : chebSum nearP D u = rawSum nearP 0 u / (D : ℝ) := rfl
  rw [hcs]
  have := (abs_le.mp h2).2
  linarith

/-- Data-side hypotheses with the moments stated by the closed form (a finite sum over the
positive gas cells, evaluated at `vY` of the cell endpoints). -/
structure NearDataClosed (S : CapSource) : Prop where
  moment : ∀ k, 1 ≤ k → k ≤ 32 →
    |((S.gas Sign.pos).map fun c => c.w / (c.hi - c.lo) *
        (momK k (MomentSource.vY c.lo) - momK k (MomentSource.vY c.hi))).sum -
      (muL.getD k 0 : ℚ)| ≤ 1 / 10000
  radial : ∀ k, 1 ≤ k → k ≤ 32 → |radCoef S k - (alL.getD k 0 : ℚ)| ≤ 1 / 10000
  tail : ∑ i ∈ Finset.range 352, |radCoef S (32 + i + 1)| ≤ 1 / 200

theorem NearDataClosed.toNearData {S : CapSource} (hS : S.Admissible) (h : NearDataClosed S) :
    NearData S where
  moment k hk1 hk2 := by rw [reflMoment_closed S hS hk1]; exact h.moment k hk1 hk2
  radial := h.radial
  tail := h.tail

/-- `NearHf` from the closed-form data-side facts. -/
theorem nearHf_closed (S : CapSource) (hS : S.Admissible) (hdeg : 31 ≤ S.reflDeg)
    (hκ : kappa Sign.pos = 14762657 / 100000000) (hd : NearDataClosed S)
    (hε1 : 1 / 10 ≤ S.eps) (hε2 : S.eps ≤ 3 / 20)
    (hmass : 63 / 100 ≤ massL (S.gas Sign.pos)) :
    CompactInstance.NearHf S (Trunc.finite 384) :=
  nearHf S hS hdeg hκ (hd.toNearData hS) hε1 hε2 hmass

end CatalanMeasure.GenD.Signed.RouteI.CompactHf

#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactHf.final_check
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactHf.reflMoment_closed
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactHf.nearHf
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompactHf.nearHf_closed
