module

public import CatalanCore.Zeta5.Potential.LogKernel
public import CatalanCore.Zeta5.Potential.Measure

/-!
# Z5-POTENTIAL, part 4: closed forms of the potential and energy (ZD12, ZD13, ZD14)

With `U(t) = ∫ log |t - u| dν(u)`, `x = 2t/b - 1`:
* `t ∈ [0, b]`: `U = c_0 log(b/4) - Σ_{k ≥ 1} c_k T_k(x)/k`
  (`logPot_nu_inside`; angle form `t = b cos² φ`: `logPot_nu_inside_cos`);
* `t = b(1+r)²/(4r)`, `r ∈ (0,1)`: `U = c_0 (log(b/4) - log r) - Σ_{k ≥ 1} c_k r^k/k`
  (`logPot_nu_outside`; `r = e^{-w}`, `t = (b/2)(1 + cosh w)`: `logPot_nu_cosh`);
* `∫ T_k(2t/b - 1) dν = c_k/2`, `ν(ℝ) = c_0` (`nu_real_univ`), and
  `∫ U dν = c_0² log(b/4) - Σ_{k ≥ 1} c_k²/(2k)` (`energy_nu`).
All hypotheses are `0 ≤ f` on `[-1, 1]` (supplied by the sum of squares of `SOS`).
-/

@[expose] public section

open MeasureTheory Set Polynomial CatalanMeasure.Signed OAI.InternalCatalan

namespace CatalanCore.Zeta5.Potential

noncomputable section

/-! ### The logarithmic potential of `ν` -/

/-- The logarithmic potential `U_μ(t) = ∫ log |t - u| dμ(u)`. -/
def logPot (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ u, Real.log |t - u| ∂μ

theorem measurable_log_abs_sub (t : ℝ) : Measurable fun u : ℝ => Real.log |t - u| :=
  Real.measurable_log.comp (Continuous.measurable (by fun_prop : Continuous fun u : ℝ => |t - u|))

/-- Reduction of the potential at `t = (b/2)(1+x)` to the angle integral of `log |x - cos θ|`. -/
theorem logPot_nu_of_integral {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {x : ℝ}
    (hae : ∀ᵐ θ ∂arc, Real.cos θ ≠ x)
    (hint : Integrable (fun θ => chebF c N (Real.cos θ) * Real.log |x - Real.cos θ|) arc) :
    logPot (nu c N b) (b / 2 * (1 + x)) =
      Real.log (b / 2) * c 0 + ∫ θ, chebF c N (Real.cos θ) * Real.log |x - Real.cos θ| ∂arc := by
  unfold logPot
  rw [integral_nu hpos (measurable_log_abs_sub _)]
  have hq : ∀ᵐ θ ∂arc, chebF c N (Real.cos θ) * Real.log |b / 2 * (1 + x) - tmap b θ| =
      Real.log (b / 2) * chebF c N (Real.cos θ) +
        chebF c N (Real.cos θ) * Real.log |x - Real.cos θ| := by
    filter_upwards [hae] with θ hθ
    have h1 : b / 2 * (1 + x) - tmap b θ = b / 2 * (x - Real.cos θ) := by unfold tmap; ring
    have h2 : x - Real.cos θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
    rw [h1, abs_mul, abs_of_pos (by linarith : 0 < b / 2),
      Real.log_mul (by linarith) (abs_ne_zero.mpr h2)]
    ring
  rw [integral_congr_ae hq, integral_add ((integrable_chebF c N).const_mul _) hint,
    integral_const_mul, integral_chebF]

/-- **ZD13, inside the support.**  For `t ∈ [0, b]`, `x = 2t/b - 1`:
`U_ν(t) = c_0 log(b/4) - Σ_{k=1}^N c_k T_k(x)/k`. -/
theorem logPot_nu_inside {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) :
    logPot (nu c N b) t = c 0 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
      c (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (2 * t / b - 1) / ((k + 1 : ℕ) : ℝ) := by
  set x : ℝ := 2 * t / b - 1 with hxdef
  have hx : x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · rw [hxdef, le_sub_iff_add_le, neg_add_cancel]
      exact div_nonneg (by linarith [ht.1]) hb.le
    · rw [hxdef, sub_le_iff_le_add, div_le_iff₀ hb]; nlinarith [ht.2]
  have ht' : t = b / 2 * (1 + x) := by rw [hxdef]; field_simp; ring
  obtain ⟨hint, hval⟩ := integral_chebF_log_inside c N hx
  rw [ht', logPot_nu_of_integral hb hpos (ae_cos_ne x hx) hint, hval]
  have : Real.log (b / 4) = Real.log (b / 2) - Real.log 2 := by
    rw [← Real.log_div (by linarith) (by norm_num)]; congr 1; ring
  rw [this]
  have e : ∀ k : ℕ, c (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) =
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) / ((k + 1 : ℕ) : ℝ) := fun k => by ring
  simp_rw [e]
  ring

/-- **ZD13, outside the support (the cosh branch).**  For `r ∈ (0, 1)` and
`t = b (1 + r)² / (4 r) ≥ b` (that is `t = (b/2)(1 + cosh w)`, `r = e^{-w}`):
`U_ν(t) = c_0 (log(b/4) - log r) - Σ_{k=1}^N c_k r^k / k`. -/
theorem logPot_nu_outside {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    logPot (nu c N b) (b * (1 + r) ^ 2 / (4 * r)) =
      c 0 * (Real.log (b / 4) - Real.log r) - ∑ k ∈ Finset.range N,
        c (k + 1) * r ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  have hr0 : r ≠ 0 := hr.1.ne'
  set x : ℝ := (1 + r ^ 2) / (2 * r) with hxdef
  have hm : 1 < x := by
    have : x - 1 = (1 - r) ^ 2 / (2 * r) := by rw [hxdef]; field_simp; ring
    have : 0 < (1 - r) ^ 2 / (2 * r) := div_pos (by nlinarith [hr.2]) (by linarith [hr.1])
    linarith
  have ht' : b * (1 + r) ^ 2 / (4 * r) = b / 2 * (1 + x) := by rw [hxdef]; field_simp; ring
  have hae : ∀ᵐ θ ∂arc, Real.cos θ ≠ x := ae_of_all _ fun θ => by
    have := Real.cos_le_one θ; intro h; linarith
  have habs : ∀ θ, |x - Real.cos θ| = x - Real.cos θ := fun θ =>
    abs_of_pos (by linarith [Real.cos_le_one θ])
  have hint : Integrable (fun θ => chebF c N (Real.cos θ) * Real.log |x - Real.cos θ|) arc := by
    simp_rw [habs]; exact integrable_chebF_log_outside c N hr
  rw [ht', logPot_nu_of_integral hb hpos hae hint]
  simp_rw [habs]
  rw [integral_chebF_log_outside c N hr]
  have : Real.log (b / 4) = Real.log (b / 2) - Real.log 2 := by
    rw [← Real.log_div (by linarith) (by norm_num)]; congr 1; ring
  have h2r : Real.log (2 * r) = Real.log 2 + Real.log r := Real.log_mul (by norm_num) hr0
  rw [this, h2r]
  have e : ∀ k : ℕ, c (k + 1) * r ^ (k + 1) / ((k + 1 : ℕ) : ℝ) =
      r ^ (k + 1) * c (k + 1) / ((k + 1 : ℕ) : ℝ) := fun k => by ring
  simp_rw [e]
  ring


/-- **ZD13 in the angle form** `t = b cos² φ`, `φ ∈ ℝ`:
`U_ν(t) = c_0 log(b/4) - Σ_{k=1}^N c_k cos(2kφ)/k`. -/
theorem logPot_nu_inside_cos {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (φ : ℝ) :
    logPot (nu c N b) (b * Real.cos φ ^ 2) = c 0 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
      c (k + 1) * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ) / ((k + 1 : ℕ) : ℝ) := by
  have ht : b * Real.cos φ ^ 2 ∈ Icc (0 : ℝ) b :=
    ⟨by positivity, by nlinarith [Real.sin_sq_add_cos_sq φ, sq_nonneg (Real.sin φ)]⟩
  rw [logPot_nu_inside hb hpos ht]
  have hx : 2 * (b * Real.cos φ ^ 2) / b - 1 = Real.cos (2 * φ) := by
    rw [Real.cos_two_mul]; field_simp
  rw [hx]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [Chebyshev.T_real_cos]
  congr 3
  push_cast; ring

/-- **ZD13, the cosh branch in `w`**: `t = (b/2)(1 + cosh w)`, `w > 0`:
`U_ν(t) = c_0 (log(b/4) + w) - Σ_{k=1}^N c_k e^{-kw}/k`. -/
theorem logPot_nu_cosh {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {w : ℝ} (hw : 0 < w) :
    logPot (nu c N b) (b / 2 * (1 + Real.cosh w)) =
      c 0 * (Real.log (b / 4) + w) - ∑ k ∈ Finset.range N,
        c (k + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * w)) / ((k + 1 : ℕ) : ℝ) := by
  have hr : Real.exp (-w) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  have h := logPot_nu_outside hb hpos hr
  have e1 : b * (1 + Real.exp (-w)) ^ 2 / (4 * Real.exp (-w)) = b / 2 * (1 + Real.cosh w) := by
    rw [Real.cosh_eq, Real.exp_neg]
    have : Real.exp w ≠ 0 := (Real.exp_pos w).ne'
    field_simp
    ring
  rw [e1] at h
  rw [h, Real.log_exp]
  have e2 : ∀ k : ℕ, Real.exp (-w) ^ (k + 1) = Real.exp (-(((k + 1 : ℕ) : ℝ) * w)) := by
    intro k
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp_rw [e2]
  ring

/-! ### Moments and the energy -/

theorem tmap_affine {b : ℝ} (hb : b ≠ 0) (θ : ℝ) : 2 * tmap b θ / b - 1 = Real.cos θ := by
  unfold tmap; field_simp; ring

/-- **ZD14, moments**: `∫ T_k(2t/b - 1) dν = c_k/2` for `1 ≤ k ≤ N` (and `c_0` for `k = 0`,
`0` for `k > N`). -/
theorem integral_nu_T {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (k : ℕ) :
    ∫ t, (Chebyshev.T ℝ (k : ℤ)).eval (2 * t / b - 1) ∂(nu c N b) =
      if k ≤ N then c k * (if k = 0 then 1 else 1 / 2) else 0 := by
  rw [integral_nu hpos (Continuous.measurable (by
    exact (Polynomial.continuous _).comp (by fun_prop)))]
  simp_rw [tmap_affine hb.ne']
  exact integral_chebF_mul_T c N k

/-- The potential of `ν` is bounded below/above on the mass: `ν` is a finite measure. -/
theorem isFiniteMeasure_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) : IsFiniteMeasure (nu c N b) :=
  ⟨by rw [nu_univ hpos]; exact ENNReal.ofReal_lt_top⟩


/-- **ZD14, the energy.**  `I(ν) = ∫ U_ν dν = c_0² log(b/4) - Σ_{k=1}^N c_k²/(2k)`. -/
theorem energy_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) :
    ∫ t, logPot (nu c N b) t ∂(nu c N b) =
      c 0 ^ 2 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
        c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) := by
  set G : ℝ → ℝ := fun t => c 0 * Real.log (b / 4) - ∑ k ∈ Finset.range N,
      c (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (2 * t / b - 1) / ((k + 1 : ℕ) : ℝ)
    with hG
  have hae : ∀ᵐ t ∂(nu c N b), logPot (nu c N b) t = G t := by
    have h0 := nu_compl_Icc (c := c) (N := N) hb.le
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with t ht
    exact logPot_nu_inside hb hpos (not_not.mp ht)
  rw [integral_congr_ae hae]
  have hGc : Continuous G := by
    simp only [hG]
    refine continuous_const.sub (continuous_finsetSum _ fun k _ => ?_)
    exact (continuous_const.mul ((Polynomial.continuous _).comp (by fun_prop))).div_const _
  rw [integral_nu hpos hGc.measurable]
  have e1 : ∀ θ, chebF c N (Real.cos θ) * G (tmap b θ) =
      c 0 * Real.log (b / 4) * chebF c N (Real.cos θ) - ∑ k ∈ Finset.range N,
        (c (k + 1) / ((k + 1 : ℕ) : ℝ)) * (chebF c N (Real.cos θ) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) := by
    intro θ
    simp only [hG, tmap_affine hb.ne']
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e1]
  rw [integral_sub ((integrable_chebF c N).const_mul _)
    (integrable_finsetSum _ fun k _ => (integrable_chebF_T c N _).const_mul _),
    integral_const_mul, integral_chebF, integral_finsetSum _ fun k _ =>
      (integrable_chebF_T c N _).const_mul _]
  have e2 : ∀ k ∈ Finset.range N, ∫ θ, (c (k + 1) / ((k + 1 : ℕ) : ℝ)) * (chebF c N (Real.cos θ) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) ∂arc =
      c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    rw [integral_const_mul, integral_chebF_mul_T]
    have hk' : k + 1 ≤ N := by simp at hk; omega
    simp only [hk', ite_true, Nat.succ_ne_zero, ite_false]
    field_simp
  rw [Finset.sum_congr rfl e2]
  ring

end

end CatalanCore.Zeta5.Potential
