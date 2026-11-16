module

public import CatalanCore.Zeta5.Potential.Basic
public import OAI.NumberTheory.Catalan.Analysis.RealEnergyKernelSeries
public import OAI.NumberTheory.Catalan.Energy.BarrierChebyshevLogFormula

/-!
# Z5-POTENTIAL, part 2: the logarithmic kernel against `f(cos θ) dθ/π` (ZD12)

For `x ∈ [-1, 1]` (endpoints included):
`∫ f(cos θ) log |x - cos θ| dA = -c_0 log 2 - Σ_{k ≥ 1} c_k T_k(x)/k`
(`integral_chebF_log_inside`, by damped kernels `r ↑ 1`, reverse Fatou and dominated convergence).
For `r ∈ (0, 1)` and `x = (1 + r²)/(2r) > 1` (the cosh branch, `r = e^{-w}`):
`∫ f(cos θ) log (x - cos θ) dA = -c_0 log (2r) - Σ_{k ≥ 1} c_k r^k/k`
(`integral_chebF_log_outside`, absolutely convergent series, no limit).
-/

@[expose] public section

open MeasureTheory Set Polynomial CatalanMeasure.Signed OAI.InternalCatalan

namespace CatalanCore.Zeta5.Potential

noncomputable section

theorem measurable_kernel_x (r x : ℝ) :
    Measurable (fun θ : ℝ => realEnergyCosineKernel r x (Real.cos θ)) := by
  unfold realEnergyCosineKernel realEnergyCirclePoint
  fun_prop

theorem integrable_w_kernel (c : ℕ → ℝ) (N : ℕ) {x r : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hr : r ∈ Ico (0 : ℝ) 1) :
    Integrable (fun θ => chebF c N (Real.cos θ) * realEnergyCosineKernel r x (Real.cos θ)) arc := by
  refine Integrable.mono' (integrable_const ((∑ k ∈ Finset.range (N + 1), |c k|) *
      (Real.log 2 + 2 / (1 - r))))
    (((continuous_chebF_cos c N).measurable.mul (measurable_kernel_x r x)).aestronglyMeasurable)
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_chebF_le c N (cos_mem θ)) (kernel_series_bound hr hx (cos_mem θ))
    (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem integral_chebF_damped_inside (c : ℕ → ℝ) (N : ℕ) {x r : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hr : r ∈ Ico (0 : ℝ) 1) :
    ∫ θ, chebF c N (Real.cos θ) * realEnergyCosineKernel r x (Real.cos θ) ∂arc =
      -Real.log 2 * c 0 - ∑ k ∈ Finset.range N,
        r ^ (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  set a : ℕ → ℝ := fun k => 2 * r ^ (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
    ((k + 1 : ℕ) : ℝ) with ha
  have hsum : Summable fun k => |a k| := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr.1 hr.2).mul_left (2 * r))
    have h1 := energy_chebyshev_abs_le_one (k + 1) hx
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    simp only [ha]
    rw [abs_div, abs_mul, abs_mul, abs_two, abs_pow, abs_of_nonneg hr.1, Nat.abs_cast,
      div_le_iff₀ (by linarith)]
    have h2 : 0 ≤ r ^ (k + 1) := pow_nonneg hr.1 _
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h2)
    have h3 : (2 * r) * r ^ k = 2 * r ^ (k + 1) := by ring
    rw [h3]
    nlinarith [abs_nonneg ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)]
  have hs : ∀ θ, HasSum (fun k : ℕ => a k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))
      (-realEnergyCosineKernel r x (Real.cos θ) - Real.log 2) := by
    intro θ
    have h := energy_hasSum_cosine_kernel hr hx (cos_mem θ)
    have h' := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, sub_zero,
      pow_zero] at h'
    convert h' using 1
    funext k
    simp only [ha]
    push_cast
    ring
  have := integral_chebF_mul_series c N hsum hs
  have hint : Integrable (fun θ => chebF c N (Real.cos θ) *
      realEnergyCosineKernel r x (Real.cos θ)) arc := integrable_w_kernel c N hx hr
  have e1 : ∀ θ, chebF c N (Real.cos θ) * (-realEnergyCosineKernel r x (Real.cos θ) - Real.log 2) =
      -(chebF c N (Real.cos θ) * realEnergyCosineKernel r x (Real.cos θ)) -
        Real.log 2 * chebF c N (Real.cos θ) := fun θ => by ring
  simp_rw [e1] at this
  have hI1 : Integrable (fun θ => -(chebF c N (Real.cos θ) *
      realEnergyCosineKernel r x (Real.cos θ))) arc := hint.neg
  rw [integral_sub hI1 ((integrable_chebF c N).const_mul _), integral_neg,
    integral_const_mul, integral_chebF] at this
  have e2 : ∑ k ∈ Finset.range N, a k * c (k + 1) / 2 = ∑ k ∈ Finset.range N,
      r ^ (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) / ((k + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by simp only [ha]; ring
  rw [e2] at this
  linarith


theorem rseq_ge_half (n : ℕ) : 1 / 2 ≤ rseq n := by
  unfold rseq
  have : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  linarith

theorem ae_cos_ne (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : ∀ᵐ θ ∂arc, Real.cos θ ≠ x := by
  have h0 : arc {Real.arccos x} = 0 := denMeasure_singleton _ _ _
  have h1 := (measure_eq_zero_iff_ae_notMem.mp h0)
  filter_upwards [h1, ae_mem_Icc_denMeasure (fun _ => (0 : ℝ)) 0] with θ hθ hmem hcos
  apply hθ
  have hα : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have hαm : Real.arccos x ∈ Icc 0 Real.pi := ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
  exact Real.injOn_cos hmem hαm (hcos.trans hα.symm)

theorem integral_chebF_log_inside (c : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun θ => chebF c N (Real.cos θ) * Real.log |x - Real.cos θ|) arc ∧
    ∫ θ, chebF c N (Real.cos θ) * Real.log |x - Real.cos θ| ∂arc =
      -Real.log 2 * c 0 - ∑ k ∈ Finset.range N,
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  set g : ℝ → ℝ := fun θ => Real.log |x - Real.cos θ| with hg
  have hgm : Measurable g :=
    Real.measurable_log.comp (Continuous.measurable (by fun_prop : Continuous fun θ : ℝ => |x - Real.cos θ|))
  have hae := ae_cos_ne x hx
  have hlim : ∀ᵐ θ ∂arc, Filter.Tendsto (fun n => realEnergyCosineKernel (rseq n) x (Real.cos θ))
      Filter.atTop (nhds (g θ)) := by
    filter_upwards [hae] with θ hθ
    exact (kernel_tendsto hx (cos_mem θ) (Ne.symm hθ)).comp rseq_tendsto
  -- integrability of g by reverse Fatou
  have hd1 : ∀ n, ∫ θ, realEnergyCosineKernel (rseq n) x (Real.cos θ) ∂arc = -Real.log 2 := by
    intro n
    have := integral_chebF_damped_inside (fun _ => (1 : ℝ)) 0 hx (rseq_mem n)
    simpa [chebF] using this
  have hfat := fatou_real (μ := arc) (fun n θ => realEnergyCosineKernel (rseq n) x (Real.cos θ)) g
    (Real.log 2) (fun n => measurable_kernel_x _ _) hgm
    (fun n θ => kernel_le_log_two ⟨(rseq_mem n).1, (rseq_mem n).2.le⟩ hx (cos_mem θ))
    (fun n => by
      have := integrable_w_kernel (fun _ => (1 : ℝ)) 0 hx (rseq_mem n)
      simpa [chebF] using this)
    hlim (I := -Real.log 2) (by simp only [hd1]; exact tendsto_const_nhds)
  have hgint : Integrable g arc := hfat.1
  set W : ℝ := ∑ k ∈ Finset.range (N + 1), |c k| with hW
  have hwg : Integrable (fun θ => chebF c N (Real.cos θ) * g θ) arc :=
    Integrable.bdd_mul hgint (continuous_chebF_cos c N).aestronglyMeasurable
      (ae_of_all _ fun θ => by simpa [Real.norm_eq_abs] using abs_chebF_le c N (cos_mem θ)) |>.congr
      (ae_of_all _ fun θ => by simp [mul_comm])
  refine ⟨hwg, ?_⟩
  -- dominated convergence
  have hdct := tendsto_integral_of_dominated_convergence (μ := arc)
    (F := fun n θ => chebF c N (Real.cos θ) * realEnergyCosineKernel (rseq n) x (Real.cos θ))
    (f := fun θ => chebF c N (Real.cos θ) * g θ)
    (fun θ => W * (|g θ| + Real.log 2))
    (fun n => ((continuous_chebF_cos c N).measurable.mul
      (measurable_kernel_x _ _)).aestronglyMeasurable)
    ((hgint.abs.add (integrable_const _)).const_mul W)
    (fun n => by
      filter_upwards [hae] with θ hθ
      have hr := rseq_mem n
      have hK1 := kernel_le_log_two ⟨hr.1, hr.2.le⟩ hx (cos_mem θ)
      have hK2 := realEnergyCosineKernel_compare hx (cos_mem θ) (Ne.symm hθ)
        (lt_of_lt_of_le (by norm_num) (rseq_ge_half n))
      have hlr : -Real.log 2 ≤ Real.log (rseq n) := by
        have := Real.log_le_log (by norm_num) (rseq_ge_half n)
        rw [one_div, Real.log_inv] at this
        exact this
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hKabs : |realEnergyCosineKernel (rseq n) x (Real.cos θ)| ≤ |g θ| + Real.log 2 := by
        rw [abs_le]
        constructor
        · have := neg_abs_le (g θ)
          simp only [hg] at this ⊢
          linarith
        · have := abs_nonneg (g θ)
          linarith
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_chebF_le c N (cos_mem θ)) hKabs (abs_nonneg _)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    (by
      filter_upwards [hlim] with θ hθ
      exact hθ.const_mul _)
  have hseq : ∀ n, ∫ θ, chebF c N (Real.cos θ) * realEnergyCosineKernel (rseq n) x (Real.cos θ)
        ∂arc = -Real.log 2 * c 0 - ∑ k ∈ Finset.range N,
        rseq n ^ (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) /
          ((k + 1 : ℕ) : ℝ) := fun n => integral_chebF_damped_inside c N hx (rseq_mem n)
  simp_rw [hseq] at hdct
  have hlim2 : Filter.Tendsto (fun n => -Real.log 2 * c 0 - ∑ k ∈ Finset.range N,
        rseq n ^ (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) /
          ((k + 1 : ℕ) : ℝ)) Filter.atTop (nhds (-Real.log 2 * c 0 - ∑ k ∈ Finset.range N,
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x * c (k + 1) / ((k + 1 : ℕ) : ℝ))) := by
    refine tendsto_const_nhds.sub (tendsto_finsetSum _ fun k _ => ?_)
    have := (((rseq_tendsto.pow (k + 1)).mul_const
      ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)).mul_const (c (k + 1))).div_const
      ((k + 1 : ℕ) : ℝ)
    simpa using this
  exact tendsto_nhds_unique hdct hlim2


/-! ### The outside branch -/

theorem hasSum_log_outside {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
    HasSum (fun k : ℕ => (2 * r ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))
      (-Real.log (1 - 2 * Real.cos θ * r + r ^ 2)) := by
  have hz : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]; exact hr.2
  have h := barrier_hasSum_chebyshev_log (x := Real.cos θ) (z := (r : ℂ))
    (abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩) hz
  have hpos : 0 < 1 - 2 * Real.cos θ * r + r ^ 2 := by
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, hr.1, hr.2, sq_nonneg (r - 1)]
  have hq : (1 - 2 * (Real.cos θ : ℂ) * (r : ℂ) + (r : ℂ) ^ 2) =
      ((1 - 2 * Real.cos θ * r + r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hq, ← Complex.ofReal_log hpos.le] at h
  have h2 : HasSum (fun k : ℕ => ((r ^ (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) /
      ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ)) (((-(1 / 2) * Real.log (1 - 2 * Real.cos θ * r + r ^ 2) : ℝ) : ℂ)) := by
    convert h using 1
    · funext k; push_cast; ring
    · push_cast; ring
  have h3 := Complex.hasSum_ofReal.mp h2
  have h4 := h3.mul_left 2
  convert h4 using 1
  · funext k; ring
  · ring

theorem integrable_chebF_log_outside (c : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun θ => chebF c N (Real.cos θ) *
      Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ)) arc := by
  have hcos : ∀ θ, (1 + r ^ 2) / (2 * r) - Real.cos θ = (1 - 2 * Real.cos θ * r + r ^ 2) / (2 * r) := by
    intro θ
    have hr0 : r ≠ 0 := hr.1.ne'
    field_simp
    ring
  have hpos : ∀ θ, 0 < 1 - 2 * Real.cos θ * r + r ^ 2 := fun θ => by
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, hr.1, hr.2, sq_nonneg (r - 1)]
  have hc : Continuous fun θ => Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ) := by
    refine Continuous.log (by fun_prop) fun θ => ?_
    rw [hcos]
    exact (div_pos (hpos θ) (by linarith [hr.1])).ne'
  have hm : 0 < (1 + r ^ 2) / (2 * r) - 1 := by
    have : (1 + r ^ 2) / (2 * r) - 1 = (1 - r) ^ 2 / (2 * r) := by
      have hr0 : r ≠ 0 := hr.1.ne'
      field_simp; ring
    rw [this]; exact div_pos (by nlinarith [hr.2]) (by linarith [hr.1])
  refine Integrable.mono' (integrable_const ((∑ k ∈ Finset.range (N + 1), |c k|) *
    (|Real.log ((1 + r ^ 2) / (2 * r) - 1)| + |Real.log ((1 + r ^ 2) / (2 * r) + 1)|)))
    ((continuous_chebF_cos c N).mul hc).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul (abs_chebF_le c N (cos_mem θ)) ?_ (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hy1 : (1 + r ^ 2) / (2 * r) - 1 ≤ (1 + r ^ 2) / (2 * r) - Real.cos θ := by
    linarith [Real.cos_le_one θ]
  have hy2 : (1 + r ^ 2) / (2 * r) - Real.cos θ ≤ (1 + r ^ 2) / (2 * r) + 1 := by
    linarith [Real.neg_one_le_cos θ]
  have l1 := Real.log_le_log hm hy1
  have l2 := Real.log_le_log (by linarith) hy2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ((1 + r ^ 2) / (2 * r) - 1)), abs_nonneg (Real.log ((1 + r ^ 2) / (2 * r) + 1))]
  · linarith [le_abs_self (Real.log ((1 + r ^ 2) / (2 * r) + 1)), abs_nonneg (Real.log ((1 + r ^ 2) / (2 * r) - 1))]

theorem integral_chebF_log_outside (c : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∫ θ, chebF c N (Real.cos θ) * Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ) ∂arc =
      -Real.log (2 * r) * c 0 - ∑ k ∈ Finset.range N,
        r ^ (k + 1) * c (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  set a : ℕ → ℝ := fun k => 2 * r ^ (k + 1) / ((k + 1 : ℕ) : ℝ) with ha
  have hsum : Summable fun k => |a k| := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr.1.le hr.2).mul_left (2 * r))
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    simp only [ha]
    rw [abs_div, abs_mul, abs_two, abs_pow, abs_of_pos hr.1, Nat.abs_cast,
      div_le_iff₀ (by linarith)]
    have h2 : 0 ≤ r ^ (k + 1) := pow_nonneg hr.1.le _
    have h3 : (2 * r) * r ^ k = 2 * r ^ (k + 1) := by ring
    rw [h3]
    nlinarith
  have hcos : ∀ θ, (1 + r ^ 2) / (2 * r) - Real.cos θ = (1 - 2 * Real.cos θ * r + r ^ 2) / (2 * r) := by
    intro θ
    have hr0 : r ≠ 0 := hr.1.ne'
    field_simp
    ring
  have hpos : ∀ θ, 0 < 1 - 2 * Real.cos θ * r + r ^ 2 := fun θ => by
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, hr.1, hr.2, sq_nonneg (r - 1)]
  have hlog : ∀ θ, Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ) =
      Real.log (1 - 2 * Real.cos θ * r + r ^ 2) - Real.log (2 * r) := by
    intro θ
    rw [hcos, Real.log_div (hpos θ).ne' (by linarith [hr.1])]
  have hs : ∀ θ, HasSum (fun k : ℕ => a k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))
      (-Real.log (2 * r) - Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ)) := by
    intro θ
    rw [hlog θ]
    have := hasSum_log_outside hr θ
    convert this using 1
    ring
  have key := integral_chebF_mul_series c N hsum hs
  have hint := integrable_chebF_log_outside c N hr
  have e1 : ∀ θ, chebF c N (Real.cos θ) * (-Real.log (2 * r) -
      Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ)) =
      -Real.log (2 * r) * chebF c N (Real.cos θ) -
        chebF c N (Real.cos θ) * Real.log ((1 + r ^ 2) / (2 * r) - Real.cos θ) := fun θ => by ring
  simp_rw [e1] at key
  rw [integral_sub ((integrable_chebF c N).const_mul _) hint, integral_const_mul, integral_chebF]
    at key
  have e2 : ∑ k ∈ Finset.range N, a k * c (k + 1) / 2 = ∑ k ∈ Finset.range N,
      r ^ (k + 1) * c (k + 1) / ((k + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by simp only [ha]; ring
  rw [e2] at key
  linarith

end

end CatalanCore.Zeta5.Potential
