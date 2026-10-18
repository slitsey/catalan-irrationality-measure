module

public import CatalanCore.NT.PNTClass

@[expose] public section

/-!
# Two-sided PNT on intervals (design WP5 / WP-H5)

`θ(bN; m, r) - θ(aN; m, r) = (b - a) / φ(m) · N + o(N)`, in the form needed by the hybrid
tropical summation, and the elementary difference identity for `thetaClass`.
-/

open Filter Topology

namespace CatalanCore.NT

/-- Telescoping: the increment of `thetaClassN` is the sum over the prime window. -/
theorem thetaClassN_sub (m : ℕ) (r : ZMod m) {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    thetaClassN m r N₂ - thetaClassN m r N₁ =
      ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod m) = r),
        Real.log n := by
  unfold thetaClassN
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ico_eq_sub _ (by omega : N₁ + 1 ≤ N₂ + 1),]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-- `θ(c N; m, r) / N → c / φ(m)` for `c > 0`. -/
theorem thetaClass_scaled {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℝ ↦ thetaClass m r (c * N) / N) atTop (𝓝 (c * (m.totient : ℝ)⁻¹)) := by
  have h := ((pnt_class hr).comp (tendsto_id.const_mul_atTop hc)).const_mul c
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  simp only [Function.comp, id]
  field_simp

/-- **Two-sided PNT on intervals.**  For `0 < a ≤ b`,
`(θ(bN; m, r) - θ(aN; m, r)) / N → (b - a) / φ(m)`. -/
theorem theta_interval_asymp {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N : ℝ ↦ (thetaClass m r (b * N) - thetaClass m r (a * N)) / N) atTop
      (𝓝 ((b - a) / (m.totient : ℝ))) := by
  have h := (thetaClass_scaled hr (by linarith : 0 < b)).sub (thetaClass_scaled hr ha)
  have e : b * (m.totient : ℝ)⁻¹ - a * (m.totient : ℝ)⁻¹ = (b - a) / (m.totient : ℝ) := by
    ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards with N
  ring

/-- Explicit `ε`-form of `theta_interval_asymp`:
`|θ(bN) - θ(aN) - (b - a)/φ(m) · N| ≤ ε N` for large `N`. -/
theorem theta_interval_abs_le {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop,
      |thetaClass m r (b * N) - thetaClass m r (a * N) - (b - a) / (m.totient : ℝ) * N| ≤ ε * N := by
  have h := theta_interval_asymp hr ha hab
  have h2 := (Metric.tendsto_nhds.mp h) ε hε
  filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  rw [Real.dist_eq] at hN
  have : thetaClass m r (b * N) - thetaClass m r (a * N) - (b - a) / (m.totient : ℝ) * N =
      ((thetaClass m r (b * N) - thetaClass m r (a * N)) / N - (b - a) / (m.totient : ℝ)) * N := by
    field_simp
  rw [this, abs_mul, abs_of_pos hN0]
  exact mul_le_mul_of_nonneg_right hN.le hN0.le

end CatalanCore.NT
