module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Finite certificate rules on polygons: tubes, corners, edge covers, tails (Part 2, §4)

These rules concern the dual potential `g = M U_σ - U_ν + (1-ε)π|Im z|`, never the cotangent
source (whose bounds hold on the physical path only, `Bounds.lean`).

* **Corner / strip rule** `convexHull_sub_tube`: if every corner `c` of a cell has a rational
  witness `t_c ∈ [0,1]` with `|c - (a + t_c (b-a))|² ≤ W²` (the checker takes the clamped
  projection), the whole convex cell lies in the closed `W`-tube of the edge `[a,b]`
  (distance to a convex segment is convex).
* **Edge cover** `segment_sub_cover`: finitely many parameter intervals covering `[0,1]` cover the
  edge.  Corners need no further rule: a polygon is a finite union of edges.
* **Support intersection / endpoint**: split the edge at the parameter of the intersection
  (`Primitive.segI_split` for integrals; `segment_sub_cover` for covers); the smooth
  derivative rule is never applied through a logarithmic singularity.
* **Tail rule** `abs_mul_logPot_sub_logPot_le` (mass cancellation, `|M U_σ - U_ν| ≤ 2M₁/|z|`
  for `|z| ≥ 2 max(R_σ, R_ν)`) and `tail_rule` (`g ≥ (1-ε)π(Im p_m + sT) - 2M₁/T` on the tail
  beyond `T`).
-/

open MeasureTheory Set Metric

namespace CatalanCore.Uniform.Decay.Polygon

/-! ### Tubes, corners and covers -/

/-- A point with a rational projection witness lies in the closed tube of the edge. -/
theorem mem_tube_of_witness {a b c : ℂ} {W t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hW : 0 ≤ W) (hd : Complex.normSq (c - (a + (t : ℂ) * (b - a))) ≤ W ^ 2) :
    c ∈ cthickening W (segment ℝ a b) := by
  refine mem_cthickening_of_dist_le c (a + (t : ℂ) * (b - a)) W _ ?_ ?_
  · rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    ring
  · rw [Complex.dist_eq]
    have h : ‖c - (a + (t : ℂ) * (b - a))‖ ^ 2 ≤ W ^ 2 := by rw [Complex.sq_norm]; exact hd
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hW two_ne_zero).1 h

/-- **Corner rule.**  Corner witnesses put the whole convex cell into the closed tube. -/
theorem convexHull_sub_tube {a b : ℂ} {W : ℝ} (hW : 0 ≤ W) {cs : Set ℂ}
    (hcs : ∀ c ∈ cs, ∃ t ∈ Icc (0 : ℝ) 1,
      Complex.normSq (c - (a + (t : ℂ) * (b - a))) ≤ W ^ 2) :
    convexHull ℝ cs ⊆ cthickening W (segment ℝ a b) := by
  refine convexHull_min (fun c hc => ?_) ((convex_segment a b).cthickening W)
  obtain ⟨t, ht, hd⟩ := hcs c hc
  exact mem_tube_of_witness ht hW hd

/-- **Edge cover by parameter intervals.** -/
theorem segment_sub_cover {a b : ℂ} {ι : Type*} (α β : ι → ℝ)
    (hcov : ∀ t ∈ Icc (0 : ℝ) 1, ∃ j, t ∈ Icc (α j) (β j)) :
    segment ℝ a b ⊆ ⋃ j, (fun t : ℝ => a + (t : ℂ) * (b - a)) '' (Icc (α j) (β j)) := by
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  obtain ⟨j, hj⟩ := hcov t ht
  refine mem_iUnion.2 ⟨j, t, hj, ?_⟩
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  ring

/-! ### The tail rule -/

/-- `|log |1 - ζ|| ≤ 2|ζ|` for `|ζ| ≤ 1/2`. -/
theorem abs_log_norm_one_sub_le {ζ : ℂ} (h : ‖ζ‖ ≤ 1 / 2) :
    |Real.log ‖1 - ζ‖| ≤ 2 * ‖ζ‖ := by
  have h1 : 1 - ‖ζ‖ ≤ ‖1 - ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ζ; simpa using this
  have h2 : ‖1 - ζ‖ ≤ 1 + ‖ζ‖ := by
    have := norm_sub_le (1 : ℂ) ζ; simpa using this
  have hpos : 0 < ‖1 - ζ‖ := by linarith
  have up : Real.log ‖1 - ζ‖ ≤ ‖ζ‖ := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have lo : -(2 * ‖ζ‖) ≤ Real.log ‖1 - ζ‖ := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : (‖1 - ζ‖)⁻¹ ≤ 1 + 2 * ‖ζ‖ := by
      rw [inv_le_comm₀ hpos (by positivity)]
      have : (1 + 2 * ‖ζ‖)⁻¹ ≤ 1 - ‖ζ‖ := by
        rw [inv_le_iff_one_le_mul₀ (by positivity)]
        nlinarith [norm_nonneg ζ]
      linarith
    linarith
  rw [abs_le]; constructor <;> linarith [norm_nonneg ζ]

/-- The logarithmic potential `U_μ(z) = ∫ -log|z - w| dμ(w)`. -/
noncomputable def logPot (μ : Measure ℂ) (z : ℂ) : ℝ := ∫ w, -Real.log ‖z - w‖ ∂μ

/-- Far from a bounded measure, `U_ρ(z) = -ρ(ℂ) log|z| - A` with `|A| ≤ 2 R ρ(ℂ) / |z|`. -/
theorem logPot_far (ρ : Measure ℂ) [IsFiniteMeasure ρ] {R : ℝ} (hρ : ∀ᵐ w ∂ρ, ‖w‖ ≤ R)
    {z : ℂ} (hz0 : z ≠ 0) (hz : 2 * R ≤ ‖z‖) :
    ∃ A : ℝ, logPot ρ z = -(ρ.real univ * Real.log ‖z‖) - A ∧
      |A| ≤ 2 * R / ‖z‖ * ρ.real univ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set g : ℂ → ℝ := fun w => Real.log ‖1 - w / z‖ with hg
  have hsmall : ∀ᵐ w ∂ρ, ‖w / z‖ ≤ 1 / 2 ∧ ‖w / z‖ ≤ R / ‖z‖ := by
    filter_upwards [hρ] with w hw
    rw [norm_div]
    constructor
    · rw [div_le_iff₀ hzn]; linarith
    · exact div_le_div_of_nonneg_right hw hzn.le
  have hbound : ∀ᵐ w ∂ρ, ‖g w‖ ≤ 2 * R / ‖z‖ := by
    filter_upwards [hsmall] with w hw
    rw [Real.norm_eq_abs]
    refine (abs_log_norm_one_sub_le hw.1).trans ?_
    have := hw.2
    calc 2 * ‖w / z‖ ≤ 2 * (R / ‖z‖) := by linarith
      _ = 2 * R / ‖z‖ := by ring
  have hmeas : AEStronglyMeasurable g ρ :=
    (Real.measurable_log.comp (by fun_prop : Measurable fun w : ℂ => ‖1 - w / z‖)).aestronglyMeasurable
  have hint : Integrable g ρ := Integrable.of_bound hmeas _ hbound
  have hpt : ∀ᵐ w ∂ρ, -Real.log ‖z - w‖ = -Real.log ‖z‖ - g w := by
    filter_upwards [hsmall] with w hw
    have hne : ‖1 - w / z‖ ≠ 0 := by
      have := norm_sub_norm_le (1 : ℂ) (w / z)
      have : (0 : ℝ) < ‖1 - w / z‖ := by rw [norm_one] at this; linarith [hw.1]
      exact this.ne'
    have e : z - w = z * (1 - w / z) := by field_simp
    rw [e, norm_mul, Real.log_mul hzn.ne' hne]
    simp only [hg]; ring
  refine ⟨∫ w, g w ∂ρ, ?_, ?_⟩
  · unfold logPot
    rw [integral_congr_ae hpt, integral_sub (integrable_const _) hint, integral_const]
    simp only [smul_eq_mul]
    ring
  · have := norm_integral_le_of_norm_le_const hbound
    rwa [Real.norm_eq_abs] at this

/-- **Mass cancellation at infinity.**  If `M ρ_σ(ℂ) = ρ_ν(ℂ)` and the supports are in
`|w| ≤ R_σ, R_ν`, then for `|z| ≥ 2 max(R_σ, R_ν)`:
`|M U_σ(z) - U_ν(z)| ≤ 2 (|M| σ(ℂ) R_σ + ν(ℂ) R_ν) / |z|`. -/
theorem abs_mul_logPot_sub_logPot_le (σ ν : Measure ℂ) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    {M Rσ Rν : ℝ} (hσ : ∀ᵐ w ∂σ, ‖w‖ ≤ Rσ) (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ Rν)
    (hmass : M * σ.real univ = ν.real univ) {z : ℂ} (hz0 : z ≠ 0)
    (hzσ : 2 * Rσ ≤ ‖z‖) (hzν : 2 * Rν ≤ ‖z‖) :
    |M * logPot σ z - logPot ν z| ≤ 2 * (|M| * σ.real univ * Rσ + ν.real univ * Rν) / ‖z‖ := by
  obtain ⟨A, hA, hAb⟩ := logPot_far σ hσ hz0 hzσ
  obtain ⟨B, hB, hBb⟩ := logPot_far ν hν hz0 hzν
  have e : M * logPot σ z - logPot ν z = B - M * A := by
    rw [hA, hB]
    have : M * (-(σ.real univ * Real.log ‖z‖) - A) = -(ν.real univ * Real.log ‖z‖) - M * A := by
      rw [← hmass]; ring
    rw [this]; ring
  rw [e]
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  calc |B - M * A| ≤ |B| + |M| * |A| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 2 * Rν / ‖z‖ * ν.real univ + |M| * (2 * Rσ / ‖z‖ * σ.real univ) :=
        add_le_add hBb (mul_le_mul_of_nonneg_left hAb (abs_nonneg M))
    _ = 2 * (|M| * σ.real univ * Rσ + ν.real univ * Rν) / ‖z‖ := by field_simp; ring

/-- **Tail rule** (Part 2, eq. `tail`).  If `|Δ(z)| ≤ 2M₁/|z|` once `|z| ≥ T₀`, then on the
tail `z = p + u(-1 + is)` (`Im p ≥ 0`, `s ≥ 1`), for `u ≥ T ≥ T₀`, `T > 0`, `0 ≤ κ`:
`κ π (Im p + s T) - 2M₁/T ≤ Δ(z) + κ π |Im z|`.  With `Δ = M U_σ - U_ν` and `κ = 1 - ε` this is the
single rational tail test `g ≥ (1-ε)π(Im p_m + sT) - 2M₁/T`. -/
theorem tail_rule {Δ : ℂ → ℝ} {M₁ T₀ T κ s u : ℝ} {p : ℂ} (hM : 0 ≤ M₁)
    (hΔ : ∀ z : ℂ, T₀ ≤ ‖z‖ → |Δ z| ≤ 2 * M₁ / ‖z‖) (hp : 0 ≤ p.im) (hs : 1 ≤ s)
    (hT0 : T₀ ≤ T) (hT : 0 < T) (hu : T ≤ u) (hκ : 0 ≤ κ) :
    κ * Real.pi * (p.im + s * T) - 2 * M₁ / T
      ≤ Δ (p + (u : ℂ) * ⟨-1, s⟩) + κ * Real.pi * |(p + (u : ℂ) * ⟨-1, s⟩).im| := by
  set z := p + (u : ℂ) * ⟨-1, s⟩ with hz
  have him : z.im = p.im + u * s := by simp [hz]
  have hu0 : 0 < u := hT.trans_le hu
  have hzim : u ≤ z.im := by rw [him]; nlinarith
  have hzn : u ≤ ‖z‖ := hzim.trans ((le_abs_self _).trans (Complex.abs_im_le_norm z))
  have hzT : T ≤ ‖z‖ := hu.trans hzn
  have h1 := hΔ z (hT0.trans hzT)
  have h2 : 2 * M₁ / ‖z‖ ≤ 2 * M₁ / T :=
    div_le_div_of_nonneg_left (by positivity) hT hzT
  have h3 : -(2 * M₁ / T) ≤ Δ z := by
    have := neg_abs_le (Δ z); linarith
  have h4 : κ * Real.pi * (p.im + s * T) ≤ κ * Real.pi * |z.im| := by
    rw [abs_of_nonneg (by linarith), him]
    have : s * T ≤ u * s := by nlinarith
    have := Real.pi_pos
    have : 0 ≤ κ * Real.pi := by positivity
    nlinarith
  linarith

end CatalanCore.Uniform.Decay.Polygon
