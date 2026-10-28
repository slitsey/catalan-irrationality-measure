module

public import CatalanCore.Uniform.Decay.Polygon.Primitive
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Deformation of a polygonal ray to a reference ray (Part 2, Lemma `deform`)

Let `H σ = {z : 0 < σ Im z}` (upper half-plane for `σ = 1`, lower for `σ = -1`) and let `v` be
a real point.  Assume `f` is holomorphic on `H σ` and on a disk `B(v, δ)` (the real-start
pole-free disk), and decays like `K / (σ Im z)²` once `σ Im z ≥ 1`.  Then for every finite list
of vertices `pts ⊂ H σ` and tail direction `d` into `H σ`, the improper polygon integral
`v → p₁ → ⋯ → p_m → p_m + [0,∞) d` equals the improper integral along the reference ray
`v + [0,∞) D` (any `D` into `H σ`).

Proof: truncate both tails at `T`, close the contour with the straight connector, and use the
explicit primitive on the two convex sets `H σ` and `B(v,δ)` (`chain_close`); the connector
integral is `O(1/T)` (`connector_tendsto_zero`).  The tails are absolutely integrable
(`integrableOn_ray`).  No homotopy, residue or general Cauchy theorem is used.
-/

open MeasureTheory Set Filter Topology

namespace CatalanCore.Uniform.Decay.Polygon

/-- The open half-plane `{z : 0 < σ Im z}`. -/
def halfP (σ : ℝ) : Set ℂ := {z | 0 < σ * z.im}

theorem convex_halfP (σ : ℝ) : Convex ℝ (halfP σ) := by
  have hl : IsLinearMap ℝ (fun z : ℂ => σ * z.im) :=
    ⟨fun x y => by simp [mul_add], fun c x => by simp; ring⟩
  exact convex_halfSpace_gt hl 0

theorem isOpen_halfP (σ : ℝ) : IsOpen (halfP σ) :=
  isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)

theorem im_lineMap (a b : ℂ) (t : ℝ) :
    (AffineMap.lineMap a b t).im = a.im + t * (b.im - a.im) := by
  simp [AffineMap.lineMap_apply_module]; ring

/-- The improper ray integral `∫_0^∞ f(p + u d) d du`. -/
noncomputable def rayInt (f : ℂ → ℂ) (p d : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), f (p + (u : ℂ) * d) * d

/-- Polygon integral: the finite chain `v :: pts`, then the tail from its last vertex. -/
noncomputable def polyI (f : ℂ → ℂ) (v : ℂ) (pts : List ℂ) (d : ℂ) : ℂ :=
  chainI f (v :: pts) + rayInt f ((v :: pts).getLast (List.cons_ne_nil v pts)) d

theorem chainI_append_singleton (f : ℂ → ℂ) (x : ℂ) :
    ∀ (l : List ℂ) (a : ℂ), chainI f (a :: l ++ [x])
      = chainI f (a :: l) + segI f ((a :: l).getLast (List.cons_ne_nil a l)) x
  | [], a => by simp [chainI]
  | b :: l, a => by
    have ih := chainI_append_singleton f x l b
    simp only [List.cons_append] at ih ⊢
    rw [chainI_cons_cons, ih, chainI_cons_cons, List.getLast_cons_cons]
    ring

section close

variable {f : ℂ → ℂ} {σ δ : ℝ} {v : ℂ}

/-- A point of `[v, w]` near `v`, inside the disk and the half-plane. -/
theorem exists_near (hv : v.im = 0) (hδ : 0 < δ) {w : ℂ} (hw : 0 < σ * w.im) :
    ∃ e ∈ segment ℝ v w, e ∈ Metric.ball v δ ∧ 0 < σ * e.im := by
  have hne : w ≠ v := by
    intro h; rw [h, hv, mul_zero] at hw; exact lt_irrefl _ hw
  have hdist : 0 < dist v w := dist_pos.2 hne.symm
  set t : ℝ := min (1 / 2) (δ / (2 * dist v w)) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t ≤ δ / (2 * dist v w) := min_le_right _ _
  refine ⟨AffineMap.lineMap v w t, ?_, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht0.le, by linarith⟩, rfl⟩
  · rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht0]
    have : t * dist v w ≤ δ / 2 := by
      calc t * dist v w ≤ δ / (2 * dist v w) * dist v w :=
            mul_le_mul_of_nonneg_right ht2 hdist.le
        _ = δ / 2 := by field_simp
    linarith
  · rw [im_lineMap, hv]
    have : σ * (0 + t * (w.im - 0)) = t * (σ * w.im) := by ring
    rw [this]; exact mul_pos ht0 hw

/-- The segment `[v, w]` lies in the disk at `v` together with the half-plane. -/
theorem segment_sub (hv : v.im = 0) (hδ : 0 < δ) {w : ℂ} (hw : 0 < σ * w.im) :
    ∀ z ∈ segment ℝ v w, z ∈ Metric.ball v δ ∨ z ∈ halfP σ := by
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := hz
  rcases ht0.lt_or_eq with h | h
  · right
    show 0 < σ * (AffineMap.lineMap v w t).im
    rw [im_lineMap, hv]
    have : σ * (0 + t * (w.im - 0)) = t * (σ * w.im) := by ring
    rw [this]; exact mul_pos h hw
  · left; rw [← h]; simp [hδ]

theorem diffAt_of_mem (hδ : 0 < δ) (hfH : DifferentiableOn ℂ f (halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) {z : ℂ}
    (hz : z ∈ Metric.ball v δ ∨ z ∈ halfP σ) : DifferentiableAt ℂ f z := by
  rcases hz with h | h
  · exact hfB.differentiableAt (Metric.isOpen_ball.mem_nhds h)
  · exact hfH.differentiableAt ((isOpen_halfP σ).mem_nhds h)

/-- **Closing the truncated contour** with the explicit primitive on the two convex sets
`H σ` and `B(v,δ)`. -/
theorem chain_close (hv : v.im = 0) (hδ : 0 < δ) (hfH : DifferentiableOn ℂ f (halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) (w1 : ℂ) (rest : List ℂ)
    (hl : ∀ z ∈ w1 :: rest, 0 < σ * z.im) {Q : ℂ} (hQ : 0 < σ * Q.im) :
    chainI f (v :: w1 :: rest) + segI f ((w1 :: rest).getLast (List.cons_ne_nil _ _)) Q
      = segI f v Q := by
  have hw1 : 0 < σ * w1.im := hl w1 (by simp)
  obtain ⟨e1, he1s, he1b, he1h⟩ := exists_near (σ := σ) hv hδ hw1
  obtain ⟨e2, he2s, he2b, he2h⟩ := exists_near (σ := σ) hv hδ hQ
  set L := (w1 :: rest).getLast (List.cons_ne_nil _ _) with hL
  have hLm : 0 < σ * L.im := hl L (List.getLast_mem _)
  have hrest : ∀ z ∈ rest, z ∈ halfP σ := fun z hz => hl z (by simp [hz])
  have s1 := segI_split he1s (fun z hz => diffAt_of_mem hδ hfH hfB (segment_sub hv hδ hw1 z hz))
  have c1 := chainI_eq (convex_halfP σ) hfH rest w1 hw1 hrest
  have a1 := segI_add (convex_halfP σ) hfH (a := e1) (b := w1) (c := L) he1h hw1 hLm
  have a2 := segI_add (convex_halfP σ) hfH (a := e1) (b := L) (c := Q) he1h hLm hQ
  have a3 := segI_add (convex_halfP σ) hfH (a := e1) (b := e2) (c := Q) he1h he2h hQ
  have b1 := segI_add (convex_ball v δ) hfB (a := v) (b := e1) (c := e2)
    (Metric.mem_ball_self hδ) he1b he2b
  have s2 := segI_split he2s (fun z hz => diffAt_of_mem hδ hfH hfB (segment_sub hv hδ hQ z hz))
  rw [chainI_cons_cons, c1]
  rw [← hL]
  linear_combination -s1 + a1 + a2 - a3 + b1 + s2

end close

/-! ### Integrability of the tails and the connector estimate -/

section improper

variable {f : ℂ → ℂ} {σ : ℝ}

theorem im_ray (p d : ℂ) (u : ℝ) : (p + (u : ℂ) * d).im = p.im + u * d.im := by simp

/-- A ray integrand is integrable if `f` is continuous along the closed ray and decays like
`K / (σ Im z)²` once `σ Im z ≥ 1`. -/
theorem integrableOn_ray {p d : ℂ} (hp : 0 ≤ σ * p.im) (hd : 0 < σ * d.im) {K : ℝ}
    (hK : 0 ≤ K) (hdec : ∀ z : ℂ, 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2)
    (hc : ∀ u : ℝ, 0 ≤ u → ContinuousAt f (p + (u : ℂ) * d)) :
    IntegrableOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ioi 0) := by
  set U : ℝ := 1 / (σ * d.im) with hU
  have hU0 : 0 < U := by positivity
  have hcont : ContinuousOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ici 0) := by
    intro u hu
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact (hc u hu).comp (f := fun u : ℝ => p + (u : ℂ) * d) (by fun_prop)
  have h1 : IntegrableOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ioc 0 U) :=
    ((hcont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ => f (p + (u : ℂ) * d) * d) (Ioi U) := by
    have hb : IntegrableOn (fun u : ℝ => (K * ‖d‖ / (σ * d.im) ^ 2) * u ^ (-2 : ℝ)) (Ioi U) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hU0).const_mul _
    refine hb.mono' ((hcont.mono (Ioi_subset_Ici hU0.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu : U < u := hu
    have hu0 : 0 < u := hU0.trans hu
    have hh : u * (σ * d.im) ≤ σ * (p + (u : ℂ) * d).im := by
      rw [im_ray]; nlinarith
    have h1le : 1 ≤ u * (σ * d.im) := by
      rw [hU] at hu
      have := (div_lt_iff₀ hd).1 hu
      linarith
    have hz := hdec _ (h1le.trans hh)
    rw [norm_mul]
    have hpos : 0 < u * (σ * d.im) := by positivity
    have hsq : K / (σ * (p + (u : ℂ) * d).im) ^ 2 ≤ K / (u * (σ * d.im)) ^ 2 :=
      div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_left₀ hpos.le hh 2)
    have hr : u ^ (-2 : ℝ) = 1 / u ^ 2 := by
      rw [Real.rpow_neg hu0.le, one_div]; norm_cast
    rw [hr]
    calc ‖f (p + (u : ℂ) * d)‖ * ‖d‖ ≤ K / (u * (σ * d.im)) ^ 2 * ‖d‖ :=
          mul_le_mul_of_nonneg_right (hz.trans hsq) (norm_nonneg _)
      _ = K * ‖d‖ / (σ * d.im) ^ 2 * (1 / u ^ 2) := by field_simp
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi hU0.le] at this

/-- Heights along a segment are at least the smaller endpoint height. -/
theorem height_segment_ge {A B z : ℂ} {m : ℝ} (hA : m ≤ σ * A.im) (hB : m ≤ σ * B.im)
    (hz : z ∈ segment ℝ A B) : m ≤ σ * z.im := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  rw [im_lineMap]
  have : σ * (A.im + t * (B.im - A.im)) = (1 - t) * (σ * A.im) + t * (σ * B.im) := by ring
  rw [this]
  nlinarith

/-- **Connector estimate.**  The straight connector from `p + T d` to `v + T D` has integral
`O(1/T)`. -/
theorem connector_tendsto_zero {p v d D : ℂ} (hp : 0 ≤ σ * p.im) (hv : 0 ≤ σ * v.im)
    (hd : 0 < σ * d.im) (hD : 0 < σ * D.im) {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ z : ℂ, 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2) :
    Tendsto (fun T : ℝ => segI f (p + (T : ℂ) * d) (v + (T : ℂ) * D)) atTop (𝓝 0) := by
  set c : ℝ := min (σ * d.im) (σ * D.im) with hc
  have hc0 : 0 < c := lt_min hd hD
  set α : ℝ := ‖v - p‖
  set β : ℝ := ‖D - d‖
  have hbound : ∀ᶠ T : ℝ in atTop, ‖segI f (p + (T : ℂ) * d) (v + (T : ℂ) * D)‖
      ≤ K / c ^ 2 * (α * (T⁻¹) ^ 2 + β * T⁻¹) := by
    filter_upwards [eventually_ge_atTop (1 / c), eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hcT : 1 ≤ c * T := by
      have := (div_le_iff₀ hc0).1 hT; linarith
    have hA : c * T ≤ σ * (p + (T : ℂ) * d).im := by
      rw [im_ray]; have := min_le_left (σ * d.im) (σ * D.im); nlinarith
    have hB : c * T ≤ σ * (v + (T : ℂ) * D).im := by
      rw [im_ray]; have := min_le_right (σ * d.im) (σ * D.im); nlinarith
    have hseg : ∀ z ∈ segment ℝ (p + (T : ℂ) * d) (v + (T : ℂ) * D),
        ‖f z‖ ≤ K / (c * T) ^ 2 := by
      intro z hz
      have hm := height_segment_ge hA hB hz
      refine (hdec z (hcT.trans hm)).trans ?_
      exact div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_left₀ (by positivity) hm 2)
    refine (norm_segI_le hseg).trans ?_
    have hlen : ‖(v + (T : ℂ) * D) - (p + (T : ℂ) * d)‖ ≤ α + T * β := by
      have e : (v + (T : ℂ) * D) - (p + (T : ℂ) * d) = (v - p) + (T : ℂ) * (D - d) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT0.le]
    calc K / (c * T) ^ 2 * ‖(v + (T : ℂ) * D) - (p + (T : ℂ) * d)‖
        ≤ K / (c * T) ^ 2 * (α + T * β) :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = K / c ^ 2 * (α * (T⁻¹) ^ 2 + β * T⁻¹) := by field_simp
  have hlim : Tendsto (fun T : ℝ => K / c ^ 2 * (α * (T⁻¹) ^ 2 + β * T⁻¹)) atTop (𝓝 0) := by
    have h0 := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have := ((h0.pow 2).const_mul α).add (h0.const_mul β)
    have := this.const_mul (K / c ^ 2)
    simpa using this
  exact squeeze_zero_norm' hbound hlim

end improper

/-! ### The deformation theorem -/

section deform

variable {f : ℂ → ℂ} {σ δ : ℝ} {v : ℂ}

theorem mem_or_half (pts : List ℂ) (hpts : ∀ z ∈ pts, 0 < σ * z.im) :
    ∀ z ∈ v :: pts, z = v ∨ 0 < σ * z.im := by
  intro z hz
  rcases List.mem_cons.1 hz with h | h
  · exact Or.inl h
  · exact Or.inr (hpts z h)

theorem ray_mem (hδ : 0 < δ) {p d : ℂ} (hp : p = v ∨ 0 < σ * p.im) (hd : 0 < σ * d.im)
    (hv : v.im = 0) {u : ℝ} (hu : 0 ≤ u) :
    p + (u : ℂ) * d ∈ Metric.ball v δ ∨ p + (u : ℂ) * d ∈ halfP σ := by
  rcases hu.lt_or_eq with h | h
  · right
    show 0 < σ * (p + (u : ℂ) * d).im
    rw [im_ray]
    have hp' : 0 ≤ σ * p.im := by
      rcases hp with h' | h'
      · rw [h', hv, mul_zero]
      · exact h'.le
    nlinarith
  · rw [← h]; simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rcases hp with h' | h'
    · left; rw [h']; exact Metric.mem_ball_self hδ
    · right; exact h'

/-- **Deformation is automatic** (Part 2, Lemma `deform`, generic form).  For `f` holomorphic on
the half-plane `H σ` and on the real-start disk `B(v, δ)`, with `K/(σ Im z)²` decay, the
improper integral along the polygon `v → pts → tail d` equals the reference ray integral. -/
theorem deform (hv : v.im = 0) (hδ : 0 < δ) (hfH : DifferentiableOn ℂ f (halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < σ * z.im) {d D : ℂ} (hd : 0 < σ * d.im) (hD : 0 < σ * D.im)
    {K : ℝ} (hK : 0 ≤ K) (hdec : ∀ z : ℂ, 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2) :
    polyI f v pts d = rayInt f v D := by
  set L := (v :: pts).getLast (List.cons_ne_nil v pts) with hL
  have hLm : L = v ∨ 0 < σ * L.im := mem_or_half pts hpts L (List.getLast_mem _)
  have hL0 : 0 ≤ σ * L.im := by
    rcases hLm with h | h
    · rw [h, hv, mul_zero]
    · exact h.le
  have hv0 : 0 ≤ σ * v.im := by rw [hv, mul_zero]
  have hdiff : ∀ z, (z ∈ Metric.ball v δ ∨ z ∈ halfP σ) → DifferentiableAt ℂ f z :=
    fun z hz => diffAt_of_mem hδ hfH hfB hz
  have hiT := integrableOn_ray hL0 hd hK hdec
    (fun u hu => (hdiff _ (ray_mem hδ hLm hd hv hu)).continuousAt)
  have hiR := integrableOn_ray hv0 hD hK hdec
    (fun u hu => (hdiff _ (ray_mem hδ (Or.inl rfl) hD hv hu)).continuousAt)
  -- the truncated identity, for every `T > 0`
  have htr : ∀ T : ℝ, 0 < T → chainI f (v :: pts) + segI f L (L + (T : ℂ) * d)
      + segI f (L + (T : ℂ) * d) (v + (T : ℂ) * D) = segI f v (v + (T : ℂ) * D) := by
    intro T hT
    have hend : 0 < σ * (L + (T : ℂ) * d).im := by rw [im_ray]; nlinarith
    have hQ : 0 < σ * (v + (T : ℂ) * D).im := by rw [im_ray]; nlinarith
    have happ := chainI_append_singleton f (L + (T : ℂ) * d) pts v
    obtain ⟨w1, rest, hwr⟩ : ∃ w1 rest, pts ++ [L + (T : ℂ) * d] = w1 :: rest := by
      cases pts with
      | nil => exact ⟨_, [], rfl⟩
      | cons a l => exact ⟨a, l ++ [L + (T : ℂ) * d], rfl⟩
    have hl : ∀ z ∈ w1 :: rest, 0 < σ * z.im := by
      rw [← hwr]; intro z hz
      rcases List.mem_append.1 hz with h | h
      · exact hpts z h
      · rw [List.mem_singleton.1 h]; exact hend
    have hcl := chain_close hv hδ hfH hfB w1 rest hl hQ (f := f)
    have hlast : (w1 :: rest).getLast (List.cons_ne_nil _ _) = L + (T : ℂ) * d := by
      simp only [← hwr, List.getLast_append_singleton]
    rw [hlast] at hcl
    have e : v :: pts ++ [L + (T : ℂ) * d] = v :: w1 :: rest := by
      rw [List.cons_append, hwr]
    rw [e] at happ
    rw [← hL] at happ
    rw [← happ]; exact hcl
  -- pass to the limit `T → ∞`
  have hT1 : Tendsto (fun T : ℝ => segI f L (L + (T : ℂ) * d)) atTop
      (𝓝 (rayInt f L d)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 hiT tendsto_id
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [segI_ray f L d hT]; rfl
  have hT2 : Tendsto (fun T : ℝ => segI f v (v + (T : ℂ) * D)) atTop
      (𝓝 (rayInt f v D)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 hiR tendsto_id
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [segI_ray f v D hT]; rfl
  have hT3 := connector_tendsto_zero (f := f) hL0 hv0 hd hD hK hdec (p := L) (v := v)
  have hsum := (tendsto_const_nhds (x := chainI f (v :: pts))).add hT1 |>.add hT3
  have hsum' : Tendsto (fun T : ℝ => segI f v (v + (T : ℂ) * D)) atTop
      (𝓝 (chainI f (v :: pts) + rayInt f L d + 0)) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact htr T hT
  have := tendsto_nhds_unique hsum' hT2
  rw [add_zero] at this
  unfold polyI
  rw [← hL]; exact this

end deform

end CatalanCore.Uniform.Decay.Polygon
