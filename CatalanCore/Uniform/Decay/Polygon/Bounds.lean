module

public import CatalanCore.Uniform.Decay.Polygon.Space
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# Certificate-independent source bounds on the physical polygon (Part 2, Lemma `sourcebounds`)

All bounds are on the actual physical path only (cotangent separation is never claimed on a
tube).  Let `e` be the first edge direction (`p₁ - x*`, or the tail direction if there is no
vertex), `q = Re e / Im e` its inverse slope, `η* = δ0 / (1 + |q|)` (a square-root-free form of
`δ* = δ0/√(1+q²)`; `η* ≤ δ*`).

* `firstEdge_sep` : points `x* + t e` (`t ≥ 0`) keep distance `η*` from every real pole.
* `two_mul_norm_sub_round_le` : `2 |w - round(Re w)| ≤ |sin πw|`.
* `path_sin_lower` : `κ e^{π|Im z|} ≤ |sin π(z+μ_i)|` on the whole upper path, with
  `κ = min(1/4, 2η* e^{-π/8})`, provided every later vertex has height `≥ 1/8`.
* `norm_EC_path`, `norm_EC_path_lower` : `‖E z‖ ≤ C e^{-2π|Im z|}` on both paths,
  `C = π ∑|w_i| / κ` (independent of the scale).
* `path_node_dist` : distance `≥ 1` from `[0, ∞)`, when later vertices have height `≥ 1` and
  `x* + |q| ≤ -1`.
* `path_growth` : `|z| ≤ V + 2|Im z|` if all vertices have norm `≤ V` and the tail has slope
  `≥ 1` (`|Re d| ≤ Im d`).
-/

open MeasureTheory Set Filter Topology Complex

namespace CatalanCore.Uniform.Decay.Polygon

/-! ### Elementary separation lemmas -/

/-- **Initial-edge pole separation** (completing the square, square-root free). -/
theorem firstEdge_sep {v p δ0 t : ℝ} {e : ℂ} (he : 0 < e.im) (ht : 0 ≤ t)
    (hgap : δ0 ≤ |v - p|) :
    δ0 / (1 + |e.re / e.im|) ≤ ‖(v : ℂ) + (t : ℂ) * e - (p : ℂ)‖ := by
  set q := e.re / e.im with hq
  set η := δ0 / (1 + |q|) with hη
  have h1q : 0 < 1 + |q| := by positivity
  have hηq : η * (1 + |q|) = δ0 := by rw [hη]; field_simp
  set y := t * e.im with hy
  have hy0 : 0 ≤ y := mul_nonneg ht he.le
  have hre : ((v : ℂ) + (t : ℂ) * e - (p : ℂ)).re = (v - p) + q * y := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [hq, hy]; field_simp; ring
  have him : ((v : ℂ) + (t : ℂ) * e - (p : ℂ)).im = y := by simp [hy]
  have nre := Complex.abs_re_le_norm ((v : ℂ) + (t : ℂ) * e - (p : ℂ))
  have nim := Complex.abs_im_le_norm ((v : ℂ) + (t : ℂ) * e - (p : ℂ))
  rw [hre] at nre
  rw [him, abs_of_nonneg hy0] at nim
  by_cases hc : η ≤ y
  · linarith
  · push_neg at hc
    have hqy : |q * y| ≤ |q| * η := by
      rw [abs_mul, abs_of_nonneg hy0]
      exact mul_le_mul_of_nonneg_left hc.le (abs_nonneg q)
    have := abs_sub_abs_le_abs_sub (v - p) (-(q * y))
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith

theorem abs_le_abs_sinh (t : ℝ) : |t| ≤ |Real.sinh t| := by
  rcases le_total 0 t with h | h
  · have h' := Real.self_le_sinh_iff.2 h
    rw [abs_of_nonneg h, abs_of_nonneg (h.trans h')]
    exact h'
  · have h' := Real.sinh_le_self_iff.2 h
    rw [abs_of_nonpos h, abs_of_nonpos (h'.trans h)]
    linarith

/-- `2 |w - n| ≤ |sin πw|` for the nearest integer `n = round (Re w)`. -/
theorem two_mul_norm_sub_round_le (w : ℂ) :
    2 * ‖w - (round w.re : ℂ)‖ ≤ ‖Complex.sin ((Real.pi : ℂ) * w)‖ := by
  have hpi := Real.pi_gt_three
  have hs := Decay.norm_sin_sq ((Real.pi : ℂ) * w)
  have hre : ((Real.pi : ℂ) * w).re = Real.pi * w.re := by simp
  have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
  rw [hre, him] at hs
  set g := |w.re - round w.re|
  have h1 := Frame.two_mul_le_abs_sin_pi (u := w.re) (g := g) (fun n => round_le w.re n)
  have h2 := abs_le_abs_sinh (Real.pi * w.im)
  have hn : ‖w - (round w.re : ℂ)‖ ^ 2 = (w.re - round w.re) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hsq : (2 * ‖w - (round w.re : ℂ)‖) ^ 2 ≤ ‖Complex.sin ((Real.pi : ℂ) * w)‖ ^ 2 := by
    rw [mul_pow, hn, hs]
    have e1 : (w.re - round w.re) ^ 2 = g ^ 2 := by rw [sq_abs]
    have a1 : (2 * g) ^ 2 ≤ Real.sin (Real.pi * w.re) ^ 2 := by
      rw [← sq_abs (Real.sin _)]; exact pow_le_pow_left₀ (by positivity) h1 2
    have a2 : (Real.pi * w.im) ^ 2 ≤ Real.sinh (Real.pi * w.im) ^ 2 := by
      rw [← sq_abs (Real.sinh _), ← sq_abs (Real.pi * w.im)]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have a3 : 4 * w.im ^ 2 ≤ (Real.pi * w.im) ^ 2 := by
      have : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      nlinarith [sq_nonneg w.im]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq

/-! ### Where the path points lie -/

/-- The direction of the first edge (`p₁ - v`, or the tail direction if there is no vertex). -/
noncomputable def firstDir (v : ℂ) : List ℂ → ℂ → ℂ
  | [], d => d
  | b :: _, _ => b - v

/-- The inverse slope `q` of the first edge. -/
noncomputable def qFirst (v : ℂ) (pts : List ℂ) (d : ℂ) : ℝ :=
  (firstDir v pts d).re / (firstDir v pts d).im

theorem firstDir_im_pos {v : ℂ} (hv : v.im = 0) {pts : List ℂ} {d : ℂ}
    (hpts : ∀ z ∈ pts, 0 < z.im) (hd : 0 < d.im) : 0 < (firstDir v pts d).im := by
  cases pts with
  | nil => exact hd
  | cons b l => simp only [firstDir, Complex.sub_im, hv, sub_zero]; exact hpts b (by simp)

/-- A path point is either at height `≥ c` or on the first edge (ray) `v + t e`, `t ≥ 0`, provided
every vertex after `v` has height `≥ c`. -/
theorem path_point_cases {v : ℂ} (hv : v.im = 0) {c : ℝ} (pts : List ℂ)
    (hpts : ∀ z ∈ pts, c ≤ z.im) {d : ℂ} (hd : 0 ≤ d.im) {u : ℝ} (hu : 0 ≤ u) :
    c ≤ (pathPt d v pts u).im ∨
      ∃ t : ℝ, 0 ≤ t ∧ pathPt d v pts u = v + (t : ℂ) * firstDir v pts d := by
  rcases pathPt_mem d pts v hu with h | ⟨t, ht, he⟩
  · cases pts with
    | nil => exact absurd h (by simp [chainSet])
    | cons b l =>
      rcases h with h | h
      · right
        rw [segment_eq_image_lineMap] at h
        obtain ⟨t, ⟨ht0, _⟩, he⟩ := h
        exact ⟨t, ht0, by rw [← he, lineMap_eq]; rfl⟩
      · left
        have hb : b ∈ {z : ℂ | c ≤ z.im} := hpts b (by simp)
        have hcv : Convex ℝ {z : ℂ | c ≤ z.im} := by
          have hl : IsLinearMap ℝ (fun z : ℂ => z.im) :=
            ⟨fun x y => by simp, fun a x => by simp⟩
          exact convex_halfSpace_ge hl c
        exact chainSet_sub_convex hcv l b hb (fun z hz => hpts z (by simp [hz])) h
  · cases pts with
    | nil =>
      right; refine ⟨t, ht, ?_⟩; rw [he]; rfl
    | cons b l =>
      left
      rw [he, im_ray]
      have hL : c ≤ ((v :: b :: l).getLast (List.cons_ne_nil _ _)).im := by
        rw [List.getLast_cons_cons]; exact hpts _ (List.getLast_mem _)
      nlinarith

theorem pathPt_conj (d : ℂ) : ∀ (l : List ℂ) (a : ℂ) (u : ℝ),
    pathPt (starRingEnd ℂ d) (starRingEnd ℂ a) (l.map (starRingEnd ℂ)) u
      = starRingEnd ℂ (pathPt d a l u)
  | [], a, u => by simp [pathPt]
  | b :: l, a, u => by
    by_cases h : u ≤ 1
    · simp [pathPt, h]
    · simp only [List.map_cons, pathPt, if_neg h]
      exact pathPt_conj d l b (u - 1)

theorem pathDer_conj (d : ℂ) : ∀ (l : List ℂ) (a : ℂ) (u : ℝ),
    pathDer (starRingEnd ℂ d) (starRingEnd ℂ a) (l.map (starRingEnd ℂ)) u
      = starRingEnd ℂ (pathDer d a l u)
  | [], a, u => by simp [pathDer]
  | b :: l, a, u => by
    by_cases h : u ≤ 1
    · simp [pathDer, h]
    · simp only [List.map_cons, pathDer, if_neg h]
      exact pathDer_conj d l b (u - 1)

/-! ### Cotangent separation on the physical path -/

variable {Fr : Frame}

theorem gap_real (hC : Fr.ContourOK) (N0 : ℕ) (n : ℤ) (i : Fin Fr.d) :
    (Fr.δ0 : ℝ) ≤ |Fr.xstar N0 - ((n : ℝ) - (Fr.μ i : ℝ))| := by
  have hg := hC.gap.2 i (-n - (N0 : ℤ))
  have : ((|(((-n - (N0 : ℤ) : ℤ) : ℚ) + Fr.μ i - Fr.xs : ℚ)| : ℚ) : ℝ)
      = |Fr.xstar N0 - ((n : ℝ) - (Fr.μ i : ℝ))| := by
    push_cast; unfold Frame.xstar; congr 1; ring
  rw [← this]; exact_mod_cast hg

/-- The uniform sine constant on a polygon with first-edge inverse slope `q`. -/
noncomputable def kappaP (Fr : Frame) (q : ℝ) : ℝ :=
  min (1 / 4) (2 * ((Fr.δ0 : ℝ) / (1 + |q|)) * Real.exp (-(Real.pi / 8)))

theorem kappaP_pos (hC : Fr.ContourOK) (q : ℝ) : 0 < kappaP Fr q := by
  have : (0 : ℝ) < Fr.δ0 := by exact_mod_cast hC.gap.1
  unfold kappaP; exact lt_min (by norm_num) (by positivity)

/-- **Sine lower bound on the whole upper physical path.** -/
theorem path_sin_lower (hC : Fr.ContourOK) (N0 : ℕ) {pts : List ℂ} {d : ℂ}
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) (i : Fin Fr.d) :
    kappaP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
        * Real.exp (Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)
      ≤ ‖Complex.sin ((Real.pi : ℂ) * (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u + (Fr.μ i : ℂ)))‖ := by
  have hpi := Real.pi_gt_three
  have hv : (((Fr.xstar N0 : ℝ) : ℂ)).im = 0 := by simp
  set z := pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u with hz
  set q := qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d
  have hκ1 : kappaP Fr q ≤ 1 / 4 := min_le_left _ _
  have hκ2 : kappaP Fr q ≤ 2 * ((Fr.δ0 : ℝ) / (1 + |q|)) * Real.exp (-(Real.pi / 8)) :=
    min_le_right _ _
  have hκ0 := kappaP_pos hC q
  have hw : ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).im = Real.pi * z.im := by simp
  by_cases hbig : 1 / 8 ≤ |z.im|
  · have hge : 3 / 8 ≤ |((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).im| := by
      rw [hw, abs_mul, abs_of_pos Real.pi_pos]; nlinarith
    have h := Decay.norm_sin_ge _ hge
    rw [hw, abs_mul, abs_of_pos Real.pi_pos] at h
    have := Real.exp_pos (Real.pi * |z.im|)
    nlinarith
  · push_neg at hbig
    rcases path_point_cases hv pts hlow hd.le hu with h | ⟨t, ht, he⟩
    · exact absurd (h.trans (le_abs_self _)) (not_le.2 hbig)
    · have hpos : 0 < (firstDir ((Fr.xstar N0 : ℝ) : ℂ) pts d).im :=
        firstDir_im_pos hv (fun z hz => by linarith [hlow z hz]) hd
      set w := z + (Fr.μ i : ℂ)
      set n : ℤ := round w.re
      have hs := two_mul_norm_sub_round_le w
      have hsep := firstEdge_sep (v := Fr.xstar N0) (p := (n : ℝ) - (Fr.μ i : ℝ)) hpos ht
        (gap_real hC N0 n i)
      have e1 : w - (n : ℂ) = ((Fr.xstar N0 : ℝ) : ℂ) + (t : ℂ) * firstDir ((Fr.xstar N0 : ℝ) : ℂ) pts d
          - (((n : ℝ) - (Fr.μ i : ℝ) : ℝ) : ℂ) := by
        simp only [w]; rw [hz, he]; push_cast; ring
      rw [e1] at hs
      have hq : (firstDir ((Fr.xstar N0 : ℝ) : ℂ) pts d).re / (firstDir ((Fr.xstar N0 : ℝ) : ℂ) pts d).im = q := rfl
      rw [hq] at hsep
      have hex : Real.exp (Real.pi * |z.im|) * Real.exp (-(Real.pi / 8)) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
      have hη : 0 ≤ (Fr.δ0 : ℝ) / (1 + |q|) := by
        have : (0 : ℝ) < Fr.δ0 := by exact_mod_cast hC.gap.1
        positivity
      calc kappaP Fr q * Real.exp (Real.pi * |z.im|)
          ≤ 2 * ((Fr.δ0 : ℝ) / (1 + |q|)) * Real.exp (-(Real.pi / 8)) *
              Real.exp (Real.pi * |z.im|) :=
            mul_le_mul_of_nonneg_right hκ2 (Real.exp_pos _).le
        _ = 2 * ((Fr.δ0 : ℝ) / (1 + |q|)) *
              (Real.exp (Real.pi * |z.im|) * Real.exp (-(Real.pi / 8))) := by ring
        _ ≤ 2 * ((Fr.δ0 : ℝ) / (1 + |q|)) * 1 :=
            mul_le_mul_of_nonneg_left hex (by positivity)
        _ ≤ _ := by linarith

/-- The cotangent constant `C = π ∑ |w_i| / κ` of the polygon. -/
noncomputable def CP (Fr : Frame) (q : ℝ) : ℝ := Real.pi * (∑ i, |(Fr.w i : ℝ)|) / kappaP Fr q

/-- **Cotangent separation on the upper physical path.** -/
theorem norm_EC_path (hC : Fr.ContourOK) (N0 : ℕ) {pts : List ℂ} {d : ℂ}
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖Fr.EC (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖
      ≤ CP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
          * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)) :=
  Fr.norm_EC_le (kappaP_pos hC _) (fun i => path_sin_lower hC N0 hlow hd hu i)

theorem conjL_conj_path (N0 : ℕ) (pts : List ℂ) (d : ℂ) (u : ℝ) :
    pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u
      = starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) := by
  have := pathPt_conj d pts ((Fr.xstar N0 : ℝ) : ℂ) u
  rwa [Complex.conj_ofReal] at this

theorem conjL_conj_der (N0 : ℕ) (pts : List ℂ) (d : ℂ) (u : ℝ) :
    pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u
      = starRingEnd ℂ (pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u) := by
  have := pathDer_conj d pts ((Fr.xstar N0 : ℝ) : ℂ) u
  rwa [Complex.conj_ofReal] at this

/-- **Cotangent separation on the lower physical path** (by conjugation). -/
theorem norm_EC_path_lower (hC : Fr.ContourOK) (N0 : ℕ) {pts : List ℂ} {d : ℂ}
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖Fr.EC (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u)‖
      ≤ CP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
          * Real.exp (-(2 * Real.pi *
              |(pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u).im|)) := by
  rw [conjL_conj_path]
  refine Fr.norm_EC_le (kappaP_pos hC _) (fun i => ?_)
  have h := path_sin_lower hC N0 hlow hd hu i
  have e : (Real.pi : ℂ) * (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u) + (Fr.μ i : ℂ))
      = starRingEnd ℂ ((Real.pi : ℂ) * (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u + (Fr.μ i : ℂ))) := by
    simp [map_add, map_mul, Complex.conj_ofReal]
  rw [e, Complex.sin_conj, Complex.norm_conj, Complex.conj_im, abs_neg]
  exact h

/-- Weight bound on the upper copy: `‖w‖ ≤ (C/2π) e^{-2π|Im γ|} ‖γ'‖`. -/
theorem norm_wUpP_le (hC : Fr.ContourOK) (N0 : ℕ) {pts : List ℂ} {d : ℂ}
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖wUpP Fr N0 pts d u‖ ≤ CP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi)
      * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))
      * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖ := by
  have hE := norm_EC_path hC N0 hlow hd hu
  have h2 : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]; simp
  unfold wUpP
  rw [norm_neg, norm_mul, norm_mul, h2]
  have hpi := Real.pi_pos
  calc 1 / (2 * Real.pi) * (‖Fr.EC (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)‖
        * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖)
      ≤ 1 / (2 * Real.pi) * ((CP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
          * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)))
        * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖) := by
        gcongr
    _ = _ := by ring

/-- Weight bound on the lower copy (same constant, `|Im γ̄| = |Im γ|`, `‖γ̄'‖ = ‖γ'‖`). -/
theorem norm_wLowP_le (hC : Fr.ContourOK) (N0 : ℕ) {pts : List ℂ} {d : ℂ}
    (hlow : ∀ z ∈ pts, 1 / 8 ≤ z.im) (hd : 0 < d.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖wLowP Fr N0 pts d u‖ ≤ CP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d) / (2 * Real.pi)
      * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))
      * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖ := by
  have hE := norm_EC_path_lower hC N0 hlow hd hu
  rw [conjL_conj_path, Complex.conj_im, abs_neg] at hE
  have h2 : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]; simp
  unfold wLowP
  rw [norm_mul, norm_mul, h2, conjL_conj_der, Complex.norm_conj, conjL_conj_path]
  have hpi := Real.pi_pos
  calc 1 / (2 * Real.pi) * (‖Fr.EC (starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u))‖
        * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖)
      ≤ 1 / (2 * Real.pi) * ((CP Fr (qFirst ((Fr.xstar N0 : ℝ) : ℂ) pts d)
          * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|)))
        * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖) := by
        gcongr
    _ = _ := by ring

/-! ### Node distance and growth -/

/-- **Node distance**: every path point keeps distance `≥ 1` from `[0, ∞)`. -/
theorem path_node_dist {v : ℂ} (hv : v.im = 0) {pts : List ℂ} {d : ℂ}
    (hone : ∀ z ∈ pts, 1 ≤ z.im) (hd : 0 < d.im)
    (hfar : v.re + |qFirst v pts d| ≤ -1) {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ ‖pathPt d v pts u - (x : ℂ)‖ := by
  set z := pathPt d v pts u with hz
  have nre := Complex.abs_re_le_norm (z - (x : ℂ))
  have nim := Complex.abs_im_le_norm (z - (x : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at nre nim
  by_cases h1 : 1 ≤ z.im
  · linarith [le_abs_self z.im]
  · push_neg at h1
    rcases path_point_cases hv pts hone hd.le hu with h | ⟨t, ht, he⟩
    · linarith
    · set e := firstDir v pts d
      have hpos : 0 < e.im := firstDir_im_pos hv (fun z hz => by linarith [hone z hz]) hd
      have hzi : z.im = t * e.im := by rw [hz, he]; simp [hv]
      have hzr : z.re = v.re + qFirst v pts d * (t * e.im) := by
        rw [hz, he]; simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        change v.re + t * e.re = v.re + e.re / e.im * (t * e.im)
        field_simp
      have hy0 : 0 ≤ t * e.im := mul_nonneg ht hpos.le
      have hy1 : t * e.im ≤ 1 := by linarith
      have hq : qFirst v pts d * (t * e.im) ≤ |qFirst v pts d| := by
        calc qFirst v pts d * (t * e.im) ≤ |qFirst v pts d * (t * e.im)| := le_abs_self _
          _ = |qFirst v pts d| * (t * e.im) := by rw [abs_mul, abs_of_nonneg hy0]
          _ ≤ |qFirst v pts d| * 1 := mul_le_mul_of_nonneg_left hy1 (abs_nonneg _)
          _ = _ := mul_one _
      have : z.re ≤ -1 := by linarith
      have : 1 ≤ |z.re - x| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      linarith

/-- Node distance on the lower path (by conjugation). -/
theorem path_node_dist_lower {v : ℝ} {pts : List ℂ} {d : ℂ}
    (hone : ∀ z ∈ pts, 1 ≤ z.im) (hd : 0 < d.im)
    (hfar : v + |qFirst (v : ℂ) pts d| ≤ -1) {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ ‖pathPt (starRingEnd ℂ d) (v : ℂ) (conjL pts) u - (x : ℂ)‖ := by
  have e := pathPt_conj d pts (v : ℂ) u
  rw [Complex.conj_ofReal] at e
  unfold conjL
  rw [e, ← Complex.conj_ofReal x, ← map_sub, Complex.norm_conj]
  exact path_node_dist (by simp) hone hd (by simpa using hfar) hu hx

/-- **Growth bound**: `|z| ≤ V + 2|Im z|` along the path, if all vertices have norm `≤ V`, all
heights are nonnegative and the tail has slope `≥ 1`. -/
theorem path_growth {v : ℂ} (hv : v.im = 0) {pts : List ℂ} {d : ℂ} {V : ℝ}
    (hV : ∀ z ∈ v :: pts, ‖z‖ ≤ V) (hpts : ∀ z ∈ pts, 0 ≤ z.im) (hslope : |d.re| ≤ d.im)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖pathPt d v pts u‖ ≤ V + 2 * |(pathPt d v pts u).im| := by
  rcases pathPt_mem d pts v hu with h | ⟨t, ht, he⟩
  · have hs := chainSet_sub_convex (convex_closedBall (0 : ℂ) V) pts v
      (by rw [mem_closedBall_zero_iff]; exact hV v (by simp))
      (fun z hz => by rw [mem_closedBall_zero_iff]; exact hV z (by simp [hz])) h
    rw [mem_closedBall_zero_iff] at hs
    linarith [abs_nonneg (pathPt d v pts u).im]
  · rw [he]
    set L := (v :: pts).getLast (List.cons_ne_nil v pts)
    have hLm : L ∈ v :: pts := List.getLast_mem _
    have hL : ‖L‖ ≤ V := hV L hLm
    have hLi : 0 ≤ L.im := by
      rcases List.mem_cons.1 hLm with h | h
      · rw [h, hv]
      · exact hpts L h
    have hd0 : 0 ≤ d.im := (abs_nonneg _).trans hslope
    have hdn : ‖d‖ ≤ 2 * d.im := by
      have := Complex.norm_le_abs_re_add_abs_im d
      rw [abs_of_nonneg hd0] at this; linarith
    have him : (L + (t : ℂ) * d).im = L.im + t * d.im := im_ray L d t
    have h1 : ‖L + (t : ℂ) * d‖ ≤ ‖L‖ + t * ‖d‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
    have h2 : 2 * (t * d.im) ≤ 2 * |(L + (t : ℂ) * d).im| := by
      rw [him]; have := le_abs_self (L.im + t * d.im); nlinarith
    nlinarith

end CatalanCore.Uniform.Decay.Polygon
