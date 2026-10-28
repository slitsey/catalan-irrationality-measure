module

public import CatalanCore.Uniform.Decay.PolyCells.Facts

@[expose] public section

/-!
# Per-edge tube cells of the polygon (lane D, package D9)

`normSet P` (the normalised polygon `Γ`) is the union of the finite edges
`(-r0,0) → p_1 → … → p_m` and the NW tail `p_m + t(-1 + is)`, `t ≥ 0`.  The tube rule covers
`Γ`, with `|δ| ≤ W`, by *cells*: a cell is a parameter interval `[α, β] ⊆ [0,1]` on one
*rational segment* `e = (a, b)`, i.e. the points `a + t (b - a)`, `t ∈ [α, β]`.  The tail is the
finite segment `(p_m, p_m + tmax(-1,s))` plus the far remainder `t ≥ tmax`.

* `cellFarOk` (port of D6's `rayFarOk` to an arbitrary segment, generic in the endpoints): the
  cell lies in `Im z ≥ T` with `T = min (Im at α) (Im at β)`, and `farOk` (mass cancellation,
  `m' ≤ (1-ε)π T - 2M₁/T`) holds.  `cellFar_sound` is valid for every real shift `δ`.
* `SegNearOracle` (filled by D6b): cells not far.
* `tubeCheck`: the Boolean test; `tubeCheck_sound`: `m' ≤ g(w + δ)` for all `w ∈ Γ`, `|δ| ≤ W`.
-/

namespace CatalanCore.Uniform.Decay.PolyCells

open Set CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Assembly
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyChain

abbrev Pt := ℚ × ℚ

/-- The point `a + t (b - a)` of the rational segment `e = (a, b)`. -/
def segPtC (e : Pt × Pt) (t : ℝ) : ℂ := vertC e.1 + (t : ℂ) * (vertC e.2 - vertC e.1)

/-- Imaginary part of the segment point at rational parameter `t`. -/
def segIm (e : Pt × Pt) (t : ℚ) : ℚ := e.1.2 + t * (e.2.2 - e.1.2)

/-- Edges of the chain `a → l`. -/
def edgesOf : Pt → List Pt → List (Pt × Pt)
  | _, [] => []
  | a, b :: l => (a, b) :: edgesOf b l

/-- Last point of the chain `a → l`. -/
def lastPt : Pt → List Pt → Pt
  | a, [] => a
  | _, b :: l => lastPt b l

/-- Base point `(-r0, 0)` of the normalised polygon. -/
def basePt (P : RatPolygon) : Pt := (-P.r0, 0)

/-- End point of the finite tail segment: `p_m + tmax (-1, s)`. -/
def tailEnd (P : RatPolygon) (tmax : ℚ) : Pt :=
  ((lastPt (basePt P) P.verts).1 - tmax, (lastPt (basePt P) P.verts).2 + P.s * tmax)

/-- All finite segments of the tube: the polygon edges and the finite tail segment. -/
def edgesAll (P : RatPolygon) (tmax : ℚ) : List (Pt × Pt) :=
  edgesOf (basePt P) P.verts ++ [(lastPt (basePt P) P.verts, tailEnd P tmax)]

/-! ### Geometry of `normSet` -/

theorem base_eq (P : RatPolygon) : ((((-(P.r0 : ℝ)) : ℝ) : ℂ)) = vertC (basePt P) := by
  apply Complex.ext <;> simp [vertC, basePt]

theorem getLast_map_vertC : ∀ (l : List Pt) (c : ℂ) (a : Pt) (_ : c = vertC a)
    (h : c :: l.map vertC ≠ []), (c :: l.map vertC).getLast h = vertC (lastPt a l)
  | [], c, a, hc, h => by simp [lastPt, hc]
  | b :: l, c, a, hc, h => by
      simp only [List.map_cons]
      rw [List.getLast_cons (by simp)]
      exact getLast_map_vertC l _ b rfl _

theorem segment_param {x y w : ℂ} (hw : w ∈ segment ℝ x y) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ w = x + (t : ℂ) * (y - x) := by
  rw [segment_eq_image'] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨t, ht.1, ht.2, by simp [Complex.real_smul]⟩

theorem chainSet_edges : ∀ (l : List Pt) (a : Pt) {w : ℂ}, w ∈ chainSet (vertC a) (l.map vertC) →
    ∃ e ∈ edgesOf a l, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ w = segPtC e t
  | [], a, w, hw => by simp [chainSet] at hw
  | b :: l, a, w, hw => by
      simp only [List.map_cons, chainSet] at hw
      rcases hw with hw | hw
      · obtain ⟨t, h0, h1, rfl⟩ := segment_param hw
        exact ⟨(a, b), by simp [edgesOf], t, h0, h1, rfl⟩
      · obtain ⟨e, he, t, h0, h1, rfl⟩ := chainSet_edges l b hw
        exact ⟨e, by simp [edgesOf, he], t, h0, h1, rfl⟩

/-- The tail point `L + t(-1 + is)` of the finite tail segment, `0 < tmax`, `t ≤ tmax`. -/
theorem tail_seg {P : RatPolygon} {tmax : ℚ} (htm : 0 < tmax) (t : ℝ) :
    vertC (lastPt (basePt P) P.verts) + (t : ℂ) * P.tailDir
      = segPtC (lastPt (basePt P) P.verts, tailEnd P tmax) (t / tmax) := by
  have hne : (tmax : ℝ) ≠ 0 := by exact_mod_cast htm.ne'
  apply Complex.ext <;> simp [segPtC, vertC, tailEnd, RatPolygon.tailDir] <;> field_simp

/-! ### Cells -/

/-- Far cell: `Im z ≥ T` on the whole cell (`T` = least endpoint value), `farOk` at `T`. -/
def cellFarOk (D : SplineData) (F : FarData) (e : Pt × Pt) (c : ℚ × ℚ) : Bool :=
  farOk D F (min (segIm e c.1) (segIm e c.2))

theorem cellFar_sound {D : SplineData} {Vnu : ℂ → ℝ} {F : FarData} (H : FarHyp D Vnu F)
    (B : SplineData.BasicFacts D) {e : Pt × Pt} {c : ℚ × ℚ} (h : cellFarOk D F e c = true)
    (t : ℝ) (h1 : (c.1 : ℝ) ≤ t) (h2 : t ≤ (c.2 : ℝ)) (δ : ℝ) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  refine far_g_ge H B h _ ?_
  have him : (segPtC e t + (δ : ℂ)).im = (e.1.2 : ℝ) + t * ((e.2.2 : ℝ) - e.1.2) := by
    simp [segPtC, vertC]
  rw [him]
  have hα : (((min (segIm e c.1) (segIm e c.2) : ℚ)) : ℝ) ≤
      (e.1.2 : ℝ) + c.1 * ((e.2.2 : ℝ) - e.1.2) := by
    have := (Rat.cast_le (K := ℝ)).2 (min_le_left (segIm e c.1) (segIm e c.2))
    simp only [segIm] at this ⊢
    push_cast at this ⊢
    linarith
  have hβ : (((min (segIm e c.1) (segIm e c.2) : ℚ)) : ℝ) ≤
      (e.1.2 : ℝ) + c.2 * ((e.2.2 : ℝ) - e.1.2) := by
    have := (Rat.cast_le (K := ℝ)).2 (min_le_right (segIm e c.1) (segIm e c.2))
    simp only [segIm] at this ⊢
    push_cast at this ⊢
    linarith
  rcases le_total (0 : ℝ) ((e.2.2 : ℝ) - e.1.2) with hd | hd
  · nlinarith [mul_le_mul_of_nonneg_right h1 hd]
  · nlinarith [mul_le_mul_of_nonpos_right h2 hd]

/-- Oracle for cells that are not far: the potential bound on the `W`-tube of a segment cell. -/
structure SegNearOracle (Vnu : ℂ → ℝ) where
  segNear : SplineData → Pt × Pt → ℚ × ℚ → Bool
  sound : ∀ D : SplineData, D.basicOk = true → ∀ e c, segNear D e c = true → ∀ t : ℝ,
    (c.1 : ℝ) ≤ t → t ≤ (c.2 : ℝ) → ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ))

/-- One cell: far or near. -/
def cellOk {Vnu : ℂ → ℝ} (N : SegNearOracle Vnu) (F : FarData) (D : SplineData) (e : Pt × Pt)
    (c : ℚ × ℚ) : Bool :=
  cellFarOk D F e c || N.segNear D e c

/-- The cells of one edge cover the parameter interval `[0,1]`, and each is ok. -/
def edgeCellsOk (ok : Pt × Pt → ℚ × ℚ → Bool) (e : Pt × Pt) (cs : List (ℚ × ℚ)) : Bool :=
  coverOk 0 1 cs && cs.all (ok e)

/-- Edge by edge. -/
def tubeCellsOk (ok : Pt × Pt → ℚ × ℚ → Bool) : List (Pt × Pt) → List (List (ℚ × ℚ)) → Bool
  | [], [] => true
  | e :: es, cs :: css => edgeCellsOk ok e cs && tubeCellsOk ok es css
  | _, _ => false

theorem tubeCellsOk_sound {ok : Pt × Pt → ℚ × ℚ → Bool} {Q : Pt × Pt → ℝ → Prop}
    (hQ : ∀ e c, ok e c = true → ∀ t : ℝ, (c.1 : ℝ) ≤ t → t ≤ (c.2 : ℝ) → Q e t) :
    ∀ (es : List (Pt × Pt)) (css : List (List (ℚ × ℚ))), tubeCellsOk ok es css = true →
      ∀ e ∈ es, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Q e t
  | [], [], _, e, he, _, _, _ => by simp at he
  | [], _ :: _, h, _, _, _, _, _ => by simp [tubeCellsOk] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [tubeCellsOk] at h
  | e0 :: es, cs :: css, h, e, he, t, ht0, ht1 => by
      simp only [tubeCellsOk, edgeCellsOk, Bool.and_eq_true] at h
      obtain ⟨⟨hcov, hall⟩, hrest⟩ := h
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨c, hc, h1, h2⟩ := coverOk_sound hcov t (by simpa using ht0) (by simpa using ht1)
        exact hQ _ c (List.all_eq_true.1 hall c hc) t h1 h2
      · exact tubeCellsOk_sound hQ es css hrest e he t ht0 ht1

/-- **The tube test.**  `tmax > 0`, `s ≥ 0`; `tcells` = one cell list per element of
`edgesAll P tmax`; the tail beyond `tmax` is far. -/
def tubeCheck {Vnu : ℂ → ℝ} (N : SegNearOracle Vnu) (F : FarData) (tmax : ℚ)
    (tcells : List (List (ℚ × ℚ))) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) && tubeCellsOk (cellOk N F D) (edgesAll P tmax) tcells &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheck_sound {Vnu : ℂ → ℝ} (N : SegNearOracle Vnu) {F : FarData} {tmax : ℚ}
    {tcells : List (List (ℚ × ℚ))} {D : SplineData} {P : RatPolygon}
    (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (h : tubeCheck N F tmax tcells D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htm, hs⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeCellsOk_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => by
      rcases Bool.or_eq_true_iff.1 hc with hc | hc
      · exact cellFar_sound H B hc t h1 h2 δ
      · exact N.sound D hb e c hc t h1 h2 δ hδ) _ _ hcells
  intro w hw δ hδ
  rcases hw with hw | hw
  · rw [base_eq] at hw
    obtain ⟨e, he, t, h0, h1, rfl⟩ := chainSet_edges P.verts (basePt P) hw
    exact key e (List.mem_append_left _ he) t h0 h1 δ hδ
  · obtain ⟨t, ht0, rfl⟩ := hw
    have hL := getLast_map_vertC P.verts _ (basePt P) (base_eq P) (List.cons_ne_nil _ _)
    rw [hL]
    by_cases hle : t ≤ tmax
    · rw [tail_seg htm]
      have htm' : (0 : ℝ) < tmax := by exact_mod_cast htm
      refine key _ (List.mem_append_right _ (List.mem_singleton_self _)) _
        (div_nonneg ht0 htm'.le) ((div_le_one htm').2 hle) δ hδ
    · push Not at hle
      refine far_g_ge H B hfar _ ?_
      have him : (vertC (lastPt (basePt P) P.verts) + (t : ℂ) * P.tailDir + (δ : ℂ)).im
          = ((lastPt (basePt P) P.verts).2 : ℝ) + t * (P.s : ℝ) := by
        simp [vertC, RatPolygon.tailDir]
      rw [him]
      have hs' : (0 : ℝ) ≤ P.s := by exact_mod_cast hs
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hle.le hs']

end CatalanCore.Uniform.Decay.PolyCells
