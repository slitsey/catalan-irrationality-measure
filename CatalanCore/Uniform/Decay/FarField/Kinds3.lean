import CatalanCore.Uniform.Decay.PolyWire2.Top2
import CatalanCore.Uniform.Decay.FarField.Cell
set_option Elab.async false

/-!
# Cell kinds with the far-field cell (lane D, package D15)

An extension of `PolyWire2.Kinds` that changes no accepted file.  `CellKind3.base k` is any cell
kind of `PolyWire2`; `CellKind3.mp rm rh` is the far-field cell `mpCellOk`.  The tube, line and
cap cell Booleans mirror `PolyWire2.cellOk2 / lineCellOk2 / capCellOk2 / ubCellOk2`; the soundness
statements are the same, with the extra hypothesis `mpGlobalOk (cellPieces D nu) M = true`
(checked once per table).
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyWire2

/-- Cell kinds: any `PolyWire2` kind, or the far-field cell (`rm`, `rh` as in `mpCellOk`). -/
inductive CellKind3 where
  | base (k : CellKind2)
  | mp (rm rh : ℚ)

structure TCell3 where
  ulo : ℚ
  uhi : ℚ
  kind : CellKind3

/-- The Boolean test of one cell of centre `zc`, direction `dd`, half-width `h`. -/
def kindOk3 (ps : List WP) (M : MPData) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ) :
    CellKind3 → Bool
  | .base k => kindOk2 ps zc dd h W Rtwo cpi m' eW eP k
  | .mp rm rh => mpCellOk M zc dd h W cpi m' rm rh

theorem kindOk3_sound {ps : List WP} {M : MPData} (hG : mpGlobalOk ps M = true) {zc dd : CQ}
    {h W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind3}
    (hc : kindOk3 ps M zc dd h W Rtwo cpi m' eW eP k = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  cases k with
  | base k => (simp only [kindOk3] at hc; exact kindOk2_sound hc s δ hs hδ)
  | mp rm rh => (simp only [kindOk3] at hc; exact mpCellOk_sound hG hc s δ hs hδ)

/-! ### Tube cells -/

def nearCellT3 (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (e : Pt × Pt)
    (c : TCell3) : Bool :=
  decide (D.ε < 1) &&
    kindOk3 (cellPieces D nu) M (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi)
      (CQ.sub (cqOf e.2) (cqOf e.1)) ((c.uhi - c.ulo) / 2) D.W Rtwo (cpiOf D) D.mprime eW eP c.kind

theorem nearCellT3_sound (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : mpGlobalOk (cellPieces D nu) M = true)
    (e : Pt × Pt) (c : TCell3) (h : nearCellT3 nu M Rtwo eW eP D e c = true)
    (t : ℝ) (h1 : (c.ulo : ℝ) ≤ t) (h2 : t ≤ (c.uhi : ℝ)) (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  unfold nearCellT3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hm⟩ := h
  have key := kindOk3_sound hG hm (t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ)) δ (by
    rw [abs_le]; push_cast; constructor <;> linarith) hδ
  have ez : (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi).toC +
      ((t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ) : ℝ) : ℂ) * (CQ.sub (cqOf e.2) (cqOf e.1)).toC
      + (δ : ℂ) = segPtC e t + (δ : ℂ) := by
    unfold edgeCentre
    rw [CQ.toC_add, CQ.toC_smul, CQ.toC_sub, cqOf_toC, cqOf_toC]
    unfold segPtC
    push_cast; ring
  rw [ez] at key
  exact gNu_ge_of D nu hV hε key

def cellOk3 (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (D : SplineData)
    (e : Pt × Pt) (c : TCell3) : Bool :=
  cellFarOk D F e (c.ulo, c.uhi) || nearCellT3 nu M Rtwo eW eP D e c

def edgeCells3 (ok : Pt × Pt → TCell3 → Bool) (e : Pt × Pt) (cs : List TCell3) : Bool :=
  coverOk 0 1 (cs.map fun c => (c.ulo, c.uhi)) && cs.all (ok e)

def tubeCells3 (ok : Pt × Pt → TCell3 → Bool) : List (Pt × Pt) → List (List TCell3) → Bool
  | [], [] => true
  | e :: es, cs :: css => edgeCells3 ok e cs && tubeCells3 ok es css
  | _, _ => false

theorem tubeCells3_sound {ok : Pt × Pt → TCell3 → Bool} {Q : Pt × Pt → ℝ → Prop}
    (hQ : ∀ e (c : TCell3), ok e c = true → ∀ t : ℝ, (c.ulo : ℝ) ≤ t → t ≤ (c.uhi : ℝ) → Q e t) :
    ∀ (es : List (Pt × Pt)) (css : List (List TCell3)), tubeCells3 ok es css = true →
      ∀ e ∈ es, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Q e t
  | [], [], _, e, he, _, _, _ => by simp at he
  | [], _ :: _, h, _, _, _, _, _ => by simp [tubeCells3] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [tubeCells3] at h
  | e0 :: es, cs :: css, h, e, he, t, ht0, ht1 => by
      simp only [tubeCells3, edgeCells3, Bool.and_eq_true] at h
      obtain ⟨⟨hcov, hall⟩, hrest⟩ := h
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨p, hp, h1, h2⟩ := coverOk_sound hcov t (by simpa using ht0) (by simpa using ht1)
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
        exact hQ _ c (List.all_eq_true.1 hall c hc) t h1 h2
      · exact tubeCells3_sound hQ es css hrest e he t ht0 ht1

/-- **The tube test.** -/
def tubeCheck3 (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (tmax : ℚ)
    (tube : List (List TCell3)) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) &&
    tubeCells3 (cellOk3 nu M Rtwo eW eP F D) (edgesAll P tmax) tube &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheck3_sound (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {tmax : ℚ} {tube : List (List TCell3)}
    {D : SplineData} {P : RatPolygon} (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (hG : mpGlobalOk (cellPieces D nu) M = true)
    (h : tubeCheck3 nu M Rtwo eW eP F tmax tube D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheck3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htm, hs⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeCells3_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => by
      rcases Bool.or_eq_true_iff.1 hc with hc | hc
      · exact cellFar_sound H B hc t h1 h2 δ
      · exact nearCellT3_sound nu M Rtwo eW eP hV D hG e c hc t h1 h2 δ hδ) _ _ hcells
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

/-! ### Line cells -/

def lineCellOk3 (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell3) :
    Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk3 (cellPieces D nu) M ⟨(c.ulo + c.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.uhi - c.ulo) / 2) D.W Rtwo
      (cpiOf D) D.gmin eW eP c.kind

theorem realCell3_sound {ps : List WP} {M : MPData} (hG : mpGlobalOk ps M = true)
    {a b W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind3} (hW : 0 ≤ W)
    (hc : kindOk3 ps M ⟨(a + b) / 2, 0⟩ ⟨1, 0⟩ ((b - a) / 2) W Rtwo cpi m' eW eP k = true)
    (x : ℝ) (hx1 : (a : ℝ) ≤ x) (hx2 : x ≤ (b : ℝ)) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (⟨x, 0⟩ : ℂ))).sum
      + (cpi : ℝ) * |(⟨x, 0⟩ : ℂ).im| := by
  have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW
  have key := kindOk3_sound hG hc (x - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
    rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
  have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
    apply Complex.ext <;> simp [CQ.toC]
  rw [hz] at key
  exact key

theorem lineCellOk3_sound (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : mpGlobalOk (cellPieces D nu) M = true)
    (c : TCell3) (h : lineCellOk3 nu M Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.ulo : ℝ) ≤ x → x ≤ c.uhi →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineCellOk3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell3_sound hG hW hm x hx1 hx2)

/-! ### Cap lower bounds and upper bounds -/

def capCellOk3 (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (c : TCell3 × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk3 (cellPieces D nu) M ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo
      (cpiOf D) c.2 eW eP c.1.kind

theorem capCellOk3_sound (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : mpGlobalOk (cellPieces D nu) M = true)
    (c : TCell3 × ℚ) (h : capCellOk3 nu M Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      (c.2 : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold capCellOk3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell3_sound hG hW hm x hx1 hx2)

/-- Cap cell with an UPPER bound `ub` of `g`, through the negated pieces.  The far-field cell
applies to the negated list as well: its global data `M'` is the data of `cellPieces D nu` mapped
by `negW` (use `mpGlobalOk ((cellPieces D nu).map negW) M'`). -/
def ubCellOk3 (nu : List Seg) (M' : MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (c : TCell3 × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk3 ((cellPieces D nu).map negW) M' ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩
      ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo 0 (-c.2) eW eP c.1.kind

theorem ubCellOk3_sound (nu : List Seg) (M' : MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hG : mpGlobalOk ((cellPieces D nu).map negW) M' = true)
    (c : TCell3 × ℚ) (h : ubCellOk3 nu M' Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ (c.2 : ℝ) := by
  intro x hx1 hx2
  unfold ubCellOk3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  have key := realCell3_sound hG hW hm x hx1 hx2
  rw [negW_sum] at key
  rw [gNu_eq D nu hV]
  have him : (⟨x, 0⟩ : ℂ).im = 0 := rfl
  rw [him] at key ⊢
  simp only [abs_zero, mul_zero, add_zero, neg_neg, Rat.cast_neg, Rat.cast_zero] at key ⊢
  linarith

end CatalanCore.Uniform.Decay.FarField
