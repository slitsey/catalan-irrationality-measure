import CatalanCore.Uniform.Decay.Breakpoint.Cell
import CatalanCore.Uniform.Decay.FarField.Cell
import CatalanCore.Uniform.Decay.FarField.CapPL
import CatalanCore.Uniform.Decay.FarField.LinJet
import CatalanCore.Uniform.Decay.PolyWire2.Top2
set_option Elab.async false

/-!
# One cell-kind inductive for every proved decay cell (lane D, package D17)

`CellKind` contains all proved kinds: `base k` (PolyWire2's `jetF` / `mixF` / `far`), `bp`
(the breakpoint cell of `Breakpoint.Cell`) and `mp` (the far-field multipole cell of
`FarField.Cell`).  `kindOk_sound` only cites `kindOk2_sound`, `bpOk_sound`, `mpCellOk_sound`.
The multipole data is an `Option MPData`: `none` for banks that do not use it (the global test is
then trivial and an `mp` cell never passes).  The tube / line / cap statements are those of
`FarField.Kinds3` and `FarField.PLKinds` with this one type.
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyWire2
open CatalanCore.Uniform.Decay.Breakpoint (bpOk bpOk_sound)
open CatalanCore.Uniform.Decay.FarField (MPData mpGlobalOk mpCellOk mpCellOk_sound cellOkFL cellOkFL_sound
  PLCell plLine plChain plSum plCapOkOf plCapOkOf_sound)

/-- All proved cell kinds.  `bp n side lo C Fs eS` is `bpOk`, `mp rm rh` is `mpCellOk`. -/
inductive CellKind where
  | base (k : CellKind2)
  | bp (n : ℕ) (side : Bool) (lo : ℚ) (C : List ℚ) (Fs : ℚ) (eS : ℕ)
  | mp (rm rh : ℚ)

/-- A cell `[ulo, uhi]` with its kind. -/
structure TCell where
  ulo : ℚ
  uhi : ℚ
  kind : CellKind

/-- The (once per table) global test of the multipole data; trivial without it. -/
def globalOk (ps : List WP) : Option MPData → Bool
  | none => true
  | some M => mpGlobalOk ps M

/-- The Boolean test of one cell of centre `zc`, direction `dd`, half-width `h`. -/
def kindOk (ps : List WP) (M : Option MPData) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ) :
    CellKind → Bool
  | .base k => kindOk2 ps zc dd h W Rtwo cpi m' eW eP k
  | .bp n side lo C Fs eS => bpOk n side ps zc dd h W Rtwo cpi lo m' C Fs eW eP eS
  | .mp rm rh => match M with
      | none => false
      | some M0 => mpCellOk M0 zc dd h W cpi m' rm rh

theorem kindOk_sound {ps : List WP} {M : Option MPData} (hG : globalOk ps M = true) {zc dd : CQ}
    {h W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind}
    (hc : kindOk ps M zc dd h W Rtwo cpi m' eW eP k = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  cases k with
  | base k => (simp only [kindOk] at hc; exact kindOk2_sound hc s δ hs hδ)
  | bp n side lo C Fs eS => (simp only [kindOk] at hc; exact bpOk_sound hc s δ hs hδ)
  | mp rm rh =>
    cases M with
    | none => (simp only [kindOk] at hc; cases hc)
    | some M0 => (simp only [kindOk] at hc; exact mpCellOk_sound hG hc s δ hs hδ)

/-! ### Tube cells -/

def nearCellT (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (e : Pt × Pt)
    (c : TCell) : Bool :=
  decide (D.ε < 1) &&
    kindOk (cellPieces D nu) M (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi)
      (CQ.sub (cqOf e.2) (cqOf e.1)) ((c.uhi - c.ulo) / 2) D.W Rtwo (cpiOf D) D.mprime eW eP c.kind

theorem nearCellT_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : globalOk (cellPieces D nu) M = true)
    (e : Pt × Pt) (c : TCell) (h : nearCellT nu M Rtwo eW eP D e c = true)
    (t : ℝ) (h1 : (c.ulo : ℝ) ≤ t) (h2 : t ≤ (c.uhi : ℝ)) (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  unfold nearCellT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hm⟩ := h
  have key := kindOk_sound hG hm (t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ)) δ (by
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

def cellOk (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (D : SplineData)
    (e : Pt × Pt) (c : TCell) : Bool :=
  cellFarOk D F e (c.ulo, c.uhi) || nearCellT nu M Rtwo eW eP D e c

def edgeCells (ok : Pt × Pt → TCell → Bool) (e : Pt × Pt) (cs : List TCell) : Bool :=
  coverOk 0 1 (cs.map fun c => (c.ulo, c.uhi)) && cs.all (ok e)

def tubeCells (ok : Pt × Pt → TCell → Bool) : List (Pt × Pt) → List (List TCell) → Bool
  | [], [] => true
  | e :: es, cs :: css => edgeCells ok e cs && tubeCells ok es css
  | _, _ => false

theorem tubeCells_sound {ok : Pt × Pt → TCell → Bool} {Q : Pt × Pt → ℝ → Prop}
    (hQ : ∀ e (c : TCell), ok e c = true → ∀ t : ℝ, (c.ulo : ℝ) ≤ t → t ≤ (c.uhi : ℝ) → Q e t) :
    ∀ (es : List (Pt × Pt)) (css : List (List TCell)), tubeCells ok es css = true →
      ∀ e ∈ es, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Q e t
  | [], [], _, e, he, _, _, _ => by simp at he
  | [], _ :: _, h, _, _, _, _, _ => by simp [tubeCells] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [tubeCells] at h
  | e0 :: es, cs :: css, h, e, he, t, ht0, ht1 => by
      simp only [tubeCells, edgeCells, Bool.and_eq_true] at h
      obtain ⟨⟨hcov, hall⟩, hrest⟩ := h
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨p, hp, h1, h2⟩ := coverOk_sound hcov t (by simpa using ht0) (by simpa using ht1)
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
        exact hQ _ c (List.all_eq_true.1 hall c hc) t h1 h2
      · exact tubeCells_sound hQ es css hrest e he t ht0 ht1

/-- **The tube test.** -/
def tubeCheck (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (tmax : ℚ)
    (tube : List (List TCell)) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) &&
    tubeCells (cellOk nu M Rtwo eW eP F D) (edgesAll P tmax) tube &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheck_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {tmax : ℚ} {tube : List (List TCell)}
    {D : SplineData} {P : RatPolygon} (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (hG : globalOk (cellPieces D nu) M = true)
    (h : tubeCheck nu M Rtwo eW eP F tmax tube D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htm, hs⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeCells_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => by
      rcases Bool.or_eq_true_iff.1 hc with hc | hc
      · exact cellFar_sound H B hc t h1 h2 δ
      · exact nearCellT_sound nu M Rtwo eW eP hV D hG e c hc t h1 h2 δ hδ) _ _ hcells
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

def lineCellOk (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell) :
    Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk (cellPieces D nu) M ⟨(c.ulo + c.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.uhi - c.ulo) / 2) D.W Rtwo
      (cpiOf D) D.gmin eW eP c.kind

theorem realCell_sound {ps : List WP} {M : Option MPData} (hG : globalOk ps M = true)
    {a b W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind} (hW : 0 ≤ W)
    (hc : kindOk ps M ⟨(a + b) / 2, 0⟩ ⟨1, 0⟩ ((b - a) / 2) W Rtwo cpi m' eW eP k = true)
    (x : ℝ) (hx1 : (a : ℝ) ≤ x) (hx2 : x ≤ (b : ℝ)) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (⟨x, 0⟩ : ℂ))).sum
      + (cpi : ℝ) * |(⟨x, 0⟩ : ℂ).im| := by
  have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW
  have key := kindOk_sound hG hc (x - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
    rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
  have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
    apply Complex.ext <;> simp [CQ.toC]
  rw [hz] at key
  exact key

theorem lineCellOk_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : globalOk (cellPieces D nu) M = true)
    (c : TCell) (h : lineCellOk nu M Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.ulo : ℝ) ≤ x → x ≤ c.uhi →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineCellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell_sound hG hW hm x hx1 hx2)

/-! ### Cap lower bounds and upper bounds -/

def capCellOk (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (c : TCell × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk (cellPieces D nu) M ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo
      (cpiOf D) c.2 eW eP c.1.kind

theorem capCellOk_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : globalOk (cellPieces D nu) M = true)
    (c : TCell × ℚ) (h : capCellOk nu M Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      (c.2 : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold capCellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell_sound hG hW hm x hx1 hx2)

/-- Cap cell with an UPPER bound `ub` of `g`, through the negated pieces.  The far-field cell
applies to the negated list as well: its global data `M'` is the data of `cellPieces D nu` mapped
by `negW` (use `globalOk ((cellPieces D nu).map negW) M'`). -/
def ubCellOk (nu : List Seg) (M' : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (c : TCell × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk ((cellPieces D nu).map negW) M' ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩
      ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo 0 (-c.2) eW eP c.1.kind

theorem ubCellOk_sound (nu : List Seg) (M' : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hG : globalOk ((cellPieces D nu).map negW) M' = true)
    (c : TCell × ℚ) (h : ubCellOk nu M' Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ (c.2 : ℝ) := by
  intro x hx1 hx2
  unfold ubCellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  have key := realCell_sound hG hW hm x hx1 hx2
  rw [negW_sum] at key
  rw [gNu_eq D nu hV]
  have him : (⟨x, 0⟩ : ℂ).im = 0 := rfl
  rw [him] at key ⊢
  simp only [abs_zero, mul_zero, add_zero, neg_neg, Rat.cast_neg, Rat.cast_zero] at key ⊢
  linarith

/-! ### Cap cells with a piecewise-linear majorant -/

inductive PLKind where
  | const (k : TCell × ℚ)
  | lin (n : ℕ) (lo : ℚ) (C : List ℚ) (Fs : ℚ)

structure PLCap where
  cell : PLCell
  kind : PLKind

/-- The Boolean of one PL cap cell (upper bound of `g` by the chord); `M'` is the multipole data of
the negated pieces. -/
def plUbOk (nu : List Seg) (M' : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (x : PLCap) :
    Bool :=
  match x.kind with
  | .const k =>
      decide (x.cell = (k.1.ulo, k.1.uhi, k.2, k.2)) && ubCellOk nu M' Rtwo eW eP D k
  | .lin n lo C Fs =>
      decide (D.ε < 1) && decide (0 ≤ D.W) && decide (x.cell.1 < x.cell.2.1) &&
        cellOkFL n ((cellPieces D nu).map negW) ⟨(x.cell.1 + x.cell.2.1) / 2, 0⟩ ⟨1, 0⟩
          ((x.cell.2.1 - x.cell.1) / 2) D.W Rtwo 0 lo 0 C Fs eW eP
          ((x.cell.2.2.1 + x.cell.2.2.2) / 2)
          ((x.cell.2.2.2 - x.cell.2.2.1) / (x.cell.2.1 - x.cell.1))

theorem plUbOk_sound (nu : List Seg) (M' : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hG : globalOk ((cellPieces D nu).map negW) M' = true) (x : PLCap)
    (h : plUbOk nu M' Rtwo eW eP D x = true) :
    ∀ y : ℝ, (x.cell.1 : ℝ) ≤ y → y ≤ x.cell.2.1 →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨y, 0⟩ ≤ plLine x.cell y := by
  intro y hy1 hy2
  unfold plUbOk at h
  rcases x with ⟨⟨a, b, ua, ub⟩, k⟩
  cases k with
  | const k =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcell, hok⟩ := h
    simp only [Prod.mk.injEq] at hcell
    obtain ⟨h1, h2, h3, h4⟩ := hcell
    have := ubCellOk_sound nu M' Rtwo eW eP hV D hG k hok y (by simp only at hy1; rw [← h1]; exact hy1)
      (by simp only at hy2; rw [← h2]; exact hy2)
    unfold plLine
    simp only
    subst h3; subst h4
    simpa using this
  | lin n lo C Fs =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hε, hW⟩, hab⟩, hc⟩ := h
    simp only at hy1 hy2 hab hc
    have hWR : (0 : ℝ) ≤ D.W := by exact_mod_cast hW
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have key := cellOkFL_sound hc (y - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
      rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hWR)
    have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((y - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
        (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨y, 0⟩ := by
      apply Complex.ext <;> simp [CQ.toC]
    rw [hz, negW_sum] at key
    rw [gNu_eq D nu hV]
    have him : (⟨y, 0⟩ : ℂ).im = 0 := rfl
    rw [him] at key ⊢
    simp only [abs_zero, mul_zero, add_zero, Rat.cast_zero, zero_mul, zero_add] at key ⊢
    unfold plLine
    simp only
    have hba : (b : ℝ) - a ≠ 0 := by linarith
    have e : (((ua + ub) / 2 : ℚ) : ℝ) + (((ub - ua) / (b - a) : ℚ) : ℝ) * (y - (((a + b) / 2 : ℚ) : ℝ))
        = (ua : ℝ) + ((ub : ℝ) - ua) * (y - a) / ((b : ℝ) - a) := by
      push_cast
      field_simp
      ring
    rw [e] at key
    linarith

/-- A constant upper-bound cell as a PL cell. -/
def PLCap.ofConst (k : TCell × ℚ) : PLCap := ⟨(k.1.ulo, k.1.uhi, k.2, k.2), .const k⟩

theorem plUbOk_ofConst (nu : List Seg) (M' : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (k : TCell × ℚ) (h : ubCellOk nu M' Rtwo eW eP D k = true) :
    plUbOk nu M' Rtwo eW eP D (PLCap.ofConst k) = true := by
  simp [plUbOk, PLCap.ofConst, h]

end CatalanCore.Uniform.Decay.PolyWire3
