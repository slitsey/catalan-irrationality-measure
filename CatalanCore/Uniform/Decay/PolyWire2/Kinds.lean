module

public import CatalanCore.Uniform.Decay.PolyWire.Tables
public import CatalanCore.Uniform.Decay.NearFast.Cell

@[expose] public section
set_option Elab.async false

/-!
# Cell kinds with the fast rules and per-cell data (lane B, package B3b)

A thin extension of `PolyWire.Tables`, changing no accepted file.  Differences:
* the cell kinds are the fast rules `cellOkF` / `mixOkF` of D12 (same soundness statements as
  `cellOk'` / `mixOk`), each carrying its own order `n`;
* a cell carries its own kind, so the Boolean of one cell does not look anything up in a table:
  `cellOk2 ... e c` is self contained and can be proved by one `decide +kernel` per cell;
* line and cap cells likewise.
-/

namespace CatalanCore.Uniform.Decay.PolyWire2

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain

/-- Cell kinds: `jetF` is `cellOkF` (order `n`, aggregate `C`, error `Fs`, Bernstein bound `lo`),
`mixF` is `mixOkF` (near pieces selected by `sel`), `far` has no near test. -/
inductive CellKind2 where
  | jetF (n : ℕ) (lo : ℚ) (C : List ℚ) (Fs : ℚ)
  | mixF (n : ℕ) (sel : List Bool) (ρ lo : ℚ) (C : List ℚ) (Fs : ℚ) (eW' eP' : ℕ)
  | far

/-- A cell `[ulo, uhi]` (edge parameter, or real coordinate for line/cap cells) with its kind. -/
structure TCell2 where
  ulo : ℚ
  uhi : ℚ
  kind : CellKind2

/-- The Boolean test of one cell of centre `zc`, direction `dd`, half-width `h`. -/
def kindOk2 (ps : List WP) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ) : CellKind2 → Bool
  | .jetF n lo C Fs => cellOkF n ps zc dd h W Rtwo cpi lo m' C Fs eW eP
  | .mixF n sel ρ lo C Fs eW' eP' =>
      mixOkF n (splitSel ps sel).1 (splitSel ps sel).2 zc dd h ρ W Rtwo cpi lo m' C Fs eW eP eW' eP'
  | .far => false

theorem kindOk2_sound {ps : List WP} {zc dd : CQ} {h W Rtwo cpi m' : ℚ} {eW eP : ℕ}
    {k : CellKind2} (hc : kindOk2 ps zc dd h W Rtwo cpi m' eW eP k = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  cases k with
  | jetF n lo C Fs => (simp only [kindOk2] at hc; exact cellOkF_sound hc s δ hs hδ)
  | mixF n sel ρ lo C Fs eW' eP' =>
      (simp only [kindOk2] at hc; exact mixOkF_sound_perm (splitSel_perm ps sel) hc s δ hs hδ)
  | far => (simp only [kindOk2] at hc; cases hc)

/-! ### Tube cells -/

/-- The near test of the cell `c` of the edge `e`. -/
def nearCellT2 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (e : Pt × Pt) (c : TCell2) :
    Bool :=
  decide (D.ε < 1) &&
    kindOk2 (cellPieces D nu) (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi)
      (CQ.sub (cqOf e.2) (cqOf e.1)) ((c.uhi - c.ulo) / 2) D.W Rtwo (cpiOf D) D.mprime eW eP c.kind

theorem nearCellT2_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (e : Pt × Pt) (c : TCell2)
    (h : nearCellT2 nu Rtwo eW eP D e c = true)
    (t : ℝ) (h1 : (c.ulo : ℝ) ≤ t) (h2 : t ≤ (c.uhi : ℝ)) (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  unfold nearCellT2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hm⟩ := h
  have key := kindOk2_sound hm (t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ)) δ (by
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

/-- One tube cell: far or near. -/
def cellOk2 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (D : SplineData) (e : Pt × Pt)
    (c : TCell2) : Bool :=
  cellFarOk D F e (c.ulo, c.uhi) || nearCellT2 nu Rtwo eW eP D e c

/-- The cells of one edge: they cover `[0,1]` and each is ok. -/
def edgeCells2 (ok : Pt × Pt → TCell2 → Bool) (e : Pt × Pt) (cs : List TCell2) : Bool :=
  coverOk 0 1 (cs.map fun c => (c.ulo, c.uhi)) && cs.all (ok e)

/-- Edge by edge. -/
def tubeCells2 (ok : Pt × Pt → TCell2 → Bool) : List (Pt × Pt) → List (List TCell2) → Bool
  | [], [] => true
  | e :: es, cs :: css => edgeCells2 ok e cs && tubeCells2 ok es css
  | _, _ => false

theorem tubeCells2_sound {ok : Pt × Pt → TCell2 → Bool} {Q : Pt × Pt → ℝ → Prop}
    (hQ : ∀ e (c : TCell2), ok e c = true → ∀ t : ℝ, (c.ulo : ℝ) ≤ t → t ≤ (c.uhi : ℝ) → Q e t) :
    ∀ (es : List (Pt × Pt)) (css : List (List TCell2)), tubeCells2 ok es css = true →
      ∀ e ∈ es, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Q e t
  | [], [], _, e, he, _, _, _ => by simp at he
  | [], _ :: _, h, _, _, _, _, _ => by simp [tubeCells2] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [tubeCells2] at h
  | e0 :: es, cs :: css, h, e, he, t, ht0, ht1 => by
      simp only [tubeCells2, edgeCells2, Bool.and_eq_true] at h
      obtain ⟨⟨hcov, hall⟩, hrest⟩ := h
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨p, hp, h1, h2⟩ := coverOk_sound hcov t (by simpa using ht0) (by simpa using ht1)
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
        exact hQ _ c (List.all_eq_true.1 hall c hc) t h1 h2
      · exact tubeCells2_sound hQ es css hrest e he t ht0 ht1

/-- **The tube test.** -/
def tubeCheck2 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (tmax : ℚ)
    (tube : List (List TCell2)) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) &&
    tubeCells2 (cellOk2 nu Rtwo eW eP F D) (edgesAll P tmax) tube &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheck2_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {tmax : ℚ} {tube : List (List TCell2)}
    {D : SplineData} {P : RatPolygon} (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (h : tubeCheck2 nu Rtwo eW eP F tmax tube D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheck2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htm, hs⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeCells2_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => by
      rcases Bool.or_eq_true_iff.1 hc with hc | hc
      · exact cellFar_sound H B hc t h1 h2 δ
      · exact nearCellT2_sound nu Rtwo eW eP hV D e c hc t h1 h2 δ hδ) _ _ hcells
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

/-! ### Line and cap cells -/

/-- Line cell `[ulo, uhi] ⊆ [0,1]`, threshold `gmin`. -/
def lineCellOk2 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell2) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk2 (cellPieces D nu) ⟨(c.ulo + c.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.uhi - c.ulo) / 2) D.W Rtwo
      (cpiOf D) D.gmin eW eP c.kind

/-- Cap cell `[ulo, uhi]` with lower bound `lb` of `g`. -/
def capCellOk2 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell2 × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk2 (cellPieces D nu) ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo
      (cpiOf D) c.2 eW eP c.1.kind

theorem realCell2_sound {ps : List WP} {a b W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind2}
    (hW : 0 ≤ W)
    (hc : kindOk2 ps ⟨(a + b) / 2, 0⟩ ⟨1, 0⟩ ((b - a) / 2) W Rtwo cpi m' eW eP k = true)
    (x : ℝ) (hx1 : (a : ℝ) ≤ x) (hx2 : x ≤ (b : ℝ)) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (⟨x, 0⟩ : ℂ))).sum
      + (cpi : ℝ) * |(⟨x, 0⟩ : ℂ).im| := by
  have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW
  have key := kindOk2_sound hc (x - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
    rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
  have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
    apply Complex.ext <;> simp [CQ.toC]
  rw [hz] at key
  exact key

theorem lineCellOk2_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : TCell2)
    (h : lineCellOk2 nu Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.ulo : ℝ) ≤ x → x ≤ c.uhi →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineCellOk2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell2_sound hW hm x hx1 hx2)

theorem capCellOk2_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : TCell2 × ℚ)
    (h : capCellOk2 nu Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      (c.2 : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold capCellOk2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell2_sound hW hm x hx1 hx2)

/-! ### Cap upper bounds (Darboux rule): the same cell rules for the negated pieces -/

/-- The piece with negated weight. -/
def negW (P : WP) : WP := { P with w := -P.w }

theorem negW_sum (l : List WP) (z : ℂ) :
    ((l.map negW).map (fun P => (P.w : ℝ) * PhiW P z)).sum
      = -((l.map fun P => (P.w : ℝ) * PhiW P z).sum) := by
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.sum_cons, ih, negW]
    push_cast
    have : PhiW { P with w := -P.w } z = PhiW P z := rfl
    rw [this]; ring

/-- Cap cell `[ulo, uhi]` with an UPPER bound `ub` of `g`: lower bound `-ub` for the negated pieces
(on the real axis `Im = 0`, so the `cpi` term vanishes). -/
def ubCellOk2 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell2 × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk2 ((cellPieces D nu).map negW) ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩
      ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo 0 (-c.2) eW eP c.1.kind

theorem ubCellOk2_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : TCell2 × ℚ)
    (h : ubCellOk2 nu Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ (c.2 : ℝ) := by
  intro x hx1 hx2
  unfold ubCellOk2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  have key := realCell2_sound hW hm x hx1 hx2
  rw [negW_sum] at key
  rw [gNu_eq D nu hV]
  have him : (⟨x, 0⟩ : ℂ).im = 0 := rfl
  rw [him] at key ⊢
  simp only [abs_zero, mul_zero, add_zero, neg_neg, Rat.cast_neg, Rat.cast_zero] at key ⊢
  linarith

end CatalanCore.Uniform.Decay.PolyWire2
