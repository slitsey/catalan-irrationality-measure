import CatalanCore.Uniform.Decay.PolyWire.Link
import CatalanCore.Uniform.Decay.NearCells.Rules
import CatalanCore.Uniform.Decay.NearCells2.Mix
import CatalanCore.Uniform.Decay.PolyCells.Assemble
import CatalanCore.Uniform.Decay.PolyFull.CapLb
set_option Elab.async false

/-!
# Near-cell oracles from Boolean cell tables (lane D, package D11)

A *cell table* entry `TCell` is `(ulo, uhi, kind)`; `CellKind` selects the rule of D6b/D6d:
* `jet lo C Fs`  : `cellOk` (order-`n` jet + Bernstein lower bound `lo`, aggregate `C`, error `Fs`);
* `jetM lo C Fs` : `cellOk'` (endpoint-merged jet remainder, D6d);
* `pt`           : `ptOk` (endpoint cell, D6b);
* `mix sel ρ lo C Fs eW' eP'` : `mixOk` (D6d), the pieces selected by `sel` being near.

`kindOk` is the common Boolean, `kindOk_sound` its soundness (the conclusion of D6b `oneCellOk_sound`).
From the tables:
* `nearOracle_of_tables` : `SegNearOracle` (tube cells; the cells of an edge are looked up by the
  edge `e = (a, b)` and the parameter interval `[ulo, uhi]`, so the tail segment is an ordinary edge);
* `lineOracle_of_tables` : `LineOracle` (cells in `[0,1]`);
* `capOracle_of_tables`  : `CapLb` (lower bounds `lb` of `g` on cap cells `(a, b, lb)`).
-/

namespace CatalanCore.Uniform.Decay.PolyWire

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly

inductive CellKind where
  | jet (lo : ℚ) (C : List ℚ) (Fs : ℚ)
  | jetM (lo : ℚ) (C : List ℚ) (Fs : ℚ)
  | pt
  | mix (sel : List Bool) (ρ lo : ℚ) (C : List ℚ) (Fs : ℚ) (eW' eP' : ℕ)

structure TCell where
  ulo : ℚ
  uhi : ℚ
  kind : CellKind

/-- The Boolean test of one cell of centre `zc`, direction `dd`, half-width `h`. -/
def kindOk (n : ℕ) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ) :
    CellKind → Bool
  | .jet lo C Fs => oneCellOk n ps zc dd h W Rtwo cpi m' eW eP (some (lo, C, Fs))
  | .jetM lo C Fs => cellOk' n ps zc dd h W Rtwo cpi lo m' C Fs eW eP
  | .pt => oneCellOk n ps zc dd h W Rtwo cpi m' eW eP none
  | .mix sel ρ lo C Fs eW' eP' =>
      mixOk n (splitSel ps sel).1 (splitSel ps sel).2 zc dd h ρ W Rtwo cpi lo m' C Fs eW eP eW' eP'

theorem kindOk_sound {n : ℕ} {ps : List WP} {zc dd : CQ} {h W Rtwo cpi m' : ℚ} {eW eP : ℕ}
    {k : CellKind} (hc : kindOk n ps zc dd h W Rtwo cpi m' eW eP k = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  cases k with
  | jet lo C Fs => (simp only [kindOk] at hc; exact oneCellOk_sound hc s δ hs hδ)
  | jetM lo C Fs => (simp only [kindOk] at hc; exact cellOk'_sound hc s δ hs hδ)
  | pt => (simp only [kindOk] at hc; exact oneCellOk_sound hc s δ hs hδ)
  | mix sel ρ lo C Fs eW' eP' => (simp only [kindOk] at hc; exact mixOk_sound_perm (splitSel_perm ps sel) hc s δ hs hδ)

/-- Table lookup by the parameter interval. -/
def findK (t : List TCell) (a b : ℚ) : Option CellKind :=
  (t.find? fun c => decide (c.ulo = a ∧ c.uhi = b)).map TCell.kind

/-- Table lookup of an edge. -/
def findEdge (tab : List ((Pt × Pt) × List TCell)) (e : Pt × Pt) : Option (List TCell) :=
  (tab.find? fun x => decide (x.1 = e)).map Prod.snd

def cqOf (p : Pt) : CQ := ⟨p.1, p.2⟩

theorem cqOf_toC (p : Pt) : (cqOf p).toC = vertC p := rfl

/-! ### Tube cells -/

/-- The near test of the cell `[c.1, c.2]` of the edge `e`. -/
def segNearT (nu : List Seg) (n : ℕ) (Rtwo : ℚ) (eW eP : ℕ)
    (tab : List ((Pt × Pt) × List TCell)) (D : SplineData) (e : Pt × Pt) (c : ℚ × ℚ) : Bool :=
  decide (D.ε < 1) &&
    match findEdge tab e with
    | none => false
    | some cs =>
      match findK cs c.1 c.2 with
      | none => false
      | some k => kindOk n (cellPieces D nu) (edgeCentre (cqOf e.1) (cqOf e.2) c.1 c.2)
          (CQ.sub (cqOf e.2) (cqOf e.1)) ((c.2 - c.1) / 2) D.W Rtwo (cpiOf D) D.mprime eW eP k

theorem segNearT_sound (nu : List Seg) (n : ℕ) (Rtwo : ℚ) (eW eP : ℕ)
    (tab : List ((Pt × Pt) × List TCell)) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z)
    (D : SplineData) (e : Pt × Pt) (c : ℚ × ℚ) (h : segNearT nu n Rtwo eW eP tab D e c = true)
    (t : ℝ) (h1 : (c.1 : ℝ) ≤ t) (h2 : t ≤ (c.2 : ℝ)) (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  unfold segNearT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hm⟩ := h
  split at hm
  · cases hm
  · rename_i cs _
    split at hm
    · cases hm
    · rename_i k _
      have key := kindOk_sound hm (t - (((c.1 + c.2) / 2 : ℚ) : ℝ)) δ (by
        rw [abs_le]; push_cast; constructor <;> linarith) hδ
      have ez : (edgeCentre (cqOf e.1) (cqOf e.2) c.1 c.2).toC +
          ((t - (((c.1 + c.2) / 2 : ℚ) : ℝ) : ℝ) : ℂ) * (CQ.sub (cqOf e.2) (cqOf e.1)).toC
          + (δ : ℂ) = segPtC e t + (δ : ℂ) := by
        unfold edgeCentre
        rw [CQ.toC_add, CQ.toC_smul, CQ.toC_sub, cqOf_toC, cqOf_toC]
        unfold segPtC
        push_cast; ring
      rw [ez] at key
      exact gNu_ge_of D nu hV hε key

/-! ### Cells on the real line -/

theorem realCell_sound {n : ℕ} {ps : List WP} {a b W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind}
    (hW : 0 ≤ W)
    (hc : kindOk n ps ⟨(a + b) / 2, 0⟩ ⟨1, 0⟩ ((b - a) / 2) W Rtwo cpi m' eW eP k = true)
    (x : ℝ) (hx1 : (a : ℝ) ≤ x) (hx2 : x ≤ (b : ℝ)) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (⟨x, 0⟩ : ℂ))).sum
      + (cpi : ℝ) * |(⟨x, 0⟩ : ℂ).im| := by
  have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW
  have key := kindOk_sound hc (x - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
    rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
  have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
    apply Complex.ext <;> simp [CQ.toC]
  rw [hz] at key
  exact key

/-- The line test of the cell `p = (a, b) ⊆ [0,1]`. -/
def lineOkT (nu : List Seg) (n : ℕ) (Rtwo : ℚ) (eW eP : ℕ) (tab : List TCell)
    (D : SplineData) (p : ℚ × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    match findK tab p.1 p.2 with
    | some k => kindOk n (cellPieces D nu) ⟨(p.1 + p.2) / 2, 0⟩ ⟨1, 0⟩ ((p.2 - p.1) / 2) D.W Rtwo
        (cpiOf D) D.gmin eW eP k
    | none => false

theorem lineOkT_sound (nu : List Seg) (n : ℕ) (Rtwo : ℚ) (eW eP : ℕ) (tab : List TCell)
    {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (p : ℚ × ℚ)
    (h : lineOkT nu n Rtwo eW eP tab D p = true) :
    ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineOkT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  split at hm
  · rename_i k _
    exact gNu_ge_of D nu hV hε (realCell_sound hW hm x hx1 hx2)
  · cases hm

/-- The cap test of the cell `c = (a, b, lb)`: `g ≥ lb` on `[a, b]`. -/
def lbOkT (nu : List Seg) (n : ℕ) (Rtwo : ℚ) (eW eP : ℕ) (tab : List TCell)
    (D : SplineData) (c : ℚ × ℚ × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    match findK tab c.1 c.2.1 with
    | some k => kindOk n (cellPieces D nu) ⟨(c.1 + c.2.1) / 2, 0⟩ ⟨1, 0⟩ ((c.2.1 - c.1) / 2) D.W
        Rtwo (cpiOf D) c.2.2 eW eP k
    | none => false

theorem lbOkT_sound (nu : List Seg) (n : ℕ) (Rtwo : ℚ) (eW eP : ℕ) (tab : List TCell)
    {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : ℚ × ℚ × ℚ)
    (h : lbOkT nu n Rtwo eW eP tab D c = true) :
    ∀ x : ℝ, (c.1 : ℝ) ≤ x → x ≤ c.2.1 →
      (c.2.2 : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lbOkT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  split at hm
  · rename_i k _
    exact gNu_ge_of D nu hV hε (realCell_sound hW hm x hx1 hx2)
  · cases hm

/-! ### The tables and the three oracles -/

/-- The cell tables and the global tuning of the near rules. -/
structure NearTables where
  nu : List Seg
  n : ℕ
  Rtwo : ℚ
  eW : ℕ
  eP : ℕ
  tube : List ((Pt × Pt) × List TCell)
  line : List TCell
  cap : List TCell

/-- Tube cells that are not far. -/
def nearOracle_of_tables (T : NearTables) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nu z) :
    SegNearOracle Vnu where
  segNear := segNearT T.nu T.n T.Rtwo T.eW T.eP T.tube
  sound D _ e c h t h1 h2 δ hδ := segNearT_sound T.nu T.n T.Rtwo T.eW T.eP T.tube hV D e c h t h1 h2 δ hδ

/-- Line cells. -/
def lineOracle_of_tables (T : NearTables) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nu z) :
    LineOracle Vnu where
  lineOk := lineOkT T.nu T.n T.Rtwo T.eW T.eP T.line
  line_sound D _ p h := lineOkT_sound T.nu T.n T.Rtwo T.eW T.eP T.line hV D p h

/-- Cap cells (lower bounds). -/
def capOracle_of_tables (T : NearTables) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nu z) :
    CapLb Vnu where
  lbOk := lbOkT T.nu T.n T.Rtwo T.eW T.eP T.cap
  lb_sound D _ c h := lbOkT_sound T.nu T.n T.Rtwo T.eW T.eP T.cap hV D c h

end CatalanCore.Uniform.Decay.PolyWire
