module

public import CatalanCore.Uniform.Decay.PolyWire3.Kinds
public import CatalanCore.Uniform.Decay.Breakpoint.CellT

@[expose] public section
set_option Elab.async false

/-!
# Tube cells with the truncated-logarithm breakpoint rule (ledger B05a; sibling of `PolyWire3.Kinds`)

`kindOkTr` is `kindOk` with the `bp n side lo C Fs K` kind read by `Breakpoint.bpOkT` (the field of the
shared inductive `CellKind` that `bpOk` uses for its exponent `eS` carries the truncation order `K`).
Every other kind is checked as in `kindOk`.  `tubeCheckTr`, `tubeCheckTr_sound` are `tubeCheck`,
`tubeCheck_sound` with `kindOkTr`: same statement, same hypotheses.  Line and cap cells keep `kindOk`.
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyWire2
open CatalanCore.Uniform.Decay.Breakpoint (bpOkT bpOkT_sound)
open CatalanCore.Uniform.Decay.FarField (MPData mpGlobalOk mpCellOk mpCellOk_sound)

/-- `kindOk` with the truncated-logarithm breakpoint rule. -/
def kindOkTr (ps : List WP) (M : Option MPData) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ) :
    CellKind → Bool
  | .base k => kindOk2 ps zc dd h W Rtwo cpi m' eW eP k
  | .bp n side lo C Fs K => bpOkT n side ps zc dd h W Rtwo cpi lo m' C Fs eW eP K
  | .mp rm rh => match M with
      | none => false
      | some M0 => mpCellOk M0 zc dd h W cpi m' rm rh
  | .flip ix k => kindOkTr (flipAt ix ps) none zc dd h W Rtwo cpi m' eW eP k
termination_by structural k => k

theorem kindOkTr_sound {ps : List WP} {M : Option MPData} (hG : globalOk ps M = true) {zc dd : CQ}
    {h W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind}
    (hc : kindOkTr ps M zc dd h W Rtwo cpi m' eW eP k = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  induction k generalizing ps M with
  | base k => (simp only [kindOkTr] at hc; exact kindOk2_sound hc s δ hs hδ)
  | bp n side lo C Fs K => (simp only [kindOkTr] at hc; exact bpOkT_sound hc s δ hs hδ)
  | mp rm rh =>
    cases M with
    | none => (simp only [kindOkTr] at hc; cases hc)
    | some M0 => (simp only [kindOkTr] at hc; exact mpCellOk_sound hG hc s δ hs hδ)
  | flip ix k ih =>
    simp only [kindOkTr] at hc
    exact flip_lower ix ps (ih (ps := flipAt ix ps) (M := none) rfl hc)

/-! ### Tube cells -/

def nearCellTr (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (e : Pt × Pt) (c : TCell) : Bool :=
  decide (D.ε < 1) &&
    kindOkTr (cellPieces D nu) M (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi)
      (CQ.sub (cqOf e.2) (cqOf e.1)) ((c.uhi - c.ulo) / 2) D.W Rtwo (cpiOf D) D.mprime eW eP c.kind

theorem nearCellTr_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (hG : globalOk (cellPieces D nu) M = true)
    (e : Pt × Pt) (c : TCell) (h : nearCellTr nu M Rtwo eW eP D e c = true)
    (t : ℝ) (h1 : (c.ulo : ℝ) ≤ t) (h2 : t ≤ (c.uhi : ℝ)) (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  unfold nearCellTr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hm⟩ := h
  have key := kindOkTr_sound hG hm (t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ)) δ (by
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

def cellOkTr (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (D : SplineData)
    (e : Pt × Pt) (c : TCell) : Bool :=
  cellFarOk D F e (c.ulo, c.uhi) || nearCellTr nu M Rtwo eW eP D e c

/-- **The tube test** with the truncated-logarithm breakpoint rule. -/
def tubeCheckTr (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (tmax : ℚ)
    (tube : List (List TCell)) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) &&
    tubeCells (cellOkTr nu M Rtwo eW eP F D) (edgesAll P tmax) tube &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheckTr_sound (nu : List Seg) (M : Option MPData) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {tmax : ℚ} {tube : List (List TCell)}
    {D : SplineData} {P : RatPolygon} (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (hG : globalOk (cellPieces D nu) M = true)
    (h : tubeCheckTr nu M Rtwo eW eP F tmax tube D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheckTr, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htm, hs⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeCells_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => by
      rcases Bool.or_eq_true_iff.1 hc with hc | hc
      · exact cellFar_sound H B hc t h1 h2 δ
      · exact nearCellTr_sound nu M Rtwo eW eP hV D hG e c hc t h1 h2 δ hδ) _ _ hcells
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

end CatalanCore.Uniform.Decay.PolyWire3
