import CatalanCore.Uniform.Decay.FarField.Kinds3
set_option Elab.async false

/-!
# The Boolean `farOk` on a polygon-edge interval (lane D, package D15)

`mpEdgeOk nu M D e ulo uhi rm rh` is the far-field test of the edge interval `[ulo, uhi]` of the
polygon edge `e`; `mpEdgeOk_sound` concludes `m' ≤ g` on the segment and its `W`-tube.
It is the case `CellKind3.mp rm rh` of `nearCellT3` (`nearCellT3_mp`), so a table cell of that
kind needs no separate lemma.
-/

namespace CatalanCore.Uniform.Decay.FarField

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Polygon
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.NearCells
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2

def mpEdgeOk (nu : List Seg) (M : MPData) (D : SplineData) (e : Pt × Pt) (ulo uhi rm rh : ℚ) : Bool :=
  nearCellT3 nu M 0 0 0 D e ⟨ulo, uhi, .mp rm rh⟩

theorem mpEdgeOk_sound (nu : List Seg) (M : MPData) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z)
    (D : SplineData) (hG : mpGlobalOk (cellPieces D nu) M = true) (e : Pt × Pt) (ulo uhi rm rh : ℚ)
    (h : mpEdgeOk nu M D e ulo uhi rm rh = true) (t : ℝ) (h1 : (ulo : ℝ) ≤ t) (h2 : t ≤ (uhi : ℝ))
    (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) :=
  nearCellT3_sound nu M 0 0 0 hV D hG e ⟨ulo, uhi, .mp rm rh⟩ h t h1 h2 δ hδ

theorem nearCellT3_mp (nu : List Seg) (M : MPData) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData)
    (e : Pt × Pt) (ulo uhi rm rh : ℚ) :
    nearCellT3 nu M Rtwo eW eP D e ⟨ulo, uhi, .mp rm rh⟩ = mpEdgeOk nu M D e ulo uhi rm rh := rfl

end CatalanCore.Uniform.Decay.FarField
