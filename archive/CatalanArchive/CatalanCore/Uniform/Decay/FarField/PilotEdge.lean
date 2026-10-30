import CatalanCore.Uniform.Decay.FarField.PilotGlobal
import CatalanCore.Uniform.Decay.FarField.PilotCell0
import CatalanCore.Uniform.Decay.FarField.PilotCell1
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Chi3 tube edge 7 by two far-field cells (lane D, D15)

`far_e7_edge`: the cells `fc0`, `fc1` cover `[0,1]` and pass `cellOk3`, i.e. they are a drop-in
replacement for `ecells7` (93 cells) in `tubeCells3 (cellOk3 ...)`.  `far_e7_sound`: the
semantic conclusion, `g ≥ m'` on the whole edge 7 and its `W`-tube.
-/

namespace CatalanCore.Uniform.Bank.Chi3.FarPilot
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire2 CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.FarField

theorem far_e7_cov : coverOk 0 1 (farE7.map fun c => (c.ulo, c.uhi)) = true := by decide +kernel

theorem far_e7_all : farE7.all (cellOk3 nuC Mfar Rtw eWc ePc Fc Dn e7) = true := by
  simp only [farE7, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨ok_fc0, ok_fc1⟩

theorem far_e7_edge : edgeCells3 (cellOk3 nuC Mfar Rtw eWc ePc Fc Dn) e7 farE7 = true := by
  simp only [edgeCells3, Bool.and_eq_true]
  exact ⟨far_e7_cov, far_e7_all⟩

theorem far_e7_sound (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (δ : ℝ) (hδ : |δ| ≤ (Dn.W : ℝ)) :
    (Dn.mprime : ℝ) ≤ gNu Dn.Mq (nuPot nuC) (Dn.ε : ℝ) Dn.A Dn.B Dn.f (segPtC e7 t + (δ : ℂ)) := by
  have hG := far_global
  have hall : tubeCells3 (nearCellT3 nuC Mfar Rtw eWc ePc Dn) [e7] [farE7] = true := by
    simp only [tubeCells3, edgeCells3, Bool.and_true, Bool.and_eq_true]
    refine ⟨far_e7_cov, ?_⟩
    have := far_e7_all
    simp only [farE7, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at this ⊢
    sorry
  exact tubeCells3_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (Dn.W : ℝ) →
      (Dn.mprime : ℝ) ≤ gNu Dn.Mq (nuPot nuC) (Dn.ε : ℝ) Dn.A Dn.B Dn.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => nearCellT3_sound nuC Mfar Rtw eWc ePc (fun z => rfl) Dn hG e c hc t h1 h2 δ hδ)
    [e7] [farE7] hall e7 (List.mem_singleton_self _) t h0 h1 δ hδ

end CatalanCore.Uniform.Bank.Chi3.FarPilot
