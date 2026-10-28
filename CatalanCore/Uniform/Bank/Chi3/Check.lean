import CatalanCore.Uniform.Bank.Chi3.Tube.Top
import CatalanCore.Uniform.Bank.Chi3.Line.Top
import CatalanCore.Uniform.Bank.Chi3.Cap.Top
import CatalanCore.Uniform.Bank.Chi3.Energy.Top
set_option Elab.async false
set_option maxRecDepth 100000

/-! The Boolean check of the chi3 tables (lane B, B3b): `TabC.check Dchi Pply = true`. -/

namespace CatalanCore.Uniform.Bank.Chi3
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull

def TabC : PolyTables2 where
  Mq := 5 / 4
  RP := RP
  CP := RP
  Rn := 3 / 2
  F := Fc
  Rtwo := Rtw
  eW := eWc
  eP := ePc
  tmax := tmaxC
  tube := tubeC
  line := lineC
  cap := capC
  G := Gcap
  E := Etab

theorem basic_ok : Dchi.basicOkP = true := by decide +kernel
theorem poly_ok : Pply.okB = true := by decide +kernel
theorem far_ok : farDataOk TabC.F TabC.Rn TabC.RP TabC.CP Dn = true := by decide +kernel
theorem cap_chain : capChain (-Dn.r0) TabC.capCells 0 = true := by decide +kernel
theorem cap_G : capGokOf TabC.RP TabC.CP Dn TabC.G = true := by decide +kernel
theorem cap_sum : decide (Dn.Scap + capSum Dn.mprime TabC.capCells ≤ TabC.G - Dn.mprime * Dn.r0) = true := by
  decide +kernel
theorem tube_far_end : farOk Dn Fc ((lastPt (basePt Pply) Pply.verts).2 + Pply.s * tmaxC) = true := by
  decide +kernel

theorem tube_chk : tubeCheck2 TabC.nu TabC.Rtwo TabC.eW TabC.eP TabC.F TabC.tmax TabC.tube Dn Pply = true := by
  unfold tubeCheck2
  have h1 : decide (0 < TabC.tmax) = true := by decide +kernel
  have h2 : decide (0 ≤ Pply.s) = true := by decide +kernel
  have h3 : tubeCells2 (cellOk2 TabC.nu TabC.Rtwo TabC.eW TabC.eP TabC.F Dn) (edgesAll Pply TabC.tmax)
      TabC.tube = true := by
    show tubeCells2 (cellOk2 nuC Rtw eWc ePc Fc Dn) (edgesAll Pply tmaxC) tubeC = true
    rw [edges_eq]; exact tube_ok
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, tube_far_end⟩

theorem line_chk : TabC.lineTest Dn = true := by
  unfold PolyTables2.lineTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨line_eq, line_all⟩

theorem cap_chk : TabC.capCheck2 Dn = true := by
  unfold PolyTables2.capCheck2
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨cap_chain, cap_all⟩, cap_G⟩, cap_sum⟩

theorem energy_chk : energyOk2 TabC.E Dn = true := by
  unfold energyOk2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨etab_ok, etab_sum⟩

theorem check_true : TabC.check Dchi Pply = true := by
  unfold PolyTables2.check
  have hr : decide (Dchi.r0 = Pply.r0) = true := by decide +kernel
  have hm : decide (Dchi.Mq = TabC.Mq) = true := by decide +kernel
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨basic_ok, poly_ok⟩, hr⟩, hm⟩, far_ok⟩, tube_chk⟩, line_chk⟩, cap_chk⟩, energy_chk⟩

end CatalanCore.Uniform.Bank.Chi3
