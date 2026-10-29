import CatalanCore.Uniform.Bank.Fifths.Cover.Glob
import CatalanCore.Uniform.Bank.Fifths.Cover.Tube.Top
import CatalanCore.Uniform.Bank.Fifths.Cover.Line.Top
import CatalanCore.Uniform.Bank.Fifths.Cover.Cap.Top
import CatalanCore.Uniform.Bank.Fifths.Cover.Energy.Top
set_option Elab.async false
set_option maxRecDepth 100000

/-! The Boolean check of the Fifths tables with the unified cell kinds (lane D, D17): `TabC.check Dchi Pply = true`. -/

namespace CatalanCore.Uniform.Bank.Fifths.Cover
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Polygon
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
open CatalanCore.Uniform.Decay.FarField (MPData)

def TabC : PolyTables3 where
  Mq := (10 / 9 : ℚ)
  RP := RP
  CP := CP
  Rn := (11 / 9 : ℚ)
  F := Fc
  Rtwo := Rtw
  eW := eWc
  eP := ePc
  tmax := tmaxC
  M := Mopt
  Mn := none
  tube := tubeC
  line := lineC
  cap := capC
  G := Gcap
  E := Etab

theorem basic_ok : Dchi.basicOkP = true := by decide +kernel
theorem poly_ok : Pply.okB = true := by decide +kernel
theorem far_ok : farDataOk TabC.F TabC.Rn TabC.RP TabC.CP Dn = true := by decide +kernel
theorem cap_chain : CatalanCore.Uniform.Decay.FarField.plChain (-Dn.r0) TabC.capCells 0 = true := by decide +kernel
theorem cap_G : capGokOf TabC.RP TabC.CP Dn TabC.G = true := by decide +kernel
theorem cap_sum : decide (Dn.Scap + CatalanCore.Uniform.Decay.FarField.plSum Dn.mprime TabC.capCells
    ≤ TabC.G - Dn.mprime * Dn.r0) = true := by
  decide +kernel
theorem tube_far_end : farOk Dn Fc ((lastPt (basePt Pply) Pply.verts).2 + Pply.s * tmaxC) = true := by
  decide +kernel

theorem tube_chk : TabC.tubeG Dn Pply = true := by
  unfold PolyTables3.tubeG
  have h3 : tubeCells (cellOk nuC Mopt Rtw eWc ePc Fc Dn) (edgesAll Pply tmaxC) tubeC = true := by
    rw [edges_eq]; exact tube_ok
  have h1 : decide (0 < TabC.tmax) = true := by decide +kernel
  have h2 : decide (0 ≤ Pply.s) = true := by decide +kernel
  simp only [Bool.and_eq_true]
  refine ⟨glob_ok, ?_⟩
  unfold CatalanCore.Uniform.Decay.PolyWire3.tubeCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, tube_far_end⟩

theorem line_chk : TabC.lineTest Dn = true := by
  unfold PolyTables3.lineTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨glob_ok, line_eq, line_all⟩

theorem cap_chk : TabC.capCheck Dn = true := by
  unfold PolyTables3.capCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨rfl, cap_chain⟩, cap_all⟩, cap_G⟩, cap_sum⟩

theorem energy_chk : energyOk2 TabC.E Dn = true := by
  unfold energyOk2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨etab_ok, etab_sum⟩

theorem check_true : TabC.check Dchi Pply = true := by
  unfold PolyTables3.check
  have hr : decide (Dchi.r0 = Pply.r0) = true := by decide +kernel
  have hm : decide (Dchi.Mq = TabC.Mq) = true := by decide +kernel
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨basic_ok, poly_ok⟩, hr⟩, hm⟩, far_ok⟩, tube_chk⟩, line_chk⟩, cap_chk⟩, energy_chk⟩

end CatalanCore.Uniform.Bank.Fifths.Cover
