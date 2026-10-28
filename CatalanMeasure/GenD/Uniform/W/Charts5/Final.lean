module
public import CatalanMeasure.GenD.Uniform.W.Charts5.Phys
public import CatalanMeasure.GenD.Uniform.Bank532.Pk.L0146_k152_25
@[expose] public section
set_option Elab.async false

/-!
# Unconditional window certificate of the L0146 packet

`win_L0146 : WinCert (NullityLB.ofPacketHost ... physHost_pilot) (cw 6 (152/25) 73 (-12))`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
  CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Charts4
noncomputable section

theorem win_L0146 :
    WinCert (NullityLB.ofPacketHost D58.Odd.design_admissible packetO packetO_sound Win cNat wNatO physHost_pilot)
      (cw (6 : ℝ) (152 / 25 : ℝ) (73 : ℝ) (-12 : ℝ)) :=
  CatalanMeasure.GenD.Uniform.Bank532.Pk.L0146_k152_25.win0 D58.Odd.design_admissible physHost_pilot

end
end CatalanMeasure.GenD.Uniform.W.Charts5
