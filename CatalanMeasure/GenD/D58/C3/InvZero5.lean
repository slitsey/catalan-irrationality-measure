module

public import CatalanMeasure.GenD.CertMod
public import CatalanMeasure.GenD.D58.C3.Data
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace CatalanMeasure.GenD
namespace D58
namespace C3

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem rowZero_5 : CertMod.RowOK 58 1009 baseRows invZeroRows (0 : ZMod 1009) (5 : Fin 58) := by
  unfold CertMod.RowOK
  decide +kernel

end C3
end D58
end CatalanMeasure.GenD
