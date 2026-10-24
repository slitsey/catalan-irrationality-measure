module

public import CatalanMeasure.GenD.CertMod
public import CatalanMeasure.GenD.D58.C3.Data
public import CatalanMeasure.GenD.D58.OddProfile
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace CatalanMeasure.GenD
namespace D58
namespace C3

open CatalanMeasure.Parametric OAI.InternalCatalan

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

instance fact1009 : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

theorem zet_5 : ∀ j : Fin 70, palindromicRatResidue 1009 (zetaRat 5 j) =
    CertMod.entry 1009 zetaRows 5 j.val := by
  decide +kernel

end C3
end D58
end CatalanMeasure.GenD
