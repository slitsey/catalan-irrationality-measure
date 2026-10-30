import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 8b47d764610b1ca9f4dc94d2d1205e3056bf289d40f7caec3ca18ee760806272, prime class 9 mod 10. -/
def C9T13 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T13_ok : C9T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T13_den : ℕ := 1
theorem C9T13_den_ok :
    (∀ d ∈ C9T13.R, ∀ e ∈ C9T13.R, (C9T13.Lq d e).den ∣ C9T13_den ∧ (C9T13.Lq' d e).den ∣ C9T13_den) ∧
    (∀ d ∈ C9T13.C, ∀ e ∈ C9T13.C, (C9T13.Pq d e).den ∣ C9T13_den ∧ (C9T13.Pq' d e).den ∣ C9T13_den) := by
  constructor <;> decide +kernel
#print axioms C9T13_ok
#print axioms C9T13_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
