import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type c95d30f75bae7ce052185ef63047ef9f69aebb02555acff541363ebfbfb1fcc1, prime class 9 mod 10. -/
def C9T07 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | 3 => (-2837 / 4788) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | 3 => (-16204129 / 22924944) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T07_ok : C9T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T07_den : ℕ := 1
theorem C9T07_den_ok :
    (∀ d ∈ C9T07.R, ∀ e ∈ C9T07.R, (C9T07.Lq d e).den ∣ C9T07_den ∧ (C9T07.Lq' d e).den ∣ C9T07_den) ∧
    (∀ d ∈ C9T07.C, ∀ e ∈ C9T07.C, (C9T07.Pq d e).den ∣ C9T07_den ∧ (C9T07.Pq' d e).den ∣ C9T07_den) := by
  constructor <;> decide +kernel
#print axioms C9T07_ok
#print axioms C9T07_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
