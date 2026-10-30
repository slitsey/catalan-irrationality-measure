import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type abf2fbd1308bba3bab61e5c7a2ed414e9c88e9c798ecd089f4ae5bfc4097b31b, root class 1. -/
def C1T28 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-69 / 16) | 1, 1 => 1 | 1, 2 => (-17 / 32) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (69 / 16) | 1, 1 => 1 | 1, 2 => (17 / 32) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C1T28_ok : C1T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T28_den : ℕ := 32
theorem C1T28_den_ok :
    (∀ d ∈ C1T28.R, ∀ e ∈ C1T28.R, (C1T28.Lq d e).den ∣ C1T28_den ∧ (C1T28.Lq' d e).den ∣ C1T28_den) ∧
    (∀ d ∈ C1T28.C, ∀ e ∈ C1T28.C, (C1T28.Pq d e).den ∣ C1T28_den ∧ (C1T28.Pq' d e).den ∣ C1T28_den) := by
  constructor <;> decide +kernel
theorem C1T28_cload_2 : C1T28.cload 2 = ((-123 / 32), (-51 / 16)) := by decide +kernel
#print axioms C1T28_ok
#print axioms C1T28_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
