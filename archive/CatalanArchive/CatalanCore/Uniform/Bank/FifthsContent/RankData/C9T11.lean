import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 799e5764a3f4431bf57d24ae8ac2b0925fcee3df289ddf20657c88941ef1d6c9, prime class 9 mod 10. -/
def C9T11 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-735163 / 880929) | 1, 1 => 1 | 1, 3 => (-93868 / 293643) | 2, 2 => 1 | 2, 3 => (-2734 / 13983) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (735163 / 880929) | 1, 1 => 1 | 1, 3 => (93868 / 293643) | 2, 2 => 1 | 2, 3 => (2734 / 13983) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C9T11_ok : C9T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T11_den : ℕ := 880929
theorem C9T11_den_ok :
    (∀ d ∈ C9T11.R, ∀ e ∈ C9T11.R, (C9T11.Lq d e).den ∣ C9T11_den ∧ (C9T11.Lq' d e).den ∣ C9T11_den) ∧
    (∀ d ∈ C9T11.C, ∀ e ∈ C9T11.C, (C9T11.Pq d e).den ∣ C9T11_den ∧ (C9T11.Pq' d e).den ∣ C9T11_den) := by
  constructor <;> decide +kernel
theorem C9T11_cload_3 : C9T11.cload 3 = ((-308080 / 880929), (-668467 / 3523716)) := by decide +kernel
#print axioms C9T11_ok
#print axioms C9T11_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
