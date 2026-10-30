import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 272d6115ee7f7eb958bedaa6959a666faa03904af0cfe6e1bb74eceb2e80d3de, prime class 9 mod 10. -/
def C9T15 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-251240 / 1520127) | 2, 1 => (-13456 / 168903) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (251240 / 1520127) | 2, 1 => (13456 / 168903) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C9T15_ok : C9T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T15_den : ℕ := 1520127
theorem C9T15_den_ok :
    (∀ d ∈ C9T15.R, ∀ e ∈ C9T15.R, (C9T15.Lq d e).den ∣ C9T15_den ∧ (C9T15.Lq' d e).den ∣ C9T15_den) ∧
    (∀ d ∈ C9T15.C, ∀ e ∈ C9T15.C, (C9T15.Pq d e).den ∣ C9T15_den ∧ (C9T15.Pq' d e).den ∣ C9T15_den) := by
  constructor <;> decide +kernel
theorem C9T15_rload_2 : C9T15.rload 2 = ((163969 / 217161), (-264791 / 675612)) := by decide +kernel
#print axioms C9T15_ok
#print axioms C9T15_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
