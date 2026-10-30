import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type c60c6e23783f9220a66b7d3bfcdbab202906ea01c211a277d464d00063ee1872, prime class 9 mod 10. -/
def C9T05 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | 3 => (-2837 / 4788) | 4 => (-5275 / 9576) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | 3 => (-16204129 / 22924944) | 4 => (-63065305 / 91699776) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-3547458961777857431 / 38955201369287755594) | 4, 1 => (-851143437020107674 / 19477600684643877797) | 4, 2 => (-79694426711681037 / 2782514383520553971) | 4, 3 => (-3117035370727518 / 146448125448450209) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (3547458961777857431 / 38955201369287755594) | 4, 1 => (851143437020107674 / 19477600684643877797) | 4, 2 => (79694426711681037 / 2782514383520553971) | 4, 3 => (3117035370727518 / 146448125448450209) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C9T05_ok : C9T05.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T05_den : ℕ := 38955201369287755594
theorem C9T05_den_ok :
    (∀ d ∈ C9T05.R, ∀ e ∈ C9T05.R, (C9T05.Lq d e).den ∣ C9T05_den ∧ (C9T05.Lq' d e).den ∣ C9T05_den) ∧
    (∀ d ∈ C9T05.C, ∀ e ∈ C9T05.C, (C9T05.Pq d e).den ∣ C9T05_den ∧ (C9T05.Pq' d e).den ∣ C9T05_den) := by
  constructor <;> decide +kernel
theorem C9T05_rload_4 : C9T05.rload 4 = ((31760602150892628509 / 38955201369287755594), (-259603945949097809749 / 701193624647179600692)) := by decide +kernel
#print axioms C9T05_ok
#print axioms C9T05_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
