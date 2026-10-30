import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 137bfe94f9fae45dd292e43277b1b0cfa6202d32349da737e67cbf3732048eee, prime class 7 mod 10. -/
def C7T09 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | 3 => (-1049 / 936) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | 3 => (-1780561 / 876096) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-113678417239 / 1890837914082) | 3, 1 => (-8840072452 / 315139652347) | 3, 2 => (-440849522 / 24241511719) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (113678417239 / 1890837914082) | 3, 1 => (8840072452 / 315139652347) | 3, 2 => (440849522 / 24241511719) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C7T09_ok : C7T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T09_den : ℕ := 1890837914082
theorem C7T09_den_ok :
    (∀ d ∈ C7T09.R, ∀ e ∈ C7T09.R, (C7T09.Lq d e).den ∣ C7T09_den ∧ (C7T09.Lq' d e).den ∣ C7T09_den) ∧
    (∀ d ∈ C7T09.C, ∀ e ∈ C7T09.C, (C7T09.Pq d e).den ∣ C7T09_den ∧ (C7T09.Pq' d e).den ∣ C7T09_den) := by
  constructor <;> decide +kernel
theorem C7T09_rload_3 : C7T09.rload 3 = ((1689732799415 / 1890837914082), (-2427586154077 / 2521117218776)) := by decide +kernel
#print axioms C7T09_ok
#print axioms C7T09_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
