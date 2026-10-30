import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 0aa5db004debc4d83a1eba4a5a629af66c65c9a7bb038395d514d6ea462fb271, prime class 7 mod 10. -/
def C7T13 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T13_ok : C7T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T13_den : ℕ := 1
theorem C7T13_den_ok :
    (∀ d ∈ C7T13.R, ∀ e ∈ C7T13.R, (C7T13.Lq d e).den ∣ C7T13_den ∧ (C7T13.Lq' d e).den ∣ C7T13_den) ∧
    (∀ d ∈ C7T13.C, ∀ e ∈ C7T13.C, (C7T13.Pq d e).den ∣ C7T13_den ∧ (C7T13.Pq' d e).den ∣ C7T13_den) := by
  constructor <;> decide +kernel
#print axioms C7T13_ok
#print axioms C7T13_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
