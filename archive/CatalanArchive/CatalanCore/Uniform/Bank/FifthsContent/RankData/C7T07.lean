import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 7efd1938ae82acf7583799a0dd5cd43d7b105df867a0520d7180b4a59d125af5, prime class 7 mod 10. -/
def C7T07 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | 3 => (-1049 / 936) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | 3 => (-1780561 / 876096) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C7T07_ok : C7T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T07_den : ℕ := 1
theorem C7T07_den_ok :
    (∀ d ∈ C7T07.R, ∀ e ∈ C7T07.R, (C7T07.Lq d e).den ∣ C7T07_den ∧ (C7T07.Lq' d e).den ∣ C7T07_den) ∧
    (∀ d ∈ C7T07.C, ∀ e ∈ C7T07.C, (C7T07.Pq d e).den ∣ C7T07_den ∧ (C7T07.Pq' d e).den ∣ C7T07_den) := by
  constructor <;> decide +kernel
#print axioms C7T07_ok
#print axioms C7T07_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
