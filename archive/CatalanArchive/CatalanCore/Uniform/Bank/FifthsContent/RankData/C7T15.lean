import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type aa4898e622414a9f6f18bbc306e39e87978fb3d53a3266b2140a6e3d3d285ef8, prime class 7 mod 10. -/
def C7T15 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-526635 / 6343168) | 1, 1 => 1 | 1, 2 => (-30807 / 792896) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (526635 / 6343168) | 1, 1 => 1 | 1, 2 => (30807 / 792896) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C7T15_ok : C7T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T15_den : ℕ := 6343168
theorem C7T15_den_ok :
    (∀ d ∈ C7T15.R, ∀ e ∈ C7T15.R, (C7T15.Lq d e).den ∣ C7T15_den ∧ (C7T15.Lq' d e).den ∣ C7T15_den) ∧
    (∀ d ∈ C7T15.C, ∀ e ∈ C7T15.C, (C7T15.Pq d e).den ∣ C7T15_den ∧ (C7T15.Pq' d e).den ∣ C7T15_den) := by
  constructor <;> decide +kernel
theorem C7T15_cload_2 : C7T15.cload 2 = ((5570077 / 6343168), (-587371 / 594672)) := by decide +kernel
#print axioms C7T15_ok
#print axioms C7T15_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
