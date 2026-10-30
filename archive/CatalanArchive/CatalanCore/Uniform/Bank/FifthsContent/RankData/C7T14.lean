import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type a8835419ce29d1906510579803aa2b59d266fd1f8cc8c7fd56acf5a4969c6478, prime class 7 mod 10. -/
def C7T14 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-526635 / 6343168) | 2, 1 => (-30807 / 792896) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (526635 / 6343168) | 2, 1 => (30807 / 792896) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C7T14_ok : C7T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T14_den : ℕ := 6343168
theorem C7T14_den_ok :
    (∀ d ∈ C7T14.R, ∀ e ∈ C7T14.R, (C7T14.Lq d e).den ∣ C7T14_den ∧ (C7T14.Lq' d e).den ∣ C7T14_den) ∧
    (∀ d ∈ C7T14.C, ∀ e ∈ C7T14.C, (C7T14.Pq d e).den ∣ C7T14_den ∧ (C7T14.Pq' d e).den ∣ C7T14_den) := by
  constructor <;> decide +kernel
theorem C7T14_rload_2 : C7T14.rload 2 = ((5570077 / 6343168), (-587371 / 594672)) := by decide +kernel
#print axioms C7T14_ok
#print axioms C7T14_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
