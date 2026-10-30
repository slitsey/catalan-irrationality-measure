import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 5f520be66058ed41ad940900e51474b5127648d704a6da56f3cce190ee0bb543, prime class 1 mod 10. -/
def C1T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-6205 / 1466784) | 2, 1 => (-443 / 244464) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (6205 / 1466784) | 2, 1 => (443 / 244464) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C1T17_ok : C1T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T17_den : ℕ := 1466784
theorem C1T17_den_ok :
    (∀ d ∈ C1T17.R, ∀ e ∈ C1T17.R, (C1T17.Lq d e).den ∣ C1T17_den ∧ (C1T17.Lq' d e).den ∣ C1T17_den) ∧
    (∀ d ∈ C1T17.C, ∀ e ∈ C1T17.C, (C1T17.Pq d e).den ∣ C1T17_den ∧ (C1T17.Pq' d e).den ∣ C1T17_den) := by
  constructor <;> decide +kernel
theorem C1T17_rload_2 : C1T17.rload 2 = ((1457921 / 1466784), (-72697 / 15279)) := by decide +kernel
#print axioms C1T17_ok
#print axioms C1T17_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
