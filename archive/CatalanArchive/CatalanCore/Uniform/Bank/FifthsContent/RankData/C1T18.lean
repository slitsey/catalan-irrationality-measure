import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 7e7dbb2774863008f61592b8a80be35de2f18205b369e9f648ba6fb19112cd54, prime class 1 mod 10. -/
def C1T18 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-6205 / 1466784) | 1, 1 => 1 | 1, 2 => (-443 / 244464) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (6205 / 1466784) | 1, 1 => 1 | 1, 2 => (443 / 244464) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C1T18_ok : C1T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T18_den : ℕ := 1466784
theorem C1T18_den_ok :
    (∀ d ∈ C1T18.R, ∀ e ∈ C1T18.R, (C1T18.Lq d e).den ∣ C1T18_den ∧ (C1T18.Lq' d e).den ∣ C1T18_den) ∧
    (∀ d ∈ C1T18.C, ∀ e ∈ C1T18.C, (C1T18.Pq d e).den ∣ C1T18_den ∧ (C1T18.Pq' d e).den ∣ C1T18_den) := by
  constructor <;> decide +kernel
theorem C1T18_cload_2 : C1T18.cload 2 = ((1457921 / 1466784), (-72697 / 15279)) := by decide +kernel
#print axioms C1T18_ok
#print axioms C1T18_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
