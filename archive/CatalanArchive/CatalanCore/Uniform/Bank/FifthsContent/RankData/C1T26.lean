import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 0d65ed7722513f8c019243a6ccdfafb683b3f7732a9f02b3f8219c7fe4316196, prime class 1 mod 10. -/
def C1T26 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-5) | _ => 0
  ee := fun d => match d with | 0 => (-25) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T26_ok : C1T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T26_den : ℕ := 1
theorem C1T26_den_ok :
    (∀ d ∈ C1T26.R, ∀ e ∈ C1T26.R, (C1T26.Lq d e).den ∣ C1T26_den ∧ (C1T26.Lq' d e).den ∣ C1T26_den) ∧
    (∀ d ∈ C1T26.C, ∀ e ∈ C1T26.C, (C1T26.Pq d e).den ∣ C1T26_den ∧ (C1T26.Pq' d e).den ∣ C1T26_den) := by
  constructor <;> decide +kernel
#print axioms C1T26_ok
#print axioms C1T26_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
