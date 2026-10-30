import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type b8e829d04a0cb9a687bd1a15980b31e4fcac00001850612e67288f196504c634, prime class 1 mod 10. -/
def C1T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | 3 => (-839 / 176) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | 3 => (-2289523 / 92928) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-974528459 / 314999745852) | 3, 1 => (-277148323 / 209999830568) | 3, 2 => (-1979213 / 2386361711) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (974528459 / 314999745852) | 3, 1 => (277148323 / 209999830568) | 3, 2 => (1979213 / 2386361711) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C1T12_ok : C1T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T12_den : ℕ := 629999491704
theorem C1T12_den_ok :
    (∀ d ∈ C1T12.R, ∀ e ∈ C1T12.R, (C1T12.Lq d e).den ∣ C1T12_den ∧ (C1T12.Lq' d e).den ∣ C1T12_den) ∧
    (∀ d ∈ C1T12.C, ∀ e ∈ C1T12.C, (C1T12.Pq d e).den ∣ C1T12_den ∧ (C1T12.Pq' d e).den ∣ C1T12_den) := by
  constructor <;> decide +kernel
theorem C1T12_rload_3 : C1T12.rload 3 = ((626696477585 / 629999491704), (-746742638197 / 157499872926)) := by decide +kernel
#print axioms C1T12_ok
#print axioms C1T12_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
