import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type f86a754b8de30eb29ea174cc2592ff0a2f465806b2c79ca210744807c806ca64, prime class 1 mod 10. -/
def C1T11 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5) | 1 => (-29 / 6) | 2 => (-158 / 33) | 3 => (-839 / 176) | _ => 0
  ee := fun d => match d with | 0 => (-25) | 1 => (-889 / 36) | 2 => (-26845 / 1089) | 3 => (-2289523 / 92928) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-974528459 / 314999745852) | 1, 1 => 1 | 1, 3 => (-277148323 / 209999830568) | 2, 2 => 1 | 2, 3 => (-1979213 / 2386361711) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (974528459 / 314999745852) | 1, 1 => 1 | 1, 3 => (277148323 / 209999830568) | 2, 2 => 1 | 2, 3 => (1979213 / 2386361711) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C1T11_ok : C1T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T11_den : ℕ := 629999491704
theorem C1T11_den_ok :
    (∀ d ∈ C1T11.R, ∀ e ∈ C1T11.R, (C1T11.Lq d e).den ∣ C1T11_den ∧ (C1T11.Lq' d e).den ∣ C1T11_den) ∧
    (∀ d ∈ C1T11.C, ∀ e ∈ C1T11.C, (C1T11.Pq d e).den ∣ C1T11_den ∧ (C1T11.Pq' d e).den ∣ C1T11_den) := by
  constructor <;> decide +kernel
theorem C1T11_cload_3 : C1T11.cload 3 = ((626696477585 / 629999491704), (-746742638197 / 157499872926)) := by decide +kernel
#print axioms C1T11_ok
#print axioms C1T11_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
