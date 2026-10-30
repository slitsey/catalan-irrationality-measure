import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type c1115b0a0a4116e61cbc7c40c8fc7ed33c17293985dda951e6c474bccaa3c28d, prime class 9 mod 10. -/
def C9T09 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | 3 => (-2837 / 4788) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | 3 => (-16204129 / 22924944) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-444476250928 / 3789967574799) | 3, 1 => (-23740084136 / 421107508311) | 3, 2 => (-2224381504 / 60158215473) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (444476250928 / 3789967574799) | 3, 1 => (23740084136 / 421107508311) | 3, 2 => (2224381504 / 60158215473) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C9T09_ok : C9T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T09_den : ℕ := 3789967574799
theorem C9T09_den_ok :
    (∀ d ∈ C9T09.R, ∀ e ∈ C9T09.R, (C9T09.Lq d e).den ∣ C9T09_den ∧ (C9T09.Lq' d e).den ∣ C9T09_den) ∧
    (∀ d ∈ C9T09.C, ∀ e ∈ C9T09.C, (C9T09.Pq d e).den ∣ C9T09_den ∧ (C9T09.Pq' d e).den ∣ C9T09_den) := by
  constructor <;> decide +kernel
theorem C9T09_rload_3 : C9T09.rload 3 = ((2991694531895 / 3789967574799), (-5700256030927 / 15159870299196)) := by decide +kernel
#print axioms C9T09_ok
#print axioms C9T09_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
