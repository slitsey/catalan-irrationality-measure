import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 1f69f9ffbc7ae76f52c60ac1e97df6287a5a1952ab310c05489b1d8931d35c36, prime class 7 mod 10. -/
def C7T22 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-27 / 200) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (27 / 200) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C7T22_ok : C7T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T22_den : ℕ := 200
theorem C7T22_den_ok :
    (∀ d ∈ C7T22.R, ∀ e ∈ C7T22.R, (C7T22.Lq d e).den ∣ C7T22_den ∧ (C7T22.Lq' d e).den ∣ C7T22_den) ∧
    (∀ d ∈ C7T22.C, ∀ e ∈ C7T22.C, (C7T22.Pq d e).den ∣ C7T22_den ∧ (C7T22.Pq' d e).den ∣ C7T22_den) := by
  constructor <;> decide +kernel
theorem C7T22_rload_1 : C7T22.rload 1 = ((173 / 200), (-16 / 15)) := by decide +kernel
#print axioms C7T22_ok
#print axioms C7T22_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
