import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 4ed408ed4903ddd30a080a76da8f45c15fca3e012dddfeda7985b88db5189ce6, prime class 1 mod 10. -/
def C1T21 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-10 / 3) | 2, 1 => (-13 / 24) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (10 / 3) | 2, 1 => (13 / 24) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C1T21_ok : C1T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T21_den : ℕ := 24
theorem C1T21_den_ok :
    (∀ d ∈ C1T21.R, ∀ e ∈ C1T21.R, (C1T21.Lq d e).den ∣ C1T21_den ∧ (C1T21.Lq' d e).den ∣ C1T21_den) ∧
    (∀ d ∈ C1T21.C, ∀ e ∈ C1T21.C, (C1T21.Pq d e).den ∣ C1T21_den ∧ (C1T21.Pq' d e).den ∣ C1T21_den) := by
  constructor <;> decide +kernel
theorem C1T21_rload_2 : C1T21.rload 2 = ((-23 / 8), (-13 / 6)) := by decide +kernel
#print axioms C1T21_ok
#print axioms C1T21_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
