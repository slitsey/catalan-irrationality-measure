import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type f7ebf1bf4c05da57e7511ace2e22ac9e3453d0fe169e795f12c800ae7bd3c39e, prime class 1 mod 10. -/
def C1T19 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T19_ok : C1T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T19_den : ℕ := 1
theorem C1T19_den_ok :
    (∀ d ∈ C1T19.R, ∀ e ∈ C1T19.R, (C1T19.Lq d e).den ∣ C1T19_den ∧ (C1T19.Lq' d e).den ∣ C1T19_den) ∧
    (∀ d ∈ C1T19.C, ∀ e ∈ C1T19.C, (C1T19.Pq d e).den ∣ C1T19_den ∧ (C1T19.Pq' d e).den ∣ C1T19_den) := by
  constructor <;> decide +kernel
#print axioms C1T19_ok
#print axioms C1T19_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
