import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 875ce762d38e62de74100c553a13781f8e4391239209067367b628aba04a4ad4, prime class 1 mod 10. -/
def C1T22 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-4) | 2 => (-13 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24) | 2 => (-220 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-10 / 3) | 1, 1 => 1 | 1, 2 => (-13 / 24) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (10 / 3) | 1, 1 => 1 | 1, 2 => (13 / 24) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C1T22_ok : C1T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T22_den : ℕ := 24
theorem C1T22_den_ok :
    (∀ d ∈ C1T22.R, ∀ e ∈ C1T22.R, (C1T22.Lq d e).den ∣ C1T22_den ∧ (C1T22.Lq' d e).den ∣ C1T22_den) ∧
    (∀ d ∈ C1T22.C, ∀ e ∈ C1T22.C, (C1T22.Pq d e).den ∣ C1T22_den ∧ (C1T22.Pq' d e).den ∣ C1T22_den) := by
  constructor <;> decide +kernel
theorem C1T22_cload_2 : C1T22.cload 2 = ((-23 / 8), (-13 / 6)) := by decide +kernel
#print axioms C1T22_ok
#print axioms C1T22_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
