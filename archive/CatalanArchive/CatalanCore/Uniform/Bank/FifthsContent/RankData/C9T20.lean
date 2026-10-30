import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type a4357a6665f628eea44b1ac05306b58e3956ac72ee5f088dc13226dba9b69770, prime class 9 mod 10. -/
def C9T20 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T20_ok : C9T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T20_den : ℕ := 1
theorem C9T20_den_ok :
    (∀ d ∈ C9T20.R, ∀ e ∈ C9T20.R, (C9T20.Lq d e).den ∣ C9T20_den ∧ (C9T20.Lq' d e).den ∣ C9T20_den) ∧
    (∀ d ∈ C9T20.C, ∀ e ∈ C9T20.C, (C9T20.Pq d e).den ∣ C9T20_den ∧ (C9T20.Pq' d e).den ∣ C9T20_den) := by
  constructor <;> decide +kernel
#print axioms C9T20_ok
#print axioms C9T20_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
