import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 901a3a5c1241292d8c80f57f8f9a478e1d722b77a7e02cffef67d3b717f996b0, prime class 3 mod 10. -/
def C3T22 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-15 / 7) | 1, 1 => 1 | 1, 2 => (-4 / 7) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (15 / 7) | 1, 1 => 1 | 1, 2 => (4 / 7) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C3T22_ok : C3T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T22_den : ℕ := 7
theorem C3T22_den_ok :
    (∀ d ∈ C3T22.R, ∀ e ∈ C3T22.R, (C3T22.Lq d e).den ∣ C3T22_den ∧ (C3T22.Lq' d e).den ∣ C3T22_den) ∧
    (∀ d ∈ C3T22.C, ∀ e ∈ C3T22.C, (C3T22.Pq d e).den ∣ C3T22_den ∧ (C3T22.Pq' d e).den ∣ C3T22_den) := by
  constructor <;> decide +kernel
theorem C3T22_cload_2 : C3T22.cload 2 = ((-12 / 7), (-6 / 7)) := by decide +kernel
#print axioms C3T22_ok
#print axioms C3T22_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
