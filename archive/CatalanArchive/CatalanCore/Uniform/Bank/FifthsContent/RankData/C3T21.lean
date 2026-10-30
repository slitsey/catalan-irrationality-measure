import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 88126d1b741b6a8c26a21a8d9b7806a7782e256d5b99024d82c0bd0fff412fd1, prime class 3 mod 10. -/
def C3T21 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-15 / 7) | 2, 1 => (-4 / 7) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (15 / 7) | 2, 1 => (4 / 7) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C3T21_ok : C3T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T21_den : ℕ := 7
theorem C3T21_den_ok :
    (∀ d ∈ C3T21.R, ∀ e ∈ C3T21.R, (C3T21.Lq d e).den ∣ C3T21_den ∧ (C3T21.Lq' d e).den ∣ C3T21_den) ∧
    (∀ d ∈ C3T21.C, ∀ e ∈ C3T21.C, (C3T21.Pq d e).den ∣ C3T21_den ∧ (C3T21.Pq' d e).den ∣ C3T21_den) := by
  constructor <;> decide +kernel
theorem C3T21_rload_2 : C3T21.rload 2 = ((-12 / 7), (-6 / 7)) := by decide +kernel
#print axioms C3T21_ok
#print axioms C3T21_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
