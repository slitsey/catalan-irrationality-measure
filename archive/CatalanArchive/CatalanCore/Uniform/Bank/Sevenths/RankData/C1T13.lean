import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c210e0aa8e375530e7909303e86d5c0260dbb8e8410a22111e73211291d01a9b, root class 1. -/
def C1T13 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | 4 => (-8681 / 1320) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | 4 => (-28262327 / 580800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T13_ok : C1T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T13_den : ℕ := 1
theorem C1T13_den_ok :
    (∀ d ∈ C1T13.R, ∀ e ∈ C1T13.R, (C1T13.Lq d e).den ∣ C1T13_den ∧ (C1T13.Lq' d e).den ∣ C1T13_den) ∧
    (∀ d ∈ C1T13.C, ∀ e ∈ C1T13.C, (C1T13.Pq d e).den ∣ C1T13_den ∧ (C1T13.Pq' d e).den ∣ C1T13_den) := by
  constructor <;> decide +kernel
#print axioms C1T13_ok
#print axioms C1T13_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
