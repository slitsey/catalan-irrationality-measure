import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type db2b8f4e47572f80a3bcc9def88418adf9173dc1a89893dc39d9cd58a40d376a, root class 1. -/
def C1T10 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | 3 => (-4351 / 1170) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | 3 => (-21315271 / 1368900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T10_ok : C1T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T10_den : ℕ := 1
theorem C1T10_den_ok :
    (∀ d ∈ C1T10.R, ∀ e ∈ C1T10.R, (C1T10.Lq d e).den ∣ C1T10_den ∧ (C1T10.Lq' d e).den ∣ C1T10_den) ∧
    (∀ d ∈ C1T10.C, ∀ e ∈ C1T10.C, (C1T10.Pq d e).den ∣ C1T10_den ∧ (C1T10.Pq' d e).den ∣ C1T10_den) := by
  constructor <;> decide +kernel
#print axioms C1T10_ok
#print axioms C1T10_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
