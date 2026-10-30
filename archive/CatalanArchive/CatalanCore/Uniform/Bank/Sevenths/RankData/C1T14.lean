import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type eafe402f715ce6448f66980e0d3a58cf6fcab842cdfa922926e084cdcbb10a91, root class 1. -/
def C1T14 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | 3 => (-9011 / 1320) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | 3 => (-28298627 / 580800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T14_ok : C1T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T14_den : ℕ := 1
theorem C1T14_den_ok :
    (∀ d ∈ C1T14.R, ∀ e ∈ C1T14.R, (C1T14.Lq d e).den ∣ C1T14_den ∧ (C1T14.Lq' d e).den ∣ C1T14_den) ∧
    (∀ d ∈ C1T14.C, ∀ e ∈ C1T14.C, (C1T14.Pq d e).den ∣ C1T14_den ∧ (C1T14.Pq' d e).den ∣ C1T14_den) := by
  constructor <;> decide +kernel
#print axioms C1T14_ok
#print axioms C1T14_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
