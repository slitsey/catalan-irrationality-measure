import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 478c0bd2ab7c0993792ab814139718d4b24a9ce103d9f7b6c87751b4d2536fd6, root class 11. -/
def C11T23 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-31237 / 2709288) | 2, 1 => (-761 / 150516) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (31237 / 2709288) | 2, 1 => (761 / 150516) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C11T23_ok : C11T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T23_den : ℕ := 2709288
theorem C11T23_den_ok :
    (∀ d ∈ C11T23.R, ∀ e ∈ C11T23.R, (C11T23.Lq d e).den ∣ C11T23_den ∧ (C11T23.Lq' d e).den ∣ C11T23_den) ∧
    (∀ d ∈ C11T23.C, ∀ e ∈ C11T23.C, (C11T23.Pq d e).den ∣ C11T23_den ∧ (C11T23.Pq' d e).den ∣ C11T23_den) := by
  constructor <;> decide +kernel
theorem C11T23_rload_2 : C11T23.rload 2 = ((2664353 / 2709288), (-950765 / 301032)) := by decide +kernel
#print axioms C11T23_ok
#print axioms C11T23_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
