import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d3c8059bdd5f37a9f9c86ea673ff5283de21adb15292e5322215e58a04860f77, root class 13. -/
def C13T37 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 6) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C13T37_ok : C13T37.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T37_den : ℕ := 1
theorem C13T37_den_ok :
    (∀ d ∈ C13T37.R, ∀ e ∈ C13T37.R, (C13T37.Lq d e).den ∣ C13T37_den ∧ (C13T37.Lq' d e).den ∣ C13T37_den) ∧
    (∀ d ∈ C13T37.C, ∀ e ∈ C13T37.C, (C13T37.Pq d e).den ∣ C13T37_den ∧ (C13T37.Pq' d e).den ∣ C13T37_den) := by
  constructor <;> decide +kernel
theorem C13T37_cload_0 : C13T37.cload 0 = (1, (-7 / 6)) := by decide +kernel
#print axioms C13T37_ok
#print axioms C13T37_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
