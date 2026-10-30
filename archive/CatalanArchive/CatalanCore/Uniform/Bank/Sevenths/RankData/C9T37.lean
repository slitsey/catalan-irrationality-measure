import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 842649ede86ada17da76990835cb42706542b01220eb6376edb24d57e3aadf44, root class 9. -/
def C9T37 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 4) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C9T37_ok : C9T37.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T37_den : ℕ := 1
theorem C9T37_den_ok :
    (∀ d ∈ C9T37.R, ∀ e ∈ C9T37.R, (C9T37.Lq d e).den ∣ C9T37_den ∧ (C9T37.Lq' d e).den ∣ C9T37_den) ∧
    (∀ d ∈ C9T37.C, ∀ e ∈ C9T37.C, (C9T37.Pq d e).den ∣ C9T37_den ∧ (C9T37.Pq' d e).den ∣ C9T37_den) := by
  constructor <;> decide +kernel
theorem C9T37_cload_0 : C9T37.cload 0 = (1, (-7 / 4)) := by decide +kernel
#print axioms C9T37_ok
#print axioms C9T37_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
