import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type e11ef3a895d95781b85958440cca3e260c39dcff2208bb312113145058abd6be, root class 9. -/
def C9T30 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-64 / 539) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (64 / 539) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C9T30_ok : C9T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T30_den : ℕ := 539
theorem C9T30_den_ok :
    (∀ d ∈ C9T30.R, ∀ e ∈ C9T30.R, (C9T30.Lq d e).den ∣ C9T30_den ∧ (C9T30.Lq' d e).den ∣ C9T30_den) ∧
    (∀ d ∈ C9T30.C, ∀ e ∈ C9T30.C, (C9T30.Pq d e).den ∣ C9T30_den ∧ (C9T30.Pq' d e).den ∣ C9T30_den) := by
  constructor <;> decide +kernel
theorem C9T30_cload_1 : C9T30.cload 1 = ((475 / 539), (-33 / 28)) := by decide +kernel
#print axioms C9T30_ok
#print axioms C9T30_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
