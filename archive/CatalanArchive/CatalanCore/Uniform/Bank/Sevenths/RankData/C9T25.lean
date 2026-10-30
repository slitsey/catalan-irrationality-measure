import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bf2970a9a3c1a361b0e1c396616c0b833811406352db71e1297e6bda54c3fe62, root class 9. -/
def C9T25 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-557416 / 7589241) | 1, 1 => 1 | 1, 2 => (-23600 / 689931) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (557416 / 7589241) | 1, 1 => 1 | 1, 2 => (23600 / 689931) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C9T25_ok : C9T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T25_den : ℕ := 7589241
theorem C9T25_den_ok :
    (∀ d ∈ C9T25.R, ∀ e ∈ C9T25.R, (C9T25.Lq d e).den ∣ C9T25_den ∧ (C9T25.Lq' d e).den ∣ C9T25_den) ∧
    (∀ d ∈ C9T25.C, ∀ e ∈ C9T25.C, (C9T25.Pq d e).den ∣ C9T25_den ∧ (C9T25.Pq' d e).den ∣ C9T25_den) := by
  constructor <;> decide +kernel
theorem C9T25_cload_2 : C9T25.cload 2 = ((6772225 / 7589241), (-1011251 / 919908)) := by decide +kernel
#print axioms C9T25_ok
#print axioms C9T25_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
