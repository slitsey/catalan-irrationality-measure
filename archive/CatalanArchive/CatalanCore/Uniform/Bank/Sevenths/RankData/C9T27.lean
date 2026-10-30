import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5df7f2be6866cac98635e379887e2b0f592120aaec07c2eb716c31500997518f, root class 9. -/
def C9T27 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-159 / 88) | 1, 1 => 1 | 1, 2 => (-13 / 22) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (159 / 88) | 1, 1 => 1 | 1, 2 => (13 / 22) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C9T27_ok : C9T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T27_den : ℕ := 88
theorem C9T27_den_ok :
    (∀ d ∈ C9T27.R, ∀ e ∈ C9T27.R, (C9T27.Lq d e).den ∣ C9T27_den ∧ (C9T27.Lq' d e).den ∣ C9T27_den) ∧
    (∀ d ∈ C9T27.C, ∀ e ∈ C9T27.C, (C9T27.Pq d e).den ∣ C9T27_den ∧ (C9T27.Pq' d e).den ∣ C9T27_den) := by
  constructor <;> decide +kernel
theorem C9T27_cload_2 : C9T27.cload 2 = ((-123 / 88), (-39 / 88)) := by decide +kernel
#print axioms C9T27_ok
#print axioms C9T27_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
