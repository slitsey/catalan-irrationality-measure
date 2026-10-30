import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 501d0fe77a85e1addd69abc67d4d0febea11046181742a9d500bdb32e1c0ef65, root class 9. -/
def C9T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | 3 => (-12097 / 9900) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | 3 => (-228949609 / 98010000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-11167687421584 / 209530759246875) | 1, 1 => 1 | 1, 3 => (-18855299176 / 761930033625) | 2, 2 => 1 | 2, 3 => (-33892974784 / 2116472315625) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (11167687421584 / 209530759246875) | 1, 1 => 1 | 1, 3 => (18855299176 / 761930033625) | 2, 2 => 1 | 2, 3 => (33892974784 / 2116472315625) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C9T17_ok : C9T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T17_den : ℕ := 209530759246875
theorem C9T17_den_ok :
    (∀ d ∈ C9T17.R, ∀ e ∈ C9T17.R, (C9T17.Lq d e).den ∣ C9T17_den ∧ (C9T17.Lq' d e).den ∣ C9T17_den) ∧
    (∀ d ∈ C9T17.C, ∀ e ∈ C9T17.C, (C9T17.Pq d e).den ∣ C9T17_den ∧ (C9T17.Pq' d e).den ∣ C9T17_den) := by
  constructor <;> decide +kernel
theorem C9T17_cload_3 : C9T17.cload 3 = ((2530966133977 / 2793743456625), (-300024842874739 / 279374345662500)) := by decide +kernel
#print axioms C9T17_ok
#print axioms C9T17_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
