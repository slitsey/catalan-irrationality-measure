import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d0495666ea38061ec01096575bd2e0727d64360b2fd091078ab501bd773eae69, root class 5. -/
def C5T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | 4 => (-3373 / 2040) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | 4 => (-19831909 / 4161600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-65238830841759 / 87522912716120) | 1, 1 => 1 | 1, 4 => (-324471202172 / 1562909155645) | 2, 2 => 1 | 2, 4 => (-4181459817993 / 35009165086448) | 3, 3 => 1 | 3, 4 => (-86203679097 / 1029681326072) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (65238830841759 / 87522912716120) | 1, 1 => 1 | 1, 4 => (324471202172 / 1562909155645) | 2, 2 => 1 | 2, 4 => (4181459817993 / 35009165086448) | 3, 3 => 1 | 3, 4 => (86203679097 / 1029681326072) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C5T15_ok : C5T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T15_den : ℕ := 175045825432240
theorem C5T15_den_ok :
    (∀ d ∈ C5T15.R, ∀ e ∈ C5T15.R, (C5T15.Lq d e).den ∣ C5T15_den ∧ (C5T15.Lq' d e).den ∣ C5T15_den) ∧
    (∀ d ∈ C5T15.C, ∀ e ∈ C5T15.C, (C5T15.Pq d e).den ∣ C5T15_den ∧ (C5T15.Pq' d e).den ∣ C5T15_den) := by
  constructor <;> decide +kernel
theorem C5T15_cload_4 : C5T15.cload 4 = ((-27334535430997 / 175045825432240), (-37058845307039 / 35009165086448)) := by decide +kernel
#print axioms C5T15_ok
#print axioms C5T15_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
