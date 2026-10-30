import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7c7254674864ee43abbbc1a9275c781770f4dd77b9f2c662c37fad7f844a1829, root class 5. -/
def C5T14 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | 4 => (-3373 / 2040) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | 4 => (-19831909 / 4161600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-65238830841759 / 87522912716120) | 4, 1 => (-324471202172 / 1562909155645) | 4, 2 => (-4181459817993 / 35009165086448) | 4, 3 => (-86203679097 / 1029681326072) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (65238830841759 / 87522912716120) | 4, 1 => (324471202172 / 1562909155645) | 4, 2 => (4181459817993 / 35009165086448) | 4, 3 => (86203679097 / 1029681326072) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C5T14_ok : C5T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T14_den : ℕ := 175045825432240
theorem C5T14_den_ok :
    (∀ d ∈ C5T14.R, ∀ e ∈ C5T14.R, (C5T14.Lq d e).den ∣ C5T14_den ∧ (C5T14.Lq' d e).den ∣ C5T14_den) ∧
    (∀ d ∈ C5T14.C, ∀ e ∈ C5T14.C, (C5T14.Pq d e).den ∣ C5T14_den ∧ (C5T14.Pq' d e).den ∣ C5T14_den) := by
  constructor <;> decide +kernel
theorem C5T14_rload_4 : C5T14.rload 4 = ((-27334535430997 / 175045825432240), (-37058845307039 / 35009165086448)) := by decide +kernel
#print axioms C5T14_ok
#print axioms C5T14_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
