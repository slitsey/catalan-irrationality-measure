import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type a324b67329537906460c19bc6c039ca50b36b9e5cf1b2cca82e095cea1b59636, prime class 3 mod 10. -/
def C3T01 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | 3 => (-151 / 84) | 4 => (-1315 / 714) | 5 => (-36698 / 19635) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | 3 => (-4369 / 784) | 4 => (-79255 / 14161) | 5 => (-960982201 / 171348100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-8405694596892102406742 / 14235583927280960561625) | 5, 1 => (-17953966647573889756223 / 113884671418247684493000) | 5, 2 => (-2199650299145493243361 / 24403858161053075248500) | 5, 3 => (-5178732743378145443 / 82167872596138300500) | 5, 4 => (-643806354365584562 / 13291861743492960375) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (8405694596892102406742 / 14235583927280960561625) | 5, 1 => (17953966647573889756223 / 113884671418247684493000) | 5, 2 => (2199650299145493243361 / 24403858161053075248500) | 5, 3 => (5178732743378145443 / 82167872596138300500) | 5, 4 => (643806354365584562 / 13291861743492960375) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C3T01_ok : C3T01.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T01_den : ℕ := 341654014254743053479000
theorem C3T01_den_ok :
    (∀ d ∈ C3T01.R, ∀ e ∈ C3T01.R, (C3T01.Lq d e).den ∣ C3T01_den ∧ (C3T01.Lq' d e).den ∣ C3T01_den) ∧
    (∀ d ∈ C3T01.C, ∀ e ∈ C3T01.C, (C3T01.Pq d e).den ∣ C3T01_den ∧ (C3T01.Pq' d e).den ∣ C3T01_den) := by
  constructor <;> decide +kernel
theorem C3T01_rload_5 : C3T01.rload 5 = ((2454110074142100958261 / 48807716322106150497000), (-145261294629912588135583 / 113884671418247684493000)) := by decide +kernel
#print axioms C3T01_ok
#print axioms C3T01_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
