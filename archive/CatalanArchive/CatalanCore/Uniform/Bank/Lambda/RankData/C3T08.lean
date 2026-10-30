import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 074732c39699e79acaeec4a86b625b7eaf622cfc7546c9a053e88d02d766e282, root class 3. -/
def C3T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | 3 => (-67 / 154) | 4 => (-2087 / 4620) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | 3 => (-62285 / 71148) | 4 => (-18869299 / 21344400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-6778938569691 / 11630782688140) | 4, 1 => (-90294790841 / 415385096005) | 4, 2 => (-219518198481 / 1661540384020) | 4, 3 => (-7153546011 / 75524562910) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (6778938569691 / 11630782688140) | 4, 1 => (90294790841 / 415385096005) | 4, 2 => (219518198481 / 1661540384020) | 4, 3 => (7153546011 / 75524562910) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C3T08_ok : C3T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T08_den : ℕ := 11630782688140
theorem C3T08_den_ok :
    (∀ d ∈ C3T08.R, ∀ e ∈ C3T08.R, (C3T08.Lq d e).den ∣ C3T08_den ∧ (C3T08.Lq' d e).den ∣ C3T08_den) ∧
    (∀ d ∈ C3T08.C, ∀ e ∈ C3T08.C, (C3T08.Pq d e).den ∣ C3T08_den ∧ (C3T08.Pq' d e).den ∣ C3T08_den) := by
  constructor <;> decide +kernel
theorem C3T08_rload_4 : C3T08.rload 4 = ((-15734175008 / 581539134407), (-6619969800313 / 23261565376280)) := by decide +kernel
#print axioms C3T08_ok
#print axioms C3T08_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
