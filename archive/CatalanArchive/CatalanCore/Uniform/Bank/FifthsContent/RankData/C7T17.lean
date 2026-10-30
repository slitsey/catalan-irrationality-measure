import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 2fc3d5c0873aafba8e4c44a1946a1f52505f6f1f17d3fcfcdebf37ef875fa92f, prime class 7 mod 10. -/
def C7T17 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-85 / 48) | 2, 1 => (-19 / 32) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (85 / 48) | 2, 1 => (19 / 32) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C7T17_ok : C7T17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T17_den : ℕ := 96
theorem C7T17_den_ok :
    (∀ d ∈ C7T17.R, ∀ e ∈ C7T17.R, (C7T17.Lq d e).den ∣ C7T17_den ∧ (C7T17.Lq' d e).den ∣ C7T17_den) ∧
    (∀ d ∈ C7T17.C, ∀ e ∈ C7T17.C, (C7T17.Pq d e).den ∣ C7T17_den ∧ (C7T17.Pq' d e).den ∣ C7T17_den) := by
  constructor <;> decide +kernel
theorem C7T17_rload_2 : C7T17.rload 2 = ((-131 / 96), (-19 / 48)) := by decide +kernel
#print axioms C7T17_ok
#print axioms C7T17_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
