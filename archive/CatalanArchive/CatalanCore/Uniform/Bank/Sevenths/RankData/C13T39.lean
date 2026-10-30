import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type dd121753545e35e713548ccf15b11812eac5c33090e145b06454caad696c12b9, root class 13. -/
def C13T39 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C13T39_ok : C13T39.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T39_den : ℕ := 1
theorem C13T39_den_ok :
    (∀ d ∈ C13T39.R, ∀ e ∈ C13T39.R, (C13T39.Lq d e).den ∣ C13T39_den ∧ (C13T39.Lq' d e).den ∣ C13T39_den) ∧
    (∀ d ∈ C13T39.C, ∀ e ∈ C13T39.C, (C13T39.Pq d e).den ∣ C13T39_den ∧ (C13T39.Pq' d e).den ∣ C13T39_den) := by
  constructor <;> decide +kernel
theorem C13T39_cload_0 : C13T39.cload 0 = (1, 0) := by decide +kernel
#print axioms C13T39_ok
#print axioms C13T39_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
