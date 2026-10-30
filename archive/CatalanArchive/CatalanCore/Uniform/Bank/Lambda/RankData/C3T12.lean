import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2d6974158ee62ec35f98bcd29c1613134ad5a5f6fedd6ecf04a6757926e17570, root class 3. -/
def C3T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | 2 => (-355 / 462) | 3 => (-1621 / 2310) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | 2 => (-210571 / 213444) | 3 => (-5050831 / 5336100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-442372438819 / 4350757692050) | 3, 1 => (-12069123711 / 248614725260) | 3, 2 => (-897096819 / 28251673325) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (442372438819 / 4350757692050) | 3, 1 => (12069123711 / 248614725260) | 3, 2 => (897096819 / 28251673325) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C3T12_ok : C3T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T12_den : ℕ := 8701515384100
theorem C3T12_den_ok :
    (∀ d ∈ C3T12.R, ∀ e ∈ C3T12.R, (C3T12.Lq d e).den ∣ C3T12_den ∧ (C3T12.Lq' d e).den ∣ C3T12_den) ∧
    (∀ d ∈ C3T12.C, ∀ e ∈ C3T12.C, (C3T12.Pq d e).den ∣ C3T12_den ∧ (C3T12.Pq' d e).den ∣ C3T12_den) := by
  constructor <;> decide +kernel
theorem C3T12_rload_3 : C3T12.rload 3 = ((284721814253 / 348060615364), (-4331966659781 / 8701515384100)) := by decide +kernel
#print axioms C3T12_ok
#print axioms C3T12_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
