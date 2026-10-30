import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5122a520575d353de23c86a4d69671c4a05f0053134c746e80baabe1fc9b52e3, root class 3. -/
def C3T11 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | 2 => (-355 / 462) | 3 => (-1621 / 2310) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | 2 => (-210571 / 213444) | 3 => (-5050831 / 5336100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-442372438819 / 4350757692050) | 1, 1 => 1 | 1, 3 => (-12069123711 / 248614725260) | 2, 2 => 1 | 2, 3 => (-897096819 / 28251673325) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (442372438819 / 4350757692050) | 1, 1 => 1 | 1, 3 => (12069123711 / 248614725260) | 2, 2 => 1 | 2, 3 => (897096819 / 28251673325) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C3T11_ok : C3T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T11_den : ℕ := 8701515384100
theorem C3T11_den_ok :
    (∀ d ∈ C3T11.R, ∀ e ∈ C3T11.R, (C3T11.Lq d e).den ∣ C3T11_den ∧ (C3T11.Lq' d e).den ∣ C3T11_den) ∧
    (∀ d ∈ C3T11.C, ∀ e ∈ C3T11.C, (C3T11.Pq d e).den ∣ C3T11_den ∧ (C3T11.Pq' d e).den ∣ C3T11_den) := by
  constructor <;> decide +kernel
theorem C3T11_cload_3 : C3T11.cload 3 = ((284721814253 / 348060615364), (-4331966659781 / 8701515384100)) := by decide +kernel
#print axioms C3T11_ok
#print axioms C3T11_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
