import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b3a7248196c182663220a4ff27fa3da6129b25a4f603d88861db031810339133, root class 3. -/
def C3T19 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | 2 => (-355 / 462) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | 2 => (-210571 / 213444) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-309879 / 2175404) | 1, 1 => 1 | 1, 2 => (-21195 / 310772) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (309879 / 2175404) | 1, 1 => 1 | 1, 2 => (21195 / 310772) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C3T19_ok : C3T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T19_den : ℕ := 2175404
theorem C3T19_den_ok :
    (∀ d ∈ C3T19.R, ∀ e ∈ C3T19.R, (C3T19.Lq d e).den ∣ C3T19_den ∧ (C3T19.Lq' d e).den ∣ C3T19_den) ∧
    (∀ d ∈ C3T19.C, ∀ e ∈ C3T19.C, (C3T19.Pq d e).den ∣ C3T19_den ∧ (C3T19.Pq' d e).den ∣ C3T19_den) := by
  constructor <;> decide +kernel
theorem C3T19_cload_2 : C3T19.cload 2 = ((429290 / 543851), (-481787 / 932316)) := by decide +kernel
#print axioms C3T19_ok
#print axioms C3T19_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
