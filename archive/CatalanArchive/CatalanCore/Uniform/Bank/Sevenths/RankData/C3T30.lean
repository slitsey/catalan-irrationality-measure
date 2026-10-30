import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 1812eccbb947aaec7b741abecee414934813c24bfdb529f29bffeea7a928d25d, root class 3. -/
def C3T30 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-125 / 588) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (125 / 588) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C3T30_ok : C3T30.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T30_den : ℕ := 588
theorem C3T30_den_ok :
    (∀ d ∈ C3T30.R, ∀ e ∈ C3T30.R, (C3T30.Lq d e).den ∣ C3T30_den ∧ (C3T30.Lq' d e).den ∣ C3T30_den) ∧
    (∀ d ∈ C3T30.C, ∀ e ∈ C3T30.C, (C3T30.Pq d e).den ∣ C3T30_den ∧ (C3T30.Pq' d e).den ∣ C3T30_den) := by
  constructor <;> decide +kernel
theorem C3T30_cload_1 : C3T30.cload 1 = ((463 / 588), (-24 / 35)) := by decide +kernel
#print axioms C3T30_ok
#print axioms C3T30_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
