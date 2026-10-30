import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type cb0f7fb7e99517e986dd2722d35f356f6f40c314a4d41995920adbcbdeb9288e, root class 1. -/
def C1T31 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T31_ok : C1T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T31_den : ℕ := 1
theorem C1T31_den_ok :
    (∀ d ∈ C1T31.R, ∀ e ∈ C1T31.R, (C1T31.Lq d e).den ∣ C1T31_den ∧ (C1T31.Lq' d e).den ∣ C1T31_den) ∧
    (∀ d ∈ C1T31.C, ∀ e ∈ C1T31.C, (C1T31.Pq d e).den ∣ C1T31_den ∧ (C1T31.Pq' d e).den ∣ C1T31_den) := by
  constructor <;> decide +kernel
#print axioms C1T31_ok
#print axioms C1T31_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
