import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 67c82a215854bb760aa86151c4eaa592cedd12d61d05717a22ec5922b41d0e94, root class 3. -/
def C3T10 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | 2 => (-355 / 462) | 3 => (-1621 / 2310) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | 2 => (-210571 / 213444) | 3 => (-5050831 / 5336100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T10_ok : C3T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T10_den : ℕ := 1
theorem C3T10_den_ok :
    (∀ d ∈ C3T10.R, ∀ e ∈ C3T10.R, (C3T10.Lq d e).den ∣ C3T10_den ∧ (C3T10.Lq' d e).den ∣ C3T10_den) ∧
    (∀ d ∈ C3T10.C, ∀ e ∈ C3T10.C, (C3T10.Pq d e).den ∣ C3T10_den ∧ (C3T10.Pq' d e).den ∣ C3T10_den) := by
  constructor <;> decide +kernel
#print axioms C3T10_ok
#print axioms C3T10_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
