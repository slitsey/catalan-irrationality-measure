import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 4add6df19056791388ac0831af339deed09c783b587b4808c3f7469f282eeae8, prime class 7 mod 10. -/
def C7T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-21570053 / 23235264) | 3, 1 => (-4826141 / 15490176) | 3, 2 => (-6893 / 37236) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (21570053 / 23235264) | 3, 1 => (4826141 / 15490176) | 3, 2 => (6893 / 37236) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C7T12_ok : C7T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T12_den : ℕ := 46470528
theorem C7T12_den_ok :
    (∀ d ∈ C7T12.R, ∀ e ∈ C7T12.R, (C7T12.Lq d e).den ∣ C7T12_den ∧ (C7T12.Lq' d e).den ∣ C7T12_den) ∧
    (∀ d ∈ C7T12.C, ∀ e ∈ C7T12.C, (C7T12.Pq d e).den ∣ C7T12_den ∧ (C7T12.Pq' d e).den ∣ C7T12_den) := by
  constructor <;> decide +kernel
theorem C7T12_rload_3 : C7T12.rload 3 = ((-19750465 / 46470528), (-3784951 / 7745088)) := by decide +kernel
#print axioms C7T12_ok
#print axioms C7T12_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
