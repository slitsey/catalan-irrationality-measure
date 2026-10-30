import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 9a18cbe4e031ba809fbe0155187e3c42afda4001619920c28f11b09f127d1603, prime class 7 mod 10. -/
def C7T11 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-21570053 / 23235264) | 1, 1 => 1 | 1, 3 => (-4826141 / 15490176) | 2, 2 => 1 | 2, 3 => (-6893 / 37236) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (21570053 / 23235264) | 1, 1 => 1 | 1, 3 => (4826141 / 15490176) | 2, 2 => 1 | 2, 3 => (6893 / 37236) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C7T11_ok : C7T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T11_den : ℕ := 46470528
theorem C7T11_den_ok :
    (∀ d ∈ C7T11.R, ∀ e ∈ C7T11.R, (C7T11.Lq d e).den ∣ C7T11_den ∧ (C7T11.Lq' d e).den ∣ C7T11_den) ∧
    (∀ d ∈ C7T11.C, ∀ e ∈ C7T11.C, (C7T11.Pq d e).den ∣ C7T11_den ∧ (C7T11.Pq' d e).den ∣ C7T11_den) := by
  constructor <;> decide +kernel
theorem C7T11_cload_3 : C7T11.cload 3 = ((-19750465 / 46470528), (-3784951 / 7745088)) := by decide +kernel
#print axioms C7T11_ok
#print axioms C7T11_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
