import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type e664d3e735f99b451dc0acb28ae61079aacc2ecdb076a65efaa4dd2c3afb49d9, prime class 7 mod 10. -/
def C7T21 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-27 / 200) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (27 / 200) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C7T21_ok : C7T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T21_den : ℕ := 200
theorem C7T21_den_ok :
    (∀ d ∈ C7T21.R, ∀ e ∈ C7T21.R, (C7T21.Lq d e).den ∣ C7T21_den ∧ (C7T21.Lq' d e).den ∣ C7T21_den) ∧
    (∀ d ∈ C7T21.C, ∀ e ∈ C7T21.C, (C7T21.Pq d e).den ∣ C7T21_den ∧ (C7T21.Pq' d e).den ∣ C7T21_den) := by
  constructor <;> decide +kernel
theorem C7T21_cload_1 : C7T21.cload 1 = ((173 / 200), (-16 / 15)) := by decide +kernel
#print axioms C7T21_ok
#print axioms C7T21_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
