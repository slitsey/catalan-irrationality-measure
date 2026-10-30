import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 8b2b161c38b85355607f1a350f2ed0d98224cb3c1a48db50168d38c80ff3bccf, prime class 3 mod 10. -/
def C3T27 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C3T27_ok : C3T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T27_den : ℕ := 1
theorem C3T27_den_ok :
    (∀ d ∈ C3T27.R, ∀ e ∈ C3T27.R, (C3T27.Lq d e).den ∣ C3T27_den ∧ (C3T27.Lq' d e).den ∣ C3T27_den) ∧
    (∀ d ∈ C3T27.C, ∀ e ∈ C3T27.C, (C3T27.Pq d e).den ∣ C3T27_den ∧ (C3T27.Pq' d e).den ∣ C3T27_den) := by
  constructor <;> decide +kernel
theorem C3T27_cload_1 : C3T27.cload 1 = (1, 0) := by decide +kernel
#print axioms C3T27_ok
#print axioms C3T27_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
