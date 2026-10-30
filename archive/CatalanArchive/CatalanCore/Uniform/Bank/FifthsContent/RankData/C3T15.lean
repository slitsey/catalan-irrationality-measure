import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 28dd3441fb3df98c3f0da256a6184237d0ded0e1ac616fc865639d894ac36e87, prime class 3 mod 10. -/
def C3T15 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | 3 => (-151 / 84) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | 3 => (-4369 / 784) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-26021 / 23058) | 3, 1 => (-6943 / 23058) | 3, 2 => (-21 / 122) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (26021 / 23058) | 3, 1 => (6943 / 23058) | 3, 2 => (21 / 122) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C3T15_ok : C3T15.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T15_den : ℕ := 23058
theorem C3T15_den_ok :
    (∀ d ∈ C3T15.R, ∀ e ∈ C3T15.R, (C3T15.Lq d e).den ∣ C3T15_den ∧ (C3T15.Lq' d e).den ∣ C3T15_den) ∧
    (∀ d ∈ C3T15.C, ∀ e ∈ C3T15.C, (C3T15.Pq d e).den ∣ C3T15_den ∧ (C3T15.Pq' d e).den ∣ C3T15_den) := by
  constructor <;> decide +kernel
theorem C3T15_rload_3 : C3T15.rload 3 = ((-4625 / 7686), (-8077 / 7686)) := by decide +kernel
#print axioms C3T15_ok
#print axioms C3T15_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
