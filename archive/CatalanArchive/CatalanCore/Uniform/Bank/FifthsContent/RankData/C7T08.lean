import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type c65b06edba3c83f9ba2f9b123ace2489ab1021a00790295675ad6678ec196bb6, prime class 7 mod 10. -/
def C7T08 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | 3 => (-1049 / 936) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | 3 => (-1780561 / 876096) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-113678417239 / 1890837914082) | 1, 1 => 1 | 1, 3 => (-8840072452 / 315139652347) | 2, 2 => 1 | 2, 3 => (-440849522 / 24241511719) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (113678417239 / 1890837914082) | 1, 1 => 1 | 1, 3 => (8840072452 / 315139652347) | 2, 2 => 1 | 2, 3 => (440849522 / 24241511719) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C7T08_ok : C7T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T08_den : ℕ := 1890837914082
theorem C7T08_den_ok :
    (∀ d ∈ C7T08.R, ∀ e ∈ C7T08.R, (C7T08.Lq d e).den ∣ C7T08_den ∧ (C7T08.Lq' d e).den ∣ C7T08_den) ∧
    (∀ d ∈ C7T08.C, ∀ e ∈ C7T08.C, (C7T08.Pq d e).den ∣ C7T08_den ∧ (C7T08.Pq' d e).den ∣ C7T08_den) := by
  constructor <;> decide +kernel
theorem C7T08_cload_3 : C7T08.cload 3 = ((1689732799415 / 1890837914082), (-2427586154077 / 2521117218776)) := by decide +kernel
#print axioms C7T08_ok
#print axioms C7T08_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
