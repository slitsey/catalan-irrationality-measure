import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 0558577854194fd4405844a436ca7fad9d8824e160ba848f829ccf26127a3dfa, root class 1. -/
def C1T05 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | 3 => (-4351 / 1170) | 4 => (-147349 / 39780) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | 3 => (-21315271 / 1368900) | 4 => (-24629159851 / 1582448400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-441923691683696893669 / 96417304021209153689460) | 4, 1 => (-28614976699574943287 / 14462595603181373053419) | 4, 2 => (-8022459634995777671 / 6427820268080610245964) | 4, 3 => (-1469818880285923 / 1615842199115286638) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (441923691683696893669 / 96417304021209153689460) | 4, 1 => (28614976699574943287 / 14462595603181373053419) | 4, 2 => (8022459634995777671 / 6427820268080610245964) | 4, 3 => (1469818880285923 / 1615842199115286638) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C1T05_ok : C1T05.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T05_den : ℕ := 289251912063627461068380
theorem C1T05_den_ok :
    (∀ d ∈ C1T05.R, ∀ e ∈ C1T05.R, (C1T05.Lq d e).den ∣ C1T05_den ∧ (C1T05.Lq' d e).den ∣ C1T05_den) ∧
    (∀ d ∈ C1T05.C, ∀ e ∈ C1T05.C, (C1T05.Pq d e).den ∣ C1T05_den ∧ (C1T05.Pq' d e).den ∣ C1T05_den) := by
  constructor <;> decide +kernel
theorem C1T05_rload_4 : C1T05.rload 4 = ((71682429623312519612552 / 72312978015906865267095), (-707739483381693894634471 / 192834608042418307378920)) := by decide +kernel
#print axioms C1T05_ok
#print axioms C1T05_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
