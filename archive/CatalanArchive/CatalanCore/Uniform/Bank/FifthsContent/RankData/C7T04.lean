import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 75221e7747feb5eb99b437c246ead04782722188e7fb2bc8ac31d97564d07f67, prime class 7 mod 10. -/
def C7T04 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | 3 => (-263 / 312) | 4 => (-815 / 936) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | 3 => (-63443 / 32448) | 4 => (-1725805 / 876096) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-12947736411661 / 20383651345304) | 1, 1 => 1 | 1, 4 => (-3261114676441 / 15287738508978) | 2, 2 => 1 | 2, 4 => (-645979875197 / 5095912836326) | 3, 3 => 1 | 3, 4 => (-17643293937 / 195996647551) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (12947736411661 / 20383651345304) | 1, 1 => 1 | 1, 4 => (3261114676441 / 15287738508978) | 2, 2 => 1 | 2, 4 => (645979875197 / 5095912836326) | 3, 3 => 1 | 3, 4 => (17643293937 / 195996647551) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C7T04_ok : C7T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T04_den : ℕ := 61150954035912
theorem C7T04_den_ok :
    (∀ d ∈ C7T04.R, ∀ e ∈ C7T04.R, (C7T04.Lq d e).den ∣ C7T04_den ∧ (C7T04.Lq' d e).den ∣ C7T04_den) ∧
    (∀ d ∈ C7T04.C, ∀ e ∈ C7T04.C, (C7T04.Pq d e).den ∣ C7T04_den ∧ (C7T04.Pq' d e).den ∣ C7T04_den) := by
  constructor <;> decide +kernel
theorem C7T04_cload_4 : C7T04.cload 4 = ((-3993180115543 / 61150954035912), (-22514969996251 / 40767302690608)) := by decide +kernel
#print axioms C7T04_ok
#print axioms C7T04_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
