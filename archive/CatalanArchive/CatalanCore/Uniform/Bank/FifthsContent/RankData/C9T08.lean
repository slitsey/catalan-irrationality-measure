import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type ff3979c343ecdad438f55022c4881ed7eac2c18651ac22caaeb6afb466022da4, prime class 9 mod 10. -/
def C9T08 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 4) | 1 => (-29 / 36) | 2 => (-167 / 252) | 3 => (-2837 / 4788) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 16) | 1 => (-1129 / 1296) | 2 => (-47545 / 63504) | 3 => (-16204129 / 22924944) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-444476250928 / 3789967574799) | 1, 1 => 1 | 1, 3 => (-23740084136 / 421107508311) | 2, 2 => 1 | 2, 3 => (-2224381504 / 60158215473) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (444476250928 / 3789967574799) | 1, 1 => 1 | 1, 3 => (23740084136 / 421107508311) | 2, 2 => 1 | 2, 3 => (2224381504 / 60158215473) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C9T08_ok : C9T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T08_den : ℕ := 3789967574799
theorem C9T08_den_ok :
    (∀ d ∈ C9T08.R, ∀ e ∈ C9T08.R, (C9T08.Lq d e).den ∣ C9T08_den ∧ (C9T08.Lq' d e).den ∣ C9T08_den) ∧
    (∀ d ∈ C9T08.C, ∀ e ∈ C9T08.C, (C9T08.Pq d e).den ∣ C9T08_den ∧ (C9T08.Pq' d e).den ∣ C9T08_den) := by
  constructor <;> decide +kernel
theorem C9T08_cload_3 : C9T08.cload 3 = ((2991694531895 / 3789967574799), (-5700256030927 / 15159870299196)) := by decide +kernel
#print axioms C9T08_ok
#print axioms C9T08_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
