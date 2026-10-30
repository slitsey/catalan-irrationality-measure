import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b53748c18ca1b70c2437fb0a65603f8fd84a28f4b4093cae5561640f976f0259, root class 11. -/
def C11T11 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | 3 => (-10553 / 3312) | 4 => (-52489 / 16560) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | 3 => (-129195409 / 10969344) | 4 => (-3227676121 / 274233600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-56981650957349723 / 8559755258127940160) | 4, 1 => (-10200034271891259 / 3515613766731118280) | 4, 2 => (-45182940172374483 / 24609296367117827960) | 4, 3 => (-716983508627259 / 534984703632996260) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (56981650957349723 / 8559755258127940160) | 4, 1 => (10200034271891259 / 3515613766731118280) | 4, 2 => (45182940172374483 / 24609296367117827960) | 4, 3 => (716983508627259 / 534984703632996260) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C11T11_ok : C11T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T11_den : ℕ := 196874370936942623680
theorem C11T11_den_ok :
    (∀ d ∈ C11T11.R, ∀ e ∈ C11T11.R, (C11T11.Lq d e).den ∣ C11T11_den ∧ (C11T11.Lq' d e).den ∣ C11T11_den) ∧
    (∀ d ∈ C11T11.C, ∀ e ∈ C11T11.C, (C11T11.Pq d e).den ∣ C11T11_den ∧ (C11T11.Pq' d e).den ∣ C11T11_den) := by
  constructor <;> decide +kernel
theorem C11T11_rload_4 : C11T11.rload 4 = ((194367277593143842371 / 196874370936942623680), (-1108000516289251149401 / 354373867686496722624)) := by decide +kernel
#print axioms C11T11_ok
#print axioms C11T11_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
