import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c4e2fcfc33cc60aa271714deddcf173a880d64e0916032634e26bb6d236740df, root class 11. -/
def C11T09 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | 4 => (-9725 / 3312) | 5 => (-49177 / 16560) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | 4 => (-128509825 / 10969344) | 5 => (-3216706777 / 274233600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-1593188082487631854103 / 2202734646742935380800) | 5, 1 => (-3392100526054625965759 / 22027346467429353808000) | 5, 2 => (-1885063355357632828623 / 22027346467429353808000) | 5, 3 => (-163000126914714674751 / 2753418308428669226000) | 5, 4 => (-1353957938436150903 / 29928459874224665500) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (1593188082487631854103 / 2202734646742935380800) | 5, 1 => (3392100526054625965759 / 22027346467429353808000) | 5, 2 => (1885063355357632828623 / 22027346467429353808000) | 5, 3 => (163000126914714674751 / 2753418308428669226000) | 5, 4 => (1353957938436150903 / 29928459874224665500) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C11T09_ok : C11T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T09_den : ℕ := 22027346467429353808000
theorem C11T09_den_ok :
    (∀ d ∈ C11T09.R, ∀ e ∈ C11T09.R, (C11T09.Lq d e).den ∣ C11T09_den ∧ (C11T09.Lq' d e).den ∣ C11T09_den) ∧
    (∀ d ∈ C11T09.C, ∀ e ∈ C11T09.C, (C11T09.Pq d e).den ∣ C11T09_den ∧ (C11T09.Pq' d e).den ∣ C11T09_den) := by
  constructor <;> decide +kernel
theorem C11T09_rload_5 : C11T09.rload 5 = ((-370553074216486997507 / 5506836616857338452000), (-81022178907268443019613 / 39649223641372836854400)) := by decide +kernel
#print axioms C11T09_ok
#print axioms C11T09_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
