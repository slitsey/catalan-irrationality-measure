import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c45d36eea45479fbaf7a760b6e5a0a923285d50d2031482b27d95338d87c87b0, root class 11. -/
def C11T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | 4 => (-9725 / 3312) | 5 => (-49177 / 16560) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | 4 => (-128509825 / 10969344) | 5 => (-3216706777 / 274233600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-1593188082487631854103 / 2202734646742935380800) | 1, 1 => 1 | 1, 5 => (-3392100526054625965759 / 22027346467429353808000) | 2, 2 => 1 | 2, 5 => (-1885063355357632828623 / 22027346467429353808000) | 3, 3 => 1 | 3, 5 => (-163000126914714674751 / 2753418308428669226000) | 4, 4 => 1 | 4, 5 => (-1353957938436150903 / 29928459874224665500) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (1593188082487631854103 / 2202734646742935380800) | 1, 1 => 1 | 1, 5 => (3392100526054625965759 / 22027346467429353808000) | 2, 2 => 1 | 2, 5 => (1885063355357632828623 / 22027346467429353808000) | 3, 3 => 1 | 3, 5 => (163000126914714674751 / 2753418308428669226000) | 4, 4 => 1 | 4, 5 => (1353957938436150903 / 29928459874224665500) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C11T08_ok : C11T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T08_den : ℕ := 22027346467429353808000
theorem C11T08_den_ok :
    (∀ d ∈ C11T08.R, ∀ e ∈ C11T08.R, (C11T08.Lq d e).den ∣ C11T08_den ∧ (C11T08.Lq' d e).den ∣ C11T08_den) ∧
    (∀ d ∈ C11T08.C, ∀ e ∈ C11T08.C, (C11T08.Pq d e).den ∣ C11T08_den ∧ (C11T08.Pq' d e).den ∣ C11T08_den) := by
  constructor <;> decide +kernel
theorem C11T08_cload_5 : C11T08.cload 5 = ((-370553074216486997507 / 5506836616857338452000), (-81022178907268443019613 / 39649223641372836854400)) := by decide +kernel
#print axioms C11T08_ok
#print axioms C11T08_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
