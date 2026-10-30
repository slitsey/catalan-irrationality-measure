import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 78a03d829b67163594ca6c03fefa86713d6826f1614377b95badb19d24148210, root class 3. -/
def C3T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | 3 => (-3891 / 4940) | 4 => (-30557 / 40755) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | 3 => (-84001043 / 73210800) | 4 => (-3753398123 / 3321940050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-60437531785518937475625 / 851095280668746469018663) | 1, 1 => 1 | 1, 4 => (-4093936614099000833000 / 121585040095535209859809) | 2, 2 => 1 | 2, 4 => (-983907008904863280000 / 44794488456249814158877) | 3, 3 => 1 | 3, 4 => (-56103453347145891000 / 3445729881249985704529) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (60437531785518937475625 / 851095280668746469018663) | 1, 1 => 1 | 1, 4 => (4093936614099000833000 / 121585040095535209859809) | 2, 2 => 1 | 2, 4 => (983907008904863280000 / 44794488456249814158877) | 3, 3 => 1 | 3, 4 => (56103453347145891000 / 3445729881249985704529) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C3T12_ok : C3T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T12_den : ℕ := 851095280668746469018663
theorem C3T12_den_ok :
    (∀ d ∈ C3T12.R, ∀ e ∈ C3T12.R, (C3T12.Lq d e).den ∣ C3T12_den ∧ (C3T12.Lq' d e).den ∣ C3T12_den) ∧
    (∀ d ∈ C3T12.C, ∀ e ∈ C3T12.C, (C3T12.Pq d e).den ∣ C3T12_den ∧ (C3T12.Pq' d e).den ∣ C3T12_den) := by
  constructor <;> decide +kernel
theorem C3T12_cload_4 : C3T12.cload 4 = ((729448406438597088315038 / 851095280668746469018663), (-2492489969965951326860766 / 4255476403343732345093315)) := by decide +kernel
#print axioms C3T12_ok
#print axioms C3T12_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
