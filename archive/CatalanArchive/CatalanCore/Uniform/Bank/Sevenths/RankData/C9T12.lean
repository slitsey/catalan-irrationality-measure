import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type c536751ca47fa2ccd0a8a6bd167531ed10a884c59c882ab63610fb7ce77dc9ee, root class 9. -/
def C9T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | 3 => (-12097 / 9900) | 4 => (-94301 / 79200) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | 3 => (-228949609 / 98010000) | 4 => (-14560890601 / 6272640000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-143798707676021772955979 / 3435839359978918113005400) | 1, 1 => 1 | 1, 4 => (-649092612635496959047 / 33465967792002449152650) | 2, 2 => 1 | 2, 4 => (-652917025932047249983 / 52058172120892698681900) | 3, 3 => 1 | 3, 4 => (-1070645538906472687 / 115684826935317108182) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (143798707676021772955979 / 3435839359978918113005400) | 1, 1 => 1 | 1, 4 => (649092612635496959047 / 33465967792002449152650) | 2, 2 => 1 | 2, 4 => (652917025932047249983 / 52058172120892698681900) | 3, 3 => 1 | 3, 4 => (1070645538906472687 / 115684826935317108182) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C9T12_ok : C9T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T12_den : ℕ := 10307518079936754339016200
theorem C9T12_den_ok :
    (∀ d ∈ C9T12.R, ∀ e ∈ C9T12.R, (C9T12.Lq d e).den ∣ C9T12_den ∧ (C9T12.Lq' d e).den ∣ C9T12_den) ∧
    (∀ d ∈ C9T12.C, ∀ e ∈ C9T12.C, (C9T12.Pq d e).den ∣ C9T12_den ∧ (C9T12.Pq' d e).den ∣ C9T12_den) := by
  constructor <;> decide +kernel
theorem C9T12_cload_4 : C9T12.cload 4 = ((9451529343565843884853453 / 10307518079936754339016200), (-26568030354499583284849 / 24987922618028495367312)) := by decide +kernel
#print axioms C9T12_ok
#print axioms C9T12_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
