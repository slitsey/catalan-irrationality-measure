import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type adac0c11236189e50a519f29c81d9cad67e163b4b9ffb4b51e460f4d8bc20dc3, prime class 3 mod 10. -/
def C3T11 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | 3 => (-2987 / 1428) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | 3 => (-1282241 / 226576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-2130534199 / 100684749627) | 1, 1 => 1 | 1, 3 => (-273290287 / 28767071322) | 2, 2 => 1 | 2, 3 => (-1712848 / 282030111) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (2130534199 / 100684749627) | 1, 1 => 1 | 1, 3 => (273290287 / 28767071322) | 2, 2 => 1 | 2, 3 => (1712848 / 282030111) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C3T11_ok : C3T11.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T11_den : ℕ := 201369499254
theorem C3T11_den_ok :
    (∀ d ∈ C3T11.R, ∀ e ∈ C3T11.R, (C3T11.Lq d e).den ∣ C3T11_den ∧ (C3T11.Lq' d e).den ∣ C3T11_den) ∧
    (∀ d ∈ C3T11.C, ∀ e ∈ C3T11.C, (C3T11.Pq d e).den ∣ C3T11_den ∧ (C3T11.Pq' d e).den ∣ C3T11_den) := by
  constructor <;> decide +kernel
theorem C3T11_cload_3 : C3T11.cload 3 = ((64657475125 / 67123166418), (-134572400701 / 67123166418)) := by decide +kernel
#print axioms C3T11_ok
#print axioms C3T11_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
