import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type b5dda78fef8d3625f26362d5b2b1f8aba2cadf908b16d50e89a811205418eff9, prime class 7 mod 10. -/
def C7T05 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-5 / 3) | 1 => (-31 / 24) | 2 => (-367 / 312) | 3 => (-1049 / 936) | 4 => (-23425 / 21528) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | 1 => (-1249 / 576) | 2 => (-201145 / 97344) | 3 => (-1780561 / 876096) | 4 => (-934853245 / 463454784) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (-1611583814810952389 / 34172714638725499096) | 4, 1 => (-281450907868674667 / 12814767989522062161) | 4, 2 => (-9350516047013281 / 657167589206259598) | 4, 3 => (-3453180342883263 / 328583794603129799) | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 0 => (1611583814810952389 / 34172714638725499096) | 4, 1 => (281450907868674667 / 12814767989522062161) | 4, 2 => (9350516047013281 / 657167589206259598) | 4, 3 => (3453180342883263 / 328583794603129799) | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := {4}
  kc := ∅

theorem C7T05_ok : C7T05.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T05_den : ℕ := 102518143916176497288
theorem C7T05_den_ok :
    (∀ d ∈ C7T05.R, ∀ e ∈ C7T05.R, (C7T05.Lq d e).den ∣ C7T05_den ∧ (C7T05.Lq' d e).den ∣ C7T05_den) ∧
    (∀ d ∈ C7T05.C, ∀ e ∈ C7T05.C, (C7T05.Pq d e).den ∣ C7T05_den ∧ (C7T05.Pq' d e).den ∣ C7T05_den) := by
  constructor <;> decide +kernel
theorem C7T05_rload_4 : C7T05.rload 4 = ((92895712438480592893 / 102518143916176497288), (-2830791024615067753 / 2971540403367434704)) := by decide +kernel
#print axioms C7T05_ok
#print axioms C7T05_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
