import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type f5289cf50541d7897e30c63bf208be51dc9dbd50d07f783ca62f2eddd0128564, prime class 3 mod 10. -/
def C3T06 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | 2 => (-179 / 84) | 3 => (-2987 / 1428) | 4 => (-8125 / 3927) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | 2 => (-40105 / 7056) | 3 => (-1282241 / 226576) | 4 => (-38713445 / 6853924) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (-3835080474129351941 / 229909555277365421304) | 1, 1 => 1 | 1, 4 => (-184088555336005553 / 24633166636860580854) | 2, 2 => 1 | 2, 4 => (-78395927288438567 / 16422111091240387236) | 3, 3 => 1 | 3, 4 => (-187880690083267 / 53667029709935906) | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 4 => (3835080474129351941 / 229909555277365421304) | 1, 1 => 1 | 1, 4 => (184088555336005553 / 24633166636860580854) | 2, 2 => 1 | 2, 4 => (78395927288438567 / 16422111091240387236) | 3, 3 => 1 | 3, 4 => (187880690083267 / 53667029709935906) | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := {4}

theorem C3T06_ok : C3T06.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T06_den : ℕ := 689728665832096263912
theorem C3T06_den_ok :
    (∀ d ∈ C3T06.R, ∀ e ∈ C3T06.R, (C3T06.Lq d e).den ∣ C3T06_den ∧ (C3T06.Lq' d e).den ∣ C3T06_den) ∧
    (∀ d ∈ C3T06.C, ∀ e ∈ C3T06.C, (C3T06.Pq d e).den ∣ C3T06_den ∧ (C3T06.Pq' d e).den ∣ C3T06_den) := by
  constructor <;> decide +kernel
theorem C3T06_cload_4 : C3T06.cload 4 = ((667361673285235485307 / 689728665832096263912), (-458270427375132250883 / 229909555277365421304)) := by decide +kernel
#print axioms C3T06_ok
#print axioms C3T06_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
