import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 6ab48924afa455dcd35eb57b5b6bc9e718d469f268f05abd33b8bb2a01ce347d, root class 1. -/
def C1T09 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | 4 => (-8681 / 1320) | 5 => (-253333 / 38280) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | 4 => (-28262327 / 580800) | 5 => (-4755507619 / 97690560) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (-118707554255272107612738103 / 98661232335208422006987750) | 5, 1 => (-5318432977719094311506641 / 35876811758257608002541000) | 5, 2 => (-11655602584612290617661313 / 147991848502812633010481625) | 5, 3 => (-23505581390243507710409 / 438494365934259653364390) | 5, 4 => (-4048666020665831701168 / 99657810439604466673725) | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 0 => (118707554255272107612738103 / 98661232335208422006987750) | 5, 1 => (5318432977719094311506641 / 35876811758257608002541000) | 5, 2 => (11655602584612290617661313 / 147991848502812633010481625) | 5, 3 => (23505581390243507710409 / 438494365934259653364390) | 5, 4 => (4048666020665831701168 / 99657810439604466673725) | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := {5}
  kc := ∅

theorem C1T09_ok : C1T09.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T09_den : ℕ := 1183934788022501064083853000
theorem C1T09_den_ok :
    (∀ d ∈ C1T09.R, ∀ e ∈ C1T09.R, (C1T09.Lq d e).den ∣ C1T09_den ∧ (C1T09.Lq' d e).den ∣ C1T09_den) ∧
    (∀ d ∈ C1T09.C, ∀ e ∈ C1T09.C, (C1T09.Pq d e).den ∣ C1T09_den ∧ (C1T09.Pq' d e).den ∣ C1T09_den) := by
  constructor <;> decide +kernel
theorem C1T09_rload_5 : C1T09.rload 5 = ((-620872194061560215917994033 / 1183934788022501064083853000), (-3638866639296810540691286813 / 789289858681667376055902000)) := by decide +kernel
#print axioms C1T09_ok
#print axioms C1T09_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
