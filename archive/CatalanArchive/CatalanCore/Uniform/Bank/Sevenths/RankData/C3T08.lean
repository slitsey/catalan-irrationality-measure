import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type db14f0acac1df0d7735d90e463ef5aad90856e5902458dd905c1afb0eecfa418, root class 3. -/
def C3T08 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | 4 => (-664 / 1235) | 5 => (-22406 / 40755) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | 4 => (-9928171 / 9151350) | 5 => (-3620520521 / 3321940050) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (-558959271015284798237364 / 1236718077708539662968875) | 1, 1 => 1 | 1, 5 => (-2148559966876929674763 / 13018085028510943820725) | 2, 2 => 1 | 2, 5 => (-24692124759856523176256 / 247343615541707932593775) | 3, 3 => 1 | 3, 5 => (-84525020476507724496 / 1183462275319176710975) | 4, 4 => 1 | 4, 5 => (-55647252082100937264 / 1001391156039303370825) | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 5 => (558959271015284798237364 / 1236718077708539662968875) | 1, 1 => 1 | 1, 5 => (2148559966876929674763 / 13018085028510943820725) | 2, 2 => 1 | 2, 5 => (24692124759856523176256 / 247343615541707932593775) | 3, 3 => 1 | 3, 5 => (84525020476507724496 / 1183462275319176710975) | 4, 4 => 1 | 4, 5 => (55647252082100937264 / 1001391156039303370825) | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := {5}

theorem C3T08_ok : C3T08.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T08_den : ℕ := 1236718077708539662968875
theorem C3T08_den_ok :
    (∀ d ∈ C3T08.R, ∀ e ∈ C3T08.R, (C3T08.Lq d e).den ∣ C3T08_den ∧ (C3T08.Lq' d e).den ∣ C3T08_den) ∧
    (∀ d ∈ C3T08.C, ∀ e ∈ C3T08.C, (C3T08.Pq d e).den ∣ C3T08_den ∧ (C3T08.Pq' d e).den ∣ C3T08_den) := by
  constructor <;> decide +kernel
theorem C3T08_cload_5 : C3T08.cload 5 = ((193131983321318700128386 / 1236718077708539662968875), (-1402631172187181546136 / 3805286392949352809135)) := by decide +kernel
#print axioms C3T08_ok
#print axioms C3T08_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
