import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 0c1e8081b7f1bfba4487f1a75e2c44300905db921fe0b0245c71f3d8bf77ec45, root class 13. -/
def C13T18 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 6) | 1 => (-55 / 78) | 2 => (-433 / 780) | 3 => (-3377 / 7020) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | 1 => (-3961 / 6084) | 2 => (-318529 / 608400) | 3 => (-23637649 / 49280400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-803026684399 / 5910140194335) | 1, 1 => 1 | 1, 3 => (-19940748751 / 303084112530) | 2, 2 => 1 | 2, 3 => (-1311756032 / 30308411253) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (803026684399 / 5910140194335) | 1, 1 => 1 | 1, 3 => (19940748751 / 303084112530) | 2, 2 => 1 | 2, 3 => (1311756032 / 30308411253) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C13T18_ok : C13T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T18_den : ℕ := 11820280388670
theorem C13T18_den_ok :
    (∀ d ∈ C13T18.R, ∀ e ∈ C13T18.R, (C13T18.Lq d e).den ∣ C13T18_den ∧ (C13T18.Lq' d e).den ∣ C13T18_den) ∧
    (∀ d ∈ C13T18.C, ∀ e ∈ C13T18.C, (C13T18.Pq d e).den ∣ C13T18_den ∧ (C13T18.Pq' d e).den ∣ C13T18_den) := by
  constructor <;> decide +kernel
theorem C13T18_cload_3 : C13T18.cload 3 = ((8924952966103 / 11820280388670), (-993366669781 / 3940093462890)) := by decide +kernel
#print axioms C13T18_ok
#print axioms C13T18_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
