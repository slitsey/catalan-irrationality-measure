import CatalanCore.Uniform.Bank.Sevenths.Roots
import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Uniform.Content.Member Finset

theorem unitClasses_fourteen : unitClasses 14 = ({1, 3, 5, 9, 11, 13} : Finset (ZMod 14)) := by
  ext c
  rw [mem_unitClasses]
  have h : ∀ c : ZMod 14, IsUnit c ↔ Nat.Coprime c.val 14 := fun c => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact ZMod.isUnit_iff_coprime _ _
  rw [h]
  revert c
  decide

def seventhPrimeClass : Fin 6 → ℕ := ![1, 3, 5, 9, 11, 13]

def rootForClass (a : Fin 6) (c : ZMod 14) : ℕ :=
  (seventhNumerator a *
    (if c = 1 then 1 else if c = 3 then 5 else if c = 5 then 3
      else if c = 9 then 4 else if c = 11 then 2 else 6)) % 7

/-- The root index used by the class profile is the actual physical pole root. -/
theorem rootForClass_spec (a c : Fin 6) (p : ℕ) [Fact p.Prime]
    (hp8 : 8 ≤ p) (hclass : p % 14 = seventhPrimeClass c) :
    7 * seventhRho a p = rootForClass a (seventhPrimeClass c : ZMod 14) * p + seventhOffset a := by
  obtain ⟨j, hj0, hj6, he⟩ := seventhRho_root a p hp8
  have hj : j = rootForClass a (seventhPrimeClass c : ZMod 14) := by
    fin_cases a <;> fin_cases c <;> interval_cases j <;>
      norm_num [rootForClass, seventhPrimeClass, seventhNumerator, seventhOffset] at * <;> omega
  simpa only [hj] using he

#print axioms unitClasses_fourteen
#print axioms rootForClass_spec
end CatalanCore.Uniform.Bank.Sevenths
