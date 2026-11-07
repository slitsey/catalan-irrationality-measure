module
public import CatalanFrames.Thirds.Window
@[expose] public section
namespace CatalanFrames.Fifths
/-- Modulus30 removes all three finite bad primes without changing the averaged price. -/
def unitClasses : Finset (ZMod 30) := {1,7,11,13,17,19,23,29}
theorem unitClasses_unit : ∀ c ∈ unitClasses, IsUnit c := by decide +kernel
theorem unitClasses_card : unitClasses.card = 8 := by decide +kernel
theorem unitClasses_nonempty : unitClasses.Nonempty := by exact ⟨1,by decide⟩
theorem window_fifths : CatalanCore.HasWindowC (Thirds.ClsIn 30 unitClasses) (Thirds.PowBad 2) 1 := by
  apply Thirds.hasWindow_powBad 30 unitClasses unitClasses_unit unitClasses_nonempty (by norm_num)
  norm_num [unitClasses_card,show Nat.totient 30 = 8 by decide]
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.window_fifths
