import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false

/-! The unit classes of `ZMod 10` (lane B, B5c). -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Uniform.Content.Member Finset

theorem unitClasses_ten : unitClasses 10 = ({1, 3, 7, 9} : Finset (ZMod 10)) := by
  ext c
  rw [mem_unitClasses]
  have h : ∀ c : ZMod 10, IsUnit c ↔ Nat.Coprime c.val 10 := fun c => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact ZMod.isUnit_iff_coprime _ _
  rw [h]
  revert c
  decide

theorem totient_ten : (Nat.totient 10 : ℝ) = 4 := by
  have : Nat.totient 10 = 4 := by decide
  rw [this]; norm_num

#print axioms unitClasses_ten
#print axioms totient_ten
end CatalanCore.Uniform.Bank.FifthsContent
