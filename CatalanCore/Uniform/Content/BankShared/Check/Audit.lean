import CatalanCore.Uniform.Content.BankShared.Check.Rank
import CatalanCore.Uniform.Content.BankShared.Check.Test
set_option Elab.async false

/-! # Axiom audit of the bank checker (lane C1L) -/

namespace CatalanCore.Uniform.Content.BankShared.Check

#print axioms evalN_cast
#print axioms evalR_err
#print axioms evalR_hom
#print axioms evalN_le_prof
#print axioms latDist_lip
#print axioms affineOn_sound
#print axioms Cond.holds_large
#print axioms Cond.holds_left
#print axioms Cond.holds_right
#print axioms k2_sound
#print axioms piece_sound
#print axioms chain_real
#print axioms mass_mkTemplate
#print axioms altContent_of_bounds
#print axioms hasScaledContent_of_check
#print axioms catValid_tableT
#print axioms catValid_LP
#print axioms catValid_win
#print axioms catValid_twoTerm
#print axioms hasScaledContent_lift
#print axioms rankPrice_eq
#print axioms catValid_rank
#print axioms catValid_bank
#print axioms Test.thirds_check
#print axioms Test.thirdsT1_real
#print axioms Test.thirdsT2_real

end CatalanCore.Uniform.Content.BankShared.Check
