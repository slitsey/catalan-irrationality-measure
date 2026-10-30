import CatalanCore.Uniform.Content.BankShared.AltCrude
import CatalanCore.Uniform.Bank.Fifths.Geom
set_option Elab.async false

/-! # Crude clearing on the fifths geometry (lane B, B5c)

The generic statement is `BankShared.altGeom_gle_Ecrude` (canonical); this file only instantiates it
at `F5 = altGeom (2/9)`. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.BankShared CatalanCore.Arith.Hybrid

/-- The fifths family: every member at an even scale is cleared by the crude exponent. -/
theorem F5_gle_Ecrude (Fr : Frame) (depth : ℕ) (i : (Fifths.F5.family Fr depth).ι)
    (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (Ecrude (cFr Fr) i.1 p) ((Fifths.F5.family Fr depth).Q i) :=
  altGeom_gle_Ecrude (2 / 9) Fifths.two_ninths_pos (by norm_num) Fr depth i hr p

#print axioms F5_gle_Ecrude
end CatalanCore.Uniform.Bank.FifthsContent
