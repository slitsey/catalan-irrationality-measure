import CatalanCore.Uniform.Bank.Lambda.Geom
import CatalanCore.Uniform.Content.BankShared.Reindex
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Rect CatalanCore.Uniform.Content.BankShared

/-- The index stores retained common nodes, at the new slope, for either frame. -/
theorem lambda_member_commonMinor (Fr : Frame) (depth r : ℕ) (hr : r % 2 = 0)
    (S : Finset (FL.geometry r).C) :
    (FL.family Fr depth).Q ⟨r, S⟩ =
      commonMinorPoly Fr r (FL.borderSize r) (retainedFin (FL_hyb hr) S) :=
  alt_member_commonMinor_borderSize Fr depth (FL_hyb hr) S

end CatalanCore.Uniform.Bank.Lambda
