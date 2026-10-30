import CatalanCore.Uniform.Bank.Sevenths.Geom
import CatalanCore.Uniform.Content.BankShared.Reindex
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Rect CatalanCore.Uniform.Content.BankShared

theorem sevenths_member_commonMinor (Fr : Frame) (depth r : ℕ) (hr : r % 2 = 0)
    (S : Finset (F7.geometry r).C) :
    (F7.family Fr depth).Q ⟨r, S⟩ =
      commonMinorPoly Fr r (F7.borderSize r) (retainedFin (F7_hyb hr) S) :=
  alt_member_commonMinor_borderSize Fr depth (F7_hyb hr) S
end CatalanCore.Uniform.Bank.Sevenths
