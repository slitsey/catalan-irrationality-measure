module

public import CatalanCore.Uniform.Bank.Plane1.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 1 content, closed form: header bank of `S⁺` (wave H5a-closed)

`eHeadP`: shifts `[(3, 2, 1), (2, 1, 1)]`, master member `a = 1`, the prefix branches `kbrPre 0 j₀ [j₁, j₂]` that
the head certificates use.  The modules `HP<j>` check the head pieces against it and `BankP` assembles the
closed bank. -/

namespace CatalanCore.Uniform.Bank.Plane1.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

/-- The prefix branches `kbrPre n j₀ [j₁, j₂]` used on `S⁺`. -/
def kPresP : List (ℕ × ℕ × ℕ × ℕ) := [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 1, 0), (0, 0, 1, 1), (0, 0, 1, 2), (0, 0, 2, 0), (0, 0, 2, 1), (0, 0, 2, 2), (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 0, 2), (0, 1, 1, 0), (0, 1, 1, 1), (0, 1, 1, 2), (0, 1, 2, 0), (0, 1, 2, 1), (0, 1, 2, 2)]

/-- The header bank. -/
def eHeadP : KBankDataC := planeHeadC 2 1 kPresP

end CatalanCore.Uniform.Bank.Plane1.Data
