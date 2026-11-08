module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Head1
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Head2
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Head3
public import CatalanCore.Uniform.Content.BankShared.KTerm.Split

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: the head (wave P210-L) -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def p2head : List (QPiece × Cert) := hd1_0 ++ (hd1_1 ++ (hd2_0 ++ (hd2_1 ++ (hd3_0))))

theorem p2head_ok : kpieceAll p2H 1 p2head = true := by
  unfold p2head
  simp only [kpieceAll_append, hd1_0_ok, hd1_1_ok, hd2_0_ok, hd2_1_ok, hd3_0_ok, Bool.and_self]

end CatalanCore.Uniform.Bank.Plane2.Content.Data
