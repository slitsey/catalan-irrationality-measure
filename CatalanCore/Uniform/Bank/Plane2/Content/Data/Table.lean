module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab01
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab02
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab03
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab04
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab05
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab06
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab07
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab08
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab09
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab10
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab11
public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Tab12

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: the table (wave P210-L)

`p2cells`: the 276 cells of one period in increasing `θ`; `p2cells_ok`: every cell passes `cellOKb`. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def p2cells : List (QPiece × Cert) := tab01_0 ++ (tab01_1 ++ (tab02_0 ++ (tab02_1 ++ (tab03_0 ++ (tab03_1 ++ (tab04_0 ++ (tab04_1 ++ (tab05_0 ++ (tab05_1 ++ (tab06_0 ++ (tab06_1 ++ (tab07_0 ++ (tab07_1 ++ (tab08_0 ++ (tab08_1 ++ (tab09_0 ++ (tab09_1 ++ (tab10_0 ++ (tab10_1 ++ (tab11_0 ++ (tab11_1 ++ (tab12_0))))))))))))))))))))))

theorem p2cells_ok : p2cells.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  unfold p2cells
  simp only [List.all_append, tab01_0_ok, tab01_1_ok, tab02_0_ok, tab02_1_ok, tab03_0_ok, tab03_1_ok, tab04_0_ok, tab04_1_ok, tab05_0_ok, tab05_1_ok, tab06_0_ok, tab06_1_ok, tab07_0_ok, tab07_1_ok, tab08_0_ok, tab08_1_ok, tab09_0_ok, tab09_1_ok, tab10_0_ok, tab10_1_ok, tab11_0_ok, tab11_1_ok, tab12_0_ok, Bool.and_self]

end CatalanCore.Uniform.Bank.Plane2.Content.Data
