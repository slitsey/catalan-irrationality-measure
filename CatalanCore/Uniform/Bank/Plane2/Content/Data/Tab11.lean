module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: table cells, part 11 (wave P210-L; ledger P210)

Cells of one period of `θ` (bands `1 .. 6` with the gap pieces at the band boundaries), each with its `pieceOK` certificate
against `p2kb`; `cellOKb p2H p2kb 1 8 41 400` also checks the ambient range of the strips. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def tab11_0 : List (QPiece × Cert) := [
  (⟨(qq (47) 574), (qq (44) 533), (qq (47) 41), (qq (25) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (1414336) 2209)⟩),
  (⟨(qq (44) 533), (qq (1) 12), (qq (223) 41), (qq (-27) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (6929) 11)⟩),
  (⟨(qq (1) 12), (qq (94) 1107), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (25344) 41)⟩),
  (⟨(qq (94) 1107), (qq (88) 1025), (qq (94) 41), (qq (21) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (1315116) 2209)⟩),
  (⟨(qq (88) 1025), (qq (2) 23), (qq (182) 41), (qq (-29) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (25625) 44)⟩),
  (⟨(qq (2) 23), (qq (47) 533), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (23276) 41)⟩),
  (⟨(qq (47) 533), (qq (11) 123), (qq (47) 41), (qq (23) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (1219504) 2209)⟩),
  (⟨(qq (11) 123), (qq (1) 11), (qq (223) 41), (qq (-25) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (5904) 11)⟩),
  (⟨(qq (1) 11), (qq (94) 1025), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (21296) 41)⟩),
  (⟨(qq (94) 1025), (qq (88) 943), (qq (94) 41), (qq (19) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (1127500) 2209)⟩),
  (⟨(qq (88) 943), (qq (2) 21), (qq (182) 41), (qq (-27) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (21689) 44)⟩),
  (⟨(qq (2) 21), (qq (47) 492), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (19404) 41)⟩)]

def tab11_1 : List (QPiece × Cert) := [
  (⟨(qq (47) 492), (qq (4) 41), (qq (47) 41), (qq (21) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (1039104) 2209)⟩),
  (⟨(qq (4) 41), (qq (94) 943), (qq (223) 41), (qq (-23) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (451) 1)⟩),
  (⟨(qq (94) 943), (qq (1) 10), (qq (176) 41), (qq (-23) 2), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (954316) 2209)⟩),
  (⟨(qq (1) 10), (qq (88) 861), (qq (94) 41), (qq (17) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (17600) 41)⟩),
  (⟨(qq (88) 861), (qq (47) 451), (qq (182) 41), (qq (-25) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (18081) 44)⟩),
  (⟨(qq (47) 451), (qq (2) 19), (qq (88) 41), (qq (19) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (873136) 2209)⟩),
  (⟨(qq (2) 19), (qq (22) 205), (qq (47) 41), (qq (19) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (15884) 41)⟩),
  (⟨(qq (22) 205), (qq (94) 861), (qq (223) 41), (qq (-21) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (4100) 11)⟩),
  (⟨(qq (94) 861), (qq (1) 9), (qq (176) 41), (qq (-21) 2), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (795564) 2209)⟩),
  (⟨(qq (1) 9), (qq (88) 779), (qq (94) 41), (qq (15) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (14256) 41)⟩),
  (⟨(qq (88) 779), (qq (47) 410), (qq (182) 41), (qq (-23) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (14801) 44)⟩),
  (⟨(qq (47) 410), (qq (2) 17), (qq (88) 41), (qq (17) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (721600) 2209)⟩)]

theorem tab11_0_ok : tab11_0.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

theorem tab11_1_ok : tab11_1.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
