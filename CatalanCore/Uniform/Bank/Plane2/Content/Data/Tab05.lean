module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: table cells, part 5 (wave P210-L; ledger P210)

Cells of one period of `θ` (bands `1 .. 6` with the gap pieces at the band boundaries), each with its `pieceOK` certificate
against `p2kb`; `cellOKb p2H p2kb 1 8 41 400` also checks the ambient range of the strips. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def tab05_0 : List (QPiece × Cert) := [
  (⟨(qq (94) 3157), (qq (11) 369), (qq (1) 1), (qq (74) 1), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (10695916) 2209)⟩),
  (⟨(qq (11) 369), (qq (2) 67), (qq (217) 41), (qq (-70) 1), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (53136) 11)⟩),
  (⟨(qq (2) 67), (qq (47) 1558), (qq (176) 41), (qq (-73) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (197516) 41)⟩),
  (⟨(qq (47) 1558), (qq (88) 2911), (qq (2) 1), (qq (79) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (10419904) 2209)⟩),
  (⟨(qq (88) 2911), (qq (1) 33), (qq (170) 41), (qq (-63) 2), (qq (1000000000000000) 1)⟩, ⟨18, [], [], (qq (206681) 44)⟩),
  (⟨(qq (1) 33), (qq (94) 3075), (qq (88) 41), (qq (69) 2), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (191664) 41)⟩),
  (⟨(qq (94) 3075), (qq (44) 1435), (qq (1) 1), (qq (72) 1), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (10147500) 2209)⟩),
  (⟨(qq (44) 1435), (qq (2) 65), (qq (217) 41), (qq (-68) 1), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (50225) 11)⟩),
  (⟨(qq (2) 65), (qq (47) 1517), (qq (176) 41), (qq (-71) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (185900) 41)⟩),
  (⟨(qq (47) 1517), (qq (88) 2829), (qq (2) 1), (qq (77) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (9878704) 2209)⟩),
  (⟨(qq (88) 2829), (qq (1) 32), (qq (170) 41), (qq (-61) 2), (qq (1000000000000000) 1)⟩, ⟨18, [], [], (qq (195201) 44)⟩),
  (⟨(qq (1) 32), (qq (94) 2993), (qq (88) 41), (qq (67) 2), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (180224) 41)⟩)]

def tab05_1 : List (QPiece × Cert) := [
  (⟨(qq (94) 2993), (qq (22) 697), (qq (1) 1), (qq (70) 1), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (9613516) 2209)⟩),
  (⟨(qq (22) 697), (qq (2) 63), (qq (217) 41), (qq (-66) 1), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (47396) 11)⟩),
  (⟨(qq (2) 63), (qq (47) 1476), (qq (176) 41), (qq (-69) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (174636) 41)⟩),
  (⟨(qq (47) 1476), (qq (88) 2747), (qq (2) 1), (qq (75) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (9351936) 2209)⟩),
  (⟨(qq (88) 2747), (qq (1) 31), (qq (170) 41), (qq (-59) 2), (qq (1000000000000000) 1)⟩, ⟨18, [], [], (qq (184049) 44)⟩),
  (⟨(qq (1) 31), (qq (94) 2911), (qq (88) 41), (qq (65) 2), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (169136) 41)⟩),
  (⟨(qq (94) 2911), (qq (4) 123), (qq (1) 1), (qq (68) 1), (qq (1000000000000000) 1)⟩, ⟨16, [], [], (qq (9093964) 2209)⟩),
  (⟨(qq (4) 123), (qq (47) 1435), (qq (217) 41), (qq (-64) 1), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (4059) 1)⟩),
  (⟨(qq (47) 1435), (qq (2) 61), (qq (3) 1), (qq (6) 1), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (8839600) 2209)⟩),
  (⟨(qq (2) 61), (qq (88) 2665), (qq (2) 1), (qq (73) 2), (qq (1000000000000000) 1)⟩, ⟨19, [], [], (qq (163724) 41)⟩),
  (⟨(qq (88) 2665), (qq (94) 2829), (qq (170) 41), (qq (-57) 2), (qq (1000000000000000) 1)⟩, ⟨18, [], [], (qq (173225) 44)⟩),
  (⟨(qq (94) 2829), (qq (1) 30), (qq (3) 1), (qq (6) 1), (qq (1000000000000000) 1)⟩, ⟨18, [], [], (qq (8588844) 2209)⟩)]

theorem tab05_0_ok : tab05_0.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

theorem tab05_1_ok : tab05_1.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
