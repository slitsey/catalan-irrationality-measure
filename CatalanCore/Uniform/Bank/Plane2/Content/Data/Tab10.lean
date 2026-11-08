module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: table cells, part 10 (wave P210-L; ledger P210)

Cells of one period of `θ` (bands `1 .. 6` with the gap pieces at the band boundaries), each with its `pieceOK` certificate
against `p2kb`; `cellOKb p2H p2kb 1 8 41 400` also checks the ambient range of the strips. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def tab10_0 : List (QPiece × Cert) := [
  (⟨(qq (2) 31), (qq (8) 123), (qq (2) 1), (qq (37) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (42284) 41)⟩),
  (⟨(qq (8) 123), (qq (94) 1435), (qq (170) 41), (qq (-29) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (4059) 4)⟩),
  (⟨(qq (94) 1435), (qq (1) 15), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (2209900) 2209)⟩),
  (⟨(qq (1) 15), (qq (11) 164), (qq (1) 1), (qq (33) 1), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (39600) 41)⟩),
  (⟨(qq (11) 164), (qq (47) 697), (qq (217) 41), (qq (-31) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (10496) 11)⟩),
  (⟨(qq (47) 697), (qq (2) 29), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (2085424) 2209)⟩),
  (⟨(qq (2) 29), (qq (88) 1271), (qq (2) 1), (qq (35) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (37004) 41)⟩),
  (⟨(qq (88) 1271), (qq (94) 1353), (qq (170) 41), (qq (-27) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (39401) 44)⟩),
  (⟨(qq (94) 1353), (qq (1) 14), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (1964556) 2209)⟩),
  (⟨(qq (1) 14), (qq (44) 615), (qq (1) 1), (qq (31) 1), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (34496) 41)⟩),
  (⟨(qq (44) 615), (qq (47) 656), (qq (217) 41), (qq (-29) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (9225) 11)⟩),
  (⟨(qq (47) 656), (qq (3000000) 41000003), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (1681000123) 9)⟩)]

def tab10_1 : List (QPiece × Cert) := [
  (⟨(qq (3000000) 41000003), (qq (3) 41), (qq (129) 41), (qq (1) 1), (qq (1000000000000000) 1)⟩, ⟨0, [], [], (qq (18491002706000099) 23062500000000)⟩),
  (⟨(qq (3) 41), (qq (3000000) 40999997), (qq (135) 41), (qq (-1) 1), (qq (1000000000000000) 1)⟩, ⟨0, [], [], (qq (7216) 9)⟩),
  (⟨(qq (3000000) 40999997), (qq (94) 1271), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (1680999877) 9)⟩),
  (⟨(qq (94) 1271), (qq (88) 1189), (qq (94) 41), (qq (25) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (1271) 1)⟩),
  (⟨(qq (88) 1189), (qq (2) 27), (qq (182) 41), (qq (-33) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (1189) 1)⟩),
  (⟨(qq (2) 27), (qq (47) 615), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (1107) 1)⟩),
  (⟨(qq (47) 615), (qq (22) 287), (qq (47) 41), (qq (27) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (1623600) 2209)⟩),
  (⟨(qq (22) 287), (qq (1) 13), (qq (223) 41), (qq (-29) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (8036) 11)⟩),
  (⟨(qq (1) 13), (qq (94) 1189), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (29744) 41)⟩),
  (⟨(qq (94) 1189), (qq (88) 1107), (qq (94) 41), (qq (23) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (1517164) 2209)⟩),
  (⟨(qq (88) 1107), (qq (2) 25), (qq (182) 41), (qq (-31) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (29889) 44)⟩),
  (⟨(qq (2) 25), (qq (47) 574), (qq (141) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (27500) 41)⟩)]

theorem tab10_0_ok : tab10_0.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

theorem tab10_1_ok : tab10_1.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
