module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: table cells, part 12 (wave P210-L; ledger P210)

Cells of one period of `θ` (bands `1 .. 6` with the gap pieces at the band boundaries), each with its `pieceOK` certificate
against `p2kb`; `cellOKb p2H p2kb 1 8 41 400` also checks the ambient range of the strips. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def tab12_0 : List (QPiece × Cert) := [
  (⟨(qq (2) 17), (qq (44) 369), (qq (47) 41), (qq (17) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (12716) 41)⟩),
  (⟨(qq (44) 369), (qq (94) 779), (qq (223) 41), (qq (-19) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (3321) 11)⟩),
  (⟨(qq (94) 779), (qq (1) 8), (qq (176) 41), (qq (-19) 2), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (651244) 2209)⟩),
  (⟨(qq (1) 8), (qq (88) 697), (qq (94) 41), (qq (13) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (11264) 41)⟩),
  (⟨(qq (88) 697), (qq (47) 369), (qq (182) 41), (qq (-21) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (11849) 44)⟩),
  (⟨(qq (47) 369), (qq (2) 15), (qq (88) 41), (qq (15) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (584496) 2209)⟩),
  (⟨(qq (2) 15), (qq (11) 82), (qq (47) 41), (qq (15) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (9900) 41)⟩),
  (⟨(qq (11) 82), (qq (94) 697), (qq (223) 41), (qq (-17) 1), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (2624) 11)⟩),
  (⟨(qq (94) 697), (qq (1) 7), (qq (176) 41), (qq (-17) 2), (qq (1000000000000000) 1)⟩, ⟨4, [], [], (qq (574) 1)⟩),
  (⟨(qq (1) 7), (qq (88) 615), (qq (94) 41), (qq (11) 2), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (615) 1)⟩),
  (⟨(qq (88) 615), (qq (47) 328), (qq (182) 41), (qq (-19) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (656) 1)⟩),
  (⟨(qq (47) 328), (qq (3000000) 20500003), (qq (88) 41), (qq (13) 2), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (840500123) 9)⟩)]

theorem tab12_0_ok : tab12_0.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
