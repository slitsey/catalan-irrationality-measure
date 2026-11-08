module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: table cells, part 9 (wave P210-L; ledger P210)

Cells of one period of `θ` (bands `1 .. 6` with the gap pieces at the band boundaries), each with its `pieceOK` certificate
against `p2kb`; `cellOKb p2H p2kb 1 8 41 400` also checks the ambient range of the strips. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def tab09_0 : List (QPiece × Cert) := [
  (⟨(qq (47) 902), (qq (88) 1681), (qq (2) 1), (qq (45) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (3492544) 2209)⟩),
  (⟨(qq (88) 1681), (qq (1) 19), (qq (170) 41), (qq (-37) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (68921) 44)⟩),
  (⟨(qq (1) 19), (qq (94) 1763), (qq (88) 41), (qq (39) 2), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (63536) 41)⟩),
  (⟨(qq (94) 1763), (qq (11) 205), (qq (1) 1), (qq (41) 1), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (3335596) 2209)⟩),
  (⟨(qq (11) 205), (qq (2) 37), (qq (217) 41), (qq (-39) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (16400) 11)⟩),
  (⟨(qq (2) 37), (qq (47) 861), (qq (176) 41), (qq (-41) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (60236) 41)⟩),
  (⟨(qq (47) 861), (qq (88) 1599), (qq (2) 1), (qq (43) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (3182256) 2209)⟩),
  (⟨(qq (88) 1599), (qq (1) 18), (qq (170) 41), (qq (-35) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (62361) 44)⟩),
  (⟨(qq (1) 18), (qq (94) 1681), (qq (88) 41), (qq (37) 2), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (57024) 41)⟩),
  (⟨(qq (94) 1681), (qq (44) 779), (qq (1) 1), (qq (39) 1), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (3032524) 2209)⟩),
  (⟨(qq (44) 779), (qq (2) 35), (qq (217) 41), (qq (-37) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (14801) 11)⟩),
  (⟨(qq (2) 35), (qq (47) 820), (qq (176) 41), (qq (-39) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (53900) 41)⟩)]

def tab09_1 : List (QPiece × Cert) := [
  (⟨(qq (47) 820), (qq (88) 1517), (qq (2) 1), (qq (41) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (2886400) 2209)⟩),
  (⟨(qq (88) 1517), (qq (94) 1599), (qq (170) 41), (qq (-33) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (56129) 44)⟩),
  (⟨(qq (94) 1599), (qq (1) 17), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (2743884) 2209)⟩),
  (⟨(qq (1) 17), (qq (22) 369), (qq (1) 1), (qq (37) 1), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (50864) 41)⟩),
  (⟨(qq (22) 369), (qq (47) 779), (qq (217) 41), (qq (-35) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (13284) 11)⟩),
  (⟨(qq (47) 779), (qq (2) 33), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (2604976) 2209)⟩),
  (⟨(qq (2) 33), (qq (88) 1435), (qq (2) 1), (qq (39) 2), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (47916) 41)⟩),
  (⟨(qq (88) 1435), (qq (94) 1517), (qq (170) 41), (qq (-31) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (50225) 44)⟩),
  (⟨(qq (94) 1517), (qq (1) 16), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (2469676) 2209)⟩),
  (⟨(qq (1) 16), (qq (44) 697), (qq (1) 1), (qq (35) 1), (qq (1000000000000000) 1)⟩, ⟨6, [], [], (qq (45056) 41)⟩),
  (⟨(qq (44) 697), (qq (47) 738), (qq (217) 41), (qq (-33) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (11849) 11)⟩),
  (⟨(qq (47) 738), (qq (2) 31), (qq (3) 1), (qq (3) 1), (qq (1000000000000000) 1)⟩, ⟨9, [], [], (qq (2337984) 2209)⟩)]

theorem tab09_0_ok : tab09_0.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

theorem tab09_1_ok : tab09_1.all (cellOKb p2H p2kb 1 8 41 400) = true := by
  -- kcost: 0.65 s measured, 12 cells
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
