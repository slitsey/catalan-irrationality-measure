module

public import CatalanCore.Uniform.Bank.Plane1.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 1 content, closed form: the period table of the root class `j = 5` (wave H5a-closed; ledger P115)

`cells5`: the 82 cells of one period of `Γ` in increasing `θ` (10 `D1x`, the others prefix
windows), `κ = (2/3, 1/2)`.  Checked once for both supports (the cells, the chain of the expansion of 16
strips, its right end `1/12` and its mass depend on the class only): `exp5_*`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

def cells5 : List PCell := [
  ⟨qq (82) 7, qq (12) 1, 11, 0, qq (2) 1, qq (-1) 6, .pre 1 2 2⟩,
  ⟨qq (152) 13, qq (82) 7, 11, 0, qq (-35) 3, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (35) 3, qq (152) 13, 11, 0, qq (41) 3, qq (-7) 6, .pre 1 1 2⟩,
  ⟨qq (81) 7, qq (35) 3, 11, 0, qq (2) 1, qq (-1) 6, .pre 1 1 2⟩,
  ⟨qq (150) 13, qq (81) 7, 11, 0, qq (-23) 2, qq (1) 1, .pre 1 1 2⟩,
  ⟨qq (23) 2, qq (150) 13, 11, 0, qq (27) 2, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (78) 7, qq (23) 2, 11, 0, qq (2) 1, qq (-1) 6, .pre 1 1 1⟩,
  ⟨qq (144) 13, qq (78) 7, 11, 0, qq (-11) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (11) 1, qq (144) 13, 11, 0, qq (13) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (76) 7, qq (11) 1, 10, 0, qq (2) 1, qq (-1) 6, .pre 1 2 2⟩,
  ⟨qq (140) 13, qq (76) 7, 10, 0, qq (-32) 3, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (75) 7, qq (140) 13, 10, 0, qq (38) 3, qq (-7) 6, .pre 1 1 2⟩,
  ⟨qq (32) 3, qq (75) 7, 10, 0, qq (1) 6, qq (0) 1, .pre 1 1 2⟩,
  ⟨qq (138) 13, qq (32) 3, 10, 0, qq (-21) 2, qq (1) 1, .pre 1 1 2⟩,
  ⟨qq (21) 2, qq (138) 13, 10, 0, qq (25) 2, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (72) 7, qq (21) 2, 10, 0, qq (2) 1, qq (-1) 6, .pre 1 1 1⟩,
  ⟨qq (132) 13, qq (72) 7, 10, 0, qq (-10) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (10) 1, qq (132) 13, 10, 0, qq (12) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (128) 13, qq (10) 1, 9, 0, qq (-29) 3, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (126) 13, qq (128) 13, 9, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (19) 2, qq (126) 13, 9, 0, qq (23) 2, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (66) 7, qq (19) 2, 9, 0, qq (2) 1, qq (-1) 6, .pre 1 1 1⟩,
  ⟨qq (120) 13, qq (66) 7, 9, 0, qq (-9) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (64) 7, qq (120) 13, 9, 0, qq (11) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (9) 1, qq (64) 7, 9, 0, qq (1) 3, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (116) 13, qq (9) 1, 8, 0, qq (-26) 3, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (114) 13, qq (116) 13, 8, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (60) 7, qq (114) 13, 8, 0, qq (21) 2, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (17) 2, qq (60) 7, 8, 0, qq (1) 2, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (108) 13, qq (17) 2, 8, 0, qq (-8) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (58) 7, qq (108) 13, 8, 0, qq (10) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (8) 1, qq (58) 7, 8, 0, qq (1) 3, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (102) 13, qq (8) 1, 7, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (54) 7, qq (102) 13, 7, 0, qq (19) 2, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (15) 2, qq (54) 7, 7, 0, qq (1) 2, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (96) 13, qq (15) 2, 7, 0, qq (-7) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (7) 1, qq (96) 13, 7, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (90) 13, qq (7) 1, 6, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (48) 7, qq (90) 13, 6, 0, qq (17) 2, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (13) 2, qq (48) 7, 6, 0, qq (1) 2, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (84) 13, qq (13) 2, 6, 0, qq (-6) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (6) 1, qq (84) 13, 6, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (39) 7, qq (6) 1, 5, 0, qq (1) 2, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (72) 13, qq (39) 7, 5, 0, qq (-6) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (66) 13, qq (72) 13, 5, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (5) 1, qq (66) 13, 5, 0, qq (11) 2, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (33) 7, qq (5) 1, 4, 0, qq (1) 2, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (60) 13, qq (33) 7, 4, 0, qq (-5) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (54) 13, qq (60) 13, 4, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (4) 1, qq (54) 13, 4, 0, qq (9) 2, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (27) 7, qq (4) 1, 3, 0, qq (1) 2, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (48) 13, qq (27) 7, 3, 0, qq (-4) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (11) 3, qq (48) 13, 3, 0, qq (4) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (24) 7, qq (11) 3, 3, 0, qq (1) 3, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (44) 13, qq (24) 7, 3, 0, qq (-11) 3, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (42) 13, qq (44) 13, 3, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (3) 1, qq (42) 13, 3, 0, qq (7) 2, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (36) 13, qq (3) 1, 2, 0, qq (-3) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (8) 3, qq (36) 13, 2, 0, qq (3) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (18) 7, qq (8) 3, 2, 0, qq (1) 3, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (32) 13, qq (18) 7, 2, 0, qq (-8) 3, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (30) 13, qq (32) 13, 2, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (15) 7, qq (30) 13, 2, 0, qq (5) 2, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (2) 1, qq (15) 7, 2, 0, qq (0) 1, qq (1) 6, .pre 0 0 0⟩,
  ⟨qq (24) 13, qq (2) 1, 1, 0, qq (-2) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (12) 7, qq (24) 13, 1, 0, qq (2) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (5) 3, qq (12) 7, 1, 0, qq (0) 1, qq (1) 6, .pre 0 1 1⟩,
  ⟨qq (20) 13, qq (5) 3, 1, 0, qq (-5) 3, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (3) 2, qq (20) 13, 1, 0, qq (5) 3, qq (-1) 1, .pre 0 0 1⟩,
  ⟨qq (10) 7, qq (3) 2, 1, 0, qq (1) 6, qq (0) 1, .pre 0 0 1⟩,
  ⟨qq (18) 13, qq (10) 7, 1, 0, qq (-3) 2, qq (7) 6, .pre 0 0 1⟩,
  ⟨qq (9) 7, qq (18) 13, 1, 0, qq (3) 2, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (1) 1, qq (9) 7, 1, 0, qq (0) 1, qq (1) 6, .pre 0 0 0⟩,
  ⟨qq (12) 13, qq (1) 1, 0, 0, qq (-1) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (6) 7, qq (12) 13, 0, 0, qq (1) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (2) 3, qq (6) 7, 0, 0, qq (0) 1, qq (1) 6, .pre 0 1 1⟩,
  ⟨qq (8) 13, qq (2) 3, 0, 0, qq (-2) 3, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (4) 7, qq (8) 13, 0, 0, qq (2) 3, qq (-1) 1, .pre 0 0 1⟩,
  ⟨qq (1) 2, qq (4) 7, 0, 0, qq (0) 1, qq (1) 6, .pre 0 0 1⟩,
  ⟨qq (6) 13, qq (1) 2, 0, 0, qq (-1) 2, qq (7) 6, .pre 0 0 1⟩,
  ⟨qq (3) 7, qq (6) 13, 0, 0, qq (1) 2, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (0) 1, qq (3) 7, 0, 0, qq (0) 1, qq (1) 6, .pre 0 0 0⟩]

theorem cells5_ok : cells5.all (fun c => c.ok (qq 1 12) (qq 2 3) (qq 1 2)) = true := by
  -- kcost: 3 s measured, 82 cells
  decide +kernel

theorem exp5_chain : chainOK (qq 1 204) (expPs (qq 1 12) 16 cells5) = true := by
  -- kcost: 6 s measured, 16 strips of the cells (rational division and comparison each piece)
  decide +kernel

theorem exp5_end : tendQ (qq 1 204) (expPs (qq 1 12) 16 cells5) = qq 1 12 := by
  -- kcost: 1 s measured, list walk over the pieces
  decide +kernel

theorem exp5_mass : ((expPs (qq 1 12) 16 cells5).map (fun x => x.1.mass)).sum = qq (198117553821296275509323600438617520353387575482251997885875986380626842002690884679518138054979818166183368169117149646450035019696534897371372801673935770358225032418877085322613968578764663061682884613574932781339215202723708301779215639) 1172606479663450071270254485843545670366150961223909398019406903843892921034492197311375250794299565777640930969414395076922190543489000226311690523969650981228920222962060889097214768545271016952279645510044261069823431077146702526641152000 := by
  -- kcost: 12 s measured, piece masses of 16 strips summed exactly
  decide +kernel

end CatalanCore.Uniform.Bank.Plane1.Data
