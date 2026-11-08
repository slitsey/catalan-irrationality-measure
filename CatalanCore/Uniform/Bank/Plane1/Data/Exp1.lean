module

public import CatalanCore.Uniform.Bank.Plane1.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 1 content, closed form: the period table of the root class `j = 1` (wave H5a-closed; ledger P115)

`cells1`: the 82 cells of one period of `Γ` in increasing `θ` (10 `D1x`, the others prefix
windows), `κ = (1/3, 1/2)`.  Checked once for both supports (the cells, the chain of the expansion of 32
strips, its right end `1/12` and its mass depend on the class only): `exp1_*`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

def cells1 : List PCell := [
  ⟨qq (81) 7, qq (12) 1, 11, 0, qq (2) 1, qq (-1) 6, .pre 1 2 2⟩,
  ⟨qq (150) 13, qq (81) 7, 11, 0, qq (-23) 2, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (23) 2, qq (150) 13, 11, 0, qq (27) 2, qq (-7) 6, .pre 1 2 1⟩,
  ⟨qq (80) 7, qq (23) 2, 11, 0, qq (2) 1, qq (-1) 6, .pre 1 2 1⟩,
  ⟨qq (148) 13, qq (80) 7, 11, 0, qq (-34) 3, qq (1) 1, .pre 1 2 1⟩,
  ⟨qq (34) 3, qq (148) 13, 11, 0, qq (40) 3, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (78) 7, qq (34) 3, 11, 0, qq (2) 1, qq (-1) 6, .pre 1 1 1⟩,
  ⟨qq (144) 13, qq (78) 7, 11, 0, qq (-11) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (11) 1, qq (144) 13, 11, 0, qq (13) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (75) 7, qq (11) 1, 10, 0, qq (2) 1, qq (-1) 6, .pre 1 2 2⟩,
  ⟨qq (138) 13, qq (75) 7, 10, 0, qq (-21) 2, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (74) 7, qq (138) 13, 10, 0, qq (25) 2, qq (-7) 6, .pre 1 2 1⟩,
  ⟨qq (21) 2, qq (74) 7, 10, 0, qq (1) 6, qq (0) 1, .pre 1 2 1⟩,
  ⟨qq (136) 13, qq (21) 2, 10, 0, qq (-31) 3, qq (1) 1, .pre 1 2 1⟩,
  ⟨qq (31) 3, qq (136) 13, 10, 0, qq (37) 3, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (72) 7, qq (31) 3, 10, 0, qq (2) 1, qq (-1) 6, .pre 1 1 1⟩,
  ⟨qq (132) 13, qq (72) 7, 10, 0, qq (-10) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (10) 1, qq (132) 13, 10, 0, qq (12) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (69) 7, qq (10) 1, 9, 0, qq (2) 1, qq (-1) 6, .pre 1 2 2⟩,
  ⟨qq (126) 13, qq (69) 7, 9, 0, qq (-19) 2, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (124) 13, qq (126) 13, 9, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (66) 7, qq (124) 13, 9, 0, qq (34) 3, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (28) 3, qq (66) 7, 9, 0, qq (1) 3, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (120) 13, qq (28) 3, 9, 0, qq (-9) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (9) 1, qq (120) 13, 9, 0, qq (11) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (114) 13, qq (9) 1, 8, 0, qq (-17) 2, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (112) 13, qq (114) 13, 8, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (60) 7, qq (112) 13, 8, 0, qq (31) 3, qq (-7) 6, .pre 1 1 1⟩,
  ⟨qq (25) 3, qq (60) 7, 8, 0, qq (1) 3, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (108) 13, qq (25) 3, 8, 0, qq (-8) 1, qq (1) 1, .pre 1 1 1⟩,
  ⟨qq (57) 7, qq (108) 13, 8, 0, qq (10) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (8) 1, qq (57) 7, 8, 0, qq (1) 2, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (102) 13, qq (8) 1, 7, 0, qq (-15) 2, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (96) 13, qq (102) 13, 7, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (51) 7, qq (96) 13, 7, 0, qq (9) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (7) 1, qq (51) 7, 7, 0, qq (1) 2, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (90) 13, qq (7) 1, 6, 0, qq (-13) 2, qq (1) 1, .pre 1 2 2⟩,
  ⟨qq (84) 13, qq (90) 13, 6, 0, qq (1) 1, qq (-1) 12, .d1x⟩,
  ⟨qq (45) 7, qq (84) 13, 6, 0, qq (8) 1, qq (-7) 6, .pre 0 1 1⟩,
  ⟨qq (6) 1, qq (45) 7, 6, 0, qq (1) 2, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (72) 13, qq (6) 1, 5, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (11) 2, qq (72) 13, 5, 0, qq (6) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (36) 7, qq (11) 2, 5, 0, qq (1) 2, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (66) 13, qq (36) 7, 5, 0, qq (-11) 2, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (5) 1, qq (66) 13, 5, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (60) 13, qq (5) 1, 4, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (9) 2, qq (60) 13, 4, 0, qq (5) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (30) 7, qq (9) 2, 4, 0, qq (1) 2, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (54) 13, qq (30) 7, 4, 0, qq (-9) 2, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (4) 1, qq (54) 13, 4, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (26) 7, qq (4) 1, 3, 0, qq (1) 3, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (48) 13, qq (26) 7, 3, 0, qq (-4) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (7) 2, qq (48) 13, 3, 0, qq (4) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (24) 7, qq (7) 2, 3, 0, qq (1) 2, qq (0) 1, .pre 0 1 1⟩,
  ⟨qq (42) 13, qq (24) 7, 3, 0, qq (-7) 2, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (40) 13, qq (42) 13, 3, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (3) 1, qq (40) 13, 3, 0, qq (10) 3, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (20) 7, qq (3) 1, 2, 0, qq (1) 3, qq (0) 1, .pre 1 1 1⟩,
  ⟨qq (36) 13, qq (20) 7, 2, 0, qq (-3) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (18) 7, qq (36) 13, 2, 0, qq (3) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (5) 2, qq (18) 7, 2, 0, qq (0) 1, qq (1) 6, .pre 0 1 1⟩,
  ⟨qq (30) 13, qq (5) 2, 2, 0, qq (-5) 2, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (28) 13, qq (30) 13, 2, 0, qq (0) 1, qq (1) 12, .d1x⟩,
  ⟨qq (2) 1, qq (28) 13, 2, 0, qq (7) 3, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (24) 13, qq (2) 1, 1, 0, qq (-2) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (12) 7, qq (24) 13, 1, 0, qq (2) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (3) 2, qq (12) 7, 1, 0, qq (0) 1, qq (1) 6, .pre 0 1 1⟩,
  ⟨qq (18) 13, qq (3) 2, 1, 0, qq (-3) 2, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (4) 3, qq (18) 13, 1, 0, qq (3) 2, qq (-1) 1, .pre 0 1 0⟩,
  ⟨qq (9) 7, qq (4) 3, 1, 0, qq (1) 6, qq (0) 1, .pre 0 1 0⟩,
  ⟨qq (16) 13, qq (9) 7, 1, 0, qq (-4) 3, qq (7) 6, .pre 0 1 0⟩,
  ⟨qq (8) 7, qq (16) 13, 1, 0, qq (4) 3, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (1) 1, qq (8) 7, 1, 0, qq (0) 1, qq (1) 6, .pre 0 0 0⟩,
  ⟨qq (12) 13, qq (1) 1, 0, 0, qq (-1) 1, qq (7) 6, .pre 1 1 1⟩,
  ⟨qq (6) 7, qq (12) 13, 0, 0, qq (1) 1, qq (-1) 1, .pre 0 1 1⟩,
  ⟨qq (1) 2, qq (6) 7, 0, 0, qq (0) 1, qq (1) 6, .pre 0 1 1⟩,
  ⟨qq (6) 13, qq (1) 2, 0, 0, qq (-1) 2, qq (7) 6, .pre 0 1 1⟩,
  ⟨qq (3) 7, qq (6) 13, 0, 0, qq (1) 2, qq (-1) 1, .pre 0 1 0⟩,
  ⟨qq (1) 3, qq (3) 7, 0, 0, qq (0) 1, qq (1) 6, .pre 0 1 0⟩,
  ⟨qq (4) 13, qq (1) 3, 0, 0, qq (-1) 3, qq (7) 6, .pre 0 1 0⟩,
  ⟨qq (2) 7, qq (4) 13, 0, 0, qq (1) 3, qq (-1) 1, .pre 0 0 0⟩,
  ⟨qq (0) 1, qq (2) 7, 0, 0, qq (0) 1, qq (1) 6, .pre 0 0 0⟩]

theorem cells1_ok : cells1.all (fun c => c.ok (qq 1 12) (qq 1 3) (qq 1 2)) = true := by
  -- kcost: 3 s measured, 82 cells
  decide +kernel

theorem exp1_chain : chainOK (qq 1 396) (expPs (qq 1 12) 32 cells1) = true := by
  -- kcost: 6 s measured, 32 strips of the cells (rational division and comparison each piece)
  decide +kernel

theorem exp1_end : tendQ (qq 1 396) (expPs (qq 1 12) 32 cells1) = qq 1 12 := by
  -- kcost: 1 s measured, list walk over the pieces
  decide +kernel

theorem exp1_mass : ((expPs (qq 1 12) 32 cells1).map (fun x => x.1.mass)).sum = qq (27614241335238215471831356507661352357486156856881630352499347141405525269786639437474324494540398014393562343438108783570567954493369689152493522102312383791948791053364691600463534449353065917111155406157601990659931570381522472479427801414524989741784520097585602409684216364113196616382841396629002518921119035948806908519008871142759317691428700597219957491994458856113301963231620936655616688378940808950736438289511355604846813723505291563082459702464135071895231312732707) 158609668040374798895936120690279213730702331882063891481484283712978107734030048442040613002473953353720150152104129973404974051326011881640309644736617518773860602149492973506543090493654211234161816063437709158240551254811565565681177293779419926564017854280969919965381087375480952714814362175329762556716643917552134940295271531191646705212558464228616061303639660808545121768871205082620485759453630911865238107230790136974335245435928188482990454765708954450743024988160000 := by
  -- kcost: 12 s measured, piece masses of 32 strips summed exactly
  decide +kernel

end CatalanCore.Uniform.Bank.Plane1.Data
