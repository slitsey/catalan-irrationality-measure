module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_024 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (1) 5), (qq (69) 340), (qq (13) 10), (qq (14) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (345) 2)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_024Palette : List KBranch := pcRawSeed2_024.law.palette 0
abbrev pcSeed2_024 : OrbitSeed := pcRawSeed2_024.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_024_ok : seedOK (pcHead 1) pcSeed2_024Palette 2 pcSeedLimit pcSeed2_024=true := by decide +kernel
#print axioms pcSeed2_024_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_025 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (1) 25), (qq (69) 1720), (qq (13) 10), (qq (74) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8625) 2)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_025Palette : List KBranch := pcRawSeed2_025.law.palette 0
abbrev pcSeed2_025 : OrbitSeed := pcRawSeed2_025.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_025_ok : seedOK (pcHead 1) pcSeed2_025Palette 2 pcSeedLimit pcSeed2_025=true := by decide +kernel
#print axioms pcSeed2_025_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_026 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (69) 340), (qq (3) 14), (qq (18) 5), (qq (-20) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11560) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_026Palette : List KBranch := pcRawSeed2_026.law.palette 0
abbrev pcSeed2_026 : OrbitSeed := pcRawSeed2_026.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_026_ok : seedOK (pcHead 1) pcSeed2_026Palette 2 pcSeedLimit pcSeed2_026=true := by decide +kernel
#print axioms pcSeed2_026_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_027 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (69) 1720), (qq (3) 74), (qq (18) 5), (qq (-98) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (295840) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_027Palette : List KBranch := pcRawSeed2_027.law.palette 0
abbrev pcSeed2_027 : OrbitSeed := pcRawSeed2_027.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_027_ok : seedOK (pcHead 1) pcSeed2_027Palette 2 pcSeedLimit pcSeed2_027=true := by decide +kernel
#print axioms pcSeed2_027_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_028 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (3) 14), (qq (13) 60), (qq (13) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2254) 15)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_028Palette : List KBranch := pcRawSeed2_028.law.palette 0
abbrev pcSeed2_028 : OrbitSeed := pcRawSeed2_028.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_028_ok : seedOK (pcHead 1) pcSeed2_028Palette 2 pcSeedLimit pcSeed2_028=true := by decide +kernel
#print axioms pcSeed2_028_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_029 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (3) 74), (qq (13) 320), (qq (13) 5), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (62974) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_029Palette : List KBranch := pcRawSeed2_029.law.palette 0
abbrev pcSeed2_029 : OrbitSeed := pcRawSeed2_029.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_029_ok : seedOK (pcHead 1) pcSeed2_029Palette 2 pcSeedLimit pcSeed2_029=true := by decide +kernel
#print axioms pcSeed2_029_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_030 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (13) 60), (qq (9) 40), (qq (13) 10), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24840) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_030Palette : List KBranch := pcRawSeed2_030.law.palette 0
abbrev pcSeed2_030 : OrbitSeed := pcRawSeed2_030.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_030_ok : seedOK (pcHead 1) pcSeed2_030Palette 2 pcSeedLimit pcSeed2_030=true := by decide +kernel
#print axioms pcSeed2_030_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_031 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (13) 320), (qq (9) 220), (qq (13) 10), (qq (24) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (706560) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_031Palette : List KBranch := pcRawSeed2_031.law.palette 0
abbrev pcSeed2_031 : OrbitSeed := pcRawSeed2_031.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_031_ok : seedOK (pcHead 1) pcSeed2_031Palette 2 pcSeedLimit pcSeed2_031=true := by decide +kernel
#print axioms pcSeed2_031_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_032 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (9) 40), (qq (39) 170), (qq (29) 20), (qq (10) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3680) 27)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_032Palette : List KBranch := pcRawSeed2_032.law.palette 0
abbrev pcSeed2_032 : OrbitSeed := pcRawSeed2_032.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_032_ok : seedOK (pcHead 1) pcSeed2_032Palette 2 pcSeedLimit pcSeed2_032=true := by decide +kernel
#print axioms pcSeed2_032_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_033 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (9) 220), (qq (39) 950), (qq (29) 20), (qq (61) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (111320) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_033Palette : List KBranch := pcRawSeed2_033.law.palette 0
abbrev pcSeed2_033 : OrbitSeed := pcRawSeed2_033.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_033_ok : seedOK (pcHead 1) pcSeed2_033Palette 2 pcSeedLimit pcSeed2_033=true := by decide +kernel
#print axioms pcSeed2_033_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_034 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (39) 170), (qq (23) 100), (qq (3) 20), (qq (9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (66470) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_034Palette : List KBranch := pcRawSeed2_034.law.palette 0
abbrev pcSeed2_034 : OrbitSeed := pcRawSeed2_034.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_034_ok : seedOK (pcHead 1) pcSeed2_034Palette 2 pcSeedLimit pcSeed2_034=true := by decide +kernel
#print axioms pcSeed2_034_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_035 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (39) 950), (qq (23) 560), (qq (3) 20), (qq (52) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2075750) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_035Palette : List KBranch := pcRawSeed2_035.law.palette 0
abbrev pcSeed2_035 : OrbitSeed := pcRawSeed2_035.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_035_ok : seedOK (pcHead 1) pcSeed2_035Palette 2 pcSeedLimit pcSeed2_035=true := by decide +kernel
#print axioms pcSeed2_035_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_036 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 100), (qq (69) 280), (qq (49) 20), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3000) 23)⟩)
  N := 8
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8]
abbrev pcSeed2_036Palette : List KBranch := pcRawSeed2_036.law.palette 0
abbrev pcSeed2_036 : OrbitSeed := pcRawSeed2_036.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=9 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_036_ok : seedOK (pcHead 1) pcSeed2_036Palette 2 pcSeedLimit pcSeed2_036=true := by decide +kernel
#print axioms pcSeed2_036_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_037 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (69) 280), (qq (1) 4), (qq (19) 4), (qq (-31) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7840) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_037Palette : List KBranch := pcRawSeed2_037.law.palette 0
abbrev pcSeed2_037 : OrbitSeed := pcRawSeed2_037.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_037_ok : seedOK (pcHead 1) pcSeed2_037Palette 2 pcSeedLimit pcSeed2_037=true := by decide +kernel
#print axioms pcSeed2_037_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_038 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (69) 1660), (qq (1) 24), (qq (19) 4), (qq (-178) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (275560) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_038Palette : List KBranch := pcRawSeed2_038.law.palette 0
abbrev pcSeed2_038 : OrbitSeed := pcRawSeed2_038.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_038_ok : seedOK (pcHead 1) pcSeed2_038Palette 2 pcSeedLimit pcSeed2_038=true := by decide +kernel
#print axioms pcSeed2_038_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_039 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (1) 4), (qq (13) 50), (qq (15) 4), (qq (-19) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (552) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_039Palette : List KBranch := pcRawSeed2_039.law.palette 0
abbrev pcSeed2_039 : OrbitSeed := pcRawSeed2_039.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_039_ok : seedOK (pcHead 1) pcSeed2_039Palette 2 pcSeedLimit pcSeed2_039=true := by decide +kernel
#print axioms pcSeed2_039_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_040 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (1) 24), (qq (13) 310), (qq (15) 4), (qq (-106) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19872) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_040Palette : List KBranch := pcRawSeed2_040.law.palette 0
abbrev pcSeed2_040 : OrbitSeed := pcRawSeed2_040.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_040_ok : seedOK (pcHead 1) pcSeed2_040Palette 2 pcSeedLimit pcSeed2_040=true := by decide +kernel
#print axioms pcSeed2_040_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_041 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (13) 50), (qq (3) 11), (qq (49) 20), (qq (-4) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17250) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_041Palette : List KBranch := pcRawSeed2_041.law.palette 0
abbrev pcSeed2_041 : OrbitSeed := pcRawSeed2_041.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_041_ok : seedOK (pcHead 1) pcSeed2_041Palette 2 pcSeedLimit pcSeed2_041=true := by decide +kernel
#print axioms pcSeed2_041_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_042 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (13) 310), (qq (3) 71), (qq (49) 20), (qq (-13) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (663090) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_042Palette : List KBranch := pcRawSeed2_042.law.palette 0
abbrev pcSeed2_042 : OrbitSeed := pcRawSeed2_042.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_042_ok : seedOK (pcHead 1) pcSeed2_042Palette 2 pcSeedLimit pcSeed2_042=true := by decide +kernel
#print axioms pcSeed2_042_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_043 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (3) 11), (qq (39) 140), (qq (29) 20), (qq (7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (280) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_043Palette : List KBranch := pcRawSeed2_043.law.palette 0
abbrev pcSeed2_043 : OrbitSeed := pcRawSeed2_043.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_043_ok : seedOK (pcHead 1) pcSeed2_043Palette 2 pcSeedLimit pcSeed2_043=true := by decide +kernel
#print axioms pcSeed2_043_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_044 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (3) 71), (qq (39) 920), (qq (29) 20), (qq (58) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (115943) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_044Palette : List KBranch := pcRawSeed2_044.law.palette 0
abbrev pcSeed2_044 : OrbitSeed := pcRawSeed2_044.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_044_ok : seedOK (pcHead 1) pcSeed2_044Palette 2 pcSeedLimit pcSeed2_044=true := by decide +kernel
#print axioms pcSeed2_044_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_045 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (39) 140), (qq (23) 80), (qq (3) 20), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (160) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_045Palette : List KBranch := pcRawSeed2_045.law.palette 0
abbrev pcSeed2_045 : OrbitSeed := pcRawSeed2_045.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_045_ok : seedOK (pcHead 1) pcSeed2_045Palette 2 pcSeedLimit pcSeed2_045=true := by decide +kernel
#print axioms pcSeed2_045_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_046 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (39) 920), (qq (23) 540), (qq (3) 20), (qq (50) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1946720) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_046Palette : List KBranch := pcRawSeed2_046.law.palette 0
abbrev pcSeed2_046 : OrbitSeed := pcRawSeed2_046.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_046_ok : seedOK (pcHead 1) pcSeed2_046Palette 2 pcSeedLimit pcSeed2_046=true := by decide +kernel
#print axioms pcSeed2_046_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_047 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 540), (qq (3) 70), (qq (49) 20), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (87480) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_047Palette : List KBranch := pcRawSeed2_047.law.palette 0
abbrev pcSeed2_047 : OrbitSeed := pcRawSeed2_047.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_047_ok : seedOK (pcHead 1) pcSeed2_047Palette 2 pcSeedLimit pcSeed2_047=true := by decide +kernel
#print axioms pcSeed2_047_ok


def pcRawSeeds2O001 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_024, pcRawSeed2_025, pcRawSeed2_026, pcRawSeed2_027, pcRawSeed2_028, pcRawSeed2_029, pcRawSeed2_030, pcRawSeed2_031, pcRawSeed2_032, pcRawSeed2_033, pcRawSeed2_034, pcRawSeed2_035, pcRawSeed2_036, pcRawSeed2_037, pcRawSeed2_038, pcRawSeed2_039, pcRawSeed2_040, pcRawSeed2_041, pcRawSeed2_042, pcRawSeed2_043, pcRawSeed2_044, pcRawSeed2_045, pcRawSeed2_046, pcRawSeed2_047]
theorem pcRawSeeds2O001_ok : ∀ S∈pcRawSeeds2O001,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O001,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_024_ok
  · exact pcSeed2_025_ok
  · exact pcSeed2_026_ok
  · exact pcSeed2_027_ok
  · exact pcSeed2_028_ok
  · exact pcSeed2_029_ok
  · exact pcSeed2_030_ok
  · exact pcSeed2_031_ok
  · exact pcSeed2_032_ok
  · exact pcSeed2_033_ok
  · exact pcSeed2_034_ok
  · exact pcSeed2_035_ok
  · exact pcSeed2_036_ok
  · exact pcSeed2_037_ok
  · exact pcSeed2_038_ok
  · exact pcSeed2_039_ok
  · exact pcSeed2_040_ok
  · exact pcSeed2_041_ok
  · exact pcSeed2_042_ok
  · exact pcSeed2_043_ok
  · exact pcSeed2_044_ok
  · exact pcSeed2_045_ok
  · exact pcSeed2_046_ok
  · exact pcSeed2_047_ok
#print axioms pcRawSeeds2O001_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
