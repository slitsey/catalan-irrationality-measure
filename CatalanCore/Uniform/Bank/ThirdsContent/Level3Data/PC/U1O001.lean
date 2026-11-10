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
def pcRawSeed1_024 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (3) 16), (qq (23) 120), (qq (13) 10), (qq (5) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2944) 15)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_024Palette : List KBranch := pcRawSeed1_024.law.palette 0
abbrev pcSeed1_024 : OrbitSeed := pcRawSeed1_024.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_024_ok : seedOK (pcHead 1) pcSeed1_024Palette 1 pcSeedLimit pcSeed1_024=true := by decide +kernel
#print axioms pcSeed1_024_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_025 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (3) 76), (qq (23) 580), (qq (13) 10), (qq (25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (66424) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_025Palette : List KBranch := pcRawSeed1_025.law.palette 0
abbrev pcSeed1_025 : OrbitSeed := pcRawSeed1_025.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_025_ok : seedOK (pcHead 1) pcSeed1_025Palette 1 pcSeedLimit pcSeed1_025=true := by decide +kernel
#print axioms pcSeed1_025_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_026 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (23) 120), (qq (1) 5), (qq (18) 5), (qq (-7) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4320) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_026Palette : List KBranch := pcRawSeed1_026.law.palette 0
abbrev pcSeed1_026 : OrbitSeed := pcRawSeed1_026.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_026_ok : seedOK (pcHead 1) pcSeed1_026Palette 1 pcSeedLimit pcSeed1_026=true := by decide +kernel
#print axioms pcSeed1_026_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_027 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (23) 580), (qq (1) 25), (qq (18) 5), (qq (-33) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (100920) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_027Palette : List KBranch := pcRawSeed1_027.law.palette 0
abbrev pcSeed1_027 : OrbitSeed := pcRawSeed1_027.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_027_ok : seedOK (pcHead 1) pcSeed1_027Palette 1 pcSeedLimit pcSeed1_027=true := by decide +kernel
#print axioms pcSeed1_027_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_028 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (1) 5), (qq (39) 190), (qq (13) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (345) 2)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_028Palette : List KBranch := pcRawSeed1_028.law.palette 0
abbrev pcSeed1_028 : OrbitSeed := pcRawSeed1_028.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_028_ok : seedOK (pcHead 1) pcSeed1_028Palette 1 pcSeedLimit pcSeed1_028=true := by decide +kernel
#print axioms pcSeed1_028_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_029 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (1) 25), (qq (39) 970), (qq (13) 5), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8625) 2)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_029Palette : List KBranch := pcRawSeed1_029.law.palette 0
abbrev pcSeed1_029 : OrbitSeed := pcRawSeed1_029.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_029_ok : seedOK (pcHead 1) pcSeed1_029Palette 1 pcSeedLimit pcSeed1_029=true := by decide +kernel
#print axioms pcSeed1_029_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_030 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (39) 190), (qq (69) 320), (qq (13) 10), (qq (13) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (83030) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_030Palette : List KBranch := pcRawSeed1_030.law.palette 0
abbrev pcSeed1_030 : OrbitSeed := pcRawSeed1_030.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_030_ok : seedOK (pcHead 1) pcSeed1_030Palette 1 pcSeedLimit pcSeed1_030=true := by decide +kernel
#print axioms pcSeed1_030_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_031 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (39) 970), (qq (69) 1700), (qq (13) 10), (qq (73) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2164070) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_031Palette : List KBranch := pcRawSeed1_031.law.palette 0
abbrev pcSeed1_031 : OrbitSeed := pcRawSeed1_031.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_031_ok : seedOK (pcHead 1) pcSeed1_031Palette 1 pcSeedLimit pcSeed1_031=true := by decide +kernel
#print axioms pcSeed1_031_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_032 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (69) 320), (qq (13) 60), (qq (18) 5), (qq (-19) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10240) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_032Palette : List KBranch := pcRawSeed1_032.law.palette 0
abbrev pcSeed1_032 : OrbitSeed := pcRawSeed1_032.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_032_ok : seedOK (pcHead 1) pcSeed1_032Palette 1 pcSeedLimit pcSeed1_032=true := by decide +kernel
#print axioms pcSeed1_032_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_033 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (69) 1700), (qq (13) 320), (qq (18) 5), (qq (-97) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (289000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_033Palette : List KBranch := pcRawSeed1_033.law.palette 0
abbrev pcSeed1_033 : OrbitSeed := pcRawSeed1_033.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_033_ok : seedOK (pcHead 1) pcSeed1_033Palette 1 pcSeedLimit pcSeed1_033=true := by decide +kernel
#print axioms pcSeed1_033_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_034 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (13) 60), (qq (9) 40), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24840) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_034Palette : List KBranch := pcRawSeed1_034.law.palette 0
abbrev pcSeed1_034 : OrbitSeed := pcRawSeed1_034.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_034_ok : seedOK (pcHead 1) pcSeed1_034Palette 1 pcSeedLimit pcSeed1_034=true := by decide +kernel
#print axioms pcSeed1_034_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_035 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (13) 320), (qq (9) 220), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (706560) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_035Palette : List KBranch := pcRawSeed1_035.law.palette 0
abbrev pcSeed1_035 : OrbitSeed := pcRawSeed1_035.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_035_ok : seedOK (pcHead 1) pcSeed1_035Palette 1 pcSeedLimit pcSeed1_035=true := by decide +kernel
#print axioms pcSeed1_035_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_036 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (9) 40), (qq (23) 100), (qq (49) 20), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3680) 27)⟩)
  N := 8
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8]
abbrev pcSeed1_036Palette : List KBranch := pcRawSeed1_036.law.palette 0
abbrev pcSeed1_036 : OrbitSeed := pcRawSeed1_036.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=9 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_036_ok : seedOK (pcHead 1) pcSeed1_036Palette 1 pcSeedLimit pcSeed1_036=true := by decide +kernel
#print axioms pcSeed1_036_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_037 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (23) 100), (qq (3) 13), (qq (19) 4), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3000) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_037Palette : List KBranch := pcRawSeed1_037.law.palette 0
abbrev pcSeed1_037 : OrbitSeed := pcRawSeed1_037.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_037_ok : seedOK (pcHead 1) pcSeed1_037Palette 1 pcSeedLimit pcSeed1_037=true := by decide +kernel
#print axioms pcSeed1_037_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_038 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (23) 560), (qq (3) 73), (qq (19) 4), (qq (-60) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (94080) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_038Palette : List KBranch := pcRawSeed1_038.law.palette 0
abbrev pcSeed1_038 : OrbitSeed := pcRawSeed1_038.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_038_ok : seedOK (pcHead 1) pcSeed1_038Palette 1 pcSeedLimit pcSeed1_038=true := by decide +kernel
#print axioms pcSeed1_038_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_039 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (3) 13), (qq (39) 160), (qq (15) 4), (qq (-20) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3887) 30)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_039Palette : List KBranch := pcRawSeed1_039.law.palette 0
abbrev pcSeed1_039 : OrbitSeed := pcRawSeed1_039.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_039_ok : seedOK (pcHead 1) pcSeed1_039Palette 1 pcSeedLimit pcSeed1_039=true := by decide +kernel
#print axioms pcSeed1_039_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_040 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (3) 73), (qq (39) 940), (qq (15) 4), (qq (-107) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (122567) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_040Palette : List KBranch := pcRawSeed1_040.law.palette 0
abbrev pcSeed1_040 : OrbitSeed := pcRawSeed1_040.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_040_ok : seedOK (pcHead 1) pcSeed1_040Palette 1 pcSeedLimit pcSeed1_040=true := by decide +kernel
#print axioms pcSeed1_040_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_041 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (39) 160), (qq (1) 4), (qq (49) 20), (qq (-4) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (58880) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_041Palette : List KBranch := pcRawSeed1_041.law.palette 0
abbrev pcSeed1_041 : OrbitSeed := pcRawSeed1_041.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_041_ok : seedOK (pcHead 1) pcSeed1_041Palette 1 pcSeedLimit pcSeed1_041=true := by decide +kernel
#print axioms pcSeed1_041_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_042 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (39) 940), (qq (1) 24), (qq (49) 20), (qq (-13) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2032280) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_042Palette : List KBranch := pcRawSeed1_042.law.palette 0
abbrev pcSeed1_042 : OrbitSeed := pcRawSeed1_042.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_042_ok : seedOK (pcHead 1) pcSeed1_042Palette 1 pcSeedLimit pcSeed1_042=true := by decide +kernel
#print axioms pcSeed1_042_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_043 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (1) 4), (qq (13) 50), (qq (29) 20), (qq (8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (552) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_043Palette : List KBranch := pcRawSeed1_043.law.palette 0
abbrev pcSeed1_043 : OrbitSeed := pcRawSeed1_043.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_043_ok : seedOK (pcHead 1) pcSeed1_043Palette 1 pcSeedLimit pcSeed1_043=true := by decide +kernel
#print axioms pcSeed1_043_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_044 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (1) 24), (qq (13) 310), (qq (29) 20), (qq (59) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19872) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_044Palette : List KBranch := pcRawSeed1_044.law.palette 0
abbrev pcSeed1_044 : OrbitSeed := pcRawSeed1_044.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_044_ok : seedOK (pcHead 1) pcSeed1_044Palette 1 pcSeedLimit pcSeed1_044=true := by decide +kernel
#print axioms pcSeed1_044_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_045 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (13) 50), (qq (69) 260), (qq (3) 20), (qq (23) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17250) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_045Palette : List KBranch := pcRawSeed1_045.law.palette 0
abbrev pcSeed1_045 : OrbitSeed := pcRawSeed1_045.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_045_ok : seedOK (pcHead 1) pcSeed1_045Palette 1 pcSeedLimit pcSeed1_045=true := by decide +kernel
#print axioms pcSeed1_045_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_046 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (13) 310), (qq (69) 1640), (qq (3) 20), (qq (152) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (663090) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_046Palette : List KBranch := pcRawSeed1_046.law.palette 0
abbrev pcSeed1_046 : OrbitSeed := pcRawSeed1_046.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_046_ok : seedOK (pcHead 1) pcSeed1_046Palette 1 pcSeedLimit pcSeed1_046=true := by decide +kernel
#print axioms pcSeed1_046_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_047 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 260), (qq (23) 80), (qq (49) 20), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6760) 69)⟩)
  N := 8
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8]
abbrev pcSeed1_047Palette : List KBranch := pcRawSeed1_047.law.palette 0
abbrev pcSeed1_047 : OrbitSeed := pcRawSeed1_047.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=9 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_047_ok : seedOK (pcHead 1) pcSeed1_047Palette 1 pcSeedLimit pcSeed1_047=true := by decide +kernel
#print axioms pcSeed1_047_ok


def pcRawSeeds1O001 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_024, pcRawSeed1_025, pcRawSeed1_026, pcRawSeed1_027, pcRawSeed1_028, pcRawSeed1_029, pcRawSeed1_030, pcRawSeed1_031, pcRawSeed1_032, pcRawSeed1_033, pcRawSeed1_034, pcRawSeed1_035, pcRawSeed1_036, pcRawSeed1_037, pcRawSeed1_038, pcRawSeed1_039, pcRawSeed1_040, pcRawSeed1_041, pcRawSeed1_042, pcRawSeed1_043, pcRawSeed1_044, pcRawSeed1_045, pcRawSeed1_046, pcRawSeed1_047]
theorem pcRawSeeds1O001_ok : ∀ S∈pcRawSeeds1O001,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O001,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_024_ok
  · exact pcSeed1_025_ok
  · exact pcSeed1_026_ok
  · exact pcSeed1_027_ok
  · exact pcSeed1_028_ok
  · exact pcSeed1_029_ok
  · exact pcSeed1_030_ok
  · exact pcSeed1_031_ok
  · exact pcSeed1_032_ok
  · exact pcSeed1_033_ok
  · exact pcSeed1_034_ok
  · exact pcSeed1_035_ok
  · exact pcSeed1_036_ok
  · exact pcSeed1_037_ok
  · exact pcSeed1_038_ok
  · exact pcSeed1_039_ok
  · exact pcSeed1_040_ok
  · exact pcSeed1_041_ok
  · exact pcSeed1_042_ok
  · exact pcSeed1_043_ok
  · exact pcSeed1_044_ok
  · exact pcSeed1_045_ok
  · exact pcSeed1_046_ok
  · exact pcSeed1_047_ok
#print axioms pcRawSeeds1O001_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
