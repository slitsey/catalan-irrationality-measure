module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_024 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (1) 7), (qq (55) 378), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4900) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_024Palette : List KBranch := pcRawSeed2_024.law.palette 0
abbrev pcSeed2_024 : OrbitSeed := pcRawSeed2_024.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_024_ok : seedOK (pcHead 1) pcSeed2_024Palette 2 pcSeedLimit pcSeed2_024=true := by decide +kernel
#print axioms pcSeed2_024_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_025 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 16), (qq (55) 873), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (25600) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_025Palette : List KBranch := pcRawSeed2_025.law.palette 0
abbrev pcSeed2_025 : OrbitSeed := pcRawSeed2_025.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_025_ok : seedOK (pcHead 1) pcSeed2_025Palette 2 pcSeedLimit pcSeed2_025=true := by decide +kernel
#print axioms pcSeed2_025_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_026 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (55) 378), (qq (50) 333), (qq (11) 9), (qq (32) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (63504) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_026Palette : List KBranch := pcRawSeed2_026.law.palette 0
abbrev pcSeed2_026 : OrbitSeed := pcRawSeed2_026.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_026_ok : seedOK (pcHead 1) pcSeed2_026Palette 2 pcSeedLimit pcSeed2_026=true := by decide +kernel
#print axioms pcSeed2_026_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_027 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (55) 873), (qq (50) 783), (qq (11) 9), (qq (77) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (338724) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_027Palette : List KBranch := pcRawSeed2_027.law.palette 0
abbrev pcSeed2_027 : OrbitSeed := pcRawSeed2_027.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_027_ok : seedOK (pcHead 1) pcSeed2_027Palette 2 pcSeedLimit pcSeed2_027=true := by decide +kernel
#print axioms pcSeed2_027_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_028 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (50) 333), (qq (11) 72), (qq (31) 9), (qq (-42) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12321) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_028Palette : List KBranch := pcRawSeed2_028.law.palette 0
abbrev pcSeed2_028 : OrbitSeed := pcRawSeed2_028.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_028_ok : seedOK (pcHead 1) pcSeed2_028Palette 2 pcSeedLimit pcSeed2_028=true := by decide +kernel
#print axioms pcSeed2_028_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_029 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (50) 783), (qq (11) 171), (qq (31) 9), (qq (-97) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (68121) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_029Palette : List KBranch := pcRawSeed2_029.law.palette 0
abbrev pcSeed2_029 : OrbitSeed := pcRawSeed2_029.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_029_ok : seedOK (pcHead 1) pcSeed2_029Palette 2 pcSeedLimit pcSeed2_029=true := by decide +kernel
#print axioms pcSeed2_029_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_030 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (11) 72), (qq (5) 32), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (57600) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_030Palette : List KBranch := pcRawSeed2_030.law.palette 0
abbrev pcSeed2_030 : OrbitSeed := pcRawSeed2_030.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_030_ok : seedOK (pcHead 1) pcSeed2_030Palette 2 pcSeedLimit pcSeed2_030=true := by decide +kernel
#print axioms pcSeed2_030_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_031 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 171), (qq (5) 77), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324900) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_031Palette : List KBranch := pcRawSeed2_031.law.palette 0
abbrev pcSeed2_031 : OrbitSeed := pcRawSeed2_031.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_031_ok : seedOK (pcHead 1) pcSeed2_031Palette 2 pcSeedLimit pcSeed2_031=true := by decide +kernel
#print axioms pcSeed2_031_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_032 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (5) 32), (qq (10) 63), (qq (11) 9), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4096) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_032Palette : List KBranch := pcRawSeed2_032.law.palette 0
abbrev pcSeed2_032 : OrbitSeed := pcRawSeed2_032.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_032_ok : seedOK (pcHead 1) pcSeed2_032Palette 2 pcSeedLimit pcSeed2_032=true := by decide +kernel
#print axioms pcSeed2_032_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_033 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 77), (qq (10) 153), (qq (11) 9), (qq (15) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23716) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_033Palette : List KBranch := pcRawSeed2_033.law.palette 0
abbrev pcSeed2_033 : OrbitSeed := pcRawSeed2_033.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_033_ok : seedOK (pcHead 1) pcSeed2_033Palette 2 pcSeedLimit pcSeed2_033=true := by decide +kernel
#print axioms pcSeed2_033_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_034 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (10) 63), (qq (55) 333), (qq (31) 9), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (441) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_034Palette : List KBranch := pcRawSeed2_034.law.palette 0
abbrev pcSeed2_034 : OrbitSeed := pcRawSeed2_034.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_034_ok : seedOK (pcHead 1) pcSeed2_034Palette 2 pcSeedLimit pcSeed2_034=true := by decide +kernel
#print axioms pcSeed2_034_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_035 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 153), (qq (55) 828), (qq (31) 9), (qq (-19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2601) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_035Palette : List KBranch := pcRawSeed2_035.law.palette 0
abbrev pcSeed2_035 : OrbitSeed := pcRawSeed2_035.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_035_ok : seedOK (pcHead 1) pcSeed2_035Palette 2 pcSeedLimit pcSeed2_035=true := by decide +kernel
#print axioms pcSeed2_035_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_036 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (55) 333), (qq (1) 6), (qq (20) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (49284) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_036Palette : List KBranch := pcRawSeed2_036.law.palette 0
abbrev pcSeed2_036 : OrbitSeed := pcRawSeed2_036.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_036_ok : seedOK (pcHead 1) pcSeed2_036Palette 2 pcSeedLimit pcSeed2_036=true := by decide +kernel
#print axioms pcSeed2_036_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_037 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (55) 828), (qq (1) 15), (qq (20) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (304704) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_037Palette : List KBranch := pcRawSeed2_037.law.palette 0
abbrev pcSeed2_037 : OrbitSeed := pcRawSeed2_037.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_037_ok : seedOK (pcHead 1) pcSeed2_037Palette 2 pcSeedLimit pcSeed2_037=true := by decide +kernel
#print axioms pcSeed2_037_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_038 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (1) 6), (qq (25) 144), (qq (11) 9), (qq (27) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (400) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_038Palette : List KBranch := pcRawSeed2_038.law.palette 0
abbrev pcSeed2_038 : OrbitSeed := pcRawSeed2_038.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_038_ok : seedOK (pcHead 1) pcSeed2_038Palette 2 pcSeedLimit pcSeed2_038=true := by decide +kernel
#print axioms pcSeed2_038_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_039 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 15), (qq (25) 369), (qq (11) 9), (qq (72) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2500) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_039Palette : List KBranch := pcRawSeed2_039.law.palette 0
abbrev pcSeed2_039 : OrbitSeed := pcRawSeed2_039.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_039_ok : seedOK (pcHead 1) pcSeed2_039Palette 2 pcSeedLimit pcSeed2_039=true := by decide +kernel
#print axioms pcSeed2_039_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_040 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨10,by decide +kernel⟩]
  base := (⟨(qq (25) 144), (qq (11) 63), (qq (31) 9), (qq (-37) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9216) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_040Palette : List KBranch := pcRawSeed2_040.law.palette 0
abbrev pcSeed2_040 : OrbitSeed := pcRawSeed2_040.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_040_ok : seedOK (pcHead 1) pcSeed2_040Palette 2 pcSeedLimit pcSeed2_040=true := by decide +kernel
#print axioms pcSeed2_040_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_041 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (25) 369), (qq (11) 162), (qq (31) 9), (qq (-92) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (60516) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_041Palette : List KBranch := pcRawSeed2_041.law.palette 0
abbrev pcSeed2_041 : OrbitSeed := pcRawSeed2_041.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_041_ok : seedOK (pcHead 1) pcSeed2_041Palette 2 pcSeedLimit pcSeed2_041=true := by decide +kernel
#print axioms pcSeed2_041_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_042 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨10,by decide +kernel⟩]
  base := (⟨(qq (11) 63), (qq (5) 27), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (44100) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_042Palette : List KBranch := pcRawSeed2_042.law.palette 0
abbrev pcSeed2_042 : OrbitSeed := pcRawSeed2_042.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_042_ok : seedOK (pcHead 1) pcSeed2_042Palette 2 pcSeedLimit pcSeed2_042=true := by decide +kernel
#print axioms pcSeed2_042_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_043 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 162), (qq (5) 72), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (291600) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_043Palette : List KBranch := pcRawSeed2_043.law.palette 0
abbrev pcSeed2_043 : OrbitSeed := pcRawSeed2_043.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_043_ok : seedOK (pcHead 1) pcSeed2_043Palette 2 pcSeedLimit pcSeed2_043=true := by decide +kernel
#print axioms pcSeed2_043_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_044 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (5) 27), (qq (55) 288), (qq (32) 9), (qq (-38) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_044Palette : List KBranch := pcRawSeed2_044.law.palette 0
abbrev pcSeed2_044 : OrbitSeed := pcRawSeed2_044.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_044_ok : seedOK (pcHead 1) pcSeed2_044Palette 2 pcSeedLimit pcSeed2_044=true := by decide +kernel
#print axioms pcSeed2_044_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_045 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 72), (qq (55) 783), (qq (32) 9), (qq (-98) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2304) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_045Palette : List KBranch := pcRawSeed2_045.law.palette 0
abbrev pcSeed2_045 : OrbitSeed := pcRawSeed2_045.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_045_ok : seedOK (pcHead 1) pcSeed2_045Palette 2 pcSeedLimit pcSeed2_045=true := by decide +kernel
#print axioms pcSeed2_045_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_046 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (55) 288), (qq (1) 5), (qq (7) 3), (qq (-6) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36864) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_046Palette : List KBranch := pcRawSeed2_046.law.palette 0
abbrev pcSeed2_046 : OrbitSeed := pcRawSeed2_046.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_046_ok : seedOK (pcHead 1) pcSeed2_046Palette 2 pcSeedLimit pcSeed2_046=true := by decide +kernel
#print axioms pcSeed2_046_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_047 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 783), (qq (1) 14), (qq (7) 3), (qq (-11) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (272484) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_047Palette : List KBranch := pcRawSeed2_047.law.palette 0
abbrev pcSeed2_047 : OrbitSeed := pcRawSeed2_047.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_047_ok : seedOK (pcHead 1) pcSeed2_047Palette 2 pcSeedLimit pcSeed2_047=true := by decide +kernel
#print axioms pcSeed2_047_ok


def pcRawSeeds2O001 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_024, pcRawSeed2_025, pcRawSeed2_026, pcRawSeed2_027, pcRawSeed2_028, pcRawSeed2_029, pcRawSeed2_030, pcRawSeed2_031, pcRawSeed2_032, pcRawSeed2_033, pcRawSeed2_034, pcRawSeed2_035, pcRawSeed2_036, pcRawSeed2_037, pcRawSeed2_038, pcRawSeed2_039, pcRawSeed2_040, pcRawSeed2_041, pcRawSeed2_042, pcRawSeed2_043, pcRawSeed2_044, pcRawSeed2_045, pcRawSeed2_046, pcRawSeed2_047]
theorem pcRawSeeds2O001_ok : ∀ S∈pcRawSeeds2O001,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000)=true := by
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
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
