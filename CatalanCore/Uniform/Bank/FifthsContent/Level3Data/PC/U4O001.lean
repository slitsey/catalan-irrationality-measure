module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_024 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (50) 801), (qq (1) 16), (qq (41) 9), (qq (-188) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (71289) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_024Palette : List KBranch := pcRawSeed4_024.law.palette 0
abbrev pcSeed4_024 : OrbitSeed := pcRawSeed4_024.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_024_ok : seedOK (pcHead 1) pcSeed4_024Palette 4 pcSeedLimit pcSeed4_024=true := by decide +kernel
#print axioms pcSeed4_024_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_025 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (1) 7), (qq (5) 34), (qq (32) 9), (qq (-48) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4900) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_025Palette : List KBranch := pcRawSeed4_025.law.palette 0
abbrev pcSeed4_025 : OrbitSeed := pcRawSeed4_025.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_025_ok : seedOK (pcHead 1) pcSeed4_025Palette 4 pcSeedLimit pcSeed4_025=true := by decide +kernel
#print axioms pcSeed4_025_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_026 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 16), (qq (5) 79), (qq (32) 9), (qq (-108) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (25600) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_026Palette : List KBranch := pcRawSeed4_026.law.palette 0
abbrev pcSeed4_026 : OrbitSeed := pcRawSeed4_026.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_026_ok : seedOK (pcHead 1) pcSeed4_026Palette 4 pcSeedLimit pcSeed4_026=true := by decide +kernel
#print axioms pcSeed4_026_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_027 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (5) 34), (qq (11) 72), (qq (23) 9), (qq (-14) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4624) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_027Palette : List KBranch := pcRawSeed4_027.law.palette 0
abbrev pcSeed4_027 : OrbitSeed := pcRawSeed4_027.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_027_ok : seedOK (pcHead 1) pcSeed4_027Palette 4 pcSeedLimit pcSeed4_027=true := by decide +kernel
#print axioms pcSeed4_027_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_028 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 79), (qq (11) 171), (qq (23) 9), (qq (-29) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24964) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_028Palette : List KBranch := pcRawSeed4_028.law.palette 0
abbrev pcSeed4_028 : OrbitSeed := pcRawSeed4_028.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_028_ok : seedOK (pcHead 1) pcSeed4_028Palette 4 pcSeedLimit pcSeed4_028=true := by decide +kernel
#print axioms pcSeed4_028_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_029 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (11) 72), (qq (55) 351), (qq (4) 3), (qq (26) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (57600) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_029Palette : List KBranch := pcRawSeed4_029.law.palette 0
abbrev pcSeed4_029 : OrbitSeed := pcRawSeed4_029.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_029_ok : seedOK (pcHead 1) pcSeed4_029Palette 4 pcSeedLimit pcSeed4_029=true := by decide +kernel
#print axioms pcSeed4_029_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_030 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 171), (qq (55) 846), (qq (4) 3), (qq (66) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324900) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_030Palette : List KBranch := pcRawSeed4_030.law.palette 0
abbrev pcSeed4_030 : OrbitSeed := pcRawSeed4_030.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_030_ok : seedOK (pcHead 1) pcSeed4_030Palette 4 pcSeedLimit pcSeed4_030=true := by decide +kernel
#print axioms pcSeed4_030_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_031 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (55) 351), (qq (10) 63), (qq (1) 9), (qq (13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (54756) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_031Palette : List KBranch := pcRawSeed4_031.law.palette 0
abbrev pcSeed4_031 : OrbitSeed := pcRawSeed4_031.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_031_ok : seedOK (pcHead 1) pcSeed4_031Palette 4 pcSeedLimit pcSeed4_031=true := by decide +kernel
#print axioms pcSeed4_031_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_032 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 846), (qq (10) 153), (qq (1) 9), (qq (32) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (318096) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_032Palette : List KBranch := pcRawSeed4_032.law.palette 0
abbrev pcSeed4_032 : OrbitSeed := pcRawSeed4_032.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_032_ok : seedOK (pcHead 1) pcSeed4_032Palette 4 pcSeedLimit pcSeed4_032=true := by decide +kernel
#print axioms pcSeed4_032_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_033 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (10) 63), (qq (25) 153), (qq (7) 3), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (441) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed4_033Palette : List KBranch := pcRawSeed4_033.law.palette 0
abbrev pcSeed4_033 : OrbitSeed := pcRawSeed4_033.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_033_ok : seedOK (pcHead 1) pcSeed4_033Palette 4 pcSeedLimit pcSeed4_033=true := by decide +kernel
#print axioms pcSeed4_033_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_034 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (25) 153), (qq (1) 6), (qq (41) 9), (qq (-73) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10404) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_034Palette : List KBranch := pcRawSeed4_034.law.palette 0
abbrev pcSeed4_034 : OrbitSeed := pcRawSeed4_034.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_034_ok : seedOK (pcHead 1) pcSeed4_034Palette 4 pcSeedLimit pcSeed4_034=true := by decide +kernel
#print axioms pcSeed4_034_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_035 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (25) 378), (qq (1) 15), (qq (41) 9), (qq (-178) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (63504) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_035Palette : List KBranch := pcRawSeed4_035.law.palette 0
abbrev pcSeed4_035 : OrbitSeed := pcRawSeed4_035.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_035_ok : seedOK (pcHead 1) pcSeed4_035Palette 4 pcSeedLimit pcSeed4_035=true := by decide +kernel
#print axioms pcSeed4_035_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_036 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (1) 6), (qq (5) 29), (qq (32) 9), (qq (-43) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (400) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_036Palette : List KBranch := pcRawSeed4_036.law.palette 0
abbrev pcSeed4_036 : OrbitSeed := pcRawSeed4_036.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_036_ok : seedOK (pcHead 1) pcSeed4_036Palette 4 pcSeedLimit pcSeed4_036=true := by decide +kernel
#print axioms pcSeed4_036_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_037 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 15), (qq (5) 74), (qq (32) 9), (qq (-103) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2500) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_037Palette : List KBranch := pcRawSeed4_037.law.palette 0
abbrev pcSeed4_037 : OrbitSeed := pcRawSeed4_037.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_037_ok : seedOK (pcHead 1) pcSeed4_037Palette 4 pcSeedLimit pcSeed4_037=true := by decide +kernel
#print axioms pcSeed4_037_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_038 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (5) 29), (qq (11) 63), (qq (23) 9), (qq (-14) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3364) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_038Palette : List KBranch := pcRawSeed4_038.law.palette 0
abbrev pcSeed4_038 : OrbitSeed := pcRawSeed4_038.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_038_ok : seedOK (pcHead 1) pcSeed4_038Palette 4 pcSeedLimit pcSeed4_038=true := by decide +kernel
#print axioms pcSeed4_038_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_039 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 74), (qq (11) 162), (qq (23) 9), (qq (-29) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (21904) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_039Palette : List KBranch := pcRawSeed4_039.law.palette 0
abbrev pcSeed4_039 : OrbitSeed := pcRawSeed4_039.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_039_ok : seedOK (pcHead 1) pcSeed4_039Palette 4 pcSeedLimit pcSeed4_039=true := by decide +kernel
#print axioms pcSeed4_039_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_040 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (11) 63), (qq (55) 306), (qq (4) 3), (qq (21) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (44100) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_040Palette : List KBranch := pcRawSeed4_040.law.palette 0
abbrev pcSeed4_040 : OrbitSeed := pcRawSeed4_040.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_040_ok : seedOK (pcHead 1) pcSeed4_040Palette 4 pcSeedLimit pcSeed4_040=true := by decide +kernel
#print axioms pcSeed4_040_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_041 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 162), (qq (55) 801), (qq (4) 3), (qq (61) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (291600) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_041Palette : List KBranch := pcRawSeed4_041.law.palette 0
abbrev pcSeed4_041 : OrbitSeed := pcRawSeed4_041.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_041_ok : seedOK (pcHead 1) pcSeed4_041Palette 4 pcSeedLimit pcSeed4_041=true := by decide +kernel
#print axioms pcSeed4_041_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_042 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (55) 306), (qq (5) 27), (qq (1) 9), (qq (11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (41616) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_042Palette : List KBranch := pcRawSeed4_042.law.palette 0
abbrev pcSeed4_042 : OrbitSeed := pcRawSeed4_042.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_042_ok : seedOK (pcHead 1) pcSeed4_042Palette 4 pcSeedLimit pcSeed4_042=true := by decide +kernel
#print axioms pcSeed4_042_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_043 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 801), (qq (5) 72), (qq (1) 9), (qq (30) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (285156) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_043Palette : List KBranch := pcRawSeed4_043.law.palette 0
abbrev pcSeed4_043 : OrbitSeed := pcRawSeed4_043.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_043_ok : seedOK (pcHead 1) pcSeed4_043Palette 4 pcSeedLimit pcSeed4_043=true := by decide +kernel
#print axioms pcSeed4_043_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_044 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (5) 27), (qq (50) 261), (qq (7) 3), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed4_044Palette : List KBranch := pcRawSeed4_044.law.palette 0
abbrev pcSeed4_044 : OrbitSeed := pcRawSeed4_044.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_044_ok : seedOK (pcHead 1) pcSeed4_044Palette 4 pcSeedLimit pcSeed4_044=true := by decide +kernel
#print axioms pcSeed4_044_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_045 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (50) 261), (qq (1) 5), (qq (41) 9), (qq (-63) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7569) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_045Palette : List KBranch := pcRawSeed4_045.law.palette 0
abbrev pcSeed4_045 : OrbitSeed := pcRawSeed4_045.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_045_ok : seedOK (pcHead 1) pcSeed4_045Palette 4 pcSeedLimit pcSeed4_045=true := by decide +kernel
#print axioms pcSeed4_045_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_046 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (50) 711), (qq (1) 14), (qq (41) 9), (qq (-168) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (56169) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_046Palette : List KBranch := pcRawSeed4_046.law.palette 0
abbrev pcSeed4_046 : OrbitSeed := pcRawSeed4_046.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_046_ok : seedOK (pcHead 1) pcSeed4_046Palette 4 pcSeedLimit pcSeed4_046=true := by decide +kernel
#print axioms pcSeed4_046_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_047 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (1) 5), (qq (11) 54), (qq (32) 9), (qq (-38) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2500) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_047Palette : List KBranch := pcRawSeed4_047.law.palette 0
abbrev pcSeed4_047 : OrbitSeed := pcRawSeed4_047.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_047_ok : seedOK (pcHead 1) pcSeed4_047Palette 4 pcSeedLimit pcSeed4_047=true := by decide +kernel
#print axioms pcSeed4_047_ok


def pcRawSeeds4O001 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed4_024, pcRawSeed4_025, pcRawSeed4_026, pcRawSeed4_027, pcRawSeed4_028, pcRawSeed4_029, pcRawSeed4_030, pcRawSeed4_031, pcRawSeed4_032, pcRawSeed4_033, pcRawSeed4_034, pcRawSeed4_035, pcRawSeed4_036, pcRawSeed4_037, pcRawSeed4_038, pcRawSeed4_039, pcRawSeed4_040, pcRawSeed4_041, pcRawSeed4_042, pcRawSeed4_043, pcRawSeed4_044, pcRawSeed4_045, pcRawSeed4_046, pcRawSeed4_047]
theorem pcRawSeeds4O001_ok : ∀ S∈pcRawSeeds4O001,
    seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds4O001,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed4_024_ok
  · exact pcSeed4_025_ok
  · exact pcSeed4_026_ok
  · exact pcSeed4_027_ok
  · exact pcSeed4_028_ok
  · exact pcSeed4_029_ok
  · exact pcSeed4_030_ok
  · exact pcSeed4_031_ok
  · exact pcSeed4_032_ok
  · exact pcSeed4_033_ok
  · exact pcSeed4_034_ok
  · exact pcSeed4_035_ok
  · exact pcSeed4_036_ok
  · exact pcSeed4_037_ok
  · exact pcSeed4_038_ok
  · exact pcSeed4_039_ok
  · exact pcSeed4_040_ok
  · exact pcSeed4_041_ok
  · exact pcSeed4_042_ok
  · exact pcSeed4_043_ok
  · exact pcSeed4_044_ok
  · exact pcSeed4_045_ok
  · exact pcSeed4_046_ok
  · exact pcSeed4_047_ok
#print axioms pcRawSeeds4O001_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
