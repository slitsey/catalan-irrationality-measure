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
def pcRawSeed3_024 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (55) 387), (qq (1) 7), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (66564) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_024Palette : List KBranch := pcRawSeed3_024.law.palette 0
abbrev pcSeed3_024 : OrbitSeed := pcRawSeed3_024.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_024_ok : seedOK (pcHead 1) pcSeed3_024Palette 3 pcSeedLimit pcSeed3_024=true := by decide +kernel
#print axioms pcSeed3_024_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_025 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (55) 882), (qq (1) 16), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (345744) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_025Palette : List KBranch := pcRawSeed3_025.law.palette 0
abbrev pcSeed3_025 : OrbitSeed := pcRawSeed3_025.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_025_ok : seedOK (pcHead 1) pcSeed3_025Palette 3 pcSeedLimit pcSeed3_025=true := by decide +kernel
#print axioms pcSeed3_025_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_026 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (1) 7), (qq (25) 171), (qq (11) 9), (qq (33) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4900) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_026Palette : List KBranch := pcRawSeed3_026.law.palette 0
abbrev pcSeed3_026 : OrbitSeed := pcRawSeed3_026.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_026_ok : seedOK (pcHead 1) pcSeed3_026Palette 3 pcSeedLimit pcSeed3_026=true := by decide +kernel
#print axioms pcSeed3_026_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_027 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 16), (qq (25) 396), (qq (11) 9), (qq (78) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (25600) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_027Palette : List KBranch := pcRawSeed3_027.law.palette 0
abbrev pcSeed3_027 : OrbitSeed := pcRawSeed3_027.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_027_ok : seedOK (pcHead 1) pcSeed3_027Palette 3 pcSeedLimit pcSeed3_027=true := by decide +kernel
#print axioms pcSeed3_027_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_028 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (25) 171), (qq (5) 33), (qq (31) 9), (qq (-43) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12996) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_028Palette : List KBranch := pcRawSeed3_028.law.palette 0
abbrev pcSeed3_028 : OrbitSeed := pcRawSeed3_028.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_028_ok : seedOK (pcHead 1) pcSeed3_028Palette 3 pcSeedLimit pcSeed3_028=true := by decide +kernel
#print axioms pcSeed3_028_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_029 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (25) 396), (qq (5) 78), (qq (31) 9), (qq (-98) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (69696) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_029Palette : List KBranch := pcRawSeed3_029.law.palette 0
abbrev pcSeed3_029 : OrbitSeed := pcRawSeed3_029.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_029_ok : seedOK (pcHead 1) pcSeed3_029Palette 3 pcSeedLimit pcSeed3_029=true := by decide +kernel
#print axioms pcSeed3_029_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_030 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (5) 33), (qq (11) 72), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (484) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_030Palette : List KBranch := pcRawSeed3_030.law.palette 0
abbrev pcSeed3_030 : OrbitSeed := pcRawSeed3_030.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_030_ok : seedOK (pcHead 1) pcSeed3_030Palette 3 pcSeedLimit pcSeed3_030=true := by decide +kernel
#print axioms pcSeed3_030_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_031 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 78), (qq (11) 171), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2704) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_031Palette : List KBranch := pcRawSeed3_031.law.palette 0
abbrev pcSeed3_031 : OrbitSeed := pcRawSeed3_031.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_031_ok : seedOK (pcHead 1) pcSeed3_031Palette 3 pcSeedLimit pcSeed3_031=true := by decide +kernel
#print axioms pcSeed3_031_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_032 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨12,by decide +kernel⟩]
  base := (⟨(qq (11) 72), (qq (10) 63), (qq (11) 9), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (57600) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_032Palette : List KBranch := pcRawSeed3_032.law.palette 0
abbrev pcSeed3_032 : OrbitSeed := pcRawSeed3_032.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_032_ok : seedOK (pcHead 1) pcSeed3_032Palette 3 pcSeedLimit pcSeed3_032=true := by decide +kernel
#print axioms pcSeed3_032_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_033 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 171), (qq (10) 153), (qq (11) 9), (qq (15) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324900) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_033Palette : List KBranch := pcRawSeed3_033.law.palette 0
abbrev pcSeed3_033 : OrbitSeed := pcRawSeed3_033.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_033_ok : seedOK (pcHead 1) pcSeed3_033Palette 3 pcSeedLimit pcSeed3_033=true := by decide +kernel
#print axioms pcSeed3_033_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_034 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (10) 63), (qq (55) 342), (qq (31) 9), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (441) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_034Palette : List KBranch := pcRawSeed3_034.law.palette 0
abbrev pcSeed3_034 : OrbitSeed := pcRawSeed3_034.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_034_ok : seedOK (pcHead 1) pcSeed3_034Palette 3 pcSeedLimit pcSeed3_034=true := by decide +kernel
#print axioms pcSeed3_034_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_035 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 153), (qq (55) 837), (qq (31) 9), (qq (-19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2601) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_035Palette : List KBranch := pcRawSeed3_035.law.palette 0
abbrev pcSeed3_035 : OrbitSeed := pcRawSeed3_035.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_035_ok : seedOK (pcHead 1) pcSeed3_035Palette 3 pcSeedLimit pcSeed3_035=true := by decide +kernel
#print axioms pcSeed3_035_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_036 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (55) 342), (qq (1) 6), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (51984) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_036Palette : List KBranch := pcRawSeed3_036.law.palette 0
abbrev pcSeed3_036 : OrbitSeed := pcRawSeed3_036.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_036_ok : seedOK (pcHead 1) pcSeed3_036Palette 3 pcSeedLimit pcSeed3_036=true := by decide +kernel
#print axioms pcSeed3_036_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_037 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (55) 837), (qq (1) 15), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (311364) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_037Palette : List KBranch := pcRawSeed3_037.law.palette 0
abbrev pcSeed3_037 : OrbitSeed := pcRawSeed3_037.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_037_ok : seedOK (pcHead 1) pcSeed3_037Palette 3 pcSeedLimit pcSeed3_037=true := by decide +kernel
#print axioms pcSeed3_037_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_038 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨11,by decide +kernel⟩]
  base := (⟨(qq (1) 6), (qq (50) 297), (qq (11) 9), (qq (28) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (400) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_038Palette : List KBranch := pcRawSeed3_038.law.palette 0
abbrev pcSeed3_038 : OrbitSeed := pcRawSeed3_038.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_038_ok : seedOK (pcHead 1) pcSeed3_038Palette 3 pcSeedLimit pcSeed3_038=true := by decide +kernel
#print axioms pcSeed3_038_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_039 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 15), (qq (50) 747), (qq (11) 9), (qq (73) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2500) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_039Palette : List KBranch := pcRawSeed3_039.law.palette 0
abbrev pcSeed3_039 : OrbitSeed := pcRawSeed3_039.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_039_ok : seedOK (pcHead 1) pcSeed3_039Palette 3 pcSeedLimit pcSeed3_039=true := by decide +kernel
#print axioms pcSeed3_039_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_040 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨10,by decide +kernel⟩]
  base := (⟨(qq (50) 297), (qq (11) 63), (qq (31) 9), (qq (-38) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9801) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_040Palette : List KBranch := pcRawSeed3_040.law.palette 0
abbrev pcSeed3_040 : OrbitSeed := pcRawSeed3_040.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_040_ok : seedOK (pcHead 1) pcSeed3_040Palette 3 pcSeedLimit pcSeed3_040=true := by decide +kernel
#print axioms pcSeed3_040_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_041 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (50) 747), (qq (11) 162), (qq (31) 9), (qq (-93) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (62001) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_041Palette : List KBranch := pcRawSeed3_041.law.palette 0
abbrev pcSeed3_041 : OrbitSeed := pcRawSeed3_041.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_041_ok : seedOK (pcHead 1) pcSeed3_041Palette 3 pcSeedLimit pcSeed3_041=true := by decide +kernel
#print axioms pcSeed3_041_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_042 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨10,by decide +kernel⟩]
  base := (⟨(qq (11) 63), (qq (5) 28), (qq (20) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (44100) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_042Palette : List KBranch := pcRawSeed3_042.law.palette 0
abbrev pcSeed3_042 : OrbitSeed := pcRawSeed3_042.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_042_ok : seedOK (pcHead 1) pcSeed3_042Palette 3 pcSeedLimit pcSeed3_042=true := by decide +kernel
#print axioms pcSeed3_042_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_043 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 162), (qq (5) 73), (qq (20) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (291600) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_043Palette : List KBranch := pcRawSeed3_043.law.palette 0
abbrev pcSeed3_043 : OrbitSeed := pcRawSeed3_043.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_043_ok : seedOK (pcHead 1) pcSeed3_043Palette 3 pcSeedLimit pcSeed3_043=true := by decide +kernel
#print axioms pcSeed3_043_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_044 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨10,by decide +kernel⟩]
  base := (⟨(qq (5) 28), (qq (5) 27), (qq (11) 9), (qq (5) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3136) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_044Palette : List KBranch := pcRawSeed3_044.law.palette 0
abbrev pcSeed3_044 : OrbitSeed := pcRawSeed3_044.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_044_ok : seedOK (pcHead 1) pcSeed3_044Palette 3 pcSeedLimit pcSeed3_044=true := by decide +kernel
#print axioms pcSeed3_044_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_045 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 73), (qq (5) 72), (qq (11) 9), (qq (14) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (21316) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_045Palette : List KBranch := pcRawSeed3_045.law.palette 0
abbrev pcSeed3_045 : OrbitSeed := pcRawSeed3_045.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_045_ok : seedOK (pcHead 1) pcSeed3_045Palette 3 pcSeedLimit pcSeed3_045=true := by decide +kernel
#print axioms pcSeed3_045_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_046 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (5) 27), (qq (25) 126), (qq (7) 3), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed3_046Palette : List KBranch := pcRawSeed3_046.law.palette 0
abbrev pcSeed3_046 : OrbitSeed := pcRawSeed3_046.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_046_ok : seedOK (pcHead 1) pcSeed3_046Palette 3 pcSeedLimit pcSeed3_046=true := by decide +kernel
#print axioms pcSeed3_046_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_047 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (25) 126), (qq (1) 5), (qq (41) 9), (qq (-61) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7056) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_047Palette : List KBranch := pcRawSeed3_047.law.palette 0
abbrev pcSeed3_047 : OrbitSeed := pcRawSeed3_047.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_047_ok : seedOK (pcHead 1) pcSeed3_047Palette 3 pcSeedLimit pcSeed3_047=true := by decide +kernel
#print axioms pcSeed3_047_ok


def pcRawSeeds3O001 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed3_024, pcRawSeed3_025, pcRawSeed3_026, pcRawSeed3_027, pcRawSeed3_028, pcRawSeed3_029, pcRawSeed3_030, pcRawSeed3_031, pcRawSeed3_032, pcRawSeed3_033, pcRawSeed3_034, pcRawSeed3_035, pcRawSeed3_036, pcRawSeed3_037, pcRawSeed3_038, pcRawSeed3_039, pcRawSeed3_040, pcRawSeed3_041, pcRawSeed3_042, pcRawSeed3_043, pcRawSeed3_044, pcRawSeed3_045, pcRawSeed3_046, pcRawSeed3_047]
theorem pcRawSeeds3O001_ok : ∀ S∈pcRawSeeds3O001,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3O001,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed3_024_ok
  · exact pcSeed3_025_ok
  · exact pcSeed3_026_ok
  · exact pcSeed3_027_ok
  · exact pcSeed3_028_ok
  · exact pcSeed3_029_ok
  · exact pcSeed3_030_ok
  · exact pcSeed3_031_ok
  · exact pcSeed3_032_ok
  · exact pcSeed3_033_ok
  · exact pcSeed3_034_ok
  · exact pcSeed3_035_ok
  · exact pcSeed3_036_ok
  · exact pcSeed3_037_ok
  · exact pcSeed3_038_ok
  · exact pcSeed3_039_ok
  · exact pcSeed3_040_ok
  · exact pcSeed3_041_ok
  · exact pcSeed3_042_ok
  · exact pcSeed3_043_ok
  · exact pcSeed3_044_ok
  · exact pcSeed3_045_ok
  · exact pcSeed3_046_ok
  · exact pcSeed3_047_ok
#print axioms pcRawSeeds3O001_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
