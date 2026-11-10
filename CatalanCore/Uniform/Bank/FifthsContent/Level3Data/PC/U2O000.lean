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
def pcRawSeed2_000 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩, ⟨0,by decide +kernel⟩]
  base := (⟨(qq (1) 9), (qq (55) 468), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨true, 1, (qq (1) 156), (qq (3) 2)⟩], (qq (900) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_000Palette : List KBranch := pcRawSeed2_000.law.palette 0
abbrev pcSeed2_000 : OrbitSeed := pcRawSeed2_000.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_000_ok : seedOK (pcHead 1) pcSeed2_000Palette 2 pcSeedLimit pcSeed2_000=true := by decide +kernel
#print axioms pcSeed2_000_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_001 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 18), (qq (55) 963), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3600) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_001Palette : List KBranch := pcRawSeed2_001.law.palette 0
abbrev pcSeed2_001 : OrbitSeed := pcRawSeed2_001.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_001_ok : seedOK (pcHead 1) pcSeed2_001Palette 2 pcSeedLimit pcSeed2_001=true := by decide +kernel
#print axioms pcSeed2_001_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_002 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩]
  base := (⟨(qq (55) 468), (qq (50) 423), (qq (11) 9), (qq (42) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (97344) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_002Palette : List KBranch := pcRawSeed2_002.law.palette 0
abbrev pcSeed2_002 : OrbitSeed := pcRawSeed2_002.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_002_ok : seedOK (pcHead 1) pcSeed2_002Palette 2 pcSeedLimit pcSeed2_002=true := by decide +kernel
#print axioms pcSeed2_002_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_003 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (55) 963), (qq (50) 873), (qq (11) 9), (qq (87) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (412164) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_003Palette : List KBranch := pcRawSeed2_003.law.palette 0
abbrev pcSeed2_003 : OrbitSeed := pcRawSeed2_003.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_003_ok : seedOK (pcHead 1) pcSeed2_003Palette 2 pcSeedLimit pcSeed2_003=true := by decide +kernel
#print axioms pcSeed2_003_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_004 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (50) 423), (qq (5) 42), (qq (31) 9), (qq (-52) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19881) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_004Palette : List KBranch := pcRawSeed2_004.law.palette 0
abbrev pcSeed2_004 : OrbitSeed := pcRawSeed2_004.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_004_ok : seedOK (pcHead 1) pcSeed2_004Palette 2 pcSeedLimit pcSeed2_004=true := by decide +kernel
#print axioms pcSeed2_004_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_005 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (50) 873), (qq (5) 87), (qq (31) 9), (qq (-107) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (84681) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_005Palette : List KBranch := pcRawSeed2_005.law.palette 0
abbrev pcSeed2_005 : OrbitSeed := pcRawSeed2_005.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_005_ok : seedOK (pcHead 1) pcSeed2_005Palette 2 pcSeedLimit pcSeed2_005=true := by decide +kernel
#print axioms pcSeed2_005_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_006 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (5) 42), (qq (11) 90), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (784) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_006Palette : List KBranch := pcRawSeed2_006.law.palette 0
abbrev pcSeed2_006 : OrbitSeed := pcRawSeed2_006.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_006_ok : seedOK (pcHead 1) pcSeed2_006Palette 2 pcSeedLimit pcSeed2_006=true := by decide +kernel
#print axioms pcSeed2_006_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_007 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 87), (qq (11) 189), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3364) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_007Palette : List KBranch := pcRawSeed2_007.law.palette 0
abbrev pcSeed2_007 : OrbitSeed := pcRawSeed2_007.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_007_ok : seedOK (pcHead 1) pcSeed2_007Palette 2 pcSeedLimit pcSeed2_007=true := by decide +kernel
#print axioms pcSeed2_007_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_008 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (11) 90), (qq (10) 81), (qq (11) 9), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (90000) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_008Palette : List KBranch := pcRawSeed2_008.law.palette 0
abbrev pcSeed2_008 : OrbitSeed := pcRawSeed2_008.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_008_ok : seedOK (pcHead 1) pcSeed2_008Palette 2 pcSeedLimit pcSeed2_008=true := by decide +kernel
#print axioms pcSeed2_008_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_009 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 189), (qq (10) 171), (qq (11) 9), (qq (17) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (396900) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_009Palette : List KBranch := pcRawSeed2_009.law.palette 0
abbrev pcSeed2_009 : OrbitSeed := pcRawSeed2_009.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_009_ok : seedOK (pcHead 1) pcSeed2_009Palette 2 pcSeedLimit pcSeed2_009=true := by decide +kernel
#print axioms pcSeed2_009_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_010 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (10) 81), (qq (1) 8), (qq (31) 9), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (729) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_010Palette : List KBranch := pcRawSeed2_010.law.palette 0
abbrev pcSeed2_010 : OrbitSeed := pcRawSeed2_010.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_010_ok : seedOK (pcHead 1) pcSeed2_010Palette 2 pcSeedLimit pcSeed2_010=true := by decide +kernel
#print axioms pcSeed2_010_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_011 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 171), (qq (1) 17), (qq (31) 9), (qq (-21) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3249) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_011Palette : List KBranch := pcRawSeed2_011.law.palette 0
abbrev pcSeed2_011 : OrbitSeed := pcRawSeed2_011.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_011_ok : seedOK (pcHead 1) pcSeed2_011Palette 2 pcSeedLimit pcSeed2_011=true := by decide +kernel
#print axioms pcSeed2_011_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_012 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (1) 8), (qq (55) 423), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6400) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_012Palette : List KBranch := pcRawSeed2_012.law.palette 0
abbrev pcSeed2_012 : OrbitSeed := pcRawSeed2_012.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_012_ok : seedOK (pcHead 1) pcSeed2_012Palette 2 pcSeedLimit pcSeed2_012=true := by decide +kernel
#print axioms pcSeed2_012_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_013 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 17), (qq (55) 918), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (28900) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_013Palette : List KBranch := pcRawSeed2_013.law.palette 0
abbrev pcSeed2_013 : OrbitSeed := pcRawSeed2_013.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_013_ok : seedOK (pcHead 1) pcSeed2_013Palette 2 pcSeedLimit pcSeed2_013=true := by decide +kernel
#print axioms pcSeed2_013_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_014 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (55) 423), (qq (25) 189), (qq (11) 9), (qq (37) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (79524) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_014Palette : List KBranch := pcRawSeed2_014.law.palette 0
abbrev pcSeed2_014 : OrbitSeed := pcRawSeed2_014.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_014_ok : seedOK (pcHead 1) pcSeed2_014Palette 2 pcSeedLimit pcSeed2_014=true := by decide +kernel
#print axioms pcSeed2_014_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_015 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (55) 918), (qq (25) 414), (qq (11) 9), (qq (82) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (374544) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_015Palette : List KBranch := pcRawSeed2_015.law.palette 0
abbrev pcSeed2_015 : OrbitSeed := pcRawSeed2_015.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_015_ok : seedOK (pcHead 1) pcSeed2_015Palette 2 pcSeedLimit pcSeed2_015=true := by decide +kernel
#print axioms pcSeed2_015_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_016 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (25) 189), (qq (5) 37), (qq (31) 9), (qq (-47) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15876) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_016Palette : List KBranch := pcRawSeed2_016.law.palette 0
abbrev pcSeed2_016 : OrbitSeed := pcRawSeed2_016.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_016_ok : seedOK (pcHead 1) pcSeed2_016Palette 2 pcSeedLimit pcSeed2_016=true := by decide +kernel
#print axioms pcSeed2_016_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_017 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (25) 414), (qq (5) 82), (qq (31) 9), (qq (-102) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (76176) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_017Palette : List KBranch := pcRawSeed2_017.law.palette 0
abbrev pcSeed2_017 : OrbitSeed := pcRawSeed2_017.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_017_ok : seedOK (pcHead 1) pcSeed2_017Palette 2 pcSeedLimit pcSeed2_017=true := by decide +kernel
#print axioms pcSeed2_017_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_018 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (5) 37), (qq (11) 81), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5476) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_018Palette : List KBranch := pcRawSeed2_018.law.palette 0
abbrev pcSeed2_018 : OrbitSeed := pcRawSeed2_018.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_018_ok : seedOK (pcHead 1) pcSeed2_018Palette 2 pcSeedLimit pcSeed2_018=true := by decide +kernel
#print axioms pcSeed2_018_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_019 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 82), (qq (11) 180), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (26896) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_019Palette : List KBranch := pcRawSeed2_019.law.palette 0
abbrev pcSeed2_019 : OrbitSeed := pcRawSeed2_019.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_019_ok : seedOK (pcHead 1) pcSeed2_019Palette 2 pcSeedLimit pcSeed2_019=true := by decide +kernel
#print axioms pcSeed2_019_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_020 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (11) 81), (qq (5) 36), (qq (11) 9), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (72900) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_020Palette : List KBranch := pcRawSeed2_020.law.palette 0
abbrev pcSeed2_020 : OrbitSeed := pcRawSeed2_020.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_020_ok : seedOK (pcHead 1) pcSeed2_020Palette 2 pcSeedLimit pcSeed2_020=true := by decide +kernel
#print axioms pcSeed2_020_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_021 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 180), (qq (5) 81), (qq (11) 9), (qq (16) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (360000) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_021Palette : List KBranch := pcRawSeed2_021.law.palette 0
abbrev pcSeed2_021 : OrbitSeed := pcRawSeed2_021.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_021_ok : seedOK (pcHead 1) pcSeed2_021Palette 2 pcSeedLimit pcSeed2_021=true := by decide +kernel
#print axioms pcSeed2_021_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_022 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (5) 36), (qq (1) 7), (qq (31) 9), (qq (-9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (576) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_022Palette : List KBranch := pcRawSeed2_022.law.palette 0
abbrev pcSeed2_022 : OrbitSeed := pcRawSeed2_022.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_022_ok : seedOK (pcHead 1) pcSeed2_022Palette 2 pcSeedLimit pcSeed2_022=true := by decide +kernel
#print axioms pcSeed2_022_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_023 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 81), (qq (1) 16), (qq (31) 9), (qq (-20) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2916) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_023Palette : List KBranch := pcRawSeed2_023.law.palette 0
abbrev pcSeed2_023 : OrbitSeed := pcRawSeed2_023.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_023_ok : seedOK (pcHead 1) pcSeed2_023Palette 2 pcSeedLimit pcSeed2_023=true := by decide +kernel
#print axioms pcSeed2_023_ok


def pcRawSeeds2O000 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_000, pcRawSeed2_001, pcRawSeed2_002, pcRawSeed2_003, pcRawSeed2_004, pcRawSeed2_005, pcRawSeed2_006, pcRawSeed2_007, pcRawSeed2_008, pcRawSeed2_009, pcRawSeed2_010, pcRawSeed2_011, pcRawSeed2_012, pcRawSeed2_013, pcRawSeed2_014, pcRawSeed2_015, pcRawSeed2_016, pcRawSeed2_017, pcRawSeed2_018, pcRawSeed2_019, pcRawSeed2_020, pcRawSeed2_021, pcRawSeed2_022, pcRawSeed2_023]
theorem pcRawSeeds2O000_ok : ∀ S∈pcRawSeeds2O000,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O000,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_000_ok
  · exact pcSeed2_001_ok
  · exact pcSeed2_002_ok
  · exact pcSeed2_003_ok
  · exact pcSeed2_004_ok
  · exact pcSeed2_005_ok
  · exact pcSeed2_006_ok
  · exact pcSeed2_007_ok
  · exact pcSeed2_008_ok
  · exact pcSeed2_009_ok
  · exact pcSeed2_010_ok
  · exact pcSeed2_011_ok
  · exact pcSeed2_012_ok
  · exact pcSeed2_013_ok
  · exact pcSeed2_014_ok
  · exact pcSeed2_015_ok
  · exact pcSeed2_016_ok
  · exact pcSeed2_017_ok
  · exact pcSeed2_018_ok
  · exact pcSeed2_019_ok
  · exact pcSeed2_020_ok
  · exact pcSeed2_021_ok
  · exact pcSeed2_022_ok
  · exact pcSeed2_023_ok
#print axioms pcRawSeeds2O000_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
