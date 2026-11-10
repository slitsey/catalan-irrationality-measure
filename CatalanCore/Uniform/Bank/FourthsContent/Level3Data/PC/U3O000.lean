module

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_000 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩, ⟨0,by decide +kernel⟩]
  base := (⟨(qq (1) 10), (qq (24) 235), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨true, 1, (qq (1) 470), (qq (3) 2)⟩], (qq (880) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_000Palette : List KBranch := pcRawSeed3_000.law.palette 0
abbrev pcSeed3_000 : OrbitSeed := pcRawSeed3_000.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_000_ok : seedOK (pcHead 1) pcSeed3_000Palette 3 pcSeedLimit pcSeed3_000=true := by decide +kernel
#print axioms pcSeed3_000_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_001 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 20), (qq (24) 475), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3520) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_001Palette : List KBranch := pcRawSeed3_001.law.palette 0
abbrev pcSeed3_001 : OrbitSeed := pcRawSeed3_001.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_001_ok : seedOK (pcHead 1) pcSeed3_001Palette 3 pcSeedLimit pcSeed3_001=true := by decide +kernel
#print axioms pcSeed3_001_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_002 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩]
  base := (⟨(qq (24) 235), (qq (22) 215), (qq (6) 5), (qq (39) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (121495) 144)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_002Palette : List KBranch := pcRawSeed3_002.law.palette 0
abbrev pcSeed3_002 : OrbitSeed := pcRawSeed3_002.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_002_ok : seedOK (pcHead 1) pcSeed3_002Palette 3 pcSeedLimit pcSeed3_002=true := by decide +kernel
#print axioms pcSeed3_002_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_003 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (24) 475), (qq (22) 435), (qq (6) 5), (qq (79) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (496375) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_003Palette : List KBranch := pcRawSeed3_003.law.palette 0
abbrev pcSeed3_003 : OrbitSeed := pcRawSeed3_003.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_003_ok : seedOK (pcHead 1) pcSeed3_003Palette 3 pcSeedLimit pcSeed3_003=true := by decide +kernel
#print axioms pcSeed3_003_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_004 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (22) 215), (qq (4) 39), (qq (17) 5), (qq (-47) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9245) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_004Palette : List KBranch := pcRawSeed3_004.law.palette 0
abbrev pcSeed3_004 : OrbitSeed := pcRawSeed3_004.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_004_ok : seedOK (pcHead 1) pcSeed3_004Palette 3 pcSeedLimit pcSeed3_004=true := by decide +kernel
#print axioms pcSeed3_004_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_005 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (22) 435), (qq (4) 79), (qq (17) 5), (qq (-95) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (37845) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_005Palette : List KBranch := pcRawSeed3_005.law.palette 0
abbrev pcSeed3_005 : OrbitSeed := pcRawSeed3_005.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_005_ok : seedOK (pcHead 1) pcSeed3_005Palette 3 pcSeedLimit pcSeed3_005=true := by decide +kernel
#print axioms pcSeed3_005_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_006 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (4) 39), (qq (6) 55), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16731) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_006Palette : List KBranch := pcRawSeed3_006.law.palette 0
abbrev pcSeed3_006 : OrbitSeed := pcRawSeed3_006.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_006_ok : seedOK (pcHead 1) pcSeed3_006Palette 3 pcSeedLimit pcSeed3_006=true := by decide +kernel
#print axioms pcSeed3_006_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_007 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (4) 79), (qq (6) 115), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (68651) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_007Palette : List KBranch := pcRawSeed3_007.law.palette 0
abbrev pcSeed3_007 : OrbitSeed := pcRawSeed3_007.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_007_ok : seedOK (pcHead 1) pcSeed3_007Palette 3 pcSeedLimit pcSeed3_007=true := by decide +kernel
#print axioms pcSeed3_007_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_008 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (6) 55), (qq (11) 100), (qq (6) 5), (qq (9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6655) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_008Palette : List KBranch := pcRawSeed3_008.law.palette 0
abbrev pcSeed3_008 : OrbitSeed := pcRawSeed3_008.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_008_ok : seedOK (pcHead 1) pcSeed3_008Palette 3 pcSeedLimit pcSeed3_008=true := by decide +kernel
#print axioms pcSeed3_008_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_009 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (6) 115), (qq (11) 210), (qq (6) 5), (qq (19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (29095) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_009Palette : List KBranch := pcRawSeed3_009.law.palette 0
abbrev pcSeed3_009 : OrbitSeed := pcRawSeed3_009.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_009_ok : seedOK (pcHead 1) pcSeed3_009Palette 3 pcSeedLimit pcSeed3_009=true := by decide +kernel
#print axioms pcSeed3_009_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_010 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (11) 100), (qq (1) 9), (qq (17) 5), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8000) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_010Palette : List KBranch := pcRawSeed3_010.law.palette 0
abbrev pcSeed3_010 : OrbitSeed := pcRawSeed3_010.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_010_ok : seedOK (pcHead 1) pcSeed3_010Palette 3 pcSeedLimit pcSeed3_010=true := by decide +kernel
#print axioms pcSeed3_010_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_011 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 210), (qq (1) 19), (qq (17) 5), (qq (-23) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (35280) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_011Palette : List KBranch := pcRawSeed3_011.law.palette 0
abbrev pcSeed3_011 : OrbitSeed := pcRawSeed3_011.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_011_ok : seedOK (pcHead 1) pcSeed3_011Palette 3 pcSeedLimit pcSeed3_011=true := by decide +kernel
#print axioms pcSeed3_011_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_012 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (1) 9), (qq (24) 215), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3564) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_012Palette : List KBranch := pcRawSeed3_012.law.palette 0
abbrev pcSeed3_012 : OrbitSeed := pcRawSeed3_012.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_012_ok : seedOK (pcHead 1) pcSeed3_012Palette 3 pcSeedLimit pcSeed3_012=true := by decide +kernel
#print axioms pcSeed3_012_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_013 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 19), (qq (24) 455), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15884) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_013Palette : List KBranch := pcRawSeed3_013.law.palette 0
abbrev pcSeed3_013 : OrbitSeed := pcRawSeed3_013.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_013_ok : seedOK (pcHead 1) pcSeed3_013Palette 3 pcSeedLimit pcSeed3_013=true := by decide +kernel
#print axioms pcSeed3_013_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_014 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (24) 215), (qq (22) 195), (qq (6) 5), (qq (35) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (101695) 144)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_014Palette : List KBranch := pcRawSeed3_014.law.palette 0
abbrev pcSeed3_014 : OrbitSeed := pcRawSeed3_014.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_014_ok : seedOK (pcHead 1) pcSeed3_014Palette 3 pcSeedLimit pcSeed3_014=true := by decide +kernel
#print axioms pcSeed3_014_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_015 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (24) 455), (qq (22) 415), (qq (6) 5), (qq (75) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (455455) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_015Palette : List KBranch := pcRawSeed3_015.law.palette 0
abbrev pcSeed3_015 : OrbitSeed := pcRawSeed3_015.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_015_ok : seedOK (pcHead 1) pcSeed3_015Palette 3 pcSeedLimit pcSeed3_015=true := by decide +kernel
#print axioms pcSeed3_015_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_016 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (22) 195), (qq (4) 35), (qq (17) 5), (qq (-43) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7605) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_016Palette : List KBranch := pcRawSeed3_016.law.palette 0
abbrev pcSeed3_016 : OrbitSeed := pcRawSeed3_016.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_016_ok : seedOK (pcHead 1) pcSeed3_016Palette 3 pcSeedLimit pcSeed3_016=true := by decide +kernel
#print axioms pcSeed3_016_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_017 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (22) 415), (qq (4) 75), (qq (17) 5), (qq (-91) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (34445) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_017Palette : List KBranch := pcRawSeed3_017.law.palette 0
abbrev pcSeed3_017 : OrbitSeed := pcRawSeed3_017.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_017_ok : seedOK (pcHead 1) pcSeed3_017Palette 3 pcSeedLimit pcSeed3_017=true := by decide +kernel
#print axioms pcSeed3_017_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_018 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (4) 35), (qq (3) 25), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2695) 4)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_018Palette : List KBranch := pcRawSeed3_018.law.palette 0
abbrev pcSeed3_018 : OrbitSeed := pcRawSeed3_018.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_018_ok : seedOK (pcHead 1) pcSeed3_018Palette 3 pcSeedLimit pcSeed3_018=true := by decide +kernel
#print axioms pcSeed3_018_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_019 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (4) 75), (qq (3) 55), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12375) 4)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_019Palette : List KBranch := pcRawSeed3_019.law.palette 0
abbrev pcSeed3_019 : OrbitSeed := pcRawSeed3_019.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_019_ok : seedOK (pcHead 1) pcSeed3_019Palette 3 pcSeedLimit pcSeed3_019=true := by decide +kernel
#print axioms pcSeed3_019_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_020 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (3) 25), (qq (11) 90), (qq (6) 5), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5500) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_020Palette : List KBranch := pcRawSeed3_020.law.palette 0
abbrev pcSeed3_020 : OrbitSeed := pcRawSeed3_020.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_020_ok : seedOK (pcHead 1) pcSeed3_020Palette 3 pcSeedLimit pcSeed3_020=true := by decide +kernel
#print axioms pcSeed3_020_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_021 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 55), (qq (11) 200), (qq (6) 5), (qq (18) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (26620) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_021Palette : List KBranch := pcRawSeed3_021.law.palette 0
abbrev pcSeed3_021 : OrbitSeed := pcRawSeed3_021.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_021_ok : seedOK (pcHead 1) pcSeed3_021Palette 3 pcSeedLimit pcSeed3_021=true := by decide +kernel
#print axioms pcSeed3_021_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_022 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (11) 90), (qq (8) 65), (qq (17) 5), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6480) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_022Palette : List KBranch := pcRawSeed3_022.law.palette 0
abbrev pcSeed3_022 : OrbitSeed := pcRawSeed3_022.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_022_ok : seedOK (pcHead 1) pcSeed3_022Palette 3 pcSeedLimit pcSeed3_022=true := by decide +kernel
#print axioms pcSeed3_022_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_023 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 200), (qq (8) 145), (qq (17) 5), (qq (-22) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (32000) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_023Palette : List KBranch := pcRawSeed3_023.law.palette 0
abbrev pcSeed3_023 : OrbitSeed := pcRawSeed3_023.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_023_ok : seedOK (pcHead 1) pcSeed3_023Palette 3 pcSeedLimit pcSeed3_023=true := by decide +kernel
#print axioms pcSeed3_023_ok


def pcRawSeeds3O000 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed3_000, pcRawSeed3_001, pcRawSeed3_002, pcRawSeed3_003, pcRawSeed3_004, pcRawSeed3_005, pcRawSeed3_006, pcRawSeed3_007, pcRawSeed3_008, pcRawSeed3_009, pcRawSeed3_010, pcRawSeed3_011, pcRawSeed3_012, pcRawSeed3_013, pcRawSeed3_014, pcRawSeed3_015, pcRawSeed3_016, pcRawSeed3_017, pcRawSeed3_018, pcRawSeed3_019, pcRawSeed3_020, pcRawSeed3_021, pcRawSeed3_022, pcRawSeed3_023]
theorem pcRawSeeds3O000_ok : ∀ S∈pcRawSeeds3O000,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 10 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3O000,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed3_000_ok
  · exact pcSeed3_001_ok
  · exact pcSeed3_002_ok
  · exact pcSeed3_003_ok
  · exact pcSeed3_004_ok
  · exact pcSeed3_005_ok
  · exact pcSeed3_006_ok
  · exact pcSeed3_007_ok
  · exact pcSeed3_008_ok
  · exact pcSeed3_009_ok
  · exact pcSeed3_010_ok
  · exact pcSeed3_011_ok
  · exact pcSeed3_012_ok
  · exact pcSeed3_013_ok
  · exact pcSeed3_014_ok
  · exact pcSeed3_015_ok
  · exact pcSeed3_016_ok
  · exact pcSeed3_017_ok
  · exact pcSeed3_018_ok
  · exact pcSeed3_019_ok
  · exact pcSeed3_020_ok
  · exact pcSeed3_021_ok
  · exact pcSeed3_022_ok
  · exact pcSeed3_023_ok
#print axioms pcRawSeeds3O000_ok
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
