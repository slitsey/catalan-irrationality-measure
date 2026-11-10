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
def pcRawSeed1_000 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩, ⟨0,by decide +kernel⟩]
  base := (⟨(qq (1) 10), (qq (8) 75), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨true, 1, (qq (1) 150), (qq (3) 2)⟩], (qq (880) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_000Palette : List KBranch := pcRawSeed1_000.law.palette 0
abbrev pcSeed1_000 : OrbitSeed := pcRawSeed1_000.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_000_ok : seedOK (pcHead 1) pcSeed1_000Palette 1 pcSeedLimit pcSeed1_000=true := by decide +kernel
#print axioms pcSeed1_000_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_001 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 20), (qq (8) 155), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3520) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_001Palette : List KBranch := pcRawSeed1_001.law.palette 0
abbrev pcSeed1_001 : OrbitSeed := pcRawSeed1_001.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_001_ok : seedOK (pcHead 1) pcSeed1_001Palette 1 pcSeedLimit pcSeed1_001=true := by decide +kernel
#print axioms pcSeed1_001_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_002 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩]
  base := (⟨(qq (8) 75), (qq (22) 205), (qq (6) 5), (qq (37) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12375) 16)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_002Palette : List KBranch := pcRawSeed1_002.law.palette 0
abbrev pcSeed1_002 : OrbitSeed := pcRawSeed1_002.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_002_ok : seedOK (pcHead 1) pcSeed1_002Palette 1 pcSeedLimit pcSeed1_002=true := by decide +kernel
#print axioms pcSeed1_002_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_003 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (8) 155), (qq (22) 425), (qq (6) 5), (qq (77) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (52855) 16)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_003Palette : List KBranch := pcRawSeed1_003.law.palette 0
abbrev pcSeed1_003 : OrbitSeed := pcRawSeed1_003.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_003_ok : seedOK (pcHead 1) pcSeed1_003Palette 1 pcSeedLimit pcSeed1_003=true := by decide +kernel
#print axioms pcSeed1_003_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_004 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (22) 205), (qq (4) 37), (qq (17) 5), (qq (-45) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8405) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_004Palette : List KBranch := pcRawSeed1_004.law.palette 0
abbrev pcSeed1_004 : OrbitSeed := pcRawSeed1_004.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_004_ok : seedOK (pcHead 1) pcSeed1_004Palette 1 pcSeedLimit pcSeed1_004=true := by decide +kernel
#print axioms pcSeed1_004_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_005 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (22) 425), (qq (4) 77), (qq (17) 5), (qq (-93) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36125) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_005Palette : List KBranch := pcRawSeed1_005.law.palette 0
abbrev pcSeed1_005 : OrbitSeed := pcRawSeed1_005.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_005_ok : seedOK (pcHead 1) pcSeed1_005Palette 1 pcSeedLimit pcSeed1_005=true := by decide +kernel
#print axioms pcSeed1_005_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_006 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (4) 37), (qq (6) 55), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15059) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_006Palette : List KBranch := pcRawSeed1_006.law.palette 0
abbrev pcSeed1_006 : OrbitSeed := pcRawSeed1_006.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_006_ok : seedOK (pcHead 1) pcSeed1_006Palette 1 pcSeedLimit pcSeed1_006=true := by decide +kernel
#print axioms pcSeed1_006_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_007 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (4) 77), (qq (6) 115), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (65219) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_007Palette : List KBranch := pcRawSeed1_007.law.palette 0
abbrev pcSeed1_007 : OrbitSeed := pcRawSeed1_007.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_007_ok : seedOK (pcHead 1) pcSeed1_007Palette 1 pcSeedLimit pcSeed1_007=true := by decide +kernel
#print axioms pcSeed1_007_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_008 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (6) 55), (qq (11) 100), (qq (6) 5), (qq (9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6655) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_008Palette : List KBranch := pcRawSeed1_008.law.palette 0
abbrev pcSeed1_008 : OrbitSeed := pcRawSeed1_008.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_008_ok : seedOK (pcHead 1) pcSeed1_008Palette 1 pcSeedLimit pcSeed1_008=true := by decide +kernel
#print axioms pcSeed1_008_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_009 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (6) 115), (qq (11) 210), (qq (6) 5), (qq (19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (29095) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_009Palette : List KBranch := pcRawSeed1_009.law.palette 0
abbrev pcSeed1_009 : OrbitSeed := pcRawSeed1_009.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_009_ok : seedOK (pcHead 1) pcSeed1_009Palette 1 pcSeedLimit pcSeed1_009=true := by decide +kernel
#print axioms pcSeed1_009_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_010 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (11) 100), (qq (1) 9), (qq (17) 5), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8000) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_010Palette : List KBranch := pcRawSeed1_010.law.palette 0
abbrev pcSeed1_010 : OrbitSeed := pcRawSeed1_010.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_010_ok : seedOK (pcHead 1) pcSeed1_010Palette 1 pcSeedLimit pcSeed1_010=true := by decide +kernel
#print axioms pcSeed1_010_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_011 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 210), (qq (1) 19), (qq (17) 5), (qq (-23) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (35280) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_011Palette : List KBranch := pcRawSeed1_011.law.palette 0
abbrev pcSeed1_011 : OrbitSeed := pcRawSeed1_011.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_011_ok : seedOK (pcHead 1) pcSeed1_011Palette 1 pcSeedLimit pcSeed1_011=true := by decide +kernel
#print axioms pcSeed1_011_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_012 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (1) 9), (qq (24) 205), (qq (12) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3564) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_012Palette : List KBranch := pcRawSeed1_012.law.palette 0
abbrev pcSeed1_012 : OrbitSeed := pcRawSeed1_012.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_012_ok : seedOK (pcHead 1) pcSeed1_012Palette 1 pcSeedLimit pcSeed1_012=true := by decide +kernel
#print axioms pcSeed1_012_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_013 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 19), (qq (24) 445), (qq (12) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15884) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_013Palette : List KBranch := pcRawSeed1_013.law.palette 0
abbrev pcSeed1_013 : OrbitSeed := pcRawSeed1_013.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_013_ok : seedOK (pcHead 1) pcSeed1_013Palette 1 pcSeedLimit pcSeed1_013=true := by decide +kernel
#print axioms pcSeed1_013_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_014 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (24) 205), (qq (22) 185), (qq (6) 5), (qq (33) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (92455) 144)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_014Palette : List KBranch := pcRawSeed1_014.law.palette 0
abbrev pcSeed1_014 : OrbitSeed := pcRawSeed1_014.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_014_ok : seedOK (pcHead 1) pcSeed1_014Palette 1 pcSeedLimit pcSeed1_014=true := by decide +kernel
#print axioms pcSeed1_014_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_015 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (24) 445), (qq (22) 405), (qq (6) 5), (qq (73) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (435655) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_015Palette : List KBranch := pcRawSeed1_015.law.palette 0
abbrev pcSeed1_015 : OrbitSeed := pcRawSeed1_015.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_015_ok : seedOK (pcHead 1) pcSeed1_015Palette 1 pcSeedLimit pcSeed1_015=true := by decide +kernel
#print axioms pcSeed1_015_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_016 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (22) 185), (qq (3) 25), (qq (17) 5), (qq (-41) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6845) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_016Palette : List KBranch := pcRawSeed1_016.law.palette 0
abbrev pcSeed1_016 : OrbitSeed := pcRawSeed1_016.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_016_ok : seedOK (pcHead 1) pcSeed1_016Palette 1 pcSeedLimit pcSeed1_016=true := by decide +kernel
#print axioms pcSeed1_016_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_017 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (22) 405), (qq (3) 55), (qq (17) 5), (qq (-89) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (32805) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_017Palette : List KBranch := pcRawSeed1_017.law.palette 0
abbrev pcSeed1_017 : OrbitSeed := pcRawSeed1_017.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_017_ok : seedOK (pcHead 1) pcSeed1_017Palette 1 pcSeedLimit pcSeed1_017=true := by decide +kernel
#print axioms pcSeed1_017_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_018 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (3) 25), (qq (4) 33), (qq (11) 5), (qq (-1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5500) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_018Palette : List KBranch := pcRawSeed1_018.law.palette 0
abbrev pcSeed1_018 : OrbitSeed := pcRawSeed1_018.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_018_ok : seedOK (pcHead 1) pcSeed1_018Palette 1 pcSeedLimit pcSeed1_018=true := by decide +kernel
#print axioms pcSeed1_018_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_019 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 55), (qq (4) 73), (qq (11) 5), (qq (-1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (26620) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_019Palette : List KBranch := pcRawSeed1_019.law.palette 0
abbrev pcSeed1_019 : OrbitSeed := pcRawSeed1_019.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_019_ok : seedOK (pcHead 1) pcSeed1_019Palette 1 pcSeedLimit pcSeed1_019=true := by decide +kernel
#print axioms pcSeed1_019_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_020 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (4) 33), (qq (11) 90), (qq (6) 5), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11979) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_020Palette : List KBranch := pcRawSeed1_020.law.palette 0
abbrev pcSeed1_020 : OrbitSeed := pcRawSeed1_020.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_020_ok : seedOK (pcHead 1) pcSeed1_020Palette 1 pcSeedLimit pcSeed1_020=true := by decide +kernel
#print axioms pcSeed1_020_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_021 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (4) 73), (qq (11) 200), (qq (6) 5), (qq (18) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (58619) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_021Palette : List KBranch := pcRawSeed1_021.law.palette 0
abbrev pcSeed1_021 : OrbitSeed := pcRawSeed1_021.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_021_ok : seedOK (pcHead 1) pcSeed1_021Palette 1 pcSeedLimit pcSeed1_021=true := by decide +kernel
#print axioms pcSeed1_021_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_022 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (11) 90), (qq (1) 8), (qq (17) 5), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6480) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_022Palette : List KBranch := pcRawSeed1_022.law.palette 0
abbrev pcSeed1_022 : OrbitSeed := pcRawSeed1_022.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_022_ok : seedOK (pcHead 1) pcSeed1_022Palette 1 pcSeedLimit pcSeed1_022=true := by decide +kernel
#print axioms pcSeed1_022_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_023 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 200), (qq (1) 18), (qq (17) 5), (qq (-22) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (32000) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_023Palette : List KBranch := pcRawSeed1_023.law.palette 0
abbrev pcSeed1_023 : OrbitSeed := pcRawSeed1_023.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_023_ok : seedOK (pcHead 1) pcSeed1_023Palette 1 pcSeedLimit pcSeed1_023=true := by decide +kernel
#print axioms pcSeed1_023_ok


def pcRawSeeds1O000 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_000, pcRawSeed1_001, pcRawSeed1_002, pcRawSeed1_003, pcRawSeed1_004, pcRawSeed1_005, pcRawSeed1_006, pcRawSeed1_007, pcRawSeed1_008, pcRawSeed1_009, pcRawSeed1_010, pcRawSeed1_011, pcRawSeed1_012, pcRawSeed1_013, pcRawSeed1_014, pcRawSeed1_015, pcRawSeed1_016, pcRawSeed1_017, pcRawSeed1_018, pcRawSeed1_019, pcRawSeed1_020, pcRawSeed1_021, pcRawSeed1_022, pcRawSeed1_023]
theorem pcRawSeeds1O000_ok : ∀ S∈pcRawSeeds1O000,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 10 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O000,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_000_ok
  · exact pcSeed1_001_ok
  · exact pcSeed1_002_ok
  · exact pcSeed1_003_ok
  · exact pcSeed1_004_ok
  · exact pcSeed1_005_ok
  · exact pcSeed1_006_ok
  · exact pcSeed1_007_ok
  · exact pcSeed1_008_ok
  · exact pcSeed1_009_ok
  · exact pcSeed1_010_ok
  · exact pcSeed1_011_ok
  · exact pcSeed1_012_ok
  · exact pcSeed1_013_ok
  · exact pcSeed1_014_ok
  · exact pcSeed1_015_ok
  · exact pcSeed1_016_ok
  · exact pcSeed1_017_ok
  · exact pcSeed1_018_ok
  · exact pcSeed1_019_ok
  · exact pcSeed1_020_ok
  · exact pcSeed1_021_ok
  · exact pcSeed1_022_ok
  · exact pcSeed1_023_ok
#print axioms pcRawSeeds1O000_ok
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
