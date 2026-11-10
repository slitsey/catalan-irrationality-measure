module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_000 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (1) 180), (qq (3) 530), (qq (49) 20), (qq (-27) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (223560) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_000Palette : List KBranch := pcRawSeed1_000.law.palette 0
abbrev pcSeed1_000 : OrbitSeed := pcRawSeed1_000.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_000_ok : seedOK (pcHead 1) pcSeed1_000Palette 1 pcSeedLimit pcSeed1_000=true := by decide +kernel
#print axioms pcSeed1_000_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_001 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (3) 530), (qq (3) 520), (qq (43) 20), (qq (26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (646070) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_001Palette : List KBranch := pcRawSeed1_001.law.palette 0
abbrev pcSeed1_001 : OrbitSeed := pcRawSeed1_001.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_001_ok : seedOK (pcHead 1) pcSeed1_001Palette 1 pcSeedLimit pcSeed1_001=true := by decide +kernel
#print axioms pcSeed1_001_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_002 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (3) 520), (qq (1) 170), (qq (49) 20), (qq (-26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (621920) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_002Palette : List KBranch := pcRawSeed1_002.law.palette 0
abbrev pcSeed1_002 : OrbitSeed := pcRawSeed1_002.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_002_ok : seedOK (pcHead 1) pcSeed1_002Palette 1 pcSeedLimit pcSeed1_002=true := by decide +kernel
#print axioms pcSeed1_002_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_003 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (1) 170), (qq (3) 500), (qq (43) 20), (qq (25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (199410) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_003Palette : List KBranch := pcRawSeed1_003.law.palette 0
abbrev pcSeed1_003 : OrbitSeed := pcRawSeed1_003.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_003_ok : seedOK (pcHead 1) pcSeed1_003Palette 1 pcSeedLimit pcSeed1_003=true := by decide +kernel
#print axioms pcSeed1_003_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_004 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩, ⟨0,by decide +kernel⟩]
  base := (⟨(qq (3) 20), (qq (39) 250), (qq (13) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨true, 1, (qq (3) 500), (qq (3) 2)⟩], (qq (920) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_004Palette : List KBranch := pcRawSeed1_004.law.palette 0
abbrev pcSeed1_004 : OrbitSeed := pcRawSeed1_004.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_004_ok : seedOK (pcHead 1) pcSeed1_004Palette 1 pcSeedLimit pcSeed1_004=true := by decide +kernel
#print axioms pcSeed1_004_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_005 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (3) 80), (qq (39) 1030), (qq (13) 5), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14720) 3)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_005Palette : List KBranch := pcRawSeed1_005.law.palette 0
abbrev pcSeed1_005 : OrbitSeed := pcRawSeed1_005.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_005_ok : seedOK (pcHead 1) pcSeed1_005Palette 1 pcSeedLimit pcSeed1_005=true := by decide +kernel
#print axioms pcSeed1_005_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_006 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (39) 250), (qq (69) 440), (qq (13) 10), (qq (19) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (143750) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_006Palette : List KBranch := pcRawSeed1_006.law.palette 0
abbrev pcSeed1_006 : OrbitSeed := pcRawSeed1_006.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_006_ok : seedOK (pcHead 1) pcSeed1_006Palette 1 pcSeedLimit pcSeed1_006=true := by decide +kernel
#print axioms pcSeed1_006_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_007 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (39) 1030), (qq (69) 1820), (qq (13) 10), (qq (79) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2440070) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_007Palette : List KBranch := pcRawSeed1_007.law.palette 0
abbrev pcSeed1_007 : OrbitSeed := pcRawSeed1_007.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_007_ok : seedOK (pcHead 1) pcSeed1_007Palette 1 pcSeedLimit pcSeed1_007=true := by decide +kernel
#print axioms pcSeed1_007_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_008 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (69) 440), (qq (3) 19), (qq (18) 5), (qq (-25) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19360) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_008Palette : List KBranch := pcRawSeed1_008.law.palette 0
abbrev pcSeed1_008 : OrbitSeed := pcRawSeed1_008.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_008_ok : seedOK (pcHead 1) pcSeed1_008Palette 1 pcSeedLimit pcSeed1_008=true := by decide +kernel
#print axioms pcSeed1_008_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_009 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (69) 1820), (qq (3) 79), (qq (18) 5), (qq (-103) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (331240) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_009Palette : List KBranch := pcRawSeed1_009.law.palette 0
abbrev pcSeed1_009 : OrbitSeed := pcRawSeed1_009.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_009_ok : seedOK (pcHead 1) pcSeed1_009Palette 1 pcSeedLimit pcSeed1_009=true := by decide +kernel
#print axioms pcSeed1_009_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_010 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (3) 19), (qq (13) 80), (qq (13) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8303) 30)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_010Palette : List KBranch := pcRawSeed1_010.law.palette 0
abbrev pcSeed1_010 : OrbitSeed := pcRawSeed1_010.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_010_ok : seedOK (pcHead 1) pcSeed1_010Palette 1 pcSeedLimit pcSeed1_010=true := by decide +kernel
#print axioms pcSeed1_010_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_011 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (3) 79), (qq (13) 340), (qq (13) 5), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (143543) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_011Palette : List KBranch := pcRawSeed1_011.law.palette 0
abbrev pcSeed1_011 : OrbitSeed := pcRawSeed1_011.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_011_ok : seedOK (pcHead 1) pcSeed1_011Palette 1 pcSeedLimit pcSeed1_011=true := by decide +kernel
#print axioms pcSeed1_011_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_012 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (13) 80), (qq (23) 140), (qq (13) 10), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (44160) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_012Palette : List KBranch := pcRawSeed1_012.law.palette 0
abbrev pcSeed1_012 : OrbitSeed := pcRawSeed1_012.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_012_ok : seedOK (pcHead 1) pcSeed1_012Palette 1 pcSeedLimit pcSeed1_012=true := by decide +kernel
#print axioms pcSeed1_012_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_013 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (13) 340), (qq (23) 600), (qq (13) 10), (qq (26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (797640) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_013Palette : List KBranch := pcRawSeed1_013.law.palette 0
abbrev pcSeed1_013 : OrbitSeed := pcRawSeed1_013.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_013_ok : seedOK (pcHead 1) pcSeed1_013Palette 1 pcSeedLimit pcSeed1_013=true := by decide +kernel
#print axioms pcSeed1_013_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_014 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (23) 140), (qq (1) 6), (qq (18) 5), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5880) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_014Palette : List KBranch := pcRawSeed1_014.law.palette 0
abbrev pcSeed1_014 : OrbitSeed := pcRawSeed1_014.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_014_ok : seedOK (pcHead 1) pcSeed1_014Palette 1 pcSeedLimit pcSeed1_014=true := by decide +kernel
#print axioms pcSeed1_014_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_015 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (23) 600), (qq (1) 26), (qq (18) 5), (qq (-34) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (108000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_015Palette : List KBranch := pcRawSeed1_015.law.palette 0
abbrev pcSeed1_015 : OrbitSeed := pcRawSeed1_015.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_015_ok : seedOK (pcHead 1) pcSeed1_015Palette 1 pcSeedLimit pcSeed1_015=true := by decide +kernel
#print axioms pcSeed1_015_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_016 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (1) 6), (qq (39) 220), (qq (13) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1242) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_016Palette : List KBranch := pcRawSeed1_016.law.palette 0
abbrev pcSeed1_016 : OrbitSeed := pcRawSeed1_016.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_016_ok : seedOK (pcHead 1) pcSeed1_016Palette 1 pcSeedLimit pcSeed1_016=true := by decide +kernel
#print axioms pcSeed1_016_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_017 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (1) 26), (qq (39) 1000), (qq (13) 5), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23322) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_017Palette : List KBranch := pcRawSeed1_017.law.palette 0
abbrev pcSeed1_017 : OrbitSeed := pcRawSeed1_017.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_017_ok : seedOK (pcHead 1) pcSeed1_017Palette 1 pcSeedLimit pcSeed1_017=true := by decide +kernel
#print axioms pcSeed1_017_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_018 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (39) 220), (qq (69) 380), (qq (13) 10), (qq (16) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (111320) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_018Palette : List KBranch := pcRawSeed1_018.law.palette 0
abbrev pcSeed1_018 : OrbitSeed := pcRawSeed1_018.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_018_ok : seedOK (pcHead 1) pcSeed1_018Palette 1 pcSeedLimit pcSeed1_018=true := by decide +kernel
#print axioms pcSeed1_018_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_019 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 2
  base := (⟨(qq (39) 1000), (qq (69) 1760), (qq (13) 10), (qq (76) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2300000) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_019Palette : List KBranch := pcRawSeed1_019.law.palette 0
abbrev pcSeed1_019 : OrbitSeed := pcRawSeed1_019.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_019_ok : seedOK (pcHead 1) pcSeed1_019Palette 1 pcSeedLimit pcSeed1_019=true := by decide +kernel
#print axioms pcSeed1_019_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_020 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (69) 380), (qq (13) 70), (qq (18) 5), (qq (-22) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14440) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_020Palette : List KBranch := pcRawSeed1_020.law.palette 0
abbrev pcSeed1_020 : OrbitSeed := pcRawSeed1_020.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_020_ok : seedOK (pcHead 1) pcSeed1_020Palette 1 pcSeedLimit pcSeed1_020=true := by decide +kernel
#print axioms pcSeed1_020_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_021 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (69) 1760), (qq (13) 330), (qq (18) 5), (qq (-100) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (309760) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_021Palette : List KBranch := pcRawSeed1_021.law.palette 0
abbrev pcSeed1_021 : OrbitSeed := pcRawSeed1_021.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_021_ok : seedOK (pcHead 1) pcSeed1_021Palette 1 pcSeedLimit pcSeed1_021=true := by decide +kernel
#print axioms pcSeed1_021_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_022 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨13,by decide +kernel⟩]
  base := (⟨(qq (13) 70), (qq (3) 16), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (33810) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_022Palette : List KBranch := pcRawSeed1_022.law.palette 0
abbrev pcSeed1_022 : OrbitSeed := pcRawSeed1_022.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_022_ok : seedOK (pcHead 1) pcSeed1_022Palette 1 pcSeedLimit pcSeed1_022=true := by decide +kernel
#print axioms pcSeed1_022_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_023 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (13) 330), (qq (3) 76), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (751410) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_023Palette : List KBranch := pcRawSeed1_023.law.palette 0
abbrev pcSeed1_023 : OrbitSeed := pcRawSeed1_023.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_023_ok : seedOK (pcHead 1) pcSeed1_023Palette 1 pcSeedLimit pcSeed1_023=true := by decide +kernel
#print axioms pcSeed1_023_ok


def pcRawSeeds1O000 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_000, pcRawSeed1_001, pcRawSeed1_002, pcRawSeed1_003, pcRawSeed1_004, pcRawSeed1_005, pcRawSeed1_006, pcRawSeed1_007, pcRawSeed1_008, pcRawSeed1_009, pcRawSeed1_010, pcRawSeed1_011, pcRawSeed1_012, pcRawSeed1_013, pcRawSeed1_014, pcRawSeed1_015, pcRawSeed1_016, pcRawSeed1_017, pcRawSeed1_018, pcRawSeed1_019, pcRawSeed1_020, pcRawSeed1_021, pcRawSeed1_022, pcRawSeed1_023]
theorem pcRawSeeds1O000_ok : ∀ S∈pcRawSeeds1O000,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
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
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
