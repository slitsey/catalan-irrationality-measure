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
def pcRawSeed4_000 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩, ⟨0,by decide +kernel⟩]
  base := (⟨(qq (1) 9), (qq (55) 486), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨true, 1, (qq (1) 486), (qq (3) 2)⟩], (qq (900) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_000Palette : List KBranch := pcRawSeed4_000.law.palette 0
abbrev pcSeed4_000 : OrbitSeed := pcRawSeed4_000.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_000_ok : seedOK (pcHead 1) pcSeed4_000Palette 4 pcSeedLimit pcSeed4_000=true := by decide +kernel
#print axioms pcSeed4_000_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_001 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 18), (qq (55) 981), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3600) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_001Palette : List KBranch := pcRawSeed4_001.law.palette 0
abbrev pcSeed4_001 : OrbitSeed := pcRawSeed4_001.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_001_ok : seedOK (pcHead 1) pcSeed4_001Palette 4 pcSeedLimit pcSeed4_001=true := by decide +kernel
#print axioms pcSeed4_001_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_002 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨17,by decide +kernel⟩]
  base := (⟨(qq (55) 486), (qq (50) 441), (qq (11) 9), (qq (44) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (104976) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_002Palette : List KBranch := pcRawSeed4_002.law.palette 0
abbrev pcSeed4_002 : OrbitSeed := pcRawSeed4_002.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_002_ok : seedOK (pcHead 1) pcSeed4_002Palette 4 pcSeedLimit pcSeed4_002=true := by decide +kernel
#print axioms pcSeed4_002_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_003 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (55) 981), (qq (50) 891), (qq (11) 9), (qq (89) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (427716) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_003Palette : List KBranch := pcRawSeed4_003.law.palette 0
abbrev pcSeed4_003 : OrbitSeed := pcRawSeed4_003.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_003_ok : seedOK (pcHead 1) pcSeed4_003Palette 4 pcSeedLimit pcSeed4_003=true := by decide +kernel
#print axioms pcSeed4_003_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_004 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (50) 441), (qq (5) 44), (qq (31) 9), (qq (-54) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (21609) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_004Palette : List KBranch := pcRawSeed4_004.law.palette 0
abbrev pcSeed4_004 : OrbitSeed := pcRawSeed4_004.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_004_ok : seedOK (pcHead 1) pcSeed4_004Palette 4 pcSeedLimit pcSeed4_004=true := by decide +kernel
#print axioms pcSeed4_004_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_005 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (50) 891), (qq (5) 89), (qq (31) 9), (qq (-109) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (88209) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_005Palette : List KBranch := pcRawSeed4_005.law.palette 0
abbrev pcSeed4_005 : OrbitSeed := pcRawSeed4_005.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_005_ok : seedOK (pcHead 1) pcSeed4_005Palette 4 pcSeedLimit pcSeed4_005=true := by decide +kernel
#print axioms pcSeed4_005_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_006 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (5) 44), (qq (11) 90), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7744) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_006Palette : List KBranch := pcRawSeed4_006.law.palette 0
abbrev pcSeed4_006 : OrbitSeed := pcRawSeed4_006.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_006_ok : seedOK (pcHead 1) pcSeed4_006Palette 4 pcSeedLimit pcSeed4_006=true := by decide +kernel
#print axioms pcSeed4_006_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_007 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 89), (qq (11) 189), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (31684) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_007Palette : List KBranch := pcRawSeed4_007.law.palette 0
abbrev pcSeed4_007 : OrbitSeed := pcRawSeed4_007.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_007_ok : seedOK (pcHead 1) pcSeed4_007Palette 4 pcSeedLimit pcSeed4_007=true := by decide +kernel
#print axioms pcSeed4_007_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_008 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨16,by decide +kernel⟩]
  base := (⟨(qq (11) 90), (qq (10) 81), (qq (11) 9), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (90000) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_008Palette : List KBranch := pcRawSeed4_008.law.palette 0
abbrev pcSeed4_008 : OrbitSeed := pcRawSeed4_008.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_008_ok : seedOK (pcHead 1) pcSeed4_008Palette 4 pcSeedLimit pcSeed4_008=true := by decide +kernel
#print axioms pcSeed4_008_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_009 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 189), (qq (10) 171), (qq (11) 9), (qq (17) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (396900) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_009Palette : List KBranch := pcRawSeed4_009.law.palette 0
abbrev pcSeed4_009 : OrbitSeed := pcRawSeed4_009.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_009_ok : seedOK (pcHead 1) pcSeed4_009Palette 4 pcSeedLimit pcSeed4_009=true := by decide +kernel
#print axioms pcSeed4_009_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_010 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (10) 81), (qq (55) 441), (qq (31) 9), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (729) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_010Palette : List KBranch := pcRawSeed4_010.law.palette 0
abbrev pcSeed4_010 : OrbitSeed := pcRawSeed4_010.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_010_ok : seedOK (pcHead 1) pcSeed4_010Palette 4 pcSeedLimit pcSeed4_010=true := by decide +kernel
#print axioms pcSeed4_010_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_011 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 171), (qq (55) 936), (qq (31) 9), (qq (-21) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3249) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_011Palette : List KBranch := pcRawSeed4_011.law.palette 0
abbrev pcSeed4_011 : OrbitSeed := pcRawSeed4_011.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_011_ok : seedOK (pcHead 1) pcSeed4_011Palette 4 pcSeedLimit pcSeed4_011=true := by decide +kernel
#print axioms pcSeed4_011_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_012 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (55) 441), (qq (1) 8), (qq (20) 9), (qq (-1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (86436) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_012Palette : List KBranch := pcRawSeed4_012.law.palette 0
abbrev pcSeed4_012 : OrbitSeed := pcRawSeed4_012.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_012_ok : seedOK (pcHead 1) pcSeed4_012Palette 4 pcSeedLimit pcSeed4_012=true := by decide +kernel
#print axioms pcSeed4_012_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_013 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (55) 936), (qq (1) 17), (qq (20) 9), (qq (-1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (389376) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_013Palette : List KBranch := pcRawSeed4_013.law.palette 0
abbrev pcSeed4_013 : OrbitSeed := pcRawSeed4_013.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_013_ok : seedOK (pcHead 1) pcSeed4_013Palette 4 pcSeedLimit pcSeed4_013=true := by decide +kernel
#print axioms pcSeed4_013_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_014 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨15,by decide +kernel⟩]
  base := (⟨(qq (1) 8), (qq (25) 198), (qq (11) 9), (qq (39) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6400) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_014Palette : List KBranch := pcRawSeed4_014.law.palette 0
abbrev pcSeed4_014 : OrbitSeed := pcRawSeed4_014.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_014_ok : seedOK (pcHead 1) pcSeed4_014Palette 4 pcSeedLimit pcSeed4_014=true := by decide +kernel
#print axioms pcSeed4_014_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_015 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 17), (qq (25) 423), (qq (11) 9), (qq (84) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (28900) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_015Palette : List KBranch := pcRawSeed4_015.law.palette 0
abbrev pcSeed4_015 : OrbitSeed := pcRawSeed4_015.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_015_ok : seedOK (pcHead 1) pcSeed4_015Palette 4 pcSeedLimit pcSeed4_015=true := by decide +kernel
#print axioms pcSeed4_015_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_016 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (25) 198), (qq (5) 39), (qq (31) 9), (qq (-49) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17424) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_016Palette : List KBranch := pcRawSeed4_016.law.palette 0
abbrev pcSeed4_016 : OrbitSeed := pcRawSeed4_016.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_016_ok : seedOK (pcHead 1) pcSeed4_016Palette 4 pcSeedLimit pcSeed4_016=true := by decide +kernel
#print axioms pcSeed4_016_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_017 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (25) 423), (qq (5) 84), (qq (31) 9), (qq (-104) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (79524) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_017Palette : List KBranch := pcRawSeed4_017.law.palette 0
abbrev pcSeed4_017 : OrbitSeed := pcRawSeed4_017.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_017_ok : seedOK (pcHead 1) pcSeed4_017Palette 4 pcSeedLimit pcSeed4_017=true := by decide +kernel
#print axioms pcSeed4_017_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_018 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (5) 39), (qq (11) 81), (qq (22) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (676) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_018Palette : List KBranch := pcRawSeed4_018.law.palette 0
abbrev pcSeed4_018 : OrbitSeed := pcRawSeed4_018.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_018_ok : seedOK (pcHead 1) pcSeed4_018Palette 4 pcSeedLimit pcSeed4_018=true := by decide +kernel
#print axioms pcSeed4_018_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_019 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (5) 84), (qq (11) 180), (qq (22) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3136) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_019Palette : List KBranch := pcRawSeed4_019.law.palette 0
abbrev pcSeed4_019 : OrbitSeed := pcRawSeed4_019.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_019_ok : seedOK (pcHead 1) pcSeed4_019Palette 4 pcSeedLimit pcSeed4_019=true := by decide +kernel
#print axioms pcSeed4_019_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_020 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨14,by decide +kernel⟩]
  base := (⟨(qq (11) 81), (qq (5) 36), (qq (11) 9), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (72900) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_020Palette : List KBranch := pcRawSeed4_020.law.palette 0
abbrev pcSeed4_020 : OrbitSeed := pcRawSeed4_020.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_020_ok : seedOK (pcHead 1) pcSeed4_020Palette 4 pcSeedLimit pcSeed4_020=true := by decide +kernel
#print axioms pcSeed4_020_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_021 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (11) 180), (qq (5) 81), (qq (11) 9), (qq (16) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (360000) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_021Palette : List KBranch := pcRawSeed4_021.law.palette 0
abbrev pcSeed4_021 : OrbitSeed := pcRawSeed4_021.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_021_ok : seedOK (pcHead 1) pcSeed4_021Palette 4 pcSeedLimit pcSeed4_021=true := by decide +kernel
#print axioms pcSeed4_021_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_022 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (5) 36), (qq (50) 351), (qq (7) 3), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (576) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed4_022Palette : List KBranch := pcRawSeed4_022.law.palette 0
abbrev pcSeed4_022 : OrbitSeed := pcRawSeed4_022.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_022_ok : seedOK (pcHead 1) pcSeed4_022Palette 4 pcSeedLimit pcSeed4_022=true := by decide +kernel
#print axioms pcSeed4_022_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_023 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (50) 351), (qq (1) 7), (qq (41) 9), (qq (-83) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (13689) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_023Palette : List KBranch := pcRawSeed4_023.law.palette 0
abbrev pcSeed4_023 : OrbitSeed := pcRawSeed4_023.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_023_ok : seedOK (pcHead 1) pcSeed4_023Palette 4 pcSeedLimit pcSeed4_023=true := by decide +kernel
#print axioms pcSeed4_023_ok


def pcRawSeeds4O000 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed4_000, pcRawSeed4_001, pcRawSeed4_002, pcRawSeed4_003, pcRawSeed4_004, pcRawSeed4_005, pcRawSeed4_006, pcRawSeed4_007, pcRawSeed4_008, pcRawSeed4_009, pcRawSeed4_010, pcRawSeed4_011, pcRawSeed4_012, pcRawSeed4_013, pcRawSeed4_014, pcRawSeed4_015, pcRawSeed4_016, pcRawSeed4_017, pcRawSeed4_018, pcRawSeed4_019, pcRawSeed4_020, pcRawSeed4_021, pcRawSeed4_022, pcRawSeed4_023]
theorem pcRawSeeds4O000_ok : ∀ S∈pcRawSeeds4O000,
    seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds4O000,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed4_000_ok
  · exact pcSeed4_001_ok
  · exact pcSeed4_002_ok
  · exact pcSeed4_003_ok
  · exact pcSeed4_004_ok
  · exact pcSeed4_005_ok
  · exact pcSeed4_006_ok
  · exact pcSeed4_007_ok
  · exact pcSeed4_008_ok
  · exact pcSeed4_009_ok
  · exact pcSeed4_010_ok
  · exact pcSeed4_011_ok
  · exact pcSeed4_012_ok
  · exact pcSeed4_013_ok
  · exact pcSeed4_014_ok
  · exact pcSeed4_015_ok
  · exact pcSeed4_016_ok
  · exact pcSeed4_017_ok
  · exact pcSeed4_018_ok
  · exact pcSeed4_019_ok
  · exact pcSeed4_020_ok
  · exact pcSeed4_021_ok
  · exact pcSeed4_022_ok
  · exact pcSeed4_023_ok
#print axioms pcRawSeeds4O000_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
