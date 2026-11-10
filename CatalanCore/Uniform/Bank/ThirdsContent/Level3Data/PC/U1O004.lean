module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (3) 55), (qq (23) 420), (qq (13) 10), (qq (18) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (13915) 6)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_096Palette : List KBranch := pcRawSeed1_096.law.palette 0
abbrev pcSeed1_096 : OrbitSeed := pcRawSeed1_096.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_096_ok : seedOK (pcHead 1) pcSeed1_096Palette 1 pcSeedLimit pcSeed1_096=true := by decide +kernel
#print axioms pcSeed1_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_097 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 420), (qq (1) 18), (qq (18) 5), (qq (-24) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (52920) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_097Palette : List KBranch := pcRawSeed1_097.law.palette 0
abbrev pcSeed1_097 : OrbitSeed := pcRawSeed1_097.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_097_ok : seedOK (pcHead 1) pcSeed1_097Palette 1 pcSeedLimit pcSeed1_097=true := by decide +kernel
#print axioms pcSeed1_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_098 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (1) 18), (qq (39) 700), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11178) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_098Palette : List KBranch := pcRawSeed1_098.law.palette 0
abbrev pcSeed1_098 : OrbitSeed := pcRawSeed1_098.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_098_ok : seedOK (pcHead 1) pcSeed1_098Palette 1 pcSeedLimit pcSeed1_098=true := by decide +kernel
#print axioms pcSeed1_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_099 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (39) 700), (qq (9) 160), (qq (13) 10), (qq (52) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1127000) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_099Palette : List KBranch := pcRawSeed1_099.law.palette 0
abbrev pcSeed1_099 : OrbitSeed := pcRawSeed1_099.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_099_ok : seedOK (pcHead 1) pcSeed1_099Palette 1 pcSeedLimit pcSeed1_099=true := by decide +kernel
#print axioms pcSeed1_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_100 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (9) 160), (qq (13) 230), (qq (29) 20), (qq (44) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (58880) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_100Palette : List KBranch := pcRawSeed1_100.law.palette 0
abbrev pcSeed1_100 : OrbitSeed := pcRawSeed1_100.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_100_ok : seedOK (pcHead 1) pcSeed1_100Palette 1 pcSeedLimit pcSeed1_100=true := by decide +kernel
#print axioms pcSeed1_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_101 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (13) 230), (qq (69) 1220), (qq (3) 20), (qq (113) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (365010) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_101Palette : List KBranch := pcRawSeed1_101.law.palette 0
abbrev pcSeed1_101 : OrbitSeed := pcRawSeed1_101.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_101_ok : seedOK (pcHead 1) pcSeed1_101Palette 1 pcSeedLimit pcSeed1_101=true := by decide +kernel
#print axioms pcSeed1_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_102 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 1220), (qq (23) 400), (qq (49) 20), (qq (-3) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (148840) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_102Palette : List KBranch := pcRawSeed1_102.law.palette 0
abbrev pcSeed1_102 : OrbitSeed := pcRawSeed1_102.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_102_ok : seedOK (pcHead 1) pcSeed1_102Palette 1 pcSeedLimit pcSeed1_102=true := by decide +kernel
#print axioms pcSeed1_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_103 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (23) 400), (qq (3) 52), (qq (19) 4), (qq (-43) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (48000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_103Palette : List KBranch := pcRawSeed1_103.law.palette 0
abbrev pcSeed1_103 : OrbitSeed := pcRawSeed1_103.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_103_ok : seedOK (pcHead 1) pcSeed1_103Palette 1 pcSeedLimit pcSeed1_103=true := by decide +kernel
#print axioms pcSeed1_103_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_104 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (3) 52), (qq (39) 670), (qq (15) 4), (qq (-77) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (31096) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_104Palette : List KBranch := pcRawSeed1_104.law.palette 0
abbrev pcSeed1_104 : OrbitSeed := pcRawSeed1_104.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_104_ok : seedOK (pcHead 1) pcSeed1_104Palette 1 pcSeedLimit pcSeed1_104=true := by decide +kernel
#print axioms pcSeed1_104_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_105 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (39) 670), (qq (1) 17), (qq (49) 20), (qq (-10) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1032470) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_105Palette : List KBranch := pcRawSeed1_105.law.palette 0
abbrev pcSeed1_105 : OrbitSeed := pcRawSeed1_105.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_105_ok : seedOK (pcHead 1) pcSeed1_105Palette 1 pcSeedLimit pcSeed1_105=true := by decide +kernel
#print axioms pcSeed1_105_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_106 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (1) 17), (qq (13) 220), (qq (29) 20), (qq (41) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19941) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_106Palette : List KBranch := pcRawSeed1_106.law.palette 0
abbrev pcSeed1_106 : OrbitSeed := pcRawSeed1_106.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_106_ok : seedOK (pcHead 1) pcSeed1_106Palette 1 pcSeedLimit pcSeed1_106=true := by decide +kernel
#print axioms pcSeed1_106_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_107 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (13) 220), (qq (69) 1160), (qq (3) 20), (qq (107) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (333960) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_107Palette : List KBranch := pcRawSeed1_107.law.palette 0
abbrev pcSeed1_107 : OrbitSeed := pcRawSeed1_107.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_107_ok : seedOK (pcHead 1) pcSeed1_107Palette 1 pcSeedLimit pcSeed1_107=true := by decide +kernel
#print axioms pcSeed1_107_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_108 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 1160), (qq (3) 50), (qq (49) 20), (qq (-3) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (134560) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_108Palette : List KBranch := pcRawSeed1_108.law.palette 0
abbrev pcSeed1_108 : OrbitSeed := pcRawSeed1_108.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_108_ok : seedOK (pcHead 1) pcSeed1_108Palette 1 pcSeedLimit pcSeed1_108=true := by decide +kernel
#print axioms pcSeed1_108_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_109 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (3) 50), (qq (23) 380), (qq (43) 20), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5750) 3)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_109Palette : List KBranch := pcRawSeed1_109.law.palette 0
abbrev pcSeed1_109 : OrbitSeed := pcRawSeed1_109.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_109_ok : seedOK (pcHead 1) pcSeed1_109Palette 1 pcSeedLimit pcSeed1_109=true := by decide +kernel
#print axioms pcSeed1_109_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_110 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (23) 380), (qq (39) 640), (qq (89) 20), (qq (-36) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (43320) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_110Palette : List KBranch := pcRawSeed1_110.law.palette 0
abbrev pcSeed1_110 : OrbitSeed := pcRawSeed1_110.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_110_ok : seedOK (pcHead 1) pcSeed1_110Palette 1 pcSeedLimit pcSeed1_110=true := by decide +kernel
#print axioms pcSeed1_110_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_111 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (39) 640), (qq (3) 49), (qq (63) 20), (qq (-44) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (942080) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_111Palette : List KBranch := pcRawSeed1_111.law.palette 0
abbrev pcSeed1_111 : OrbitSeed := pcRawSeed1_111.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_111_ok : seedOK (pcHead 1) pcSeed1_111Palette 1 pcSeedLimit pcSeed1_111=true := by decide +kernel
#print axioms pcSeed1_111_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_112 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (3) 49), (qq (13) 210), (qq (43) 20), (qq (5) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (55223) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_112Palette : List KBranch := pcRawSeed1_112.law.palette 0
abbrev pcSeed1_112 : OrbitSeed := pcRawSeed1_112.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_112_ok : seedOK (pcHead 1) pcSeed1_112Palette 1 pcSeedLimit pcSeed1_112=true := by decide +kernel
#print axioms pcSeed1_112_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_113 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (13) 210), (qq (1) 16), (qq (17) 20), (qq (68) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (304290) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_113Palette : List KBranch := pcRawSeed1_113.law.palette 0
abbrev pcSeed1_113 : OrbitSeed := pcRawSeed1_113.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_113_ok : seedOK (pcHead 1) pcSeed1_113Palette 1 pcSeedLimit pcSeed1_113=true := by decide +kernel
#print axioms pcSeed1_113_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_114 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (1) 16), (qq (69) 1100), (qq (-3) 20), (qq (116) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8832) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_114Palette : List KBranch := pcRawSeed1_114.law.palette 0
abbrev pcSeed1_114 : OrbitSeed := pcRawSeed1_114.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_114_ok : seedOK (pcHead 1) pcSeed1_114Palette 1 pcSeedLimit pcSeed1_114=true := by decide +kernel
#print axioms pcSeed1_114_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_115 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 1100), (qq (23) 360), (qq (43) 20), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (121000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_115Palette : List KBranch := pcRawSeed1_115.law.palette 0
abbrev pcSeed1_115 : OrbitSeed := pcRawSeed1_115.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_115_ok : seedOK (pcHead 1) pcSeed1_115Palette 1 pcSeedLimit pcSeed1_115=true := by decide +kernel
#print axioms pcSeed1_115_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_116 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (23) 360), (qq (39) 610), (qq (89) 20), (qq (-34) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (38880) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_116Palette : List KBranch := pcRawSeed1_116.law.palette 0
abbrev pcSeed1_116 : OrbitSeed := pcRawSeed1_116.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_116_ok : seedOK (pcHead 1) pcSeed1_116Palette 1 pcSeedLimit pcSeed1_116=true := by decide +kernel
#print axioms pcSeed1_116_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_117 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (39) 610), (qq (9) 140), (qq (63) 20), (qq (-41) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (855830) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_117Palette : List KBranch := pcRawSeed1_117.law.palette 0
abbrev pcSeed1_117 : OrbitSeed := pcRawSeed1_117.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_117_ok : seedOK (pcHead 1) pcSeed1_117Palette 1 pcSeedLimit pcSeed1_117=true := by decide +kernel
#print axioms pcSeed1_117_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_118 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (9) 140), (qq (13) 200), (qq (33) 10), (qq (-16) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (45080) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_118Palette : List KBranch := pcRawSeed1_118.law.palette 0
abbrev pcSeed1_118 : OrbitSeed := pcRawSeed1_118.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_118_ok : seedOK (pcHead 1) pcSeed1_118Palette 1 pcSeedLimit pcSeed1_118=true := by decide +kernel
#print axioms pcSeed1_118_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_119 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (13) 200), (qq (3) 46), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (276000) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_119Palette : List KBranch := pcRawSeed1_119.law.palette 0
abbrev pcSeed1_119 : OrbitSeed := pcRawSeed1_119.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_119_ok : seedOK (pcHead 1) pcSeed1_119Palette 1 pcSeedLimit pcSeed1_119=true := by decide +kernel
#print axioms pcSeed1_119_ok


def pcRawSeeds1O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_096, pcRawSeed1_097, pcRawSeed1_098, pcRawSeed1_099, pcRawSeed1_100, pcRawSeed1_101, pcRawSeed1_102, pcRawSeed1_103, pcRawSeed1_104, pcRawSeed1_105, pcRawSeed1_106, pcRawSeed1_107, pcRawSeed1_108, pcRawSeed1_109, pcRawSeed1_110, pcRawSeed1_111, pcRawSeed1_112, pcRawSeed1_113, pcRawSeed1_114, pcRawSeed1_115, pcRawSeed1_116, pcRawSeed1_117, pcRawSeed1_118, pcRawSeed1_119]
theorem pcRawSeeds1O004_ok : ∀ S∈pcRawSeeds1O004,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_096_ok
  · exact pcSeed1_097_ok
  · exact pcSeed1_098_ok
  · exact pcSeed1_099_ok
  · exact pcSeed1_100_ok
  · exact pcSeed1_101_ok
  · exact pcSeed1_102_ok
  · exact pcSeed1_103_ok
  · exact pcSeed1_104_ok
  · exact pcSeed1_105_ok
  · exact pcSeed1_106_ok
  · exact pcSeed1_107_ok
  · exact pcSeed1_108_ok
  · exact pcSeed1_109_ok
  · exact pcSeed1_110_ok
  · exact pcSeed1_111_ok
  · exact pcSeed1_112_ok
  · exact pcSeed1_113_ok
  · exact pcSeed1_114_ok
  · exact pcSeed1_115_ok
  · exact pcSeed1_116_ok
  · exact pcSeed1_117_ok
  · exact pcSeed1_118_ok
  · exact pcSeed1_119_ok
#print axioms pcRawSeeds1O004_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
