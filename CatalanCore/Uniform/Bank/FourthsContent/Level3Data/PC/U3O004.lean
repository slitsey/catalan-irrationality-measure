module

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 130), (qq (4) 47), (qq (16) 5), (qq (-12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (13520) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_096Palette : List KBranch := pcRawSeed3_096.law.palette 0
abbrev pcSeed3_096 : OrbitSeed := pcRawSeed3_096.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_096_ok : seedOK (pcHead 1) pcSeed3_096Palette 3 pcSeedLimit pcSeed3_096=true := by decide +kernel
#print axioms pcSeed3_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_097 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (4) 7), (qq (3) 5), (qq (11) 5), (qq (-1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (49) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_097Palette : List KBranch := pcRawSeed3_097.law.palette 0
abbrev pcSeed3_097 : OrbitSeed := pcRawSeed3_097.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_097_ok : seedOK (pcHead 1) pcSeed3_097Palette 3 pcSeedLimit pcSeed3_097=true := by decide +kernel
#print axioms pcSeed3_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_098 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (4) 47), (qq (3) 35), (qq (11) 5), (qq (-1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24299) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_098Palette : List KBranch := pcRawSeed3_098.law.palette 0
abbrev pcSeed3_098 : OrbitSeed := pcRawSeed3_098.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_098_ok : seedOK (pcHead 1) pcSeed3_098Palette 3 pcSeedLimit pcSeed3_098=true := by decide +kernel
#print axioms pcSeed3_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_099 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (3) 5), (qq (22) 35), (qq (1) 1), (qq (7) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (140) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_099Palette : List KBranch := pcRawSeed3_099.law.palette 0
abbrev pcSeed3_099 : OrbitSeed := pcRawSeed3_099.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_099_ok : seedOK (pcHead 1) pcSeed3_099Palette 3 pcSeedLimit pcSeed3_099=true := by decide +kernel
#print axioms pcSeed3_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_100 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (3) 35), (qq (22) 255), (qq (1) 1), (qq (55) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10780) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_100Palette : List KBranch := pcRawSeed3_100.law.palette 0
abbrev pcSeed3_100 : OrbitSeed := pcRawSeed3_100.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_100_ok : seedOK (pcHead 1) pcSeed3_100Palette 3 pcSeedLimit pcSeed3_100=true := by decide +kernel
#print axioms pcSeed3_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_101 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (22) 255), (qq (24) 275), (qq (16) 5), (qq (-47) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (13005) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_101Palette : List KBranch := pcRawSeed3_101.law.palette 0
abbrev pcSeed3_101 : OrbitSeed := pcRawSeed3_101.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_101_ok : seedOK (pcHead 1) pcSeed3_101Palette 3 pcSeedLimit pcSeed3_101=true := by decide +kernel
#print axioms pcSeed3_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_102 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (24) 275), (qq (1) 11), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (166375) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_102Palette : List KBranch := pcRawSeed3_102.law.palette 0
abbrev pcSeed3_102 : OrbitSeed := pcRawSeed3_102.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_102_ok : seedOK (pcHead 1) pcSeed3_102Palette 3 pcSeedLimit pcSeed3_102=true := by decide +kernel
#print axioms pcSeed3_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_103 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 11), (qq (11) 120), (qq (1) 1), (qq (13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5324) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_103Palette : List KBranch := pcRawSeed3_103.law.palette 0
abbrev pcSeed3_103 : OrbitSeed := pcRawSeed3_103.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_103_ok : seedOK (pcHead 1) pcSeed3_103Palette 3 pcSeedLimit pcSeed3_103=true := by decide +kernel
#print axioms pcSeed3_103_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_104 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 120), (qq (6) 65), (qq (16) 5), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11520) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_104Palette : List KBranch := pcRawSeed3_104.law.palette 0
abbrev pcSeed3_104 : OrbitSeed := pcRawSeed3_104.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_104_ok : seedOK (pcHead 1) pcSeed3_104Palette 3 pcSeedLimit pcSeed3_104=true := by decide +kernel
#print axioms pcSeed3_104_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_105 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (6) 65), (qq (4) 43), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9295) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_105Palette : List KBranch := pcRawSeed3_105.law.palette 0
abbrev pcSeed3_105 : OrbitSeed := pcRawSeed3_105.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_105_ok : seedOK (pcHead 1) pcSeed3_105Palette 3 pcSeedLimit pcSeed3_105=true := by decide +kernel
#print axioms pcSeed3_105_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_106 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (4) 43), (qq (22) 235), (qq (1) 1), (qq (51) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20339) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_106Palette : List KBranch := pcRawSeed3_106.law.palette 0
abbrev pcSeed3_106 : OrbitSeed := pcRawSeed3_106.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_106_ok : seedOK (pcHead 1) pcSeed3_106Palette 3 pcSeedLimit pcSeed3_106=true := by decide +kernel
#print axioms pcSeed3_106_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_107 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (22) 235), (qq (8) 85), (qq (16) 5), (qq (-43) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11045) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_107Palette : List KBranch := pcRawSeed3_107.law.palette 0
abbrev pcSeed3_107 : OrbitSeed := pcRawSeed3_107.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_107_ok : seedOK (pcHead 1) pcSeed3_107Palette 3 pcSeedLimit pcSeed3_107=true := by decide +kernel
#print axioms pcSeed3_107_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_108 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (8) 85), (qq (1) 10), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15895) 16)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_108Palette : List KBranch := pcRawSeed3_108.law.palette 0
abbrev pcSeed3_108 : OrbitSeed := pcRawSeed3_108.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_108_ok : seedOK (pcHead 1) pcSeed3_108Palette 3 pcSeedLimit pcSeed3_108=true := by decide +kernel
#print axioms pcSeed3_108_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_109 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (22) 115), (qq (199999) 1000000), (qq (9) 2), (qq (-25) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2000000) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_109Palette : List KBranch := pcRawSeed3_109.law.palette 0
abbrev pcSeed3_109 : OrbitSeed := pcRawSeed3_109.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_109_ok : seedOK (pcHead 1) pcSeed3_109Palette 3 pcSeedLimit pcSeed3_109=true := by decide +kernel
#print axioms pcSeed3_109_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_110 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩, ⟨10,by decide +kernel⟩]
  base := (⟨(qq (199999) 1000000), (qq (1) 5), (qq (-99977) 5), (qq (199975) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 1000000), (qq (2) 1)⟩], (qq (2000000) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_110Palette : List KBranch := pcRawSeed3_110.law.palette 0
abbrev pcSeed3_110 : OrbitSeed := pcRawSeed3_110.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_110_ok : seedOK (pcHead 1) pcSeed3_110Palette 3 pcSeedLimit pcSeed3_110=true := by decide +kernel
#print axioms pcSeed3_110_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_111 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (22) 35), (qq (1) 1), (qq (43) 10), (qq (-7) 2), (qq (1000000000000) 1)⟩, ⟨0, [(qq (24) 35)], [], (qq (490) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_111Palette : List KBranch := pcRawSeed3_111.law.palette 0
abbrev pcSeed3_111 : OrbitSeed := pcRawSeed3_111.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_111_ok : seedOK (pcHead 1) pcSeed3_111Palette 3 pcSeedLimit pcSeed3_111=true := by decide +kernel
#print axioms pcSeed3_111_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_112 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (11) 10), (qq (23) 10), (qq (-3) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 10), (qq (3) 2)⟩], (qq (30) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_112Palette : List KBranch := pcRawSeed3_112.law.palette 0
abbrev pcSeed3_112 : OrbitSeed := pcRawSeed3_112.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_112_ok : seedOK (pcHead 1) pcSeed3_112Palette 3 pcSeedLimit pcSeed3_112=true := by decide +kernel
#print axioms pcSeed3_112_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_113 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (11) 10), (qq (6) 5), (qq (17) 5), (qq (-5) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (280) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_113Palette : List KBranch := pcRawSeed3_113.law.palette 0
abbrev pcSeed3_113 : OrbitSeed := pcRawSeed3_113.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_113_ok : seedOK (pcHead 1) pcSeed3_113Palette 3 pcSeedLimit pcSeed3_113=true := by decide +kernel
#print axioms pcSeed3_113_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_114 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (6) 5), (qq (4) 3), (qq (11) 5), (qq (-3) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (70) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_114Palette : List KBranch := pcRawSeed3_114.law.palette 0
abbrev pcSeed3_114 : OrbitSeed := pcRawSeed3_114.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_114_ok : seedOK (pcHead 1) pcSeed3_114Palette 3 pcSeedLimit pcSeed3_114=true := by decide +kernel
#print axioms pcSeed3_114_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_115 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (4) 3), (qq (8) 5), (qq (6) 5), (qq (-3) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (21) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_115Palette : List KBranch := pcRawSeed3_115.law.palette 0
abbrev pcSeed3_115 : OrbitSeed := pcRawSeed3_115.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_115_ok : seedOK (pcHead 1) pcSeed3_115Palette 3 pcSeedLimit pcSeed3_115=true := by decide +kernel
#print axioms pcSeed3_115_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_116 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (8) 5), (qq (29) 5), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (35) 2)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_116Palette : List KBranch := pcRawSeed3_116.law.palette 0
abbrev pcSeed3_116 : OrbitSeed := pcRawSeed3_116.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_116_ok : seedOK (pcHead 1) pcSeed3_116Palette 3 pcSeedLimit pcSeed3_116=true := by decide +kernel
#print axioms pcSeed3_116_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_117 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (29) 5), (qq (14) 1), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (140) 29)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_117Palette : List KBranch := pcRawSeed3_117.law.palette 0
abbrev pcSeed3_117 : OrbitSeed := pcRawSeed3_117.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_117_ok : seedOK (pcHead 1) pcSeed3_117Palette 3 pcSeedLimit pcSeed3_117=true := by decide +kernel
#print axioms pcSeed3_117_ok


def pcRawSeeds3O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed3_096, pcRawSeed3_097, pcRawSeed3_098, pcRawSeed3_099, pcRawSeed3_100, pcRawSeed3_101, pcRawSeed3_102, pcRawSeed3_103, pcRawSeed3_104, pcRawSeed3_105, pcRawSeed3_106, pcRawSeed3_107, pcRawSeed3_108, pcRawSeed3_109, pcRawSeed3_110, pcRawSeed3_111, pcRawSeed3_112, pcRawSeed3_113, pcRawSeed3_114, pcRawSeed3_115, pcRawSeed3_116, pcRawSeed3_117]
theorem pcRawSeeds3O004_ok : ∀ S∈pcRawSeeds3O004,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 10 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed3_096_ok
  · exact pcSeed3_097_ok
  · exact pcSeed3_098_ok
  · exact pcSeed3_099_ok
  · exact pcSeed3_100_ok
  · exact pcSeed3_101_ok
  · exact pcSeed3_102_ok
  · exact pcSeed3_103_ok
  · exact pcSeed3_104_ok
  · exact pcSeed3_105_ok
  · exact pcSeed3_106_ok
  · exact pcSeed3_107_ok
  · exact pcSeed3_108_ok
  · exact pcSeed3_109_ok
  · exact pcSeed3_110_ok
  · exact pcSeed3_111_ok
  · exact pcSeed3_112_ok
  · exact pcSeed3_113_ok
  · exact pcSeed3_114_ok
  · exact pcSeed3_115_ok
  · exact pcSeed3_116_ok
  · exact pcSeed3_117_ok
#print axioms pcRawSeeds3O004_ok
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
