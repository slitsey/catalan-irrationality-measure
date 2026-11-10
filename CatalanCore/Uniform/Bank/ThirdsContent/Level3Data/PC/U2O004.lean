module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (39) 710), (qq (1) 18), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1159430) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_096Palette : List KBranch := pcRawSeed2_096.law.palette 0
abbrev pcSeed2_096 : OrbitSeed := pcRawSeed2_096.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_096_ok : seedOK (pcHead 1) pcSeed2_096Palette 2 pcSeedLimit pcSeed2_096=true := by decide +kernel
#print axioms pcSeed2_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_097 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (1) 18), (qq (69) 1240), (qq (13) 10), (qq (53) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11178) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_097Palette : List KBranch := pcRawSeed2_097.law.palette 0
abbrev pcSeed2_097 : OrbitSeed := pcRawSeed2_097.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_097_ok : seedOK (pcHead 1) pcSeed2_097Palette 2 pcSeedLimit pcSeed2_097=true := by decide +kernel
#print axioms pcSeed2_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_098 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (69) 1240), (qq (9) 160), (qq (18) 5), (qq (-71) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (153760) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_098Palette : List KBranch := pcRawSeed2_098.law.palette 0
abbrev pcSeed2_098 : OrbitSeed := pcRawSeed2_098.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_098_ok : seedOK (pcHead 1) pcSeed2_098Palette 2 pcSeedLimit pcSeed2_098=true := by decide +kernel
#print axioms pcSeed2_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_099 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (9) 160), (qq (13) 230), (qq (15) 4), (qq (-79) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (58880) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_099Palette : List KBranch := pcRawSeed2_099.law.palette 0
abbrev pcSeed2_099 : OrbitSeed := pcRawSeed2_099.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_099_ok : seedOK (pcHead 1) pcSeed2_099Palette 2 pcSeedLimit pcSeed2_099=true := by decide +kernel
#print axioms pcSeed2_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_100 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (13) 230), (qq (3) 53), (qq (49) 20), (qq (-10) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (365010) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_100Palette : List KBranch := pcRawSeed2_100.law.palette 0
abbrev pcSeed2_100 : OrbitSeed := pcRawSeed2_100.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_100_ok : seedOK (pcHead 1) pcSeed2_100Palette 2 pcSeedLimit pcSeed2_100=true := by decide +kernel
#print axioms pcSeed2_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_101 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (3) 53), (qq (39) 680), (qq (29) 20), (qq (43) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (64607) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_101Palette : List KBranch := pcRawSeed2_101.law.palette 0
abbrev pcSeed2_101 : OrbitSeed := pcRawSeed2_101.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_101_ok : seedOK (pcHead 1) pcSeed2_101Palette 2 pcSeedLimit pcSeed2_101=true := by decide +kernel
#print axioms pcSeed2_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_102 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (39) 680), (qq (23) 400), (qq (3) 20), (qq (37) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1063520) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_102Palette : List KBranch := pcRawSeed2_102.law.palette 0
abbrev pcSeed2_102 : OrbitSeed := pcRawSeed2_102.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_102_ok : seedOK (pcHead 1) pcSeed2_102Palette 2 pcSeedLimit pcSeed2_102=true := by decide +kernel
#print axioms pcSeed2_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_103 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 400), (qq (69) 1180), (qq (49) 20), (qq (-3) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (48000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_103Palette : List KBranch := pcRawSeed2_103.law.palette 0
abbrev pcSeed2_103 : OrbitSeed := pcRawSeed2_103.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_103_ok : seedOK (pcHead 1) pcSeed2_103Palette 2 pcSeedLimit pcSeed2_103=true := by decide +kernel
#print axioms pcSeed2_103_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_104 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (69) 1180), (qq (1) 17), (qq (19) 4), (qq (-127) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (139240) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_104Palette : List KBranch := pcRawSeed2_104.law.palette 0
abbrev pcSeed2_104 : OrbitSeed := pcRawSeed2_104.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_104_ok : seedOK (pcHead 1) pcSeed2_104Palette 2 pcSeedLimit pcSeed2_104=true := by decide +kernel
#print axioms pcSeed2_104_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_105 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (1) 17), (qq (13) 220), (qq (15) 4), (qq (-76) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19941) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_105Palette : List KBranch := pcRawSeed2_105.law.palette 0
abbrev pcSeed2_105 : OrbitSeed := pcRawSeed2_105.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_105_ok : seedOK (pcHead 1) pcSeed2_105Palette 2 pcSeedLimit pcSeed2_105=true := by decide +kernel
#print axioms pcSeed2_105_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_106 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (13) 220), (qq (3) 50), (qq (49) 20), (qq (-10) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (333960) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_106Palette : List KBranch := pcRawSeed2_106.law.palette 0
abbrev pcSeed2_106 : OrbitSeed := pcRawSeed2_106.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_106_ok : seedOK (pcHead 1) pcSeed2_106Palette 2 pcSeedLimit pcSeed2_106=true := by decide +kernel
#print axioms pcSeed2_106_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_107 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (3) 50), (qq (23) 380), (qq (-3) 20), (qq (40) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5750) 3)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_107Palette : List KBranch := pcRawSeed2_107.law.palette 0
abbrev pcSeed2_107 : OrbitSeed := pcRawSeed2_107.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_107_ok : seedOK (pcHead 1) pcSeed2_107Palette 2 pcSeedLimit pcSeed2_107=true := by decide +kernel
#print axioms pcSeed2_107_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_108 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 380), (qq (69) 1120), (qq (43) 20), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (43320) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_108Palette : List KBranch := pcRawSeed2_108.law.palette 0
abbrev pcSeed2_108 : OrbitSeed := pcRawSeed2_108.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_108_ok : seedOK (pcHead 1) pcSeed2_108Palette 2 pcSeedLimit pcSeed2_108=true := by decide +kernel
#print axioms pcSeed2_108_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_109 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (69) 1120), (qq (13) 210), (qq (89) 20), (qq (-106) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (125440) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_109Palette : List KBranch := pcRawSeed2_109.law.palette 0
abbrev pcSeed2_109 : OrbitSeed := pcRawSeed2_109.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_109_ok : seedOK (pcHead 1) pcSeed2_109Palette 2 pcSeedLimit pcSeed2_109=true := by decide +kernel
#print axioms pcSeed2_109_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_110 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (13) 210), (qq (1) 16), (qq (63) 20), (qq (-43) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (304290) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_110Palette : List KBranch := pcRawSeed2_110.law.palette 0
abbrev pcSeed2_110 : OrbitSeed := pcRawSeed2_110.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_110_ok : seedOK (pcHead 1) pcSeed2_110Palette 2 pcSeedLimit pcSeed2_110=true := by decide +kernel
#print axioms pcSeed2_110_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_111 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (1) 16), (qq (39) 620), (qq (43) 20), (qq (5) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8832) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_111Palette : List KBranch := pcRawSeed2_111.law.palette 0
abbrev pcSeed2_111 : OrbitSeed := pcRawSeed2_111.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_111_ok : seedOK (pcHead 1) pcSeed2_111Palette 2 pcSeedLimit pcSeed2_111=true := by decide +kernel
#print axioms pcSeed2_111_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_112 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (39) 620), (qq (3) 47), (qq (17) 20), (qq (67) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (884120) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_112Palette : List KBranch := pcRawSeed2_112.law.palette 0
abbrev pcSeed2_112 : OrbitSeed := pcRawSeed2_112.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_112_ok : seedOK (pcHead 1) pcSeed2_112Palette 2 pcSeedLimit pcSeed2_112=true := by decide +kernel
#print axioms pcSeed2_112_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_113 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 2 (by decide +kernel)
  base := (⟨(qq (3) 47), (qq (23) 360), (qq (-3) 20), (qq (38) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (50807) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_113Palette : List KBranch := pcRawSeed2_113.law.palette 0
abbrev pcSeed2_113 : OrbitSeed := pcRawSeed2_113.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_113_ok : seedOK (pcHead 1) pcSeed2_113Palette 2 pcSeedLimit pcSeed2_113=true := by decide +kernel
#print axioms pcSeed2_113_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_114 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 360), (qq (9) 140), (qq (43) 20), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (38880) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_114Palette : List KBranch := pcRawSeed2_114.law.palette 0
abbrev pcSeed2_114 : OrbitSeed := pcRawSeed2_114.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_114_ok : seedOK (pcHead 1) pcSeed2_114Palette 2 pcSeedLimit pcSeed2_114=true := by decide +kernel
#print axioms pcSeed2_114_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_115 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (9) 140), (qq (13) 200), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (45080) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_115Palette : List KBranch := pcRawSeed2_115.law.palette 0
abbrev pcSeed2_115 : OrbitSeed := pcRawSeed2_115.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_115_ok : seedOK (pcHead 1) pcSeed2_115Palette 2 pcSeedLimit pcSeed2_115=true := by decide +kernel
#print axioms pcSeed2_115_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_116 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (13) 200), (qq (69) 1060), (qq (1) 1), (qq (59) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (276000) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_116Palette : List KBranch := pcRawSeed2_116.law.palette 0
abbrev pcSeed2_116 : OrbitSeed := pcRawSeed2_116.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_116_ok : seedOK (pcHead 1) pcSeed2_116Palette 2 pcSeedLimit pcSeed2_116=true := by decide +kernel
#print axioms pcSeed2_116_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_117 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (69) 1060), (qq (39) 590), (qq (33) 10), (qq (-47) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (112360) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_117Palette : List KBranch := pcRawSeed2_117.law.palette 0
abbrev pcSeed2_117 : OrbitSeed := pcRawSeed2_117.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_117_ok : seedOK (pcHead 1) pcSeed2_117Palette 2 pcSeedLimit pcSeed2_117=true := by decide +kernel
#print axioms pcSeed2_117_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_118 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (39) 590), (qq (1) 15), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (800630) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_118Palette : List KBranch := pcRawSeed2_118.law.palette 0
abbrev pcSeed2_118 : OrbitSeed := pcRawSeed2_118.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_118_ok : seedOK (pcHead 1) pcSeed2_118Palette 2 pcSeedLimit pcSeed2_118=true := by decide +kernel
#print axioms pcSeed2_118_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_119 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (1) 15), (qq (23) 340), (qq (1) 1), (qq (19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3105) 2)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_119Palette : List KBranch := pcRawSeed2_119.law.palette 0
abbrev pcSeed2_119 : OrbitSeed := pcRawSeed2_119.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_119_ok : seedOK (pcHead 1) pcSeed2_119Palette 2 pcSeedLimit pcSeed2_119=true := by decide +kernel
#print axioms pcSeed2_119_ok


def pcRawSeeds2O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_096, pcRawSeed2_097, pcRawSeed2_098, pcRawSeed2_099, pcRawSeed2_100, pcRawSeed2_101, pcRawSeed2_102, pcRawSeed2_103, pcRawSeed2_104, pcRawSeed2_105, pcRawSeed2_106, pcRawSeed2_107, pcRawSeed2_108, pcRawSeed2_109, pcRawSeed2_110, pcRawSeed2_111, pcRawSeed2_112, pcRawSeed2_113, pcRawSeed2_114, pcRawSeed2_115, pcRawSeed2_116, pcRawSeed2_117, pcRawSeed2_118, pcRawSeed2_119]
theorem pcRawSeeds2O004_ok : ∀ S∈pcRawSeeds2O004,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_096_ok
  · exact pcSeed2_097_ok
  · exact pcSeed2_098_ok
  · exact pcSeed2_099_ok
  · exact pcSeed2_100_ok
  · exact pcSeed2_101_ok
  · exact pcSeed2_102_ok
  · exact pcSeed2_103_ok
  · exact pcSeed2_104_ok
  · exact pcSeed2_105_ok
  · exact pcSeed2_106_ok
  · exact pcSeed2_107_ok
  · exact pcSeed2_108_ok
  · exact pcSeed2_109_ok
  · exact pcSeed2_110_ok
  · exact pcSeed2_111_ok
  · exact pcSeed2_112_ok
  · exact pcSeed2_113_ok
  · exact pcSeed2_114_ok
  · exact pcSeed2_115_ok
  · exact pcSeed2_116_ok
  · exact pcSeed2_117_ok
  · exact pcSeed2_118_ok
  · exact pcSeed2_119_ok
#print axioms pcRawSeeds2O004_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
