module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_048 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (23) 540), (qq (3) 70), (qq (19) 4), (qq (-58) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (87480) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_048Palette : List KBranch := pcRawSeed1_048.law.palette 0
abbrev pcSeed1_048 : OrbitSeed := pcRawSeed1_048.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_048_ok : seedOK (pcHead 1) pcSeed1_048Palette 1 pcSeedLimit pcSeed1_048=true := by decide +kernel
#print axioms pcSeed1_048_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_049 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (3) 10), (qq (13) 40), (qq (43) 20), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (230) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_049Palette : List KBranch := pcRawSeed1_049.law.palette 0
abbrev pcSeed1_049 : OrbitSeed := pcRawSeed1_049.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_049_ok : seedOK (pcHead 1) pcSeed1_049Palette 1 pcSeedLimit pcSeed1_049=true := by decide +kernel
#print axioms pcSeed1_049_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_050 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (3) 70), (qq (13) 300), (qq (43) 20), (qq (8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11270) 3)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_050Palette : List KBranch := pcRawSeed1_050.law.palette 0
abbrev pcSeed1_050 : OrbitSeed := pcRawSeed1_050.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_050_ok : seedOK (pcHead 1) pcSeed1_050Palette 1 pcSeedLimit pcSeed1_050=true := by decide +kernel
#print axioms pcSeed1_050_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_051 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (13) 40), (qq (1) 3), (qq (17) 20), (qq (11) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (80) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_051Palette : List KBranch := pcRawSeed1_051.law.palette 0
abbrev pcSeed1_051 : OrbitSeed := pcRawSeed1_051.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_051_ok : seedOK (pcHead 1) pcSeed1_051Palette 1 pcSeedLimit pcSeed1_051=true := by decide +kernel
#print axioms pcSeed1_051_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_052 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (13) 300), (qq (1) 23), (qq (17) 20), (qq (98) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (621000) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_052Palette : List KBranch := pcRawSeed1_052.law.palette 0
abbrev pcSeed1_052 : OrbitSeed := pcRawSeed1_052.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_052_ok : seedOK (pcHead 1) pcSeed1_052Palette 1 pcSeedLimit pcSeed1_052=true := by decide +kernel
#print axioms pcSeed1_052_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_053 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 3), (qq (69) 200), (qq (-3) 20), (qq (20) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (621) 10)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_053Palette : List KBranch := pcRawSeed1_053.law.palette 0
abbrev pcSeed1_053 : OrbitSeed := pcRawSeed1_053.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_053_ok : seedOK (pcHead 1) pcSeed1_053Palette 1 pcSeedLimit pcSeed1_053=true := by decide +kernel
#print axioms pcSeed1_053_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_054 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (1) 23), (qq (69) 1580), (qq (-3) 20), (qq (167) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36501) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_054Palette : List KBranch := pcRawSeed1_054.law.palette 0
abbrev pcSeed1_054 : OrbitSeed := pcRawSeed1_054.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_054_ok : seedOK (pcHead 1) pcSeed1_054Palette 1 pcSeedLimit pcSeed1_054=true := by decide +kernel
#print axioms pcSeed1_054_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_055 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 200), (qq (23) 60), (qq (43) 20), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4000) 69)⟩)
  N := 8
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8]
abbrev pcSeed1_055Palette : List KBranch := pcRawSeed1_055.law.palette 0
abbrev pcSeed1_055 : OrbitSeed := pcRawSeed1_055.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=9 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_055_ok : seedOK (pcHead 1) pcSeed1_055Palette 1 pcSeedLimit pcSeed1_055=true := by decide +kernel
#print axioms pcSeed1_055_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_056 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (23) 60), (qq (39) 100), (qq (89) 20), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1080) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_056Palette : List KBranch := pcRawSeed1_056.law.palette 0
abbrev pcSeed1_056 : OrbitSeed := pcRawSeed1_056.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_056_ok : seedOK (pcHead 1) pcSeed1_056Palette 1 pcSeedLimit pcSeed1_056=true := by decide +kernel
#print axioms pcSeed1_056_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_057 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (23) 520), (qq (39) 880), (qq (89) 20), (qq (-49) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (81120) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_057Palette : List KBranch := pcRawSeed1_057.law.palette 0
abbrev pcSeed1_057 : OrbitSeed := pcRawSeed1_057.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_057_ok : seedOK (pcHead 1) pcSeed1_057Palette 1 pcSeedLimit pcSeed1_057=true := by decide +kernel
#print axioms pcSeed1_057_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_058 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (39) 100), (qq (3) 7), (qq (63) 20), (qq (-8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23000) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_058Palette : List KBranch := pcRawSeed1_058.law.palette 0
abbrev pcSeed1_058 : OrbitSeed := pcRawSeed1_058.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_058_ok : seedOK (pcHead 1) pcSeed1_058Palette 1 pcSeedLimit pcSeed1_058=true := by decide +kernel
#print axioms pcSeed1_058_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_059 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (39) 880), (qq (3) 67), (qq (63) 20), (qq (-59) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1781120) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_059Palette : List KBranch := pcRawSeed1_059.law.palette 0
abbrev pcSeed1_059 : OrbitSeed := pcRawSeed1_059.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_059_ok : seedOK (pcHead 1) pcSeed1_059Palette 1 pcSeedLimit pcSeed1_059=true := by decide +kernel
#print axioms pcSeed1_059_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_060 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (3) 7), (qq (13) 30), (qq (43) 20), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1127) 30)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_060Palette : List KBranch := pcRawSeed1_060.law.palette 0
abbrev pcSeed1_060 : OrbitSeed := pcRawSeed1_060.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_060_ok : seedOK (pcHead 1) pcSeed1_060Palette 1 pcSeedLimit pcSeed1_060=true := by decide +kernel
#print axioms pcSeed1_060_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_061 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (3) 67), (qq (13) 290), (qq (43) 20), (qq (8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (103247) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_061Palette : List KBranch := pcRawSeed1_061.law.palette 0
abbrev pcSeed1_061 : OrbitSeed := pcRawSeed1_061.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_061_ok : seedOK (pcHead 1) pcSeed1_061Palette 1 pcSeedLimit pcSeed1_061=true := by decide +kernel
#print axioms pcSeed1_061_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_062 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (13) 30), (qq (9) 20), (qq (17) 20), (qq (8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6210) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_062Palette : List KBranch := pcRawSeed1_062.law.palette 0
abbrev pcSeed1_062 : OrbitSeed := pcRawSeed1_062.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_062_ok : seedOK (pcHead 1) pcSeed1_062Palette 1 pcSeedLimit pcSeed1_062=true := by decide +kernel
#print axioms pcSeed1_062_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_063 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (13) 290), (qq (9) 200), (qq (17) 20), (qq (95) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (580290) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_063Palette : List KBranch := pcRawSeed1_063.law.palette 0
abbrev pcSeed1_063 : OrbitSeed := pcRawSeed1_063.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_063_ok : seedOK (pcHead 1) pcSeed1_063Palette 1 pcSeedLimit pcSeed1_063=true := by decide +kernel
#print axioms pcSeed1_063_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_064 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (9) 20), (qq (69) 140), (qq (1) 1), (qq (7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (920) 27)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_064Palette : List KBranch := pcRawSeed1_064.law.palette 0
abbrev pcSeed1_064 : OrbitSeed := pcRawSeed1_064.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_064_ok : seedOK (pcHead 1) pcSeed1_064Palette 1 pcSeedLimit pcSeed1_064=true := by decide +kernel
#print axioms pcSeed1_064_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_065 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (9) 200), (qq (69) 1520), (qq (1) 1), (qq (85) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (92000) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_065Palette : List KBranch := pcRawSeed1_065.law.palette 0
abbrev pcSeed1_065 : OrbitSeed := pcRawSeed1_065.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_065_ok : seedOK (pcHead 1) pcSeed1_065Palette 1 pcSeedLimit pcSeed1_065=true := by decide +kernel
#print axioms pcSeed1_065_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_066 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (69) 140), (qq (1) 2), (qq (33) 10), (qq (-7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1960) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_066Palette : List KBranch := pcRawSeed1_066.law.palette 0
abbrev pcSeed1_066 : OrbitSeed := pcRawSeed1_066.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_066_ok : seedOK (pcHead 1) pcSeed1_066Palette 1 pcSeedLimit pcSeed1_066=true := by decide +kernel
#print axioms pcSeed1_066_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_067 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (69) 1520), (qq (1) 22), (qq (33) 10), (qq (-67) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (231040) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_067Palette : List KBranch := pcRawSeed1_067.law.palette 0
abbrev pcSeed1_067 : OrbitSeed := pcRawSeed1_067.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_067_ok : seedOK (pcHead 1) pcSeed1_067Palette 1 pcSeedLimit pcSeed1_067=true := by decide +kernel
#print axioms pcSeed1_067_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_068 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (1) 2), (qq (39) 70), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (138) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_068Palette : List KBranch := pcRawSeed1_068.law.palette 0
abbrev pcSeed1_068 : OrbitSeed := pcRawSeed1_068.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_068_ok : seedOK (pcHead 1) pcSeed1_068Palette 1 pcSeedLimit pcSeed1_068=true := by decide +kernel
#print axioms pcSeed1_068_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_069 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (1) 22), (qq (39) 850), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16698) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_069Palette : List KBranch := pcRawSeed1_069.law.palette 0
abbrev pcSeed1_069 : OrbitSeed := pcRawSeed1_069.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_069_ok : seedOK (pcHead 1) pcSeed1_069Palette 1 pcSeedLimit pcSeed1_069=true := by decide +kernel
#print axioms pcSeed1_069_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_070 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (39) 70), (qq (23) 40), (qq (1) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11270) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_070Palette : List KBranch := pcRawSeed1_070.law.palette 0
abbrev pcSeed1_070 : OrbitSeed := pcRawSeed1_070.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_070_ok : seedOK (pcHead 1) pcSeed1_070Palette 1 pcSeedLimit pcSeed1_070=true := by decide +kernel
#print axioms pcSeed1_070_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_071 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (39) 850), (qq (23) 500), (qq (1) 1), (qq (28) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1661750) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_071Palette : List KBranch := pcRawSeed1_071.law.palette 0
abbrev pcSeed1_071 : OrbitSeed := pcRawSeed1_071.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_071_ok : seedOK (pcHead 1) pcSeed1_071Palette 1 pcSeedLimit pcSeed1_071=true := by decide +kernel
#print axioms pcSeed1_071_ok


def pcRawSeeds1O002 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_048, pcRawSeed1_049, pcRawSeed1_050, pcRawSeed1_051, pcRawSeed1_052, pcRawSeed1_053, pcRawSeed1_054, pcRawSeed1_055, pcRawSeed1_056, pcRawSeed1_057, pcRawSeed1_058, pcRawSeed1_059, pcRawSeed1_060, pcRawSeed1_061, pcRawSeed1_062, pcRawSeed1_063, pcRawSeed1_064, pcRawSeed1_065, pcRawSeed1_066, pcRawSeed1_067, pcRawSeed1_068, pcRawSeed1_069, pcRawSeed1_070, pcRawSeed1_071]
theorem pcRawSeeds1O002_ok : ∀ S∈pcRawSeeds1O002,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O002,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_048_ok
  · exact pcSeed1_049_ok
  · exact pcSeed1_050_ok
  · exact pcSeed1_051_ok
  · exact pcSeed1_052_ok
  · exact pcSeed1_053_ok
  · exact pcSeed1_054_ok
  · exact pcSeed1_055_ok
  · exact pcSeed1_056_ok
  · exact pcSeed1_057_ok
  · exact pcSeed1_058_ok
  · exact pcSeed1_059_ok
  · exact pcSeed1_060_ok
  · exact pcSeed1_061_ok
  · exact pcSeed1_062_ok
  · exact pcSeed1_063_ok
  · exact pcSeed1_064_ok
  · exact pcSeed1_065_ok
  · exact pcSeed1_066_ok
  · exact pcSeed1_067_ok
  · exact pcSeed1_068_ok
  · exact pcSeed1_069_ok
  · exact pcSeed1_070_ok
  · exact pcSeed1_071_ok
#print axioms pcRawSeeds1O002_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
