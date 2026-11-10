module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_048 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (3) 10), (qq (69) 220), (qq (43) 20), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (230) 3)⟩)
  N := 8
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8]
abbrev pcSeed2_048Palette : List KBranch := pcRawSeed2_048.law.palette 0
abbrev pcSeed2_048 : OrbitSeed := pcRawSeed2_048.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=9 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_048_ok : seedOK (pcHead 1) pcSeed2_048Palette 2 pcSeedLimit pcSeed2_048=true := by decide +kernel
#print axioms pcSeed2_048_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_049 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (69) 220), (qq (13) 40), (qq (89) 20), (qq (-22) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (440) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_049Palette : List KBranch := pcRawSeed2_049.law.palette 0
abbrev pcSeed2_049 : OrbitSeed := pcRawSeed2_049.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_049_ok : seedOK (pcHead 1) pcSeed2_049Palette 2 pcSeedLimit pcSeed2_049=true := by decide +kernel
#print axioms pcSeed2_049_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_050 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (69) 1600), (qq (13) 300), (qq (89) 20), (qq (-151) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (256000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_050Palette : List KBranch := pcRawSeed2_050.law.palette 0
abbrev pcSeed2_050 : OrbitSeed := pcRawSeed2_050.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_050_ok : seedOK (pcHead 1) pcSeed2_050Palette 2 pcSeedLimit pcSeed2_050=true := by decide +kernel
#print axioms pcSeed2_050_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_051 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (13) 40), (qq (1) 3), (qq (63) 20), (qq (-10) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (80) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_051Palette : List KBranch := pcRawSeed2_051.law.palette 0
abbrev pcSeed2_051 : OrbitSeed := pcRawSeed2_051.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_051_ok : seedOK (pcHead 1) pcSeed2_051Palette 2 pcSeedLimit pcSeed2_051=true := by decide +kernel
#print axioms pcSeed2_051_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_052 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (13) 300), (qq (1) 23), (qq (63) 20), (qq (-61) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (621000) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_052Palette : List KBranch := pcRawSeed2_052.law.palette 0
abbrev pcSeed2_052 : OrbitSeed := pcRawSeed2_052.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_052_ok : seedOK (pcHead 1) pcSeed2_052Palette 2 pcSeedLimit pcSeed2_052=true := by decide +kernel
#print axioms pcSeed2_052_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_053 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 3), (qq (39) 110), (qq (43) 20), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (621) 10)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_053Palette : List KBranch := pcRawSeed2_053.law.palette 0
abbrev pcSeed2_053 : OrbitSeed := pcRawSeed2_053.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_053_ok : seedOK (pcHead 1) pcSeed2_053Palette 2 pcSeedLimit pcSeed2_053=true := by decide +kernel
#print axioms pcSeed2_053_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_054 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (1) 23), (qq (39) 890), (qq (43) 20), (qq (8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36501) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_054Palette : List KBranch := pcRawSeed2_054.law.palette 0
abbrev pcSeed2_054 : OrbitSeed := pcRawSeed2_054.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_054_ok : seedOK (pcHead 1) pcSeed2_054Palette 2 pcSeedLimit pcSeed2_054=true := by decide +kernel
#print axioms pcSeed2_054_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_055 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (39) 110), (qq (3) 8), (qq (17) 20), (qq (10) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (27830) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_055Palette : List KBranch := pcRawSeed2_055.law.palette 0
abbrev pcSeed2_055 : OrbitSeed := pcRawSeed2_055.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_055_ok : seedOK (pcHead 1) pcSeed2_055Palette 2 pcSeedLimit pcSeed2_055=true := by decide +kernel
#print axioms pcSeed2_055_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_056 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (39) 890), (qq (3) 68), (qq (17) 20), (qq (97) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1821830) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_056Palette : List KBranch := pcRawSeed2_056.law.palette 0
abbrev pcSeed2_056 : OrbitSeed := pcRawSeed2_056.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_056_ok : seedOK (pcHead 1) pcSeed2_056Palette 2 pcSeedLimit pcSeed2_056=true := by decide +kernel
#print axioms pcSeed2_056_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_057 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (3) 8), (qq (23) 60), (qq (-3) 20), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (736) 15)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_057Palette : List KBranch := pcRawSeed2_057.law.palette 0
abbrev pcSeed2_057 : OrbitSeed := pcRawSeed2_057.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_057_ok : seedOK (pcHead 1) pcSeed2_057Palette 2 pcSeedLimit pcSeed2_057=true := by decide +kernel
#print axioms pcSeed2_057_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_058 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (3) 68), (qq (23) 520), (qq (-3) 20), (qq (55) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (53176) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_058Palette : List KBranch := pcRawSeed2_058.law.palette 0
abbrev pcSeed2_058 : OrbitSeed := pcRawSeed2_058.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_058_ok : seedOK (pcHead 1) pcSeed2_058Palette 2 pcSeedLimit pcSeed2_058=true := by decide +kernel
#print axioms pcSeed2_058_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_059 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 60), (qq (69) 160), (qq (43) 20), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1080) 23)⟩)
  N := 8
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8]
abbrev pcSeed2_059Palette : List KBranch := pcRawSeed2_059.law.palette 0
abbrev pcSeed2_059 : OrbitSeed := pcRawSeed2_059.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=9 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_059_ok : seedOK (pcHead 1) pcSeed2_059Palette 2 pcSeedLimit pcSeed2_059=true := by decide +kernel
#print axioms pcSeed2_059_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_060 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (69) 160), (qq (13) 30), (qq (89) 20), (qq (-16) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2560) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_060Palette : List KBranch := pcRawSeed2_060.law.palette 0
abbrev pcSeed2_060 : OrbitSeed := pcRawSeed2_060.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_060_ok : seedOK (pcHead 1) pcSeed2_060Palette 2 pcSeedLimit pcSeed2_060=true := by decide +kernel
#print axioms pcSeed2_060_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_061 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (69) 1540), (qq (13) 290), (qq (89) 20), (qq (-145) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (237160) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_061Palette : List KBranch := pcRawSeed2_061.law.palette 0
abbrev pcSeed2_061 : OrbitSeed := pcRawSeed2_061.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_061_ok : seedOK (pcHead 1) pcSeed2_061Palette 2 pcSeedLimit pcSeed2_061=true := by decide +kernel
#print axioms pcSeed2_061_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_062 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (13) 30), (qq (9) 20), (qq (63) 20), (qq (-7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6210) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_062Palette : List KBranch := pcRawSeed2_062.law.palette 0
abbrev pcSeed2_062 : OrbitSeed := pcRawSeed2_062.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_062_ok : seedOK (pcHead 1) pcSeed2_062Palette 2 pcSeedLimit pcSeed2_062=true := by decide +kernel
#print axioms pcSeed2_062_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_063 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 3 (by decide +kernel)
  base := (⟨(qq (13) 290), (qq (9) 200), (qq (63) 20), (qq (-58) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (580290) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_063Palette : List KBranch := pcRawSeed2_063.law.palette 0
abbrev pcSeed2_063 : OrbitSeed := pcRawSeed2_063.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_063_ok : seedOK (pcHead 1) pcSeed2_063Palette 2 pcSeedLimit pcSeed2_063=true := by decide +kernel
#print axioms pcSeed2_063_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_064 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (9) 20), (qq (39) 80), (qq (33) 10), (qq (-8) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (920) 27)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_064Palette : List KBranch := pcRawSeed2_064.law.palette 0
abbrev pcSeed2_064 : OrbitSeed := pcRawSeed2_064.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_064_ok : seedOK (pcHead 1) pcSeed2_064Palette 2 pcSeedLimit pcSeed2_064=true := by decide +kernel
#print axioms pcSeed2_064_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_065 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (9) 200), (qq (39) 860), (qq (33) 10), (qq (-68) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (92000) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_065Palette : List KBranch := pcRawSeed2_065.law.palette 0
abbrev pcSeed2_065 : OrbitSeed := pcRawSeed2_065.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_065_ok : seedOK (pcHead 1) pcSeed2_065Palette 2 pcSeedLimit pcSeed2_065=true := by decide +kernel
#print axioms pcSeed2_065_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_066 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (39) 80), (qq (1) 2), (qq (2) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14720) 507)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_066Palette : List KBranch := pcRawSeed2_066.law.palette 0
abbrev pcSeed2_066 : OrbitSeed := pcRawSeed2_066.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_066_ok : seedOK (pcHead 1) pcSeed2_066Palette 2 pcSeedLimit pcSeed2_066=true := by decide +kernel
#print axioms pcSeed2_066_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_067 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (39) 860), (qq (1) 22), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1701080) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_067Palette : List KBranch := pcRawSeed2_067.law.palette 0
abbrev pcSeed2_067 : OrbitSeed := pcRawSeed2_067.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_067_ok : seedOK (pcHead 1) pcSeed2_067Palette 2 pcSeedLimit pcSeed2_067=true := by decide +kernel
#print axioms pcSeed2_067_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_068 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (1) 2), (qq (23) 40), (qq (1) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (138) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_068Palette : List KBranch := pcRawSeed2_068.law.palette 0
abbrev pcSeed2_068 : OrbitSeed := pcRawSeed2_068.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_068_ok : seedOK (pcHead 1) pcSeed2_068Palette 2 pcSeedLimit pcSeed2_068=true := by decide +kernel
#print axioms pcSeed2_068_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_069 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (1) 22), (qq (23) 500), (qq (1) 1), (qq (28) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16698) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_069Palette : List KBranch := pcRawSeed2_069.law.palette 0
abbrev pcSeed2_069 : OrbitSeed := pcRawSeed2_069.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_069_ok : seedOK (pcHead 1) pcSeed2_069Palette 2 pcSeedLimit pcSeed2_069=true := by decide +kernel
#print axioms pcSeed2_069_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_070 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (23) 40), (qq (3) 5), (qq (33) 10), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (480) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_070Palette : List KBranch := pcRawSeed2_070.law.palette 0
abbrev pcSeed2_070 : OrbitSeed := pcRawSeed2_070.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_070_ok : seedOK (pcHead 1) pcSeed2_070Palette 2 pcSeedLimit pcSeed2_070=true := by decide +kernel
#print axioms pcSeed2_070_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_071 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (23) 500), (qq (3) 65), (qq (33) 10), (qq (-22) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (75000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_071Palette : List KBranch := pcRawSeed2_071.law.palette 0
abbrev pcSeed2_071 : OrbitSeed := pcRawSeed2_071.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_071_ok : seedOK (pcHead 1) pcSeed2_071Palette 2 pcSeedLimit pcSeed2_071=true := by decide +kernel
#print axioms pcSeed2_071_ok


def pcRawSeeds2O002 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_048, pcRawSeed2_049, pcRawSeed2_050, pcRawSeed2_051, pcRawSeed2_052, pcRawSeed2_053, pcRawSeed2_054, pcRawSeed2_055, pcRawSeed2_056, pcRawSeed2_057, pcRawSeed2_058, pcRawSeed2_059, pcRawSeed2_060, pcRawSeed2_061, pcRawSeed2_062, pcRawSeed2_063, pcRawSeed2_064, pcRawSeed2_065, pcRawSeed2_066, pcRawSeed2_067, pcRawSeed2_068, pcRawSeed2_069, pcRawSeed2_070, pcRawSeed2_071]
theorem pcRawSeeds2O002_ok : ∀ S∈pcRawSeeds2O002,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O002,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_048_ok
  · exact pcSeed2_049_ok
  · exact pcSeed2_050_ok
  · exact pcSeed2_051_ok
  · exact pcSeed2_052_ok
  · exact pcSeed2_053_ok
  · exact pcSeed2_054_ok
  · exact pcSeed2_055_ok
  · exact pcSeed2_056_ok
  · exact pcSeed2_057_ok
  · exact pcSeed2_058_ok
  · exact pcSeed2_059_ok
  · exact pcSeed2_060_ok
  · exact pcSeed2_061_ok
  · exact pcSeed2_062_ok
  · exact pcSeed2_063_ok
  · exact pcSeed2_064_ok
  · exact pcSeed2_065_ok
  · exact pcSeed2_066_ok
  · exact pcSeed2_067_ok
  · exact pcSeed2_068_ok
  · exact pcSeed2_069_ok
  · exact pcSeed2_070_ok
  · exact pcSeed2_071_ok
#print axioms pcRawSeeds2O002_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
