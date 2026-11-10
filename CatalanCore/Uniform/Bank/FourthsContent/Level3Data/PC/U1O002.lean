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
def pcRawSeed1_048 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (6) 35), (qq (22) 125), (qq (1) 10), (qq (23) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2695) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_048Palette : List KBranch := pcRawSeed1_048.law.palette 0
abbrev pcSeed1_048 : OrbitSeed := pcRawSeed1_048.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_048_ok : seedOK (pcHead 1) pcSeed1_048Palette 1 pcSeedLimit pcSeed1_048=true := by decide +kernel
#print axioms pcSeed1_048_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_049 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (6) 95), (qq (22) 345), (qq (1) 10), (qq (65) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19855) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_049Palette : List KBranch := pcRawSeed1_049.law.palette 0
abbrev pcSeed1_049 : OrbitSeed := pcRawSeed1_049.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_049_ok : seedOK (pcHead 1) pcSeed1_049Palette 1 pcSeedLimit pcSeed1_049=true := by decide +kernel
#print axioms pcSeed1_049_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_050 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (22) 125), (qq (11) 60), (qq (23) 10), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3125) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed1_050Palette : List KBranch := pcRawSeed1_050.law.palette 0
abbrev pcSeed1_050 : OrbitSeed := pcRawSeed1_050.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_050_ok : seedOK (pcHead 1) pcSeed1_050Palette 1 pcSeedLimit pcSeed1_050=true := by decide +kernel
#print axioms pcSeed1_050_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_051 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (11) 60), (qq (4) 21), (qq (9) 2), (qq (-13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2880) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_051Palette : List KBranch := pcRawSeed1_051.law.palette 0
abbrev pcSeed1_051 : OrbitSeed := pcRawSeed1_051.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_051_ok : seedOK (pcHead 1) pcSeed1_051Palette 1 pcSeedLimit pcSeed1_051=true := by decide +kernel
#print axioms pcSeed1_051_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_052 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 170), (qq (4) 61), (qq (9) 2), (qq (-36) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23120) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_052Palette : List KBranch := pcRawSeed1_052.law.palette 0
abbrev pcSeed1_052 : OrbitSeed := pcRawSeed1_052.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_052_ok : seedOK (pcHead 1) pcSeed1_052Palette 1 pcSeedLimit pcSeed1_052=true := by decide +kernel
#print axioms pcSeed1_052_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_053 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (4) 21), (qq (24) 125), (qq (7) 2), (qq (-31) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (250) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_053Palette : List KBranch := pcRawSeed1_053.law.palette 0
abbrev pcSeed1_053 : OrbitSeed := pcRawSeed1_053.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_053_ok : seedOK (pcHead 1) pcSeed1_053Palette 1 pcSeedLimit pcSeed1_053=true := by decide +kernel
#print axioms pcSeed1_053_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_054 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 61), (qq (24) 365), (qq (7) 2), (qq (-83) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (40931) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_054Palette : List KBranch := pcRawSeed1_054.law.palette 0
abbrev pcSeed1_054 : OrbitSeed := pcRawSeed1_054.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_054_ok : seedOK (pcHead 1) pcSeed1_054Palette 1 pcSeedLimit pcSeed1_054=true := by decide +kernel
#print axioms pcSeed1_054_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_055 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (24) 365), (qq (1) 15), (qq (23) 10), (qq (-5) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (293095) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_055Palette : List KBranch := pcRawSeed1_055.law.palette 0
abbrev pcSeed1_055 : OrbitSeed := pcRawSeed1_055.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_055_ok : seedOK (pcHead 1) pcSeed1_055Palette 1 pcSeedLimit pcSeed1_055=true := by decide +kernel
#print axioms pcSeed1_055_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_056 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 5), (qq (22) 105), (qq (-1) 10), (qq (21) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (220) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_056Palette : List KBranch := pcRawSeed1_056.law.palette 0
abbrev pcSeed1_056 : OrbitSeed := pcRawSeed1_056.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_056_ok : seedOK (pcHead 1) pcSeed1_056Palette 1 pcSeedLimit pcSeed1_056=true := by decide +kernel
#print axioms pcSeed1_056_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_057 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 15), (qq (22) 325), (qq (-1) 10), (qq (67) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1980) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_057Palette : List KBranch := pcRawSeed1_057.law.palette 0
abbrev pcSeed1_057 : OrbitSeed := pcRawSeed1_057.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_057_ok : seedOK (pcHead 1) pcSeed1_057Palette 1 pcSeedLimit pcSeed1_057=true := by decide +kernel
#print axioms pcSeed1_057_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_058 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (22) 105), (qq (11) 50), (qq (21) 10), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2205) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed1_058Palette : List KBranch := pcRawSeed1_058.law.palette 0
abbrev pcSeed1_058 : OrbitSeed := pcRawSeed1_058.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_058_ok : seedOK (pcHead 1) pcSeed1_058Palette 1 pcSeedLimit pcSeed1_058=true := by decide +kernel
#print axioms pcSeed1_058_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_059 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 50), (qq (8) 35), (qq (43) 10), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2000) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_059Palette : List KBranch := pcRawSeed1_059.law.palette 0
abbrev pcSeed1_059 : OrbitSeed := pcRawSeed1_059.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_059_ok : seedOK (pcHead 1) pcSeed1_059Palette 1 pcSeedLimit pcSeed1_059=true := by decide +kernel
#print axioms pcSeed1_059_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_060 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 160), (qq (8) 115), (qq (43) 10), (qq (-31) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20480) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_060Palette : List KBranch := pcRawSeed1_060.law.palette 0
abbrev pcSeed1_060 : OrbitSeed := pcRawSeed1_060.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_060_ok : seedOK (pcHead 1) pcSeed1_060Palette 1 pcSeedLimit pcSeed1_060=true := by decide +kernel
#print axioms pcSeed1_060_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_061 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (8) 35), (qq (4) 17), (qq (31) 10), (qq (-19) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2695) 16)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_061Palette : List KBranch := pcRawSeed1_061.law.palette 0
abbrev pcSeed1_061 : OrbitSeed := pcRawSeed1_061.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_061_ok : seedOK (pcHead 1) pcSeed1_061Palette 1 pcSeedLimit pcSeed1_061=true := by decide +kernel
#print axioms pcSeed1_061_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_062 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (8) 115), (qq (4) 57), (qq (31) 10), (qq (-55) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (29095) 16)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_062Palette : List KBranch := pcRawSeed1_062.law.palette 0
abbrev pcSeed1_062 : OrbitSeed := pcRawSeed1_062.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_062_ok : seedOK (pcHead 1) pcSeed1_062Palette 1 pcSeedLimit pcSeed1_062=true := by decide +kernel
#print axioms pcSeed1_062_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_063 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (4) 17), (qq (6) 25), (qq (21) 10), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3179) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_063Palette : List KBranch := pcRawSeed1_063.law.palette 0
abbrev pcSeed1_063 : OrbitSeed := pcRawSeed1_063.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_063_ok : seedOK (pcHead 1) pcSeed1_063Palette 1 pcSeedLimit pcSeed1_063=true := by decide +kernel
#print axioms pcSeed1_063_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_064 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 57), (qq (6) 85), (qq (21) 10), (qq (1) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (35739) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_064Palette : List KBranch := pcRawSeed1_064.law.palette 0
abbrev pcSeed1_064 : OrbitSeed := pcRawSeed1_064.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_064_ok : seedOK (pcHead 1) pcSeed1_064Palette 1 pcSeedLimit pcSeed1_064=true := by decide +kernel
#print axioms pcSeed1_064_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_065 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (6) 25), (qq (1) 4), (qq (9) 10), (qq (9) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1375) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_065Palette : List KBranch := pcRawSeed1_065.law.palette 0
abbrev pcSeed1_065 : OrbitSeed := pcRawSeed1_065.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_065_ok : seedOK (pcHead 1) pcSeed1_065Palette 1 pcSeedLimit pcSeed1_065=true := by decide +kernel
#print axioms pcSeed1_065_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_066 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (6) 85), (qq (1) 14), (qq (9) 10), (qq (35) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15895) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_066Palette : List KBranch := pcRawSeed1_066.law.palette 0
abbrev pcSeed1_066 : OrbitSeed := pcRawSeed1_066.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_066_ok : seedOK (pcHead 1) pcSeed1_066Palette 1 pcSeedLimit pcSeed1_066=true := by decide +kernel
#print axioms pcSeed1_066_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_067 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 4), (qq (22) 85), (qq (-1) 10), (qq (17) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (704) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_067Palette : List KBranch := pcRawSeed1_067.law.palette 0
abbrev pcSeed1_067 : OrbitSeed := pcRawSeed1_067.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_067_ok : seedOK (pcHead 1) pcSeed1_067Palette 1 pcSeedLimit pcSeed1_067=true := by decide +kernel
#print axioms pcSeed1_067_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_068 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 14), (qq (22) 305), (qq (-1) 10), (qq (63) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8624) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_068Palette : List KBranch := pcRawSeed1_068.law.palette 0
abbrev pcSeed1_068 : OrbitSeed := pcRawSeed1_068.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_068_ok : seedOK (pcHead 1) pcSeed1_068Palette 1 pcSeedLimit pcSeed1_068=true := by decide +kernel
#print axioms pcSeed1_068_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_069 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (22) 85), (qq (11) 40), (qq (21) 10), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1445) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed1_069Palette : List KBranch := pcRawSeed1_069.law.palette 0
abbrev pcSeed1_069 : OrbitSeed := pcRawSeed1_069.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_069_ok : seedOK (pcHead 1) pcSeed1_069Palette 1 pcSeedLimit pcSeed1_069=true := by decide +kernel
#print axioms pcSeed1_069_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_070 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 40), (qq (24) 85), (qq (43) 10), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1280) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_070Palette : List KBranch := pcRawSeed1_070.law.palette 0
abbrev pcSeed1_070 : OrbitSeed := pcRawSeed1_070.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_070_ok : seedOK (pcHead 1) pcSeed1_070Palette 1 pcSeedLimit pcSeed1_070=true := by decide +kernel
#print axioms pcSeed1_070_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_071 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 150), (qq (24) 325), (qq (43) 10), (qq (-29) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (18000) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_071Palette : List KBranch := pcRawSeed1_071.law.palette 0
abbrev pcSeed1_071 : OrbitSeed := pcRawSeed1_071.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_071_ok : seedOK (pcHead 1) pcSeed1_071Palette 1 pcSeedLimit pcSeed1_071=true := by decide +kernel
#print axioms pcSeed1_071_ok


def pcRawSeeds1O002 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_048, pcRawSeed1_049, pcRawSeed1_050, pcRawSeed1_051, pcRawSeed1_052, pcRawSeed1_053, pcRawSeed1_054, pcRawSeed1_055, pcRawSeed1_056, pcRawSeed1_057, pcRawSeed1_058, pcRawSeed1_059, pcRawSeed1_060, pcRawSeed1_061, pcRawSeed1_062, pcRawSeed1_063, pcRawSeed1_064, pcRawSeed1_065, pcRawSeed1_066, pcRawSeed1_067, pcRawSeed1_068, pcRawSeed1_069, pcRawSeed1_070, pcRawSeed1_071]
theorem pcRawSeeds1O002_ok : ∀ S∈pcRawSeeds1O002,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 10 1 10000)=true := by
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
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
