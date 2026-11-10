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
def pcRawSeed2_048 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (1) 5), (qq (11) 54), (qq (4) 3), (qq (19) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2500) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_048Palette : List KBranch := pcRawSeed2_048.law.palette 0
abbrev pcSeed2_048 : OrbitSeed := pcRawSeed2_048.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_048_ok : seedOK (pcHead 1) pcSeed2_048Palette 2 pcSeedLimit pcSeed2_048=true := by decide +kernel
#print axioms pcSeed2_048_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_049 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 14), (qq (11) 153), (qq (4) 3), (qq (59) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19600) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_049Palette : List KBranch := pcRawSeed2_049.law.palette 0
abbrev pcSeed2_049 : OrbitSeed := pcRawSeed2_049.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_049_ok : seedOK (pcHead 1) pcSeed2_049Palette 2 pcSeedLimit pcSeed2_049=true := by decide +kernel
#print axioms pcSeed2_049_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_050 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (11) 54), (qq (50) 243), (qq (1) 9), (qq (49) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (32400) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_050Palette : List KBranch := pcRawSeed2_050.law.palette 0
abbrev pcSeed2_050 : OrbitSeed := pcRawSeed2_050.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_050_ok : seedOK (pcHead 1) pcSeed2_050Palette 2 pcSeedLimit pcSeed2_050=true := by decide +kernel
#print axioms pcSeed2_050_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_051 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 153), (qq (50) 693), (qq (1) 9), (qq (144) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (260100) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_051Palette : List KBranch := pcRawSeed2_051.law.palette 0
abbrev pcSeed2_051 : OrbitSeed := pcRawSeed2_051.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_051_ok : seedOK (pcHead 1) pcSeed2_051Palette 2 pcSeedLimit pcSeed2_051=true := by decide +kernel
#print axioms pcSeed2_051_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_052 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (50) 243), (qq (2) 9), (qq (7) 3), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6561) 25)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed2_052Palette : List KBranch := pcRawSeed2_052.law.palette 0
abbrev pcSeed2_052 : OrbitSeed := pcRawSeed2_052.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_052_ok : seedOK (pcHead 1) pcSeed2_052Palette 2 pcSeedLimit pcSeed2_052=true := by decide +kernel
#print axioms pcSeed2_052_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_053 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (2) 9), (qq (55) 243), (qq (13) 3), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (225) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_053Palette : List KBranch := pcRawSeed2_053.law.palette 0
abbrev pcSeed2_053 : OrbitSeed := pcRawSeed2_053.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_053_ok : seedOK (pcHead 1) pcSeed2_053Palette 2 pcSeedLimit pcSeed2_053=true := by decide +kernel
#print axioms pcSeed2_053_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_054 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (2) 27), (qq (55) 738), (qq (13) 3), (qq (-29) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2025) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_054Palette : List KBranch := pcRawSeed2_054.law.palette 0
abbrev pcSeed2_054 : OrbitSeed := pcRawSeed2_054.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_054_ok : seedOK (pcHead 1) pcSeed2_054Palette 2 pcSeedLimit pcSeed2_054=true := by decide +kernel
#print axioms pcSeed2_054_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_055 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (55) 243), (qq (5) 22), (qq (28) 9), (qq (-23) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (486) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_055Palette : List KBranch := pcRawSeed2_055.law.palette 0
abbrev pcSeed2_055 : OrbitSeed := pcRawSeed2_055.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_055_ok : seedOK (pcHead 1) pcSeed2_055Palette 2 pcSeedLimit pcSeed2_055=true := by decide +kernel
#print axioms pcSeed2_055_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_056 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 738), (qq (5) 67), (qq (28) 9), (qq (-63) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (242064) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_056Palette : List KBranch := pcRawSeed2_056.law.palette 0
abbrev pcSeed2_056 : OrbitSeed := pcRawSeed2_056.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_056_ok : seedOK (pcHead 1) pcSeed2_056Palette 2 pcSeedLimit pcSeed2_056=true := by decide +kernel
#print axioms pcSeed2_056_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_057 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (5) 22), (qq (11) 45), (qq (19) 9), (qq (-1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (396) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_057Palette : List KBranch := pcRawSeed2_057.law.palette 0
abbrev pcSeed2_057 : OrbitSeed := pcRawSeed2_057.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_057_ok : seedOK (pcHead 1) pcSeed2_057Palette 2 pcSeedLimit pcSeed2_057=true := by decide +kernel
#print axioms pcSeed2_057_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_058 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 67), (qq (11) 144), (qq (19) 9), (qq (4) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17956) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_058Palette : List KBranch := pcRawSeed2_058.law.palette 0
abbrev pcSeed2_058 : OrbitSeed := pcRawSeed2_058.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_058_ok : seedOK (pcHead 1) pcSeed2_058Palette 2 pcSeedLimit pcSeed2_058=true := by decide +kernel
#print axioms pcSeed2_058_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_059 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 45), (qq (1) 4), (qq (8) 9), (qq (24) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (22500) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_059Palette : List KBranch := pcRawSeed2_059.law.palette 0
abbrev pcSeed2_059 : OrbitSeed := pcRawSeed2_059.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_059_ok : seedOK (pcHead 1) pcSeed2_059Palette 2 pcSeedLimit pcSeed2_059=true := by decide +kernel
#print axioms pcSeed2_059_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_060 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 144), (qq (1) 13), (qq (8) 9), (qq (84) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (230400) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_060Palette : List KBranch := pcRawSeed2_060.law.palette 0
abbrev pcSeed2_060 : OrbitSeed := pcRawSeed2_060.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_060_ok : seedOK (pcHead 1) pcSeed2_060Palette 2 pcSeedLimit pcSeed2_060=true := by decide +kernel
#print axioms pcSeed2_060_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_061 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 4), (qq (25) 99), (qq (-1) 9), (qq (44) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1600) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_061Palette : List KBranch := pcRawSeed2_061.law.palette 0
abbrev pcSeed2_061 : OrbitSeed := pcRawSeed2_061.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_061_ok : seedOK (pcHead 1) pcSeed2_061Palette 2 pcSeedLimit pcSeed2_061=true := by decide +kernel
#print axioms pcSeed2_061_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_062 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 13), (qq (25) 324), (qq (-1) 9), (qq (149) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16900) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_062Palette : List KBranch := pcRawSeed2_062.law.palette 0
abbrev pcSeed2_062 : OrbitSeed := pcRawSeed2_062.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_062_ok : seedOK (pcHead 1) pcSeed2_062Palette 2 pcSeedLimit pcSeed2_062=true := by decide +kernel
#print axioms pcSeed2_062_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_063 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (25) 99), (qq (5) 18), (qq (19) 9), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4356) 25)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed2_063Palette : List KBranch := pcRawSeed2_063.law.palette 0
abbrev pcSeed2_063 : OrbitSeed := pcRawSeed2_063.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_063_ok : seedOK (pcHead 1) pcSeed2_063Palette 2 pcSeedLimit pcSeed2_063=true := by decide +kernel
#print axioms pcSeed2_063_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_064 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (5) 18), (qq (5) 17), (qq (29) 9), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (144) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_064Palette : List KBranch := pcRawSeed2_064.law.palette 0
abbrev pcSeed2_064 : OrbitSeed := pcRawSeed2_064.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_064_ok : seedOK (pcHead 1) pcSeed2_064Palette 2 pcSeedLimit pcSeed2_064=true := by decide +kernel
#print axioms pcSeed2_064_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_065 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 63), (qq (5) 62), (qq (29) 9), (qq (-13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1764) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_065Palette : List KBranch := pcRawSeed2_065.law.palette 0
abbrev pcSeed2_065 : OrbitSeed := pcRawSeed2_065.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_065_ok : seedOK (pcHead 1) pcSeed2_065Palette 2 pcSeedLimit pcSeed2_065=true := by decide +kernel
#print axioms pcSeed2_065_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_066 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (5) 17), (qq (11) 36), (qq (20) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1156) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_066Palette : List KBranch := pcRawSeed2_066.law.palette 0
abbrev pcSeed2_066 : OrbitSeed := pcRawSeed2_066.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_066_ok : seedOK (pcHead 1) pcSeed2_066Palette 2 pcSeedLimit pcSeed2_066=true := by decide +kernel
#print axioms pcSeed2_066_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_067 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 62), (qq (11) 135), (qq (20) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15376) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_067Palette : List KBranch := pcRawSeed2_067.law.palette 0
abbrev pcSeed2_067 : OrbitSeed := pcRawSeed2_067.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_067_ok : seedOK (pcHead 1) pcSeed2_067Palette 2 pcSeedLimit pcSeed2_067=true := by decide +kernel
#print axioms pcSeed2_067_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_068 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (11) 36), (qq (50) 153), (qq (1) 1), (qq (17) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14400) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_068Palette : List KBranch := pcRawSeed2_068.law.palette 0
abbrev pcSeed2_068 : OrbitSeed := pcRawSeed2_068.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_068_ok : seedOK (pcHead 1) pcSeed2_068Palette 2 pcSeedLimit pcSeed2_068=true := by decide +kernel
#print axioms pcSeed2_068_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_069 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 135), (qq (50) 603), (qq (1) 1), (qq (72) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (202500) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_069Palette : List KBranch := pcRawSeed2_069.law.palette 0
abbrev pcSeed2_069 : OrbitSeed := pcRawSeed2_069.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_069_ok : seedOK (pcHead 1) pcSeed2_069Palette 2 pcSeedLimit pcSeed2_069=true := by decide +kernel
#print axioms pcSeed2_069_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_070 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (50) 153), (qq (1) 3), (qq (29) 9), (qq (-17) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2601) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_070Palette : List KBranch := pcRawSeed2_070.law.palette 0
abbrev pcSeed2_070 : OrbitSeed := pcRawSeed2_070.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_070_ok : seedOK (pcHead 1) pcSeed2_070Palette 2 pcSeedLimit pcSeed2_070=true := by decide +kernel
#print axioms pcSeed2_070_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_071 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (50) 603), (qq (1) 12), (qq (29) 9), (qq (-62) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (40401) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_071Palette : List KBranch := pcRawSeed2_071.law.palette 0
abbrev pcSeed2_071 : OrbitSeed := pcRawSeed2_071.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_071_ok : seedOK (pcHead 1) pcSeed2_071Palette 2 pcSeedLimit pcSeed2_071=true := by decide +kernel
#print axioms pcSeed2_071_ok


def pcRawSeeds2O002 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_048, pcRawSeed2_049, pcRawSeed2_050, pcRawSeed2_051, pcRawSeed2_052, pcRawSeed2_053, pcRawSeed2_054, pcRawSeed2_055, pcRawSeed2_056, pcRawSeed2_057, pcRawSeed2_058, pcRawSeed2_059, pcRawSeed2_060, pcRawSeed2_061, pcRawSeed2_062, pcRawSeed2_063, pcRawSeed2_064, pcRawSeed2_065, pcRawSeed2_066, pcRawSeed2_067, pcRawSeed2_068, pcRawSeed2_069, pcRawSeed2_070, pcRawSeed2_071]
theorem pcRawSeeds2O002_ok : ∀ S∈pcRawSeeds2O002,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000)=true := by
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
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
