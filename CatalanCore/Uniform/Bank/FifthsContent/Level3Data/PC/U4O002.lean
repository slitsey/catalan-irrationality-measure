module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_048 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 14), (qq (11) 153), (qq (32) 9), (qq (-98) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19600) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_048Palette : List KBranch := pcRawSeed4_048.law.palette 0
abbrev pcSeed4_048 : OrbitSeed := pcRawSeed4_048.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_048_ok : seedOK (pcHead 1) pcSeed4_048Palette 4 pcSeedLimit pcSeed4_048=true := by decide +kernel
#print axioms pcSeed4_048_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_049 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (11) 54), (qq (5) 24), (qq (7) 3), (qq (-8) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (32400) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_049Palette : List KBranch := pcRawSeed4_049.law.palette 0
abbrev pcSeed4_049 : OrbitSeed := pcRawSeed4_049.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_049_ok : seedOK (pcHead 1) pcSeed4_049Palette 4 pcSeedLimit pcSeed4_049=true := by decide +kernel
#print axioms pcSeed4_049_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_050 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 153), (qq (5) 69), (qq (7) 3), (qq (-13) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (260100) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_050Palette : List KBranch := pcRawSeed4_050.law.palette 0
abbrev pcSeed4_050 : OrbitSeed := pcRawSeed4_050.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_050_ok : seedOK (pcHead 1) pcSeed4_050Palette 4 pcSeedLimit pcSeed4_050=true := by decide +kernel
#print axioms pcSeed4_050_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_051 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (5) 24), (qq (55) 261), (qq (4) 3), (qq (16) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (256) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_051Palette : List KBranch := pcRawSeed4_051.law.palette 0
abbrev pcSeed4_051 : OrbitSeed := pcRawSeed4_051.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_051_ok : seedOK (pcHead 1) pcSeed4_051Palette 4 pcSeedLimit pcSeed4_051=true := by decide +kernel
#print axioms pcSeed4_051_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_052 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 69), (qq (55) 756), (qq (4) 3), (qq (56) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2116) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_052Palette : List KBranch := pcRawSeed4_052.law.palette 0
abbrev pcSeed4_052 : OrbitSeed := pcRawSeed4_052.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_052_ok : seedOK (pcHead 1) pcSeed4_052Palette 4 pcSeedLimit pcSeed4_052=true := by decide +kernel
#print axioms pcSeed4_052_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_053 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩, ⟨1,by decide +kernel⟩]
  base := (⟨(qq (55) 261), (qq (2) 9), (qq (1) 9), (qq (9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 87), (qq (2) 1)⟩], (qq (30276) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_053Palette : List KBranch := pcRawSeed4_053.law.palette 0
abbrev pcSeed4_053 : OrbitSeed := pcRawSeed4_053.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_053_ok : seedOK (pcHead 1) pcSeed4_053Palette 4 pcSeedLimit pcSeed4_053=true := by decide +kernel
#print axioms pcSeed4_053_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_054 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 756), (qq (2) 27), (qq (1) 9), (qq (28) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (254016) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_054Palette : List KBranch := pcRawSeed4_054.law.palette 0
abbrev pcSeed4_054 : OrbitSeed := pcRawSeed4_054.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_054_ok : seedOK (pcHead 1) pcSeed4_054Palette 4 pcSeedLimit pcSeed4_054=true := by decide +kernel
#print axioms pcSeed4_054_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_055 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (2) 9), (qq (25) 108), (qq (19) 9), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (225) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed4_055Palette : List KBranch := pcRawSeed4_055.law.palette 0
abbrev pcSeed4_055 : OrbitSeed := pcRawSeed4_055.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_055_ok : seedOK (pcHead 1) pcSeed4_055Palette 4 pcSeedLimit pcSeed4_055=true := by decide +kernel
#print axioms pcSeed4_055_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_056 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (25) 108), (qq (11) 45), (qq (13) 3), (qq (-48) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (216) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_056Palette : List KBranch := pcRawSeed4_056.law.palette 0
abbrev pcSeed4_056 : OrbitSeed := pcRawSeed4_056.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_056_ok : seedOK (pcHead 1) pcSeed4_056Palette 4 pcSeedLimit pcSeed4_056=true := by decide +kernel
#print axioms pcSeed4_056_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_057 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (25) 333), (qq (11) 144), (qq (13) 3), (qq (-143) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (49284) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_057Palette : List KBranch := pcRawSeed4_057.law.palette 0
abbrev pcSeed4_057 : OrbitSeed := pcRawSeed4_057.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_057_ok : seedOK (pcHead 1) pcSeed4_057Palette 4 pcSeedLimit pcSeed4_057=true := by decide +kernel
#print axioms pcSeed4_057_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_058 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 45), (qq (1) 4), (qq (28) 9), (qq (-23) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (22500) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_058Palette : List KBranch := pcRawSeed4_058.law.palette 0
abbrev pcSeed4_058 : OrbitSeed := pcRawSeed4_058.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_058_ok : seedOK (pcHead 1) pcSeed4_058Palette 4 pcSeedLimit pcSeed4_058=true := by decide +kernel
#print axioms pcSeed4_058_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_059 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 144), (qq (1) 13), (qq (28) 9), (qq (-63) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (230400) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_059Palette : List KBranch := pcRawSeed4_059.law.palette 0
abbrev pcSeed4_059 : OrbitSeed := pcRawSeed4_059.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_059_ok : seedOK (pcHead 1) pcSeed4_059Palette 4 pcSeedLimit pcSeed4_059=true := by decide +kernel
#print axioms pcSeed4_059_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_060 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 4), (qq (55) 216), (qq (19) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1600) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_060Palette : List KBranch := pcRawSeed4_060.law.palette 0
abbrev pcSeed4_060 : OrbitSeed := pcRawSeed4_060.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_060_ok : seedOK (pcHead 1) pcSeed4_060Palette 4 pcSeedLimit pcSeed4_060=true := by decide +kernel
#print axioms pcSeed4_060_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_061 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 13), (qq (55) 711), (qq (19) 9), (qq (2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16900) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_061Palette : List KBranch := pcRawSeed4_061.law.palette 0
abbrev pcSeed4_061 : OrbitSeed := pcRawSeed4_061.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_061_ok : seedOK (pcHead 1) pcSeed4_061Palette 4 pcSeedLimit pcSeed4_061=true := by decide +kernel
#print axioms pcSeed4_061_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_062 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (55) 216), (qq (5) 19), (qq (8) 9), (qq (21) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20736) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_062Palette : List KBranch := pcRawSeed4_062.law.palette 0
abbrev pcSeed4_062 : OrbitSeed := pcRawSeed4_062.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_062_ok : seedOK (pcHead 1) pcSeed4_062Palette 4 pcSeedLimit pcSeed4_062=true := by decide +kernel
#print axioms pcSeed4_062_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_063 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 711), (qq (5) 64), (qq (8) 9), (qq (81) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (224676) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_063Palette : List KBranch := pcRawSeed4_063.law.palette 0
abbrev pcSeed4_063 : OrbitSeed := pcRawSeed4_063.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_063_ok : seedOK (pcHead 1) pcSeed4_063Palette 4 pcSeedLimit pcSeed4_063=true := by decide +kernel
#print axioms pcSeed4_063_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_064 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (5) 19), (qq (5) 18), (qq (-1) 9), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1444) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_064Palette : List KBranch := pcRawSeed4_064.law.palette 0
abbrev pcSeed4_064 : OrbitSeed := pcRawSeed4_064.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_064_ok : seedOK (pcHead 1) pcSeed4_064Palette 4 pcSeedLimit pcSeed4_064=true := by decide +kernel
#print axioms pcSeed4_064_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_065 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 64), (qq (5) 63), (qq (-1) 9), (qq (29) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16384) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_065Palette : List KBranch := pcRawSeed4_065.law.palette 0
abbrev pcSeed4_065 : OrbitSeed := pcRawSeed4_065.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_065_ok : seedOK (pcHead 1) pcSeed4_065Palette 4 pcSeedLimit pcSeed4_065=true := by decide +kernel
#print axioms pcSeed4_065_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_066 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (5) 18), (qq (50) 171), (qq (19) 9), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (144) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed4_066Palette : List KBranch := pcRawSeed4_066.law.palette 0
abbrev pcSeed4_066 : OrbitSeed := pcRawSeed4_066.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_066_ok : seedOK (pcHead 1) pcSeed4_066Palette 4 pcSeedLimit pcSeed4_066=true := by decide +kernel
#print axioms pcSeed4_066_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_067 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (50) 171), (qq (11) 36), (qq (13) 3), (qq (-38) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3249) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_067Palette : List KBranch := pcRawSeed4_067.law.palette 0
abbrev pcSeed4_067 : OrbitSeed := pcRawSeed4_067.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_067_ok : seedOK (pcHead 1) pcSeed4_067Palette 4 pcSeedLimit pcSeed4_067=true := by decide +kernel
#print axioms pcSeed4_067_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_068 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (50) 621), (qq (11) 135), (qq (13) 3), (qq (-133) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (42849) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_068Palette : List KBranch := pcRawSeed4_068.law.palette 0
abbrev pcSeed4_068 : OrbitSeed := pcRawSeed4_068.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_068_ok : seedOK (pcHead 1) pcSeed4_068Palette 4 pcSeedLimit pcSeed4_068=true := by decide +kernel
#print axioms pcSeed4_068_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_069 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 36), (qq (55) 171), (qq (28) 9), (qq (-18) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14400) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_069Palette : List KBranch := pcRawSeed4_069.law.palette 0
abbrev pcSeed4_069 : OrbitSeed := pcRawSeed4_069.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_069_ok : seedOK (pcHead 1) pcSeed4_069Palette 4 pcSeedLimit pcSeed4_069=true := by decide +kernel
#print axioms pcSeed4_069_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_070 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 135), (qq (55) 666), (qq (28) 9), (qq (-58) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (202500) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_070Palette : List KBranch := pcRawSeed4_070.law.palette 0
abbrev pcSeed4_070 : OrbitSeed := pcRawSeed4_070.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_070_ok : seedOK (pcHead 1) pcSeed4_070Palette 4 pcSeedLimit pcSeed4_070=true := by decide +kernel
#print axioms pcSeed4_070_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_071 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (55) 171), (qq (1) 3), (qq (17) 9), (qq (1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12996) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_071Palette : List KBranch := pcRawSeed4_071.law.palette 0
abbrev pcSeed4_071 : OrbitSeed := pcRawSeed4_071.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_071_ok : seedOK (pcHead 1) pcSeed4_071Palette 4 pcSeedLimit pcSeed4_071=true := by decide +kernel
#print axioms pcSeed4_071_ok


def pcRawSeeds4O002 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed4_048, pcRawSeed4_049, pcRawSeed4_050, pcRawSeed4_051, pcRawSeed4_052, pcRawSeed4_053, pcRawSeed4_054, pcRawSeed4_055, pcRawSeed4_056, pcRawSeed4_057, pcRawSeed4_058, pcRawSeed4_059, pcRawSeed4_060, pcRawSeed4_061, pcRawSeed4_062, pcRawSeed4_063, pcRawSeed4_064, pcRawSeed4_065, pcRawSeed4_066, pcRawSeed4_067, pcRawSeed4_068, pcRawSeed4_069, pcRawSeed4_070, pcRawSeed4_071]
theorem pcRawSeeds4O002_ok : ∀ S∈pcRawSeeds4O002,
    seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds4O002,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed4_048_ok
  · exact pcSeed4_049_ok
  · exact pcSeed4_050_ok
  · exact pcSeed4_051_ok
  · exact pcSeed4_052_ok
  · exact pcSeed4_053_ok
  · exact pcSeed4_054_ok
  · exact pcSeed4_055_ok
  · exact pcSeed4_056_ok
  · exact pcSeed4_057_ok
  · exact pcSeed4_058_ok
  · exact pcSeed4_059_ok
  · exact pcSeed4_060_ok
  · exact pcSeed4_061_ok
  · exact pcSeed4_062_ok
  · exact pcSeed4_063_ok
  · exact pcSeed4_064_ok
  · exact pcSeed4_065_ok
  · exact pcSeed4_066_ok
  · exact pcSeed4_067_ok
  · exact pcSeed4_068_ok
  · exact pcSeed4_069_ok
  · exact pcSeed4_070_ok
  · exact pcSeed4_071_ok
#print axioms pcRawSeeds4O002_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
