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
def pcRawSeed3_048 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (22) 135), (qq (1) 6), (qq (9) 2), (qq (-29) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3645) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_048Palette : List KBranch := pcRawSeed3_048.law.palette 0
abbrev pcSeed3_048 : OrbitSeed := pcRawSeed3_048.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_048_ok : seedOK (pcHead 1) pcSeed3_048Palette 3 pcSeedLimit pcSeed3_048=true := by decide +kernel
#print axioms pcSeed3_048_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_049 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (22) 355), (qq (1) 16), (qq (9) 2), (qq (-75) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (25205) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_049Palette : List KBranch := pcRawSeed3_049.law.palette 0
abbrev pcSeed3_049 : OrbitSeed := pcRawSeed3_049.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_049_ok : seedOK (pcHead 1) pcSeed3_049Palette 3 pcSeedLimit pcSeed3_049=true := by decide +kernel
#print axioms pcSeed3_049_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_050 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (1) 6), (qq (6) 35), (qq (7) 2), (qq (-17) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1584) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_050Palette : List KBranch := pcRawSeed3_050.law.palette 0
abbrev pcSeed3_050 : OrbitSeed := pcRawSeed3_050.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_050_ok : seedOK (pcHead 1) pcSeed3_050Palette 3 pcSeedLimit pcSeed3_050=true := by decide +kernel
#print axioms pcSeed3_050_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_051 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 16), (qq (6) 95), (qq (7) 2), (qq (-43) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11264) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_051Palette : List KBranch := pcRawSeed3_051.law.palette 0
abbrev pcSeed3_051 : OrbitSeed := pcRawSeed3_051.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_051_ok : seedOK (pcHead 1) pcSeed3_051Palette 3 pcSeedLimit pcSeed3_051=true := by decide +kernel
#print axioms pcSeed3_051_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_052 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (6) 35), (qq (4) 23), (qq (23) 10), (qq (-3) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2695) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_052Palette : List KBranch := pcRawSeed3_052.law.palette 0
abbrev pcSeed3_052 : OrbitSeed := pcRawSeed3_052.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_052_ok : seedOK (pcHead 1) pcSeed3_052Palette 3 pcSeedLimit pcSeed3_052=true := by decide +kernel
#print axioms pcSeed3_052_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_053 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (6) 95), (qq (4) 63), (qq (23) 10), (qq (-5) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19855) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_053Palette : List KBranch := pcRawSeed3_053.law.palette 0
abbrev pcSeed3_053 : OrbitSeed := pcRawSeed3_053.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_053_ok : seedOK (pcHead 1) pcSeed3_053Palette 3 pcSeedLimit pcSeed3_053=true := by decide +kernel
#print axioms pcSeed3_053_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_054 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (4) 23), (qq (8) 45), (qq (13) 10), (qq (17) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5819) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_054Palette : List KBranch := pcRawSeed3_054.law.palette 0
abbrev pcSeed3_054 : OrbitSeed := pcRawSeed3_054.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_054_ok : seedOK (pcHead 1) pcSeed3_054Palette 3 pcSeedLimit pcSeed3_054=true := by decide +kernel
#print axioms pcSeed3_054_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_055 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 63), (qq (8) 125), (qq (13) 10), (qq (53) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (43659) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_055Palette : List KBranch := pcRawSeed3_055.law.palette 0
abbrev pcSeed3_055 : OrbitSeed := pcRawSeed3_055.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_055_ok : seedOK (pcHead 1) pcSeed3_055Palette 3 pcSeedLimit pcSeed3_055=true := by decide +kernel
#print axioms pcSeed3_055_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_056 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨66,by decide +kernel⟩]
  base := (⟨(qq (8) 45), (qq (11) 60), (qq (1) 10), (qq (11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4455) 16)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_056Palette : List KBranch := pcRawSeed3_056.law.palette 0
abbrev pcSeed3_056 : OrbitSeed := pcRawSeed3_056.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_056_ok : seedOK (pcHead 1) pcSeed3_056Palette 3 pcSeedLimit pcSeed3_056=true := by decide +kernel
#print axioms pcSeed3_056_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_057 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (8) 125), (qq (11) 170), (qq (1) 10), (qq (32) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (34375) 16)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_057Palette : List KBranch := pcRawSeed3_057.law.palette 0
abbrev pcSeed3_057 : OrbitSeed := pcRawSeed3_057.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_057_ok : seedOK (pcHead 1) pcSeed3_057Palette 3 pcSeedLimit pcSeed3_057=true := by decide +kernel
#print axioms pcSeed3_057_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_058 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (11) 60), (qq (22) 115), (qq (23) 10), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2880) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed3_058Palette : List KBranch := pcRawSeed3_058.law.palette 0
abbrev pcSeed3_058 : OrbitSeed := pcRawSeed3_058.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_058_ok : seedOK (pcHead 1) pcSeed3_058Palette 3 pcSeedLimit pcSeed3_058=true := by decide +kernel
#print axioms pcSeed3_058_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_059 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (22) 335), (qq (1) 15), (qq (9) 2), (qq (-71) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (22445) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_059Palette : List KBranch := pcRawSeed3_059.law.palette 0
abbrev pcSeed3_059 : OrbitSeed := pcRawSeed3_059.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_059_ok : seedOK (pcHead 1) pcSeed3_059Palette 3 pcSeedLimit pcSeed3_059=true := by decide +kernel
#print axioms pcSeed3_059_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_060 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 5), (qq (24) 115), (qq (21) 10), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (220) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_060Palette : List KBranch := pcRawSeed3_060.law.palette 0
abbrev pcSeed3_060 : OrbitSeed := pcRawSeed3_060.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_060_ok : seedOK (pcHead 1) pcSeed3_060Palette 3 pcSeedLimit pcSeed3_060=true := by decide +kernel
#print axioms pcSeed3_060_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_061 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 15), (qq (24) 355), (qq (21) 10), (qq (1) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1980) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_061Palette : List KBranch := pcRawSeed3_061.law.palette 0
abbrev pcSeed3_061 : OrbitSeed := pcRawSeed3_061.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_061_ok : seedOK (pcHead 1) pcSeed3_061Palette 3 pcSeedLimit pcSeed3_061=true := by decide +kernel
#print axioms pcSeed3_061_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_062 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (24) 115), (qq (4) 19), (qq (9) 10), (qq (21) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (230) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_062Palette : List KBranch := pcRawSeed3_062.law.palette 0
abbrev pcSeed3_062 : OrbitSeed := pcRawSeed3_062.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_062_ok : seedOK (pcHead 1) pcSeed3_062Palette 3 pcSeedLimit pcSeed3_062=true := by decide +kernel
#print axioms pcSeed3_062_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_063 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (24) 355), (qq (4) 59), (qq (9) 10), (qq (73) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (277255) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_063Palette : List KBranch := pcRawSeed3_063.law.palette 0
abbrev pcSeed3_063 : OrbitSeed := pcRawSeed3_063.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_063_ok : seedOK (pcHead 1) pcSeed3_063Palette 3 pcSeedLimit pcSeed3_063=true := by decide +kernel
#print axioms pcSeed3_063_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_064 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (4) 19), (qq (11) 50), (qq (-1) 10), (qq (10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3971) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_064Palette : List KBranch := pcRawSeed3_064.law.palette 0
abbrev pcSeed3_064 : OrbitSeed := pcRawSeed3_064.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_064_ok : seedOK (pcHead 1) pcSeed3_064Palette 3 pcSeedLimit pcSeed3_064=true := by decide +kernel
#print axioms pcSeed3_064_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_065 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 59), (qq (11) 160), (qq (-1) 10), (qq (33) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (38291) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_065Palette : List KBranch := pcRawSeed3_065.law.palette 0
abbrev pcSeed3_065 : OrbitSeed := pcRawSeed3_065.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_065_ok : seedOK (pcHead 1) pcSeed3_065Palette 3 pcSeedLimit pcSeed3_065=true := by decide +kernel
#print axioms pcSeed3_065_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_066 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (11) 50), (qq (22) 95), (qq (21) 10), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2000) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed3_066Palette : List KBranch := pcRawSeed3_066.law.palette 0
abbrev pcSeed3_066 : OrbitSeed := pcRawSeed3_066.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_066_ok : seedOK (pcHead 1) pcSeed3_066Palette 3 pcSeedLimit pcSeed3_066=true := by decide +kernel
#print axioms pcSeed3_066_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_067 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (22) 95), (qq (6) 25), (qq (43) 10), (qq (-19) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1805) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_067Palette : List KBranch := pcRawSeed3_067.law.palette 0
abbrev pcSeed3_067 : OrbitSeed := pcRawSeed3_067.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_067_ok : seedOK (pcHead 1) pcSeed3_067Palette 3 pcSeedLimit pcSeed3_067=true := by decide +kernel
#print axioms pcSeed3_067_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_068 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (22) 315), (qq (6) 85), (qq (43) 10), (qq (-61) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19845) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_068Palette : List KBranch := pcRawSeed3_068.law.palette 0
abbrev pcSeed3_068 : OrbitSeed := pcRawSeed3_068.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_068_ok : seedOK (pcHead 1) pcSeed3_068Palette 3 pcSeedLimit pcSeed3_068=true := by decide +kernel
#print axioms pcSeed3_068_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_069 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (6) 25), (qq (1) 4), (qq (31) 10), (qq (-9) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1375) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_069Palette : List KBranch := pcRawSeed3_069.law.palette 0
abbrev pcSeed3_069 : OrbitSeed := pcRawSeed3_069.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_069_ok : seedOK (pcHead 1) pcSeed3_069Palette 3 pcSeedLimit pcSeed3_069=true := by decide +kernel
#print axioms pcSeed3_069_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_070 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (6) 85), (qq (1) 14), (qq (31) 10), (qq (-27) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15895) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_070Palette : List KBranch := pcRawSeed3_070.law.palette 0
abbrev pcSeed3_070 : OrbitSeed := pcRawSeed3_070.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_070_ok : seedOK (pcHead 1) pcSeed3_070Palette 3 pcSeedLimit pcSeed3_070=true := by decide +kernel
#print axioms pcSeed3_070_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_071 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 4), (qq (24) 95), (qq (21) 10), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (704) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_071Palette : List KBranch := pcRawSeed3_071.law.palette 0
abbrev pcSeed3_071 : OrbitSeed := pcRawSeed3_071.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_071_ok : seedOK (pcHead 1) pcSeed3_071Palette 3 pcSeedLimit pcSeed3_071=true := by decide +kernel
#print axioms pcSeed3_071_ok


def pcRawSeeds3O002 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed3_048, pcRawSeed3_049, pcRawSeed3_050, pcRawSeed3_051, pcRawSeed3_052, pcRawSeed3_053, pcRawSeed3_054, pcRawSeed3_055, pcRawSeed3_056, pcRawSeed3_057, pcRawSeed3_058, pcRawSeed3_059, pcRawSeed3_060, pcRawSeed3_061, pcRawSeed3_062, pcRawSeed3_063, pcRawSeed3_064, pcRawSeed3_065, pcRawSeed3_066, pcRawSeed3_067, pcRawSeed3_068, pcRawSeed3_069, pcRawSeed3_070, pcRawSeed3_071]
theorem pcRawSeeds3O002_ok : ∀ S∈pcRawSeeds3O002,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 10 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3O002,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed3_048_ok
  · exact pcSeed3_049_ok
  · exact pcSeed3_050_ok
  · exact pcSeed3_051_ok
  · exact pcSeed3_052_ok
  · exact pcSeed3_053_ok
  · exact pcSeed3_054_ok
  · exact pcSeed3_055_ok
  · exact pcSeed3_056_ok
  · exact pcSeed3_057_ok
  · exact pcSeed3_058_ok
  · exact pcSeed3_059_ok
  · exact pcSeed3_060_ok
  · exact pcSeed3_061_ok
  · exact pcSeed3_062_ok
  · exact pcSeed3_063_ok
  · exact pcSeed3_064_ok
  · exact pcSeed3_065_ok
  · exact pcSeed3_066_ok
  · exact pcSeed3_067_ok
  · exact pcSeed3_068_ok
  · exact pcSeed3_069_ok
  · exact pcSeed3_070_ok
  · exact pcSeed3_071_ok
#print axioms pcRawSeeds3O002_ok
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
