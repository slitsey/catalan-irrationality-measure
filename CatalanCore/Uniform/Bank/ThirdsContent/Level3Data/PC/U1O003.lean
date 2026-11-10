module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_072 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (23) 40), (qq (13) 20), (qq (33) 10), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (480) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_072Palette : List KBranch := pcRawSeed1_072.law.palette 0
abbrev pcSeed1_072 : OrbitSeed := pcRawSeed1_072.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_072_ok : seedOK (pcHead 1) pcSeed1_072Palette 1 pcSeedLimit pcSeed1_072=true := by decide +kernel
#print axioms pcSeed1_072_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_073 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (23) 500), (qq (13) 280), (qq (33) 10), (qq (-22) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (75000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_073Palette : List KBranch := pcRawSeed1_073.law.palette 0
abbrev pcSeed1_073 : OrbitSeed := pcRawSeed1_073.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_073_ok : seedOK (pcHead 1) pcSeed1_073Palette 1 pcSeedLimit pcSeed1_073=true := by decide +kernel
#print axioms pcSeed1_073_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_074 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (13) 20), (qq (3) 4), (qq (2) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2760) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_074Palette : List KBranch := pcRawSeed1_074.law.palette 0
abbrev pcSeed1_074 : OrbitSeed := pcRawSeed1_074.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_074_ok : seedOK (pcHead 1) pcSeed1_074Palette 1 pcSeedLimit pcSeed1_074=true := by decide +kernel
#print axioms pcSeed1_074_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_075 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (13) 280), (qq (3) 64), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (540960) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_075Palette : List KBranch := pcRawSeed1_075.law.palette 0
abbrev pcSeed1_075 : OrbitSeed := pcRawSeed1_075.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_075_ok : seedOK (pcHead 1) pcSeed1_075Palette 1 pcSeedLimit pcSeed1_075=true := by decide +kernel
#print axioms pcSeed1_075_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_076 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (3) 4), (qq (69) 80), (qq (1) 1), (qq (4) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (184) 15)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_076Palette : List KBranch := pcRawSeed1_076.law.palette 0
abbrev pcSeed1_076 : OrbitSeed := pcRawSeed1_076.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_076_ok : seedOK (pcHead 1) pcSeed1_076Palette 1 pcSeedLimit pcSeed1_076=true := by decide +kernel
#print axioms pcSeed1_076_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_077 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (3) 64), (qq (69) 1460), (qq (1) 1), (qq (82) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (47104) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_077Palette : List KBranch := pcRawSeed1_077.law.palette 0
abbrev pcSeed1_077 : OrbitSeed := pcRawSeed1_077.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_077_ok : seedOK (pcHead 1) pcSeed1_077Palette 1 pcSeedLimit pcSeed1_077=true := by decide +kernel
#print axioms pcSeed1_077_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_078 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (69) 1460), (qq (39) 820), (qq (33) 10), (qq (-64) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (213160) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_078Palette : List KBranch := pcRawSeed1_078.law.palette 0
abbrev pcSeed1_078 : OrbitSeed := pcRawSeed1_078.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_078_ok : seedOK (pcHead 1) pcSeed1_078Palette 1 pcSeedLimit pcSeed1_078=true := by decide +kernel
#print axioms pcSeed1_078_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_079 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (39) 820), (qq (1) 21), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1546520) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_079Palette : List KBranch := pcRawSeed1_079.law.palette 0
abbrev pcSeed1_079 : OrbitSeed := pcRawSeed1_079.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_079_ok : seedOK (pcHead 1) pcSeed1_079Palette 1 pcSeedLimit pcSeed1_079=true := by decide +kernel
#print axioms pcSeed1_079_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_080 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (1) 21), (qq (23) 480), (qq (1) 1), (qq (27) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (30429) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_080Palette : List KBranch := pcRawSeed1_080.law.palette 0
abbrev pcSeed1_080 : OrbitSeed := pcRawSeed1_080.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_080_ok : seedOK (pcHead 1) pcSeed1_080Palette 1 pcSeedLimit pcSeed1_080=true := by decide +kernel
#print axioms pcSeed1_080_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_081 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (23) 480), (qq (13) 270), (qq (33) 10), (qq (-21) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (69120) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_081Palette : List KBranch := pcRawSeed1_081.law.palette 0
abbrev pcSeed1_081 : OrbitSeed := pcRawSeed1_081.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_081_ok : seedOK (pcHead 1) pcSeed1_081Palette 1 pcSeedLimit pcSeed1_081=true := by decide +kernel
#print axioms pcSeed1_081_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_082 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (13) 270), (qq (3) 61), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (503010) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_082Palette : List KBranch := pcRawSeed1_082.law.palette 0
abbrev pcSeed1_082 : OrbitSeed := pcRawSeed1_082.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_082_ok : seedOK (pcHead 1) pcSeed1_082Palette 1 pcSeedLimit pcSeed1_082=true := by decide +kernel
#print axioms pcSeed1_082_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_083 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (3) 61), (qq (69) 1400), (qq (1) 1), (qq (79) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (85583) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_083Palette : List KBranch := pcRawSeed1_083.law.palette 0
abbrev pcSeed1_083 : OrbitSeed := pcRawSeed1_083.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_083_ok : seedOK (pcHead 1) pcSeed1_083Palette 1 pcSeedLimit pcSeed1_083=true := by decide +kernel
#print axioms pcSeed1_083_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_084 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (69) 1400), (qq (39) 790), (qq (33) 10), (qq (-61) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (196000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_084Palette : List KBranch := pcRawSeed1_084.law.palette 0
abbrev pcSeed1_084 : OrbitSeed := pcRawSeed1_084.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_084_ok : seedOK (pcHead 1) pcSeed1_084Palette 1 pcSeedLimit pcSeed1_084=true := by decide +kernel
#print axioms pcSeed1_084_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_085 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (39) 790), (qq (1) 20), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1435430) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_085Palette : List KBranch := pcRawSeed1_085.law.palette 0
abbrev pcSeed1_085 : OrbitSeed := pcRawSeed1_085.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_085_ok : seedOK (pcHead 1) pcSeed1_085Palette 1 pcSeedLimit pcSeed1_085=true := by decide +kernel
#print axioms pcSeed1_085_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_086 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (1) 20), (qq (39) 760), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2760) 1)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_086Palette : List KBranch := pcRawSeed1_086.law.palette 0
abbrev pcSeed1_086 : OrbitSeed := pcRawSeed1_086.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_086_ok : seedOK (pcHead 1) pcSeed1_086Palette 1 pcSeedLimit pcSeed1_086=true := by decide +kernel
#print axioms pcSeed1_086_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_087 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (39) 760), (qq (69) 1340), (qq (13) 10), (qq (58) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1328480) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_087Palette : List KBranch := pcRawSeed1_087.law.palette 0
abbrev pcSeed1_087 : OrbitSeed := pcRawSeed1_087.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_087_ok : seedOK (pcHead 1) pcSeed1_087Palette 1 pcSeedLimit pcSeed1_087=true := by decide +kernel
#print axioms pcSeed1_087_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_088 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (69) 1340), (qq (3) 58), (qq (18) 5), (qq (-76) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (179560) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_088Palette : List KBranch := pcRawSeed1_088.law.palette 0
abbrev pcSeed1_088 : OrbitSeed := pcRawSeed1_088.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_088_ok : seedOK (pcHead 1) pcSeed1_088Palette 1 pcSeedLimit pcSeed1_088=true := by decide +kernel
#print axioms pcSeed1_088_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_089 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (3) 58), (qq (13) 250), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (38686) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_089Palette : List KBranch := pcRawSeed1_089.law.palette 0
abbrev pcSeed1_089 : OrbitSeed := pcRawSeed1_089.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_089_ok : seedOK (pcHead 1) pcSeed1_089Palette 1 pcSeedLimit pcSeed1_089=true := by decide +kernel
#print axioms pcSeed1_089_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_090 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (13) 250), (qq (23) 440), (qq (13) 10), (qq (19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (431250) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_090Palette : List KBranch := pcRawSeed1_090.law.palette 0
abbrev pcSeed1_090 : OrbitSeed := pcRawSeed1_090.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_090_ok : seedOK (pcHead 1) pcSeed1_090Palette 1 pcSeedLimit pcSeed1_090=true := by decide +kernel
#print axioms pcSeed1_090_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_091 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 440), (qq (1) 19), (qq (18) 5), (qq (-25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (58080) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_091Palette : List KBranch := pcRawSeed1_091.law.palette 0
abbrev pcSeed1_091 : OrbitSeed := pcRawSeed1_091.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_091_ok : seedOK (pcHead 1) pcSeed1_091Palette 1 pcSeedLimit pcSeed1_091=true := by decide +kernel
#print axioms pcSeed1_091_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_092 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (1) 19), (qq (39) 730), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24909) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_092Palette : List KBranch := pcRawSeed1_092.law.palette 0
abbrev pcSeed1_092 : OrbitSeed := pcRawSeed1_092.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_092_ok : seedOK (pcHead 1) pcSeed1_092Palette 1 pcSeedLimit pcSeed1_092=true := by decide +kernel
#print axioms pcSeed1_092_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_093 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (39) 730), (qq (69) 1280), (qq (13) 10), (qq (55) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1225670) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_093Palette : List KBranch := pcRawSeed1_093.law.palette 0
abbrev pcSeed1_093 : OrbitSeed := pcRawSeed1_093.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_093_ok : seedOK (pcHead 1) pcSeed1_093Palette 1 pcSeedLimit pcSeed1_093=true := by decide +kernel
#print axioms pcSeed1_093_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_094 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (69) 1280), (qq (13) 240), (qq (18) 5), (qq (-73) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (163840) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_094Palette : List KBranch := pcRawSeed1_094.law.palette 0
abbrev pcSeed1_094 : OrbitSeed := pcRawSeed1_094.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_094_ok : seedOK (pcHead 1) pcSeed1_094Palette 1 pcSeedLimit pcSeed1_094=true := by decide +kernel
#print axioms pcSeed1_094_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_095 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (13) 240), (qq (3) 55), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (397440) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_095Palette : List KBranch := pcRawSeed1_095.law.palette 0
abbrev pcSeed1_095 : OrbitSeed := pcRawSeed1_095.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_095_ok : seedOK (pcHead 1) pcSeed1_095Palette 1 pcSeedLimit pcSeed1_095=true := by decide +kernel
#print axioms pcSeed1_095_ok


def pcRawSeeds1O003 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_072, pcRawSeed1_073, pcRawSeed1_074, pcRawSeed1_075, pcRawSeed1_076, pcRawSeed1_077, pcRawSeed1_078, pcRawSeed1_079, pcRawSeed1_080, pcRawSeed1_081, pcRawSeed1_082, pcRawSeed1_083, pcRawSeed1_084, pcRawSeed1_085, pcRawSeed1_086, pcRawSeed1_087, pcRawSeed1_088, pcRawSeed1_089, pcRawSeed1_090, pcRawSeed1_091, pcRawSeed1_092, pcRawSeed1_093, pcRawSeed1_094, pcRawSeed1_095]
theorem pcRawSeeds1O003_ok : ∀ S∈pcRawSeeds1O003,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O003,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_072_ok
  · exact pcSeed1_073_ok
  · exact pcSeed1_074_ok
  · exact pcSeed1_075_ok
  · exact pcSeed1_076_ok
  · exact pcSeed1_077_ok
  · exact pcSeed1_078_ok
  · exact pcSeed1_079_ok
  · exact pcSeed1_080_ok
  · exact pcSeed1_081_ok
  · exact pcSeed1_082_ok
  · exact pcSeed1_083_ok
  · exact pcSeed1_084_ok
  · exact pcSeed1_085_ok
  · exact pcSeed1_086_ok
  · exact pcSeed1_087_ok
  · exact pcSeed1_088_ok
  · exact pcSeed1_089_ok
  · exact pcSeed1_090_ok
  · exact pcSeed1_091_ok
  · exact pcSeed1_092_ok
  · exact pcSeed1_093_ok
  · exact pcSeed1_094_ok
  · exact pcSeed1_095_ok
#print axioms pcRawSeeds1O003_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
