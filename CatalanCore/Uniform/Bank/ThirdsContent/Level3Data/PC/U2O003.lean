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
def pcRawSeed2_072 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (3) 5), (qq (13) 20), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (115) 6)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_072Palette : List KBranch := pcRawSeed2_072.law.palette 0
abbrev pcSeed2_072 : OrbitSeed := pcRawSeed2_072.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_072_ok : seedOK (pcHead 1) pcSeed2_072Palette 2 pcSeedLimit pcSeed2_072=true := by decide +kernel
#print axioms pcSeed2_072_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_073 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (3) 65), (qq (13) 280), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19435) 6)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_073Palette : List KBranch := pcRawSeed2_073.law.palette 0
abbrev pcSeed2_073 : OrbitSeed := pcRawSeed2_073.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_073_ok : seedOK (pcHead 1) pcSeed2_073Palette 2 pcSeedLimit pcSeed2_073=true := by decide +kernel
#print axioms pcSeed2_073_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_074 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (13) 20), (qq (69) 100), (qq (1) 1), (qq (5) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2760) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_074Palette : List KBranch := pcRawSeed2_074.law.palette 0
abbrev pcSeed2_074 : OrbitSeed := pcRawSeed2_074.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_074_ok : seedOK (pcHead 1) pcSeed2_074Palette 2 pcSeedLimit pcSeed2_074=true := by decide +kernel
#print axioms pcSeed2_074_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_075 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (13) 280), (qq (69) 1480), (qq (1) 1), (qq (83) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (540960) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_075Palette : List KBranch := pcRawSeed2_075.law.palette 0
abbrev pcSeed2_075 : OrbitSeed := pcRawSeed2_075.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_075_ok : seedOK (pcHead 1) pcSeed2_075Palette 2 pcSeedLimit pcSeed2_075=true := by decide +kernel
#print axioms pcSeed2_075_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_076 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (69) 1480), (qq (39) 830), (qq (33) 10), (qq (-65) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (219040) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_076Palette : List KBranch := pcRawSeed2_076.law.palette 0
abbrev pcSeed2_076 : OrbitSeed := pcRawSeed2_076.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_076_ok : seedOK (pcHead 1) pcSeed2_076Palette 2 pcSeedLimit pcSeed2_076=true := by decide +kernel
#print axioms pcSeed2_076_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_077 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (39) 830), (qq (1) 21), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1584470) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_077Palette : List KBranch := pcRawSeed2_077.law.palette 0
abbrev pcSeed2_077 : OrbitSeed := pcRawSeed2_077.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_077_ok : seedOK (pcHead 1) pcSeed2_077Palette 2 pcSeedLimit pcSeed2_077=true := by decide +kernel
#print axioms pcSeed2_077_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_078 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 1 1
  base := (⟨(qq (1) 21), (qq (23) 480), (qq (1) 1), (qq (27) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (30429) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_078Palette : List KBranch := pcRawSeed2_078.law.palette 0
abbrev pcSeed2_078 : OrbitSeed := pcRawSeed2_078.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_078_ok : seedOK (pcHead 1) pcSeed2_078Palette 2 pcSeedLimit pcSeed2_078=true := by decide +kernel
#print axioms pcSeed2_078_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_079 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (23) 480), (qq (13) 270), (qq (33) 10), (qq (-21) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (69120) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_079Palette : List KBranch := pcRawSeed2_079.law.palette 0
abbrev pcSeed2_079 : OrbitSeed := pcRawSeed2_079.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_079_ok : seedOK (pcHead 1) pcSeed2_079Palette 2 pcSeedLimit pcSeed2_079=true := by decide +kernel
#print axioms pcSeed2_079_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_080 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (13) 270), (qq (3) 62), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (503010) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_080Palette : List KBranch := pcRawSeed2_080.law.palette 0
abbrev pcSeed2_080 : OrbitSeed := pcRawSeed2_080.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_080_ok : seedOK (pcHead 1) pcSeed2_080Palette 2 pcSeedLimit pcSeed2_080=true := by decide +kernel
#print axioms pcSeed2_080_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_081 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 1
  base := (⟨(qq (3) 62), (qq (69) 1420), (qq (1) 1), (qq (80) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (44206) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_081Palette : List KBranch := pcRawSeed2_081.law.palette 0
abbrev pcSeed2_081 : OrbitSeed := pcRawSeed2_081.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_081_ok : seedOK (pcHead 1) pcSeed2_081Palette 2 pcSeedLimit pcSeed2_081=true := by decide +kernel
#print axioms pcSeed2_081_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_082 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (69) 1420), (qq (39) 800), (qq (33) 10), (qq (-62) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (201640) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_082Palette : List KBranch := pcRawSeed2_082.law.palette 0
abbrev pcSeed2_082 : OrbitSeed := pcRawSeed2_082.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_082_ok : seedOK (pcHead 1) pcSeed2_082Palette 2 pcSeedLimit pcSeed2_082=true := by decide +kernel
#print axioms pcSeed2_082_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_083 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 3 0 0
  base := (⟨(qq (39) 800), (qq (1) 20), (qq (2) 1), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1472000) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_083Palette : List KBranch := pcRawSeed2_083.law.palette 0
abbrev pcSeed2_083 : OrbitSeed := pcRawSeed2_083.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_083_ok : seedOK (pcHead 1) pcSeed2_083Palette 2 pcSeedLimit pcSeed2_083=true := by decide +kernel
#print axioms pcSeed2_083_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_084 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (1) 20), (qq (39) 770), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2760) 1)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_084Palette : List KBranch := pcRawSeed2_084.law.palette 0
abbrev pcSeed2_084 : OrbitSeed := pcRawSeed2_084.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_084_ok : seedOK (pcHead 1) pcSeed2_084Palette 2 pcSeedLimit pcSeed2_084=true := by decide +kernel
#print axioms pcSeed2_084_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_085 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (39) 770), (qq (69) 1360), (qq (13) 10), (qq (59) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1363670) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_085Palette : List KBranch := pcRawSeed2_085.law.palette 0
abbrev pcSeed2_085 : OrbitSeed := pcRawSeed2_085.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_085_ok : seedOK (pcHead 1) pcSeed2_085Palette 2 pcSeedLimit pcSeed2_085=true := by decide +kernel
#print axioms pcSeed2_085_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_086 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (69) 1360), (qq (3) 59), (qq (18) 5), (qq (-77) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (184960) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_086Palette : List KBranch := pcRawSeed2_086.law.palette 0
abbrev pcSeed2_086 : OrbitSeed := pcRawSeed2_086.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_086_ok : seedOK (pcHead 1) pcSeed2_086Palette 2 pcSeedLimit pcSeed2_086=true := by decide +kernel
#print axioms pcSeed2_086_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_087 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (3) 59), (qq (13) 250), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (80063) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_087Palette : List KBranch := pcRawSeed2_087.law.palette 0
abbrev pcSeed2_087 : OrbitSeed := pcRawSeed2_087.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_087_ok : seedOK (pcHead 1) pcSeed2_087Palette 2 pcSeedLimit pcSeed2_087=true := by decide +kernel
#print axioms pcSeed2_087_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_088 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (13) 250), (qq (23) 440), (qq (13) 10), (qq (19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (431250) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_088Palette : List KBranch := pcRawSeed2_088.law.palette 0
abbrev pcSeed2_088 : OrbitSeed := pcRawSeed2_088.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_088_ok : seedOK (pcHead 1) pcSeed2_088Palette 2 pcSeedLimit pcSeed2_088=true := by decide +kernel
#print axioms pcSeed2_088_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_089 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 440), (qq (1) 19), (qq (18) 5), (qq (-25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (58080) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_089Palette : List KBranch := pcRawSeed2_089.law.palette 0
abbrev pcSeed2_089 : OrbitSeed := pcRawSeed2_089.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_089_ok : seedOK (pcHead 1) pcSeed2_089Palette 2 pcSeedLimit pcSeed2_089=true := by decide +kernel
#print axioms pcSeed2_089_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_090 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (1) 19), (qq (39) 740), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24909) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_090Palette : List KBranch := pcRawSeed2_090.law.palette 0
abbrev pcSeed2_090 : OrbitSeed := pcRawSeed2_090.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_090_ok : seedOK (pcHead 1) pcSeed2_090Palette 2 pcSeedLimit pcSeed2_090=true := by decide +kernel
#print axioms pcSeed2_090_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_091 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 2
  base := (⟨(qq (39) 740), (qq (69) 1300), (qq (13) 10), (qq (56) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1259480) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_091Palette : List KBranch := pcRawSeed2_091.law.palette 0
abbrev pcSeed2_091 : OrbitSeed := pcRawSeed2_091.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_091_ok : seedOK (pcHead 1) pcSeed2_091Palette 2 pcSeedLimit pcSeed2_091=true := by decide +kernel
#print axioms pcSeed2_091_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_092 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (69) 1300), (qq (3) 56), (qq (18) 5), (qq (-74) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (169000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_092Palette : List KBranch := pcRawSeed2_092.law.palette 0
abbrev pcSeed2_092 : OrbitSeed := pcRawSeed2_092.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_092_ok : seedOK (pcHead 1) pcSeed2_092Palette 2 pcSeedLimit pcSeed2_092=true := by decide +kernel
#print axioms pcSeed2_092_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_093 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (3) 56), (qq (13) 240), (qq (13) 5), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36064) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_093Palette : List KBranch := pcRawSeed2_093.law.palette 0
abbrev pcSeed2_093 : OrbitSeed := pcRawSeed2_093.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_093_ok : seedOK (pcHead 1) pcSeed2_093Palette 2 pcSeedLimit pcSeed2_093=true := by decide +kernel
#print axioms pcSeed2_093_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_094 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (13) 240), (qq (23) 420), (qq (13) 10), (qq (18) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (397440) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_094Palette : List KBranch := pcRawSeed2_094.law.palette 0
abbrev pcSeed2_094 : OrbitSeed := pcRawSeed2_094.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_094_ok : seedOK (pcHead 1) pcSeed2_094Palette 2 pcSeedLimit pcSeed2_094=true := by decide +kernel
#print axioms pcSeed2_094_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_095 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 420), (qq (39) 710), (qq (18) 5), (qq (-24) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (52920) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_095Palette : List KBranch := pcRawSeed2_095.law.palette 0
abbrev pcSeed2_095 : OrbitSeed := pcRawSeed2_095.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_095_ok : seedOK (pcHead 1) pcSeed2_095Palette 2 pcSeedLimit pcSeed2_095=true := by decide +kernel
#print axioms pcSeed2_095_ok


def pcRawSeeds2O003 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_072, pcRawSeed2_073, pcRawSeed2_074, pcRawSeed2_075, pcRawSeed2_076, pcRawSeed2_077, pcRawSeed2_078, pcRawSeed2_079, pcRawSeed2_080, pcRawSeed2_081, pcRawSeed2_082, pcRawSeed2_083, pcRawSeed2_084, pcRawSeed2_085, pcRawSeed2_086, pcRawSeed2_087, pcRawSeed2_088, pcRawSeed2_089, pcRawSeed2_090, pcRawSeed2_091, pcRawSeed2_092, pcRawSeed2_093, pcRawSeed2_094, pcRawSeed2_095]
theorem pcRawSeeds2O003_ok : ∀ S∈pcRawSeeds2O003,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O003,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_072_ok
  · exact pcSeed2_073_ok
  · exact pcSeed2_074_ok
  · exact pcSeed2_075_ok
  · exact pcSeed2_076_ok
  · exact pcSeed2_077_ok
  · exact pcSeed2_078_ok
  · exact pcSeed2_079_ok
  · exact pcSeed2_080_ok
  · exact pcSeed2_081_ok
  · exact pcSeed2_082_ok
  · exact pcSeed2_083_ok
  · exact pcSeed2_084_ok
  · exact pcSeed2_085_ok
  · exact pcSeed2_086_ok
  · exact pcSeed2_087_ok
  · exact pcSeed2_088_ok
  · exact pcSeed2_089_ok
  · exact pcSeed2_090_ok
  · exact pcSeed2_091_ok
  · exact pcSeed2_092_ok
  · exact pcSeed2_093_ok
  · exact pcSeed2_094_ok
  · exact pcSeed2_095_ok
#print axioms pcRawSeeds2O003_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
