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
def pcRawSeed2_072 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (1) 3), (qq (55) 153), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (100) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_072Palette : List KBranch := pcRawSeed2_072.law.palette 0
abbrev pcSeed2_072 : OrbitSeed := pcRawSeed2_072.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_072_ok : seedOK (pcHead 1) pcSeed2_072Palette 2 pcSeedLimit pcSeed2_072=true := by decide +kernel
#print axioms pcSeed2_072_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_073 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 12), (qq (55) 648), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1600) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_073Palette : List KBranch := pcRawSeed2_073.law.palette 0
abbrev pcSeed2_073 : OrbitSeed := pcRawSeed2_073.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_073_ok : seedOK (pcHead 1) pcSeed2_073Palette 2 pcSeedLimit pcSeed2_073=true := by decide +kernel
#print axioms pcSeed2_073_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_074 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (55) 153), (qq (10) 27), (qq (1) 1), (qq (3) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10404) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_074Palette : List KBranch := pcRawSeed2_074.law.palette 0
abbrev pcSeed2_074 : OrbitSeed := pcRawSeed2_074.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_074_ok : seedOK (pcHead 1) pcSeed2_074Palette 2 pcSeedLimit pcSeed2_074=true := by decide +kernel
#print axioms pcSeed2_074_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_075 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (55) 648), (qq (10) 117), (qq (1) 1), (qq (14) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (186624) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_075Palette : List KBranch := pcRawSeed2_075.law.palette 0
abbrev pcSeed2_075 : OrbitSeed := pcRawSeed2_075.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_075_ok : seedOK (pcHead 1) pcSeed2_075Palette 2 pcSeedLimit pcSeed2_075=true := by decide +kernel
#print axioms pcSeed2_075_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_076 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (10) 27), (qq (11) 27), (qq (29) 9), (qq (-3) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (81) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_076Palette : List KBranch := pcRawSeed2_076.law.palette 0
abbrev pcSeed2_076 : OrbitSeed := pcRawSeed2_076.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_076_ok : seedOK (pcHead 1) pcSeed2_076Palette 2 pcSeedLimit pcSeed2_076=true := by decide +kernel
#print axioms pcSeed2_076_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_077 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 117), (qq (11) 126), (qq (29) 9), (qq (-12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1521) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_077Palette : List KBranch := pcRawSeed2_077.law.palette 0
abbrev pcSeed2_077 : OrbitSeed := pcRawSeed2_077.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_077_ok : seedOK (pcHead 1) pcSeed2_077Palette 2 pcSeedLimit pcSeed2_077=true := by decide +kernel
#print axioms pcSeed2_077_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_078 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (11) 27), (qq (5) 12), (qq (2) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8100) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_078Palette : List KBranch := pcRawSeed2_078.law.palette 0
abbrev pcSeed2_078 : OrbitSeed := pcRawSeed2_078.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_078_ok : seedOK (pcHead 1) pcSeed2_078Palette 2 pcSeedLimit pcSeed2_078=true := by decide +kernel
#print axioms pcSeed2_078_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_079 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 126), (qq (5) 57), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (176400) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_079Palette : List KBranch := pcRawSeed2_079.law.palette 0
abbrev pcSeed2_079 : OrbitSeed := pcRawSeed2_079.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_079_ok : seedOK (pcHead 1) pcSeed2_079Palette 2 pcSeedLimit pcSeed2_079=true := by decide +kernel
#print axioms pcSeed2_079_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_080 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (5) 12), (qq (25) 54), (qq (1) 1), (qq (12) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (64) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_080Palette : List KBranch := pcRawSeed2_080.law.palette 0
abbrev pcSeed2_080 : OrbitSeed := pcRawSeed2_080.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_080_ok : seedOK (pcHead 1) pcSeed2_080Palette 2 pcSeedLimit pcSeed2_080=true := by decide +kernel
#print axioms pcSeed2_080_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_081 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 57), (qq (25) 279), (qq (1) 1), (qq (67) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1444) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_081Palette : List KBranch := pcRawSeed2_081.law.palette 0
abbrev pcSeed2_081 : OrbitSeed := pcRawSeed2_081.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_081_ok : seedOK (pcHead 1) pcSeed2_081Palette 2 pcSeedLimit pcSeed2_081=true := by decide +kernel
#print axioms pcSeed2_081_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_082 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (25) 54), (qq (1) 2), (qq (29) 9), (qq (-12) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1296) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_082Palette : List KBranch := pcRawSeed2_082.law.palette 0
abbrev pcSeed2_082 : OrbitSeed := pcRawSeed2_082.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_082_ok : seedOK (pcHead 1) pcSeed2_082Palette 2 pcSeedLimit pcSeed2_082=true := by decide +kernel
#print axioms pcSeed2_082_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_083 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (25) 279), (qq (1) 11), (qq (29) 9), (qq (-57) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (34596) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_083Palette : List KBranch := pcRawSeed2_083.law.palette 0
abbrev pcSeed2_083 : OrbitSeed := pcRawSeed2_083.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_083_ok : seedOK (pcHead 1) pcSeed2_083Palette 2 pcSeedLimit pcSeed2_083=true := by decide +kernel
#print axioms pcSeed2_083_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_084 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (1) 2), (qq (55) 108), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (400) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_084Palette : List KBranch := pcRawSeed2_084.law.palette 0
abbrev pcSeed2_084 : OrbitSeed := pcRawSeed2_084.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_084_ok : seedOK (pcHead 1) pcSeed2_084Palette 2 pcSeedLimit pcSeed2_084=true := by decide +kernel
#print axioms pcSeed2_084_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_085 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 11), (qq (55) 603), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12100) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_085Palette : List KBranch := pcRawSeed2_085.law.palette 0
abbrev pcSeed2_085 : OrbitSeed := pcRawSeed2_085.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_085_ok : seedOK (pcHead 1) pcSeed2_085Palette 2 pcSeedLimit pcSeed2_085=true := by decide +kernel
#print axioms pcSeed2_085_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_086 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (55) 108), (qq (5) 9), (qq (1) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5184) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_086Palette : List KBranch := pcRawSeed2_086.law.palette 0
abbrev pcSeed2_086 : OrbitSeed := pcRawSeed2_086.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_086_ok : seedOK (pcHead 1) pcSeed2_086Palette 2 pcSeedLimit pcSeed2_086=true := by decide +kernel
#print axioms pcSeed2_086_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_087 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (55) 603), (qq (5) 54), (qq (1) 1), (qq (13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (161604) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_087Palette : List KBranch := pcRawSeed2_087.law.palette 0
abbrev pcSeed2_087 : OrbitSeed := pcRawSeed2_087.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_087_ok : seedOK (pcHead 1) pcSeed2_087Palette 2 pcSeedLimit pcSeed2_087=true := by decide +kernel
#print axioms pcSeed2_087_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_088 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (5) 9), (qq (11) 18), (qq (29) 9), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_088Palette : List KBranch := pcRawSeed2_088.law.palette 0
abbrev pcSeed2_088 : OrbitSeed := pcRawSeed2_088.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_088_ok : seedOK (pcHead 1) pcSeed2_088Palette 2 pcSeedLimit pcSeed2_088=true := by decide +kernel
#print axioms pcSeed2_088_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_089 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 54), (qq (11) 117), (qq (29) 9), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1296) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_089Palette : List KBranch := pcRawSeed2_089.law.palette 0
abbrev pcSeed2_089 : OrbitSeed := pcRawSeed2_089.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_089_ok : seedOK (pcHead 1) pcSeed2_089Palette 2 pcSeedLimit pcSeed2_089=true := by decide +kernel
#print axioms pcSeed2_089_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_090 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (11) 18), (qq (5) 7), (qq (2) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3600) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_090Palette : List KBranch := pcRawSeed2_090.law.palette 0
abbrev pcSeed2_090 : OrbitSeed := pcRawSeed2_090.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_090_ok : seedOK (pcHead 1) pcSeed2_090Palette 2 pcSeedLimit pcSeed2_090=true := by decide +kernel
#print axioms pcSeed2_090_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_091 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 117), (qq (5) 52), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (152100) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_091Palette : List KBranch := pcRawSeed2_091.law.palette 0
abbrev pcSeed2_091 : OrbitSeed := pcRawSeed2_091.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_091_ok : seedOK (pcHead 1) pcSeed2_091Palette 2 pcSeedLimit pcSeed2_091=true := by decide +kernel
#print axioms pcSeed2_091_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_092 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (5) 7), (qq (50) 63), (qq (1) 1), (qq (7) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (196) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_092Palette : List KBranch := pcRawSeed2_092.law.palette 0
abbrev pcSeed2_092 : OrbitSeed := pcRawSeed2_092.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_092_ok : seedOK (pcHead 1) pcSeed2_092Palette 2 pcSeedLimit pcSeed2_092=true := by decide +kernel
#print axioms pcSeed2_092_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_093 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 52), (qq (50) 513), (qq (1) 1), (qq (62) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10816) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_093Palette : List KBranch := pcRawSeed2_093.law.palette 0
abbrev pcSeed2_093 : OrbitSeed := pcRawSeed2_093.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_093_ok : seedOK (pcHead 1) pcSeed2_093Palette 2 pcSeedLimit pcSeed2_093=true := by decide +kernel
#print axioms pcSeed2_093_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_094 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (50) 513), (qq (55) 558), (qq (29) 9), (qq (-52) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (29241) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_094Palette : List KBranch := pcRawSeed2_094.law.palette 0
abbrev pcSeed2_094 : OrbitSeed := pcRawSeed2_094.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_094_ok : seedOK (pcHead 1) pcSeed2_094Palette 2 pcSeedLimit pcSeed2_094=true := by decide +kernel
#print axioms pcSeed2_094_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_095 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (55) 558), (qq (1) 10), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (138384) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_095Palette : List KBranch := pcRawSeed2_095.law.palette 0
abbrev pcSeed2_095 : OrbitSeed := pcRawSeed2_095.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_095_ok : seedOK (pcHead 1) pcSeed2_095Palette 2 pcSeedLimit pcSeed2_095=true := by decide +kernel
#print axioms pcSeed2_095_ok


def pcRawSeeds2O003 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_072, pcRawSeed2_073, pcRawSeed2_074, pcRawSeed2_075, pcRawSeed2_076, pcRawSeed2_077, pcRawSeed2_078, pcRawSeed2_079, pcRawSeed2_080, pcRawSeed2_081, pcRawSeed2_082, pcRawSeed2_083, pcRawSeed2_084, pcRawSeed2_085, pcRawSeed2_086, pcRawSeed2_087, pcRawSeed2_088, pcRawSeed2_089, pcRawSeed2_090, pcRawSeed2_091, pcRawSeed2_092, pcRawSeed2_093, pcRawSeed2_094, pcRawSeed2_095]
theorem pcRawSeeds2O003_ok : ∀ S∈pcRawSeeds2O003,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000)=true := by
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
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
