module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_072 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 666), (qq (1) 12), (qq (17) 9), (qq (16) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (197136) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_072Palette : List KBranch := pcRawSeed4_072.law.palette 0
abbrev pcSeed4_072 : OrbitSeed := pcRawSeed4_072.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_072_ok : seedOK (pcHead 1) pcSeed4_072Palette 4 pcSeedLimit pcSeed4_072=true := by decide +kernel
#print axioms pcSeed4_072_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_073 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 3), (qq (5) 14), (qq (8) 9), (qq (16) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (100) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_073Palette : List KBranch := pcRawSeed4_073.law.palette 0
abbrev pcSeed4_073 : OrbitSeed := pcRawSeed4_073.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_073_ok : seedOK (pcHead 1) pcSeed4_073Palette 4 pcSeedLimit pcSeed4_073=true := by decide +kernel
#print axioms pcSeed4_073_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_074 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 12), (qq (5) 59), (qq (8) 9), (qq (76) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1600) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_074Palette : List KBranch := pcRawSeed4_074.law.palette 0
abbrev pcSeed4_074 : OrbitSeed := pcRawSeed4_074.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_074_ok : seedOK (pcHead 1) pcSeed4_074Palette 4 pcSeedLimit pcSeed4_074=true := by decide +kernel
#print axioms pcSeed4_074_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_075 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (5) 14), (qq (10) 27), (qq (-1) 9), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (784) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_075Palette : List KBranch := pcRawSeed4_075.law.palette 0
abbrev pcSeed4_075 : OrbitSeed := pcRawSeed4_075.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_075_ok : seedOK (pcHead 1) pcSeed4_075Palette 4 pcSeedLimit pcSeed4_075=true := by decide +kernel
#print axioms pcSeed4_075_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_076 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (5) 59), (qq (10) 117), (qq (-1) 9), (qq (27) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (13924) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_076Palette : List KBranch := pcRawSeed4_076.law.palette 0
abbrev pcSeed4_076 : OrbitSeed := pcRawSeed4_076.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_076_ok : seedOK (pcHead 1) pcSeed4_076Palette 4 pcSeedLimit pcSeed4_076=true := by decide +kernel
#print axioms pcSeed4_076_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_077 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (10) 27), (qq (25) 63), (qq (19) 9), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (81) 1)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed4_077Palette : List KBranch := pcRawSeed4_077.law.palette 0
abbrev pcSeed4_077 : OrbitSeed := pcRawSeed4_077.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_077_ok : seedOK (pcHead 1) pcSeed4_077Palette 4 pcSeedLimit pcSeed4_077=true := by decide +kernel
#print axioms pcSeed4_077_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_078 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (25) 63), (qq (11) 27), (qq (13) 3), (qq (-28) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1764) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_078Palette : List KBranch := pcRawSeed4_078.law.palette 0
abbrev pcSeed4_078 : OrbitSeed := pcRawSeed4_078.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_078_ok : seedOK (pcHead 1) pcSeed4_078Palette 4 pcSeedLimit pcSeed4_078=true := by decide +kernel
#print axioms pcSeed4_078_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_079 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (25) 288), (qq (11) 126), (qq (13) 3), (qq (-123) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36864) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_079Palette : List KBranch := pcRawSeed4_079.law.palette 0
abbrev pcSeed4_079 : OrbitSeed := pcRawSeed4_079.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_079_ok : seedOK (pcHead 1) pcSeed4_079Palette 4 pcSeedLimit pcSeed4_079=true := by decide +kernel
#print axioms pcSeed4_079_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_080 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 27), (qq (55) 126), (qq (28) 9), (qq (-13) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8100) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_080Palette : List KBranch := pcRawSeed4_080.law.palette 0
abbrev pcSeed4_080 : OrbitSeed := pcRawSeed4_080.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_080_ok : seedOK (pcHead 1) pcSeed4_080Palette 4 pcSeedLimit pcSeed4_080=true := by decide +kernel
#print axioms pcSeed4_080_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_081 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 126), (qq (55) 621), (qq (28) 9), (qq (-53) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (176400) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_081Palette : List KBranch := pcRawSeed4_081.law.palette 0
abbrev pcSeed4_081 : OrbitSeed := pcRawSeed4_081.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_081_ok : seedOK (pcHead 1) pcSeed4_081Palette 4 pcSeedLimit pcSeed4_081=true := by decide +kernel
#print axioms pcSeed4_081_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_082 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (55) 126), (qq (1) 2), (qq (17) 9), (qq (1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7056) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_082Palette : List KBranch := pcRawSeed4_082.law.palette 0
abbrev pcSeed4_082 : OrbitSeed := pcRawSeed4_082.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_082_ok : seedOK (pcHead 1) pcSeed4_082Palette 4 pcSeedLimit pcSeed4_082=true := by decide +kernel
#print axioms pcSeed4_082_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_083 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (55) 621), (qq (1) 11), (qq (17) 9), (qq (16) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (171396) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_083Palette : List KBranch := pcRawSeed4_083.law.palette 0
abbrev pcSeed4_083 : OrbitSeed := pcRawSeed4_083.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_083_ok : seedOK (pcHead 1) pcSeed4_083Palette 4 pcSeedLimit pcSeed4_083=true := by decide +kernel
#print axioms pcSeed4_083_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_084 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 2), (qq (5) 9), (qq (8) 9), (qq (11) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (400) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_084Palette : List KBranch := pcRawSeed4_084.law.palette 0
abbrev pcSeed4_084 : OrbitSeed := pcRawSeed4_084.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_084_ok : seedOK (pcHead 1) pcSeed4_084Palette 4 pcSeedLimit pcSeed4_084=true := by decide +kernel
#print axioms pcSeed4_084_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_085 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 11), (qq (5) 54), (qq (8) 9), (qq (71) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12100) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_085Palette : List KBranch := pcRawSeed4_085.law.palette 0
abbrev pcSeed4_085 : OrbitSeed := pcRawSeed4_085.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_085_ok : seedOK (pcHead 1) pcSeed4_085Palette 4 pcSeedLimit pcSeed4_085=true := by decide +kernel
#print axioms pcSeed4_085_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_086 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (5) 9), (qq (11) 18), (qq (20) 9), (qq (-1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (36) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_086Palette : List KBranch := pcRawSeed4_086.law.palette 0
abbrev pcSeed4_086 : OrbitSeed := pcRawSeed4_086.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_086_ok : seedOK (pcHead 1) pcSeed4_086Palette 4 pcSeedLimit pcSeed4_086=true := by decide +kernel
#print axioms pcSeed4_086_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_087 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 54), (qq (11) 117), (qq (20) 9), (qq (-1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1296) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_087Palette : List KBranch := pcRawSeed4_087.law.palette 0
abbrev pcSeed4_087 : OrbitSeed := pcRawSeed4_087.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_087_ok : seedOK (pcHead 1) pcSeed4_087Palette 4 pcSeedLimit pcSeed4_087=true := by decide +kernel
#print axioms pcSeed4_087_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_088 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (11) 18), (qq (50) 81), (qq (1) 1), (qq (9) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3600) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_088Palette : List KBranch := pcRawSeed4_088.law.palette 0
abbrev pcSeed4_088 : OrbitSeed := pcRawSeed4_088.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_088_ok : seedOK (pcHead 1) pcSeed4_088Palette 4 pcSeedLimit pcSeed4_088=true := by decide +kernel
#print axioms pcSeed4_088_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_089 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 117), (qq (50) 531), (qq (1) 1), (qq (64) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (152100) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_089Palette : List KBranch := pcRawSeed4_089.law.palette 0
abbrev pcSeed4_089 : OrbitSeed := pcRawSeed4_089.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_089_ok : seedOK (pcHead 1) pcSeed4_089Palette 4 pcSeedLimit pcSeed4_089=true := by decide +kernel
#print axioms pcSeed4_089_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_090 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (50) 531), (qq (55) 576), (qq (29) 9), (qq (-54) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (31329) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_090Palette : List KBranch := pcRawSeed4_090.law.palette 0
abbrev pcSeed4_090 : OrbitSeed := pcRawSeed4_090.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_090_ok : seedOK (pcHead 1) pcSeed4_090Palette 4 pcSeedLimit pcSeed4_090=true := by decide +kernel
#print axioms pcSeed4_090_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_091 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (55) 576), (qq (1) 10), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (147456) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_091Palette : List KBranch := pcRawSeed4_091.law.palette 0
abbrev pcSeed4_091 : OrbitSeed := pcRawSeed4_091.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_091_ok : seedOK (pcHead 1) pcSeed4_091Palette 4 pcSeedLimit pcSeed4_091=true := by decide +kernel
#print axioms pcSeed4_091_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_092 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 10), (qq (10) 99), (qq (1) 1), (qq (12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10000) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_092Palette : List KBranch := pcRawSeed4_092.law.palette 0
abbrev pcSeed4_092 : OrbitSeed := pcRawSeed4_092.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_092_ok : seedOK (pcHead 1) pcSeed4_092Palette 4 pcSeedLimit pcSeed4_092=true := by decide +kernel
#print axioms pcSeed4_092_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_093 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 99), (qq (11) 108), (qq (29) 9), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1089) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_093Palette : List KBranch := pcRawSeed4_093.law.palette 0
abbrev pcSeed4_093 : OrbitSeed := pcRawSeed4_093.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_093_ok : seedOK (pcHead 1) pcSeed4_093Palette 4 pcSeedLimit pcSeed4_093=true := by decide +kernel
#print axioms pcSeed4_093_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_094 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 108), (qq (5) 49), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (129600) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_094Palette : List KBranch := pcRawSeed4_094.law.palette 0
abbrev pcSeed4_094 : OrbitSeed := pcRawSeed4_094.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_094_ok : seedOK (pcHead 1) pcSeed4_094Palette 4 pcSeedLimit pcSeed4_094=true := by decide +kernel
#print axioms pcSeed4_094_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_095 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 49), (qq (25) 243), (qq (1) 1), (qq (59) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9604) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_095Palette : List KBranch := pcRawSeed4_095.law.palette 0
abbrev pcSeed4_095 : OrbitSeed := pcRawSeed4_095.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_095_ok : seedOK (pcHead 1) pcSeed4_095Palette 4 pcSeedLimit pcSeed4_095=true := by decide +kernel
#print axioms pcSeed4_095_ok


def pcRawSeeds4O003 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed4_072, pcRawSeed4_073, pcRawSeed4_074, pcRawSeed4_075, pcRawSeed4_076, pcRawSeed4_077, pcRawSeed4_078, pcRawSeed4_079, pcRawSeed4_080, pcRawSeed4_081, pcRawSeed4_082, pcRawSeed4_083, pcRawSeed4_084, pcRawSeed4_085, pcRawSeed4_086, pcRawSeed4_087, pcRawSeed4_088, pcRawSeed4_089, pcRawSeed4_090, pcRawSeed4_091, pcRawSeed4_092, pcRawSeed4_093, pcRawSeed4_094, pcRawSeed4_095]
theorem pcRawSeeds4O003_ok : ∀ S∈pcRawSeeds4O003,
    seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds4O003,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed4_072_ok
  · exact pcSeed4_073_ok
  · exact pcSeed4_074_ok
  · exact pcSeed4_075_ok
  · exact pcSeed4_076_ok
  · exact pcSeed4_077_ok
  · exact pcSeed4_078_ok
  · exact pcSeed4_079_ok
  · exact pcSeed4_080_ok
  · exact pcSeed4_081_ok
  · exact pcSeed4_082_ok
  · exact pcSeed4_083_ok
  · exact pcSeed4_084_ok
  · exact pcSeed4_085_ok
  · exact pcSeed4_086_ok
  · exact pcSeed4_087_ok
  · exact pcSeed4_088_ok
  · exact pcSeed4_089_ok
  · exact pcSeed4_090_ok
  · exact pcSeed4_091_ok
  · exact pcSeed4_092_ok
  · exact pcSeed4_093_ok
  · exact pcSeed4_094_ok
  · exact pcSeed4_095_ok
#print axioms pcRawSeeds4O003_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
