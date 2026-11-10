module

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_072 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 14), (qq (24) 335), (qq (21) 10), (qq (1) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8624) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_072Palette : List KBranch := pcRawSeed3_072.law.palette 0
abbrev pcSeed3_072 : OrbitSeed := pcRawSeed3_072.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_072_ok : seedOK (pcHead 1) pcSeed3_072Palette 3 pcSeedLimit pcSeed3_072=true := by decide +kernel
#print axioms pcSeed3_072_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_073 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (24) 95), (qq (4) 15), (qq (9) 10), (qq (17) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19855) 144)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_073Palette : List KBranch := pcRawSeed3_073.law.palette 0
abbrev pcSeed3_073 : OrbitSeed := pcRawSeed3_073.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_073_ok : seedOK (pcHead 1) pcSeed3_073Palette 3 pcSeedLimit pcSeed3_073=true := by decide +kernel
#print axioms pcSeed3_073_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_074 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (24) 335), (qq (4) 55), (qq (9) 10), (qq (69) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (246895) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_074Palette : List KBranch := pcRawSeed3_074.law.palette 0
abbrev pcSeed3_074 : OrbitSeed := pcRawSeed3_074.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_074_ok : seedOK (pcHead 1) pcSeed3_074Palette 3 pcSeedLimit pcSeed3_074=true := by decide +kernel
#print axioms pcSeed3_074_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_075 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (4) 15), (qq (11) 40), (qq (-1) 10), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (495) 4)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_075Palette : List KBranch := pcRawSeed3_075.law.palette 0
abbrev pcSeed3_075 : OrbitSeed := pcRawSeed3_075.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_075_ok : seedOK (pcHead 1) pcSeed3_075Palette 3 pcSeedLimit pcSeed3_075=true := by decide +kernel
#print axioms pcSeed3_075_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_076 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 55), (qq (11) 150), (qq (-1) 10), (qq (31) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6655) 4)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_076Palette : List KBranch := pcRawSeed3_076.law.palette 0
abbrev pcSeed3_076 : OrbitSeed := pcRawSeed3_076.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_076_ok : seedOK (pcHead 1) pcSeed3_076Palette 3 pcSeedLimit pcSeed3_076=true := by decide +kernel
#print axioms pcSeed3_076_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_077 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (11) 40), (qq (22) 75), (qq (21) 10), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1280) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed3_077Palette : List KBranch := pcRawSeed3_077.law.palette 0
abbrev pcSeed3_077 : OrbitSeed := pcRawSeed3_077.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_077_ok : seedOK (pcHead 1) pcSeed3_077Palette 3 pcSeedLimit pcSeed3_077=true := by decide +kernel
#print axioms pcSeed3_077_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_078 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (22) 75), (qq (3) 10), (qq (43) 10), (qq (-15) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1125) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_078Palette : List KBranch := pcRawSeed3_078.law.palette 0
abbrev pcSeed3_078 : OrbitSeed := pcRawSeed3_078.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_078_ok : seedOK (pcHead 1) pcSeed3_078Palette 3 pcSeedLimit pcSeed3_078=true := by decide +kernel
#print axioms pcSeed3_078_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_079 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (22) 295), (qq (3) 40), (qq (43) 10), (qq (-57) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17405) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_079Palette : List KBranch := pcRawSeed3_079.law.palette 0
abbrev pcSeed3_079 : OrbitSeed := pcRawSeed3_079.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_079_ok : seedOK (pcHead 1) pcSeed3_079Palette 3 pcSeedLimit pcSeed3_079=true := by decide +kernel
#print axioms pcSeed3_079_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_080 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (3) 10), (qq (8) 25), (qq (31) 10), (qq (-7) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (880) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_080Palette : List KBranch := pcRawSeed3_080.law.palette 0
abbrev pcSeed3_080 : OrbitSeed := pcRawSeed3_080.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_080_ok : seedOK (pcHead 1) pcSeed3_080Palette 3 pcSeedLimit pcSeed3_080=true := by decide +kernel
#print axioms pcSeed3_080_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_081 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (3) 40), (qq (8) 105), (qq (31) 10), (qq (-25) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14080) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_081Palette : List KBranch := pcRawSeed3_081.law.palette 0
abbrev pcSeed3_081 : OrbitSeed := pcRawSeed3_081.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_081_ok : seedOK (pcHead 1) pcSeed3_081Palette 3 pcSeedLimit pcSeed3_081=true := by decide +kernel
#print axioms pcSeed3_081_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_082 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (8) 25), (qq (1) 3), (qq (19) 10), (qq (1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (175) 2)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_082Palette : List KBranch := pcRawSeed3_082.law.palette 0
abbrev pcSeed3_082 : OrbitSeed := pcRawSeed3_082.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_082_ok : seedOK (pcHead 1) pcSeed3_082Palette 3 pcSeedLimit pcSeed3_082=true := by decide +kernel
#print axioms pcSeed3_082_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_083 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (8) 105), (qq (1) 13), (qq (19) 10), (qq (13) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24255) 16)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_083Palette : List KBranch := pcRawSeed3_083.law.palette 0
abbrev pcSeed3_083 : OrbitSeed := pcRawSeed3_083.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_083_ok : seedOK (pcHead 1) pcSeed3_083Palette 3 pcSeedLimit pcSeed3_083=true := by decide +kernel
#print axioms pcSeed3_083_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_084 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 3), (qq (4) 11), (qq (9) 10), (qq (13) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (84) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_084Palette : List KBranch := pcRawSeed3_084.law.palette 0
abbrev pcSeed3_084 : OrbitSeed := pcRawSeed3_084.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_084_ok : seedOK (pcHead 1) pcSeed3_084Palette 3 pcSeedLimit pcSeed3_084=true := by decide +kernel
#print axioms pcSeed3_084_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_085 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 13), (qq (4) 51), (qq (9) 10), (qq (65) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7436) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_085Palette : List KBranch := pcRawSeed3_085.law.palette 0
abbrev pcSeed3_085 : OrbitSeed := pcRawSeed3_085.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_085_ok : seedOK (pcHead 1) pcSeed3_085Palette 3 pcSeedLimit pcSeed3_085=true := by decide +kernel
#print axioms pcSeed3_085_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_086 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (4) 11), (qq (11) 30), (qq (-1) 10), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (77) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_086Palette : List KBranch := pcRawSeed3_086.law.palette 0
abbrev pcSeed3_086 : OrbitSeed := pcRawSeed3_086.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_086_ok : seedOK (pcHead 1) pcSeed3_086Palette 3 pcSeedLimit pcSeed3_086=true := by decide +kernel
#print axioms pcSeed3_086_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_087 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 51), (qq (11) 140), (qq (-1) 10), (qq (29) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (28611) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_087Palette : List KBranch := pcRawSeed3_087.law.palette 0
abbrev pcSeed3_087 : OrbitSeed := pcRawSeed3_087.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_087_ok : seedOK (pcHead 1) pcSeed3_087Palette 3 pcSeedLimit pcSeed3_087=true := by decide +kernel
#print axioms pcSeed3_087_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_088 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (11) 30), (qq (2) 5), (qq (21) 10), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (840) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed3_088Palette : List KBranch := pcRawSeed3_088.law.palette 0
abbrev pcSeed3_088 : OrbitSeed := pcRawSeed3_088.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_088_ok : seedOK (pcHead 1) pcSeed3_088Palette 3 pcSeedLimit pcSeed3_088=true := by decide +kernel
#print axioms pcSeed3_088_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_089 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (2) 5), (qq (24) 55), (qq (16) 5), (qq (-11) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (70) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_089Palette : List KBranch := pcRawSeed3_089.law.palette 0
abbrev pcSeed3_089 : OrbitSeed := pcRawSeed3_089.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_089_ok : seedOK (pcHead 1) pcSeed3_089Palette 3 pcSeedLimit pcSeed3_089=true := by decide +kernel
#print axioms pcSeed3_089_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_090 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (2) 25), (qq (24) 295), (qq (16) 5), (qq (-51) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1375) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_090Palette : List KBranch := pcRawSeed3_090.law.palette 0
abbrev pcSeed3_090 : OrbitSeed := pcRawSeed3_090.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_090_ok : seedOK (pcHead 1) pcSeed3_090Palette 3 pcSeedLimit pcSeed3_090=true := by decide +kernel
#print axioms pcSeed3_090_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_091 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (24) 55), (qq (1) 2), (qq (2) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (385) 6)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_091Palette : List KBranch := pcRawSeed3_091.law.palette 0
abbrev pcSeed3_091 : OrbitSeed := pcRawSeed3_091.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_091_ok : seedOK (pcHead 1) pcSeed3_091Palette 3 pcSeedLimit pcSeed3_091=true := by decide +kernel
#print axioms pcSeed3_091_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_092 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (24) 295), (qq (1) 12), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (191455) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_092Palette : List KBranch := pcRawSeed3_092.law.palette 0
abbrev pcSeed3_092 : OrbitSeed := pcRawSeed3_092.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_092_ok : seedOK (pcHead 1) pcSeed3_092Palette 3 pcSeedLimit pcSeed3_092=true := by decide +kernel
#print axioms pcSeed3_092_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_093 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (1) 2), (qq (11) 20), (qq (1) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (56) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_093Palette : List KBranch := pcRawSeed3_093.law.palette 0
abbrev pcSeed3_093 : OrbitSeed := pcRawSeed3_093.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_093_ok : seedOK (pcHead 1) pcSeed3_093Palette 3 pcSeedLimit pcSeed3_093=true := by decide +kernel
#print axioms pcSeed3_093_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_094 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 12), (qq (11) 130), (qq (1) 1), (qq (14) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6336) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_094Palette : List KBranch := pcRawSeed3_094.law.palette 0
abbrev pcSeed3_094 : OrbitSeed := pcRawSeed3_094.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_094_ok : seedOK (pcHead 1) pcSeed3_094Palette 3 pcSeedLimit pcSeed3_094=true := by decide +kernel
#print axioms pcSeed3_094_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_095 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (11) 20), (qq (4) 7), (qq (16) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (560) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_095Palette : List KBranch := pcRawSeed3_095.law.palette 0
abbrev pcSeed3_095 : OrbitSeed := pcRawSeed3_095.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_095_ok : seedOK (pcHead 1) pcSeed3_095Palette 3 pcSeedLimit pcSeed3_095=true := by decide +kernel
#print axioms pcSeed3_095_ok


def pcRawSeeds3O003 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed3_072, pcRawSeed3_073, pcRawSeed3_074, pcRawSeed3_075, pcRawSeed3_076, pcRawSeed3_077, pcRawSeed3_078, pcRawSeed3_079, pcRawSeed3_080, pcRawSeed3_081, pcRawSeed3_082, pcRawSeed3_083, pcRawSeed3_084, pcRawSeed3_085, pcRawSeed3_086, pcRawSeed3_087, pcRawSeed3_088, pcRawSeed3_089, pcRawSeed3_090, pcRawSeed3_091, pcRawSeed3_092, pcRawSeed3_093, pcRawSeed3_094, pcRawSeed3_095]
theorem pcRawSeeds3O003_ok : ∀ S∈pcRawSeeds3O003,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 10 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3O003,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed3_072_ok
  · exact pcSeed3_073_ok
  · exact pcSeed3_074_ok
  · exact pcSeed3_075_ok
  · exact pcSeed3_076_ok
  · exact pcSeed3_077_ok
  · exact pcSeed3_078_ok
  · exact pcSeed3_079_ok
  · exact pcSeed3_080_ok
  · exact pcSeed3_081_ok
  · exact pcSeed3_082_ok
  · exact pcSeed3_083_ok
  · exact pcSeed3_084_ok
  · exact pcSeed3_085_ok
  · exact pcSeed3_086_ok
  · exact pcSeed3_087_ok
  · exact pcSeed3_088_ok
  · exact pcSeed3_089_ok
  · exact pcSeed3_090_ok
  · exact pcSeed3_091_ok
  · exact pcSeed3_092_ok
  · exact pcSeed3_093_ok
  · exact pcSeed3_094_ok
  · exact pcSeed3_095_ok
#print axioms pcRawSeeds3O003_ok
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
