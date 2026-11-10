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
def pcRawSeed1_072 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (24) 85), (qq (3) 10), (qq (31) 10), (qq (-15) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15895) 144)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_072Palette : List KBranch := pcRawSeed1_072.law.palette 0
abbrev pcSeed1_072 : OrbitSeed := pcRawSeed1_072.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_072_ok : seedOK (pcHead 1) pcSeed1_072Palette 1 pcSeedLimit pcSeed1_072=true := by decide +kernel
#print axioms pcSeed1_072_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_073 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (24) 325), (qq (3) 40), (qq (31) 10), (qq (-51) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (232375) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_073Palette : List KBranch := pcRawSeed1_073.law.palette 0
abbrev pcSeed1_073 : OrbitSeed := pcRawSeed1_073.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_073_ok : seedOK (pcHead 1) pcSeed1_073Palette 1 pcSeedLimit pcSeed1_073=true := by decide +kernel
#print axioms pcSeed1_073_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_074 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (3) 10), (qq (4) 13), (qq (19) 10), (qq (1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (880) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_074Palette : List KBranch := pcRawSeed1_074.law.palette 0
abbrev pcSeed1_074 : OrbitSeed := pcRawSeed1_074.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_074_ok : seedOK (pcHead 1) pcSeed1_074Palette 1 pcSeedLimit pcSeed1_074=true := by decide +kernel
#print axioms pcSeed1_074_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_075 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (3) 40), (qq (4) 53), (qq (19) 10), (qq (13) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14080) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_075Palette : List KBranch := pcRawSeed1_075.law.palette 0
abbrev pcSeed1_075 : OrbitSeed := pcRawSeed1_075.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_075_ok : seedOK (pcHead 1) pcSeed1_075Palette 1 pcSeedLimit pcSeed1_075=true := by decide +kernel
#print axioms pcSeed1_075_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_076 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (4) 13), (qq (1) 3), (qq (9) 10), (qq (7) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1859) 20)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_076Palette : List KBranch := pcRawSeed1_076.law.palette 0
abbrev pcSeed1_076 : OrbitSeed := pcRawSeed1_076.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_076_ok : seedOK (pcHead 1) pcSeed1_076Palette 1 pcSeedLimit pcSeed1_076=true := by decide +kernel
#print axioms pcSeed1_076_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_077 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (4) 53), (qq (1) 13), (qq (9) 10), (qq (33) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (30899) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_077Palette : List KBranch := pcRawSeed1_077.law.palette 0
abbrev pcSeed1_077 : OrbitSeed := pcRawSeed1_077.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_077_ok : seedOK (pcHead 1) pcSeed1_077Palette 1 pcSeedLimit pcSeed1_077=true := by decide +kernel
#print axioms pcSeed1_077_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_078 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (1) 3), (qq (22) 65), (qq (-1) 10), (qq (13) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (84) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_078Palette : List KBranch := pcRawSeed1_078.law.palette 0
abbrev pcSeed1_078 : OrbitSeed := pcRawSeed1_078.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_078_ok : seedOK (pcHead 1) pcSeed1_078Palette 1 pcSeedLimit pcSeed1_078=true := by decide +kernel
#print axioms pcSeed1_078_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_079 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 13), (qq (22) 285), (qq (-1) 10), (qq (59) 2), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7436) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_079Palette : List KBranch := pcRawSeed1_079.law.palette 0
abbrev pcSeed1_079 : OrbitSeed := pcRawSeed1_079.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_079_ok : seedOK (pcHead 1) pcSeed1_079Palette 1 pcSeedLimit pcSeed1_079=true := by decide +kernel
#print axioms pcSeed1_079_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_080 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (22) 65), (qq (11) 30), (qq (21) 10), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (910) 11)⟩)
  N := 24
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
abbrev pcSeed1_080Palette : List KBranch := pcRawSeed1_080.law.palette 0
abbrev pcSeed1_080 : OrbitSeed := pcRawSeed1_080.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=25 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_080_ok : seedOK (pcHead 1) pcSeed1_080Palette 1 pcSeedLimit pcSeed1_080=true := by decide +kernel
#print axioms pcSeed1_080_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_081 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (11) 30), (qq (24) 65), (qq (43) 10), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (840) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_081Palette : List KBranch := pcRawSeed1_081.law.palette 0
abbrev pcSeed1_081 : OrbitSeed := pcRawSeed1_081.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_081_ok : seedOK (pcHead 1) pcSeed1_081Palette 1 pcSeedLimit pcSeed1_081=true := by decide +kernel
#print axioms pcSeed1_081_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_082 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (11) 140), (qq (24) 305), (qq (43) 10), (qq (-27) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (15680) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_082Palette : List KBranch := pcRawSeed1_082.law.palette 0
abbrev pcSeed1_082 : OrbitSeed := pcRawSeed1_082.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_082_ok : seedOK (pcHead 1) pcSeed1_082Palette 1 pcSeedLimit pcSeed1_082=true := by decide +kernel
#print axioms pcSeed1_082_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_083 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨9,by decide +kernel⟩]
  base := (⟨(qq (24) 65), (qq (2) 5), (qq (31) 10), (qq (-11) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (455) 6)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_083Palette : List KBranch := pcRawSeed1_083.law.palette 0
abbrev pcSeed1_083 : OrbitSeed := pcRawSeed1_083.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_083_ok : seedOK (pcHead 1) pcSeed1_083Palette 1 pcSeedLimit pcSeed1_083=true := by decide +kernel
#print axioms pcSeed1_083_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_084 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (24) 305), (qq (2) 25), (qq (31) 10), (qq (-47) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (204655) 144)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_084Palette : List KBranch := pcRawSeed1_084.law.palette 0
abbrev pcSeed1_084 : OrbitSeed := pcRawSeed1_084.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_084_ok : seedOK (pcHead 1) pcSeed1_084Palette 1 pcSeedLimit pcSeed1_084=true := by decide +kernel
#print axioms pcSeed1_084_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_085 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (2) 5), (qq (4) 9), (qq (2) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (70) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_085Palette : List KBranch := pcRawSeed1_085.law.palette 0
abbrev pcSeed1_085 : OrbitSeed := pcRawSeed1_085.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_085_ok : seedOK (pcHead 1) pcSeed1_085Palette 1 pcSeedLimit pcSeed1_085=true := by decide +kernel
#print axioms pcSeed1_085_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_086 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (2) 25), (qq (4) 49), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1375) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_086Palette : List KBranch := pcRawSeed1_086.law.palette 0
abbrev pcSeed1_086 : OrbitSeed := pcRawSeed1_086.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_086_ok : seedOK (pcHead 1) pcSeed1_086Palette 1 pcSeedLimit pcSeed1_086=true := by decide +kernel
#print axioms pcSeed1_086_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_087 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (4) 9), (qq (22) 45), (qq (1) 1), (qq (9) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (63) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_087Palette : List KBranch := pcRawSeed1_087.law.palette 0
abbrev pcSeed1_087 : OrbitSeed := pcRawSeed1_087.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_087_ok : seedOK (pcHead 1) pcSeed1_087Palette 1 pcSeedLimit pcSeed1_087=true := by decide +kernel
#print axioms pcSeed1_087_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_088 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (4) 49), (qq (22) 265), (qq (1) 1), (qq (57) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (26411) 20)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_088Palette : List KBranch := pcRawSeed1_088.law.palette 0
abbrev pcSeed1_088 : OrbitSeed := pcRawSeed1_088.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_088_ok : seedOK (pcHead 1) pcSeed1_088Palette 1 pcSeedLimit pcSeed1_088=true := by decide +kernel
#print axioms pcSeed1_088_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_089 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (22) 45), (qq (1) 2), (qq (16) 5), (qq (-9) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (630) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_089Palette : List KBranch := pcRawSeed1_089.law.palette 0
abbrev pcSeed1_089 : OrbitSeed := pcRawSeed1_089.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_089_ok : seedOK (pcHead 1) pcSeed1_089Palette 1 pcSeedLimit pcSeed1_089=true := by decide +kernel
#print axioms pcSeed1_089_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_090 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (22) 265), (qq (1) 12), (qq (16) 5), (qq (-49) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14045) 11)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_090Palette : List KBranch := pcRawSeed1_090.law.palette 0
abbrev pcSeed1_090 : OrbitSeed := pcRawSeed1_090.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_090_ok : seedOK (pcHead 1) pcSeed1_090Palette 1 pcSeedLimit pcSeed1_090=true := by decide +kernel
#print axioms pcSeed1_090_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_091 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (1) 2), (qq (8) 15), (qq (11) 5), (qq (-1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (56) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_091Palette : List KBranch := pcRawSeed1_091.law.palette 0
abbrev pcSeed1_091 : OrbitSeed := pcRawSeed1_091.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_091_ok : seedOK (pcHead 1) pcSeed1_091Palette 1 pcSeedLimit pcSeed1_091=true := by decide +kernel
#print axioms pcSeed1_091_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_092 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 12), (qq (8) 95), (qq (11) 5), (qq (-1) 4), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6336) 5)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_092Palette : List KBranch := pcRawSeed1_092.law.palette 0
abbrev pcSeed1_092 : OrbitSeed := pcRawSeed1_092.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_092_ok : seedOK (pcHead 1) pcSeed1_092Palette 1 pcSeedLimit pcSeed1_092=true := by decide +kernel
#print axioms pcSeed1_092_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_093 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (8) 15), (qq (11) 20), (qq (1) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (105) 2)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_093Palette : List KBranch := pcRawSeed1_093.law.palette 0
abbrev pcSeed1_093 : OrbitSeed := pcRawSeed1_093.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_093_ok : seedOK (pcHead 1) pcSeed1_093Palette 1 pcSeedLimit pcSeed1_093=true := by decide +kernel
#print axioms pcSeed1_093_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_094 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (8) 95), (qq (11) 130), (qq (1) 1), (qq (14) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19855) 16)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_094Palette : List KBranch := pcRawSeed1_094.law.palette 0
abbrev pcSeed1_094 : OrbitSeed := pcRawSeed1_094.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_094_ok : seedOK (pcHead 1) pcSeed1_094Palette 1 pcSeedLimit pcSeed1_094=true := by decide +kernel
#print axioms pcSeed1_094_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_095 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨8,by decide +kernel⟩]
  base := (⟨(qq (11) 20), (qq (3) 5), (qq (16) 5), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (560) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_095Palette : List KBranch := pcRawSeed1_095.law.palette 0
abbrev pcSeed1_095 : OrbitSeed := pcRawSeed1_095.toSeed 10 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_095_ok : seedOK (pcHead 1) pcSeed1_095Palette 1 pcSeedLimit pcSeed1_095=true := by decide +kernel
#print axioms pcSeed1_095_ok


def pcRawSeeds1O003 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_072, pcRawSeed1_073, pcRawSeed1_074, pcRawSeed1_075, pcRawSeed1_076, pcRawSeed1_077, pcRawSeed1_078, pcRawSeed1_079, pcRawSeed1_080, pcRawSeed1_081, pcRawSeed1_082, pcRawSeed1_083, pcRawSeed1_084, pcRawSeed1_085, pcRawSeed1_086, pcRawSeed1_087, pcRawSeed1_088, pcRawSeed1_089, pcRawSeed1_090, pcRawSeed1_091, pcRawSeed1_092, pcRawSeed1_093, pcRawSeed1_094, pcRawSeed1_095]
theorem pcRawSeeds1O003_ok : ∀ S∈pcRawSeeds1O003,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 10 1 10000)=true := by
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
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
