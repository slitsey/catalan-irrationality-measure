module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_120 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (3) 46), (qq (69) 1040), (qq (1) 1), (qq (58) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24334) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_120Palette : List KBranch := pcRawSeed1_120.law.palette 0
abbrev pcSeed1_120 : OrbitSeed := pcRawSeed1_120.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_120_ok : seedOK (pcHead 1) pcSeed1_120Palette 1 pcSeedLimit pcSeed1_120=true := by decide +kernel
#print axioms pcSeed1_120_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_121 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (69) 1040), (qq (1) 15), (qq (33) 10), (qq (-46) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (108160) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_121Palette : List KBranch := pcRawSeed1_121.law.palette 0
abbrev pcSeed1_121 : OrbitSeed := pcRawSeed1_121.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_121_ok : seedOK (pcHead 1) pcSeed1_121Palette 1 pcSeedLimit pcSeed1_121=true := by decide +kernel
#print axioms pcSeed1_121_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_122 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (1) 15), (qq (39) 580), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3105) 2)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_122Palette : List KBranch := pcRawSeed1_122.law.palette 0
abbrev pcSeed1_122 : OrbitSeed := pcRawSeed1_122.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_122_ok : seedOK (pcHead 1) pcSeed1_122Palette 1 pcSeedLimit pcSeed1_122=true := by decide +kernel
#print axioms pcSeed1_122_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_123 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (39) 580), (qq (23) 340), (qq (1) 1), (qq (19) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (773720) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_123Palette : List KBranch := pcRawSeed1_123.law.palette 0
abbrev pcSeed1_123 : OrbitSeed := pcRawSeed1_123.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_123_ok : seedOK (pcHead 1) pcSeed1_123Palette 1 pcSeedLimit pcSeed1_123=true := by decide +kernel
#print axioms pcSeed1_123_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_124 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 340), (qq (13) 190), (qq (33) 10), (qq (-15) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (34680) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_124Palette : List KBranch := pcRawSeed1_124.law.palette 0
abbrev pcSeed1_124 : OrbitSeed := pcRawSeed1_124.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_124_ok : seedOK (pcHead 1) pcSeed1_124Palette 1 pcSeedLimit pcSeed1_124=true := by decide +kernel
#print axioms pcSeed1_124_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_125 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (13) 190), (qq (3) 43), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (249090) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_125Palette : List KBranch := pcRawSeed1_125.law.palette 0
abbrev pcSeed1_125 : OrbitSeed := pcRawSeed1_125.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_125_ok : seedOK (pcHead 1) pcSeed1_125Palette 1 pcSeedLimit pcSeed1_125=true := by decide +kernel
#print axioms pcSeed1_125_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_126 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (3) 43), (qq (69) 980), (qq (1) 1), (qq (55) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (42527) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_126Palette : List KBranch := pcRawSeed1_126.law.palette 0
abbrev pcSeed1_126 : OrbitSeed := pcRawSeed1_126.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_126_ok : seedOK (pcHead 1) pcSeed1_126Palette 1 pcSeedLimit pcSeed1_126=true := by decide +kernel
#print axioms pcSeed1_126_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_127 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (69) 980), (qq (39) 550), (qq (33) 10), (qq (-43) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (96040) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_127Palette : List KBranch := pcRawSeed1_127.law.palette 0
abbrev pcSeed1_127 : OrbitSeed := pcRawSeed1_127.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_127_ok : seedOK (pcHead 1) pcSeed1_127Palette 1 pcSeedLimit pcSeed1_127=true := by decide +kernel
#print axioms pcSeed1_127_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_128 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (39) 550), (qq (1) 14), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (695750) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_128Palette : List KBranch := pcRawSeed1_128.law.palette 0
abbrev pcSeed1_128 : OrbitSeed := pcRawSeed1_128.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_128_ok : seedOK (pcHead 1) pcSeed1_128Palette 1 pcSeedLimit pcSeed1_128=true := by decide +kernel
#print axioms pcSeed1_128_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_129 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (1) 14), (qq (23) 320), (qq (1) 1), (qq (18) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6762) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_129Palette : List KBranch := pcRawSeed1_129.law.palette 0
abbrev pcSeed1_129 : OrbitSeed := pcRawSeed1_129.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_129_ok : seedOK (pcHead 1) pcSeed1_129Palette 1 pcSeedLimit pcSeed1_129=true := by decide +kernel
#print axioms pcSeed1_129_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_130 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 320), (qq (13) 180), (qq (33) 10), (qq (-14) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (30720) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_130Palette : List KBranch := pcRawSeed1_130.law.palette 0
abbrev pcSeed1_130 : OrbitSeed := pcRawSeed1_130.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_130_ok : seedOK (pcHead 1) pcSeed1_130Palette 1 pcSeedLimit pcSeed1_130=true := by decide +kernel
#print axioms pcSeed1_130_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_131 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (13) 180), (qq (3) 40), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (223560) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_131Palette : List KBranch := pcRawSeed1_131.law.palette 0
abbrev pcSeed1_131 : OrbitSeed := pcRawSeed1_131.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_131_ok : seedOK (pcHead 1) pcSeed1_131Palette 1 pcSeedLimit pcSeed1_131=true := by decide +kernel
#print axioms pcSeed1_131_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_132 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 40), (qq (13) 170), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3680) 3)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_132Palette : List KBranch := pcRawSeed1_132.law.palette 0
abbrev pcSeed1_132 : OrbitSeed := pcRawSeed1_132.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_132_ok : seedOK (pcHead 1) pcSeed1_132Palette 1 pcSeedLimit pcSeed1_132=true := by decide +kernel
#print axioms pcSeed1_132_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_133 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (13) 170), (qq (23) 300), (qq (13) 10), (qq (13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (199410) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_133Palette : List KBranch := pcRawSeed1_133.law.palette 0
abbrev pcSeed1_133 : OrbitSeed := pcRawSeed1_133.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_133_ok : seedOK (pcHead 1) pcSeed1_133Palette 1 pcSeedLimit pcSeed1_133=true := by decide +kernel
#print axioms pcSeed1_133_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_134 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 300), (qq (1) 13), (qq (18) 5), (qq (-17) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (27000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_134Palette : List KBranch := pcRawSeed1_134.law.palette 0
abbrev pcSeed1_134 : OrbitSeed := pcRawSeed1_134.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_134_ok : seedOK (pcHead 1) pcSeed1_134Palette 1 pcSeedLimit pcSeed1_134=true := by decide +kernel
#print axioms pcSeed1_134_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_135 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 13), (qq (39) 490), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11661) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_135Palette : List KBranch := pcRawSeed1_135.law.palette 0
abbrev pcSeed1_135 : OrbitSeed := pcRawSeed1_135.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_135_ok : seedOK (pcHead 1) pcSeed1_135Palette 1 pcSeedLimit pcSeed1_135=true := by decide +kernel
#print axioms pcSeed1_135_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_136 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (39) 490), (qq (69) 860), (qq (13) 10), (qq (37) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (552230) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_136Palette : List KBranch := pcRawSeed1_136.law.palette 0
abbrev pcSeed1_136 : OrbitSeed := pcRawSeed1_136.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_136_ok : seedOK (pcHead 1) pcSeed1_136Palette 1 pcSeedLimit pcSeed1_136=true := by decide +kernel
#print axioms pcSeed1_136_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_137 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (69) 860), (qq (3) 37), (qq (18) 5), (qq (-49) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (73960) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_137Palette : List KBranch := pcRawSeed1_137.law.palette 0
abbrev pcSeed1_137 : OrbitSeed := pcRawSeed1_137.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_137_ok : seedOK (pcHead 1) pcSeed1_137Palette 1 pcSeedLimit pcSeed1_137=true := by decide +kernel
#print axioms pcSeed1_137_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_138 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 37), (qq (13) 160), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (31487) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_138Palette : List KBranch := pcRawSeed1_138.law.palette 0
abbrev pcSeed1_138 : OrbitSeed := pcRawSeed1_138.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_138_ok : seedOK (pcHead 1) pcSeed1_138Palette 1 pcSeedLimit pcSeed1_138=true := by decide +kernel
#print axioms pcSeed1_138_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_139 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (13) 160), (qq (23) 280), (qq (13) 10), (qq (12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (176640) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_139Palette : List KBranch := pcRawSeed1_139.law.palette 0
abbrev pcSeed1_139 : OrbitSeed := pcRawSeed1_139.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_139_ok : seedOK (pcHead 1) pcSeed1_139Palette 1 pcSeedLimit pcSeed1_139=true := by decide +kernel
#print axioms pcSeed1_139_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_140 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 280), (qq (1) 12), (qq (18) 5), (qq (-16) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23520) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_140Palette : List KBranch := pcRawSeed1_140.law.palette 0
abbrev pcSeed1_140 : OrbitSeed := pcRawSeed1_140.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_140_ok : seedOK (pcHead 1) pcSeed1_140Palette 1 pcSeedLimit pcSeed1_140=true := by decide +kernel
#print axioms pcSeed1_140_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_141 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 12), (qq (39) 460), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4968) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_141Palette : List KBranch := pcRawSeed1_141.law.palette 0
abbrev pcSeed1_141 : OrbitSeed := pcRawSeed1_141.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_141_ok : seedOK (pcHead 1) pcSeed1_141Palette 1 pcSeedLimit pcSeed1_141=true := by decide +kernel
#print axioms pcSeed1_141_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_142 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (39) 460), (qq (69) 800), (qq (13) 10), (qq (34) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (486680) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_142Palette : List KBranch := pcRawSeed1_142.law.palette 0
abbrev pcSeed1_142 : OrbitSeed := pcRawSeed1_142.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_142_ok : seedOK (pcHead 1) pcSeed1_142Palette 1 pcSeedLimit pcSeed1_142=true := by decide +kernel
#print axioms pcSeed1_142_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_143 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (69) 800), (qq (13) 150), (qq (18) 5), (qq (-46) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (64000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_143Palette : List KBranch := pcRawSeed1_143.law.palette 0
abbrev pcSeed1_143 : OrbitSeed := pcRawSeed1_143.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_143_ok : seedOK (pcHead 1) pcSeed1_143Palette 1 pcSeedLimit pcSeed1_143=true := by decide +kernel
#print axioms pcSeed1_143_ok


def pcRawSeeds1O005 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_120, pcRawSeed1_121, pcRawSeed1_122, pcRawSeed1_123, pcRawSeed1_124, pcRawSeed1_125, pcRawSeed1_126, pcRawSeed1_127, pcRawSeed1_128, pcRawSeed1_129, pcRawSeed1_130, pcRawSeed1_131, pcRawSeed1_132, pcRawSeed1_133, pcRawSeed1_134, pcRawSeed1_135, pcRawSeed1_136, pcRawSeed1_137, pcRawSeed1_138, pcRawSeed1_139, pcRawSeed1_140, pcRawSeed1_141, pcRawSeed1_142, pcRawSeed1_143]
theorem pcRawSeeds1O005_ok : ∀ S∈pcRawSeeds1O005,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O005,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_120_ok
  · exact pcSeed1_121_ok
  · exact pcSeed1_122_ok
  · exact pcSeed1_123_ok
  · exact pcSeed1_124_ok
  · exact pcSeed1_125_ok
  · exact pcSeed1_126_ok
  · exact pcSeed1_127_ok
  · exact pcSeed1_128_ok
  · exact pcSeed1_129_ok
  · exact pcSeed1_130_ok
  · exact pcSeed1_131_ok
  · exact pcSeed1_132_ok
  · exact pcSeed1_133_ok
  · exact pcSeed1_134_ok
  · exact pcSeed1_135_ok
  · exact pcSeed1_136_ok
  · exact pcSeed1_137_ok
  · exact pcSeed1_138_ok
  · exact pcSeed1_139_ok
  · exact pcSeed1_140_ok
  · exact pcSeed1_141_ok
  · exact pcSeed1_142_ok
  · exact pcSeed1_143_ok
#print axioms pcRawSeeds1O005_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
