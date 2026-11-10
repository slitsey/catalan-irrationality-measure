module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_120 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 340), (qq (3) 44), (qq (33) 10), (qq (-15) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (34680) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_120Palette : List KBranch := pcRawSeed2_120.law.palette 0
abbrev pcSeed2_120 : OrbitSeed := pcRawSeed2_120.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_120_ok : seedOK (pcHead 1) pcSeed2_120Palette 2 pcSeedLimit pcSeed2_120=true := by decide +kernel
#print axioms pcSeed2_120_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_121 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (3) 44), (qq (13) 190), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (22264) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_121Palette : List KBranch := pcRawSeed2_121.law.palette 0
abbrev pcSeed2_121 : OrbitSeed := pcRawSeed2_121.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_121_ok : seedOK (pcHead 1) pcSeed2_121Palette 2 pcSeedLimit pcSeed2_121=true := by decide +kernel
#print axioms pcSeed2_121_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_122 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (13) 190), (qq (69) 1000), (qq (1) 1), (qq (56) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (249090) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_122Palette : List KBranch := pcRawSeed2_122.law.palette 0
abbrev pcSeed2_122 : OrbitSeed := pcRawSeed2_122.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_122_ok : seedOK (pcHead 1) pcSeed2_122Palette 2 pcSeedLimit pcSeed2_122=true := by decide +kernel
#print axioms pcSeed2_122_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_123 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (69) 1000), (qq (39) 560), (qq (33) 10), (qq (-44) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (100000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_123Palette : List KBranch := pcRawSeed2_123.law.palette 0
abbrev pcSeed2_123 : OrbitSeed := pcRawSeed2_123.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_123_ok : seedOK (pcHead 1) pcSeed2_123Palette 2 pcSeedLimit pcSeed2_123=true := by decide +kernel
#print axioms pcSeed2_123_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_124 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (39) 560), (qq (1) 14), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (721280) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_124Palette : List KBranch := pcRawSeed2_124.law.palette 0
abbrev pcSeed2_124 : OrbitSeed := pcRawSeed2_124.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_124_ok : seedOK (pcHead 1) pcSeed2_124Palette 2 pcSeedLimit pcSeed2_124=true := by decide +kernel
#print axioms pcSeed2_124_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_125 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 1 1
  base := (⟨(qq (1) 14), (qq (23) 320), (qq (1) 1), (qq (18) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (6762) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_125Palette : List KBranch := pcRawSeed2_125.law.palette 0
abbrev pcSeed2_125 : OrbitSeed := pcRawSeed2_125.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_125_ok : seedOK (pcHead 1) pcSeed2_125Palette 2 pcSeedLimit pcSeed2_125=true := by decide +kernel
#print axioms pcSeed2_125_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_126 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (23) 320), (qq (13) 180), (qq (33) 10), (qq (-14) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (30720) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_126Palette : List KBranch := pcRawSeed2_126.law.palette 0
abbrev pcSeed2_126 : OrbitSeed := pcRawSeed2_126.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_126_ok : seedOK (pcHead 1) pcSeed2_126Palette 2 pcSeedLimit pcSeed2_126=true := by decide +kernel
#print axioms pcSeed2_126_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_127 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (13) 180), (qq (3) 41), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (223560) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_127Palette : List KBranch := pcRawSeed2_127.law.palette 0
abbrev pcSeed2_127 : OrbitSeed := pcRawSeed2_127.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_127_ok : seedOK (pcHead 1) pcSeed2_127Palette 2 pcSeedLimit pcSeed2_127=true := by decide +kernel
#print axioms pcSeed2_127_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_128 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 1
  base := (⟨(qq (3) 41), (qq (69) 940), (qq (1) 1), (qq (53) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (38663) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_128Palette : List KBranch := pcRawSeed2_128.law.palette 0
abbrev pcSeed2_128 : OrbitSeed := pcRawSeed2_128.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_128_ok : seedOK (pcHead 1) pcSeed2_128Palette 2 pcSeedLimit pcSeed2_128=true := by decide +kernel
#print axioms pcSeed2_128_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_129 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (69) 940), (qq (39) 530), (qq (33) 10), (qq (-41) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (88360) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_129Palette : List KBranch := pcRawSeed2_129.law.palette 0
abbrev pcSeed2_129 : OrbitSeed := pcRawSeed2_129.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_129_ok : seedOK (pcHead 1) pcSeed2_129Palette 2 pcSeedLimit pcSeed2_129=true := by decide +kernel
#print axioms pcSeed2_129_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_130 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 2 0 0
  base := (⟨(qq (39) 530), (qq (3) 40), (qq (2) 1), (qq (4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (646070) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_130Palette : List KBranch := pcRawSeed2_130.law.palette 0
abbrev pcSeed2_130 : OrbitSeed := pcRawSeed2_130.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_130_ok : seedOK (pcHead 1) pcSeed2_130Palette 2 pcSeedLimit pcSeed2_130=true := by decide +kernel
#print axioms pcSeed2_130_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_131 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 40), (qq (13) 170), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3680) 3)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_131Palette : List KBranch := pcRawSeed2_131.law.palette 0
abbrev pcSeed2_131 : OrbitSeed := pcRawSeed2_131.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_131_ok : seedOK (pcHead 1) pcSeed2_131Palette 2 pcSeedLimit pcSeed2_131=true := by decide +kernel
#print axioms pcSeed2_131_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_132 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (13) 170), (qq (23) 300), (qq (13) 10), (qq (13) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (199410) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_132Palette : List KBranch := pcRawSeed2_132.law.palette 0
abbrev pcSeed2_132 : OrbitSeed := pcRawSeed2_132.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_132_ok : seedOK (pcHead 1) pcSeed2_132Palette 2 pcSeedLimit pcSeed2_132=true := by decide +kernel
#print axioms pcSeed2_132_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_133 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 300), (qq (1) 13), (qq (18) 5), (qq (-17) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (27000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_133Palette : List KBranch := pcRawSeed2_133.law.palette 0
abbrev pcSeed2_133 : OrbitSeed := pcRawSeed2_133.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_133_ok : seedOK (pcHead 1) pcSeed2_133Palette 2 pcSeedLimit pcSeed2_133=true := by decide +kernel
#print axioms pcSeed2_133_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_134 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 13), (qq (39) 500), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11661) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_134Palette : List KBranch := pcRawSeed2_134.law.palette 0
abbrev pcSeed2_134 : OrbitSeed := pcRawSeed2_134.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_134_ok : seedOK (pcHead 1) pcSeed2_134Palette 2 pcSeedLimit pcSeed2_134=true := by decide +kernel
#print axioms pcSeed2_134_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_135 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (39) 500), (qq (69) 880), (qq (13) 10), (qq (38) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (575000) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_135Palette : List KBranch := pcRawSeed2_135.law.palette 0
abbrev pcSeed2_135 : OrbitSeed := pcRawSeed2_135.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_135_ok : seedOK (pcHead 1) pcSeed2_135Palette 2 pcSeedLimit pcSeed2_135=true := by decide +kernel
#print axioms pcSeed2_135_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_136 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (69) 880), (qq (3) 38), (qq (18) 5), (qq (-50) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (77440) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_136Palette : List KBranch := pcRawSeed2_136.law.palette 0
abbrev pcSeed2_136 : OrbitSeed := pcRawSeed2_136.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_136_ok : seedOK (pcHead 1) pcSeed2_136Palette 2 pcSeedLimit pcSeed2_136=true := by decide +kernel
#print axioms pcSeed2_136_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_137 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 38), (qq (13) 160), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (16606) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_137Palette : List KBranch := pcRawSeed2_137.law.palette 0
abbrev pcSeed2_137 : OrbitSeed := pcRawSeed2_137.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_137_ok : seedOK (pcHead 1) pcSeed2_137Palette 2 pcSeedLimit pcSeed2_137=true := by decide +kernel
#print axioms pcSeed2_137_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_138 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (13) 160), (qq (23) 280), (qq (13) 10), (qq (12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (176640) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_138Palette : List KBranch := pcRawSeed2_138.law.palette 0
abbrev pcSeed2_138 : OrbitSeed := pcRawSeed2_138.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_138_ok : seedOK (pcHead 1) pcSeed2_138Palette 2 pcSeedLimit pcSeed2_138=true := by decide +kernel
#print axioms pcSeed2_138_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_139 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 280), (qq (39) 470), (qq (18) 5), (qq (-16) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23520) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_139Palette : List KBranch := pcRawSeed2_139.law.palette 0
abbrev pcSeed2_139 : OrbitSeed := pcRawSeed2_139.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_139_ok : seedOK (pcHead 1) pcSeed2_139Palette 2 pcSeedLimit pcSeed2_139=true := by decide +kernel
#print axioms pcSeed2_139_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_140 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (39) 470), (qq (1) 12), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (508070) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_140Palette : List KBranch := pcRawSeed2_140.law.palette 0
abbrev pcSeed2_140 : OrbitSeed := pcRawSeed2_140.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_140_ok : seedOK (pcHead 1) pcSeed2_140Palette 2 pcSeedLimit pcSeed2_140=true := by decide +kernel
#print axioms pcSeed2_140_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_141 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 2
  base := (⟨(qq (1) 12), (qq (69) 820), (qq (13) 10), (qq (35) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4968) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_141Palette : List KBranch := pcRawSeed2_141.law.palette 0
abbrev pcSeed2_141 : OrbitSeed := pcRawSeed2_141.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_141_ok : seedOK (pcHead 1) pcSeed2_141Palette 2 pcSeedLimit pcSeed2_141=true := by decide +kernel
#print axioms pcSeed2_141_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_142 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (69) 820), (qq (3) 35), (qq (18) 5), (qq (-47) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (67240) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_142Palette : List KBranch := pcRawSeed2_142.law.palette 0
abbrev pcSeed2_142 : OrbitSeed := pcRawSeed2_142.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_142_ok : seedOK (pcHead 1) pcSeed2_142Palette 2 pcSeedLimit pcSeed2_142=true := by decide +kernel
#print axioms pcSeed2_142_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_143 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 35), (qq (13) 150), (qq (13) 5), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5635) 6)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_143Palette : List KBranch := pcRawSeed2_143.law.palette 0
abbrev pcSeed2_143 : OrbitSeed := pcRawSeed2_143.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_143_ok : seedOK (pcHead 1) pcSeed2_143Palette 2 pcSeedLimit pcSeed2_143=true := by decide +kernel
#print axioms pcSeed2_143_ok


def pcRawSeeds2O005 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_120, pcRawSeed2_121, pcRawSeed2_122, pcRawSeed2_123, pcRawSeed2_124, pcRawSeed2_125, pcRawSeed2_126, pcRawSeed2_127, pcRawSeed2_128, pcRawSeed2_129, pcRawSeed2_130, pcRawSeed2_131, pcRawSeed2_132, pcRawSeed2_133, pcRawSeed2_134, pcRawSeed2_135, pcRawSeed2_136, pcRawSeed2_137, pcRawSeed2_138, pcRawSeed2_139, pcRawSeed2_140, pcRawSeed2_141, pcRawSeed2_142, pcRawSeed2_143]
theorem pcRawSeeds2O005_ok : ∀ S∈pcRawSeeds2O005,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O005,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_120_ok
  · exact pcSeed2_121_ok
  · exact pcSeed2_122_ok
  · exact pcSeed2_123_ok
  · exact pcSeed2_124_ok
  · exact pcSeed2_125_ok
  · exact pcSeed2_126_ok
  · exact pcSeed2_127_ok
  · exact pcSeed2_128_ok
  · exact pcSeed2_129_ok
  · exact pcSeed2_130_ok
  · exact pcSeed2_131_ok
  · exact pcSeed2_132_ok
  · exact pcSeed2_133_ok
  · exact pcSeed2_134_ok
  · exact pcSeed2_135_ok
  · exact pcSeed2_136_ok
  · exact pcSeed2_137_ok
  · exact pcSeed2_138_ok
  · exact pcSeed2_139_ok
  · exact pcSeed2_140_ok
  · exact pcSeed2_141_ok
  · exact pcSeed2_142_ok
  · exact pcSeed2_143_ok
#print axioms pcRawSeeds2O005_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
