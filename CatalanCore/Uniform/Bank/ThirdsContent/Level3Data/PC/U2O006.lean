module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_144 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (13) 150), (qq (23) 260), (qq (13) 10), (qq (11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (155250) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_144Palette : List KBranch := pcRawSeed2_144.law.palette 0
abbrev pcSeed2_144 : OrbitSeed := pcRawSeed2_144.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_144_ok : seedOK (pcHead 1) pcSeed2_144Palette 2 pcSeedLimit pcSeed2_144=true := by decide +kernel
#print axioms pcSeed2_144_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_145 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 260), (qq (39) 440), (qq (18) 5), (qq (-15) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20280) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_145Palette : List KBranch := pcRawSeed2_145.law.palette 0
abbrev pcSeed2_145 : OrbitSeed := pcRawSeed2_145.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_145_ok : seedOK (pcHead 1) pcSeed2_145Palette 2 pcSeedLimit pcSeed2_145=true := by decide +kernel
#print axioms pcSeed2_145_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_146 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (39) 440), (qq (9) 100), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (445280) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_146Palette : List KBranch := pcRawSeed2_146.law.palette 0
abbrev pcSeed2_146 : OrbitSeed := pcRawSeed2_146.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_146_ok : seedOK (pcHead 1) pcSeed2_146Palette 2 pcSeedLimit pcSeed2_146=true := by decide +kernel
#print axioms pcSeed2_146_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_147 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (9) 100), (qq (69) 760), (qq (49) 20), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23000) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_147Palette : List KBranch := pcRawSeed2_147.law.palette 0
abbrev pcSeed2_147 : OrbitSeed := pcRawSeed2_147.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_147_ok : seedOK (pcHead 1) pcSeed2_147Palette 2 pcSeedLimit pcSeed2_147=true := by decide +kernel
#print axioms pcSeed2_147_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_148 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (69) 760), (qq (1) 11), (qq (19) 4), (qq (-82) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (57760) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_148Palette : List KBranch := pcRawSeed2_148.law.palette 0
abbrev pcSeed2_148 : OrbitSeed := pcRawSeed2_148.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_148_ok : seedOK (pcHead 1) pcSeed2_148Palette 2 pcSeedLimit pcSeed2_148=true := by decide +kernel
#print axioms pcSeed2_148_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_149 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 11), (qq (13) 140), (qq (15) 4), (qq (-49) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8349) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_149Palette : List KBranch := pcRawSeed2_149.law.palette 0
abbrev pcSeed2_149 : OrbitSeed := pcRawSeed2_149.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_149_ok : seedOK (pcHead 1) pcSeed2_149Palette 2 pcSeedLimit pcSeed2_149=true := by decide +kernel
#print axioms pcSeed2_149_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_150 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (13) 140), (qq (3) 32), (qq (49) 20), (qq (-7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (135240) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_150Palette : List KBranch := pcRawSeed2_150.law.palette 0
abbrev pcSeed2_150 : OrbitSeed := pcRawSeed2_150.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_150_ok : seedOK (pcHead 1) pcSeed2_150Palette 2 pcSeedLimit pcSeed2_150=true := by decide +kernel
#print axioms pcSeed2_150_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_151 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (3) 32), (qq (39) 410), (qq (29) 20), (qq (25) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (11776) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_151Palette : List KBranch := pcRawSeed2_151.law.palette 0
abbrev pcSeed2_151 : OrbitSeed := pcRawSeed2_151.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_151_ok : seedOK (pcHead 1) pcSeed2_151Palette 2 pcSeedLimit pcSeed2_151=true := by decide +kernel
#print axioms pcSeed2_151_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_152 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (39) 410), (qq (23) 240), (qq (3) 20), (qq (22) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (386630) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_152Palette : List KBranch := pcRawSeed2_152.law.palette 0
abbrev pcSeed2_152 : OrbitSeed := pcRawSeed2_152.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_152_ok : seedOK (pcHead 1) pcSeed2_152Palette 2 pcSeedLimit pcSeed2_152=true := by decide +kernel
#print axioms pcSeed2_152_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_153 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 240), (qq (69) 700), (qq (49) 20), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17280) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_153Palette : List KBranch := pcRawSeed2_153.law.palette 0
abbrev pcSeed2_153 : OrbitSeed := pcRawSeed2_153.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_153_ok : seedOK (pcHead 1) pcSeed2_153Palette 2 pcSeedLimit pcSeed2_153=true := by decide +kernel
#print axioms pcSeed2_153_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_154 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (69) 700), (qq (1) 10), (qq (19) 4), (qq (-76) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (49000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_154Palette : List KBranch := pcRawSeed2_154.law.palette 0
abbrev pcSeed2_154 : OrbitSeed := pcRawSeed2_154.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_154_ok : seedOK (pcHead 1) pcSeed2_154Palette 2 pcSeedLimit pcSeed2_154=true := by decide +kernel
#print axioms pcSeed2_154_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_155 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 10), (qq (39) 380), (qq (43) 20), (qq (2) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (690) 1)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_155Palette : List KBranch := pcRawSeed2_155.law.palette 0
abbrev pcSeed2_155 : OrbitSeed := pcRawSeed2_155.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_155_ok : seedOK (pcHead 1) pcSeed2_155Palette 2 pcSeedLimit pcSeed2_155=true := by decide +kernel
#print axioms pcSeed2_155_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_156 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (39) 380), (qq (3) 29), (qq (17) 20), (qq (40) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (332120) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_156Palette : List KBranch := pcRawSeed2_156.law.palette 0
abbrev pcSeed2_156 : OrbitSeed := pcRawSeed2_156.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_156_ok : seedOK (pcHead 1) pcSeed2_156Palette 2 pcSeedLimit pcSeed2_156=true := by decide +kernel
#print axioms pcSeed2_156_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_157 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (3) 29), (qq (23) 220), (qq (-3) 20), (qq (23) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (19343) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_157Palette : List KBranch := pcRawSeed2_157.law.palette 0
abbrev pcSeed2_157 : OrbitSeed := pcRawSeed2_157.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_157_ok : seedOK (pcHead 1) pcSeed2_157Palette 2 pcSeedLimit pcSeed2_157=true := by decide +kernel
#print axioms pcSeed2_157_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_158 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 220), (qq (69) 640), (qq (43) 20), (qq (1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14520) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_158Palette : List KBranch := pcRawSeed2_158.law.palette 0
abbrev pcSeed2_158 : OrbitSeed := pcRawSeed2_158.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_158_ok : seedOK (pcHead 1) pcSeed2_158Palette 2 pcSeedLimit pcSeed2_158=true := by decide +kernel
#print axioms pcSeed2_158_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_159 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (69) 640), (qq (13) 120), (qq (89) 20), (qq (-61) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (40960) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_159Palette : List KBranch := pcRawSeed2_159.law.palette 0
abbrev pcSeed2_159 : OrbitSeed := pcRawSeed2_159.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_159_ok : seedOK (pcHead 1) pcSeed2_159Palette 2 pcSeedLimit pcSeed2_159=true := by decide +kernel
#print axioms pcSeed2_159_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_160 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (13) 120), (qq (1) 9), (qq (63) 20), (qq (-25) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (99360) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_160Palette : List KBranch := pcRawSeed2_160.law.palette 0
abbrev pcSeed2_160 : OrbitSeed := pcRawSeed2_160.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_160_ok : seedOK (pcHead 1) pcSeed2_160Palette 2 pcSeedLimit pcSeed2_160=true := by decide +kernel
#print axioms pcSeed2_160_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_161 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 9), (qq (39) 350), (qq (43) 20), (qq (2) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5589) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_161Palette : List KBranch := pcRawSeed2_161.law.palette 0
abbrev pcSeed2_161 : OrbitSeed := pcRawSeed2_161.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_161_ok : seedOK (pcHead 1) pcSeed2_161Palette 2 pcSeedLimit pcSeed2_161=true := by decide +kernel
#print axioms pcSeed2_161_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_162 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (39) 350), (qq (9) 80), (qq (17) 20), (qq (37) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (281750) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_162Palette : List KBranch := pcRawSeed2_162.law.palette 0
abbrev pcSeed2_162 : OrbitSeed := pcRawSeed2_162.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_162_ok : seedOK (pcHead 1) pcSeed2_162Palette 2 pcSeedLimit pcSeed2_162=true := by decide +kernel
#print axioms pcSeed2_162_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_163 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (9) 80), (qq (23) 200), (qq (1) 1), (qq (11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14720) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_163Palette : List KBranch := pcRawSeed2_163.law.palette 0
abbrev pcSeed2_163 : OrbitSeed := pcRawSeed2_163.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_163_ok : seedOK (pcHead 1) pcSeed2_163Palette 2 pcSeedLimit pcSeed2_163=true := by decide +kernel
#print axioms pcSeed2_163_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_164 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 200), (qq (3) 26), (qq (33) 10), (qq (-9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_164Palette : List KBranch := pcRawSeed2_164.law.palette 0
abbrev pcSeed2_164 : OrbitSeed := pcRawSeed2_164.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_164_ok : seedOK (pcHead 1) pcSeed2_164Palette 2 pcSeedLimit pcSeed2_164=true := by decide +kernel
#print axioms pcSeed2_164_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_165 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (3) 26), (qq (13) 110), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7774) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_165Palette : List KBranch := pcRawSeed2_165.law.palette 0
abbrev pcSeed2_165 : OrbitSeed := pcRawSeed2_165.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_165_ok : seedOK (pcHead 1) pcSeed2_165Palette 2 pcSeedLimit pcSeed2_165=true := by decide +kernel
#print axioms pcSeed2_165_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_166 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (13) 110), (qq (69) 580), (qq (1) 1), (qq (32) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (83490) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_166Palette : List KBranch := pcRawSeed2_166.law.palette 0
abbrev pcSeed2_166 : OrbitSeed := pcRawSeed2_166.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_166_ok : seedOK (pcHead 1) pcSeed2_166Palette 2 pcSeedLimit pcSeed2_166=true := by decide +kernel
#print axioms pcSeed2_166_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_167 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (69) 580), (qq (39) 320), (qq (33) 10), (qq (-26) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (33640) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_167Palette : List KBranch := pcRawSeed2_167.law.palette 0
abbrev pcSeed2_167 : OrbitSeed := pcRawSeed2_167.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_167_ok : seedOK (pcHead 1) pcSeed2_167Palette 2 pcSeedLimit pcSeed2_167=true := by decide +kernel
#print axioms pcSeed2_167_ok


def pcRawSeeds2O006 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_144, pcRawSeed2_145, pcRawSeed2_146, pcRawSeed2_147, pcRawSeed2_148, pcRawSeed2_149, pcRawSeed2_150, pcRawSeed2_151, pcRawSeed2_152, pcRawSeed2_153, pcRawSeed2_154, pcRawSeed2_155, pcRawSeed2_156, pcRawSeed2_157, pcRawSeed2_158, pcRawSeed2_159, pcRawSeed2_160, pcRawSeed2_161, pcRawSeed2_162, pcRawSeed2_163, pcRawSeed2_164, pcRawSeed2_165, pcRawSeed2_166, pcRawSeed2_167]
theorem pcRawSeeds2O006_ok : ∀ S∈pcRawSeeds2O006,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O006,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_144_ok
  · exact pcSeed2_145_ok
  · exact pcSeed2_146_ok
  · exact pcSeed2_147_ok
  · exact pcSeed2_148_ok
  · exact pcSeed2_149_ok
  · exact pcSeed2_150_ok
  · exact pcSeed2_151_ok
  · exact pcSeed2_152_ok
  · exact pcSeed2_153_ok
  · exact pcSeed2_154_ok
  · exact pcSeed2_155_ok
  · exact pcSeed2_156_ok
  · exact pcSeed2_157_ok
  · exact pcSeed2_158_ok
  · exact pcSeed2_159_ok
  · exact pcSeed2_160_ok
  · exact pcSeed2_161_ok
  · exact pcSeed2_162_ok
  · exact pcSeed2_163_ok
  · exact pcSeed2_164_ok
  · exact pcSeed2_165_ok
  · exact pcSeed2_166_ok
  · exact pcSeed2_167_ok
#print axioms pcRawSeeds2O006_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
