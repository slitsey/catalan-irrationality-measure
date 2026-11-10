module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_144 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (13) 150), (qq (3) 34), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (155250) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_144Palette : List KBranch := pcRawSeed1_144.law.palette 0
abbrev pcSeed1_144 : OrbitSeed := pcRawSeed1_144.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_144_ok : seedOK (pcHead 1) pcSeed1_144Palette 1 pcSeedLimit pcSeed1_144=true := by decide +kernel
#print axioms pcSeed1_144_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_145 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (3) 34), (qq (23) 260), (qq (13) 10), (qq (11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (13294) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_145Palette : List KBranch := pcRawSeed1_145.law.palette 0
abbrev pcSeed1_145 : OrbitSeed := pcRawSeed1_145.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_145_ok : seedOK (pcHead 1) pcSeed1_145Palette 1 pcSeedLimit pcSeed1_145=true := by decide +kernel
#print axioms pcSeed1_145_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_146 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 260), (qq (9) 100), (qq (18) 5), (qq (-15) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20280) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_146Palette : List KBranch := pcRawSeed1_146.law.palette 0
abbrev pcSeed1_146 : OrbitSeed := pcRawSeed1_146.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_146_ok : seedOK (pcHead 1) pcSeed1_146Palette 1 pcSeedLimit pcSeed1_146=true := by decide +kernel
#print axioms pcSeed1_146_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_147 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (9) 100), (qq (39) 430), (qq (15) 4), (qq (-50) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23000) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_147Palette : List KBranch := pcRawSeed1_147.law.palette 0
abbrev pcSeed1_147 : OrbitSeed := pcRawSeed1_147.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_147_ok : seedOK (pcHead 1) pcSeed1_147Palette 1 pcSeedLimit pcSeed1_147=true := by decide +kernel
#print axioms pcSeed1_147_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_148 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (39) 430), (qq (1) 11), (qq (49) 20), (qq (-7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (425270) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_148Palette : List KBranch := pcRawSeed1_148.law.palette 0
abbrev pcSeed1_148 : OrbitSeed := pcRawSeed1_148.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_148_ok : seedOK (pcHead 1) pcSeed1_148Palette 1 pcSeedLimit pcSeed1_148=true := by decide +kernel
#print axioms pcSeed1_148_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_149 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 11), (qq (13) 140), (qq (29) 20), (qq (26) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8349) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_149Palette : List KBranch := pcRawSeed1_149.law.palette 0
abbrev pcSeed1_149 : OrbitSeed := pcRawSeed1_149.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_149_ok : seedOK (pcHead 1) pcSeed1_149Palette 1 pcSeedLimit pcSeed1_149=true := by decide +kernel
#print axioms pcSeed1_149_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_150 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (13) 140), (qq (69) 740), (qq (3) 20), (qq (68) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (135240) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_150Palette : List KBranch := pcRawSeed1_150.law.palette 0
abbrev pcSeed1_150 : OrbitSeed := pcRawSeed1_150.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_150_ok : seedOK (pcHead 1) pcSeed1_150Palette 1 pcSeedLimit pcSeed1_150=true := by decide +kernel
#print axioms pcSeed1_150_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_151 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 740), (qq (23) 240), (qq (49) 20), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (54760) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_151Palette : List KBranch := pcRawSeed1_151.law.palette 0
abbrev pcSeed1_151 : OrbitSeed := pcRawSeed1_151.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_151_ok : seedOK (pcHead 1) pcSeed1_151Palette 1 pcSeedLimit pcSeed1_151=true := by decide +kernel
#print axioms pcSeed1_151_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_152 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (23) 240), (qq (3) 31), (qq (19) 4), (qq (-26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (17280) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_152Palette : List KBranch := pcRawSeed1_152.law.palette 0
abbrev pcSeed1_152 : OrbitSeed := pcRawSeed1_152.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_152_ok : seedOK (pcHead 1) pcSeed1_152Palette 1 pcSeedLimit pcSeed1_152=true := by decide +kernel
#print axioms pcSeed1_152_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_153 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (3) 31), (qq (39) 400), (qq (15) 4), (qq (-47) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (22103) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_153Palette : List KBranch := pcRawSeed1_153.law.palette 0
abbrev pcSeed1_153 : OrbitSeed := pcRawSeed1_153.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_153_ok : seedOK (pcHead 1) pcSeed1_153Palette 1 pcSeedLimit pcSeed1_153=true := by decide +kernel
#print axioms pcSeed1_153_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_154 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (39) 400), (qq (1) 10), (qq (49) 20), (qq (-7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (368000) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_154Palette : List KBranch := pcRawSeed1_154.law.palette 0
abbrev pcSeed1_154 : OrbitSeed := pcRawSeed1_154.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_154_ok : seedOK (pcHead 1) pcSeed1_154Palette 1 pcSeedLimit pcSeed1_154=true := by decide +kernel
#print axioms pcSeed1_154_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_155 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 10), (qq (69) 680), (qq (-3) 20), (qq (71) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (690) 1)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_155Palette : List KBranch := pcRawSeed1_155.law.palette 0
abbrev pcSeed1_155 : OrbitSeed := pcRawSeed1_155.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_155_ok : seedOK (pcHead 1) pcSeed1_155Palette 1 pcSeedLimit pcSeed1_155=true := by decide +kernel
#print axioms pcSeed1_155_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_156 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 680), (qq (23) 220), (qq (43) 20), (qq (1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (46240) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_156Palette : List KBranch := pcRawSeed1_156.law.palette 0
abbrev pcSeed1_156 : OrbitSeed := pcRawSeed1_156.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_156_ok : seedOK (pcHead 1) pcSeed1_156Palette 1 pcSeedLimit pcSeed1_156=true := by decide +kernel
#print axioms pcSeed1_156_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_157 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (23) 220), (qq (39) 370), (qq (89) 20), (qq (-21) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14520) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_157Palette : List KBranch := pcRawSeed1_157.law.palette 0
abbrev pcSeed1_157 : OrbitSeed := pcRawSeed1_157.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_157_ok : seedOK (pcHead 1) pcSeed1_157Palette 1 pcSeedLimit pcSeed1_157=true := by decide +kernel
#print axioms pcSeed1_157_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_158 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (39) 370), (qq (3) 28), (qq (63) 20), (qq (-26) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (314870) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_158Palette : List KBranch := pcRawSeed1_158.law.palette 0
abbrev pcSeed1_158 : OrbitSeed := pcRawSeed1_158.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_158_ok : seedOK (pcHead 1) pcSeed1_158Palette 1 pcSeedLimit pcSeed1_158=true := by decide +kernel
#print axioms pcSeed1_158_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_159 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (3) 28), (qq (13) 120), (qq (43) 20), (qq (2) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9016) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_159Palette : List KBranch := pcRawSeed1_159.law.palette 0
abbrev pcSeed1_159 : OrbitSeed := pcRawSeed1_159.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_159_ok : seedOK (pcHead 1) pcSeed1_159Palette 1 pcSeedLimit pcSeed1_159=true := by decide +kernel
#print axioms pcSeed1_159_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_160 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (13) 120), (qq (1) 9), (qq (17) 20), (qq (38) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (99360) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_160Palette : List KBranch := pcRawSeed1_160.law.palette 0
abbrev pcSeed1_160 : OrbitSeed := pcRawSeed1_160.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_160_ok : seedOK (pcHead 1) pcSeed1_160Palette 1 pcSeedLimit pcSeed1_160=true := by decide +kernel
#print axioms pcSeed1_160_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_161 : CatalogueSeed pcLegacyCatalogue where
  law := .wrap 1 (by decide +kernel)
  base := (⟨(qq (1) 9), (qq (69) 620), (qq (-3) 20), (qq (65) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5589) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_161Palette : List KBranch := pcRawSeed1_161.law.palette 0
abbrev pcSeed1_161 : OrbitSeed := pcRawSeed1_161.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_161_ok : seedOK (pcHead 1) pcSeed1_161Palette 1 pcSeedLimit pcSeed1_161=true := by decide +kernel
#print axioms pcSeed1_161_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_162 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (69) 620), (qq (9) 80), (qq (43) 20), (qq (1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (38440) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_162Palette : List KBranch := pcRawSeed1_162.law.palette 0
abbrev pcSeed1_162 : OrbitSeed := pcRawSeed1_162.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_162_ok : seedOK (pcHead 1) pcSeed1_162Palette 1 pcSeedLimit pcSeed1_162=true := by decide +kernel
#print axioms pcSeed1_162_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_163 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (9) 80), (qq (39) 340), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (14720) 27)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_163Palette : List KBranch := pcRawSeed1_163.law.palette 0
abbrev pcSeed1_163 : OrbitSeed := pcRawSeed1_163.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_163_ok : seedOK (pcHead 1) pcSeed1_163Palette 1 pcSeedLimit pcSeed1_163=true := by decide +kernel
#print axioms pcSeed1_163_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_164 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (39) 340), (qq (23) 200), (qq (1) 1), (qq (11) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (265880) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_164Palette : List KBranch := pcRawSeed1_164.law.palette 0
abbrev pcSeed1_164 : OrbitSeed := pcRawSeed1_164.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_164_ok : seedOK (pcHead 1) pcSeed1_164Palette 1 pcSeedLimit pcSeed1_164=true := by decide +kernel
#print axioms pcSeed1_164_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_165 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 200), (qq (13) 110), (qq (33) 10), (qq (-9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12000) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_165Palette : List KBranch := pcRawSeed1_165.law.palette 0
abbrev pcSeed1_165 : OrbitSeed := pcRawSeed1_165.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_165_ok : seedOK (pcHead 1) pcSeed1_165Palette 1 pcSeedLimit pcSeed1_165=true := by decide +kernel
#print axioms pcSeed1_165_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_166 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (13) 110), (qq (3) 25), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (83490) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_166Palette : List KBranch := pcRawSeed1_166.law.palette 0
abbrev pcSeed1_166 : OrbitSeed := pcRawSeed1_166.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_166_ok : seedOK (pcHead 1) pcSeed1_166Palette 1 pcSeedLimit pcSeed1_166=true := by decide +kernel
#print axioms pcSeed1_166_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_167 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (3) 25), (qq (69) 560), (qq (1) 1), (qq (31) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2875) 6)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_167Palette : List KBranch := pcRawSeed1_167.law.palette 0
abbrev pcSeed1_167 : OrbitSeed := pcRawSeed1_167.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_167_ok : seedOK (pcHead 1) pcSeed1_167Palette 1 pcSeedLimit pcSeed1_167=true := by decide +kernel
#print axioms pcSeed1_167_ok


def pcRawSeeds1O006 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_144, pcRawSeed1_145, pcRawSeed1_146, pcRawSeed1_147, pcRawSeed1_148, pcRawSeed1_149, pcRawSeed1_150, pcRawSeed1_151, pcRawSeed1_152, pcRawSeed1_153, pcRawSeed1_154, pcRawSeed1_155, pcRawSeed1_156, pcRawSeed1_157, pcRawSeed1_158, pcRawSeed1_159, pcRawSeed1_160, pcRawSeed1_161, pcRawSeed1_162, pcRawSeed1_163, pcRawSeed1_164, pcRawSeed1_165, pcRawSeed1_166, pcRawSeed1_167]
theorem pcRawSeeds1O006_ok : ∀ S∈pcRawSeeds1O006,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O006,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_144_ok
  · exact pcSeed1_145_ok
  · exact pcSeed1_146_ok
  · exact pcSeed1_147_ok
  · exact pcSeed1_148_ok
  · exact pcSeed1_149_ok
  · exact pcSeed1_150_ok
  · exact pcSeed1_151_ok
  · exact pcSeed1_152_ok
  · exact pcSeed1_153_ok
  · exact pcSeed1_154_ok
  · exact pcSeed1_155_ok
  · exact pcSeed1_156_ok
  · exact pcSeed1_157_ok
  · exact pcSeed1_158_ok
  · exact pcSeed1_159_ok
  · exact pcSeed1_160_ok
  · exact pcSeed1_161_ok
  · exact pcSeed1_162_ok
  · exact pcSeed1_163_ok
  · exact pcSeed1_164_ok
  · exact pcSeed1_165_ok
  · exact pcSeed1_166_ok
  · exact pcSeed1_167_ok
#print axioms pcRawSeeds1O006_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
