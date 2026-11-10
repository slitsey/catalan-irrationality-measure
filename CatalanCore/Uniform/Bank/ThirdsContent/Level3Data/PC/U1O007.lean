module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_168 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (69) 560), (qq (1) 8), (qq (33) 10), (qq (-25) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (31360) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_168Palette : List KBranch := pcRawSeed1_168.law.palette 0
abbrev pcSeed1_168 : OrbitSeed := pcRawSeed1_168.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_168_ok : seedOK (pcHead 1) pcSeed1_168Palette 1 pcSeedLimit pcSeed1_168=true := by decide +kernel
#print axioms pcSeed1_168_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_169 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 8), (qq (39) 310), (qq (23) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2208) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_169Palette : List KBranch := pcRawSeed1_169.law.palette 0
abbrev pcSeed1_169 : OrbitSeed := pcRawSeed1_169.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_169_ok : seedOK (pcHead 1) pcSeed1_169Palette 1 pcSeedLimit pcSeed1_169=true := by decide +kernel
#print axioms pcSeed1_169_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_170 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (39) 310), (qq (23) 180), (qq (1) 1), (qq (10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (221030) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_170Palette : List KBranch := pcRawSeed1_170.law.palette 0
abbrev pcSeed1_170 : OrbitSeed := pcRawSeed1_170.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_170_ok : seedOK (pcHead 1) pcSeed1_170Palette 1 pcSeedLimit pcSeed1_170=true := by decide +kernel
#print axioms pcSeed1_170_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_171 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 180), (qq (13) 100), (qq (33) 10), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9720) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_171Palette : List KBranch := pcRawSeed1_171.law.palette 0
abbrev pcSeed1_171 : OrbitSeed := pcRawSeed1_171.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_171_ok : seedOK (pcHead 1) pcSeed1_171Palette 1 pcSeedLimit pcSeed1_171=true := by decide +kernel
#print axioms pcSeed1_171_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_172 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (13) 100), (qq (3) 22), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (69000) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_172Palette : List KBranch := pcRawSeed1_172.law.palette 0
abbrev pcSeed1_172 : OrbitSeed := pcRawSeed1_172.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_172_ok : seedOK (pcHead 1) pcSeed1_172Palette 1 pcSeedLimit pcSeed1_172=true := by decide +kernel
#print axioms pcSeed1_172_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_173 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (3) 22), (qq (69) 500), (qq (1) 1), (qq (28) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5566) 15)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_173Palette : List KBranch := pcRawSeed1_173.law.palette 0
abbrev pcSeed1_173 : OrbitSeed := pcRawSeed1_173.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_173_ok : seedOK (pcHead 1) pcSeed1_173Palette 1 pcSeedLimit pcSeed1_173=true := by decide +kernel
#print axioms pcSeed1_173_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_174 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (69) 500), (qq (39) 280), (qq (33) 10), (qq (-22) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (25000) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_174Palette : List KBranch := pcRawSeed1_174.law.palette 0
abbrev pcSeed1_174 : OrbitSeed := pcRawSeed1_174.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_174_ok : seedOK (pcHead 1) pcSeed1_174Palette 1 pcSeedLimit pcSeed1_174=true := by decide +kernel
#print axioms pcSeed1_174_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_175 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (39) 280), (qq (1) 7), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (180320) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_175Palette : List KBranch := pcRawSeed1_175.law.palette 0
abbrev pcSeed1_175 : OrbitSeed := pcRawSeed1_175.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_175_ok : seedOK (pcHead 1) pcSeed1_175Palette 1 pcSeedLimit pcSeed1_175=true := by decide +kernel
#print axioms pcSeed1_175_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_176 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 7), (qq (23) 160), (qq (1) 1), (qq (9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3381) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_176Palette : List KBranch := pcRawSeed1_176.law.palette 0
abbrev pcSeed1_176 : OrbitSeed := pcRawSeed1_176.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_176_ok : seedOK (pcHead 1) pcSeed1_176Palette 1 pcSeedLimit pcSeed1_176=true := by decide +kernel
#print axioms pcSeed1_176_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_177 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 160), (qq (13) 90), (qq (33) 10), (qq (-7) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7680) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_177Palette : List KBranch := pcRawSeed1_177.law.palette 0
abbrev pcSeed1_177 : OrbitSeed := pcRawSeed1_177.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_177_ok : seedOK (pcHead 1) pcSeed1_177Palette 1 pcSeedLimit pcSeed1_177=true := by decide +kernel
#print axioms pcSeed1_177_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_178 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (13) 90), (qq (3) 20), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (55890) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed1_178Palette : List KBranch := pcRawSeed1_178.law.palette 0
abbrev pcSeed1_178 : OrbitSeed := pcRawSeed1_178.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_178_ok : seedOK (pcHead 1) pcSeed1_178Palette 1 pcSeedLimit pcSeed1_178=true := by decide +kernel
#print axioms pcSeed1_178_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_179 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩]
  base := (⟨(qq (23) 80), (qq (599997) 2000000), (qq (19) 4), (qq (-9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (4000000) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_179Palette : List KBranch := pcRawSeed1_179.law.palette 0
abbrev pcSeed1_179 : OrbitSeed := pcRawSeed1_179.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_179_ok : seedOK (pcHead 1) pcSeed1_179Palette 1 pcSeedLimit pcSeed1_179=true := by decide +kernel
#print axioms pcSeed1_179_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_180 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨65,by decide +kernel⟩, ⟨10,by decide +kernel⟩]
  base := (⟨(qq (599997) 2000000), (qq (3) 10), (qq (-399903) 20), (qq (199973) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (3) 2000000), (qq (2) 1)⟩], (qq (4000000) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_180Palette : List KBranch := pcRawSeed1_180.law.palette 0
abbrev pcSeed1_180 : OrbitSeed := pcRawSeed1_180.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_180_ok : seedOK (pcHead 1) pcSeed1_180Palette 1 pcSeedLimit pcSeed1_180=true := by decide +kernel
#print axioms pcSeed1_180_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_181 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (69) 80), (qq (1) 1), (qq (89) 20), (qq (-8) 3), (qq (1000000000000) 1)⟩, ⟨0, [(qq (39) 40)], [], (qq (640) 69)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_181Palette : List KBranch := pcRawSeed1_181.law.palette 0
abbrev pcSeed1_181 : OrbitSeed := pcRawSeed1_181.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_181_ok : seedOK (pcHead 1) pcSeed1_181Palette 1 pcSeedLimit pcSeed1_181=true := by decide +kernel
#print axioms pcSeed1_181_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_182 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (23) 20), (qq (49) 20), (qq (-2) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (3) 20), (qq (3) 2)⟩], (qq (20) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_182Palette : List KBranch := pcRawSeed1_182.law.palette 0
abbrev pcSeed1_182 : OrbitSeed := pcRawSeed1_182.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_182_ok : seedOK (pcHead 1) pcSeed1_182Palette 1 pcSeedLimit pcSeed1_182=true := by decide +kernel
#print axioms pcSeed1_182_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_183 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (23) 20), (qq (13) 10), (qq (18) 5), (qq (-5) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_183Palette : List KBranch := pcRawSeed1_183.law.palette 0
abbrev pcSeed1_183 : OrbitSeed := pcRawSeed1_183.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_183_ok : seedOK (pcHead 1) pcSeed1_183Palette 1 pcSeedLimit pcSeed1_183=true := by decide +kernel
#print axioms pcSeed1_183_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_184 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (13) 10), (qq (3) 1), (qq (23) 10), (qq (-2) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (690) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_184Palette : List KBranch := pcRawSeed1_184.law.palette 0
abbrev pcSeed1_184 : OrbitSeed := pcRawSeed1_184.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_184_ok : seedOK (pcHead 1) pcSeed1_184Palette 1 pcSeedLimit pcSeed1_184=true := by decide +kernel
#print axioms pcSeed1_184_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_185 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (3) 1), (qq (39) 10), (qq (13) 10), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (5) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_185Palette : List KBranch := pcRawSeed1_185.law.palette 0
abbrev pcSeed1_185 : OrbitSeed := pcRawSeed1_185.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_185_ok : seedOK (pcHead 1) pcSeed1_185Palette 1 pcSeedLimit pcSeed1_185=true := by decide +kernel
#print axioms pcSeed1_185_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_186 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (39) 10), (qq (49) 10), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20) 9)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_186Palette : List KBranch := pcRawSeed1_186.law.palette 0
abbrev pcSeed1_186 : OrbitSeed := pcRawSeed1_186.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_186_ok : seedOK (pcHead 1) pcSeed1_186Palette 1 pcSeedLimit pcSeed1_186=true := by decide +kernel
#print axioms pcSeed1_186_ok


def pcRawSeeds1O007 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_168, pcRawSeed1_169, pcRawSeed1_170, pcRawSeed1_171, pcRawSeed1_172, pcRawSeed1_173, pcRawSeed1_174, pcRawSeed1_175, pcRawSeed1_176, pcRawSeed1_177, pcRawSeed1_178, pcRawSeed1_179, pcRawSeed1_180, pcRawSeed1_181, pcRawSeed1_182, pcRawSeed1_183, pcRawSeed1_184, pcRawSeed1_185, pcRawSeed1_186]
theorem pcRawSeeds1O007_ok : ∀ S∈pcRawSeeds1O007,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O007,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_168_ok
  · exact pcSeed1_169_ok
  · exact pcSeed1_170_ok
  · exact pcSeed1_171_ok
  · exact pcSeed1_172_ok
  · exact pcSeed1_173_ok
  · exact pcSeed1_174_ok
  · exact pcSeed1_175_ok
  · exact pcSeed1_176_ok
  · exact pcSeed1_177_ok
  · exact pcSeed1_178_ok
  · exact pcSeed1_179_ok
  · exact pcSeed1_180_ok
  · exact pcSeed1_181_ok
  · exact pcSeed1_182_ok
  · exact pcSeed1_183_ok
  · exact pcSeed1_184_ok
  · exact pcSeed1_185_ok
  · exact pcSeed1_186_ok
#print axioms pcRawSeeds1O007_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
