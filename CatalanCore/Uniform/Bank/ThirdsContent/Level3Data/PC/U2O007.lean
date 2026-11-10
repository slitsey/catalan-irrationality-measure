module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_168 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (39) 320), (qq (1) 8), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (235520) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_168Palette : List KBranch := pcRawSeed2_168.law.palette 0
abbrev pcSeed2_168 : OrbitSeed := pcRawSeed2_168.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_168_ok : seedOK (pcHead 1) pcSeed2_168Palette 2 pcSeedLimit pcSeed2_168=true := by decide +kernel
#print axioms pcSeed2_168_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_169 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 8), (qq (23) 180), (qq (1) 1), (qq (10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2208) 5)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_169Palette : List KBranch := pcRawSeed2_169.law.palette 0
abbrev pcSeed2_169 : OrbitSeed := pcRawSeed2_169.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_169_ok : seedOK (pcHead 1) pcSeed2_169Palette 2 pcSeedLimit pcSeed2_169=true := by decide +kernel
#print axioms pcSeed2_169_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_170 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 180), (qq (13) 100), (qq (33) 10), (qq (-8) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9720) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_170Palette : List KBranch := pcRawSeed2_170.law.palette 0
abbrev pcSeed2_170 : OrbitSeed := pcRawSeed2_170.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_170_ok : seedOK (pcHead 1) pcSeed2_170Palette 2 pcSeedLimit pcSeed2_170=true := by decide +kernel
#print axioms pcSeed2_170_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_171 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (13) 100), (qq (3) 23), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (69000) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_171Palette : List KBranch := pcRawSeed2_171.law.palette 0
abbrev pcSeed2_171 : OrbitSeed := pcRawSeed2_171.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_171_ok : seedOK (pcHead 1) pcSeed2_171Palette 2 pcSeedLimit pcSeed2_171=true := by decide +kernel
#print axioms pcSeed2_171_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_172 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (3) 23), (qq (69) 520), (qq (1) 1), (qq (29) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (12167) 30)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_172Palette : List KBranch := pcRawSeed2_172.law.palette 0
abbrev pcSeed2_172 : OrbitSeed := pcRawSeed2_172.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_172_ok : seedOK (pcHead 1) pcSeed2_172Palette 2 pcSeedLimit pcSeed2_172=true := by decide +kernel
#print axioms pcSeed2_172_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_173 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (69) 520), (qq (39) 290), (qq (33) 10), (qq (-23) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (27040) 69)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_173Palette : List KBranch := pcRawSeed2_173.law.palette 0
abbrev pcSeed2_173 : OrbitSeed := pcRawSeed2_173.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_173_ok : seedOK (pcHead 1) pcSeed2_173Palette 2 pcSeedLimit pcSeed2_173=true := by decide +kernel
#print axioms pcSeed2_173_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_174 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (39) 290), (qq (1) 7), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (193430) 507)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_174Palette : List KBranch := pcRawSeed2_174.law.palette 0
abbrev pcSeed2_174 : OrbitSeed := pcRawSeed2_174.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_174_ok : seedOK (pcHead 1) pcSeed2_174Palette 2 pcSeedLimit pcSeed2_174=true := by decide +kernel
#print axioms pcSeed2_174_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_175 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 7), (qq (23) 160), (qq (1) 1), (qq (9) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3381) 10)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_175Palette : List KBranch := pcRawSeed2_175.law.palette 0
abbrev pcSeed2_175 : OrbitSeed := pcRawSeed2_175.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_175_ok : seedOK (pcHead 1) pcSeed2_175Palette 2 pcSeedLimit pcSeed2_175=true := by decide +kernel
#print axioms pcSeed2_175_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_176 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (23) 160), (qq (13) 90), (qq (33) 10), (qq (-7) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (7680) 23)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_176Palette : List KBranch := pcRawSeed2_176.law.palette 0
abbrev pcSeed2_176 : OrbitSeed := pcRawSeed2_176.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_176_ok : seedOK (pcHead 1) pcSeed2_176Palette 2 pcSeedLimit pcSeed2_176=true := by decide +kernel
#print axioms pcSeed2_176_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_177 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (13) 90), (qq (3) 20), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (55890) 169)⟩)
  N := 7
  times := [0, 1, 2, 3, 4, 5, 6, 7]
abbrev pcSeed2_177Palette : List KBranch := pcRawSeed2_177.law.palette 0
abbrev pcSeed2_177 : OrbitSeed := pcRawSeed2_177.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=8 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_177_ok : seedOK (pcHead 1) pcSeed2_177Palette 2 pcSeedLimit pcSeed2_177=true := by decide +kernel
#print axioms pcSeed2_177_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_178 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (23) 80), (qq (599997) 2000000), (qq (49) 20), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1920) 23)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_178Palette : List KBranch := pcRawSeed2_178.law.palette 0
abbrev pcSeed2_178 : OrbitSeed := pcRawSeed2_178.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_178_ok : seedOK (pcHead 1) pcSeed2_178Palette 2 pcSeedLimit pcSeed2_178=true := by decide +kernel
#print axioms pcSeed2_178_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_179 : CatalogueSeed pcLegacyCatalogue where
  law := .d1x
  base := (⟨(qq (599997) 2000000), (qq (3) 10), (qq (49) 20), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9200000000000) 119998800003)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_179Palette : List KBranch := pcRawSeed2_179.law.palette 0
abbrev pcSeed2_179 : OrbitSeed := pcRawSeed2_179.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_179_ok : seedOK (pcHead 1) pcSeed2_179Palette 2 pcSeedLimit pcSeed2_179=true := by decide +kernel
#print axioms pcSeed2_179_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_180 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (69) 100), (qq (1) 1), (qq (89) 20), (qq (-10) 3), (qq (1000000000000) 1)⟩, ⟨0, [(qq (39) 50)], [], (qq (25) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_180Palette : List KBranch := pcRawSeed2_180.law.palette 0
abbrev pcSeed2_180 : OrbitSeed := pcRawSeed2_180.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_180_ok : seedOK (pcHead 1) pcSeed2_180Palette 2 pcSeedLimit pcSeed2_180=true := by decide +kernel
#print axioms pcSeed2_180_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_181 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (23) 20), (qq (49) 20), (qq (-4) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (3) 20), (qq (3) 2)⟩], (qq (20) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_181Palette : List KBranch := pcRawSeed2_181.law.palette 0
abbrev pcSeed2_181 : OrbitSeed := pcRawSeed2_181.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_181_ok : seedOK (pcHead 1) pcSeed2_181Palette 2 pcSeedLimit pcSeed2_181=true := by decide +kernel
#print axioms pcSeed2_181_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_182 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (23) 20), (qq (13) 10), (qq (18) 5), (qq (-7) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (20) 3)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_182Palette : List KBranch := pcRawSeed2_182.law.palette 0
abbrev pcSeed2_182 : OrbitSeed := pcRawSeed2_182.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_182_ok : seedOK (pcHead 1) pcSeed2_182Palette 2 pcSeedLimit pcSeed2_182=true := by decide +kernel
#print axioms pcSeed2_182_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_183 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (13) 10), (qq (3) 2), (qq (23) 10), (qq (-4) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (690) 169)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_183Palette : List KBranch := pcRawSeed2_183.law.palette 0
abbrev pcSeed2_183 : OrbitSeed := pcRawSeed2_183.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_183_ok : seedOK (pcHead 1) pcSeed2_183Palette 2 pcSeedLimit pcSeed2_183=true := by decide +kernel
#print axioms pcSeed2_183_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_184 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (3) 2), (qq (39) 20), (qq (13) 10), (qq (-2) 3), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_184Palette : List KBranch := pcRawSeed2_184.law.palette 0
abbrev pcSeed2_184 : OrbitSeed := pcRawSeed2_184.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_184_ok : seedOK (pcHead 1) pcSeed2_184Palette 2 pcSeedLimit pcSeed2_184=true := by decide +kernel
#print axioms pcSeed2_184_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_185 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (39) 20), (qq (49) 10), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (40) 13)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_185Palette : List KBranch := pcRawSeed2_185.law.palette 0
abbrev pcSeed2_185 : OrbitSeed := pcRawSeed2_185.toSeed 20 3 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_185_ok : seedOK (pcHead 1) pcSeed2_185Palette 2 pcSeedLimit pcSeed2_185=true := by decide +kernel
#print axioms pcSeed2_185_ok


def pcRawSeeds2O007 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_168, pcRawSeed2_169, pcRawSeed2_170, pcRawSeed2_171, pcRawSeed2_172, pcRawSeed2_173, pcRawSeed2_174, pcRawSeed2_175, pcRawSeed2_176, pcRawSeed2_177, pcRawSeed2_178, pcRawSeed2_179, pcRawSeed2_180, pcRawSeed2_181, pcRawSeed2_182, pcRawSeed2_183, pcRawSeed2_184, pcRawSeed2_185]
theorem pcRawSeeds2O007_ok : ∀ S∈pcRawSeeds2O007,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O007,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_168_ok
  · exact pcSeed2_169_ok
  · exact pcSeed2_170_ok
  · exact pcSeed2_171_ok
  · exact pcSeed2_172_ok
  · exact pcSeed2_173_ok
  · exact pcSeed2_174_ok
  · exact pcSeed2_175_ok
  · exact pcSeed2_176_ok
  · exact pcSeed2_177_ok
  · exact pcSeed2_178_ok
  · exact pcSeed2_179_ok
  · exact pcSeed2_180_ok
  · exact pcSeed2_181_ok
  · exact pcSeed2_182_ok
  · exact pcSeed2_183_ok
  · exact pcSeed2_184_ok
  · exact pcSeed2_185_ok
#print axioms pcRawSeeds2O007_ok
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
