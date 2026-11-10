module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (50) 459), (qq (55) 504), (qq (29) 9), (qq (-46) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (23409) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_096Palette : List KBranch := pcRawSeed1_096.law.palette 0
abbrev pcSeed1_096 : OrbitSeed := pcRawSeed1_096.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_096_ok : seedOK (pcHead 1) pcSeed1_096Palette 1 pcSeedLimit pcSeed1_096=true := by decide +kernel
#print axioms pcSeed1_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed1_097 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (55) 504), (qq (1) 9), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (112896) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed1_097Palette : List KBranch := pcRawSeed1_097.law.palette 0
abbrev pcSeed1_097 : OrbitSeed := pcRawSeed1_097.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_097_ok : seedOK (pcHead 1) pcSeed1_097Palette 1 pcSeedLimit pcSeed1_097=true := by decide +kernel
#print axioms pcSeed1_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_098 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (25) 27), (qq (1) 1), (qq (13) 3), (qq (-12) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (324) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_098Palette : List KBranch := pcRawSeed1_098.law.palette 0
abbrev pcSeed1_098 : OrbitSeed := pcRawSeed1_098.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_098_ok : seedOK (pcHead 1) pcSeed1_098Palette 1 pcSeedLimit pcSeed1_098=true := by decide +kernel
#print axioms pcSeed1_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_099 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (10) 9), (qq (7) 3), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 9), (qq (3) 2)⟩], (qq (27) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_099Palette : List KBranch := pcRawSeed1_099.law.palette 0
abbrev pcSeed1_099 : OrbitSeed := pcRawSeed1_099.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_099_ok : seedOK (pcHead 1) pcSeed1_099Palette 1 pcSeedLimit pcSeed1_099=true := by decide +kernel
#print axioms pcSeed1_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_100 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (10) 9), (qq (11) 9), (qq (31) 9), (qq (-7) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_100Palette : List KBranch := pcRawSeed1_100.law.palette 0
abbrev pcSeed1_100 : OrbitSeed := pcRawSeed1_100.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_100_ok : seedOK (pcHead 1) pcSeed1_100Palette 1 pcSeedLimit pcSeed1_100=true := by decide +kernel
#print axioms pcSeed1_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_101 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (11) 9), (qq (5) 1), (qq (20) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (900) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_101Palette : List KBranch := pcRawSeed1_101.law.palette 0
abbrev pcSeed1_101 : OrbitSeed := pcRawSeed1_101.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_101_ok : seedOK (pcHead 1) pcSeed1_101Palette 1 pcSeedLimit pcSeed1_101=true := by decide +kernel
#print axioms pcSeed1_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_102 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (5) 1), (qq (55) 9), (qq (11) 9), (qq (-1) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_102Palette : List KBranch := pcRawSeed1_102.law.palette 0
abbrev pcSeed1_102 : OrbitSeed := pcRawSeed1_102.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_102_ok : seedOK (pcHead 1) pcSeed1_102Palette 1 pcSeedLimit pcSeed1_102=true := by decide +kernel
#print axioms pcSeed1_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed1_103 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (55) 9), (qq (64) 9), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (18) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed1_103Palette : List KBranch := pcRawSeed1_103.law.palette 0
abbrev pcSeed1_103 : OrbitSeed := pcRawSeed1_103.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed1_103_ok : seedOK (pcHead 1) pcSeed1_103Palette 1 pcSeedLimit pcSeed1_103=true := by decide +kernel
#print axioms pcSeed1_103_ok


def pcRawSeeds1O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed1_096, pcRawSeed1_097, pcRawSeed1_098, pcRawSeed1_099, pcRawSeed1_100, pcRawSeed1_101, pcRawSeed1_102, pcRawSeed1_103]
theorem pcRawSeeds1O004_ok : ∀ S∈pcRawSeeds1O004,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed1_096_ok
  · exact pcSeed1_097_ok
  · exact pcSeed1_098_ok
  · exact pcSeed1_099_ok
  · exact pcSeed1_100_ok
  · exact pcSeed1_101_ok
  · exact pcSeed1_102_ok
  · exact pcSeed1_103_ok
#print axioms pcRawSeeds1O004_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
