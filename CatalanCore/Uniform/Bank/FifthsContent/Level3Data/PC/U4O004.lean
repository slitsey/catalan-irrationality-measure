module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (25) 243), (qq (55) 531), (qq (29) 9), (qq (-49) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (26244) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_096Palette : List KBranch := pcRawSeed4_096.law.palette 0
abbrev pcSeed4_096 : OrbitSeed := pcRawSeed4_096.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_096_ok : seedOK (pcHead 1) pcSeed4_096Palette 4 pcSeedLimit pcSeed4_096=true := by decide +kernel
#print axioms pcSeed4_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed4_097 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (55) 531), (qq (1) 9), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (125316) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed4_097Palette : List KBranch := pcRawSeed4_097.law.palette 0
abbrev pcSeed4_097 : OrbitSeed := pcRawSeed4_097.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_097_ok : seedOK (pcHead 1) pcSeed4_097Palette 4 pcSeedLimit pcSeed4_097=true := by decide +kernel
#print axioms pcSeed4_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_098 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (50) 81), (qq (1) 1), (qq (13) 3), (qq (-18) 5), (qq (1000000000000) 1)⟩, ⟨0, [(qq (55) 81)], [], (qq (162) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_098Palette : List KBranch := pcRawSeed4_098.law.palette 0
abbrev pcSeed4_098 : OrbitSeed := pcRawSeed4_098.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_098_ok : seedOK (pcHead 1) pcSeed4_098Palette 4 pcSeedLimit pcSeed4_098=true := by decide +kernel
#print axioms pcSeed4_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_099 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (10) 9), (qq (7) 3), (qq (-8) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 9), (qq (3) 2)⟩], (qq (27) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_099Palette : List KBranch := pcRawSeed4_099.law.palette 0
abbrev pcSeed4_099 : OrbitSeed := pcRawSeed4_099.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_099_ok : seedOK (pcHead 1) pcSeed4_099Palette 4 pcSeedLimit pcSeed4_099=true := by decide +kernel
#print axioms pcSeed4_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_100 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (10) 9), (qq (11) 9), (qq (31) 9), (qq (-13) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_100Palette : List KBranch := pcRawSeed4_100.law.palette 0
abbrev pcSeed4_100 : OrbitSeed := pcRawSeed4_100.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_100_ok : seedOK (pcHead 1) pcSeed4_100Palette 4 pcSeedLimit pcSeed4_100=true := by decide +kernel
#print axioms pcSeed4_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_101 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (11) 9), (qq (5) 4), (qq (20) 9), (qq (-8) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (900) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_101Palette : List KBranch := pcRawSeed4_101.law.palette 0
abbrev pcSeed4_101 : OrbitSeed := pcRawSeed4_101.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_101_ok : seedOK (pcHead 1) pcSeed4_101Palette 4 pcSeedLimit pcSeed4_101=true := by decide +kernel
#print axioms pcSeed4_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_102 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (5) 4), (qq (55) 36), (qq (11) 9), (qq (-4) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (72) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_102Palette : List KBranch := pcRawSeed4_102.law.palette 0
abbrev pcSeed4_102 : OrbitSeed := pcRawSeed4_102.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_102_ok : seedOK (pcHead 1) pcSeed4_102Palette 4 pcSeedLimit pcSeed4_102=true := by decide +kernel
#print axioms pcSeed4_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed4_103 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (55) 36), (qq (64) 9), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (72) 11)⟩)
  N := 0
  times := [0]
abbrev pcSeed4_103Palette : List KBranch := pcRawSeed4_103.law.palette 0
abbrev pcSeed4_103 : OrbitSeed := pcRawSeed4_103.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed4_103_ok : seedOK (pcHead 1) pcSeed4_103Palette 4 pcSeedLimit pcSeed4_103=true := by decide +kernel
#print axioms pcSeed4_103_ok


def pcRawSeeds4O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed4_096, pcRawSeed4_097, pcRawSeed4_098, pcRawSeed4_099, pcRawSeed4_100, pcRawSeed4_101, pcRawSeed4_102, pcRawSeed4_103]
theorem pcRawSeeds4O004_ok : ∀ S∈pcRawSeeds4O004,
    seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds4O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed4_096_ok
  · exact pcSeed4_097_ok
  · exact pcSeed4_098_ok
  · exact pcSeed4_099_ok
  · exact pcSeed4_100_ok
  · exact pcSeed4_101_ok
  · exact pcSeed4_102_ok
  · exact pcSeed4_103_ok
#print axioms pcRawSeeds4O004_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
