module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 10), (qq (10) 99), (qq (1) 1), (qq (12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10000) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_096Palette : List KBranch := pcRawSeed3_096.law.palette 0
abbrev pcSeed3_096 : OrbitSeed := pcRawSeed3_096.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_096_ok : seedOK (pcHead 1) pcSeed3_096Palette 3 pcSeedLimit pcSeed3_096=true := by decide +kernel
#print axioms pcSeed3_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_097 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 99), (qq (11) 108), (qq (29) 9), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1089) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_097Palette : List KBranch := pcRawSeed3_097.law.palette 0
abbrev pcSeed3_097 : OrbitSeed := pcRawSeed3_097.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_097_ok : seedOK (pcHead 1) pcSeed3_097Palette 3 pcSeedLimit pcSeed3_097=true := by decide +kernel
#print axioms pcSeed3_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_098 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 108), (qq (5) 48), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (129600) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_098Palette : List KBranch := pcRawSeed3_098.law.palette 0
abbrev pcSeed3_098 : OrbitSeed := pcRawSeed3_098.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_098_ok : seedOK (pcHead 1) pcSeed3_098Palette 3 pcSeedLimit pcSeed3_098=true := by decide +kernel
#print axioms pcSeed3_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_099 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 48), (qq (50) 477), (qq (1) 1), (qq (58) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1024) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_099Palette : List KBranch := pcRawSeed3_099.law.palette 0
abbrev pcSeed3_099 : OrbitSeed := pcRawSeed3_099.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_099_ok : seedOK (pcHead 1) pcSeed3_099Palette 3 pcSeedLimit pcSeed3_099=true := by decide +kernel
#print axioms pcSeed3_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_100 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (50) 477), (qq (55) 522), (qq (29) 9), (qq (-48) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (25281) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_100Palette : List KBranch := pcRawSeed3_100.law.palette 0
abbrev pcSeed3_100 : OrbitSeed := pcRawSeed3_100.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_100_ok : seedOK (pcHead 1) pcSeed3_100Palette 3 pcSeedLimit pcSeed3_100=true := by decide +kernel
#print axioms pcSeed3_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed3_101 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (55) 522), (qq (1) 9), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (121104) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed3_101Palette : List KBranch := pcRawSeed3_101.law.palette 0
abbrev pcSeed3_101 : OrbitSeed := pcRawSeed3_101.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_101_ok : seedOK (pcHead 1) pcSeed3_101Palette 3 pcSeedLimit pcSeed3_101=true := by decide +kernel
#print axioms pcSeed3_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_102 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (25) 36), (qq (1) 1), (qq (13) 3), (qq (-16) 5), (qq (1000000000000) 1)⟩, ⟨0, [(qq (55) 72)], [], (qq (576) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_102Palette : List KBranch := pcRawSeed3_102.law.palette 0
abbrev pcSeed3_102 : OrbitSeed := pcRawSeed3_102.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_102_ok : seedOK (pcHead 1) pcSeed3_102Palette 3 pcSeedLimit pcSeed3_102=true := by decide +kernel
#print axioms pcSeed3_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_103 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (10) 9), (qq (7) 3), (qq (-6) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 9), (qq (3) 2)⟩], (qq (27) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_103Palette : List KBranch := pcRawSeed3_103.law.palette 0
abbrev pcSeed3_103 : OrbitSeed := pcRawSeed3_103.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_103_ok : seedOK (pcHead 1) pcSeed3_103Palette 3 pcSeedLimit pcSeed3_103=true := by decide +kernel
#print axioms pcSeed3_103_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_104 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (10) 9), (qq (11) 9), (qq (31) 9), (qq (-11) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_104Palette : List KBranch := pcRawSeed3_104.law.palette 0
abbrev pcSeed3_104 : OrbitSeed := pcRawSeed3_104.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_104_ok : seedOK (pcHead 1) pcSeed3_104Palette 3 pcSeedLimit pcSeed3_104=true := by decide +kernel
#print axioms pcSeed3_104_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_105 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (11) 9), (qq (5) 3), (qq (20) 9), (qq (-6) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (900) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_105Palette : List KBranch := pcRawSeed3_105.law.palette 0
abbrev pcSeed3_105 : OrbitSeed := pcRawSeed3_105.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_105_ok : seedOK (pcHead 1) pcSeed3_105Palette 3 pcSeedLimit pcSeed3_105=true := by decide +kernel
#print axioms pcSeed3_105_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_106 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (5) 3), (qq (55) 27), (qq (11) 9), (qq (-3) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (27) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_106Palette : List KBranch := pcRawSeed3_106.law.palette 0
abbrev pcSeed3_106 : OrbitSeed := pcRawSeed3_106.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_106_ok : seedOK (pcHead 1) pcSeed3_106Palette 3 pcSeedLimit pcSeed3_106=true := by decide +kernel
#print axioms pcSeed3_106_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed3_107 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (55) 27), (qq (64) 9), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (243) 55)⟩)
  N := 0
  times := [0]
abbrev pcSeed3_107Palette : List KBranch := pcRawSeed3_107.law.palette 0
abbrev pcSeed3_107 : OrbitSeed := pcRawSeed3_107.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed3_107_ok : seedOK (pcHead 1) pcSeed3_107Palette 3 pcSeedLimit pcSeed3_107=true := by decide +kernel
#print axioms pcSeed3_107_ok


def pcRawSeeds3O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed3_096, pcRawSeed3_097, pcRawSeed3_098, pcRawSeed3_099, pcRawSeed3_100, pcRawSeed3_101, pcRawSeed3_102, pcRawSeed3_103, pcRawSeed3_104, pcRawSeed3_105, pcRawSeed3_106, pcRawSeed3_107]
theorem pcRawSeeds3O004_ok : ∀ S∈pcRawSeeds3O004,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed3_096_ok
  · exact pcSeed3_097_ok
  · exact pcSeed3_098_ok
  · exact pcSeed3_099_ok
  · exact pcSeed3_100_ok
  · exact pcSeed3_101_ok
  · exact pcSeed3_102_ok
  · exact pcSeed3_103_ok
  · exact pcSeed3_104_ok
  · exact pcSeed3_105_ok
  · exact pcSeed3_106_ok
  · exact pcSeed3_107_ok
#print axioms pcRawSeeds3O004_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
