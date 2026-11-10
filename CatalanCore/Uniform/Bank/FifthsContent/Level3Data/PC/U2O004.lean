module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_096 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 1 1
  base := (⟨(qq (1) 10), (qq (10) 99), (qq (1) 1), (qq (12) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10000) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_096Palette : List KBranch := pcRawSeed2_096.law.palette 0
abbrev pcSeed2_096 : OrbitSeed := pcRawSeed2_096.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_096_ok : seedOK (pcHead 1) pcSeed2_096Palette 2 pcSeedLimit pcSeed2_096=true := by decide +kernel
#print axioms pcSeed2_096_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_097 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (10) 99), (qq (11) 108), (qq (29) 9), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (1089) 1)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_097Palette : List KBranch := pcRawSeed2_097.law.palette 0
abbrev pcSeed2_097 : OrbitSeed := pcRawSeed2_097.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_097_ok : seedOK (pcHead 1) pcSeed2_097Palette 2 pcSeedLimit pcSeed2_097=true := by decide +kernel
#print axioms pcSeed2_097_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_098 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (11) 108), (qq (5) 47), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (129600) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_098Palette : List KBranch := pcRawSeed2_098.law.palette 0
abbrev pcSeed2_098 : OrbitSeed := pcRawSeed2_098.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_098_ok : seedOK (pcHead 1) pcSeed2_098Palette 2 pcSeedLimit pcSeed2_098=true := by decide +kernel
#print axioms pcSeed2_098_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_099 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 1
  base := (⟨(qq (5) 47), (qq (25) 234), (qq (1) 1), (qq (57) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (8836) 9)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_099Palette : List KBranch := pcRawSeed2_099.law.palette 0
abbrev pcSeed2_099 : OrbitSeed := pcRawSeed2_099.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_099_ok : seedOK (pcHead 1) pcSeed2_099Palette 2 pcSeedLimit pcSeed2_099=true := by decide +kernel
#print axioms pcSeed2_099_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_100 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (25) 234), (qq (55) 513), (qq (29) 9), (qq (-47) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (24336) 25)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_100Palette : List KBranch := pcRawSeed2_100.law.palette 0
abbrev pcSeed2_100 : OrbitSeed := pcRawSeed2_100.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_100_ok : seedOK (pcHead 1) pcSeed2_100Palette 2 pcSeedLimit pcSeed2_100=true := by decide +kernel
#print axioms pcSeed2_100_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
def pcRawSeed2_101 : CatalogueSeed pcLegacyCatalogue where
  law := .pre 1 0 0
  base := (⟨(qq (55) 513), (qq (1) 9), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (116964) 121)⟩)
  N := 23
  times := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
abbrev pcSeed2_101Palette : List KBranch := pcRawSeed2_101.law.palette 0
abbrev pcSeed2_101 : OrbitSeed := pcRawSeed2_101.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=24 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_101_ok : seedOK (pcHead 1) pcSeed2_101Palette 2 pcSeedLimit pcSeed2_101=true := by decide +kernel
#print axioms pcSeed2_101_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_102 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨6,by decide +kernel⟩]
  base := (⟨(qq (50) 63), (qq (1) 1), (qq (13) 3), (qq (-14) 5), (qq (1000000000000) 1)⟩, ⟨0, [(qq (55) 63)], [], (qq (441) 25)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_102Palette : List KBranch := pcRawSeed2_102.law.palette 0
abbrev pcSeed2_102 : OrbitSeed := pcRawSeed2_102.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_102_ok : seedOK (pcHead 1) pcSeed2_102Palette 2 pcSeedLimit pcSeed2_102=true := by decide +kernel
#print axioms pcSeed2_102_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_103 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨7,by decide +kernel⟩, ⟨4,by decide +kernel⟩]
  base := (⟨(qq (1) 1), (qq (10) 9), (qq (7) 3), (qq (-4) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [⟨false, 1, (qq (1) 9), (qq (3) 2)⟩], (qq (27) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_103Palette : List KBranch := pcRawSeed2_103.law.palette 0
abbrev pcSeed2_103 : OrbitSeed := pcRawSeed2_103.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_103_ok : seedOK (pcHead 1) pcSeed2_103Palette 2 pcSeedLimit pcSeed2_103=true := by decide +kernel
#print axioms pcSeed2_103_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_104 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (10) 9), (qq (11) 9), (qq (31) 9), (qq (-9) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (9) 1)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_104Palette : List KBranch := pcRawSeed2_104.law.palette 0
abbrev pcSeed2_104 : OrbitSeed := pcRawSeed2_104.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_104_ok : seedOK (pcHead 1) pcSeed2_104Palette 2 pcSeedLimit pcSeed2_104=true := by decide +kernel
#print axioms pcSeed2_104_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_105 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨4,by decide +kernel⟩]
  base := (⟨(qq (11) 9), (qq (5) 2), (qq (20) 9), (qq (-4) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (900) 121)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_105Palette : List KBranch := pcRawSeed2_105.law.palette 0
abbrev pcSeed2_105 : OrbitSeed := pcRawSeed2_105.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_105_ok : seedOK (pcHead 1) pcSeed2_105Palette 2 pcSeedLimit pcSeed2_105=true := by decide +kernel
#print axioms pcSeed2_105_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_106 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (5) 2), (qq (55) 18), (qq (11) 9), (qq (-2) 5), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (18) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_106Palette : List KBranch := pcRawSeed2_106.law.palette 0
abbrev pcSeed2_106 : OrbitSeed := pcRawSeed2_106.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_106_ok : seedOK (pcHead 1) pcSeed2_106Palette 2 pcSeedLimit pcSeed2_106=true := by decide +kernel
#print axioms pcSeed2_106_ok

-- kcost: catalogue-index bounds <1s estimated, catalogue<=91 branches; no numeric profile recomputation.
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
def pcRawSeed2_107 : CatalogueSeed pcLegacyCatalogue where
  law := .constant [⟨5,by decide +kernel⟩]
  base := (⟨(qq (55) 18), (qq (64) 9), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (18) 5)⟩)
  N := 0
  times := [0]
abbrev pcSeed2_107Palette : List KBranch := pcRawSeed2_107.law.palette 0
abbrev pcSeed2_107 : OrbitSeed := pcRawSeed2_107.toSeed 9 1 10000
-- kcost: 55.5003s/24 complete original hard-class unit measured; selected24unit19.0267s measured. Here one complete seed: <=2branches, actual cuts/strips, <=1 time-index bounds and one exact threshold product.
set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcSeed2_107_ok : seedOK (pcHead 1) pcSeed2_107Palette 2 pcSeedLimit pcSeed2_107=true := by decide +kernel
#print axioms pcSeed2_107_ok


def pcRawSeeds2O004 : List (CatalogueSeed pcLegacyCatalogue) := [pcRawSeed2_096, pcRawSeed2_097, pcRawSeed2_098, pcRawSeed2_099, pcRawSeed2_100, pcRawSeed2_101, pcRawSeed2_102, pcRawSeed2_103, pcRawSeed2_104, pcRawSeed2_105, pcRawSeed2_106, pcRawSeed2_107]
theorem pcRawSeeds2O004_ok : ∀ S∈pcRawSeeds2O004,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2O004,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pcSeed2_096_ok
  · exact pcSeed2_097_ok
  · exact pcSeed2_098_ok
  · exact pcSeed2_099_ok
  · exact pcSeed2_100_ok
  · exact pcSeed2_101_ok
  · exact pcSeed2_102_ok
  · exact pcSeed2_103_ok
  · exact pcSeed2_104_ok
  · exact pcSeed2_105_ok
  · exact pcSeed2_106_ok
  · exact pcSeed2_107_ok
#print axioms pcRawSeeds2O004_ok
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
