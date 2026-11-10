module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Basic

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_0 : cellOKb (pcHead 1) pcBase 1 125 9 10000 pcCellBase1_0 = true := by decide +kernel
#print axioms pcCell1_0

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_1 : cellOKb (pcHead 1) pcBase 1 125 9 10000 pcCellBase1_1 = true := by decide +kernel
#print axioms pcCell1_1

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_0 : cellOKb (pcHead 1) pcBase 2 125 9 10000 pcCellBase2_0 = true := by decide +kernel
#print axioms pcCell2_0

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_1 : cellOKb (pcHead 1) pcBase 2 125 9 10000 pcCellBase2_1 = true := by decide +kernel
#print axioms pcCell2_1

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell3_0 : cellOKb (pcHead 1) pcBase 3 125 9 10000 pcCellBase3_0 = true := by decide +kernel
#print axioms pcCell3_0

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell3_1 : cellOKb (pcHead 1) pcBase 3 125 9 10000 pcCellBase3_1 = true := by decide +kernel
#print axioms pcCell3_1

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell4_0 : cellOKb (pcHead 1) pcBase 4 125 9 10000 pcCellBase4_0 = true := by decide +kernel
#print axioms pcCell4_0

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell4_1 : cellOKb (pcHead 1) pcBase 4 125 9 10000 pcCellBase4_1 = true := by decide +kernel
#print axioms pcCell4_1

-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_0 : pcCellBase1_0.2.R*pcCellBase1_0.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_0
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_1 : pcCellBase1_1.2.R*pcCellBase1_1.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_1
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_0 : pcCellBase2_0.2.R*pcCellBase2_0.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_0
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_1 : pcCellBase2_1.2.R*pcCellBase2_1.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_1
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit3_0 : pcCellBase3_0.2.R*pcCellBase3_0.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit3_0
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit3_1 : pcCellBase3_1.2.R*pcCellBase3_1.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit3_1
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit4_0 : pcCellBase4_0.2.R*pcCellBase4_0.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit4_0
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit4_1 : pcCellBase4_1.2.R*pcCellBase4_1.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit4_1
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
