module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.Basic

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_0 : cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_0 = true := by decide +kernel
#print axioms pcCell1_0

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_1 : cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_1 = true := by decide +kernel
#print axioms pcCell1_1

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_2 : cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_2 = true := by decide +kernel
#print axioms pcCell1_2

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_3 : cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_3 = true := by decide +kernel
#print axioms pcCell1_3

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_4 : cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_4 = true := by decide +kernel
#print axioms pcCell1_4

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell1_5 : cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_5 = true := by decide +kernel
#print axioms pcCell1_5

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_0 : cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_0 = true := by decide +kernel
#print axioms pcCell2_0

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_1 : cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_1 = true := by decide +kernel
#print axioms pcCell2_1

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_2 : cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_2 = true := by decide +kernel
#print axioms pcCell2_2

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_3 : cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_3 = true := by decide +kernel
#print axioms pcCell2_3

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_4 : cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_4 = true := by decide +kernel
#print axioms pcCell2_4

set_option profiler true in
-- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
theorem pcCell2_5 : cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_5 = true := by decide +kernel
#print axioms pcCell2_5

-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_0 : pcCellBase1_0.2.R*pcCellBase1_0.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_0
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_1 : pcCellBase1_1.2.R*pcCellBase1_1.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_1
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_2 : pcCellBase1_2.2.R*pcCellBase1_2.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_2
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_3 : pcCellBase1_3.2.R*pcCellBase1_3.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_3
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_4 : pcCellBase1_4.2.R*pcCellBase1_4.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_4
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit1_5 : pcCellBase1_5.2.R*pcCellBase1_5.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit1_5
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_0 : pcCellBase2_0.2.R*pcCellBase2_0.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_0
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_1 : pcCellBase2_1.2.R*pcCellBase2_1.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_1
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_2 : pcCellBase2_2.2.R*pcCellBase2_2.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_2
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_3 : pcCellBase2_3.2.R*pcCellBase2_3.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_3
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_4 : pcCellBase2_4.2.R*pcCellBase2_4.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_4
-- kcost: <1s estimated; one rational product/comparison, no catalogue computation.
theorem pcCellLimit2_5 : pcCellBase2_5.2.R*pcCellBase2_5.1.t≤(pcSeedLimit:ℚ) := by decide +kernel
#print axioms pcCellLimit2_5
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
