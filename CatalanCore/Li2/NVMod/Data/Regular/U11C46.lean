module
public import CatalanCore.Li2.NVMod.Data.Families.U11C46
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.U11C46
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.U11C46
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0xe0813290321a0c9f,-0x1710c0a69,0xa045d09ed,-0x1b190d93c1b,0xc190d08ed9,-0x5f9e2c9d90d,0x1a687ceb07,0x14b594d069e3,-0x271b1ab399f,-0x371a7cc75,0x1e441507692e1,0xf197fcddff320223a72f8ce4340df0ca305240973,-0xa68c12d3438888204a4cdb2de737431e699d109800b]
def regularDenominators : List ℤ := raw_ints% [0xe9e68902ee22867cc307445f3088ed77bc8d289000000,0x4146b26606977190f5a8799a6e78fc8d43580000,0x92df11658ed4bf8628bb119b7890383dd7860000,0x92df11658ed4bf8628bb119b7890383dd78600000,0x1d5fd04782f759813b589d1f181cd80c5e4e00000,0x92df11658ed4bf8628bb119b7890383dd78600000,0x662bdf948fe1e9687560be55e490d93626a00000,0x92df11658ed4bf8628bb119b7890383dd78600000,0x5dff674b3cb11e6a5781f6c9e6c2b35ac7600000,0xb3e65c5a1983fa847b62131df9573c50a600000,0x92df11658ed4bf8628bb119b7890383dd78600000,0x92df11658ed4bf8628bb119b7890383dd78600000,0x1d5fd04782f759813b589d1f181cd80c5e4e00000]
def regularValueAt (e : ℕ) : ℚ := (regularNumerators.getD e 0:ℚ)/(regularDenominators.getD e 1:ℚ)
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_0 : regularValueAt 0=regularMomentWith indices rho 0 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_1 : regularValueAt 1=regularMomentWith indices rho 1 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_2 : regularValueAt 2=regularMomentWith indices rho 2 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_3 : regularValueAt 3=regularMomentWith indices rho 3 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_4 : regularValueAt 4=regularMomentWith indices rho 4 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_5 : regularValueAt 5=regularMomentWith indices rho 5 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_6 : regularValueAt 6=regularMomentWith indices rho 6 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_7 : regularValueAt 7=regularMomentWith indices rho 7 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_8 : regularValueAt 8=regularMomentWith indices rho 8 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_9 : regularValueAt 9=regularMomentWith indices rho 9 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_10 : regularValueAt 10=regularMomentWith indices rho 10 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_11 : regularValueAt 11=regularMomentWith indices rho 11 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_12 : regularValueAt 12=regularMomentWith indices rho 12 := by decide +kernel
theorem regular_prefix (e : ℕ) (he : e<13) : regularValueAt e=regularMomentWith indices rho e := by
  interval_cases e
  · exact regular_ok_0
  · exact regular_ok_1
  · exact regular_ok_2
  · exact regular_ok_3
  · exact regular_ok_4
  · exact regular_ok_5
  · exact regular_ok_6
  · exact regular_ok_7
  · exact regular_ok_8
  · exact regular_ok_9
  · exact regular_ok_10
  · exact regular_ok_11
  · exact regular_ok_12
def regularValue (e : ℕ) : ℚ := if e<13 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  unfold regularValue
  split_ifs with he
  · exact (regular_prefix e he).trans h
  · exact h
theorem h0_key (size : ℕ) : h0 (key size)=12 := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.U11C46
