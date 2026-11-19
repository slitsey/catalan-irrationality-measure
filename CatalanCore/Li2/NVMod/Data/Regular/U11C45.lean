module
public import CatalanCore.Li2.NVMod.Data.Families.U11C45
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.U11C45
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.U11C45
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0x5eec16e7bddd3648d,-0x106000233d,0x2d5a51618d,-0xdc7e44abd,0x118fb59a9d1,-0x498e968f,0xd9439d68f9,0x5d3b3af3b3b,-0x1263a226c35f,0x251d98c46b3,0x1943c36fe525053e4a5f5355c5dd37529c687c89,-0x92be91e1f64c29b09fc88ca828a9e30f024d70bad]
def regularDenominators : List ℤ := raw_ints% [0x2265aabcaa8c9b4e9526b73b2cc8d7a0aac976e800000,0x11476b755c19077931f7e3f42c4d33cb0a4c0000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0x1b4e186d9b04c9708187ba6568c5d9bf4600000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0x27a43103c85ffe37e71f0f93b5a0eeb200000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0xf5bedbda732b14f48dc58d90aef4a7b97600000,0x1b4e186d9b04c9708187ba6568c5d9bf4600000]
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
theorem regular_prefix (e : ℕ) (he : e<12) : regularValueAt e=regularMomentWith indices rho e := by
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
def regularValue (e : ℕ) : ℚ := if e<12 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  unfold regularValue
  split_ifs with he
  · exact (regular_prefix e he).trans h
  · exact h
theorem h0_key (size : ℕ) : h0 (key size)=11 := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.U11C45
