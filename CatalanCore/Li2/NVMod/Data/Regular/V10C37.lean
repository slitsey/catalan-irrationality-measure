module
public import CatalanCore.Li2.NVMod.Data.Families.V10C37
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.V10C37
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.V10C37
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0x1664b,0x17b25,-0x100b7,0x985,-0x14f59,-0x2c1d97,0x62e5a4243e63e802b8badd4e5ddf,-0x16c43eaff00ca85d2757558debc3d5]
def regularDenominators : List ℤ := raw_ints% [0x8042bb2cba420f7e146be268000,0x35712352a2f0dbc9ddd79e56000,0x10e05bff25fb37eee7bd5a6c000,0x628b2a1574fb211bb86904000,0x10e05bff25fb37eee7bd5a6c000,0x140a6d3efd1a526bb330db604000,0x3c1f47bcf74ef74319929220c000,0x6ae246a545e1b793bbaf3cac000]
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
theorem regular_prefix (e : ℕ) (he : e<8) : regularValueAt e=regularMomentWith indices rho e := by
  interval_cases e
  · exact regular_ok_0
  · exact regular_ok_1
  · exact regular_ok_2
  · exact regular_ok_3
  · exact regular_ok_4
  · exact regular_ok_5
  · exact regular_ok_6
  · exact regular_ok_7
def regularValue (e : ℕ) : ℚ := if e<8 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  unfold regularValue
  split_ifs with he
  · exact (regular_prefix e he).trans h
  · exact h
theorem h0_key (size : ℕ) : h0 (key size)=7 := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.V10C37
