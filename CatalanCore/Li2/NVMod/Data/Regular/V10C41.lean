module
public import CatalanCore.Li2.NVMod.Data.Families.V10C41
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.V10C41
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.V10C41
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0x16c1a36b3,0x161cc65,-0x1ca0ec3,0xed91,-0x3f01,-0x7f24cdef,0x9777535f,-0x37057,-0xa5a1b27,0xa15e8a9b,0x12574b9b6d6ac0f58fa95e9002668cb32a9,-0x229c8a867b93e4e3f8065e7992d7ceb86319]
def regularDenominators : List ℤ := raw_ints% [0xd10ff2fc443e889a387c8c329804da9e0000,0x539ffacb4e7f69d749cb6b477001f10c00,0x35851b63657043bcfc074ee60a3eaec000,0x12bf83141b2075e3c2a323584a35a000,0x8aca10147a0bde94e87dec2031e8000,0x539ffacb4e7f69d749cb6b477001f10c000,0x2173311e1f662a561d84914fc6672d38000,0xe158df1bc60e967a0a39b7fe7bfa7400,0x64be51ac0a3cbbbe16a458479ad058000,0x3fb6d776543050a407766a1e0c323dc000,0xb2665b4b5220e1cb48185c542226468000,0x7dede6170ccbeaad9c4d6e5981846e000]
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
end CatalanCore.Li2.NVMod.RegularFamily.V10C41
