module
public import CatalanCore.Li2.NVMod.Data.Families.U12C50
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.U12C50
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.U12C50
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0xd75fa332ec8b2a5d,-0x3fad4755,0x1b8812e3b,-0x2b39f9aea9,0x14c0a109e83,-0x487a5681db,0x84d758d42f,0x255944db05,-0x1b90eaa66bcd,0x10f054f495d,0x171797a901,-0x4917dfea0853,0x4764cb9147b44ad515fc0876ae97b5c6ff3bd603f7ba7,-0x60b72846be61a8bc244e8a26dab5b8624bbc56b9d8c8bfd]
def regularDenominators : List ℤ := raw_ints% [0xaf303481d138657cee36c47705ec1d75bb4a7759c1000000,0x10c234558041ad65594a81c1625dd786ccac5000000,0x2230045c8085fb53df1d1d2e58071e12fdb17000000,0x11ce579ad845c83baedf29dd7883b4ff397715000000,0x356b06d088d158b30c9d7d98698b1efdac653f000000,0x5ef7288f2c1ed693a4a6349d2d691aa687d07000000,0xaaf015ce829de8a35b9191e7b823965ef4773000000,0x19e650e13a940bf9b88a6b70af4b35d05395f000000,0x356b06d088d158b30c9d7d98698b1efdac653f000000,0x19e650e13a940bf9b88a6b70af4b35d05395f000000,0x892dcfb1c381216a37d451c79963fb7b8cd000000,0x5ef7288f2c1ed693a4a6349d2d691aa687d07000000,0x2b66f5896f2a18117a3ff60bd5c1092e1c12433000000,0xe77a72dcfb8b2b07e155203f1eb030f5eb0c11000000]
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
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_13 : regularValueAt 13=regularMomentWith indices rho 13 := by decide +kernel
theorem regular_prefix (e : ℕ) (he : e<14) : regularValueAt e=regularMomentWith indices rho e := by
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
  · exact regular_ok_13
def regularValue (e : ℕ) : ℚ := if e<14 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  unfold regularValue
  split_ifs with he
  · exact (regular_prefix e he).trans h
  · exact h
theorem h0_key (size : ℕ) : h0 (key size)=13 := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.U12C50
