module
public import CatalanCore.Li2.NVMod.Data.Families.V12C51
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.V12C51
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.V12C51
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0x1299cb3336f,0x2861a43c43,-0x1b025d854e0b,0xd0a86379599d,-0x34405b373fd3,0x13dc98a249b9,0xea7853de0428d,-0x13dd25a5f2247,-0x2649e0e6c85b1,0x96e0918bb614b,-0x1f0a48a45de389,-0x4eaced3ffb090d,0x2eb99f417a42a5f,0x4b9d799ddaa97d,0x13aa1a2bdc9cf8bd6e7ab541c1c8242a2bfd9fd1878ba889,-0x3fbbf9b6a8875a1f36ddefb6b649f6f7fdaa3915d8429f658df]
def regularDenominators : List ℤ := raw_ints% [0xd67521e7e76f0de525b950c191cd10b9618dc0c5d000000,0x9bf818a8a850c4498fcc97d29895236f8cc42f1b800000,0x2835f65b7b64d29af712bf244b567322c24a942517000000,0x9370874f6f1c598d89ef6785143cfb7f73117487ff000000,0x1a04cc958c140fcdaeee03359a28e1167db7c9452d000000,0x9370874f6f1c598d89ef6785143cfb7f73117487ff000000,0x1ba5195ee4d550ca89dce368f3cb6f27e59345d97fd000000,0x1061d625453c09f348370b8090788db8d3e57eb9c7000000,0x2835f65b7b64d29af712bf244b567322c24a942517000000,0xd67521e7e76f0de525b950c191cd10b9618dc0c5d000000,0x2835f65b7b64d29af712bf244b567322c24a942517000000,0xd67521e7e76f0de525b950c191cd10b9618dc0c5d000000,0x2835f65b7b64d29af712bf244b567322c24a942517000000,0x195daead526d7ac30476435bb668153f3794e540b000000,0xbf45dff858cad50aa51ae7292f0301140ae6364f9000000,0x9370874f6f1c598d89ef6785143cfb7f73117487ff000000]
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
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_14 : regularValueAt 14=regularMomentWith indices rho 14 := by decide +kernel
-- kcost: 2 s estimated; one original regularMoment value at z=1 through proved residues
set_option trace.profiler true in
theorem regular_ok_15 : regularValueAt 15=regularMomentWith indices rho 15 := by decide +kernel
theorem regular_prefix (e : ℕ) (he : e<16) : regularValueAt e=regularMomentWith indices rho e := by
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
  · exact regular_ok_14
  · exact regular_ok_15
def regularValue (e : ℕ) : ℚ := if e<16 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  unfold regularValue
  split_ifs with he
  · exact (regular_prefix e he).trans h
  · exact h
theorem h0_key (size : ℕ) : h0 (key size)=15 := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.V12C51
