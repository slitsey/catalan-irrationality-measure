module
public import CatalanCore.Li2.NVMod.Data.Families.V12C50
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.V12C50
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.V12C50
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0xb81bab67f9,0x5e67da54d,-0x11f6f1e1e4b,0x6408c03135479,-0x14d7d4d23b12f,0x1624059f213a1,0x22a29e0bc726f,-0x70fd26a43ab5,-0x4cefcd135e4ab,0x48cff326640f13,-0xd71a19f79cd15,-0x34e37d02ef670f,0x58df70f1fdaf3ff7,0x5261592559dd590981d6950f663bb1e4a6ad2634cf0987,-0x99889bd930e672f6cecd2af7d75778e718510bbec1a1310181]
def regularDenominators : List ℤ := raw_ints% [0x2d262215dfe17c303dd62bf2db5397bb3cf56bf3c00000,0x7b1166395ac34f55d71f2228f37cf58014c90b000000,0x8ef5ddeb73ea9a80f4ed8b8b28161f63ae36c7d000000,0x1747a99347704408dfe26ea939171a3c8b6e8ba9af000000,0x353615e2ec6e525d6d73461514c71765d0fcacf19000000,0x1747a99347704408dfe26ea939171a3c8b6e8ba9af000000,0x15e91812251e5e26785ca463088e36cf9249ecdbf000000,0x1d5ba224ec602d7156de7ef125f241dfe60fd22d000000,0x21dc999067e91d242e60a0f6247eb1cc6db810f6d000000,0x21dc999067e91d242e60a0f6247eb1cc6db810f6d000000,0x4d65f14a1214d4e4fc4a947bc12196658d126feb000000,0x3140df5dae6a58eecf182ff1a97276face230167000000,0x1747a99347704408dfe26ea939171a3c8b6e8ba9af000000,0x3214c94e0bb32057ee8a9c50138e342397846689000000,0x1747a99347704408dfe26ea939171a3c8b6e8ba9af000000]
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
theorem regular_prefix (e : ℕ) (he : e<15) : regularValueAt e=regularMomentWith indices rho e := by
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
def regularValue (e : ℕ) : ℚ := if e<15 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  unfold regularValue
  split_ifs with he
  · exact (regular_prefix e he).trans h
  · exact h
theorem h0_key (size : ℕ) : h0 (key size)=14 := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.V12C50
