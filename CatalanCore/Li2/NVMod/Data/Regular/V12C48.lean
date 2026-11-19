module
public import CatalanCore.Li2.NVMod.Data.Families.V12C48
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.V12C48
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.V12C48
noncomputable section
def regularNumerators : List ℤ := raw_ints% [-0x24bf0f89,0x1d080b83,-0x54ae343b8f,0xf860382c71,-0x1e2f2aeaa1,0x79054568d1,0xbeaa9e03b9,-0x1ad66495aa3,-0x6e20a0281,0xb56e9ddd71b,-0x13f52736a13e9,0xb0297db734bf218f5492ac11109fa6a8dab1a0336d,-0x3bf5174124d594b2e8f1eb305bb8a2e73d1ccdd5d6d47]
def regularDenominators : List ℤ := raw_ints% [0x11d954c7e5cd690da32c11403a35150ea06a10000,0x49b2ea7330bb80384f29918d536fd2d109f80000,0x5051fd838a1c58bd5e464da105eedec1d1dd480000,0x6b17fcaf62d07651d30867815d3e7e57c27c600000,0x8746b871c02fbde09ec73f6009fe18daa4d300000,0x6b17fcaf62d07651d30867815d3e7e57c27c600000,0xe9a8b2f30623eae11240e1d46e59cdd6bf9b00000,0xbe6388543de46091772b62ad178b8b46af1600000,0xdbea11d5ab6d194c4d6a3df51c90c1bb0eb00000,0x9bc5cca20417f1eb6180968d9ee68939d51200000,0xa0a3fb071438b17abc8c9b420bddbd83a3ba900000,0x6b17fcaf62d07651d30867815d3e7e57c27c600000,0xa0a3fb071438b17abc8c9b420bddbd83a3ba900000]
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
end CatalanCore.Li2.NVMod.RegularFamily.V12C48
