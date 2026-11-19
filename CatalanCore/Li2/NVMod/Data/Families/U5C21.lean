module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialFamily
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialSourceCache
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.FamilySource.U5C21
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,5,21,size⟩
def bases : List ℕ := [1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def num : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x5e8988296df8000,0x80c319b7278e800,0x5150de2bbf15700,0x1f9d36eda478380,0x878a2063394f90,0x1a8c9010d0ba00,0x3eeedad83ece8,0x731fd3178de8,0xa449a7b85e1,0xb78ab1e670,0xa0084010c,0x6bc6dcc0,0x36f90d6,0x148890,0x54c4,0xd8,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x7,0xe,-0x69,0xe7,-0x34f,0x6e9a,-0x2cee9,0xaebc3,-0x22f27,0x27478,-0x5377f,0x384de,-0x2fc20e,0xcbc48]
def rhoDenominators : List ℤ := raw_ints% [0xe6f190,0x5dd8,0x6b4,0x63,0x2c,0xa,0x6,0x31,0x70,0xd8,0x1e,0x21,0x63,0x8f,0x1b5f,0x3aa7]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 22
  decide +kernel
-- kcost: 1 s estimated; once-per-family integer numerator/denominator source bindings
theorem num_ok : numeratorCoefficients .U bases=num := by decide +kernel
theorem den_ok : linearProductCoefficients (indices.map (fun (m : ℕ)=>(m:ℤ)))=den := by decide +kernel
theorem num_source (size : ℕ) : coefficientsPoly num=numeratorZ (key size) := by
  have h:=numeratorCoefficients_spec (key size) bases bases_nodup (base_set size)
  rw [show numeratorCoefficients (key size).kind bases=num from num_ok] at h
  exact h
theorem den_source (size : ℕ) : coefficientsPoly den=denominatorZ (key size) := by
  have h:=denominatorCoefficients_spec (key size) indices indices_nodup (indices_set size)
  rw [den_ok] at h
  exact h
-- kcost: 2 s estimated; every pole checked once against integer Horner/derivative source
theorem rho_ok : indices.all (fun (m : ℕ)=>decide (rho m=((evalAndDerivative (-(m:ℤ)) num).1:ℚ)/((evalAndDerivative (-(m:ℤ)) den).2:ℚ)))=true := by decide +kernel
theorem rho_source (size m : ℕ) (hm : m∈indices.toFinset) : rho m=residue (key size) m := by
  have h:=of_decide_eq_true ((List.all_eq_true.mp rho_ok) m (List.mem_toFinset.mp hm))
  exact h.trans (residue_from_tables (key size) num den (num_source size) (den_source size) m).symm
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤21))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤21 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 22 omega6=padCoefficients 22 (omegaCoefficients 21 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 21 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 22 omega7=padCoefficients 22 (omegaCoefficients 21 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 21 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 22 omega8=padCoefficients 22 (omegaCoefficients 21 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 21 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 22 omega9=padCoefficients 22 (omegaCoefficients 21 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 21 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 22 omega10=padCoefficients 22 (omegaCoefficients 21 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 21 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 22 omega11=padCoefficients 22 (omegaCoefficients 21 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 21 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 22 omega12=padCoefficients 22 (omegaCoefficients 21 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 21 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 22 omega13=padCoefficients 22 (omegaCoefficients 21 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 21 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 22 omega14=padCoefficients 22 (omegaCoefficients 21 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 21 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 22 omega15=padCoefficients 22 (omegaCoefficients 21 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 21 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 22 omega16=padCoefficients 22 (omegaCoefficients 21 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 21 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 22 omega17=padCoefficients 22 (omegaCoefficients 21 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 21 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 22 omega18=padCoefficients 22 (omegaCoefficients 21 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 21 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 22 omega19=padCoefficients 22 (omegaCoefficients 21 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 21 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 22 omega20=padCoefficients 22 (omegaCoefficients 21 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 21 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 22 omega21=padCoefficients 22 (omegaCoefficients 21 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 21 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 16 li0=padCoefficients 16 (liCoefficients 15 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 15 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 16 li1=padCoefficients 16 (liCoefficients 15 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 15 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x36,-0x9a,0x113,-0x129,0x84,0x84,-0x129,0x113,-0x9a,0x36,-0xb,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 16 li2=padCoefficients 16 (liCoefficients 15 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 15 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x7,0xc,0x2c,-0x113,0x2b5,-0x420,0x420,-0x2b5,0x113,-0x2c,-0xc,0x7,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 16 li3=padCoefficients 16 (liCoefficients 15 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 15 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x1,-0x36,0x10a,-0x271,0x30f,-0x174,-0x174,0x30f,-0x271,0x10a,-0x36,0x1,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 16 li4=padCoefficients 16 (liCoefficients 15 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 15 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x11,-0x84,0x11c,0x55,-0x5bb,0xba0,-0xba0,0x5bb,-0x55,-0x11c,0x84,-0x11,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 16 li5=padCoefficients 16 (liCoefficients 15 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 15 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x31,-0x7e,-0x23e,0xb9f,-0x1371,0xa5c,0xa5c,-0x1371,0xb9f,-0x23e,-0x7e,0x31,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 16 li6=padCoefficients 16 (liCoefficients 15 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 15 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x71,0x174,-0xd6c,0x1405,0x1395,-0x52e0,0x52e0,-0x1395,-0x1405,0xd6c,-0x174,-0x71,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 16 li7=padCoefficients 16 (liCoefficients 15 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 15 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf1,0xb0a,-0x1936,-0x48c1,0xf4ef,-0x9ef4,-0x9ef4,0xf4ef,-0x48c1,-0x1936,0xb0a,0xf1,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 16 li8=padCoefficients 16 (liCoefficients 15 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 15 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f1,0x2f4c,0x4eec,-0x2322b,0xb3e5,0x4f7a0,-0x4f7a0,-0xb3e5,0x2322b,-0x4eec,-0x2f4c,-0x1f1,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 16 li9=padCoefficients 16 (liCoefficients 15 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 15 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f1,0xab12,0x41e52,-0x37861,-0x1536b1,0x13e1bc,0x13e1bc,-0x1536b1,-0x37861,0x41e52,0xab12,0x3f1,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 16 li10=padCoefficients 16 (liCoefficients 15 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 15 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f1,0x23c64,0x1aba84,0x36ae25,-0x6b4dcb,-0x9f0de0,0x9f0de0,0x6b4dcb,-0x36ae25,-0x1aba84,-0x23c64,-0x7f1,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 16 li11=padCoefficients 16 (liCoefficients 15 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 15 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff1,0x72c5a,0x8ceb1a,0x2c4557f,0x263502f,-0x5bbcd14,-0x5bbcd14,0x263502f,0x2c4557f,0x8ceb1a,0x72c5a,0xff1,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 16 li12=padCoefficients 16 (liCoefficients 15 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 15 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff1,0x16743c,0x2a034dc,0x1683fa75,0x40833285,0x2dde68a0,-0x2dde68a0,-0x40833285,-0x1683fa75,-0x2a034dc,-0x16743c,-0x1ff1,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 16 li13=padCoefficients 16 (liCoefficients 15 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 15 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3ff1,0x453be2,0xbd38222,0x9949abdf,0x2fd84a38f,0x68336469c,0x68336469c,0x2fd84a38f,0x9949abdf,0xbd38222,0x453be2,0x3ff1,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 16 li14=padCoefficients 16 (liCoefficients 15 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 15 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 15 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^15 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 6=>omega6
  | 7=>omega7
  | 8=>omega8
  | 9=>omega9
  | 10=>omega10
  | 11=>omega11
  | 12=>omega12
  | 13=>omega13
  | 14=>omega14
  | 15=>omega15
  | 16=>omega16
  | 17=>omega17
  | 18=>omega18
  | 19=>omega19
  | 20=>omega20
  | 21=>omega21
  | _=>[]
def liCache : ℕ→List ℚ
  | 0=>li0
  | 1=>li1
  | 2=>li2
  | 3=>li3
  | 4=>li4
  | 5=>li5
  | 6=>li6
  | 7=>li7
  | 8=>li8
  | 9=>li9
  | 10=>li10
  | 11=>li11
  | 12=>li12
  | 13=>li13
  | 14=>li14
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 21 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 22 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_6
  · exact omega_spec_7
  · exact omega_spec_8
  · exact omega_spec_9
  · exact omega_spec_10
  · exact omega_spec_11
  · exact omega_spec_12
  · exact omega_spec_13
  · exact omega_spec_14
  · exact omega_spec_15
  · exact omega_spec_16
  · exact omega_spec_17
  · exact omega_spec_18
  · exact omega_spec_19
  · exact omega_spec_20
  · exact omega_spec_21
theorem cache_li (j : ℕ) (hj : j<15) : coefficientsPoly (cache.li j)=liNumerator 15 j := by
  interval_cases j
  · exact li_spec_0
  · exact li_spec_1
  · exact li_spec_2
  · exact li_spec_3
  · exact li_spec_4
  · exact li_spec_5
  · exact li_spec_6
  · exact li_spec_7
  · exact li_spec_8
  · exact li_spec_9
  · exact li_spec_10
  · exact li_spec_11
  · exact li_spec_12
  · exact li_spec_13
  · exact li_spec_14
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,0xe2479232a143ef56e50000,-0x1423f11581a3b08460868000,0xdc01398a5a983f3d12cc1000,-0x5fd841473b4f626bbb71b9000,0x1deb2009a2b05c048177c12c00,-0x71f9e4dbbbc0ce3d6c3f673800,0x15839bcf1ad496e8a91bb572a00,-0x34db189840010e905c6e3dc6900,0x6b8ca54aca280f085667c265280,-0xb795ef6d12138bf91cecf878fc0,0x10952bb340a440892b72b0d18c20,-0x146c04367f7679071c3d1c6a0ee0,0x1585cc8e27e8afae28bd7fbd97e0,-0x13754d9d14eb586630dfef36a6f0,0xf1a4a185935a5b5fa2eb8318ee8,-0xa0e3a44f4089c4b3bc77422d218,0x5bad0773510305c9d219c039f28,-0x2c867ac7d7de009fe0a14374f98,0x1252e344c46757aed393a173448,-0x65685f03b98a5197db1e29f9b8,0x1d2981e222f6d186e9c814e438,-0x6df708bd7be896c21f1470f28,0x14d629a09e578d4af261f9ae8,-0x317e593decfc6e6d146f5818,0x58dd35348579502e4411a68,-0x7284184dbf7ff126a68d18,0x61d664de60a9ac5bc32e8,-0x3084d2ac22ae7a78ef18,0xacbdfcf584709a0b08,-0x8f26e9cf34accd48,-0x1c699ecc37d70,0xcea30e876790,-0x44e104d7cd30,0xfe5288091d0,-0x2454eedcbb0,0x26c0fec950]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 16 30 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 30 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 37 indices rho q0 m0 0 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 37 indices rho q0 m0 0 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x128fdefe273a92a220c90000,0x19fd8755a8b947461cc33c000,-0x11700b5c02fe901cfca605c000,0x77629efba6d8db469fba2f6000,-0x24956135e428b6cb5a16abd0000,0x88baf5787ea2060123139797c00,-0x194dfbf7968f027a57404c22fc00,0x3ce936ae2469983b83fb0c986f00,-0x79579d9bf2984a196bc8cf0cf600,0xca9fedeebb40e029b73089cf7dc0,-0x11e378ad3ec36ebd96d346401da80,0x1582df9c25df7f8f1166c5e50ca80,-0x161cfd1e00da8c20b8dd5011a9880,0x137a53e6e442d5d5a23a2d39071b0,-0xeb5bee4a12d27e620bcf60ca9320,0x98418a029f6bc943cbf9c8425060,-0x542811c16c460ad4abad91c94a20,0x27934d3370de2d6fb41f499a80a0,-0xfbc84d64829820c201e38e2dea0,0x53f11af1bbf8edd2f02b12ff3e0,-0x1733841918db7f503c445484fa0,0x53ce0eaefb3b075e295afc8380,-0xf2652f420955c3194dd6ffd60,0x22291510f776b7923dc492420,-0x39dbd38ef967f6d2f3ddc460,0x45c332cb9a82146480c81a0,-0x3726db265132f1d3748260,0x18e931ead4eee8d27fe20,-0x4edbf2c1cc6aca68b60,0x37f503dc71c534ed0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 16 31 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 31 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 37 indices rho q1 m1 1 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 37 indices rho q1 m1 1 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x185cd4ad937ce074cb07d0000,-0x218eb34437aa390a7b579fc000,0x162331981068238d7c05e170000,-0x94f1cc6a9be70c58c3f41988000,0x2cd3f5854eaa53512a1513c0a000,-0xa4754ea691914fe8d90d5881d400,0x1ddb35033d7c30310dbf207a4c000,-0x4672d1251c67cf4a17bde818cc100,0x8977979eff8a7de7a3e275c20a100,-0xe0a9d291a49038de835eed034a740,0x1364fc5c99345852da7d4008a53040,-0x16c859d4b2cc0fcf3d78a57be21ac0,0x16da8f058ffd726f5a0f5298fe7740,-0x139ea8d9a7d85209fec397a8e67590,0xe6c1e359b89434d7c0aef0b51d8d0,-0x91161b0c885f36040dc4afc9982b0,0x4dcfad013458518756ca3bbf5d550,-0x236fed6002528ad639ef3655258f0,0xd9dec6da00b3327c7117abfa8390,-0x460434c9c941ebcb02a3075a30f0,0x12998a00095801441c473bfe7510,-0x4058d244f7b1c310ae5125406d0,0xb1824589d90662971d7c72a670,-0x17bc776cb7f536837235082110,0x25e5d6c71d66f5658f363c0f0,-0x2ab616a3c391b70c0d76b810,0x1f33b1d8ad13785c621c0f0,-0xcd046d4b615c937971390,0x23ff91c2035571c58870,-0x15da62a63120c7f360]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 16 32 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 32 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 37 indices rho q2 m2 2 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 37 indices rho q2 m2 2 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x1ff9d723d193e6994a7a410000,0x2b59b95645d4393bd4e03aec000,-0x1c222af3f040422e118e69788000,0xba1d1fa4c53e8ae5faf56bb2e000,-0x370b670b32226886ef46070d8a000,0xc651e6cba4894351fa153970f7c00,-0x2355c5ea84383fe0161f5cb9a60800,0x51c5070ec5d7c3da40f477ea38c700,-0x9c5cfc6a147422da3da5a051f35100,0xfa37e81d156921cc220c89215836c0,-0x152185a25a7a52f50233a935a427a40,0x184229cc5de930513d06e69ababaac0,-0x17c14ab0550993934c83ffe44b12940,0x13e245a8c63a0166deb920c5acd8af0,-0xe3b5aea3a8bda3e5ec358ded969f50,0x8b30d94073c869149b9c889bf3ef30,-0x487341d51798a37372d5ae4cf65bd0,0x1ff61740798c3bc72d268c009127f0,-0xbdea521fb4e81e3d9da333ae48810,0x3ad5c5e33a7e50f81c4f4fc91bd70,-0xf05657a999fa24b83aea99c53190,0x31c3944f0426a2edb487f17f2e90,-0x82e433f8a2df5a25cc3059f41f0,0x109951746530c7b6a81dcf9d490,-0x18f6f04bf4fb74008b47c0e470,0x1a45859766d450c70c32e8090,-0x11b5e9f99820d263fe8e6870,0x699f91df5cff547072e110,-0x106e1fa8d0dd019079ff0,0x88706a2ebdbf9f7740]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 16 33 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 33 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 37 indices rho q3 m3 3 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 37 indices rho q3 m3 3 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x29f7ea5f03121ea931c07550000,-0x3807ccd1279c8d141f22d4e5c000,0x23ca55ed12eeaced932ef45c20000,-0xe8eaaad3f6135dab35a8b4d730000,0x43ba3d5de71338374b7d91fc324000,-0xefc28ca77a854243826ae4c725d400,0x29f20c3aca0ee1b66eb6ace3f401800,-0x5f3de2d17c3d2fd04506cfcfcb2e100,0xb28f774af52ad207a94f41246e05300,-0x117e857c92d72265cbc5026f71672d40,0x17225b22e65e7861644d0ce6a132f0c0,-0x19f723650eb1ab465e8bb9e2c4ee3a40,0x18d4bc2b5bf1f30e4ed3e5bd4f0105c0,-0x1445b72f26578b9a91afe5940d8db510,0xe21f6b6da6693d98ce49e85f8740170,-0x866ae8883452281049c213915a92410,0x43ebc2b7b314d5903f262e60ed96af0,-0x1d0781417cd1345337fc0ab5f3c5950,0xa6bbbb903b32faa7fdd1f69b48e5b0,-0x31cba8e9c8e1d96d58ceaa6fb6e8d0,0xc37b995704b5bbf6fcdf96d437e30,-0x26c1157adcadef69d743ddae01fb0,0x6128669af7b9e9073efaad0b9050,-0xbadca4adb55af4a40c5051ead30,0x1088966fa16f80a1c535236c3d0,-0x103ad7946e581eb9ff5bdf3f30,0xa1535bc725b9afd47265dbd0,-0x367d5747a1c94de1baec6b0,0x77f41feffb2e2b0445e50,-0x353318d4c9d8b263580]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 16 34 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 34 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 37 indices rho q4 m4 4 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 37 indices rho q4 m4 4 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x5e8988296df8000,-0x80c319b7278e800,-0x5150de2bbf15700,-0x1f9d36eda478380,-0x878a2063394f90,-0x1a8c9010d0ba00,-0x3eeedad83b4a8,-0x731fd3168d08,-0xa449a798dad,-0xb78aafb51c,-0xa00827747,-0x6bc6264a,-0x36f581b,-0x147cd8,-0x5339,-0xba]
def m5 : List ℤ := raw_ints% [0x0,-0x3715639cb407c83e114c99f90000,0x4874c8c66af0fb9d668960e18c000,-0x2d93cbeb86b8f5c9091689530c8000,0x123ee0d6604e72fbf1b124151fde000,-0x537fed640a71497aa0cf396c1c36000,0x1229483da74c059c2bc9acb8979b1c00,-0x31f0acc2cf7114fd4a5c347c6a411800,0x6f5049ab1e1071262ff4707c3bb18700,-0xccb319866dc15b0c2d297a5184752d00,0x13a788f07a4ffba6f03f0735624e62ac0,-0x197283faaedb22d4c2ce6ddb438e33940,0x1bef6730fec64656be158040e26660bc0,-0x1a19483845f374db21101c451991c0c40,0x14ca1cc0afa7c4f723f12fbce8fbaa9f0,-0xe1ef092f61c41e74fc63e3f16ddeaa10,0x82a54f09a24500f74669fefa097c0070,-0x4019afda0577d3abb77b9a986319ac90,0x1a8c0eb840775ae2840bb8932f8ed330,-0x9366835f23c43f47bfb9b55cce5cfd0,0x2a707ff645009b8f2ecb678befb91b0,-0xa01961ef4f69919c7f6696b2038b50,0x1e621109cda6c39f5fef29a0dec4d0,-0x4893e5127239085cc1acd22394230,0x843e172c2d8b0e90fb51bad17850,-0xb0164414ffdaaf9d375b33612b0,0xa111f6d02b0529d8c28bcde650,-0x5c17cc77028e4ba66f7b6f6b0,0x1c2463cb68f6c8ee33ee86d0,-0x36b79f0e17548b2f759830,0x14ba525fe47a9a1ecd00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 16 36 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 36 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 37 indices rho q5 m5 5 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 37 indices rho q5 m5 5 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xba,0x1]
def r6 : List ℤ := raw_ints% [0x44afecee19e630000,0x5d2f3726e94f91000,0x3a93fe5211ae04e00,0x16a6e90a7dc043400,0x608088193d5c4b20,0x12c2968bd46dd470,0x2c10c2001096690,0x4fb631b19965e8,0x702b86aa8b872,0x7b162ac7dfb3,0x68cd5390d9c,0x444df9ec39,0x213491532,0xb7be085,0x291990,0x49b7]
def m6 : List ℤ := raw_ints% [0x0,0x484c12bdac4a36d176b48a16d0000,-0x5dbe76754d0cad4e53aae2f907c000,0x3a1925709ddaeeb46e6fcc777860000,-0x16e70046d2cae3564e0e9571d7a80000,0x6725afd73c848450ac32affac414c000,-0x161080c359f3a8ba76e0f7191d27f7400,0x3ba198fde0846ebfd46af2a75cdc65800,-0x8288e107b4d2e874aeb1418ba3d570100,0xeb8eb18d2f9aa212259388413464fbb00,-0x162cbda287af26386547ccc0a6fc710540,0x1c1f20199ed6b3d66735fe0a9cd0a512c0,-0x1e349c96316134ca4712ea02069a09b840,0x1b9447937de28fa94bec7326fc88c3ffc0,-0x15712b6b5e6a216025695a55aaec595910,0xe31b80b556eeee1da0ea837d2e97c75f0,-0x7fc79a50684027c70dd93ed49568c4790,0x3ce38fc1243b4e87ec09b991475346370,-0x18707299aeb6e2cf737667bd58429c0d0,0x8331019c911003376fd44fbf8a1ba830,-0x246a4f5da42a7f99aa2dcc400d2f9e50,0x83ff4b1d300e2f016ff270be1830cb0,-0x17f970ba18ca6837c5e7753264b3d30,0x368c2548b566f56b2ddeebc6b50dd0,-0x5e1bd0ac071618eaa729ce8c417b0,0x75c595f6c98ccae9f04f938d1550,-0x6447fb6a3faa758827773457db0,0x34b2ffed0b96cb280e81cfe550,-0xe8c4b9f7d55035778156c530,0x18f330077a5b14f2e9b83d0,-0x811fbcb92e41d0987600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 16 38 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 38 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 37 indices rho q6 m6 6 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 37 indices rho q6 m6 6 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x49b7,-0xba,0x1]
def r7 : List ℤ := raw_ints% [-0x1b38cc2425f95448000,-0x24cefddfae1b032d800,-0x170d00f223d965b2100,-0x8dfda0db5b52be3280,-0x259cd868ca69a3bbf0,-0x7448f07ae4ce2aae0,-0x10f2efbd5d36ead68,-0x1e6552d19c443248,-0x2a530e5f5e076ef,-0x2dd7087538f19e,-0x26635d7e14be1,-0x187beae17fa4,-0xb8f713a2c1,-0x3d65599be,-0xcec9b97,-0x1518d8]
def m7 : List ℤ := raw_ints% [0x0,-0x5ee3d898f22167f2ebccf53df10000,0x795876270dfd1f4a7a2c82ac1a2c000,-0x4a218739d49b3763e7126c2687348000,0x1cca14064015a22e7491467574643e000,-0x7fa9c6e1124534d36b68bfb57fac26000,0x1adee29d0d5915db03d6bf239b7ddc7c00,-0x4767da7227fdb5a41eb2fb5e5119f5f800,0x9994280fe60949aebc3d5df0e689d22700,-0x11013a0c78679e9258b063059d1c3367d00,0x191f37c36871b01a40645edfcd8c25e5ac0,-0x1f37d3befc94259df3b9eceb7c030761540,0x20d2386fb788f02175802c68166c1cecfc0,-0x1d4c2944b840132f0a91ebaa5085fb65840,0x163d359088bd7567d21640d9be4b0babff0,-0xe5a24a93ae84aaa393f17b1c1dfde3eb10,0x7dbed32d49161c366e2f2e63367cdedf70,-0x3a34c05634a12b1af0104d4a8485b67590,0x16a5257ec5e69a72d4c35bac2667b5d230,-0x7588910e211d1f29cc1a1b3f4db3cbcd0,0x1f73a381017d522a8aeee1cfc2ec5a4b0,-0x6d8834b6015890fb243a0bd124395050,0x130914683313307253b1f32e309abbd0,-0x293c846bd8f2f40363a715ad8b3a530,0x435343cf6a8b0b2c42b79422f23550,-0x4f1f99a292d7a751758ee08347db0,0x3ea6833cc1a75cd7326ea4c46350,-0x1e38dcf48b4023cb8b31764e9b0,0x786b63073a6cecf733f1c33d0,-0xb5f2d568e00c636f49dc330,0x323d253c981d50df6f400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 16 40 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 40 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 37 indices rho q7 m7 7 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 37 indices rho q7 m7 7 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x1518d8,0x49b7,-0xba,0x1]
def r8 : List ℤ := raw_ints% [0x7ca74d434ca9c0940000,0xa81473ee8f6f5e7f4000,0x68eb76cc68d7a6969000,0x283e9ea58f9f13cfd300,0xa9d7e56dcf94be26f00,0x20a7e8d137699e93410,0x4bb6a814f2e7aaf8e0,0x86d9973bd21c6ce58,0xba3a71ae4bf6db90,0xc7aff8fa5047791,0xa52c48703d1082,0x67b8fd85af61f,0x30005262c4ec,0xf83add16bf,0x325f84ba2,0x4e05aa9]
def m8 : List ℤ := raw_ints% [0x0,0x7c8b0c48bdcbd86ed57d01e14c50000,-0x9d26346ba16fd3da57cdb2787259c000,0x5eada64786aa8490fbbc1ef77ad5a0000,-0x243dbc39888d814b7212415d4e68eb0000,0x9e4de227f418b7b5b7f9e00f6b513dc000,-0x20cce63004880abc6ba0de2929cc0559400,0x55be585af903ed3db93628a8c6a85d03800,-0xb5461431112a4b140521b4cba3262182100,0x13b678e2c280906c4c82a60a67f75f213b00,-0x1c9389e24908f24e692776e5ff3871222540,0x22cf4a628d1bac04a4122792e57a1cff5ac0,-0x23d5d2c080d1547389a84286d720a76e1040,0x1f489d14350601e1b8ffb7bb70796cfd87c0,-0x173136edbf82a04b3551f68cb8831f40af10,0xe9870da92fd67250acbcffad226e48001f0,-0x7c7caf91eb3400d1b48980e401c35160b90,0x37fc8b6bc0fc9e8c63cfc84278509e4ef70,-0x151d99de558c6b3be749f4b24b29466bcd0,0x69f8ac1243c716a283f889f96550c07430,-0x1b568857e29ef577669b8a7543f9214250,0x5b757c116ff7a76f8300e4d095f2d58b0,-0xf346db31e0b9647c9b610cb93dc74530,0x1f592d653a91e615a0e12417870611d0,-0x3068031445665ec01d899f3cc3043b0,0x3561ed2d87d7ec27dbf6fa94c7f950,-0x2743f6cb13487b4fc02b31d3a01b0,0x115d896b66567287c8393cf56150,-0x3e558525b1fce4474f8528b930,0x52e3fc8870f0de213022bfd0,-0x13889bc6f464a905085800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 16 42 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 42 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 37 indices rho q8 m8 8 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 37 indices rho q8 m8 8 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r9 : List ℤ := raw_ints% [-0x1ccfff28ca18d02c8b8000,-0x26c1a42208269e52cd2800,-0x18205bff2d89d9ac692f00,-0x939ae67dd40b4a6da3f80,-0x26cb2bf47ba0870fe5310,-0x76d926ec8d95ef4c5b00,-0x1123acb919943e77c118,-0x1e5ad422e1985c54548,-0x29a47a8c08efb5ad31,-0x2c4cab182307da460,-0x244b0ebe34fe715b,-0x1686356c7a62a3e,-0xa4589b876e327,-0x3420b12e0224,-0xa51ea7c6a5,-0xf75432f6]
def m9 : List ℤ := raw_ints% [0x0,-0xa376801f791b8c1178341277b4290000,0xcb9cc47bbabb4789508e12f24a15cc000,-0x7908a4e585c6c140ceea7b315b273c8000,0x2daf70191f25db311b37dd0f545a7bde000,-0xc4a982ddd8de86883eae249397e6ad66000,0x28216a359e601ac0b1c847a32911853bdc00,-0x673dda3219a8d40d040dc5a88ee73d5f1800,0xd6a394295534fd423711f9efca7054f44700,-0x16ef06be939500e7d5fbe59f329e94bcd9d00,0x20a2885a0abc79f2cfec34509d5e255193ac0,-0x26fbd65e398d7df3f89db1b80b52a41306540,0x274f8ea6c4f7e2a44e4ce4eb9e50fe5861fc0,-0x2192c78d28168a8f0716496d0fc79dbd14840,0x1850e559b4b215003d3942ffdc9f2c7fdb1f0,-0xeed37f680d5a9104839abd7af92796c47510,0x7bf6f5dd59844c118a440f044e5037d08570,-0x362d6f116ad7eeec0ca8425f05f31d718f90,0x13cf9f08031e7c2c639ed53e733444c8b030,-0x602434d25bb1c154f1d3ce2125f3bdd6ed0,0x17e8d08cb3323519dec1c030d88bf7882b0,-0x4cd4704599dcd7beaa7661905cee7af250,0xc37195a4c60b6e41bb82899ab73f585d0,-0x17f58bc8884766d6c677a22aac287e330,0x22f832867fe1a865231186e78a380750,-0x2428852a23190eeab5d939470a92bb0,0x18ae65b6ccb458d6c8976f8f8f2d50,-0x9febaf3cd7deaf47674844b67fb0,0x2047f5abe92f9c8bc5045faedd0,-0x25be702688c608e9569dbc930,0x7970ffe06b5588770ad000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 16 44 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 44 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 37 indices rho q9 m9 9 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 37 indices rho q9 m9 9 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r10 : List ℤ := raw_ints% [0x5b55ca525b734caa1c50000,0x7a999783712266f90f37000,0x4c23aad2ea50018f61a7200,0x1d091020729e8a5b1fe2e00,0x79b92b25b8a85def0254e0,0x1739a7a92e63a383e868f0,0x355f959ecaf9025de9bf0,0x5e15e54ebbe09c01ebd8,0x805e458f4b311e752ee,0x87aeb52522c2ffa26f,0x6e4fed487027fb528,0x43d542f3e2372f25,0x1e962b25010cf66,0x990fa1d307739,0x1dc44c01ba34,0x2b906338eb]
def m10 : List ℤ := raw_ints% [0x0,0xd68b88294ef427d6edc4583d1c75d0000,-0x107ef097c79a46fbda65e97bf423c9bc000,0x9addeec7a0e617f9df585d240d6e22e0000,-0x39ab4358aae695f5d717890e0e15b2060000,0xf4c1823bb65978058dfed6b98d89b520c000,-0x313580fd4bb3efc6884d96a59edb02aaeb400,0x7ca49bda61646247911e35c6d316ce1af9800,-0xfeee778cacc028a9817ed84714f645f954100,0x1ac6364d25ae5490fb70cfd38ea3ac07d11b00,-0x256a39fcf5a1e6e00ad4beb503049fa423a540,0x2bd833f27c72f6d2d8d64b1252e2c554857ac0,-0x2b52987e26a6cce5b57acd2db2b3e612909040,0x24358151b927ab25b46633bcd5c23afefc87c0,-0x19a0c6a72f611958aa2a498c9bca09c5588d10,0xf59772079cdaec9150ccf746ea248d0744bf0,-0x7c2708347de829d85ecb6b7cfbbeff22af190,0x34bc8dfa071fbfc45c256077507f9fc8b2970,-0x12b2e77bbb26ac394f807834b8c6510312ad0,0x57c05918ff082076be64a0ac75b8863c4630,-0x150950124e1c277d060a3750609723dfc050,0x40eb076e4bae8315a9fa620d0e3d6957ab0,-0x9de3991f62306943921cda908519861730,0x1267d4c8788ebcffa8d1bd79c6a5e64fd0,-0x196067d2f0da39ca90852ac63fd5055b0,0x18950709332fc47a334a28b28fba4750,-0xf8e368f0df8baeb0015a454ba6bbb0,0x5c2f172a77e8d77ae784453920750,-0x10b90c94c8fd549865fd6dbd2330,0x112d7bc156f50f7339a451b5d0,-0x2f289bc8a77180e079b6000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 16 46 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 46 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 37 indices rho q10 m10 10 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 37 indices rho q10 m10 10 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r11 : List ℤ := raw_ints% [-0x10166bdfc14c9214fe32a8000,-0x158e0f2dfc22495339df7f800,-0xd5bd8bb2883b3e14659f6d00,-0x515193ed109a1088e8cf4480,-0x154014a9686ff1e4b1b55b30,-0x40adc62f9a10ae717486920,-0x942030735f08bebdbcd008,-0x10414da0acacba28836808,-0x1613a9f2668c28eae31b3,-0x1735ecb0435b471fb5e2,-0x12c0ba1b4cfbe0bf395,-0xb7231e1c2cb96ef18,-0x51d8275f0fa3954d,-0x195224410580cca,-0x4dbc0fd7438b3,-0x6fd87b64c14]
def m11 : List ℤ := raw_ints% [0x0,-0x1199722b637a0744a1811b3d0355aa10000,0x1564755f3f95a1cf8b2294dc4982f8c6c000,-0xc65592d1776dac8ff2dfe79faeffefe48000,0x48e4a025c5fef69570a0232c18ada2f3fe000,-0x13126309811edfa5fa46e5e2edf4d958966000,0x3c79461b6ae947c25a10bc8996cdf5c47e3c00,-0x96dfdf71abd1249dc0f19acb1473a66b0e3800,0x12fb45a562cf655327a7634748208ad9bea6700,-0x1f5d76cc32325a1c2292bdd875819996829fd00,0x2b0f00f4987cff1cfc28fbab16d9c40d67c9ac0,-0x318477d7f845f492fba5b5a722301319075c540,0x2ff5bf0a9520c023b5b0d943686046c7ba65fc0,-0x273da3f3550747b3e8a49805f808eedd6ec0840,0x1b264c509cdea8540cb9fa9625b2d2bbbeed3f0,-0xfde90ed2b9dd52470d0ca664359d23dadd2310,0x7d0990e9f29dfee27ed53241edc8b61c834770,-0x33a13f1da97974d172526b6b26efb76e0fed90,0x11c0aa29abaaa7ed211ff79ab2666e21b80a30,-0x5090a93f67d91e1a780f88206a99b156334d0,0x129dc891e29a2501c521647e16ba8b2b68cb0,-0x3729c11a29084d8693767222e050d5c00850,0x803ba51cf36b21e461b82fd22d889bf1bd0,-0xe35637351e8503c03095c6d2bd090e8d30,0x127e6c7ce525c279a04ac5d710df492d50,-0x10c5101da603a64582bacf5980ffbe5b0,0x9d3f26235bf076bffce0df4ac2d6b50,-0x35351f003bfd150f74edb02bc861b0,0x8aa36744e909746b5524c12c1bd0,-0x7d047dbbeecf0f9c7596a2fb30,0x124d46beed4c8a068f674000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 16 48 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 48 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 37 indices rho q11 m11 11 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 37 indices rho q11 m11 11 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r12 : List ℤ := raw_ints% [0x294d93a62325bb4e6323760000,0x374014168b5fb3511de327a000,0x222df2cf68b97aadc390b6d400,0xcfa2928aaf5bb0a11e000d900,0x362268ac3e5d91c775ba9b2c0,0xa4564923e54ba6d4d1d12cd0,0x1773ec5ef804ae2e664af900,0x290a23d7b639544f92b2618,0x37858f6dd40b4669d7d98c,0x3a1caeae7ea6ffb410f0d,0x2eb4fb3000d60607ef0e,0x1c55a3592c1e7864b6b,0xc92478d726a43e9a0,0x3db1119410e1d5f3,0xbb685fa830c286,0x10a29845bf82d]
def m12 : List ℤ := raw_ints% [0x0,0x171965d8f290298a13f973c014606f350000,-0x1bc12a0b0f76522ea2396a651fd4e684dc000,0xfe390c7aafa695d184d81bdd5daf9f6020000,-0x5c418855619ae396cd3e823b02859dfd210000,0x17d19ef8b5883a3e4d06fc82eb514b4637bc000,-0x4a7a061811e5956d6167c87f057f0e3041cd400,0xb718069a5c940ea854510c84f7b87e4bf6bf800,-0x16ae15eeacd4330adb1e0fb8ff5f9055759a6100,0x24ddc5fe4d2e9a9b1c61508deffde34af99a7b00,-0x31bd098e71f1c47def1580f2e17991863d51e540,0x3827338ea951aedde71ef878f9c0fd3a8fe1bac0,-0x35542da9f489a9df7e73093732b47a00b81af040,0x2aba670783cd87589be821d13bdd61084f4a27c0,-0x1ce7f5c486ff6d13dfcca79b9318a9145ca8cb10,0x107e53c9d016e9c06336ff275f200d5ec691cdf0,-0x7e9e4ad55f55eeeaa539f8a18e5abd9f6911f90,0x32d4b5e8f0dec1e8bcc85eb5150b250e45f5b70,-0x10f3584bf151807d92dab11303d9f52723ba0d0,0x4a64159e6e5456eff4efd121cf3ee3cbddf030,-0x1091589b58a151e4138b049834d90e6579e650,0x2f2140d4f875a025920c363d9317153e0b4b0,-0x68aeca01cb4a7b7c164478b82613eadd5130,0xb0513ac1f1d992f36adda3ea32d9bbb35d0,-0xd8840e43f31d277af1286d4e75ee743fb0,0xb7a1ad8066da6d55324ae0971a0a1fd50,-0x63917cb151cbaa9b0ce817e0be4fcdb0,0x1ebed35d97daf6bf7d481bdbd8dd550,-0x47d7d35a8fc74686267845a8ae530,0x38d5fbcc5d40d915eb61d0413d0,-0x719435c79fb3b9af50d58000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 16 50 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 50 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 37 indices rho q12 m12 12 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 37 indices rho q12 m12 12 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r13 : List ℤ := raw_ints% [-0x624a3c62bba4ea3b08f89498000,-0x834ac14fe6ad42d316f948ac800,-0x5117359689fa101f474df8cab00,-0x1ebb9c6c2e4394e66e7d3bf4980,-0x7ff157b188ad6dce349e55a350,-0x18383563cba9908d3feb36ff40,-0x3728ff9d4451a4e3f525837f8,-0x603dd09614f75b9b97c9b8c8,-0x81c5092ab7f846b73385a75,-0x874e51878e3357f87a2824,-0x6c45d7f2eaa348c3ac00f,-0x415920c21be90a06deb2,-0x1cd20edbe2f9b777a33,-0x8c6f28f6848d397b0,-0x1a7055a372f6f081,-0x252aa80568a372]
def m13 : List ℤ := raw_ints% [0x0,-0x1e5155acbe5d36853a3767ec1abe91f590000,0x24062b2c134db51eff6e6469b8f6ae8e60c000,-0x14623051c710e4dd18f85221f37dc338b2c8000,0x74e91bc53705e37e0e3065a0dbb6bf93599e000,-0x1dcc2b59a24dc0e3d27fae4f05354a71c45e6000,0x5bea1692efa559439a7095a98682278354ef9c00,-0xdebfe33abcec7786a72a82d496c96012c4825800,0x1b2d7b78d624e580f73e194bd673a4c6ccebe8700,-0x2b797da968bb24f3ac71076e98cd3084c1e0d5d00,0x39aa1028ed8d56823fdf491180fb5a6737259bac0,-0x3feedc198f2d653d9386fb93b811c4024f643a540,0x3b8e4ef4d919cd4caf7c205a28367f384149a1fc0,-0x2ebdd0d42a526dddd627fcf288d8ead5258864840,0x1eed7a688e8b87364ba856e012e812b856aae75f0,-0x113b0342149efe93224684d58a61ddc79870ba110,0x80e7e1f22e0f47378f805260d1328dd673be3970,-0x3251bde86f23921b06bad0bd553669754c639b90,0x1046631dfb44ae64c230210bdbda1c8a15ff1430,-0x45129a126a8d15b4518a65f5d538f0b0acf8ad0,0xed34b967dd705530cb5a6bc52c07eff0f906b0,-0x287a995d55ad9220f4ac654e50252aed4f2e50,0x55e139e756e950dcf9fd4da36ff144eba21d0,-0x895b70bc25d166944081abcd7084d51ea730,0x9f07f2b643f9372e8d9e37d37c24619e350,-0x7e0ca135fcf7466d4c9afcf6b6f4c88fb0,0x3f2c51447c2030daaa46ab7e8343df950,-0x11c8784af58101f933ab84f92cc2f3b0,0x253affb9512c58618369fa421b99d0,-0x19d323dfe151589bb7c597465d30,0x2c0762691f2d51f659a8d0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 16 52 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 52 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 37 indices rho q13 m13 13 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 37 indices rho q13 m13 13 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r14 : List ℤ := raw_ints% [0xdb9a14a945ff6a5ab8837e070000,0x124f5d000f599b82b7e32ac45d000,0xb4af1fe3f8296a7983f11f52f600,0x445e6459c4275d2b2682c9066400,0x11c1d28667061391ff07fbeed4a0,0x35acbf72d885a3d7d15550b30b0,0x79f7ec8ffd4f3cc78b1fa03810,0xd443850864fb8a0ebdbbfb158,0x11d6281d97305d6c1a1de286a,0x1289505bb7f915e56339936b,0xec6f68d413a0f5f7d8f334,0x8e155c590a3b47ee1cd71,0x3e595d38a1df8bcfe29a,0x12e07c3ef5fcb2105ed,0x387813b0230eaf398,0x4eba8211d52f7af]
def m14 : List ℤ := raw_ints% [0x0,0x27cac072b9da578edc68b865e31a1f924d0000,-0x2ec6e5a6cc19014aec64aec101bed51adefc000,0x1a2bd5981a2b55812ff70cdf5a1e156751d60000,-0x94565a62549dc51f89977a615714b682439c0000,0x255699f0fec3c691a4d1b9e61e3539c5ad286c000,-0x71aad83a86449505493f4b699089ad7e0b9cff400,0x10fa820aa0a76564e771125b71cb1b93e9461b5800,-0x20a8d45f50f1951fe805f4d64b7b497a9b83278100,0x336e9422fd44b056cd9061d0c97ea2de41b531db00,-0x431793d87be9e039241f77ee706fe9d31386006540,0x491382f5d3ac08fb4acc0489ad1c2b219354093ac0,-0x42cae0f8ecf5986fec57733e91a6e0812f75a81040,0x335d3eb5750780f7de617562d8d8ba1c3c924f07c0,-0x213ffcb030edfc41e61ea7849814c23a544e3ec910,0x1217645bd9d88ad1ad80955b656df2c623ea6deff0,-0x83ebe9cbfe88a9441723a8aca258a174329e1ad90,0x3214861740b4031865782f65c9abfddc07c7a2d70,-0xfb60ddf0d7ccc91f0f9203f53e2824a27a3df6d0,0x407b6db7d9efd7cc9d8e42329b151820417b3a30,-0xd5631bcc652b57511f9afa81c5a0379b9d06c50,0x22f18d363e6f897356ccd2e08271ed826de8eb0,-0x46c9d24240cf6a30bb7554b052a880c899eb30,0x6b75cea6a72f9bbc465cf7c35fc6f7d06fbd0,-0x753a266e7eaa61063017f55e1c5b2af349b0,0x56c332cc90c7f8deec569fb707f787f9350,-0x28276f037c65944d1ddc8ff5e32cfa3fb0,0xa4b4b0882c6cc8b482faa37fd84a4350,-0x134aebcce6cadf51b776ba6782c0730,0xbba482aeeeb02910d83bfca211d0,-0x110efbb723ebbe54b7c2f60000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 16 54 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 54 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 37 indices rho q14 m14 14 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 37 indices rho q14 m14 14 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r15 : List ℤ := raw_ints% [-0x1d12c771fa9c81b8e165edc7488000,-0x26bda6eddf18166b707134ba779800,-0x17dcebf379f419abbd844a86a5a900,-0x9043fe67676f60a8df1beb6706e80,-0x2568eed1bcc905f288d4c230aef70,-0x70e0e5a9ff9ed738199a7a365160,-0xfffd43b641ef33579cebc0799e8,-0x1bc81325bab2a627368a3b4a188,-0x2541e9c65b2d02f8c34beeea77,-0x269bd21d17c24860e52f46e26,-0x1eadca77450bb86305ddb7c9,-0x125e25f420548c50995340c,-0x806992fb4385921acaed9,-0x26afbb3dd2d0601c67d6,-0x730fd3a799e1aa080f,-0x9f54a0ee8d160810]
def m15 : List ℤ := raw_ints% [0x0,-0x343a1c9693ee92eb81497205ba1249700510000,0x3cc38da71b54962922b0e31121044bb344aac000,-0x21a11afc5f25bd830b04681d26eb2968edf148000,0xbc70619a1dceeb5135ae6471ba69de425798be000,-0x2edcc9a51601521bddf96813b9aaf708997d9e6000,0x8cd97ea8a1a21f2422aa5a1fc985429b239fb7fc00,-0x14c17e522fd2468940fb4b8c798424e4f249b7f7800,0x275b0f0c226be7db254980fbc588caa72f89b18a700,-0x3d096da8e8c95efdabaffdd418c09ca8f9355cebd00,0x4e5590e8e4999d4ccd3b3fa423eaea254a8d7e39ac0,-0x53d8f508b0c382009fe145b2ff0f8c1ff820e05c540,0x4b38466843d42c059a4d862e378f1140a0964259fc0,-0x38b20a54d88d3a8de061f71af28d36707111b94c840,0x23ea47f9b7fde35ace0fd6a9aa50410fd45888dd7f0,-0x1316cd5c23c2352f61be673ef79364a6864093b9f10,0x87b2e83a34a5164e4ca760aeb8df3bb91fc3d4ab70,-0x321a78e5a04b7a4e31c62338c07076ee55b94dc990,0xf3f496a22a3c72694506a6130f1f9502089b49e30,-0x3c8397a8d899121b0e6280863f1636ad3e3e260d0,0xc0f2e06be79783da3a246dd100d1c4ac705300b0,-0x1e503e85e684430283ba981d96c4399aefe4d450,0x3a9d4e14b3d6db9f66941f545df71652b3627d0,-0x5468fd3a6d815c223010a32d1fbb948e1d4130,0x56b410ef54c17df42032014cba90c445e1950,-0x3bdf7c34f41e2327ce99ef24ffbb923bb9b0,0x19906d07b56527e6835010106df0cc24750,-0x5f6898a804879f8d913462585aeb1c5b0,0x9ff0c56fc84429b19c4c83f3076d7d0,-0x552a962dc79f2b9eb2e5b00f3ff30,0x69b0e7fb62e11d61fab5f40000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 16 56 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 56 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 37 indices rho q15 m15 15 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 37 indices rho q15 m15 15 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r16 : List ℤ := raw_ints% [0x3ad6ac2075f57b69f68ad9569f80000,0x4e529177fe6b9f2283ead8917860000,0x3030413584f1f02be0e787f0955d800,0x122f49d41f6b481c2e7900826ee8f00,0x4b5758be6c0b208becc3006e010a80,0xe2f855d32b59902d6109d6bd0b090,0x201d19816b8285254152ea15fbd20,0x37a6feb0abb61d21c1a62bd08498,0x4a77fb77f010042bc3d4e88c488,0x4cf9e79bdb4856f2606c02fc89,0x3cfe34fc9ce5103a9885c029a,0x246659a52233502ea5f61437,0xfd8b5a1c55dca6fa4e8954,0x4c101f8080e8290405a27,0xe12065baa1edf67046a,0x135f9421ad28ecc571]
def m16 : List ℤ := raw_ints% [0x0,0x448c4585a22920d519b065a78438006306a50000,-0x4ef6ca368f2fbaaa7d1017273dbdec5b4a201c000,0x2b3f237254d0bb151a103b26e00039214a4eaa0000,-0xefa9c4534a60820dfd0d796d6e387d6b15c5b70000,0x3ae876ddf079670db7ed0590b26db720a7611e1c000,-0xaedf66fd6ae3f4670d539e5c47147840f09d2301400,0x196ec1c1ca4e86f6434f3540c831eaca13af3dedb800,-0x2f8d9c06be420ca591c294e3b751070b47fc53cca100,0x48a86433fc06899a0456d6000953b179c7f466393b00,-0x5bc5e5637ddc8bc4e34c8ed59447d96cc9b257c72540,0x6091582d54f9302e1db64753d638fa9bd524d3be7ac0,-0x550e22d412e4fc32aedc475323aa2fcacbf965b57040,0x3eda51f7095c47dc8eb7d2180d0d8fd7148e9abba7c0,-0x26f91b49ec096330fc3023d2996065f5121b90a40710,0x143d3966ea178eb50c01f321cd892ab248c1959051f0,-0x8c4873c3c10fad78aee975e236a2c940551b4fafb90,0x32621ec2f9d077052d64a2de417cc6dfe9525443f70,-0xedf975268dc7d4968091a59b33dd07db85434e8cd0,0x3914d14fc6e35ea37a0eeffbc8c7cce8561b444430,-0xaf56cbe9eea63f05c970a8204d1b360b89ee53250,0x1a6bedb2dabe2802203421d8ca4ec8598895e28b0,-0x30bef9665f99109baf47939058f93d00f377c530,0x428f0e56e79c55ce379ab7f79535d1304d681d0,-0x4054941905b8d11a65edb8eb47a341b8f293b0,0x296a12482029c8075e5cea13c0ec1fa8ce950,-0x104c93a858d10fa6331230f51675b6f731b0,0x374c4c30746e23f6b3a10f9c2cfb583150,-0x52dba276a3a1fd29be200f3e80c5a930,0x26a240258bf49d7e426c31757f8fd0,-0x28e81cef4f14397a3d4f2580000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 16 58 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 58 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 37 indices rho q16 m16 16 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 37 indices rho q16 m16 16 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r17 : List ℤ := raw_ints% [-0x72780d88cedc5e385d8751c896278000,-0x983b724bd8ded54866f30ad507ee6800,-0x5d909fbac4aa8bcfee6db140c9f46700,-0x2344874dc47c678cdd7fed61926cb380,-0x91ee679cf5204750bd0163298575f90,-0x1b700deb8acbe9bd26df50315430f80,-0x3e040f5cd9dfc2bdcce03d569969d8,-0x6b4867f899075f31e4ef9be196e48,-0x8f45ded133ff50fac25aa627b8b9,-0x93c5228f3b2c8d7a433bf9222e8,-0x74cbdf1191bd451f663a1fb5c3,-0x4581c3b8699c1ab07934b2e26,-0x1e29c9efb821c290ae05883f,-0x9041e4fa6844fd40988e3c,-0x1a92fd06e8b7e75cfe45d,-0x2469ea0bffba85f92ee]
def m17 : List ℤ := raw_ints% [0x0,-0x59f81b3f64d5fb17b1b7856bdd898081f8b890000,0x66a791c5a61387f9638f06cc740ba177d14a24c000,-0x37a81dead168e7cbd155ca85638b8b7d6ee999c8000,0x131291891311b84e1693eaf26c65bb48d7a54395e000,-0x4a29ae0384a1255eca59998afa4058d9c49973166000,0xd986ffe4cd9fd680e93e7502d71e0feb3c7a232f5c00,-0x1f3bf420c03bd0707d009bb6f8afb6431838d065d9800,0x399c26701ed9db6cacb8104bd9110b5c27950d798c700,-0x56c0358a4a5a4eb711e421f1608b7727b24f0670a1d00,0x6be08aa600b8e13f7f3422ec02433edc0effce8543ac0,-0x6fa0663ff4b0a0d33f813ef21f490f8907192dc8d2540,0x608f537283da460ffc5a2dd6ee2bc347a7e6c8447dfc0,-0x45f9eb9ccf9e4efd342fd635455cf2f5dcb5b3efc8840,0x2a7b837af0784196bfc443a84716680915e07d695f9f0,-0x158f608d699e2bac8cdad7e99fb8841766f89ce4bdd10,0x91bb65c5da0033130614479c5fb37ed0920e779fdd70,-0x32eb09850f41c5054985627c937da9180db4c6673790,0xe94f2ef8b210526b05e1eb5aee166abb69d0da2e830,-0x361ca4a3fb4321272d0ca9f3771dec724d3c54c76d0,0xa01b8de1f8eecd9947e35ed9e79dc8c3ac53d7bab0,-0x172280c3e6ed11b450d912b43ab5948029e1dbba50,0x28b560059bf34ecce3766403b088d773a94df6dd0,-0x34ac8e9cee1505bcfaae9c672e5a91cda4289b30,0x2fdf41831a2f33a85f9b40dec1120f049778f50,-0x1cb55a9063c99241d4ccd660f018f4baf5a3b0,0xa67c6a8307e783c6454124619f6639051550,-0x2010951073946aece0d7bc639241c0e17b0,0x2aea7f6b90a82a47eb9566d7b27c095d0,-0x11840f2ac365a2bc31c9e21d2872130,0xfd32311b18eb0dbaa40c6d00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 16 60 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 60 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 37 indices rho q17 m17 17 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 37 indices rho q17 m17 17 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r18 : List ℤ := raw_ints% [0xd7273fcd143930c151e536c643ac90000,0x11de3d4e236413dc0cef8bbf22e2903000,0xaf8c84eb5bfd9dd9efc8e99cc9f0e7a00,0x4219f7c675fe9ab2f270675a0ba06da00,0x111337aafc69599c815f8d5fc62ab6460,0x334d1c791898f0bf5cf456d919c98c70,0x73c9f68ba04e541e2aa0fcea2978030,0xc7fda0793520658b9553124152d3d8,0x10a9cd7f34de2b123be335a9965ae6,0x112712c7acef243ea4c6fc4386367,0xd870c8ab8f2d8efe5d44733ae40,0x807d03344a0c4b4e5f4de704bd,0x379a80eaf9db380366e7184ce,0x1091669de7f113e848638da1,0x30a83937a94aef04ca07fc,0x4266073370d79ad41473]
def m18 : List ℤ := raw_ints% [0x0,0x7615a3c33458d98f1940df1d92c478aa96723d0000,-0x858081c8f6a7be2f59f01b6f881235fd42b1503c000,0x47ae587f446a8ffb89a6883fedbce670a277657e0000,-0x184fd77444d01db55bee38c2c5cd7f284629e07320000,0x5d81ac8ba66574aae647182596c75d5e3128924ccc000,-0x10f169067cb5fed31eabb9ce0ee2f39d001eafecc53400,0x2671c0fbf56c145a095cd5a71b34bbf930432685bb1800,-0x45f9490d79615790141c3b252a6ad95c9ff2a6f759c100,0x67e19436e06a19ccc1e18aeb3f28aa4b7ca584d8289b00,-0x7f38da59ed598e2e835657d3b2f0f833e79e9348402540,0x817f6c53c36f4bae6728636ec4401661ee256bc7b17ac0,-0x6e0c5a33865cbd3e97cee4db07ee85a9bbbfb835131040,0x4e3b8c820eae300d15d4ec2246692660a181d4463807c0,-0x2e8348098ba8bbaf4a01976eebe1116a1670106c2a8510,0x1712d505923fa90a9b69adb87626de0207cc1061e373f0,-0x981e212e75c14eeb6f158575baeefc1ff0e6c7a168990,0x33b5c775c9af352dd13b741ca4669ded6ff21b3401170,-0xe5dbf22aa1cd41e955a3600c39eac5caf9f13993e2d0,0x338bb8e9c500ecad6531e05afe171a8176a0885c8e30,-0x92e28e1cd986d1fb4d6478aeffad299352e4994b850,0x1458a07b6182fa8393826ef37be3585bd774a1702b0,-0x2221e1f24d9212060feaef82e126c878e6dee45f30,0x29d470ec7d8a68264baab05d3e9d9edd66d8f47d0,-0x23b92c5c53b08cd9ed2de81c3200a6c4a3809db0,0x13f0acd684644cf15187dc3e20b4c5638b77f50,-0x6a67fbaa517218c2446661ea727f80a1a23b0,0x129975861a9595cb80d3c5a9e58f623c1f50,-0x163903f27dda5cb44c419cfe0792134b30,0x7efe713fe08bdf6fc74116bf0950dd0,-0x61e6f7ab41addc43864143600000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 16 62 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 62 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 37 indices rho q18 m18 18 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 37 indices rho q18 m18 18 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x4266073370d79ad41473,-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r19 : List ℤ := raw_ints% [-0x1885228fb0a6cd5338aac029a893c668000,-0x208e76bcdf6c3522c904ba96111c3a73800,-0x13f95df47782ba6943fa592179871a5e500,-0x783952be27c61bf60d806342e0eb579880,-0x1f0601b618152ea3c5bcca95eed62f23b0,-0x5d19e6a3a618cb3c9990742c981a029a0,-0xd1dd7948e1fb76f6c6591415e71bffc8,-0x169f76ee74cf0975d5f4ccb21c335f08,-0x1e1c9d2dcf109eed61dc29c02f3e43b,-0x1ef11acac2387537ca2e15bf14e96a,-0x185ad5868d2cf8164771edd1904fd,-0xe6d2ca2d3b627166981fb607c00,-0x63a4e06aad5c7aeb25a1bfc365,-0x1d9bc0e8c94069be2ecb313e2,-0x56ae9dc7c780ff7d8b1d66b,-0x75ddcdbbdeafb9e27390c]
def m19 : List ℤ := raw_ints% [0x0,-0x9afc66f034b49d8bd12524d6d0a1de5fe575f010000,0xadae616ab395cc442f209f265e4b95706788b94ec000,-0x5c62aa0d7482eec70746cea6fb323d23824c670c48000,0x1f0627cdc2b249ae081e26f1fdb35541fa993c0937e000,-0x7610e67810be69c80f1988bdf46445f7ab4229a2c66000,0x152728b830a161e42ee4524091ef699345eab76fb2dbc00,-0x2f6be0fad21df41b2757717db3961c7d8fb44c3ba04b800,0x553484b9f17142946b0ea3a89b253d923f6d33d493ee700,-0x7cc02879f42abc94c79e5172f907de603193603e1af7d00,0x9684236915436861b2417b5d4f962ccfadeed930e719ac0,-0x96c23e9d07e82842b5ad28aa4cb67817b795ee32e7fc540,0x7de656405af5c56b2c0712ad04cf566d0f8b7543faadfc0,-0x57d230c5a33f0207a8ef9eb055fc0ebee7a720e99638840,0x33256e64ada2f49168306b95898ee75796e384cc93edbf0,-0x18ce2672d29e949f1917486c0fe1db66ba3179b0c535b10,0x9f86ef4f299b74f90001bee3b188d6ac593fac9be4cf70,-0x34c3dd2b3f8ac1c4996c799cbf86f7bc9174315792e590,0xe38b7e4242ec3c9c134d04bb886254a8801c9c045f230,-0x315543bde837032d2c2a6c6a288dde87825de370dccd0,0x875dd93ee13ce007f7c28968b2fb14e1f04b6e4f34b0,-0x11f845c058a12a8f0b69cf7e6d67ab45815cd0d3e050,0x1cba669ad43f10b687dc4c1b409b3faad683948f3d0,-0x2153b03d90a3e1aab1d779d32828fb30d79437b530,0x1aba084605e45821071d709d49afa8870410b4550,-0xde001914d6090adc872137ed24d0f8356594db0,0x44135e7deac6b22b5bbda824cdf2f08f626350,-0xacaa87bebd6dda72aa955342a34ced9be9b0,0xb810e8cd073754e128b8cbb454357cd3d0,-0x3983fab67b3f6a3b5d0f7ccb6523c330,0x25d6825326197e805d8ef57400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 16 64 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 64 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 37 indices rho q19 m19 19 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 37 indices rho q19 m19 19 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x75ddcdbbdeafb9e27390c,0x4266073370d79ad41473,-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r20 : List ℤ := raw_ints% [0x2b86c3eefdc21327f1549e01a6c355fa0000,0x39c0687fa743e0509a80f38bdcd864ec6000,0x236782476ad94255710bc91aa3de0907dc00,0xd4ea85bd82d3714613eaaa3d2c1be7bc500,0x36e3facc8019640c68a551f8bc17cff3240,0xa48de6ab78ab1614e31abdd528c3039450,0x17281260fb7867135b74d50ec547a69940,0x27e372e3697e801793d864c0c0aef4f18,0x35048a56245c466fc5b9a7f7e5ad0084,0x3664cc5cd87bcf7175a610354c1d905,0x2abd52384086822a4d98053c2acf26,0x19446ea71b5c76cb2b8af98a01403,0xae247a85f9e33cd967729b3f408,0x339e62e1217ed749789f8eb35b,0x96b446a5fa7bdca7080c894e,0xcc487cebc6345598664bb5]
def m20 : List ℤ := raw_ints% [0x0,0xcb6b471b452d0ec78280c059f1d473dddd2acb150000,-0xe20804b3b784a7690935aacf5663ce5c87e373375c000,0x7727357f9ef708a797ac731e2334c7fe3f86ea6f520000,-0x27a186aba3f06b24aa52ef15e66ad06f7fa0546b9cd0000,0x95491bed815b9f07955f92fd44a0a4af7a42d187107c000,-0x1a7499b7148c5faf300b5eb89a58e1c6b3f663ba8dd75400,0x3a9e405715784953eb5b25fc743593576569ddd5b0bb7800,-0x6801d04c42ff1a1df7b4ffaa0b139e894b287b71819ee100,0x963b63405b7da94f6297c41709c69f399dc54a7dc34ffb00,-0xb2a1e5b6f4a7f41c2e411c6a4bb3b8131e68e0d4ed9d6540,0xb01d5e0b61fcd00cb84f9f04a2c14c80fa9ce01aca583ac0,-0x9092abb4f00e1d70259d90a2e901a495b4c424d6e44af040,0x62fad1d008b1ac27505548b7ad5bafcf99b8d523b65a27c0,-0x387ad885a0705eec122935b606a6ad80aa12d2e264664310,0x1ac90c5eb282c45f51875232f7c98abfe54fd3a8f10555f0,-0xa8107506eaa1e31a003dea0a36086a87254c5bafc325790,0x3617c59753292bf14f809a3f7256528222ad122937fa370,-0xe24e6e0cc4d2f0c706f5011a569b923ec0ea292f5cf8d0,0x2f6e9697e6b3ac06d3707df84863777b9ea6d7da4d1830,-0x7d4ceac75b6f43d30ed7ebb0875583aa86e28f88dfe50,0xfef9bb9960d827fa303c7b4c82dda6c8ab05d9fa1cb0,-0x18449fa6dba2ce3e0821306c192e11d89bd3c5bbb930,0x1aa274d57b13915d11631e684cb599586378be14dd0,-0x140b470c34d10453c062a7b49cf454414780a967b0,0x9abb0893d6da2193374c5d38891e2bfd4e635550,-0x2b974fc865d2a07ec9e2f8d90cb667fd49815b0,0x6433a6ecdb1335f2ca9a3a6c889bc5e110d50,-0x5f41d28b9d8125ded447c4258d91c61ed30,0x1a090713ce77d5ff7055f570a8bb58bd0,-0xe9e07b838f7ba9d4443f375800000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 16 66 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 66 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 37 indices rho q20 m20 20 4921248682285534190592000 21=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 37 indices rho q20 m20 20 4921248682285534190592000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_20
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<21) : intPolyRF (mz e)=rfPoly (C (4921248682285534190592000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^e) := by
  interval_cases e
  · exact moment_source_0 size
  · exact moment_source_1 size
  · exact moment_source_2 size
  · exact moment_source_3 size
  · exact moment_source_4 size
  · exact moment_source_5 size
  · exact moment_source_6 size
  · exact moment_source_7 size
  · exact moment_source_8 size
  · exact moment_source_9 size
  · exact moment_source_10 size
  · exact moment_source_11 size
  · exact moment_source_12 size
  · exact moment_source_13 size
  · exact moment_source_14 size
  · exact moment_source_15 size
  · exact moment_source_16 size
  · exact moment_source_17 size
  · exact moment_source_18 size
  · exact moment_source_19 size
  · exact moment_source_20 size
#print axioms moment_source_20
end
end CatalanCore.Li2.NVMod.FamilySource.U5C21
