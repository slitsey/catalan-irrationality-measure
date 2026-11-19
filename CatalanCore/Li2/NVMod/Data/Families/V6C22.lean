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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C22
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,22,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x5e8988296df8000,0x80c319b7278e800,0x5150de2bbf15700,0x1f9d36eda478380,0x878a2063394f90,0x1a8c9010d0ba00,0x3eeedad83ece8,0x731fd3178de8,0xa449a7b85e1,0xb78ab1e670,0xa0084010c,0x6bc6dcc0,0x36f90d6,0x148890,0x54c4,0xd8,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0xe,-0xe,0x20d,-0x9ed,0x69e,-0x59dd2,0x2cee9,-0x369acf,0x117938,-0x29bbf8,0xa6efe,-0x42dc7a,0x3bb2918,-0xcbc48]
def rhoDenominators : List ℤ := raw_ints% [0x267d98,0xd68,0x1ad,0xb,0x16,0xa,0x1,0x31,0x8,0x48,0xf,0x21,0xb,0x8f,0x1b5f,0x2cb]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 22
  decide +kernel
-- kcost: 1 s estimated; once-per-family integer numerator/denominator source bindings
theorem num_ok : numeratorCoefficients .V bases=num := by decide +kernel
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 17 li0=padCoefficients 17 (liCoefficients 16 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 16 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 17 li1=padCoefficients 17 (liCoefficients 16 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 16 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x41,-0xd0,0x1ad,-0x23c,0x1ad,0x0,-0x1ad,0x23c,-0x1ad,0xd0,-0x41,0xc,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 17 li2=padCoefficients 17 (liCoefficients 16 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 16 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x8,0x13,0x20,-0x13f,0x3c8,-0x6d5,0x840,-0x6d5,0x3c8,-0x13f,0x20,0x13,-0x8,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 17 li3=padCoefficients 17 (liCoefficients 16 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 16 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x0,-0x37,0x140,-0x37b,0x580,-0x483,0x0,0x483,-0x580,0x37b,-0x140,0x37,0x0,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 17 li4=padCoefficients 17 (liCoefficients 16 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 16 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x10,-0x95,0x1a0,-0xc7,-0x610,0x115b,-0x1740,0x115b,-0x610,-0xc7,0x1a0,-0x95,0x10,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 17 li5=padCoefficients 17 (liCoefficients 16 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 16 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x30,-0xaf,-0x1c0,0xddd,-0x1f10,0x1dcd,0x0,-0x1dcd,0x1f10,-0xddd,0x1c0,0xaf,-0x30,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 17 li6=padCoefficients 17 (liCoefficients 16 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 16 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x70,0x103,-0xee0,0x2171,-0x70,-0x6675,0xa5c0,-0x6675,-0x70,0x2171,-0xee0,0x103,0x70,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 17 li7=padCoefficients 17 (liCoefficients 16 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 16 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf0,0xa19,-0x2440,-0x2f8b,0x13db0,-0x193e3,0x0,0x193e3,-0x13db0,0x2f8b,0x2440,-0xa19,-0xf0,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 17 li8=padCoefficients 17 (liCoefficients 16 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 16 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f0,0x2d5b,0x1fa0,-0x28117,0x2e610,0x443bb,-0x9ef40,0x443bb,0x2e610,-0x28117,0x1fa0,0x2d5b,0x1f0,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 17 li9=padCoefficients 17 (liCoefficients 16 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 16 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f0,0xa721,0x37340,-0x796b3,-0x11be50,0x29186d,0x0,-0x29186d,0x11be50,0x796b3,-0x37340,-0xa721,-0x3f0,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 17 li10=padCoefficients 17 (liCoefficients 16 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 16 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f0,0x23473,0x187e20,0x1bf3a1,-0xa1fbf0,-0x33c015,0x13e1bc0,-0x33c015,-0xa1fbf0,0x1bf3a1,0x187e20,0x23473,0x7f0,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 17 li11=padCoefficients 17 (liCoefficients 16 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 16 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff0,0x71c69,0x85bec0,0x2376a65,-0x610550,-0x81f1d43,0x0,0x81f1d43,0x610550,-0x2376a65,-0x85bec0,-0x71c69,-0xff0,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 17 li12=padCoefficients 17 (liCoefficients 16 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 16 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff0,0x16544b,0x289c0a0,0x13e3c599,0x29ff3810,-0x12a4c9e5,-0x5bbcd140,-0x12a4c9e5,0x29ff3810,0x13e3c599,0x289c0a0,0x16544b,0x1ff0,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 17 li13=padCoefficients 17 (liCoefficients 16 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 16 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3ff0,0x44fbf1,0xb8e4640,0x8d7629bd,0x2643af7b0,0x385b1a30d,0x0,-0x385b1a30d,-0x2643af7b0,-0x8d7629bd,-0xb8e4640,-0x44fbf1,-0x3ff0,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 17 li14=padCoefficients 17 (liCoefficients 16 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 16 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7ff0,0xd2f2e3,0x328cd720,0x38086f2d1,0x17edfc8c10,0x488025ae4b,0x68336469c0,0x488025ae4b,0x17edfc8c10,0x38086f2d1,0x328cd720,0xd2f2e3,0x7ff0,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 17 li15=padCoefficients 17 (liCoefficients 16 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 16 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 16 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^16 := by
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
  | 15=>li15
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
theorem cache_li (j : ℕ) (hj : j<16) : coefficientsPoly (cache.li j)=liNumerator 16 j := by
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
  · exact li_spec_15
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x14ba9ba5e641379000,0x1e51edf364f47420c00,-0x15499265995ad4c81800,0x98cbb4442ad9eefcb200,-0x312fdbdb60c78a831e600,0xc18bee6231bdc30b59bc0,-0x25cd4e48413eaf54a4af80,0x6047ce4687925323a967b0,-0xcb8794f96cbb1f3e601550,0x169c980770737e6d63bce7c,-0x221e8d01da3a8beafb03244,0x2bffd50be498d62f076a950,-0x30b79b501e1aadc6ab1cf30,0x2e724ac4adeb7c10da59e33,-0x262dcc0367d353b80339fbd,0x1b0dd9769f0f2dbe9ef90b8,-0x10802f218c9f4fefd16d128,0x8a2d2d5658044df68778ec,-0x3dc4d92d7731ae9ca337b4,0x176eabce4aeb1e697e6ca8,-0x77a6a8a3791c56fd666b8,0x1fc2502fd3740d4f08092,-0x6e81b3c96780b6b0d0ae,0x134d74f0e3511d366e98,-0x2a2fccde92aec96d008,0x457b79d0ff9b875660,-0x51c189cca6cc45c40,0x3f5434d1360e7188,-0x1c29bd1abd87d18,0x584f319d7fb33,-0x3e7d53f225d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 16 31 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 31 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 38 indices rho q0 m0 0 327572756102592000 21=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 38 indices rho q0 m0 0 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1b34ec49be3598ed000,-0x272ce483b31c14540c00,0x1b10629a0e8c8041bac00,-0xbf0de2aacf4e618e17800,0x3c74fd5d1b4393e0faf200,-0xe9b7ea783000c4cca7c340,0x2cd1fefb450ea81b89c6540,-0x7003b20e307ef1b152deb10,0xe830197b012adb0216d9c20,-0x19467e9d06a02b6c777f4144,0x2556da8ad7791c90a3b77bf8,-0x2f19d363d7c120018fbfc5b0,0x32f6c7f3eaf2e5eecf195f20,-0x2f6e90d668bd62274372763d,0x260425ab122e7587e77e2e06,-0x1a3b851e210bb06fc08e6038,0xf8eb374764e4151e4d27d80,-0x7e781aab6ed7757d52301a4,0x36c7dd126825c1f0d4f4b48,-0x1417ea81864355789cad0c8,0x62f6188d844ca3ce075c60,-0x1943258543e27fb6d9915e,0x543f92abc72a71a701694,-0xe0bd12da4750728f5af8,0x1d26fd77fbef5cdd0420,-0x2d4d99024820200e290,0x31e00db1ca86c6c290,-0x23bd229fbf6a772c8,0xe776b5d42245dc0,-0x284bce52755c2d,0x18677a5fa756]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 16 32 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 32 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 38 indices rho q1 m1 1 327572756102592000 21=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 38 indices rho q1 m1 1 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x23b57620c9a658b71000,0x32a49f2e2956e591a3c00,-0x227188c10134bbf00c3400,0xef423464b559c2e9a2d600,-0x4a75e57a596506340033800,0x11af142b3d521247a04795c0,-0x354d559c84dee4cc4f1d2440,0x82c68c492b710254a64d09f0,-0x109eec39629b029801b5e8980,0x1c60bd7015515241a36fe3bbc,-0x290fe60cb35323d47050f0e10,0x32b02d08eb42f5824e11ae150,-0x359e5e59c9f4db06c1ab68940,0x30bbbd8f51e786eb5fd3ef6d3,-0x26193284598550ce6cb6f7564,0x199bb9555dbed4f05718fdc68,-0xec59219eb361b0ad1c1ef5b0,0x7499c0757d56d1d6dbdcaf7c,-0x30f2a7220edc4e86c27f6b00,0x115ca27a9c0ceae4b35cecd8,-0x527a6803cb230041426ebf0,0x143f7c7bfc275e480b13062,-0x40b58e412ff728feb76088,0xa4b55cb14f64c2646dce8,-0x14477358877cd8973a690,0x1db67025387d2252b550,-0x1e931d581b661995990,0x143d2908cb451fe918,-0x7719c2d0eadd7b10,0x1262ac2f3d39603,-0x985dfbd32134]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 16 33 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 33 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 38 indices rho q2 m2 2 327572756102592000 21=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 38 indices rho q2 m2 2 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x2ede2b0b08aa547045000,-0x418030fe38149aeb4fec00,0x2be118fbaae76a1d28dbc00,-0x12c137b5e5fed508c9625000,0x5be40a050ac3216d5eae1400,-0x157623ec511914cddccdbfd40,0x3f939c5da626dd9409c59e2c0,-0x9933dc5b238efaac325a3ea90,0x131c41a0475109553133cb0f40,-0x1fffd69dc4ed066a200ad68cc4,0x2d5f1562dc9487efce2dc55be0,-0x36d4ddc5a7cd78f729ccfd03b0,0x38b9f47eec019ef59a2d50b400,-0x325e644a93d7509ddc126edd1d,0x266be4eee7f932f3097c2946e8,-0x192a14d89d59135566c921fad8,0xe1f5af0c1db545f44d7ee85f0,-0x6c44af551719f3fe8d1cb7d04,0x2c0e3b1040c92723925cdc0f0,-0xf1ce7e8085a564f81c2af068,0x4540b05aba2bcb930c210b70,-0x105950114781cced1e20a97e,0x320f47aef70c0539588cb00,-0x798ad7ffa3efd9e6f19458,0xe323d4d3b761d96d6fa10,-0x1398b215298a625ae5930,0x12d40a53478c664612b0,-0xb7f649d63b71b4f9a8,0x3d5fc11ed171a3150,-0x86306c8f001f5ad,0x3b69001c2bbd8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 16 34 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 34 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 38 indices rho q3 m3 3 327572756102592000 21=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 38 indices rho q3 m3 3 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x5e8988296df8000,-0x80c319b7278e800,-0x5150de2bbf15700,-0x1f9d36eda478380,-0x878a2063394f90,-0x1a8c9010d0ba00,-0x3eeedad83b4a8,-0x731fd3168d08,-0xa449a798dad,-0xb78aafb51c,-0xa00827747,-0x6bc6264a,-0x36f581b,-0x147cd8,-0x5339,-0xba]
def m4 : List ℤ := raw_ints% [0x0,-0x3d83987e7b5f8ed35a9000,0x54c26863b3e23c580c25c00,-0x37f48a4970160c941ea61400,0x178e876e949574c2e6dedc600,-0x719f8764d157d07041a63d400,0x1a1c00dd49f7c796aee8001bc0,-0x4c0d35c5ac773a96f8bf5a9f40,0xb41421f5777f1d7dc5503ab6f0,-0x160e7a4441c4f2468cb5066c740,0x243c765834456bea5d526dfa8bc,-0x325df1e5e578d0534b1b3a00240,0x3b9d49be5a2cbf04af53afbf350,-0x3c5785e866d2f4439d5dc75e980,0x345cadf6bcdc01c835de6791cf3,-0x26fc5ebf7e90194a4037527d140,0x18e34f2454917e559905a6df228,-0xd97b1ac9de6b8f35d24d4671d0,0x653accd666e576ff7b35a8733c,-0x27ef29dc88fbbf7cccf0022330,0xd4007f66decab804ef0e5b298,-0x3a91751d5258098ad47dc58d0,0xd4b821513bf28da0f07fdf62,-0x26fee4418cbfefeac4ddc570,0x5a47d0c93028ff6f1be2328,-0x9ff889bbf617da866c89b0,0xcfe2b6c5132f16257fa90,-0xba4d26a3dbea1ae1f4d0,0x68cee5015e6feff0858,-0x1faa8a6589bcde4ef0,0x3d320769b916b4e3,-0x1725c9235463d0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 16 36 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 36 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 38 indices rho q4 m4 4 327572756102592000 21=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 38 indices rho q4 m4 4 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0xba,0x1]
def r5 : List ℤ := raw_ints% [0x44afecee19e630000,0x5d2f3726e94f91000,0x3a93fe5211ae04e00,0x16a6e90a7dc043400,0x608088193d5c4b20,0x12c2968bd46dd470,0x2c10c2001096690,0x4fb631b19965e8,0x702b86aa8b872,0x7b162ac7dfb3,0x68cd5390d9c,0x444df9ec39,0x213491532,0xb7be085,0x291990,0x49b7]
def m5 : List ℤ := raw_ints% [0x0,0x50bcb82601ed6b7566dd000,-0x6dbbdb1e68f1ec7790018c00,0x476c73beb3fa5252cc57e1c00,-0x1da18aec9e49dad8abc4dce000,0x8cc3c226a32df44414fa6e0c00,-0x1fd6eeba1d9616ca001804e1f40,0x5b3ba0cde6afcba652a77cd80c0,-0xd45db473f54dda5a1f49e93b090,0x198d476f2e3110db7e3993915fc0,-0x29345a31d908ec9d2aeaba4de0c4,0x382b0117b3c43b520dac9c4b2980,-0x4122e10a12ba7c1c73faf5f0bdb0,0x4087d3057e1014f33af2b6ef8380,-0x36be7b2d645ef3db8ed7cdd900fd,0x27cbe6b98d186c030e856e8179f0,-0x18c512172d0c0779953919f2fc58,0xd2b1a4f853d7b6f6f107f0d7bb0,-0x5f4a184eb39e279b72028372304,0x2472f0637f7ea54cb3ceda36190,-0xbb2c591c2ca7cedb787df78fe8,0x31e11c4965a1a09ceef1b29bb0,-0xae2e0b2914864bf3639d9183e,0x1e949346b888e3633238255b0,-0x437bd98a7d7bd873bc0bbad8,0x7150a40ca8260d7090ca9d0,-0x8a851477e058de883cd230,0x73aa91edb3919862a6f30,-0x3bdde4185d307e4eb228,0x105aef5daddd70acf90,-0x1be5d850e551e9e0d,0x9032b037ebc960]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 16 38 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 38 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 38 indices rho q5 m5 5 327572756102592000 21=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 38 indices rho q5 m5 5 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x49b7,-0xba,0x1]
def r6 : List ℤ := raw_ints% [-0x1b38cc2425f95448000,-0x24cefddfae1b032d800,-0x170d00f223d965b2100,-0x8dfda0db5b52be3280,-0x259cd868ca69a3bbf0,-0x7448f07ae4ce2aae0,-0x10f2efbd5d36ead68,-0x1e6552d19c443248,-0x2a530e5f5e076ef,-0x2dd7087538f19e,-0x26635d7e14be1,-0x187beae17fa4,-0xb8f713a2c1,-0x3d65599be,-0xcec9b97,-0x1518d8]
def m6 : List ℤ := raw_ints% [0x0,-0x69f7b1b1e2879d0a17021000,0x8e226e3a59ccc2f1ed1607c00,-0x5b4129c97e29c9c91217d73400,0x2553071bed4d2f6bf64c01ea600,-0xaeb789c8207ba18eb3d80972400,0x26eaff91ecb61772516f811341c0,-0x6dbfc9c843159182ec276f10c340,0xfb3fcf7babb342f003fbf9508ef0,-0x1db58c39ccd9bd794ded13995b640,0x2f0b6db879e3c1289f1c4a047c0bc,-0x3eeacd47541009a9cedee602d9700,0x4783e69ad7898e8837bd43e808d50,-0x455ed661bbeae6f4951470c744a80,0x398d930189fd44e164370265c8913,-0x28dce771d000154bfa4bf7f355bb0,0x18cddda16825c031b686a4726d428,-0xcd6d14e298804f9bd017a7b9e450,0x5a4a2f862b23e464ba3011be87bc,-0x217dfae9a2c94240ece4982585f0,0xa660b894cd423795c024b7ac298,-0x2ac4b20891c7a3d2fa0f5bf5e50,0x8f939b5b9fb989c3af2846ef22,-0x1822c5bec48c6d8030aacc5910,0x32bfd9bcdb1b88e4f6bb33528,-0x50b5169a2111e5812b887430,0x5cbbaec047c6faa884e8110,-0x4812dd65d9276b71dc8bd0,0x22468c2c7349049a1a258,-0x8745635a2239388b470,0xcb6895b61bd3d5003,-0x381a90a83488b40]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 16 40 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 40 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 38 indices rho q6 m6 6 327572756102592000 21=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 38 indices rho q6 m6 6 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x1518d8,0x49b7,-0xba,0x1]
def r7 : List ℤ := raw_ints% [0x7ca74d434ca9c0940000,0xa81473ee8f6f5e7f4000,0x68eb76cc68d7a6969000,0x283e9ea58f9f13cfd300,0xa9d7e56dcf94be26f00,0x20a7e8d137699e93410,0x4bb6a814f2e7aaf8e0,0x86d9973bd21c6ce58,0xba3a71ae4bf6db90,0xc7aff8fa5047791,0xa52c48703d1082,0x67b8fd85af61f,0x30005262c4ec,0xf83add16bf,0x325f84ba2,0x4e05aa9]
def m7 : List ℤ := raw_ints% [0x0,0x8b1519397951fe1d3e32b5000,-0xb83006f7a1efcb97c745ea2c00,0x74b31703ff4a4221cb7fdc27c00,-0x2f1485e850c2f6065eebdfc35000,0xd941bad8b6971b7c473a9158cc00,-0x2fadb7478796b3cc093f31c757140,0x8462010648a5bf18df8bf79cb80c0,-0x12a306744a5dcaece071239c316090,0x22aa92d25e35399f4b346822b469c0,-0x35ed293ccf566b84aec2b6e93feac4,0x46c929438e7ed14599c7afd2be9800,-0x4ee462231912d18400338dc11a87b0,0x4af453c30d8eff57bb93568e790180,-0x3cd5dfda44c9e4e961b4e4221708dd,0x2a32f70ed4fd09dfac621015e36e10,-0x18fcf3b18acae2040a0d2532bcc158,0xc98acbd187da2a5c13dae2a8910b0,-0x561a642f95ba013baad281cf91384,0x1efa22bfca3e3feab1523e3355610,-0x94df3d6421346773224bb20746e8,0x24e9b890a505ac742d1704fb2ab0,-0x771da027bb49ed6fe7a4130b97e,0x132af60d8f33210252e45220a70,-0x2662f58059690cbabb2d3e1dd8,0x39c87ee6ad445f74eb4614ad0,-0x3e5ae2fd27badf6a1efe80b0,0x2d0fb840ba6633f1fea0f30,-0x13aa1f7ec7f15214977928,0x45f8fae50a40ebeaf290,-0x5ca7098e88c240c9ed,0x15d0621b72d50d80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 16 42 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 42 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 38 indices rho q7 m7 7 327572756102592000 21=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 38 indices rho q7 m7 7 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r8 : List ℤ := raw_ints% [-0x1ccfff28ca18d02c8b8000,-0x26c1a42208269e52cd2800,-0x18205bff2d89d9ac692f00,-0x939ae67dd40b4a6da3f80,-0x26cb2bf47ba0870fe5310,-0x76d926ec8d95ef4c5b00,-0x1123acb919943e77c118,-0x1e5ad422e1985c54548,-0x29a47a8c08efb5ad31,-0x2c4cab182307da460,-0x244b0ebe34fe715b,-0x1686356c7a62a3e,-0xa4589b876e327,-0x3420b12e0224,-0xa51ea7c6a5,-0xf75432f6]
def m8 : List ℤ := raw_ints% [0x0,-0xb68bb11b6f3b9d8661a28d9000,0xeeca9502d3a289e005ab0359c00,-0x955fee181094afcccefe07b95400,0x3b7762a4e41ca36ce99fe895cc600,-0x10ea3a7bee774989100e8382ba0400,0x3a8aabcead3693eeba3584823297c0,-0xa01c08a0e0e106da01a22347becb40,0x162fd7e10445112b16c14048cdf02f0,-0x28978d40df2857643267aed35610a40,0x3e0e42df595774be73668320992e0bc,-0x4ffabce5d2f88c4994f25efda037a00,0x576f4679028d16275405b63f95e8750,-0x516486548d6e0c73b0ad1c0271c2e80,0x40a5bc38a072fa8f834d763b25ead33,-0x2bd2e7c3699f257f09e04bc5480c770,0x19524b0dc3075ffeee3ff7c80298728,-0xc6f048efa51cf6cc8b77f3cd66f050,0x52a03f713d8035538750131762cf3c,-0x1cd586e0560a244a3f77f577186ef0,0x8610d1080c31ce9772ae21287ab98,-0x201025b0b2245a507ba0997b42650,0x6370b49a1227cc98a21fb6bfb9e2,-0xf5041f72a57e95573581a4ee190,0x1d3269331c86b8fd50321180628,-0x29935ab45454cd86be94fb9c30,0x2a1a224747488a5134fa66090,-0x1c429a01512b5e08e1d171d0,0xb4d7cea9c299e9e4ee9758,-0x2436d9bdc383d7b1cc070,0x2a2eea16270130ab423,-0x879e5a2ddf521d00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 16 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 38 indices rho q8 m8 8 327572756102592000 21=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 38 indices rho q8 m8 8 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r9 : List ℤ := raw_ints% [0x5b55ca525b734caa1c50000,0x7a999783712266f90f37000,0x4c23aad2ea50018f61a7200,0x1d091020729e8a5b1fe2e00,0x79b92b25b8a85def0254e0,0x1739a7a92e63a383e868f0,0x355f959ecaf9025de9bf0,0x5e15e54ebbe09c01ebd8,0x805e458f4b311e752ee,0x87aeb52522c2ffa26f,0x6e4fed487027fb528,0x43d542f3e2372f25,0x1e962b25010cf66,0x990fa1d307739,0x1dc44c01ba34,0x2b906338eb]
def m9 : List ℤ := raw_ints% [0x0,0xef97587401fe3ec0602559cd000,-0x135b85268f8a317490b978465cc00,0xbf5e2837d40cb1643c1cb75d5dc00,-0x4b35e0661291826078a387ae1f4000,0x151baee08eb097e5b53345ce682ac00,-0x480968653dfd208442a9364f0979340,0xc225ca026faa8c3a29230f1718088c0,-0x1a7e2e61d1cde49f8cb21a6f29c4a890,0x2fb174d469b6144022a3bf5763ae39c0,-0x47aec60d67acedd73ebbfb53c4bd20c4,0x5abeeb9f279bed129e1696603e1ff200,-0x6157d83ad3eb6bbe3b8867fe90b0f1b0,0x58d0f43ad2c0ebc4f2d31915a5279980,-0x450e51e142c8f8a84f47a263cc2670bd,0x2dc2e13d45dfeb3790841fd917252890,-0x19ce882d29cf44a38b6b68eeb3e7e458,0xc58a06a5cb94ba131ccb2b4faf022b0,-0x4fc659ab08d991fe1537cb83f969604,0x1b01a8c4b933268e5cdd0c0af907a10,-0x797cd9cc2169b5daeaa6d86352dbe8,0x1c05f1e0e9c98e05858ec05e6374b0,-0x538448f46149df8f1785be75c44be,0xc4e01b0ddd1172594fef313e2b70,-0x165351a21759140a092cfeb812d8,0x1e0e07df50e0adcfa4c325790d0,-0x1c899fb6c1fd643a51c1d40930,0x11c60b916c82742480984c530,-0x681cddfa7d1b1035852ba28,0x12c00146b114e0444f4890,-0x133223efa7d97d7643cd,0x34a9f94840719d600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 16 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 38 indices rho q9 m9 9 327572756102592000 21=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 38 indices rho q9 m9 9 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r10 : List ℤ := raw_ints% [-0x10166bdfc14c9214fe32a8000,-0x158e0f2dfc22495339df7f800,-0xd5bd8bb2883b3e14659f6d00,-0x515193ed109a1088e8cf4480,-0x154014a9686ff1e4b1b55b30,-0x40adc62f9a10ae717486920,-0x942030735f08bebdbcd008,-0x10414da0acacba28836808,-0x1613a9f2668c28eae31b3,-0x1735ecb0435b471fb5e2,-0x12c0ba1b4cfbe0bf395,-0xb7231e1c2cb96ef18,-0x51d8275f0fa3954d,-0x195224410580cca,-0x4dbc0fd7438b3,-0x6fd87b64c14]
def m10 : List ℤ := raw_ints% [0x0,-0x13a76a418429db25c7e3105dd1000,0x191e3f6b459eb4177a467b1c59bc00,-0xf560b3c5af25222efb2b439b907400,0x5f3ee35da2071b716a461d667fd6600,-0x1a62cd881105de0368aac3781a742400,0x58d4edf39b83c51327a4527dde07ddc0,-0xec056be2fb6a91a0b151a891c5da6340,0x1fba59aeec2be3603e1eeee54cf3d16f0,-0x3839606d936b1071ab2abf6e10255b240,0x531caabc298fdb7f3f60e3749751a1cbc,-0x67622a6badc7e5634992658cb78444600,0x6cdb6346a281320d11fe458997667c150,-0x61616f7135e669b87bd3bd07f0050de80,0x4a240e93ce8d6517834bd04f15185b153,-0x300a839d5c85b606707ef35f9048fd470,0x1a72fb73ea2367f7bd29fc536f4cb8e28,-0xc54a9fc49ccb3ce5fc23f41839c96250,0x4d7b732aad05d501a0b1bda07b3e52bc,-0x1972bcb6c5a87914929f8a8b723920f0,0x6ec28b38f7409972bd3785a90305898,-0x18a3ca6b600fb89192958a6e99fb850,0x468d961b396f5b21bba004c5ba68a2,-0x9f11fd056dcc8363d53f28198a590,0x11287713410f9d2e0a5a34269f328,-0x15d2c3885db0c918993086e37a30,0x1369d7911c4f1e4f79b9415d810,-0xb35144c14c637ddbf15e6d3d0,0x3c0615779feb5c2879b0f858,-0x9b5e4ee63b72d180636670,0x8bb128519b21ddc67443,-0x14703d2d172cf03400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 16 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 38 indices rho q10 m10 10 327572756102592000 21=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 38 indices rho q10 m10 10 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r11 : List ℤ := raw_ints% [0x294d93a62325bb4e6323760000,0x374014168b5fb3511de327a000,0x222df2cf68b97aadc390b6d400,0xcfa2928aaf5bb0a11e000d900,0x362268ac3e5d91c775ba9b2c0,0xa4564923e54ba6d4d1d12cd0,0x1773ec5ef804ae2e664af900,0x290a23d7b639544f92b2618,0x37858f6dd40b4669d7d98c,0x3a1caeae7ea6ffb410f0d,0x2eb4fb3000d60607ef0e,0x1c55a3592c1e7864b6b,0xc92478d726a43e9a0,0x3db1119410e1d5f3,0xbb685fa830c286,0x10a29845bf82d]
def m11 : List ℤ := raw_ints% [0x0,0x19cbbb75fd76efa1965a057b225000,-0x209b5c0f9ee7f458ebe4522535c6c00,0x13ae548e538f17adbfc9d28456403c00,-0x78c513ae70aba7b1fb24f1febd8b3000,0x2109e0c7f4c061a05a0a86b966b5c0c00,-0x6dc5446a5db072e33eb80816edf098540,0x11fa3b4c7201dac2a4ac52ae2512bab0c0,-0x261b62dd679b4ec91b6fd0184c15bd4090,0x427f703dc8694aefd2e9c9a7fd771ea1c0,-0x60b70c2c0d44b3de5777b48e5306757ac4,0x7640dfe05ecea132e0b4d27da6b7501a00,-0x7a43511792a32370a2ac62df66e6453bb0,0x6b454daaa0c976aea6ed874496a98d1980,-0x4fff324b05584e4e98211e36433bf3489d,0x32b314ec0f2065e996e66517fcdb114490,-0x1b41a477749a4ef45e53b2b39937e22f58,0xc62a2f4b5ae1103aa21f5a41081e0e8b0,-0x4bb1bf4c3b53204a40c1631b45894f884,0x181f213a1c45c31cc0691f61590999c10,-0x6593c9f6678b469e2f5ea492518b08e8,0x15ca980f625d16ff061c611449efeab0,-0x3bf0374e21a3a41301d9d65f74a07fe,0x8135b60036c16b7efdba9c1abf4d70,-0xd4034188ccf82e5c467cc33330fd8,0xfe9bde8661f18b54ed64defd2ad0,-0xd404b1a9c2f963ec6d040ededb0,0x715680ca6c70c0b528d503b330,-0x22a5e6d74733c85df0ef90328,0x507a5f301a877daf4f1aa90,-0x3f807c9ebe2c42f25e5ad,0x7ed6969aa29745d800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 16 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 38 indices rho q11 m11 11 327572756102592000 21=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 38 indices rho q11 m11 11 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r12 : List ℤ := raw_ints% [-0x624a3c62bba4ea3b08f89498000,-0x834ac14fe6ad42d316f948ac800,-0x5117359689fa101f474df8cab00,-0x1ebb9c6c2e4394e66e7d3bf4980,-0x7ff157b188ad6dce349e55a350,-0x18383563cba9908d3feb36ff40,-0x3728ff9d4451a4e3f525837f8,-0x603dd09614f75b9b97c9b8c8,-0x81c5092ab7f846b73385a75,-0x874e51878e3357f87a2824,-0x6c45d7f2eaa348c3ac00f,-0x415920c21be90a06deb2,-0x1cd20edbe2f9b777a33,-0x8c6f28f6848d397b0,-0x1a7055a372f6f081,-0x252aa80568a372]
def m12 : List ℤ := raw_ints% [0x0,-0x21db660adcac1a84155627319d09000,0x2a587bdc08fa02ad57dd7084d694dc00,-0x19470983b7a9a5c38f10aa79bc3e49400,0x99526b2bf042d5fb83bfd66e5d59d8600,-0x296fa0dcf4dd4e553048868d646e9c4400,0x87ebb20ba4629ab34ffa696c2f57a593c0,-0x15f65e807d7fa41938d3ed886cf86e13b40,0x2de5c2947042ae785516504eead16ee5af0,-0x4ee675b3c10c14b1b1cd4f0791e5d5faa40,0x70f2273226fef1c64ad8f84fc98129fa4bc,-0x87caefb284261b49b77ae7492513ccff600,0x89e7b6781d5918023486a84fc47a5dabb50,-0x76b4e33ac2c2af117b90db2d2d62203be80,0x56bc7bfadb7e4c508cb05f06a49750b9573,-0x35c7ba5ebcdce58f01b017143ea0b331670,0x1c3d3a28d6c9772a0e481cf624e2c517528,-0xc825e10e1bb10a83ee4452aa2017202c50,0x4a5e5714fb7d38f304f9ee068b52a1a63c,-0x16fef453d1d03a274d741cf720f53c76f0,0x5db13e1f55021d4d6b4962f057c78b598,-0x1361a1c2280b64e119c73a1cf98b3b250,0x3332d2eb293e2fd4f0fc154618b74f62,-0x697e135b3a7f2d11638fc266d04b790,0xa47dfd51f24219dd325805c7db7028,-0xba64ebfa868737d874a3ddae37030,0x912c761366891a298b6adbacd390,-0x47ca0800b5feb50036ef8d2e5d0,0x1405815f97fca2ca581592c958,-0x29b07e8cdcdfd62cd35b3470,0x1cda00a7f6dc32e9950c63,-0x312b36d290dab5fd000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 16 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 38 indices rho q12 m12 12 327572756102592000 21=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 38 indices rho q12 m12 12 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r13 : List ℤ := raw_ints% [0xdb9a14a945ff6a5ab8837e070000,0x124f5d000f599b82b7e32ac45d000,0xb4af1fe3f8296a7983f11f52f600,0x445e6459c4275d2b2682c9066400,0x11c1d28667061391ff07fbeed4a0,0x35acbf72d885a3d7d15550b30b0,0x79f7ec8ffd4f3cc78b1fa03810,0xd443850864fb8a0ebdbbfb158,0x11d6281d97305d6c1a1de286a,0x1289505bb7f915e56339936b,0xec6f68d413a0f5f7d8f334,0x8e155c590a3b47ee1cd71,0x3e595d38a1df8bcfe29a,0x12e07c3ef5fcb2105ed,0x387813b0230eaf398,0x4eba8211d52f7af]
def m13 : List ℤ := raw_ints% [0x0,0x2c6ff5ee41a1e2cd5c0113711e1bd000,-0x3703da5a364c19fa4e24d98f59a360c00,0x207dc80b2d90973c23b9a6ee272d999c00,-0xc2e17c2a3481a05f7ab9ed4ed7494d2000,0x340cf2dddc3cb15e870d8840b7045266c00,-0xa8a2584138fc506261ed98adc7e00b9c740,0x1ae4ea027ac74a64ab777ad6fa536d7058c0,-0x376ecd3035fa86a6a4b6a049edb65d9e8890,0x5de888a491d6e6726fb2628f9796b98669c0,-0x845c5266ec71cb16d97cc1dfd72beba178c4,0x9c881b7d7d2ac07f5238f1338421f57f7a00,-0x9c32746d64eef1a99561906e5f821cb065b0,0x83f34fe1f975fa13ee7f4149ad1f04ec3980,-0x5e7dfaf053da8967424cfae08819bc96f07d,0x3955bf3271cf194839f15fd8f263ee28c690,-0x1d6937f6b5a04abbed8d5f6e3cc06a720a58,0xcb3fac2bde7d1caadb3a0ce5f9c11a7beb0,-0x4978caff501deb59ddb3d573291c83ac304,0x160bbfc71cb48c02546b0bd9f6f1df47610,-0x56e749af140d39f71bfa398d434596b5e8,0x115522df0f886d12bd0ed4f1ff7a0050b0,-0x2bf6b2aa5c7ac3b1d6896a3899b214b3e,0x568d7571d9c1d48b726944201ba6f370,-0x802feb74c67f0fc80f543028d312cd8,0x88f7d10b283be967b261b08b0ad4d0,-0x63b19dd47c27a3243615877e10630,0x2d8f656124fcc7976f953a34c130,-0xb947beb52918fbaf9b3eb48c28,0x159897557d171304d13fcfc90,-0xd19f60cc27466306e8a78d,0x130cc9c1b1ec25f16000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 16 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 38 indices rho q13 m13 13 327572756102592000 21=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 38 indices rho q13 m13 13 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r14 : List ℤ := raw_ints% [-0x1d12c771fa9c81b8e165edc7488000,-0x26bda6eddf18166b707134ba779800,-0x17dcebf379f419abbd844a86a5a900,-0x9043fe67676f60a8df1beb6706e80,-0x2568eed1bcc905f288d4c230aef70,-0x70e0e5a9ff9ed738199a7a365160,-0xfffd43b641ef33579cebc0799e8,-0x1bc81325bab2a627368a3b4a188,-0x2541e9c65b2d02f8c34beeea77,-0x269bd21d17c24860e52f46e26,-0x1eadca77450bb86305ddb7c9,-0x125e25f420548c50995340c,-0x806992fb4385921acaed9,-0x26afbb3dd2d0601c67d6,-0x730fd3a799e1aa080f,-0x9f54a0ee8d160810]
def m14 : List ℤ := raw_ints% [0x0,-0x3a52f2c8b62479ad88c16984778481000,0x4780b4522c68d62d041720e565a66efc00,-0x29cbdbd64af5af245c4f96703d4cebdb400,0xf7fe233ff3290d3f32187efba1776c92600,-0x417c4d2c39946c452974614b51ee81a56400,0xd1a02cc171be527db5b14eeb758c4bdd39c0,-0x2102796319670717e76a8afd6921129061340,0x432105edf08bbac2b3176d48601c84bed8ef0,-0x701cc7edac3f06c7479eb6cbe57af238be240,0x9ba42fc193df3109e141e5f0b7451995a18bc,-0xb51d6d1f03868869a824b9a979d792c48b600,0xb1a30f13326405a2cdbc79f9b4897d93a7550,-0x9350afda2d2a7bac8dcb5ddd71715d71b5e80,0x676c0c67cdbb5e5b186a871bae328fb96b993,-0x3d6ceb5dde18f0084f2c8e5b95fcda1702c70,0x1ec9f02948e39473e700a51c82d05e86c2c28,-0xcf7e3266c63471b8962cef054452d2e41650,0x48facdae7a6a6759fcdabfea3f3e4c8449bc,-0x1540371280ec66bab57089ca05be74401cf0,0x510babfa47323b2afdd98c80d1c98a6f298,-0xf95373ad4dc9ae54829d32a758ec438c50,0x25f17ede517157e905b97caa8d16cb2e22,-0x4759434624a0ca17d92ca156071de4190,0x6450d77af4dcb2fdc41b06379d590d28,-0x65010d9097b66dc70c17d0d78530630,0x44a59a92ba8063f0c4f70236d83310,-0x1cf6f941700f882e8e480dd8d77d0,0x6b3e8dc59aae099706f697a9a58,-0xb2fbcd831416242526ffc6270,0x5f2336a9fadf85de172dc83,-0x76078ca3aa06017b4000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 16 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 38 indices rho q14 m14 14 327572756102592000 21=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 38 indices rho q14 m14 14 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r15 : List ℤ := raw_ints% [0x3ad6ac2075f57b69f68ad9569f80000,0x4e529177fe6b9f2283ead8917860000,0x3030413584f1f02be0e787f0955d800,0x122f49d41f6b481c2e7900826ee8f00,0x4b5758be6c0b208becc3006e010a80,0xe2f855d32b59902d6109d6bd0b090,0x201d19816b8285254152ea15fbd20,0x37a6feb0abb61d21c1a62bd08498,0x4a77fb77f010042bc3d4e88c488,0x4cf9e79bdb4856f2606c02fc89,0x3cfe34fc9ce5103a9885c029a,0x246659a52233502ea5f61437,0xfd8b5a1c55dca6fa4e8954,0x4c101f8080e8290405a27,0xe12065baa1edf67046a,0x135f9421ad28ecc571]
def m15 : List ℤ := raw_ints% [0x0,0x4c8cdea76f0fdfb3c37dda7ddcdde95000,-0x5cf77bd690b7ca34b246cf5ca56a71aac00,0x35ce82409cc2e0286dd1a77027e03b39fc00,-0x13befd79de89fcaecb75e25a82fd66ab91000,0x52833c0ac5a6317161f78aac2e87b5e7fcc00,-0x105128cfd51d23297902ebdcb446dc03a0d940,0x289b6d21700358ce1150f7ec5700c6a1d300c0,-0x518197d2742ea90f3d57716fcb376011e48090,0x863e94999bd43d69da08c60fa96626ab8eb1c0,-0xb7a067d88b83231b36bb6b0b9ee8784262bac4,0xd253ec59b937e2ff5a867db765ab322dcb3a00,-0xcad365ae5a8396356ab5fc3875031484866fb0,0xa52cc7e1768a8a37803d910795a08e0001d980,-0x71b68eb25ba51893f96a83daa233074473085d,0x421fecf0c6ed8cb399d4a2d937de19faba2090,-0x2064a3eba76b399caf83d4887350dd1ecfd558,0xd4ecc12db977b7c0f14b81518911ab6de14b0,-0x48dff2c55b152588bd7c226d8c448d26ce584,0x1498033c814f7d67b6586e8a23bbfab70f010,-0x4bfba92f595f960a2fe517600b763ccf02e8,0xe150780388708a453bd02a11f3270d4b6b0,-0x20e88a6b063883025b01fb6d4e5ff9bbe7e,0x3b150ab861c81e611076c8eb57f047e970,-0x4ed1a75d5424e4f94b3146857b7fb89d8,0x4abb1e2a1627b4d4b9638f5bd0e37ed0,-0x2f62fed657fe4e2764ed99643e702b0,0x127170a73de8d83eb21a3ad7cc0f30,-0x3e1d71f162db416e31376aa2b528,0x5cb30a5993c604df3e7973ce90,-0x2b27b36b745e07e9bde6796d,0x2daea29e58854b1ad8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 16 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 38 indices rho q15 m15 15 327572756102592000 21=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 38 indices rho q15 m15 15 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r16 : List ℤ := raw_ints% [-0x72780d88cedc5e385d8751c896278000,-0x983b724bd8ded54866f30ad507ee6800,-0x5d909fbac4aa8bcfee6db140c9f46700,-0x2344874dc47c678cdd7fed61926cb380,-0x91ee679cf5204750bd0163298575f90,-0x1b700deb8acbe9bd26df50315430f80,-0x3e040f5cd9dfc2bdcce03d569969d8,-0x6b4867f899075f31e4ef9be196e48,-0x8f45ded133ff50fac25aa627b8b9,-0x93c5228f3b2c8d7a433bf9222e8,-0x74cbdf1191bd451f663a1fb5c3,-0x4581c3b8699c1ab07934b2e26,-0x1e29c9efb821c290ae05883f,-0x9041e4fa6844fd40988e3c,-0x1a92fd06e8b7e75cfe45d,-0x2469ea0bffba85f92ee]
def m16 : List ℤ := raw_ints% [0x0,-0x6478e43bc1c4d59bf0952ec531e34239000,0x78eb057f01faf6c52e1f81650d1bb5301c00,-0x4551ab4d69cb8bf0ba1364456141b0763d400,0x192f0768045eb983945c74995fe64e66684600,-0x681ea5289b0dd7679d5fa0d483ddc3b0c38400,0x145be05e41930e16d7a51aee418b0ee30484fc0,-0x321027496c962e23f4f6f036316aae1caa3eb40,0x63374469367c369f2c05d9d73f8d08fe17232f0,-0xa136ac047a4861897ab22860a9fb7d2ad321a40,0xd959543307700af4c4d8f26fdb1c847fe38d8bc,-0xf520f247bc015f047dfcbcab7662cd154a03600,0xe87d81f7cac2a0cc4d46b2fca10f4450fe3ef50,-0xb9fa4870434a6047193e1b94663b55c1d11fe80,0x7d96556eab7643d5f6c15207bc584e7514ffdb3,-0x4784d7a74f1561827db0a1ada6ee70c58c8d270,0x223fa1a91e01a2c4960b42529a215d4573f3328,-0xdb9b729d7ef4ae3bcf534fb178a5cd89d24050,0x49257e4462992d4958f6befbe5a1a673256d3c,-0x140f9970139adfafafe412ff03c53c9b7cc2f0,0x479a972322a85b5b1208d0a898754a5c34f98,-0xcca25f35b41b7ffe3042055fd5b123702650,0x1cad4613d091b4f5d25de24de1dcb9db74e2,-0x31232570202a6c7b312ed2ca52c72296b90,0x3e2a202da3070378ff900c79fe675aca28,-0x3776e6b4ca412e88bf9fb0e5ee5f85c30,0x20c93e94064cd35d472300d21827a690,-0xbc28e22e83cf581af779d1c97ec9d0,0x23fec8c71b0038497bca98e7c2b58,-0x3000a158972b9a5bd5cc066d070,0x1390a2da1d7578889767dd4a3,-0x11ac11d885faabe1dd0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 16 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 38 indices rho q16 m16 16 327572756102592000 21=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 38 indices rho q16 m16 16 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r17 : List ℤ := raw_ints% [0xd7273fcd143930c151e536c643ac90000,0x11de3d4e236413dc0cef8bbf22e2903000,0xaf8c84eb5bfd9dd9efc8e99cc9f0e7a00,0x4219f7c675fe9ab2f270675a0ba06da00,0x111337aafc69599c815f8d5fc62ab6460,0x334d1c791898f0bf5cf456d919c98c70,0x73c9f68ba04e541e2aa0fcea2978030,0xc7fda0793520658b9553124152d3d8,0x10a9cd7f34de2b123be335a9965ae6,0x112712c7acef243ea4c6fc4386367,0xd870c8ab8f2d8efe5d44733ae40,0x807d03344a0c4b4e5f4de704bd,0x379a80eaf9db380366e7184ce,0x1091669de7f113e848638da1,0x30a83937a94aef04ca07fc,0x4266073370d79ad41473]
def m17 : List ℤ := raw_ints% [0x0,0x83deab8e6e52585cabc3cd62d17a46ead000,-0x9d5436e96fa5909ad1b48f5ef2345dcf24c00,0x595df8e16d10bbe17647d7250d60bcd8395c00,-0x20273421edd462a38d4cd7e7fc85bcd33db0000,0x839297dcdd72071d8da999de925dfca04d82c00,-0x1972861202ba32f3ba782ddc31294a61e8c33b40,0x3dda733ef935635bd4565487f784259800e8a8c0,-0x79132ed6b821adb38ee72c78fca9b773b1f1a890,0xc226a0e5d69b52a82b52a86c9069705b6343f9c0,-0x10215190cdfba2d6d578f4d471242e5a2a5a060c4,0x11eb08276050a5dfd9ef3b56263f3cdf7a315fa00,-0x10b82c220430c581580ef78ebe5a2431b6c9f59b0,0xd242cb11e89e0c67ca7d4b6f3b63030f085d7980,-0x8b4eed0809a00002a6cc2218f1b52c2c91f5303d,0x4db5bf0b712d82949c55c6ec92b314c5d7869a90,-0x24626a9d88d6f6299ecd3a64b313f1448469d058,0xe39f6e07e5ee600f0d1bd9010869ada93e3aab0,-0x49ca41b89f8593012507915310ee2f7c000f004,0x13a41a1df46f887312b39fec02893c8b7c1aa10,-0x43d0b84188e81cfe87e7412ca815558973efe8,0xbac0fdb16e909dc3e8ed2c3a44194efa25cb0,-0x191a8ec37657f87d7b0d5cd64f79390dab1be,0x29095be6f5894160795fc06d690c08e85f70,-0x3134da0598f112f2f54894f4cb9248566d8,0x29491331d9dd1c58ccf5f31977600ae8d0,-0x16bb6d438ed96a8abbe6154dcaa8ef330,0x782054bc5a78dcf90b83241c3e71d30,-0x14de21e0ce21d6df75e1c958177e28,0x18da04dbfcc8912aa21bb21d6090,-0x8dd891917a656abee7c1c2b4d,0x6d54d636ad916c2c560000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 16 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 38 indices rho q17 m17 17 327572756102592000 21=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 38 indices rho q17 m17 17 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x4266073370d79ad41473,-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r18 : List ℤ := raw_ints% [-0x1885228fb0a6cd5338aac029a893c668000,-0x208e76bcdf6c3522c904ba96111c3a73800,-0x13f95df47782ba6943fa592179871a5e500,-0x783952be27c61bf60d806342e0eb579880,-0x1f0601b618152ea3c5bcca95eed62f23b0,-0x5d19e6a3a618cb3c9990742c981a029a0,-0xd1dd7948e1fb76f6c6591415e71bffc8,-0x169f76ee74cf0975d5f4ccb21c335f08,-0x1e1c9d2dcf109eed61dc29c02f3e43b,-0x1ef11acac2387537ca2e15bf14e96a,-0x185ad5868d2cf8164771edd1904fd,-0xe6d2ca2d3b627166981fb607c00,-0x63a4e06aad5c7aeb25a1bfc365,-0x1d9bc0e8c94069be2ecb313e2,-0x56ae9dc7c780ff7d8b1d66b,-0x75ddcdbbdeafb9e27390c]
def m18 : List ℤ := raw_ints% [0x0,-0xad14412af0cc13f9a170fd91b2f07d1431000,0xccc637b1ced885b139b2ff198324bb1fe03c00,-0x734af84127e71657c800c91fc158361445ef400,0x29180eadf227038bf296f248f4adf53231b2e600,-0xa67eb4bcbf59c71bfcc34ea572de586325aea400,0x1fdcea3147e0c89b34e4bce9c9ffed605b78c55c0,-0x4c946d0c048c4c556281a0a4360dd712b1706c340,0x941c0673acd1f26d33ad3661d7c6c974b0552c6f0,-0xea7756346d407d2adcf10e603cc0f85d029715240,0x13366d13e53491d70c96694705a116512abde944bc,-0x150722c7b6499057837d5526672d9d9c9189513600,0x134f4b2065773eb6bec2f2f53f21873c57e23c2950,-0xeeabb5508d9d9fe74527f9ded1247b6cbeaec9e80,0x9b30befe9cd0b1d2e4e6a45787badb32f59a341d3,-0x54d170801dd838cada6ea57015adef2afda42f870,0x26d5e0b72d4e4fdd0cc676cafdf867b0ed24c4a28,-0xed1348bcc8cc1819d30711788d21236e016d2a50,0x4ace8539d6358224e3b9428ce468f36acd7800bc,-0x135336e0669e6f97035d09b79696884b078e28f0,0x408a5316cc343e90c3e85c1b16f3085f8524c98,-0xab3cad17aff6a53ff7bb0c21078dd8bdf80050,0x16129f2178b4444f4506e7bb3a84b9892453a2,-0x226870714e8b30e61e47bb831d3d1774cd590,0x27153b88dcfb76fe889b3a820fc82efe6728,-0x1ed0b16e6deb147145ba8ce1ccd2c9bf230,0xfcab15b845ce0aa9b82e7acce32641e10,-0x4cc6ad24e0985fc7806dbe5ed8f8dbd0,0xc1a051fffac992874d8529e653fc58,-0xcdce11ae0025a39165f8b37cfe70,0x403d822d91d49fe9810fa324c3,-0x2a4151bd959808dbf340000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 16 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 38 indices rho q18 m18 18 327572756102592000 21=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 38 indices rho q18 m18 18 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x75ddcdbbdeafb9e27390c,0x4266073370d79ad41473,-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r19 : List ℤ := raw_ints% [0x2b86c3eefdc21327f1549e01a6c355fa0000,0x39c0687fa743e0509a80f38bdcd864ec6000,0x236782476ad94255710bc91aa3de0907dc00,0xd4ea85bd82d3714613eaaa3d2c1be7bc500,0x36e3facc8019640c68a551f8bc17cff3240,0xa48de6ab78ab1614e31abdd528c3039450,0x17281260fb7867135b74d50ec547a69940,0x27e372e3697e801793d864c0c0aef4f18,0x35048a56245c466fc5b9a7f7e5ad0084,0x3664cc5cd87bcf7175a610354c1d905,0x2abd52384086822a4d98053c2acf26,0x19446ea71b5c76cb2b8af98a01403,0xae247a85f9e33cd967729b3f408,0x339e62e1217ed749789f8eb35b,0x96b446a5fa7bdca7080c894e,0xcc487cebc6345598664bb5]
def m19 : List ℤ := raw_ints% [0x0,0xe32a95885c0bda37a3e44ccf3adba42a805000,-0x10a9dc4a0a6df355823ce72799ab03599d64ec00,0x94d6dec999ae82b7738dc12ab69d70ddad6fbc00,-0x3492eeea34b15f29c91c260350fe712e6999ef000,0xd2f8865d73d9899c5a5f3f6b6f35ee787d8278c00,-0x27f6a6c7d86a3f79bc42ef723dfca8cb13bf596d40,0x5f0154bccd65a32a5752cc0a5aed2829090aa950c0,-0xb59c391537b836da54868d32ccf97de5479fce8090,0x11beb4bb96d1335b22571b339507b820396dbc841c0,-0x16f419ab223cec14dc97af9f962db54cd7e3a688ac4,0x18c291b0ee480fdec402b3c8059891fa56f5ee23a00,-0x1661ffd7ae1ba1666bbdc3a9e88be8be48befab23b0,0x10ffc373fc4dd39a791cb0d41a9cc50998600811980,-0xad9bac97d13d255ea3e4a4005fc5554dcfd80e081d,0x5cfc53caff43c615305c6e84e622bd9609d2175490,-0x29a47e320eef73c9a7f8cdbe1423173d0d041dbb58,0xf81788f2bd5da437254585782f636bbf99ce980b0,-0x4c33fac4e2cb77fd23e802002115699e3df5ff284,0x131b1dc66e3325b3a186d9ac029f5f8ba642c2410,-0x3db6f914c385db46e0721c7c87b4c19366b0fce8,0x9db977011cd319f52c828a122b19ab5a24342b0,-0x137d7b9f8aa98e54f65db992f6175fae311f4fe,0x1cf5cafc0e10aeec0485a6c8b053b008e51570,-0x1f249798f7904ce2e4a860ac3091ecc6e83d8,0x170f19c22eb38a59967a688557672ae812d0,-0xafd62226f37acb9a374623554b530d67b0,0x311df5131090d6d07cba7e25bd56aeb30,-0x70509f520d9e01c8824896a37e16728,0x6a7db74b1415650196f29fb3bb290,-0x1d1420ccd130e83f641a2bd0d2d,0x1052e0a4e81d315b4fd80000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 16 66 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 66 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 38 indices rho q19 m19 19 327572756102592000 21=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 38 indices rho q19 m19 19 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0xcc487cebc6345598664bb5,-0x75ddcdbbdeafb9e27390c,0x4266073370d79ad41473,-0x2469ea0bffba85f92ee,0x135f9421ad28ecc571,-0x9f54a0ee8d160810,0x4eba8211d52f7af,-0x252aa80568a372,0x10a29845bf82d,-0x6fd87b64c14,0x2b906338eb,-0xf75432f6,0x4e05aa9,-0x1518d8,0x49b7,-0xba,0x1]
def r20 : List ℤ := raw_ints% [-0x4b705d50feae4fe7b7c581df4679526858000,-0x640781f3566b17be275b5b652649a757a0800,-0x3d4770ef6dece36c7a39dae247256db332300,-0x1703c3459f9f1117991c912b36b87a40e9d80,-0x5ed9ca7011d2a35123f2fe0a8e1966b8abd0,-0x11c1479dac6bdf73aaf4e74c6ea1a9124fc0,-0x27ef49dccf50c472d97fd1ffafab61ae3b8,-0x44b5e2f699d4b7c17b0a4fff3f2903b3c8,-0x5b35c3a5a95d85d3711cd1c214e4543fd,-0x5d71f3ffbe4af17bb877c653993dbcac,-0x494f1719e7bc35aac45f2693fa96877,-0x2b43aa366b64f94039d7e82e9b849a,-0x129998e06b4d2da5373d549f4054b,-0x5805b852f63ce2d3aa2d232c9c8,-0x1005cd9be00e14de119f9aa739,-0x15a8e2c0f4c04b918e43576a]
def m20 : List ℤ := raw_ints% [0x0,-0x12a27e442f8cf8e69071ba4cffd404777c869000,0x15b3f147bf440bd5b19175ad1c13b4659e9475c00,-0xc045775c05a7729450c85ccbe21279e0989771400,0x4353a804f6ef5a55c204a7fb56fdcf78bc5b010600,-0x10bad8bf3390fed12d57769a9600ae0a9437f6ec400,0x3234b353b1d256486e39cc3613482e352decf4acbc0,-0x7618d998c8679eca54ec3ee19d11c9c3c5df47e9b40,0xdf3404ab9bdb266d810de66722dbd6aca98da5dcaf0,-0x158b5c5aaf1af5e6371d9db4ee31f51f55be06f58a40,0x1b8108998adf9aa0836d23c8a8c01aeb6a448a53bcbc,-0x1d4002103a84d49b24e1bf6d26941fc50e2c8206b600,0x1a09a0069577c0d5987f815f11bb1983ec995b082350,-0x13724a8f951c0cc32fbfa8d089fa9744d96c58cb3e80,0xc3023ab0197bfff3e8a5c5b482dccc14eff11b965f3,-0x66617a31e83072b067d6c46110782b7339bcb045e70,0x2cda98ab3ce3fa32a48c69e41a1a1ac75042b9e3128,-0x104d34dd22b1d57481a320e5f174919ad99640cd450,0x4dfdbaf42db704aac63ce7c534b6e364de3a52f43c,-0x12fa68fa9f9d420d1611ce819bcf38721b13f84ef0,0x3b48f259508a099d93b1e545b73a5eb6b1f896998,-0x91eb46b60ce9550398715aadd8e5b92293b01a50,0x1147bae10286ea1998a7c6e786d51721da2cfa62,-0x1876b5dc051f237a6725a9de1e462d576e2ff90,0x18e465637c2312e786f67bd06e0319c8d4a428,-0x114bc9a226d629d274be594661b42e22fc830,0x7a90a0972b8773a72f0c13fffacfdb18990,-0x1f72de3ae6fed99aca7d6f0614ed44add0,0x4128fef8081aa3af445c8523d2f98d58,-0x3715dd7169f4990acc42442a4bec70,0xd27e897089da271e67e69b1fce3,-0x64da7896c2bdefe45bd00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 16 68 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 68 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 38 indices rho q20 m20 20 327572756102592000 21=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 38 indices rho q20 m20 20 327572756102592000 21 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_20
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<21) : intPolyRF (mz e)=rfPoly (C (327572756102592000:ℚ))*rfX^21*(1-rfX)^16*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V6C22
