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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C23
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,23,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x81fd1b38f7350000,0xb6f4dbde6d437000,0x77db631799366200,0x308d39697e16a400,0xd9fb237613459e0,0x2cf9e81d5294b90,0x7114fcfa2715f0,0xdd3a9d18a1ed8,0x1550519b50f3e,0x1a0a85c55381,0x1939609fd78,0x13439af98c,0xb75d4f24,0x5334d36,0x1bd168,0x6754,0xee,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0xe,0xaf,-0xe7,0x34f,-0x9fc2,0x2cee9,-0x7ccf9,0x8bc9c,-0x29bbf8,0x5377f,-0x16497e,0x1dd948c,-0xcbc48,0x1182e3]
def rhoDenominators : List ℤ := raw_ints% [0x267d980,0xc918,0x1ad,0x8f,0x58,0xa,0x5,0x31,0x40,0x48,0x2d,0xa5,0x16,0x8f,0x1b5f,0x2cb,0x2080]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 23
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤22))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤22 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 23 omega6=padCoefficients 23 (omegaCoefficients 22 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 22 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 23 omega7=padCoefficients 23 (omegaCoefficients 22 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 22 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 23 omega8=padCoefficients 23 (omegaCoefficients 22 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 22 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 23 omega9=padCoefficients 23 (omegaCoefficients 22 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 22 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 23 omega10=padCoefficients 23 (omegaCoefficients 22 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 22 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 23 omega11=padCoefficients 23 (omegaCoefficients 22 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 22 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 23 omega12=padCoefficients 23 (omegaCoefficients 22 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 22 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 23 omega13=padCoefficients 23 (omegaCoefficients 22 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 22 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 23 omega14=padCoefficients 23 (omegaCoefficients 22 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 22 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 23 omega15=padCoefficients 23 (omegaCoefficients 22 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 22 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 23 omega16=padCoefficients 23 (omegaCoefficients 22 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 22 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 23 omega17=padCoefficients 23 (omegaCoefficients 22 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 22 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 23 omega18=padCoefficients 23 (omegaCoefficients 22 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 22 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 23 omega19=padCoefficients 23 (omegaCoefficients 22 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 22 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 23 omega20=padCoefficients 23 (omegaCoefficients 22 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 22 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 23 omega21=padCoefficients 23 (omegaCoefficients 22 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 22 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 23 omega22=padCoefficients 23 (omegaCoefficients 22 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 22 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 18 li0=padCoefficients 18 (liCoefficients 17 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 17 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 18 li1=padCoefficients 18 (liCoefficients 17 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 17 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4d,-0x111,0x27d,-0x3e9,0x3e9,-0x1ad,-0x1ad,0x3e9,-0x3e9,0x27d,-0x111,0x4d,-0xd,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 18 li2=padCoefficients 18 (liCoefficients 17 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 17 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x1b,0xd,-0x15f,0x507,-0xa9d,0xf15,-0xf15,0xa9d,-0x507,0x15f,-0xd,-0x1b,0x9,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 18 li3=padCoefficients 18 (liCoefficients 17 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 17 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x1,-0x37,0x177,-0x4bb,0x8fb,-0xa03,0x483,0x483,-0xa03,0x8fb,-0x4bb,0x177,-0x37,-0x1,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 18 li4=padCoefficients 18 (liCoefficients 17 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 17 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xf,-0xa5,0x235,-0x267,-0x549,0x176b,-0x289b,0x289b,-0x176b,0x549,0x267,-0x235,0xa5,-0xf,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 18 li5=padCoefficients 18 (liCoefficients 17 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 17 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2f,-0xdf,-0x111,0xf9d,-0x2ced,0x3cdd,-0x1dcd,-0x1dcd,0x3cdd,-0x2ced,0xf9d,-0x111,-0xdf,0x2f,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 18 li6=padCoefficients 18 (liCoefficients 17 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 17 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6f,0x93,-0xfe3,0x3051,-0x21e1,-0x6605,0x10c35,-0x10c35,0x6605,0x21e1,-0x3051,0xfe3,-0x93,-0x6f,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 18 li7=padCoefficients 18 (liCoefficients 17 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 17 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xef,0x929,-0x2e59,-0xb4b,0x16d3b,-0x2d193,0x193e3,0x193e3,-0x2d193,0x16d3b,-0xb4b,-0x2e59,0x929,0xef,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 18 li8=padCoefficients 18 (liCoefficients 17 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 17 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ef,0x2b6b,-0xdbb,-0x2a0b7,0x56727,0x15dab,-0xe32fb,0xe32fb,-0x15dab,-0x56727,0x2a0b7,0xdbb,-0x2b6b,-0x1ef,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 18 li9=padCoefficients 18 (liCoefficients 17 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 17 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ef,0xa331,0x2cc1f,-0xb09f3,-0xa279d,0x3ad6bd,-0x29186d,-0x29186d,0x3ad6bd,-0xa279d,-0xb09f3,0x2cc1f,0xa331,0x3ef,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 18 li10=padCoefficients 18 (liCoefficients 17 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 17 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ef,0x22c83,0x1649ad,0x37581,-0xbdef91,0x6e3bdb,0x171dbd5,-0x171dbd5,-0x6e3bdb,0xbdef91,-0x37581,-0x1649ad,-0x22c83,-0x7ef,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 18 li11=padCoefficients 18 (liCoefficients 17 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 17 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfef,0x70c79,0x7ea257,0x1b1aba5,-0x2986fb5,-0x7be17f3,0x81f1d43,0x81f1d43,-0x7be17f3,-0x2986fb5,0x1b1aba5,0x7ea257,0x70c79,0xfef,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 18 li12=padCoefficients 18 (liCoefficients 17 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 17 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fef,0x16345b,0x2736c55,0x115a04f9,0x161b7277,-0x3ca401f5,-0x4918075b,0x4918075b,0x3ca401f5,-0x161b7277,-0x115a04f9,-0x2736c55,-0x16345b,-0x1fef,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 18 li13=padCoefficients 18 (liCoefficients 17 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 17 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fef,0x44bc01,0xb494a4f,0x81e7e37d,0x1d6c4cdf3,0x12176ab5d,-0x385b1a30d,-0x385b1a30d,0x12176ab5d,0x1d6c4cdf3,0x81e7e37d,0xb494a4f,0x44bc01,0x3fef,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 18 li14=padCoefficients 18 (liCoefficients 17 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 17 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fef,0xd272f3,0x31b9e43d,0x34dfa1bb1,0x146d75993f,0x309229223b,0x1fb33ebb75,-0x1fb33ebb75,-0x309229223b,-0x146d75993f,-0x34dfa1bb1,-0x31b9e43d,-0xd272f3,-0x7fef,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 18 li15=padCoefficients 18 (liCoefficients 17 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 17 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffef,0x27fd7c9,0xd4e9b207,0x13e13cd395,0xb619b7b75b,0x2eacce53cad,0x5ce1c766ea3,0x5ce1c766ea3,0x2eacce53cad,0xb619b7b75b,0x13e13cd395,0xd4e9b207,0x27fd7c9,0xffef,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 18 li16=padCoefficients 18 (liCoefficients 17 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 17 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 17 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^17 := by
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
  | 22=>omega22
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
  | 16=>li16
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 22 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 23 at hb
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
  · exact omega_spec_22
theorem cache_li (j : ℕ) (hj : j<17) : coefficientsPoly (cache.li j)=liNumerator 17 j := by
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
  · exact li_spec_16
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x9cc339169d4d343100,-0xf706ce5b45b1b0e34c0,0xbb60c8e69c16adf220c0,-0x5b187e6e885181fe85bf0,0x1fe26e9472fa4027936ef0,-0x88e6d912795bebeb94ef40,0x1d4a28863cfbdf4c09d7140,-0x5210261ad9b5189749b8f7c,0xbfb6442e46af8195765253c,-0x17a83fdb53d4d775b910bf20,0x27df0d310535ee52d5d745a0,-0x39c8e255d7e50f13087b6080,0x486635f87683e1189199cd00,-0x4eb54549e4c52d0affde5b60,0x4a69db4f8ff74f6008c5f620,-0x3d3e92ff64a00c6ea418001f,0x2bdf2871e958fdc3237e664f,-0x1b50ebfbe3f888ddd98e6898,0xebed39cdf1a3105756db6f8,-0x6dfc8a2604440f2fdfc1af4,0x2c0bb239390d0a007520e94,-0xf0b861b38e0a39f9bc7d08,0x457dbd89eee4057ff90868,-0x10c0f65184c7e836fbd716,0x3525f7711077c3bb9a3d6,-0x87e2089002d5a180c108,0x11084316063cdbf069a8,-0x19d065ae4d6f9159f84,0x1c059eeceed7254e64,-0x14128a16997564158,0x845d3d544126fb8,-0x1817a2afd9fbe7,0xfddeca6a037]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 17 32 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 32 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 40 indices rho q0 m0 0 20964656390565888000 22=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 40 indices rho q0 m0 0 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xd78c6e7f184a27c3600,0x14e7ab4d4064405548880,-0xf9bdae51a5c90d467d080,0x77760186c7858bbb6ee6a0,-0x291f02f17707452757908a0,0xad8e44b17e011a073268f80,-0x247b088f9d903dd253a74b80,0x645cb11952425eeeaecb84a8,-0xe615569beefd118f6f2b6728,0x1bd81a4093737278565112cc0,-0x2dfd6dcda55a5b999398708c0,0x41456df3b62f722413f9a1b00,-0x5004f1b233407cfb47980b900,0x550b632e99e23cf1b32fdba40,-0x4e87140832f282ae2ab27ce00,0x3f0e046d24ec5d25ea3c086aa,-0x2c03ee3e1f21bc8ea8410ad8a,0x1aabc2544e8a1cc56f0a48510,-0xdfda279f63c1e33b2fdb3450,0x653ebc53521015bd08fe28f8,-0x274333cfbdeaba7f18a429b8,0xcf592cf4d95a80520fde6b0,-0x39b2a668d5556e7cdace670,0xd5eb7d4fc17d91d1502be4,-0x28a06a0ce3f038282442e4,0x631504cad1f596dc0eeb0,-0xbc97b1f5fe98df1f7a70,0x10d8a73437f754ef0d58,-0x111a073f59dc8814a98,0xb53c9b65a87adf590,-0x43f803226d778710,0xafd13f56f441da,-0x631d06892d7a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 17 33 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 33 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 40 indices rho q1 m1 1 20964656390565888000 22=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 40 indices rho q1 m1 1 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x1286117eec165f6aca400,-0x1c51b7d9119102118fbb00,0x14d2cc2de303496c834eb00,-0x9ce175e0bfe80fbff99d1c0,0x35222af6f032938ed91dbdc0,-0xdc8a27921b33654b6e35d500,0x2d9078262379439e7c7b32d00,-0x7b24141a1f17956e1b4734670,0x11527ead40b3891b201b26c970,-0x20e854eaa5f81632a908980c80,0x354a16ed95af87ac04b6636780,-0x4a1820e522faeaf254a98f0300,0x58eaa0d95aaa1cb4f5933f7c00,-0x5c6b818a22ea12503eab84cd80,0x53606558b12161a9f612765cc0,-0x41569875b40a0a2857566281dc,0x2c757ce31dffd9c63d564b5a5c,-0x1a399d0f46276b1f0f55ec0160,0xd5f321fe743bb5ca79f76b5e0,-0x5de645031b16d008629444a50,0x23447558a9887a946579491d0,-0xb3fd6da730bbf19ae1468920,0x3047554b7349af0a74a05e20,-0xac07518da8b80d3aa79c918,0x1f49b8db5e826f033415c98,-0x48c3e2824fe1bb937cbd20,0x83613891bc4cb753ad9a0,-0xb0eff7073c1f1aa1dd90,0xa7cd20029efdf8f1310,-0x66a0f0557975fef860,0x22f627a1041d72020,-0x502edfe43bcc7fc,0x26a9ff7e012fc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 17 34 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 34 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 40 indices rho q2 m2 2 20964656390565888000 22=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 40 indices rho q2 m2 2 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x1978580e849ec332d61800,0x266186f1f500c9754961200,-0x1bce58e4d74cbfc8c0393200,0xce4f0d680eec8b15ad9c0680,-0x44c82c1ef36b50e903ccbce80,0x118e37438bc3802af10f1cce00,-0x39110893b80ca44f3316b26e00,0x97928131fa342fb269a8b98da0,-0x14f11ea6a2359ce8c84fac9c3a0,0x270c9f8326e099d6556522c3700,-0x3e05f51c4fd645561d315599600,0x5485045bddefe587af78ef7cf00,-0x63529865750461232211cf8d000,0x65002f4542b3e50c123c90f0500,-0x590e045fac96cdcd29f98cbf3c0,0x4421d59cecb2980904f40dc1b28,-0x2d3450c1db6ec200e362aa550e8,0x19f6e5192e38f74beadf6939840,-0xcdf19638d3a3f95569b54a5640,0x57b984fe623295f41ff4d7c3e0,-0x1fea4ef2be615a312e0fae91e0,0x9d6b52da80060091d7b1996c0,-0x28b39c27ccb2b90c0cfc10240,0x8b5ebaa28b61ced0cc530d90,-0x1845252a90b7fb5b280e9910,0x35ce2370b81dfb2be1762c0,-0x5c1a445cf6d6d12177bbc0,0x74cb6bbf09dcb4ee55260,-0x675e4c60fa3387faf960,0x3a4c3f4716424904e40,-0x12027b186dfc387e00,0x248fab9de88b61e8,-0xf1240587954a8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 17 35 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 35 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 40 indices rho q3 m3 3 20964656390565888000 22=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 40 indices rho q3 m3 3 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x23057913f65a4c65e661000,-0x340aa0e084be6baf83d18c00,0x252a01ebec670ab33efdb4c00,-0x10fae6b6c30eb124ad73fe8f00,0x59336a5926883c55be3d80bf00,-0x1668f6f5f469c86132d4860b400,0x47aa52a7f4a01033b9910d12400,-0xbb2701923a37c4fcd7a327a2bc0,0x19686c423be2e05f127d0de37bc0,-0x2e857b7ad7125546b854b40e4600,0x48812af76ab71b6693d42d4be300,-0x60df2afe28c9780415b82251a100,0x6f8494c15fcd855690d9ccc9fc00,-0x6efc8c6e16c394f56814b3dc8200,0x5fad2fd12d591f153c2731a2ab40,-0x477bf369668170282d6bece15430,0x2e427098ac63b92f1c96576483f0,-0x19e11f1047c13a1b380aec8ee380,0xc79d96f5d5cda858bab25e2ac80,-0x528a5c44710cc767241243b5840,0x1d1763cfb37cfca6da4dad43340,-0x8aafc635a013f4a5be8133fe80,0x2290769bb90a5850874a28f600,-0x71b92e6ea3dc475c4a4c60ae0,0x12f515cecaaa38e7652a95160,-0x280c2b67c54fbb7ce3dee280,0x40f4fc459b2c509bef55280,-0x4d7fe93d3582d5ca9a1c40,0x3ff1a690e0e77b0ce5840,-0x2135c587b478f09bfb80,0x949ecdebf1e5d114c0,-0x10aa969558ace08b0,0x5ded8729be5070]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 17 36 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 36 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 40 indices rho q4 m4 4 20964656390565888000 22=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 40 indices rho q4 m4 4 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x81fd1b38f7350000,-0xb6f4dbde6d437000,-0x77db631799366200,-0x308d39697e16a400,-0xd9fb237613459e0,-0x2cf9e81d5294b90,-0x7114fcfa2715f0,-0xdd3a9d189e698,-0x1550519b40e5e,-0x1a0a85c35b4d,-0x1939607cc24,-0x1343996fc7,-0xb75c98ae,-0x533147b,-0x1bc5b0,-0x65c9,-0xd0]
def m5 : List ℤ := raw_ints% [0x0,-0x3027867b72bc290c1cc56000,0x46988ed2bc9855d607d5e0800,-0x31b7581cb69f4de161959d8800,0x1663fa780d86e2d10801dc44a00,-0x73e33e35ca159d92db62419ea00,0x1cab9b56e279be70d94223e8f800,-0x5a3cb3520a98c51fb266d8fd2800,0xe7cb54805270ee503e967fd10280,-0x1eef0f7c25c81b226673b4c371680,0x37a39ab00169fc39a331f50da7800,-0x551edeed15392e20d0c1e12e98300,0x6f8c410df1a575f633c1c53191700,-0x7dd77da0d3d13381088fbf25e4400,0x7a9e0d2daf0cffff5bf01987bf800,-0x676114c7d56ecd3a3de6d88391ac0,0x4b742b835e16f372a0eef7321af60,-0x2fa36f58f840b8b8d0ff79d327ca0,0x19f6ca82260ba2132f846672e8f00,-0xc2cb35a9f4a685ecad5485c19000,0x4e33c1315f79448ebf8fb273fa80,-0x1ab45cc8d911c0a625329446f580,0x7b0d3368afd2bffff50e9f50500,-0x1d8f654984e86cd581248771780,0x5d70de736f2242bbf8d19bbac0,-0xee825a8ceb96e45bd7392d840,0x1dfee555736b0285d8a7c4100,-0x2e132d95a38a3bdc37f40700,0x33adfe6855587801ac29580,-0x27b5bfca38ca02b97c4b80,0x12f78c30aa635b611cb00,-0x4cbb69709ec42b6d3c0,0x79843c0a2d2ee9260,-0x248f754c141f5a0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 17 38 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 38 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 40 indices rho q5 m5 5 20964656390565888000 22=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 40 indices rho q5 m5 5 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xd0,0x1]
def r6 : List ℤ := raw_ints% [0x699da61e48db100000,0x9424f5897fcf960000,0x60ab4ba74e0eec3000,0x26fae3429ed92ede00,0xae13393957c726200,0x23b111745d0590b20,0x59116f096a988770,0xacae4fd4611f990,0x107407b11927bc8,0x13d387969fca72,0x12ddf625a9633,0xe1357e2f59c,0x81b836dd79,0x382522332,0x11671005,0x382e90,0x5b97]
def m6 : List ℤ := raw_ints% [0x0,0x423658e9bdc2b870a78f64000,-0x5fced1812b49c058752aa0b000,0x4290fa8cf7f6c8092a93fb2b000,-0x1d90579f502f521b01ed2ef45c00,0x96d260ffd37b58aa7784837b1c00,-0x24c260632a61869eb7b7f434a5000,0x71eaabd9ac9fd18804f37f6b6a000,-0x11ff2f04e7049cf12415f0f50e3700,0x25ca4ff5ac832eb74b1752f46f9b00,-0x42cc2c0466903f2ef8592469823c00,0x645a0a1dbb60200ef4c18228412100,-0x810902a0c9103836b904997de56900,0x8eb4d434b19ff8f5cb5bc245200c00,-0x882ea51aec7f3bbb32aeb7e2970400,0x7053e9060cdc97fc62aac882c72d40,-0x501d235ae501b6c5f5f144ce465700,0x315c7ae626cfe11ef66fa5653923c0,-0x1a374b5947bd9e202043a69de24800,0xbf587a77ee878080d5919ad7ab300,-0x4a97e777567f8b0a3df13df566200,0x18ae9216d9e62055d84fdd75cbb00,-0x6deec9568d2f6c21d71830838800,0x19742c061905144e8847574f0980,-0x4d4a8a42c58b4fecd0aac869100,0xbcc1f904426cf654900b1a7380,-0x169a4262acb3952558a0946c00,0x20dc2158b7532b7887c999a00,-0x229f4e69c67526feb2e88100,0x18bfcbaa3fbc9bad2662700,-0xadb7bff5c45084f270400,0x27a65c22df42b15acb40,-0x375a649e5adde6b900,0xe38953aa0b8c3c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 17 40 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 40 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 40 indices rho q6 m6 6 20964656390565888000 22=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 40 indices rho q6 m6 6 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x5b97,-0xd0,0x1]
def r7 : List ℤ := raw_ints% [-0x2e81a4f84e79a7430000,-0x410b56efa2c090871000,-0x2a4d89ab4ce1e453ce00,-0x10fe2b69b5bd5cba8c00,-0x4b8d2a88b9918a4c520,-0xf6949b11c4ecc55ff0,-0x263a1836dda1813570,-0x49953c79d46d671f8,-0x6f37112840250e02,-0x849d946fa80a04f,-0x7c90db765e5f56,-0x5b68594c35f61,-0x3386fb4884a0,-0x15a957ddf61,-0x671865926,-0x1390be87,-0x1cf7d2]
def m7 : List ℤ := raw_ints% [0x0,-0x5b0aba4164ebbd9ae665298000,0x8214814ad3fb4a0578be94b2000,-0x593450dc7f137e19905160b82000,0x2715eb3859b1f68d41e27bb13e800,-0xc49f7ef1a17da6e8427ad4f1de800,0x2f3b1a44ca0ef5d651f45f9af06000,-0x902d0e3fb1ac4bb837a38ec9185000,0x166c358154e72927bca7cf906377a00,-0x2e522f8cbd793cea3b7f846e942c600,0x507e5a39ab211a7681ef5d4579fdc00,-0x76cb8f6c4ff4cc6c1547bb8fe3b1700,0x95eed4dd20f95a96a2e7870b4611700,-0xa29cf6cfe955904575f720a4537f400,0x980773c5e051d4c2327bcfabbc46400,-0x7ab8460f803546058957f6e88e8fec0,0x558d7200246304c4da8b00055924940,-0x337477b7a754602b26a4dc51bdd1c80,0x1aa2dbdede3948214f7afd5d9441200,-0xbd2bd74ab71143b10316468a705f00,0x479ed3a823741584ab668ab8690100,-0x16f70742afb5130777341799e5f000,0x62defa2faa5ebdd459343dcc57600,-0x16104198cf762cd02e219ff377480,0x4058e5d5368e1014a6f60ebe6980,-0x964fa8fb925d3a7a45b54625f00,0x1121507e0e2bc344177fdd6f200,-0x178e797872aec67acdbf75ec00,0x174bd4abc78ab9464d537de00,-0xf79e67fef8c571f353bd000,0x63a561b2b841bf82c4a600,-0x14808bb3fce670c4c5ac0,0x19341e480bef05d1540,-0x58729068fdbe0280]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 17 42 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 42 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 40 indices rho q7 m7 7 20964656390565888000 22=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 40 indices rho q7 m7 7 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x1cf7d2,0x5b97,-0xd0,0x1]
def r8 : List ℤ := raw_ints% [0xeb584d11f550aec7a0000,0x148562bc5b9cc84b1ee000,0xd4efa7e382d614ea35400,0x55424d41c5ec9527aba00,0x179a994988c33b76e4dc0,0x4cb523ca1016dee32700,0xbd52f13976263b52ef0,0x16a4f0b2eb7e52e7fc0,0x21fd5ab22d2c2ce0e4,0x2832514200166e8d0,0x256140a576601421,0x1b17a1fd0d86982,0xf093085134827,0x631e3a33ebac,0x1cb3fbf3fef,0x53fb075c2,0x75da6b5]
def m8 : List ℤ := raw_ints% [0x0,0x7d2ec019eac424b4fccb1910000,-0xb0afdd61fd943dcf110d41a0c000,0x77a469cd01d4b9b5400340a73c000,-0x33bd4b0fad6f0e06cd7799288bf000,0x100c360b619dedef53c7fed6b1ef000,-0x3ccfeb1b91b729c0a61769b09a14000,0xb6ed7eda4f8cdebc59142d9d4879000,-0x1c048ab09d7ce6cb0fc390c0f887fc00,0x38f6b7c058ccaa0a7634dd528c84b000,-0x615a55bda128c33fe7bfbd4fce4a5400,0x8d31f631228dafcb9ec4da22dbfed900,-0xaefad00ff5e18d5c8ddbc00080b74900,0xba2c708436f13dad1bb4fd7cfc870c00,-0xaa9411b68ac81054167884783dfe4c00,0x86cad36dfbb307375586e4d3a0034d40,-0x5be04705eb966adc68f962f95bf49040,0x35f429ec6e2209426786e19e3cf49900,-0x1b3a8636c8bca2035a7667895a650a00,0xbc32fc067452b22d749347e051f1d00,-0x4535414b58c18d4cd4a3cebcd6bb100,0x1581a4562e849891cb09e21ea9b6200,-0x59805a8458b3c00a26cf27385bbe00,0x133f758d5513eacb7489ea63caf780,-0x35e81677d864127fd6f03afac1580,0x7868f2c396196930257ca86a1800,-0xd0def51a26cd7d11dd7689ea200,0x10f85bbffdc04d8df799c2f6800,-0xfbd4ccbe5866e165a98a91c00,0x9b50661bfa7a586172c1ca00,-0x3943046f096c1b51c4b5600,0xa9b579bd58a6f83a0ad40,-0xb787326e75b6289f840,0x225bfe2291910d700]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 17 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 40 indices rho q8 m8 8 20964656390565888000 22=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 40 indices rho q8 m8 8 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r9 : List ℤ := raw_ints% [-0x3bd79577a0f70d426790000,-0x534ea96455ce3a1bed43000,-0x35e5312e8c5e5afe5e06a00,-0x158508326a13ead19b6a000,-0x5f059d9d2349e020301160,-0x133aed2af946e229137f10,-0x2f43c0a83c2c7df28fbb0,-0x5a035b5f13936f6aafc8,-0x865959586bfeb3d7b16,-0x9dd31587f93959cf51,-0x919998412ea9d1d08,-0x688416ef4fdf23db,-0x39527581185e2f2,-0x1744f1f2e15307,-0x69c8ce0892dc,-0x12dd90e4675,-0x199608684]
def m9 : List ℤ := raw_ints% [0x0,-0xac204823a2cdb278db9742760000,0xf017a1a24eeee6869debb006c8000,-0xa0994439905a264a56556435278000,0x449314d7ed8177e7af470fb804aa000,-0x14fd94c98ca48f6f6c58bf42ef222000,0x4e75771c592d9478ecb610cfce290000,-0xe8a954d986763ae507eabcb7087f7000,0x231ba3e11a535eec12bd886a2df56e800,-0x4646d68db584a16834d1d7b22ebf39400,0x762a5c9c44bcb2540c5d6886b2a5fec00,-0xa87b3e7b8162deaf50db1f72f2aebe700,0xcd169e24a702221d40f7ef7922a299700,-0xd62299de162a4c31cbdad73c8db1ab400,0xc056a5279ad44dccddb90194d352d1400,-0x94d45213ee9de82b489ad61396191b6c0,0x633638a9216a4aeb6d0b7796c2f273cc0,-0x38e66cf0cc452b5bd0516556412718000,0x1c0024a424ad12e9aea4f09ba6090fe00,-0xbc61f870a74a69f67b98811b3e3c9b00,0x434bc83335278be232af3a200871ab00,-0x14449cfa4a43017b8984e107c153ca00,0x51883ec7ca619dd3f9c927448edda00,-0x10e57563c029ad113eccfd0f6793880,0x2d6ee1407a69abf4422c5cd522fc80,-0x6102aba37de19d0d121e79f642200,0xa004158a6e2a74a1a01578b95600,-0xc483ef1cab615183ffa4393c000,0xaacb69e848207524bcc093d000,-0x61b0c5268cb059bae2ca51200,0x20f5570745401bb86ba37200,-0x57d564c4f33a31c5f1bec0,0x537c5568ba5de0a70cc0,-0xd56e6e41052eb3a00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 17 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 40 indices rho q9 m9 9 20964656390565888000 22=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 40 indices rho q9 m9 9 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r10 : List ℤ := raw_ints% [0xcfde63b5bb123ba535540000,0x120d4b5e3d74212477cecc000,0xba75c7fa3a41e5b278825800,0x4a459c1f1e1a613677a42600,0x1470f642c610b9fb0052f780,0x41fbdf561214fdacca844e0,0xa19a3e4ad83733f28f70b0,0x132824e8dc83892133fbb0,0x1c7525fcd57c25d2ba030,0x213f0bc3d51ac197196e,0x1e78fccc25d2379b28f,0x15b4ac8e0d506ad728,0xbcb51fd8452a82b5,0x4bbc4fbb19830e6,0x15371a5a131699,0x3b735bc2ac74,0x4ebeaec843]
def m10 : List ℤ := raw_ints% [0x0,0xecac6330ffdad5662deffb6240000,-0x1466220dd5c8083fe17a37ca21f0000,0xd7bff6af6598e8b9626f02610be0000,-0x5aff55f36d03a9532dce5cde777fc000,0x1b7ffd897b22fc035a0871af78fa7c000,-0x656dc08d3ea84023564af78b68f0b0000,0x1289f8ed9a5b722e06ceba4744f463d000,-0x2c1d448be57c03d1a0156a7c66ab70f000,0x56f944425b643a967ccf75bcd975a26400,-0x8fee56894fa276fba52af947924785b400,0xc9d167315d8f31ab36d55c9343956f3900,-0xf163ad0741d0b82dc22044d98ee84e4900,0xf769e29adf98529041e5285b8f20128c00,-0xd9eceff90b38d518e54781e7951bbcec00,0xa52c1f5462b6a620334e377c920f032540,-0x6bb64120ebc7ee0bbdfcd3e0133a78e540,0x3c587b707cf34fa777740924a6d27dc600,-0x1cf6683bd0cbd5f020d4c3ed1896741200,0xbdb29d86b0eabeae9d70f3d08b7872500,-0x41d632aa78933233e92bba084f000ad00,0x1337fa3fc749b18eda34d7065e45dde00,-0x4abaa3677379680b5b672fcdd6dc9600,0xeebf3cd1c41c2f8189814e3be7c7f80,-0x2683e30f588a8ec2afdbd342a65a780,0x4e96d0d4cffb965922a2dbb50b5a00,-0x7b34d51e25dde4c22e38c1c047a00,0x8edae15c77a3bfc85804c3cc0000,-0x743fafe0001673201c5b6804800,0x3d9a6d5765743e8e1f604fb600,-0x12ff2026452d0e8f2178b1e00,0x2d789ce44b7d1d691634d40,-0x25f53b330ecb02a54a540,0x52cff2786559c17c00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 17 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 40 indices rho q10 m10 10 20964656390565888000 22=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 40 indices rho q10 m10 10 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r11 : List ℤ := raw_ints% [-0x27fbf0e547dcd9fd101adf0000,-0x3777033ecb439b85e432d25000,-0x23bd4a23b878e5a84ab4dee600,-0xe34bbacbe8bbd0486af8a9400,-0x3e68884390fa8d5c235865fa0,-0xc8e958413523be8e48644f30,-0x1ea8e1e7526089c23dd5f8f0,-0x39f300845292e87137f61d8,-0x55bd6b899f38266d3b718a,-0x63b47f92082e74e640293,-0x5ae5482e8136a89bfcfa,-0x40562bf50b22632fd15,-0x22b2560084154cff44,-0xdccc06d9ba48e26d,-0x3d2c11d95f8dd52,-0xa917489d99463,-0xdc1eabb81d6]
def m11 : List ℤ := raw_ints% [0x0,-0x1456d08635fcce56c7f29f9a7180000,0x1bbdd129ffe263eb3ee8807477660000,-0x12211c5ad5439eb8c71a7783ce2a10000,0x78e51a61f211f9794525f8b704a6e8000,-0x2415a8e2a15c34ce4a63b90ac574f40000,0x836139d2bb5dc441f6d34b0c0fae8f8000,-0x17b0d758c58b9672ef1b03ca26ee1937000,0x3794d4d9012ecbe56cb99a7ece9c3246000,-0x6bf811bff6b12d7059503f8810ad6160c00,0xafeac875ad99a6a588c8ab2d91dc0cb2c00,-0xf2aa6b197166294f30c27691d30fb9b2700,0x11d4958a004a90d0648af8c6ad0c9f219700,-0x11f2234285f5f2baa43b6ecb851116963400,0xf816954879543e10d7cdd1fa0b2b4145400,-0xb83b4b92c69e30b846c3a8f5878d4a13ec0,0x758ef500f96e2088a848f268711810242c0,-0x405a49f65a244606b8d550a5a57bff65e00,0x1e20e5f6321c3f38a5e97e80c5148bd6e00,-0xc02413dd60ce81b63145e2d09283afeb00,0x40caf9b2091ed181d3c7cdc0714231f300,-0x12553ebd1cbe33797c6be6ef4105b2b200,0x44e70b4528f2da8e89ba9db5202f0aa00,-0xd414646c1f0c084363d3a0a6882ab880,0x20d5aaba35ab7b75b39144a9cff8d880,-0x4000c21e7242e69617b99708e538e00,0x5f5217da5866738cafd91815072600,-0x684771d966aa3bbd35d6215337000,0x4f62ee7c89b0d716d0532fdb3800,-0x26efecd1f9e7491bcce60e69a00,0xaf66f42fd9440464f80dce200,-0x178b57b644888b98f411f6c0,0x113fcb428248e0f59c22c0,-0x201cf8b12ea7a93a800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 17 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 40 indices rho q11 m11 11 20964656390565888000 22=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 40 indices rho q11 m11 11 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r12 : List ℤ := raw_ints% [0x6fc5163fb3238d47be75b4e0000,0x9ad0994fb952e81c89106f0a000,0x6397750fb65b3fab657de059c00,0x278359d2679d9cbeedfe6b23200,0xad393472680ee5db045a226d40,0x22c59e69742b6bd2fb9c425ac0,0x54ad0032e49fe7582eca5f770,0x9f8ffe5d841d81b77cf2a7a0,0xeb463cebf4b609f74d399fc,0x110852f068d70c6be075d4c,0xf750cb5071786fd5757bd,0xae21383b8ccf33f42a0e,0x5d53fbfc5f0ddfa4f03,0x24d907a6e1dfefc1e0,0xa1e8a25768759283,0x1bac7f4e0cad6e6,0x238d3b0792091]
def m12 : List ℤ := raw_ints% [0x0,0x1bf75eb88a3b9bb752ed9b745c100000,-0x25bdd0abe7e16da4f026488a37a300000,0x1864a69dc941fcb0c5af3c8b47da270000,-0xa0cd01b2d9795149eb723011fbfe550000,0x2f6bfa96aacddd9e275d635cc331a1d0000,-0xaa8023010aae26d3d4f351ba40ec6860000,0x1e57eb8546562b8bfa621afab434c9475000,-0x463700c59ba91fdf3f593fa2771a5412c000,0x866fb0dd7ccc54178ac74ea97aa447e8b400,-0xd7bc1edb02b21eb5607d84ee962b5a7d3400,0x124dcb4288680f9195873037aee163a4e3900,-0x15286ded8eb639ca455e63f4fe0a63b7dc900,0x14eadfb7986c66ae13c4338262c108b930c00,-0x11bbce59319f8aecf5654862ecff78529ec00,0xce8067ec679111be11895ef2e3e8e5c2dd40,-0x80f7ff1391d93faddba26c7c0b7b550e7140,0x44fef759db033311c0d6c8f0de05c24f1a00,-0x1f842a577a54beefe203a3db248dcf817200,0xc3ba9faa7f8ee6394b07e887b60b3a5e500,-0x4022df3336a42738c2e81a4974164a5bd00,0x11971ecda6d5e8e5623c9b1e59df4320e00,-0x3fe616fda5d3d51cb001d76f6561f1b600,0xbd759c0398d3465bd05b02fbf652f2f80,-0x1c24e6148087db0f1a7a5e6135d0d3f80,0x34639063ac37c17530169598be96e200,-0x4a15a0efecc70d1d0c75bcd428e9a00,0x4c6b3222ada1c9bf3cf925d7a58000,-0x3661817da2e30bc16e8e0a06e9800,0x18a9add2bf65053777c354a3a600,-0x65540ae7ed84469c54184ffe00,0xc3120af6fea5575bf3a72540,-0x7d59cf9692e9a3807b9140,0xc72304cf780b73a7000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 17 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 40 indices rho q12 m12 12 20964656390565888000 22=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 40 indices rho q12 m12 12 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r13 : List ℤ := raw_ints% [-0x120d5119f5853a453d237a5050000,-0x18f8a4061a7ba89ad2c9ce5e47000,-0x100a4d6b996e021e3df07df1ce200,-0x65a805ef76b54545539ee54d4800,-0x1bcd61d1d994687ef1cd2e10b5e0,-0x591c18b5504fb1e135242c35f50,-0xd87e752203f5b15ff1550f1230,-0x196e3fc2c36ce553631a8880e8,-0x2562d50f542670a8b88d0ba7e,-0x2b287d9ee1df9f0f2259d215,-0x2703d72042cd975cb0833ac,-0x1b58e124fb2a09dfcd808f,-0xe94d6fab76b379ce2956,-0x5b8e06e688f1c412c93,-0x18f697def72426da08,-0x43af2f1f3b637411,-0x560cd92fd16fe8]
def m13 : List ℤ := raw_ints% [0x0,-0x2674223dbe11f61c1206b5bffe9600000,0x335d915433634658b9df4b21460bfc0000,-0x20d88c5001dfa861b96c27f3a30a5ff0000,0xd61ebe058cf87e4a0a9961b83813cf20000,-0x3e6a12bc6c3b5eca79d5269bebfdddf78000,0xddaefe3d81b716760aad6f6306b401118000,-0x26f3768b9e517c3c5645d958d1797bbaaf000,0x58ee5aa768171861dba5d27797c8b97e8c000,-0xa7e28aeb50285efbfb577cb332af6ba19ec00,0x1096f9c5b1761396ee2f3aef26f4dcb3412c00,-0x162b9507e3eee94e4da7492f33084d02e52700,0x1934a2cb118dfb41df5879f27993f540e89700,-0x187c2903c70f10622b7dc094e4233353f6b400,0x145fc953d8baefe982aae57a1217d379fbd400,-0xe8943717a6d7398cd60c940104e1dfaea06c0,0x8e33f1248273eb172a6737a3d6fb93f92c2c0,-0x4a5d56f9a83acf0a2529474898670d1a95600,0x2125d429da1364954379e8c52089ef8b76e00,-0xc87f8d81a998ebb10a5b4f8e6f74ffcd0b00,0x3fd8a00c37ce59277763a165948caeb6f300,-0x10f9484d539e093c5e09288031f68f021200,0x3b97a7a464bfe47bd0be60f5d711fabaa00,-0xaa2e7ac187a561449b21365506574da880,0x18400f53f981448b429afd6a889021b880,-0x2b1769bcf663d6555471bd01328ed7e00,0x39d4aa457ee70eb142b952bb08892600,-0x38357818bf828308307ff12e4281000,0x255bcc67e37deecb944cd8a992b800,-0xfa6b6fc1b4b47610d905aca47a00,0x3a96c786532fd694dffdb606200,-0x65036cdd8ac88e9f7b44cfec0,0x38e7300179ec3e7cd6762c0,-0x4d234b5301a4e711a000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 17 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 40 indices rho q13 m13 13 20964656390565888000 22=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 40 indices rho q13 m13 13 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r14 : List ℤ := raw_ints% [0x2bb18d4a3d9b2342ffec1503080000,0x3c5e9b7d22cb3d12f9665a0da88000,0x26ba2d018b406bc831ff9889e26000,0xf513c422f071f602402d61a83be00,0x42eace3ef516e069fd8d464fc4b00,0xd615fbbd9f2b697067ef07af34a0,0x2070f85c79a446b4e1c75c1b9230,0x3cd4e3e385384cfc65449d48990,0x5932946e49e713fd8d86c73148,0x66aaa3562aba563c51c88e16a,0x5c802b2a4d839b282292eaab,0x4097020fc174f521ae9a734,0x2249ab612ac056fa76d411,0xd631518c30676e40399a,0x3a0ddec2acd1aa8b1ad,0x9c4cfba89d0983618,0xc50c2cb3952959f]
def m14 : List ℤ := raw_ints% [0x0,0x34dfaf14e558b26698c939e7fe0e400000,-0x45eee7fc0da1f92eca2302fffbd80b40000,0x2c4295871e29eea5c2652343e6802f730000,-0x11d6ec3db6d98576edc6be93b85e948e20000,0x52445cb23f495977f90b46c57083359960000,-0x120c1daec727a8c092f002f62c01947a9e0000,0x321c05d37d5b26cbf2fc1e56660b78a8a3d000,-0x70ebf8c48b89fdabd99e6c4bfaffa383788000,0xd2429136e2070e57a58cc4ae2baec13a81f400,-0x147a3a1880e3153b232f4cfd6f7b7b19e5d3400,0x1af2d97eab6f5e0585a1480f28705f4f5b8b900,-0x1e24ce1fa67cc74c3a6ad0e119be39b4bc04900,0x1cc7ce25862c4fbe582e7ec63221d64ab3b8c00,-0x17831dc20c8776321d9b7840f8ae3e4147c6c00,0x1072f790bf213ce42da1e3c76d968632f521540,-0x9d927d0981f4fa93fb3e55d2e8fa80c6aef940,0x509099ccfd7503ace939123205c49bddd92a00,-0x230cb70b2ef8a32b95f75fffe5a68a59513200,0xce8144c77d8b8212400214cd9089782fe8500,-0x3fe8b95f31871cbf37a14598643dd77ea9d00,0x10783651cf7bf4ca8fc1ebd391e9767628e00,-0x37e16b5e81a27067c8c381b23708d2fef600,0x99adb0a345430086eb6ffc5ec4638457f80,-0x15003293188c0600d8291cd3d4eb0d62f80,0x239c1459893ed5535744c218fb4e60c200,-0x2d548ffe303d009c19203ef4cacc8da00,0x297cca67eb53db44c53f295ee07aa000,-0x19bb9404352f4c7080a5f320d29f800,0x9f31052aefe0a00aada5e9bcf2600,-0x21e7004e12272bd4b9e82de63e00,0x344df082776da66f42c534dd40,-0x19d1469c8d66c22070609940,0x1ddd608b5a9225f2bc000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 17 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 40 indices rho q14 m14 14 20964656390565888000 22=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 40 indices rho q14 m14 14 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r15 : List ℤ := raw_ints% [-0x640df482cd4c82da55d0c3d62eb0000,-0x8a1807ca42425ae95f9ec32fa0a9000,-0x587b9cbfc519b8e6205c6b826285e00,-0x22f359771b2c9f0d70889147ba17c00,-0x987763dd6b0ad2c9c6b88a670f7420,-0x1e6fc64c0371f1eda3af1d4cc47370,-0x49a927ab70e65d15bf8808d3c1b70,-0x89d7a7e81c020186700b25d14df8,-0xc9a840ae1dae45b9e5abf5b03f2,-0xe782cb44d6985d10eee0b3c0d7,-0xcffb03db41475b403cca2641e,-0x90bee17c9b80ca6028c48f49,-0x4c8c843b52ea7e774a27428,-0x1dc1f049107f24dda28e79,-0x806629b9e7aa0f385dfe,-0x157aaf383f1eea35f7f,-0x1ae455e657a2ee3ba]
def m15 : List ℤ := raw_ints% [0x0,-0x48b390bcbb59f54d1214af9efd539800000,0x5f3f332f6fe624b99fcd1e79e86afd740000,-0x3baef60bce9a7baccbd8839f663bc661f0000,0x17ce75386db426916a3f01e923336ef8400000,-0x6c96d778be0c60136835e0f9cb3958512d8000,0x178cb812d0f36c146597ac6d90521446df18000,-0x409a161b15b00a5d629e12f5f131dab1d6c7000,0x8fbd570273bd01bc5a886ced71010b01387c000,-0x10812a7d7344d0341dd01105e09c0e3dca426c00,0x195b18aa42c5122b2876314c28336b67bda62c00,-0x20dee72f6eb8a868531a40a1e52782dde4612700,0x242f94f8028dfb23022d44b71aa11ca719d29700,-0x21f7b982cfa5436d87686981f835026556533400,0x1b4079ef1bbc087fab47a5f9f957aa2dad3c5400,-0x12b32175fee21c51a025c19e523068d16487cec0,0xaf732dfba7bbc4f29f8ff0a42f4c969d14feac0,-0x57b91c9812c1c3eeb3232c26c1bb08299937600,0x254106db73442978121b46fca5ff9b4d8e9ae00,-0xd5d37e8cfc781c947340f0dec5d8bd67c76b00,0x40513db2a5441401bfeaed447895d81d0fd300,-0x10110e3bf3f28dfb2c571b9e63ea3fa8b45200,0x34adbad4ab3ba50aa28bfa6a39d60e7496a00,-0x8b7d963d976d5f2a21a44f2dd488124a5880,0x124680c594d1af1e886575f34961080c2880,-0x1d8f07cba7bac000aaa2f673f94ee7cfe00,0x23ac0be882bdda60155535bf516e3de600,-0x1eb8bc8072bbb07d091d08a3b7fbb7000,0x11c4a8fc14c0b1fdc56d4d8808309800,-0x655a87de332c032e19880fa1c8ba00,0x13a13e0691855455b497d940a2200,-0x1b146e84f4b283ee3a896bb46c0,0xbb51b4e9126c15d0ecc60ac0,-0xb8e8196b20773cef28000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 17 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 40 indices rho q15 m15 15 20964656390565888000 22=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 40 indices rho q15 m15 15 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r16 : List ℤ := raw_ints% [0xda7a5ce07c7abd9de8fdf81d9b820000,0x12d3ffd7d204e8f86f845e3beec646000,0xc0d17a48c5b6c26ae9fc1c472c5ea400,0x4c12a49ac8dffcdbf8b0a0f501b6ca00,0x14b6b8d2a672976b20542df6765970c0,0x42107d94913711136633d0c4ad22280,0x9fa01efae1c5d013f73dab6d354cf0,0x12a2b3e937e1faf4c85a6ba547d580,0x1b3535164fe9bc2bd8ab75d63bf14,0x1f2a3716ce4a4fbb050de63d0ac8,0x1bed095c4acc56abb45b9dfd059,0x13611664b01bcb4bef4c660f9a,0xa37189352396b46c2eabdcdf,0x3f4cc2bb472090a6bce8714,0x10ff5619e295c711f2cf17,0x2d44ee03e5cae5ca310a,0x38598a3e65a8f4576d]
def m16 : List ℤ := raw_ints% [0x0,0x63f6e703819bb149f8dc717a9c52f1000000,-0x81c4b2e69c2033006cac127da81fa4da40000,0x5089912937f5c6ecd88fba471a854f85ab0000,-0x1fcd69459ec07b94c332ca4ef89ddd0c0560000,0x8f886ede8b3b796e5ab55623160ffed7d260000,-0x1ec87433ccbdf3e38afad7628baac76f248a0000,0x537587411d742cb043d0c0f04dd8b6dbff285000,-0xb76932270ddbc36519e69cd4388f867850b40000,0x14c92658aeedd64033c375c2a44db2fa273d4f400,-0x1f7e41386b8eed61734502eab9743d93aef7b3400,0x283b01ef6fa08a0d5e01081a2df51975623fe3900,-0x2b999b843a704d37b8b936d8b88b38bc02c9bc900,0x284001cbbd344ed1c71a9f2af5de2a308d6bc0c00,-0x1fb8a6f286de532dd7d6b602b6adfb74bc11cec00,0x155ac0a7ef2e28650e4d49e6282341cad86734d40,-0xc448c0513dfd857bb6962134ca8506c83193f140,0x5ffd6319fe343bd423fa3edcdf956d72d02eaa00,-0x27cc8d6e1dbd0bbee93f5e740146f795389a7200,0xde8fa1051601eff9b2c762428ab47649864a500,-0x4111b7552c2472c64aede20039cde7307e6bd00,0xfc1841e91b4258746a215f9c0453fe6f824e00,-0x31eab4b886f85b42fe97f1d1c4dc287760b600,0x7f3e6df90c8c1f88088d637f33d9576464f80,-0xffa7a4a098b0f8fe089282f83edab8217f80,0x18a4216c78de2cd4c1559b8a8ae26de10200,-0x1c2d3a0fb663343277a34a0841d418f9a00,0x16d1afaabed82c3e209b51a497c77b4000,-0xc4be2e26991bdd21b727b569c7689800,0x409e426cc92db65ee1ed4c74b8ee600,-0xb5f2c0a18fb9219143351b33dfe00,0xe048b7390a6dcadc66f1d861540,-0x54e61f6a00465d05874069140,0x47849879ea8ec75d770000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 17 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 40 indices rho q16 m16 16 20964656390565888000 22=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 40 indices rho q16 m16 16 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r17 : List ℤ := raw_ints% [-0x1c9cd5250c797c646a0f7459c844910000,-0x276b13a8ce38c3080a8c6bd27f9544b000,-0x1934a9ae99bd3b8e57000ab48433115a00,-0x9ef0e65b6ea9b2cd25699ecb185013000,-0x2b3a037dfe361ccd0a89dc8e8d59e9a60,-0x89afa649f5d61d53cdca6384da29ab90,-0x14c31cda42ccf939d9488703e906c4b0,-0x26b83145d79b576ab9f6ef3e0f53d08,-0x386db0a431e9c9a4f4ee860c15b9e6,-0x40815aa4bdfbf6d954dfee5f5a5d9,-0x39abc4335d1203f46efab787a950,-0x27eb638d6455762589d735b0443,-0x14fb7560b17b9be4c28a89deba,-0x8198ff5ebee477397ee15d1f,-0x22abd671d6120f6eb53fa34,-0x5bf2de694ca8ead66bbad,-0x71e50821cb82d5f164c]
def m17 : List ℤ := raw_ints% [0x0,-0x89737da4d23613c5b62f1c0896f20b6000000,0xb0dc926c27a532ca25aa44b1b263f5a3340000,-0x6cc05d49a1f994752e10fcd07ef665b27c70000,0x2a86ef5124e0fcff183200bb2710c24162680000,-0xbdfa8feac8b2ea6714b9ebb8d0d7640d4e3d8000,0x284e6914f7077d153251f7d1c87bc1f0758e98000,-0x6c0a274d55aec28f08e0440b8897c0a6faa81f000,0xea95a30bc783dd9c507614dab107e9a5834694000,-0x1a3f770b25fabd053aa8cec36c26f73b8aeec56c00,0x273be1ebdd2174055be403f9df59b2926ceb832c00,-0x3166e2a85b75dc2068433eb8bd1ca2fabc3d1c2700,0x34b94cbbe54ca484b8f354ad907970bc2f1f1f9700,-0x2fe188a7260cdc612e978d1c71b3b1bd29531fb400,0x25140663d9397e5abb2d270977120f58375b00d400,-0x187e866f6d2474fa7f6a47e606a62be60df56996c0,0xdc9d3d2a3699ae33fdf1f0bb3da539849bc82b2c0,-0x698b49efa2421131ec891d6fa32982fb1e2013600,0x2abaec42ab67b4bc6bf7040c1556a5e5a98e8ee00,-0xe8d5412e85df33160bbfa370272645a5dabacb00,0x422b1627ff251a9264d062419521651f05483300,-0xf87c4f176e65a40a8ddb635050c138d452e1200,0x2f8989381a1af8a560cdb040c93aa07f5722a00,-0x74a1ede410155e1e0b1a6ee3796760d7240880,0xe088a0b187a1e7673606362b3a480d1a8d880,-0x14a03c18679ac677d98bc0fa024bf1048be00,0x1655cc2f5edda22d019e03e943304d8da600,-0x10ff72e343bfbde5c7d118058cb9c96d000,0x886fe19c3f43c538d36caee1eb960f800,-0x293f67a6d73f03da92d8aa4a7f8a7a00,0x6972a33c5740fe985de771ae94e200,-0x74133400a932b79d93fed05c8ec0,0x267574c4d4695f1a43e1db52c0,-0x1ba60a458a99a2990fa0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 17 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 40 indices rho q17 m17 17 20964656390565888000 22=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 40 indices rho q17 m17 17 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r18 : List ℤ := raw_ints% [0x39d5048e90e3f53aaedef2b07d2f1bc0000,0x4f9bf693594be0aa619c599f05a87144000,0x32dc60912f823eb2330a4b87a14f14c6800,0x14067b9bd5027446dbfc8570cde09bf5600,0x570bd0d4bffb2c7c4f87f81d539062be80,0x114eec37730420cf6dc25cda0f59923460,0x29b474a3ad2a20f6183cd4cf1196377b0,0x4da9aef32d0b462ea132bc5594c8f370,0x7100277840a4f6d49c75933de1c9d60,0x80f163f447e170533328b8498b2666,0x730cf1cd0b35d3f899639a851e9c7,0x4f7573b3a14569dc3f8ce2e07440,0x29a8d8ac6a2391dfbc4b381926d,0x10094cd265f40d751d8e5db14e,0x446c226536d659aaeaf7bdc1,0xb4caefa6de65b939d7eabc,0xdf00f261e8ab80fffefb]
def m18 : List ℤ := raw_ints% [0x0,0xbcfeccc2a10a5b2fda80c68bcf8ccfa4000000,-0xf11fcea67cc9dc74811b0f3eca0388a4bc40000,0x92f237beb55d01489ce5986dda159bcc73d30000,-0x38ecbc1e52a52f8b14b73480e9c4fb0f12a060000,0xfbc940f6d2cca6b553534ec78bd1376a1b4320000,-0x34dce94cd87d325620c4daf9596e9bc4d377460000,0x8c230a2661abf6ab475fabb1553cde5a9d4050d000,-0x12cba81dbf3596b230aeebc13a93f85451a16128000,0x213b8d26fd7367a2f31b2648b0e4dc7db03ce62f400,-0x31056f655dd30b85ef709e23fce708ea196efdd3400,0x3cdc88bfb2e8b8ac3950ee67357caec0cab0754b900,-0x3ffbb3144fb65008d274886400ce203457a7f204900,0x392d4ed37b31542d5390d54de330bc1fcc937648c00,-0x2b8472948200642acc30629b9734c000a2492dd6c00,0x1c37b1f8ce4928a6c56cfd2628701b9f64c82688540,-0xf91709152c5feee1ac6430c013a91ed9bbd448a940,0x74997b3f4099b9751673c8252ee75296b26fffea00,-0x2e19ec7c29e12178708be7936c7081140310a5b200,0xf4cacdafd6b5e97a439ea6252f7ea87abd2e6c500,-0x439fa78159d5bdac3cafbaca68301008c838ddd00,0xf626563803d39882964558933adf6693a48f0e00,-0x2d7deaa5fbf0cc2cb37d4d5d019ae210d23c7600,0x6b67c3fc5ce33bd8f645b634a2098325dd51f80,-0xc60f4aec83bc6bdfdfbb2706d7fb2b93be4f80,0x1155283fbaaebc40e0f316e895b7200acec200,-0x11c39df2f4cd05cfc1b3485723a0586185a00,0xcb20b76f874f85b94926bec0c7cce7ee000,-0x5ecb9fd5aa2da18f4eef0eaf0850d13800,0x1a5ba0cece1fe6b2c93199f9ff63fa600,-0x3d21b0dc4f7ee04eff0ea827393be00,0x3c0eddec9124de737355a59914d40,-0x1169a6d6ec9cd1ceb2b4c4e4940,0xaaf1891f32ee4875ffc0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 17 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 40 indices rho q18 m18 18 20964656390565888000 22=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 40 indices rho q18 m18 18 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r19 : List ℤ := raw_ints% [-0x713bf5c99a1ecb831e5d55ebf3ebf6f70000,-0x9bc2a87749078acf4e2827cb99d7a882d000,-0x636ecd63939d99d7f036ae11e5f84479d600,-0x271d6cf1e3c691ef27e3e594f201819e6400,-0xa9dc16aacb92df0b7e1691eaa95bbe108a0,-0x21bd1eb9afed217ea8797651091ac8337b0,-0x5132c7378be7163f5ff85399638c946df0,-0x97026baaccabe4f1903bedabf1ccb1618,-0xdb670552ca68b76093a5308f739e825a,-0xf9f40b747cf43a8c7e33850c0b5401b,-0xde9fccddb3c04dcc3f53b136456e42,-0x997271fd6e06df63efe65f6adaa7d,-0x504581d9108d023a41a54efddc0c,-0x1ed27a3bf850e3461303530b585,-0x832371c31fcc3afdfbd45cfaa,-0x15966b6fb5e6ff82689ee99b,-0x1a87f1b027e9b8b427229e]
def m19 : List ℤ := raw_ints% [0x0,-0x103de598b9d6e3d61cc7111003d619d818000000,0x148d76b203fd25ed04aff71000ef919ee32140000,-0xc6aeaeb727684ca8146c895b4164672d5ab4f0000,0x4c45253ac08fcee4710d784cfc08af2da08cb80000,-0x14e2189c6e0b007fcf6cccc9ba40ece0d07f7d58000,0x457165bbfee6220bcd5144132159e4f84d667a18000,-0xb61ef8958156d9e844f74f9ecce83d02f4c38337000,0x182641cbf1b7fae14092eab3788b3e62240a40d0c000,-0x2a2f20479db9358503ec9947db035caab4cca61e6c00,0x3d6d2bb8c099e619c8f8605e736b8d3a9c2cebfc2c00,-0x4b37c369cafdd7826035e942a73026d357f8caa22700,0x4deab24506bb25807d5b4bee25e7bf4c89751e279700,-0x4488b0e8c2739ffac25713442ecf39757eefdf4c3400,0x33479beed72c438d8bfd2af124db9444163154d55400,-0x20a522e4defade9e66cda19b9e36a8a0abc211035ec0,0x11a7f209d6e59adcedd34709633ae57d3e5744affac0,-0x816935292609bcd70511ec245b947bd83aa7c2d7600,0x31f9dfd9fb1ec9adf042a4721368130190e7fe02e00,-0x1029e67541f79ba786f4a0f71c4eba1f290668a2b00,0x4573174b4c50e85dd9ac0dc53082371e9e0ca69300,-0xf5054645b7bc23b350311be550dc49c702c2dd200,0x2bbd9b2a289e2e8445f347289859fd5c47e9eea00,-0x635ada6cb58db7e6836f5d914e486fc2493bb880,0xaf706e62feaf36dd37f3c7dbb7972fe96108880,-0xe9ea64d299988c3b399e3b4fe4d6575af57e00,0xe2c67861fa35dec4318caa3c5d7229f816600,-0x98178a28c149cdef06ca58d6abe1fee33000,0x41fa1ba32508d9fb807b5e83f741abc5800,-0x10dbe9bea34712df52b562d58f56423a00,0x2372cb2a831c0661e6f95e8f7a73a200,-0x1f10dd593c24d3d26ab752ea73d6c0,0x7e13bd6d9ec2221b204d8f11ac0,-0x4206d5948fa7803272a80000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 17 66 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 66 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 40 indices rho q19 m19 19 20964656390565888000 22=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 40 indices rho q19 m19 19 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x1a87f1b027e9b8b427229e,0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r20 : List ℤ := raw_ints% [0xd78bbf5dd0d5322b3594af66b4b109cb60000,0x1284ca3927a43d47e5efdcf785d9e47d882000,0xbd02b4131857acc36f637315fb5430e11ac00,0x4a4b156f591cc88a33a042dfb8ca58b476200,0x14256c05fe03a13553e8103fc7e40a1c0d440,0x3ff67bbed6465834b9b5a41f49c71294ba40,0x99c5c99c71adfdb30fe7c3c48ab00163270,0x11da4246485f2b1ffed10c6643ab1ab4b60,0x19e77586bb1cd5d160ebace7adb76c8e2c,0x1d77eb315f9d6542cf504d531bde92944,0x1a344d71b085d2d64776a2b12a671ff5,0x12078c71a7d6f18ab1353df8cd92e26,0x969b23b91597e115f4b21f7e7f5bb,0x39b34c3a2dee52ce40f97226f748,0xf4e29d5fb0be4d5d0d94a258ab,0x2832fbcfbdf5e51371e7f1e2e,0x313f7420f344a3513c34549]
def m20 : List ℤ := raw_ints% [0x0,0x16551bb1ff8779466791b77605466389210000000,-0x1c09b88f6365112f5888faa2cd7ab1516dada40000,0x10cccee83f17ce99b2d9d0a005fb0961eeabf7b0000,-0x664910447a354aa1e79b5ac8914acf0ddf962a60000,0x1bbf6063bc15ef926834458d0827a4942d9d88ae0000,-0x5b5dbe0d5fda432d21c1d00492dac956ced076420000,0xed210a0225ed759a7e59d4a01c8351f769a6f42d5000,-0x1f18ba8a59c5b96b287babc8d35bce83211af11410000,0x35ae562b30ca322ed2b5ed5dd88504d27f56ba8a8f400,-0x4d2ffe0ace406eb1426da3802e3e0e30f343d61fb3400,0x5d3ff917c8d98077448e6e06db14da0754a1bddbc3900,-0x5f350a47e5201493c436ef8d8d2d1537714aa44b5c900,0x5272cedde4460fa77f479ca144d3d053669c98d350c00,-0x3caa05957d427fa267457dec11e3c06ba63c13f45ec00,0x25ecb06b5440889db483ff70f164e1454ed375281bd40,-0x141c8ccbfc39b141f7b17d62d3595b40a65155dc86140,0x9048749950c0952ff0e355a13f5ab5148af11ea42a00,-0x366e161b6a9901cbe3c8589774e8c6a3e596bb74f200,0x11286ed25c33d195886ba735e5aa5c956109bd82e500,-0x47aa79e4b4af9814d9f0dc0419c5d97fa04334afd00,0xf50d0b40f2f4a376500b988c22c436de3114a7ce00,-0x2a401138c284bcbc535ff09066e2254ca0a4983600,0x5c4f2fad4fc3b2ca6c010fbe835756e90f5d3ef80,-0x9c07368af00686615256e2d017fd7725e7a91f80,0xc601f8cb1d0af1e8a3f8de400d337cc7c328200,-0xb57ac0b24e1bfc2bcbe14d40e85b7bdf791a00,0x72249e66b3296693e68f7f84798cc6a278000,-0x2dfde5a249cb357800e52f278a302e1ad800,0xacacff987da1cbe806a36368ce169c6600,-0x148f10181e1a02fb3c9effb47bea97e00,0x10107d7fba78fdc6dd26638a7c48540,-0x39068c8b4c4d469b652dff750140,0x197de318a5118ad81e4700000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 17 68 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 68 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 40 indices rho q20 m20 20 20964656390565888000 22=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 40 indices rho q20 m20 20 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x313f7420f344a3513c34549,-0x1a87f1b027e9b8b427229e,0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r21 : List ℤ := raw_ints% [-0x1901aa7705d54d2da065c03c0395a3ec71d0000,-0x225aab96d0edb69d1b436f30e89c67e08b4f000,-0x15e666b02ae04f7bdc3ae00ebadcbd48163d200,-0x89a0e107cce119754127413d2dc638ec971800,-0x254a682238c708c3c607c13f4e7b445e7f9ee0,-0x764a494634d236bc9ca9af94c6719871387d0,-0x11c1a426465ca2a67cbe3553a3edf514a3730,-0x20f2b13fa1b02f5dcc8a510c87738124d128,-0x2fc03e98e772fafc28ad2cc5309a64bc34e,-0x36400a963868b459b5fa827996cb9d069d,-0x302bd5b88886dd9b0aaac9698b6a975f4,-0x2117232e927dfce4e4e7b5935bb0c4f7,-0x113ec2d897c9fed81964127d783171e,-0x69809f878b9e1aff0134329aa9cab,-0x1bec54b6cdd55e9e4f514f70c760,-0x49286b561a48b657507850c249,-0x5960226e433eac21410b4bb0]
def m21 : List ℤ := raw_ints% [0x0,-0x1eb50614bf5a46c0ce685c424740c8dc8d60000000,0x2642d3cc17ecc3bd7f7a91b6a68963be18dca740000,-0x16be241aa6b7c8a5c5811c96c088e913f3d301170000,0x894c90bb98f598a4f66c3589e3ce43f9fa91caa80000,-0x24e9c48b37c10223532b9aeacae2066f63a10a0ed8000,0x7864e082830c1f406c0c8dbfb710b216d45f38db98000,-0x135518abe3acdac6e06d733a7fce259a440bc54d80f000,0x2820ca4a8986f71f0c9d7407c3dcd41469b5da893c4000,-0x447a83025184f9eb82623dcbe6b7301fad598cc76b6c00,0x6142562581626e20778b21c9677d66e0c6678e16c12c00,-0x73f4dd43a5ac6c824fa126ea078027c7645dc0bbdb2700,0x74b8ab7869b3007c43b7d0952e48ee801daa5ed1029700,-0x638b73eb65e1302a1faa272ab08f70206e65daded8b400,0x480acd0801967c191befc298b1abbc61d3112e7b29d400,-0x2c3cd704ee2bc8a83ca2fdf057609cbdc247e675fd26c0,0x1701b2c4f2c8a1f023521a3f8c4d899ac4091edfc742c0,-0xa1949b9b85c3b1e9281fca2c6c78276d9c8baf977b600,0x3b8d6b039aacee8e8fa7971dbddc6608d1390314b6e00,-0x124c543e2563eebdd0124a118a9a3f591b8eeb14d8b00,0x4a4c5e9ec51c5f6eb49780f3ef4e8419be08d5a0f300,-0xf6360ef87b78d626f0dc3e68d2c251fb6aae5fd9200,0x28fe2dfcdf205bc77f55ac0a6844c4b726156b3aa00,-0x5620212889d1060f083b2d409ca9636f59a8f16880,0x8b4d5203fea58780d4cef1c87e169bf6da48a3880,-0xa82ec54e5469b9fc6321eb2b7d8d4fc2be6e3e00,0x91a440feb124a4a97f4c44a5ef0457a734d2600,-0x55d8f0c23e5227f2ed4fb9eca0659927109000,0x201b28206ef99134ca4e261a46fa938c0b800,-0x6e9dc28a30a2a76522197a83385e1e1fa00,0xbecb0ebcb029e075f906dbe2b11326200,-0x84deb3920270f46208a98396b691ec0,0x19c7cb798418ac5651942938ee2c0,-0x9d67a1c3248a2f012ada00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 17 70 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 70 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 40 indices rho q21 m21 21 20964656390565888000 22=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 40 indices rho q21 m21 21 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x5960226e433eac21410b4bb0,0x313f7420f344a3513c34549,-0x1a87f1b027e9b8b427229e,0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r22 : List ℤ := raw_ints% [0x2d61cedc9dd27502b436867da1087bdd7b700000,0x3e4fba36a980fa59cc10e82735c63a04e9100000,0x27b29d1db2f7fa3221cddadfe41749d671647000,0xf94ee07dcc6a97ca66887b744e2e33fdc38ee00,0x43801cc21a0d5f68fd0c9c8ba448745fa5b5200,0xd5f1ef3a92e479f0367fd97f89a9f716378420,0x20161e72f06a3f3f72baba39e1e44bc888dd30,0x3b7ad0334554ee103ef79c7a132e05ffc4550,0x561c247783b0fff75283e81e1d3a9c76d378,0x61b6c0ad2b0caa2bf61ce19f2b2785f7062,0x56a6ad6e672b52d0d7690b2116a4ab63e3,0x3b6ff769d6936db3c24e3978570021e4c,0x1eed28fbfdc71c2d349a766195312fc9,0xbcdd9a3e6d6c67784d3c26cab2d002,0x31e3574525f6bf38edc8a7746d2d5,0x826acaedb66e9338cc393b7de60,0x9eef4ac683b8daf9a002f9b57]
def m22 : List ℤ := raw_ints% [0x0,0x2a38e85c871c21491bcf7edb21f9142f42640000000,-0x343a0e21baebe909d4d2334910bdd00deee1a3840000,0x1ece3a9fbd5911b5d6b4beb4ecf8f736e28cb9ee30000,-0xb8760b89399205bd7ba8de73ee3aa3c18317456860000,0x312a17ba381d00f8925fa7f2983350ebce46091aea0000,-0x9ee1435993990abe1ad5215871d7d9040b0ba1003e0000,0x19434bd40435aa220a60d655c118610ac977160939dd000,-0x33e40d97882c248adc9e57d8d4e30ebbcbefe4fb1f38000,0x57905be93e36a904b6ebf1b6a528597b40d1285741af400,-0x7ae113f5b8fac80632028106cdd826e7f5ea92e6dd53400,0x909efc7486e8eae532e7b90984ec19f6d8a50e9185cb900,-0x8f900d57fadefe49e94512b9a1f127781003adac8244900,0x789bedc5d397de367f2e51ae196d694b9f6987a87ad8c00,-0x55e0750fb8f92ad0050903f3a679d6b4a5f1c87eef66c00,0x33ced37ba6b23ae763f06057275ed3c82d247265046f540,-0x1a6dd0776b679fbe8455d459ee8fb850e5270b2e0201940,0xb5bdaffb3a982f6d8a08709478cbde2244d9ba04c06a00,-0x4172f22d1ebfe5c5d23f0a5afa5263328a22dcd9403200,0x139a5e2825052542eb4bcd579671ee99dd96423fc50500,-0x4d60eafe6c0633cc2f435059b3218ef4e5cfeebfe1d00,0xf87cdb1681383d4a4fbc62f5a66269a401f7a5888e00,-0x27f201fcd578b5091c4983c621637168d3fc8c6bf600,0x50af0efdd1a6de5120f62d338f779e3b8459acebf80,-0x7cd4cf4bf1ba8889d788de81b8e35937f964c7ef80,0x8f503805daaf3086ea8bcbec0a078645c4a0e4200,-0x753126d8caeafc4c77991166ebdb3512b7b9da00,0x40b1f12fe5930c5f4c5b9984bf4c4ed45712000,-0x16710da9142213b370c53b05533b4de1b57800,0x46e76f5d4fc1881788029bdfc44c30912600,-0x6eab2dc4cbc487e424d9b7c761fb273e00,0x44a9b41149fdc3fbc2e84d1eafbbbd40,-0xba63d47dfcd4b190fb0d83debb940,0x3cb89d4a881a5fd91493c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 17 72 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 72 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 40 indices rho q22 m22 22 20964656390565888000 22=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 40 indices rho q22 m22 22 20964656390565888000 22 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_22
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<23) : intPolyRF (mz e)=rfPoly (C (20964656390565888000:ℚ))*rfX^22*(1-rfX)^17*momentRF (key size) (X^e) := by
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
  · exact moment_source_21 size
  · exact moment_source_22 size
#print axioms moment_source_22
end
end CatalanCore.Li2.NVMod.FamilySource.V6C23
