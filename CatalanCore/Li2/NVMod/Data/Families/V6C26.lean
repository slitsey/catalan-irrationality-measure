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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C26
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,26,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x1b5f340376ce01080000,0x29f369e6f37da9d88000,0x1e33d75c99a3bc6b6000,0xd95c4bb4caf3c843e00,0x4485dfe027b0d582f00,0x1018fdf532689d01aa0,0x2ecbe90be6a15b3cf0,0x6bc3ad79e600d4430,0xc7b387368b2b3068,0x12ccf1636a8ef7da,0x17265e5852c4847,0x17591040b59aee,0x1341e49004155,0xcebed9337a4,0x6fc67f6936,0x2ff36bb0c,0xff15fd2,0x3f5c82,0xb103,0x136,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0x5,-0xb,0x4d,-0x743,0x743,-0x18f65,0x4fe1,-0xbec9,0xbec9,-0xb24bf,0x7f5ad,-0x19789,0x1182e3,-0x200db3,0x200db3,-0xb194f]
def rhoDenominators : List ℤ := raw_ints% [0x36a285a100,0xf05eb00,0x1ab530,0x8610,0x1ad0,0x410,0x30c,0xb7c,0x280,0x2880,0x32a,0x3de,0x294,0x2184,0x1b5f,0x861,0xc300,0x45100,0x15da10,0x530970]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 26
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤25))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤25 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 26 omega6=padCoefficients 26 (omegaCoefficients 25 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 25 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 26 omega7=padCoefficients 26 (omegaCoefficients 25 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 25 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 26 omega8=padCoefficients 26 (omegaCoefficients 25 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 25 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 26 omega9=padCoefficients 26 (omegaCoefficients 25 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 25 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 26 omega10=padCoefficients 26 (omegaCoefficients 25 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 25 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 26 omega11=padCoefficients 26 (omegaCoefficients 25 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 25 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 26 omega12=padCoefficients 26 (omegaCoefficients 25 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 25 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 26 omega13=padCoefficients 26 (omegaCoefficients 25 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 25 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 26 omega14=padCoefficients 26 (omegaCoefficients 25 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 25 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 26 omega15=padCoefficients 26 (omegaCoefficients 25 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 25 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 26 omega16=padCoefficients 26 (omegaCoefficients 25 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 25 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 26 omega17=padCoefficients 26 (omegaCoefficients 25 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 25 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 26 omega18=padCoefficients 26 (omegaCoefficients 25 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 25 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 26 omega19=padCoefficients 26 (omegaCoefficients 25 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 25 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 26 omega20=padCoefficients 26 (omegaCoefficients 25 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 25 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 26 omega21=padCoefficients 26 (omegaCoefficients 25 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 25 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 26 omega22=padCoefficients 26 (omegaCoefficients 25 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 25 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 26 omega23=padCoefficients 26 (omegaCoefficients 25 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 25 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 26 omega24=padCoefficients 26 (omegaCoefficients 25 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 25 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 26 omega25=padCoefficients 26 (omegaCoefficients 25 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 25 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 19 li0=padCoefficients 19 (liCoefficients 18 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 18 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 19 li1=padCoefficients 19 (liCoefficients 18 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 18 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5a,-0x15e,0x38e,-0x666,0x7d2,-0x596,0x0,0x596,-0x7d2,0x666,-0x38e,0x15e,-0x5a,0xe,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 19 li2=padCoefficients 19 (liCoefficients 18 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 18 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xa,0x24,-0xe,-0x16c,0x666,-0xfa4,0x19b2,-0x1e2a,0x19b2,-0xfa4,0x666,-0x16c,-0xe,0x24,-0xa,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 19 li3=padCoefficients 19 (liCoefficients 18 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 18 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x2,-0x36,0x1ae,-0x632,0xdb6,-0x12fe,0xe86,0x0,-0xe86,0x12fe,-0xdb6,0x632,-0x1ae,0x36,0x2,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 19 li4=padCoefficients 19 (liCoefficients 18 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 18 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xe,-0xb4,0x2da,-0x49c,-0x2e2,0x1cb4,-0x4006,0x5136,-0x4006,0x1cb4,-0x2e2,-0x49c,0x2da,-0xb4,0xe,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 19 li5=padCoefficients 19 (liCoefficients 18 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 18 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2e,-0x10e,-0x32,0x10ae,-0x3c8a,0x69ca,-0x5aaa,0x0,0x5aaa,-0x69ca,0x3c8a,-0x10ae,0x32,0x10e,-0x2e,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 19 li6=padCoefficients 19 (liCoefficients 18 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 18 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6e,0x24,-0x1076,0x4034,-0x5232,-0x4424,0x1723a,-0x2186a,0x1723a,-0x4424,-0x5232,0x4034,-0x1076,0x24,0x6e,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 19 li7=padCoefficients 19 (liCoefficients 18 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 18 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xee,0x83a,-0x3782,0x230e,0x17886,-0x43ece,0x46576,0x0,-0x46576,0x43ece,-0x17886,-0x230e,0x3782,-0x83a,-0xee,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 19 li8=padCoefficients 19 (liCoefficients 18 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 18 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ee,0x297c,-0x3926,-0x292fc,0x807de,-0x4097c,-0xf90a6,0x1c65f6,-0xf90a6,-0x4097c,0x807de,-0x292fc,-0x3926,0x297c,0x1ee,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 19 li9=padCoefficients 19 (liCoefficients 18 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 18 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ee,0x9f42,0x228ee,-0xdd612,0xe256,0x44fe5a,-0x63ef2a,0x0,0x63ef2a,-0x44fe5a,-0xe256,0xdd612,-0x228ee,-0x9f42,-0x3ee,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 19 li10=padCoefficients 19 (liCoefficients 18 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 18 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ee,0x22494,0x141d2a,-0x12d42c,-0xc16512,0x12c2b6c,0x1039ffa,-0x2e3b7aa,0x1039ffa,0x12c2b6c,-0xc16512,-0x12d42c,0x141d2a,0x22494,0x7ee,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 19 li11=padCoefficients 19 (liCoefficients 18 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 18 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfee,0x6fc8a,0x7795de,0x133094e,-0x44a1b5a,-0x525a83e,0xfdd3536,0x0,-0xfdd3536,0x525a83e,0x44a1b5a,-0x133094e,-0x7795de,-0x6fc8a,-0xfee,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 19 li12=padCoefficients 19 (liCoefficients 18 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 18 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fee,0x16146c,0x25d37fa,0xee698a4,0x4c16d7e,-0x52bf746c,-0xc740566,0x92300eb6,-0xc740566,-0x52bf746c,0x4c16d7e,0xee698a4,0x25d37fa,0x16146c,0x1fee,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 19 li13=padCoefficients 19 (liCoefficients 18 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 18 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fee,0x447c12,0xb048e4e,0x769e992e,0x154dcea76,-0xb54e2296,-0x4a7284e6a,0x0,0x4a7284e6a,0xb54e2296,-0x154dcea76,-0x769e992e,-0xb048e4e,-0x447c12,-0x3fee,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 19 li14=padCoefficients 19 (liCoefficients 18 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 18 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fee,0xd1f304,0x30e7714a,0x31c403774,0x111f7b7d8e,0x1c24b388fc,-0x10deea66c6,-0x3f667d76ea,-0x10deea66c6,0x1c24b388fc,0x111f7b7d8e,0x31c403774,0x30e7714a,0xd1f304,0x7fee,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 19 li15=padCoefficients 19 (liCoefficients 18 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 18 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffee,0x27ed7da,0xd269da3e,0x130c53218e,0xa2387ae3c6,0x234b32d8552,0x2e34f9131f6,0x0,-0x2e34f9131f6,-0x234b32d8552,-0xa2387ae3c6,-0x130c53218e,-0xd269da3e,-0x27ed7da,-0xffee,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 19 li16=padCoefficients 19 (liCoefficients 18 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 18 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffee,0x78e865c,0x376a4951a,0x6e360e2c44,0x5332928371e,0x1c3eb52989a4,0x4b9ce4a7d3da,0x687e0053c776,0x4b9ce4a7d3da,0x1c3eb52989a4,0x5332928371e,0x6e360e2c44,0x376a4951a,0x78e865c,0x1ffee,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 19 li17=padCoefficients 19 (liCoefficients 18 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 18 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x12,0x99,-0x330,0xbf4,-0x2178,0x4884,-0x7c50,0xaaee,-0xbdec,0xaaee,-0x7c50,0x4884,-0x2178,0xbf4,-0x330,0x99,-0x12,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 18 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^18 := by
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
  | 23=>omega23
  | 24=>omega24
  | 25=>omega25
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
  | 17=>li17
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 25 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 26 at hb
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
  · exact omega_spec_23
  · exact omega_spec_24
  · exact omega_spec_25
theorem cache_li (j : ℕ) (hj : j<18) : coefficientsPoly (cache.li j)=liNumerator 18 j := by
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
  · exact li_spec_17
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x57df7feb33849f584469000,0x9dc19bb2850bbeb52d73ac00,-0x88f23c485aa3c7ae88a170f00,0x4c8fd30975fd9c18a512ed3940,-0x1ef9ccf3289ffe9c30a48ccd940,0x9a9800a3a6e47229420ec921f90,-0x26aceb9b8e71d37202cbbf470750,0x7f87a76c166c6e4206295b2ec830,-0x16118f6f86a78aaf34381c79ecd70,0x3408cf4659e24ee5cd73988537bb4,-0x6999b6114c26796532a5e0ffda764,0xb9f710b10a1f56a4f3825b787680c,-0x11df2a4662087a98b77262dc32295c,0x181b8276527c91fd868fc420b920a0,-0x1ca04c67128df3f7b83e3767e96420,0x1dfe856a0fa8d19a9957b13139e510,-0x1bc5883933eea6a89fa67f1d1211d0,0x16bc458cef9c0739538b4bc95b43dd,-0x1073dcbf5f947c1b92cb2ce96d3c09,0xa835300d056914f7a373542d81113,-0x5eb977a43b962c4c5a69cc5c6e827,0x2ee0d67acea50a7611fe2d980abd4,-0x144f50d4c1acba2ee3373f44f8484,0x7aa2e42439ff8202a711091c41fc,-0x280f732f1b4a7971fe79ada8fa0c,0xb3ca24c375dfc2b6dfa7f5f4eaa,-0x2adf1cad96edfd3ecdd591766c2,0x894c289cf38a4429e93c69c326,-0x16b297074251a096701cda97ce,0x308e7d12045738e269bd00d34,-0x51b44ffd14003328d6748d64,0x681562ccc3ba694620bf84c,-0x5f0a0e43d58d83bb8ef71c,0x393b7ed5ef71cad5ad98d,-0x13c9349b6fd3987d6279,0x301f8d1ae6429815f3,-0x1a50295d717ce407]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 20 35 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 35 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 44 indices rho q0 m0 0 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 44 indices rho q0 m0 0 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x894d37df807f38f9eae41000,-0xf2ba28aa5664101c22ebc9c00,0xcf6a68543a35e34e4838c91d00,-0x721aca63c092721e5b62a9dd1c0,0x2d68c5ba1522460ea3065e362000,-0xded3a1f00e48c7cab109a00ac870,0x36c969c4c1c11b2bde73c49d3b180,-0xb1778d393abd4333b04eb647026f0,0x1e273bc3b6523a76fb593cf0c12620,-0x45c58ca6f9133fd1cea96fd143c6ac,0x8ae196806f4f2a8b0466e0c47f84c0,-0xefbdb634772645f4ee8782c82d90dc,0x1691fd8cf0421d7cb92584063f52528,-0x1dce0776c9562dc16dc4d922e2aefa0,0x229f1a5a00bb9993dc8ffdcb9eb4240,-0x23757dcd2be6bc7c966d26596ee0fd0,0x2010810e7effa87dbfcba07a9fa28e0,-0x199ce2b0b018aa6abcb54bf1b0f685b,0x121114a7711319eeaef102282cfaed0,-0xb3d85c81aff79b8d38f40021565327,0x627d4eaa15a42320e2c0be0b7fa5ca,-0x2f55cc37d16f89f53cec317ae4807c,0x13e2c850d5872399e2ef9f59212cf0,-0x743cae3d51552256bb8c592f6a15c,0x24af6b5396cbb4ad4f5200c2b1458,-0x9eb8e5ba862ad978544d73337fd6,0x24650df9c3317f250810458b2ff0,-0x6fbfdc44b5e22e888f79bdc68be,0x11a68b368aa837576bef8595744,-0x23ecd20b32d49badb3d67d56fc,0x3937b55365bdef44d09bc3650,-0x448c3ff4acd31b47891ac14c,0x3a5f69ac4d71e2ef57fb518,-0x206a9a08f5e44c55a1a39b,0xa2c2bb2994a9d5ab2780,-0x15effeac26cd6d7ca17,0xa43b69ab5288965a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 20 36 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 36 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 44 indices rho q1 m1 1 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 44 indices rho q1 m1 1 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0xd688a74d38c6c9067f0459000,0x1759c579f40beea5d886afebc00,-0x13a64464dcf674aca9e5b03d2b00,0xaa4168e01cea4fa0553420f0f840,-0x42abf3c7f464523ea58051819ad80,0x141cc877658288fe35bc551bb12f10,-0x4dca452301ac83701107f91b358160,0xf7a063e5ada4a58b4e01cb34426bd0,-0x2953a838b35e74ef4f888442a2c37c0,0x5de0fc5b6c2523d139b056c3b5d5df4,-0xb759a8b51ae48e1040b964dcbffa498,0x1365d2ce5cb6c552db86e162051b32f4,-0x1ca24301145e985730394328c211f430,0x25077cda66a5c17d0fc581728c3bbfe0,-0x2a178d27e95ef87b47097d6205cb1900,0x2a2725497d59f841444593a6154b1490,-0x253d2ad2ac817a9f5d33617649954520,0x1d087462f1e5cf610008a3dd2da0564d,-0x13f7b8964cfabd5bcbd88ab5391a7d26,0xc19544434e18581f945046b2f0dca8d,-0x671e49ef7b12c798aa6177935fd612c,0x3023c7523d6a7edf4f02ab871676d44,-0x139d2d6057924e5482f66f0171b96c8,0x6eff1ae0675bd08a16572a38a0b354,-0x21d9451f44d8df19e1728c686b8880,0x8d2fdbbd8a6d69219798df3530dda,-0x1f211afb63b3482876d632ae7bb7c,0x5ba0cd738c1775348def3ebe174a,-0xdd2e921e5d94fb1f9e8b8af40c8,0x1ac25db98006d99bc1e5de52904,-0x28517890f2d5a24dde614e1ae8,0x2d63e7f2edd2a43eafa7e93c4,-0x2402b827c6c2b452a57b21c0,0x126ad6caa0cb5ed0ce150ad,-0x53cd87863c88790e3f4b6,0x9ffb2b5debd9abad77d,-0x40043aa91b156bc3c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 20 37 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 37 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 44 indices rho q2 m2 2 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 44 indices rho q2 m2 2 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x14f358568a8b69a1a2676cb1000,-0x23f4a7d087bce27fc7fef0b45c00,0x1dce886a7b600146436b6677a0d00,-0xfe54cae2a1ee0700570d882756fc0,0x620a53cdcfdc8a435797ee1abbc380,-0x1d19f299185f94ea932a81f7e54ea70,0x6eb48979ce142fae0422165cc21c6e0,-0x15a71dfb2fcd15ea17c5f0f22f414bb0,0x38d01c390d4ed6c298b739646b062280,-0x7ebee953cc39163fde869af01c1a966c,0xf2f862aa3917b1c1c487393d4e741f38,-0x19372bd31b391ee51b11c5c4b5422260c,0x247d27c8d58e9712c52a7c9e3813d3360,-0x2e39ef3f2b2409dfa9777bba664977b20,0x33700edda369119602f5542aedac42680,-0x32626537199e1441089e63582672761d0,0x2b7f7a99945f66fb0af940652f0997020,-0x211bfeaf0e00f4323d1f95fdcfedf900b,0x1635559daccc57c3f0ce45148a7b44e8e,-0xd1bde67e818a05859f5f8ca643922df3,0x6cb31570ef8a76e35a32ad58bee885f8,-0x314d0247ea3027d5d74f6679067a6f5c,0x137bfc9ccba2190bffc8006b9d8e1cc8,-0x6ac37d8c1a01648e4ae1258a6e2c82c,0x1f75fd4251745793bd52146af9e0110,-0x7e83187be135b1dcec05c865f86216,0x1ad1d1d1f58ca25ab34185724e166c,-0x4baa51e8f10a2c0e5f303c59bc576,0xae6af427cf6cb75d7b8cce33aec0,-0x140f8d8a8acb9ffbf4c375c3c41c,0x1c93dee03f4b7ecaecaab702ea8,-0x1e35becd2350a07c1855a79ddc,0x164e69952ce2321b956868d90,-0xa7e356c8977642274efba6b,0x2b33cab2ebfae065daa4fe,-0x48e650c19be4d6b42b43,0x18ef5450cf67da3428]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 20 38 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 38 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 44 indices rho q3 m3 3 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 44 indices rho q3 m3 3 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x20bc3a073879d50c8dc199d49000,0x3762db18cbb67e52a10114d7cfc00,-0x2d3fbe82b8ef518895240246f1db00,0x17c5baa4cdbc62f3f038ce6342c0840,-0x9062e378b7f9d2e2fd33dc672982280,0x2a2ff414a2e20d633e40ead4c3f5d210,-0x9de765bb6047c28417290dbbaf706da0,0x1e5f8ebb1f9c5e73602fe453f2d425f50,-0x4e5600861fee2d61139deb5c1fd3e0c00,0xabb1743ca6d3b1c5b1e35f7facbcae334,-0x1432bb52db3337a4912c7faae52e626068,0x20e93bb65779d9c38960e4b9c5858105d4,-0x2eb4044614634538f58c32efcd39f04100,0x39fafebce11221c20980946240f3f1b0e0,-0x3f2d02c8206de8b694e17cae453b807880,0x3c8bbd316abf5b2777fa25807edd13b790,-0x3318a251802a3aa64835427b59192075a0,0x25fb65406ce8bf44c8be813be36a6f319d,-0x18da7a123e6f78babbffe862292b49eb5a,0xe4b5fd67685a40a408585ae491bf0ecc5,-0x73581bea80dfe3814260cb44225ec73a0,0x32d5a4a0f4431a554133b6aed6a761444,-0x137d90d63e180a16a53d054ad8ca3dfd8,0x676b3b1a38e9275a0c5e45519f712df4,-0x1d73327b9217baaf42bfee8428942b50,0x722b7447c9921f1bb47b341576971ba,-0x1744e9eec93db0cc5fd69fa11df04e4,0x3ee999b40bb18df3245643202fc37a,-0x8a726247466a5c3c85bb21371f570,0xf21c2670dda73cfe203fcc757384,-0x145e7e81c4208facd1a3b3c782f8,0x14340928fd0cb23ab2488de7de4,-0xddea667c688409467c0298010,0x5fe45d3a9ac514e103ac42bd,-0x164b7c45b46b01d2f21e46a,0x213559cbba8b5b5beaef5,-0x9b4982e1ac1fff1d70]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 20 39 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 39 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 44 indices rho q4 m4 4 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 44 indices rho q4 m4 4 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x33261aab483e5ce39d7e805c21000,-0x555955ab31bc30019055cbae349c00,0x44be3c73bc5c9e6558b8dc444fddd00,-0x239793bcbcc8ebb9b96e12ec107e53c0,0xd4f57f62f9917154d96f42fcdd61b980,-0x3d458753311902cfdd486964e7f9a5d70,0xe1ba3f875a6a36e4395f1893b714c5e60,-0x2ab75991ddac051988fdb6bf4558be4db0,0x6c54c7c28681f35d78f7b8c95ab72eb000,-0xe9590a3993e019894f26969fc2a7eb012c,0x1af6969d170bfaa64a432c6b3af697fb598,-0x2b206255e53dcb06137b7028a3af79b768c,0x3c08f234f2283c9587498de27c14820c140,-0x490f9935fa32b441f29d65b0685fd4d2d20,0x4dfa19cb2229e94c63b15e1400d9b5ce380,-0x492394fec918a5efe8acff2fc5a80e59ed0,0x3c5ab1999cd93ef4e7cbcb547496edd2920,-0x2bd32bcc18cc4d3269d5ac1e70a62284b3b,0x1bfb6939f82247cf5bc0398367a26fd3ba6,-0xfaf6a047582d65be2a8b80a519ae476793,0x7b3064064c44ea7e582d2fa2473db2a3f0,-0x34c3d40dc06216cc0ff182ee98fe2e4b9c,0x13a10abc0acd5f11f4a064e64956b095a8,-0x64de490d9e54c86b82b2ea27cf47f9f2c,0x1bc226a98875487a5bdeccd9fa9098bf0,-0x67be01a80200370813ba12a194e595f6,0x14537b26b72c618d2d190a2b5a0bd99c,-0x34a7b3b55a7b0213c5561a80a4e9c36,0x6e96b54feed5da05ecf22b4ae54c30,-0xb7b321f4a65d5e26b19f2a32eb35c,0xe9866795db2306c1e4272e1c5388,-0xd9277725e9eeae8f7965efe76dc,0x8a776eb252edd6e8b3a31e5d70,-0x36e4c1e6d30c819c29ff6d81b,0xb83e4898a0bf6fb96a00c16,-0xf1f427455b46d95834f63,0x3c66cb9b1881110e3a0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 20 40 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 40 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 44 indices rho q5 m5 5 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 44 indices rho q5 m5 5 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x4feb89aba0e17123a615a88ff39000,0x8391e4da2adc9af320ac36ebb233c00,-0x6883606fb2b5460ae3474c90d91e8b00,0x355903fea9135972a73926c416da65c40,-0x13a8fc6da0547911936c2858fe708b5e80,0x5927092ec1332279d9b59acc87e5babb10,-0x14364477fb5aa85c9ca91f0a9b182e298a0,0x3c3a70c0191e597d024c6480292cfe90650,-0x963f1a6052a6e4c548226ebefcb15377500,0x13e2c256b73f173eeee2937160cec3d45e74,-0x241f8e63dbb9440a0be63cf1404f61c3b628,0x38bbf79e05965320a4b15c282ddca0225d94,-0x4d7ff49817e32f51651a269954f0ecdcce40,0x5c7bc227eb2f3eb736eb9ffdb540316500e0,-0x60b6b5de8cd765ed46267bce706348db3a80,0x58ce841f3e2cdc35c14cc06330aa8083b090,-0x47ad45dec1511e6278392f180b0d6f0a6da0,0x32dab161ba78156fdc7c1f68914ca0ca6aed,-0x1fb0fd312c878c5cce4ff4d041a4f167d0ca,0x11512cb06ed04b90534c3abf9a71424fb135,-0x8466aa6537c6dd41247bd8c69a69b51c9f0,0x371fd6cebe8ef3ba52b65665c08dd59fd84,-0x13e640b9d58bb085898a640cc8a5d45f998,0x630a07477cca9ee85e60b44a82c95a5cb4,-0x1a56fc18219edb3df02e3ffc87cfefa190,0x5ee5a389db8c91b52112e3b42bc71735a,-0x11df364f257ed0e5e92e2e2da9095c6c4,0x2c59cd9b151b12edf55ee1c9a2b1985a,-0x58df1778dd3194eb362f4720104a810,0x8c2a05e9629cbc902dab1402eb08c4,-0xa82b5dcffe2ca04bec9b7704c46b8,0x927ee7a48b798ae355f98869d5a4,-0x56acf6a7c2188fb0dd175dc4c50,0x1f7ca703fd1c2a3ea67482050d,-0x5f39d4aa8d3bb1fc63767cda,0x6e2230e3f20e1d83fcd365,-0x177a90fb75f353ab97c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 20 41 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 41 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 44 indices rho q6 m6 6 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 44 indices rho q6 m6 6 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x7ce0071c2b6040c7b381d760ec91000,-0xcae56c12e6b28a04e9c652d18670dc00,0x9f031b814c8d36d5f7b3944700186ad00,-0x500c6285316f69a469f0f9cce87d754fc0,0x1d1505b3148d17822d8408ef2e89e2fc980,-0x81f47802d6c0545bcf30ed5be6e2db5e470,0x1d0504d53ed44b59d005adb4ff39d4f77a60,-0x5522099cbc61dd628f3cf2843d61ce968cb0,0xd0f98b5c6c6a861d56c1a131618d1493a600,-0x1b337c6d9fb403b399698d8d930846a9143ec,0x3090dd71b72da4dfb3f217d6a1201482c8e98,-0x4aec56861d8f1d017a6358aa7d41fffcf864c,0x64766a3c52a0c94558ed1e1c37476ab1d48c0,-0x7597dd8688913f087c61c9bc2812bbdd62920,0x7886695155053194ab73a55113a9bb71ed380,-0x6c60325ce0463cd48f49a335ec93aecc0e7d0,0x55939d41cbdc85e6cec6a027e0d6678e6eb20,-0x3b570a36d3950755fe1de6f72226319ebbf6b,0x2419c37a3fcf886e5ed04d7470696113508e6,-0x133bd0309629512ef9eb30e3fe24f53753d03,0x8f2ec3f9430a858a63eca19875ef8cef1dd0,-0x39f44810ed7feda85e6e577cd532f1644d5c,0x144db5c4f773f75d70706319e8d36aac89a8,-0x61e05f7a96bdbf1e741364f5da76f8f5cec,0x19281ff667d7bc4fb7907d66b1336a7a670,-0x575e351ab86d5a7c4d21d59c3575767256,0xfd05724ded4fbbf1cd9eebb274d834d1c,-0x2595d508d442d1383ea21057986c97016,0x47d5749c3455a991b80289fc7c005ef0,-0x6b84c335cea33acde22cd71b327631c,0x79adb850ef13142c81100bca138988,-0x6337e27ea306c7dc72adb12ff9f9c,0x366a93c6a27652cd8fadd26b5ff0,-0x1217cb3b4ed4f879704c1de704b,0x313e605c31b5b065b49575c56,-0x321be2bd5313b81f0998bd3,0x91ee59c5ceefae317a80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 20 42 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 42 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 44 indices rho q7 m7 7 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 44 indices rho q7 m7 7 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0x1b5f340376ce01080000,-0x29f369e6f37da9d88000,-0x1e33d75c99a3bc6b6000,-0xd95c4bb4caf3c843e00,-0x4485dfe027b0d582f00,-0x1018fdf532689d01aa0,-0x2ecbe90be6a15b3cf0,-0x6bc3ad79e600d4430,-0xc7b387368b2b3068,-0x12ccf1636a8ef7da,-0x17265e5852c1007,-0x17591040b49a0e,-0x1341e48fe4921,-0xcebed910650,-0x6fc67ddf71,-0x2ff360496,-0xff12717,-0x3f50ca,-0xaf78,-0x118]
def m8 : List ℤ := raw_ints% [0x0,-0xc31e0b1c03c66538087ae08771a29000,0x13900aa9a8e0dbb85375bbce9421057c00,-0xf21aa2e040049ee7dad4efd67ecda63b00,0x783dfbd3f58789dcfad7699c07521848040,-0x2b14c646b1d20bc8c252d2a644fb03b25680,0xbdc4e08e22257221bfaa72e32c4d69e5cc10,-0x29c103efbde2e57b7eacc4f317f54a9ea86a0,0x78a2208ca08bf7adeabb76541305835251b50,-0x12379bc765e43072ac250f906dc35dc21fd900,0x25530fb0f21596081f7adf2e86f73b1d9855b4,-0x418552893a0b2a3fbba54d0f7b2c931283dda8,0x6351729622bb617f2741073095be301023f0d4,-0x82c32f484403ac8b99ab3667ba38333d0d2f40,0x962d7ea46b3f97c36d88c40d1f5b3bf5922ce0,-0x96e6fe4cecd8618da2934b4f350ec89e602680,0x84e9ac3f8dbd6e3dea4c4e390d9866486cd190,-0x66b47aba2f95c45b583550705dba05bc5993a0,0x459ea6558bce0d06d81d34862ad3aebf05ad3d,-0x295b643e70ede6445c0a3b791c2e4bdd81c1aa,0x157ce606f5d1ab57772345af20a24e3ace7885,-0x9bc7578a67202865e749ff9ad676dd16e1830,0x3d4e5fbd7cf13a139e8e4faa813bc7170fbc4,-0x14d896428121d77c11ee8018b08906adba818,0x61571b1240c2692bdd42ca12b36015eb7bf4,-0x182dd6e34b40225553a44770728619931790,0x50f0dad5bea9873dfa209a0cdad5722f5fa,-0xe141c7ccb3a2182e5c5c7b4087921e4784,0x200a32ad69984780dd49ea07188c87ebfa,-0x3a62b2dfaff23aaa37193e30aabc69b90,0x52e593f2dbc7c4ef6f39f86e3bf3a504,-0x586f28349a0a359fbe0f29518c59b38,0x43720f41dacbbb5036fce253b543e4,-0x22416ec773cabf06a23e7b8759250,0xa69abc48f51737c0f2038b2f15d,-0x1979af5bcbdac7a0bf408c66ba,0x16c9bd9a0f9e41dbbb2a7db5,-0x38a78e28095015956a700]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 20 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 44 indices rho q8 m8 8 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 44 indices rho q8 m8 8 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x118,0x1]
def r9 : List ℤ := raw_ints% [0x1df020e3c9f15120c00000,0x2dc6dca096daa3c3c40000,0x20dec0236117986b988000,0xebd9b557f460674387000,0x4a191091769e75bef2a00,0x1156cfe44efabae44f000,0x322d7705b119f1fa8be0,0x72f1472c9526d275790,0xd3b0210c09d72fad90,0x13c8747d860133e608,0x1825281a63de015ce,0x181703e141756449,0x139a80f9792daea,0xceded9006923f,0x6d552dca0cc0,0x2d75d5eb5af,0xe70cac91a,0x355c0719,0x824a7e,0xa398]
def m9 : List ℤ := raw_ints% [0x0,0x130def15bc5e5fe278d3ffed3a18e01000,-0x1e308552d06579acc75a0206f4739891c00,0x170e086cc303fe2a195757970447a1ac7d00,-0xb4cf32f10104178b04d40f2d4fe5da5e6bc0,0x3fe89f6a9ea242bcf739c225a872ff1928180,-0x11599822d9aede6f7bad556fa85c5143eceb70,0x3c33c883af3e74afbceaad60ca36ce87cbf860,-0xab5a5ec77e1ec663033e95ffbbb203666b0fb0,0x197ab9a55ced58868ea0f32ac7971225c4e2e00,-0x335fa65fa2bc2f834e57d4a5e66b421b392e2ac,0x58b23d94f904d8e8cc28783a02a43908ccf1618,-0x84256296bb32b238941f950898c3153a0b1870c,0xaae2c2d7143d64ca73808333a6bb543234302c0,-0xc09e7d6a0ec963a6067fec7cd58938565604d20,0xbdcdf65f8a1ad18889c998ef26796fef6fa8f80,-0xa3cc5168e8ea056990c0a645ba6a342a90350d0,0x7be46de30f6b0640b7c3db0236231aaa38a7120,-0x521e01e10906d002346bffced820cd220b37e9b,0x2fa468e9b1ab32f28e21e7506bc179f3b3f87c6,-0x1824f564587b2d40d646c6702e2f348a92e36b3,0xaa7c015e963b89eb56d1c059f7a6d15e51b250,-0x413e5015ffd30c68d6414777e69f2390a4011c,0x1588ba849333889bd926f51db9902bc605ee28,-0x61676439e9a4b4b7b1f44764b6f364931b9ac,0x1761e36574887916a1276dacc50e52fe25b70,-0x4b7130fb56741d590cfdd5df208ff7c28eb6,0xc9ba27a633a40e8efe032e77c1e862b93dc,-0x1b77bbbf52bbaf1d3c969ca752675dfa276,0x2fb5319c50f22635541c288df519925cf0,-0x403922c678367587594febf75d844f0dc,0x408b35eee9497da323f77178b3194808,-0x2e011c07309cd7ce65fd27091aafb5c,0x159e0458619150fd868a91bc3c88f0,-0x6003ba1464eea3001ee167b4c97b,0xd2ed68844e0b9965bcd0e05236,-0xa5bb782216756113aa581e83,0x15fb5c61c2b24964001a00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 20 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 44 indices rho q9 m9 9 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 44 indices rho q9 m9 9 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0xa398,-0x118,0x1]
def r10 : List ℤ := raw_ints% [-0x117ddea516b3b4f8b4c00000,-0x1ab0f4d40a5fa470914c0000,-0x131f2a0b34379f8c7a1d0000,-0x88d8e6feda803fbb6665000,-0x2ade13534e68c889e107800,-0x9ff5f795737eb9f8948500,-0x1cd23176adfa0137b40e80,-0x41babc3342c17885080a0,-0x786ecd3d39acb44f9e30,-0xb2ff74093d6758349e0,-0xd8ea59268c431c3920,-0xd693fb933cf997182,-0xaccf3695404a852f,-0x7083c4a34439a76,-0x3a7fd36b9d47d1,-0x17cf233cda660,-0x758c9f4e501,-0x1a0cbaea16,-0x3bc1fbaf,-0x43cf92]
def m10 : List ℤ := raw_ints% [0x0,-0x1dc5c591f65375d1dccb3fe2aac6de19000,0x2e9aff4ffa67c1a91ee7b60921749e63bc00,-0x2326ca5fb29aa1518e658ab92688a67f8eb00,0x1102b2b9670bee7c93caabcf65e70a917b2440,-0x5eefc8b1d94131c0c241b774946a54da0d3e80,0x196c80a353239c8b531dadeb9ebdbf7e9fd4d10,-0x56fb06db93857c3385a09307ad93af80d8540a0,0xf3fad46ce3c179d5291301921521272d2b03850,-0x23bbc39c7d2acb37b033f5df134e1fe32c57c900,0x46ed045bb131b510cadabf735c8014477534e0f4,-0x7878b7fb0699751872d4a1d660b6ae74bffc1c28,0xb077b306e5648b20cbfe84702ec81a7855624614,-0xe0341767ac9afa706454bc1a9c629a5475922740,0xf81a20823cc919727283cc73ca91ccddafe208e0,-0xefd02614370509c85eb2ddbb1c449e7782257a80,0xcad2e8c68f26815676dea78c6c2d7085331fc290,-0x96334110b36e6a510fe2837677e182e2c9b491a0,0x615dae7fcff3630fdd4e0d0ea7ae4b92105e748d,-0x372e7cd54df94aa5ee4c67f448aa5d5c3205b44a,0x1b482acfbbb023c5312fcd007ff375bff118f855,-0xbba7f9167d988381588a5d3b885827471fd0830,0x45d7bc66094dc5a869b84de7a2c91f50e020204,-0x1660aea6494ee67bdd1d3715e3d9c0f6ab84998,0x620d69a66ae66f330f2d3e0f5cafd534a71134,-0x16bf403bba86f72c0fcce0991279d6fd112490,0x46bb2012910ef25db2c7ba5a3222100723e9a,-0xb5b04d1ea66fca0b360143e0ed92291d5bc4,0x17ad3a79e7455219e71f98e977ad691e849a,-0x272e79feedccc512b7b246ef5add8ad2690,0x31fc3a8f4d0abcc2db9da0d484eb75b144,-0x2f4b5e9ee83b23d2959a4c7b0d92f72b8,0x1f7aa63b4356f2a1b9d22a5671305024,-0xdac150aec0809e36acb6bef6671750,0x37662a383c849384b7052bb1ca6ad,-0x6d2ba17f4d56e92dccbbc44fa5a,0x4b4ba5ee0c16dce69f638bc85,-0x88629b105846d25132bc00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 20 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 44 indices rho q10 m10 10 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 44 indices rho q10 m10 10 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x43cf92,0xa398,-0x118,0x1]
def r11 : List ℤ := raw_ints% [0x7401c34428ef4996a0e900000,0xb0b3a9840c7c938b1b8390000,0x7e55d8d1cde85b065d690c000,0x386172c778378a4ef31705c00,0x119dc0050b76b641080e57e00,0x418b9c772fc91a5838061740,0xbc5599843710227c68a4be0,0x1abe73fe5ad3175228fa4e0,0x30ca3caeca77d96dad32b0,0x48272cfd8b79a89b10224,0x56ed0773fa5536c4579e,0x556533cb8930906949c,0x443481982a209e8bf8,0x2bf6a1a99d794d259,0x1693584e8f9b1056,0x90b99256fc1907,0x2bc27244bcd64,0x96fcc00fb23,0x14d69476a0,0x165b5f1d]
def m11 : List ℤ := raw_ints% [0x0,0x2e8504b410e26817e8fd93d22ad6bb071000,-0x47f8f56ad66febe8fb6aa8bba986377bd5c00,0x35a1cfb4f49adf6702411efe2a2b2f5c3f4d00,-0x19a1c35907da417f293d5c4f3ca4353c584c7c0,0x8d3898c76375308990cd6149f46f0b6b6565980,-0x25516f2773db493fcbceb329304b021afacaa270,0x7decb7fb13d7d10fe5f505340b05ea3c45529e60,-0x15c34bf7c4e3f9e744b11a39259fd67bc1ca412b0,0x323f8563e61126a1c7851d55952426a059d4ebe00,-0x62363c5b24e1e43e177d038ae6e76717721b12d6c,0xa42b5806c5977dfd049f385597e455ebd4c88bf98,-0xec8052edcbc6cd97c7ce41ee733783ea46dbb47cc,0x1274c90529ebea5add192447b058a2c35d2346f6c0,-0x140e5a0be7ced2b6a48fbf7a3277352aa7ced85120,0x1305708aa6091429c84c29864d4487e5dbffa43b80,-0xfc52f11522545588e35e8692da59cfbe51ae669d0,0xb6fd90f937b7a43846a2a10440b3e81f1ca1ca720,-0x740a1e78badbf765f683ad688ebb98c8eae1400cb,0x40414a95fafe6f665e80de4b449326bccf0d5b726,-0x1eff3425f7d306c1eb33a2918805a6219d6e3e863,0xcfb9582d41b3e7c6cb8de22c805507980ef64d50,-0x4b324d23cd4f521c0f24f26d459f5d92c96248dc,0x1763bfcd2dff2f3a6b0005df21a5daaa3b944ca8,-0x63481efd2fd6780f815b29f5bf66f69de368e6c,0x1641e9fcba4966e6e61e12013839d437062da70,-0x42b12eb9f800bdc24a0e525e889e118bdab916,0xa48b659c4d14780b8692f2ed82fab668a4b9c,-0x14841d1e97cf2ecee67e9487d7c5aabb14cd6,0x20560296c7d83e30b1f238046518b34f8ff0,-0x2712ef8e3549d6231d16f40a934c2da629c,0x22c8c8435bd8806615df3e0101f53a0088,-0x159a7a7b3829967b86a35a50b13f6ef1c,0x8aa28d2969374957f0eb52d761b2bf0,-0x1fff454282885049604d034d2a1dab,0x388249799fa76676659f01b9f896,-0x2230d4e0b64405b037ad29c133,0x34db9ed048f7cf6e6a32800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 20 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 44 indices rho q11 m11 11 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 44 indices rho q11 m11 11 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r12 : List ℤ := raw_ints% [-0x263f37b37871ccbf59015e80000,-0x3a2a41a5ea27ed498cf06768000,-0x29830ed93a8aa1d26319890e000,-0x127d2d398073da4e73f216c4600,-0x5c394d681dda1c9f57bffdf700,-0x15646f06c8534733b48c6ee620,-0x3d4ae495e71e10754343cdff0,-0x8acf1e7726ca790164543d90,-0xfc4cd62192f8be0cd436ee8,-0x1738857d97fef1388fcc702,-0x1bd682bff524c4c66286e7,-0x1b30fb394c06408e68758,-0x1592404764a6db765d05,-0xdcae9385d64a009d9c,-0x70389ef0df71722c5,-0x2c6d31452e459406,-0xd3b5632590afc3,-0x2cc69746beb56,-0x605a3d42f34,-0x63c10b67e]
def m12 : List ℤ := raw_ints% [0x0,-0x48afd7595a61c2a55c0c36f862ef843b09000,0x6f2f2933bdd394952187921950c1b6b17dfc00,-0x51e23ed525e0badb30e6cd3afeb9d01c3c69b00,0x26a96462daba93ed80e0757bd6d9df0ba07b0840,-0xd25a1add1955150af24924904c98167241c66680,0x36de4aa76449d80b3da6dd5a9fb85aeddb3ae5e10,-0xb6ab258cd91fd94c04e962964f6f58964e6f9caa0,0x1f21b195147a07673f3bdad19ff54fcbfe448a8550,-0x46d81a9604c1f6863317018ee510e5987fc9416900,0x8864f0e52940406a3e374e7da818481adc7899a034,-0xe070fedb137aa1e72f1b381ae10d604e1c1233dea8,0x13e13c753979ef97ef910763dbb50883e7cd063e754,-0x1866c4d05f979b48d229df06a4025edd4fc2285db40,0x1a0bf533592d23c95ec385e5edc32fdfddb1fb164e0,-0x183e8be1c0e881a3974b7a8f253da39b4f4b114ae80,0x13b5900fba2ee8562b2803b6a4313067b639847a390,-0xe003e83ea8796c670d692826fb29430283dd6d0fa0,0x8afdbb378ffacbb2b60e8cc6775cf269cd3cdd40dd,-0x4b3622cf6bb8cf90029b7320c1fe4c45f02b6ac7ea,0x236854b513fb9628db04704124d7e3f17100a2c325,-0xe7352786f8bc77990f5bed1aedc157c4c58c37730,0x516a6719aafbfe3307d92a66452013152fdf0bc44,-0x18960f12734df0757908d82d79e23ace9db754f18,0x6519156a536c5c870a55fac0138accc2352a4274,-0x15e6b49d284322092c6b8dcf676cbc98816d7d90,0x3f3b32a1549849dab15630bfa2355391dc8e13a,-0x95d004f66290af61b96ae4857dfe892cffa204,0x11ddfb87c649a8ca44aed4d115510c1a96133a,-0x1acf8d7037a1d99c4f47d3e68ce3872f56f90,0x1eabd4036f2bcf751011cbdf17ba69fff184,-0x19ac46a0e67bc51498433006cafd4b8ce38,0xeddc788098343c3d2e42e228dd4f86864,-0x5804ef5e6eef5158865eb75ac1fb4850,0x127f31e5c0c268da845caae7adad0fd,-0x1d4029afaa001d971aa94c35c1efa,0xf847eef77d7cb609ca3ffc6655,-0x14798f31e91f568e56277000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 20 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 44 indices rho q12 m12 12 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 44 indices rho q12 m12 12 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r13 : List ℤ := raw_ints% [0xaaa751bc00b9cb78dea031f00000,0x1032851def003dab794916da70000,0xb8aa87501d9fbae29ef20ca2c000,0x521a689d93b49ad367e01499a400,0x198b9ebb6dc0ea0667551164dc00,0x5e994777b493081b699315ce3c0,0x10e5ddff9fa4c418421cacbb800,0x2629411fb0e11866d803c4cfb0,0x452412a1544bccf4335d785a0,0x65721dbbbdd5eaf1deef8a64,0x791c31979d7c9f0a6a145f0,0x75ba44c94a7c79a604ee3d,0x5cdf1391295bc14fc0e7e,0x3afd74cf5a74a6cd9db3,0x1dc323ae42f38e18ef8,0xbabc15d670f937523,0x36f8aa8f79c6e156,0xb7537a45834439,0x18330cdf35624,0x1871868cd60]
def m13 : List ℤ := raw_ints% [0x0,0x7192c07b9d38c0225fd315e41a963e9c3e1000,-0xabd0eefc0ec1a61ea96d33f5b1fead7554d9c00,0x7d19b35cd7907843ba1a6755a81e38f4830f1d00,-0x3a5f74a01e24c1b5addf5b0cbaca396af479ce3c0,0x139bc84f59ff0410752e6a609ea9ccd95adb863180,-0x50cdecdf95f8c6ca5d7a9eaf144d9b83d68980c970,0x1098038f633a91e9caf19030af957d4da847eafc460,-0x2ca27b10339fa8a6e19a48fd7017817d1453a3a05b0,0x6423d7fcc5bcb5568b089bf0fa9edef310b32646e00,-0xbdf7aebee3701cf7c34a979173d97d870c8e67b242c,0x133d138e2bb694ac159b22d2224b05e96815dadb6918,-0x1ad4663d1cd8d1ec9833f27db146555a009b5c39e48c,0x2061f969c11ddecba0b217d2219e4fb5ccc04e6d52c0,-0x21f66a078592ce07dc870dbf1dae1c2e21b425441520,0x1f0897e94b538f9645d29769cce27e8a5c8e87336780,-0x18be40be6638ac95853470e856230b3cc0d9aee872d0,0x113892e7eab25e22ef7512bc034b2a075c2e55093d20,-0xa74dfd0969a4f34b57dff6f65511fbc1b1db70b95fb,0x587ca6f083de35ade294fed020bde4d4aa5a591b686,-0x28a8c0843ff01e96eb320135d83f8c742019f015913,0x102bc648f16e2856d9f1cdf3af20edb8a6f21334250,-0x58a20cb2ca2024a4b6f88a500a5c71d983f0192c9c,0x19fcaa909562a1e4f08988a12798b2d7597adc9b28,-0x6784694bcfe66fe2c49199bc9852fc003c118df2c,0x15ab2a4a9b07d34b594c54692cec369fe66487170,-0x3c454a36e28f34d87c2cb4ab36d440164aa34976,0x8919f5d4442bae4ec234ecbd11886738ec9b35c,-0xfa2ba16b14ad2d96a72d5fddab0b4d9af40536,0x165419e16ca7aa5a4dd815af9ab0b7530fa6f0,-0x182b88cb93b1b89ca00c43c002848408dd05c,0x1302ab8e5e0dd6e2f373d978306e04c3c908,-0xa4181eb3c381dcd2534bd816c033892edc,0x37f98d90fe3acc14741193368209b26f0,-0xab3520f67c2429e02ab9708b51b84db,0xf23e14a1086d484646f60c4af1ef6,-0x709fdb43868b52d9f1bdc6e52e3,0x7ed4d45a42271f4d44bfa000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 20 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 44 indices rho q13 m13 13 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 44 indices rho q13 m13 13 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r14 : List ℤ := raw_ints% [-0x29d10492cd69896e70af53cb000000,-0x3f6c1f6c7a37f0f8c2dd75ddc00000,-0x2d20e6d60abbfc9b386356367d0000,-0x1408608cf184010a9a23c3ba9a8000,-0x638d5affdc410f957892fa21afc00,-0x16fefae4a956cc0bacce412f74000,-0x419452bfec97cc969c70a2262640,-0x93bc466bc4a8e1493450d484a00,-0x10aecfcfa6f5fac7ffb2c709f50,-0x18668e6dbb082791a05ccefe20,-0x1d06ad502b905bbf98c646b3c,-0x1c197ea1cb4691c84b396950,-0x160fd5db06ec66470eca2a3,-0xdefa20b437c7de0672302,-0x6fc5602898839e2a148d,-0x2b7e38402686c4d3188,-0xcaf6d242bd1fba39d,-0x29d3aa9b1fdfe96a,-0x5718fb79b683e7,-0x5666c0f55c1c]
def m14 : List ℤ := raw_ints% [0x0,-0xb1754cc125a8ac35b5b9d234698ac1d420f9000,0x109995352a84928806048b0b51bd5ef0754943c00,-0xbf400b8d099eda50a3aa356bc932fc6e1d7bf4b00,0x5838234b8dc1b6256f1b7c0374261eb25858432c40,-0x1d48990e49ea93b198c3f94808f187deba97ee50e80,0x77311f29897fbebdd53b8b39dc09af3c0fe5c667f10,-0x182a2d58a3bacf35e3448fadb8095af090791c4db4a0,0x40232e73329ad8c4ae87e0a2d83782eab6b386a8a250,-0x8de8ccf0dead339ad5d14574f7edcbefdce56ec8c900,0x1095541449ab6572ec20e3add0e285ebcd4fddc5f5374,-0x1a77c2048d4d7795548c881569f7d4d79a9997c55b928,0x245521a105f46dd968055ccdf377e78ffcfa96435fc94,-0x2b21f83058ae6090d0b457e4de8e4ef8a117bb02e3f40,0x2c756eca0009d448672af12d2786950ca6fc4a4ab80e0,-0x27e3fddc79e67e740de189365e415484467ae6425a280,0x1f334c1d0959c5eeebf32f3505475a73116970949f490,-0x1547ad922bf0ac869fcbd962778f49184372ed9f3ada0,0xca5c74ae6f124d2bfb7899c295f73faf389d7669222d,-0x68a0c3f85b6c28e53ba7355d957440fa7e93ee52718a,0x2eee521e132d4957be1358c07415e44d51e0b2b4e2f5,-0x123123b2d8fdad281675e0452a976925144cef91f230,0x6101f258b9788c89b22a4e6cd88992f4d0129cb9a84,-0x1b9dad4ececc1d160acbfef6288e760e54e4912dc98,0x6a90c2e84ee8af0d2403b544207fac9f90549727b4,-0x158d71a85217baad2440bcb79edbdcea5b2d1a5690,0x39bf0e330962c94f6847a55c00dfa4da9db42cdda,-0x7e177102efe2e73faa00a4001254186d05f38444,0xdbf20c48fbbf49b8df5b0041b7200cfd8345bda,-0x12acb132fa296a4e162cd8897941f5e98bac090,0x131e2525354dc6ee23c680426395efabaa35c4,-0xe1ec409e8aee56bd48f641ac976f0c8711b8,0x717738717498211a39b1095b40aa80ac4a4,-0x23a6098b328a2267950269f3c9dccf3950,0x631ab2adcf7e46bfc40278f2d441b04d,-0x7d5ef97bb91c06edf668aabf14699a,0x330fd3397869f313075d3eb21525,-0x31143654626991fb5167fc000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 20 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 44 indices rho q14 m14 14 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 44 indices rho q14 m14 14 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r15 : List ℤ := raw_ints% [0x93cf80986431ff33c30038efce00000,0xdfecb29f97d72ead43c07a716ae0000,0x9f21da552087e82d8a0e2ec347e8000,0x468a319d11dc002936fc6a34441c800,0x15dff429c63bf2820c4fd2266eea400,0x50b4e0cbaf2a8d5211bc6fb5596d80,0xe5b59205868079a9923f7ae99aa40,0x2045b84c1e32fcc230e5ce5be8f00,0x3a2ab313824513319ec9045e6160,0x54d77ee52ea65c7d2c28fe6d488,0x649c5875e1d5705f3689f56da4,0x610dfb660e507a9e290ec0ecc,0x4be45a33675ea7e00ea147fc,0x2fb742fc18977c1b320634d,0x17c9ea18d9516dd005c6e6,0x932af4c455f9f986b0c3,0x2a998dd06de4482c170,0x8b31525bc029b329b,0x11ea6402c7af86ea,0x1187722f670601]
def m15 : List ℤ := raw_ints% [0x0,0x1154747edcad78d13ebf25871e4e8cedb73851000,-0x19ab3df0e60ca2eb149c6ab62cc12457b74279dc00,0x1249093ac7930e0a578476bbd7376955d2614ebed00,-0x857420953e388ac0c02045bee7b13fe51f6e154bfc0,0x2bc9b46dbb8f3895a13abbb298691048f2b0d3a98980,-0xb01802942ffb8f9661baf4ca893a94dca7d9ded96070,0x2341a371c57c36a6be73ff5e7a3162663a17d9e07ca60,-0x5c5d1bc5e84c140c230a7a5946471d8ba1fa5adb7a8b0,0xc99a1ae6d6783aa5a6dd27504db3429dadd307f089e00,-0x173a13264cb2456096775013cafe6218fe0af74a5c86ec,0x248679b4dfecbb9c75b7fa88172581f174dea8421a4a98,-0x315dacc975cd58ac1fa68f37a11f47d52449a8066c0d4c,0x39a8b52e49284f48a859a635c73cd08e7e776712b10ec0,-0x3a6c92e7b9b9667f0c380b86afaeeb84dc78bdf69d1920,0x337c8c696d7bdf5d4d9e1811c5ce0394577124cf625380,-0x278382492a8b005ef1f76edb15ebea1318f219416d6bd0,0x1a6a62302aca0c66f2c2db931a4e1e7956a1a63604f320,-0xf5ed05f097672983fc3dd62336962019906c0d8d7ee2b,0x7c5260be95ddb3a1192b16ac3eb8f5543d847abe673e6,-0x3671b3b9cac12e8492698ae88924de01524c2357eb4c3,0x14923c212c6bf63018fdebd92565ff20557c7cd6cef50,-0x6abad10f1ddf7eef6da654d817a5327dbcb2ab108c5c,0x1d806705f1c2f4126fa73baaee193d71669d69fe71a8,-0x6e476908934390dddbbeb20ee4ad5b31e180181fbec,0x158c39f382fd3506e67a4b134d88342a6b26ee79870,-0x379aee526fba42e28561866c5a4b5da909daa97fd6,0x7485650f965432a5c59c82ba93b5cef105cfea71c,-0xc23c873639135bd7cecc20cb3dc1a32dd1c04396,0xfae8b4a338c3d3e6bce6c0ef101397860097df0,-0xf2cb9dfdc544cb1ec78d6f27c8da3630455a1c,0xa849b21754ca993ac7d94f56e57e6cb46b988,-0x4e9fbf4784fd599cab710ef1cfb2beccca9c,0x16bba5f4e5a7b705f103b570e50ca9731f0,-0x3965415a363dbb4f61e088c54e56acf0b,0x40dfded08acd4f4c2ab433870f67356,-0x1723758b3ecc861946a66b9db5f93,0x12fb845af780b40e3b456a8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 20 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 44 indices rho q15 m15 15 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 44 indices rho q15 m15 15 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r16 : List ℤ := raw_ints% [-0x1dfcdde1f5f5e829b956f2d0c31080000,-0x2d61f234f2ab1bb02ef12f7853ff88000,-0x2036d513ba2becf33f6a3ae3ac9fd6000,-0xe42ffcbf1d252fda2419c1c51379be00,-0x46a9ad5a29f34bd1e6a09b43c3306700,-0x1044d4527088aeff1432201d19e136a0,-0x2e398005bf46536153d1604a3ff6f70,-0x67b4d34a5933baa3182c22405cb9f0,-0xba8393517a81991e512b03a671168,-0x10f63ca90ade77aac1b347eb5b27a,-0x140f4541843ae1664af61c881dbf,-0x134a81d644967893bdd0023c14a,-0xf082889aca4fe95e49dcf3089,-0x969c9a503c43cd17d13bc7a8,-0x4abddce82b1bcf54e9049e9,-0x1cbea464051b44ed673c26,-0x844bce25ce9eda279b0f,-0x1ad11d074814e35a712,-0x36bc56360c6c09068,-0x34fa0429f11be4c]
def m16 : List ℤ := raw_ints% [0x0,-0x1b13f60638cf0cc6f20aaaa31f5abc336e47fe9000,0x27b477fd24dffb81210460eb617ba8c90e57de67c00,-0x1bfd4a167f9b98d52cbaa1b987c307e1c1e05592fb00,0xca12200e1d23a0aba6c044c3dbcec3f419eff7c39040,-0x418ecc4621a96cbc7eaecbda11adfe1b0c38f17a63680,0x104905d5a3eceef1b580b35a332c4404137c023718b010,-0x3388d18768a0acedc81f3eb69a37bbc80891a8d7e73ea0,0x854c5ddb570cfb972c99d40f12d1830e6ff48355420f50,-0x11f1a9e55288fcdaf10f5c7f5362c25ec0036d06d1c2900,0x209eee6ed3e7cd12d0d1a47c15f88c91c0d8a0669833ab4,-0x328e74b642e845ae0f035c7faab29f7c4cb03920c29fba8,0x434b9120456e6fd6c6b664acfef886d1e953e921d3c65d4,-0x4d59ea64df295b3773b4a93e4e0f8e2c0c2517e4da0a340,0x4d117d7362aa320a80ae5dc2e9182258fbdc5e8d12f5ce0,-0x42b8d0a04a1a7d37f06d4a23c4b33e80088da6b420fd680,0x324170777860fc8823d5d48ef6b3ea7791806ef1c87b590,-0x20efeb39d73166b3d5e6242dce7c2fe1554e5b6db60eba0,0x12c42fba81666233b98db99481eacb38cc445eabbfa687d,-0x946f4209197f3506cc50a80761883780125005efba052a,0x3f791bcce2d41e77fd83a03c6184e9c56ec817ee5acfc5,-0x176119b83b7c64bfe487e1324cbaacac8bce300eef0d30,0x760705428ff486f2765fc5559870d548aa24bc06b9cc4,-0x1fad8d04efc0b874ab80abfba8ccbf9d8093e1fc88218,0x72b4650a5f5708aa082d57986801759d2c2e535b60f4,-0x15a6abef9589abde67f99c96af4df7a53196d4a2ff90,0x35cdaf9ff0584f3099b65cd705c86c2d16c2ec7e47a,-0x6c2c8d95c0cc61cd69e83b051b476bf93d0d80aa84,0xac448af1e39b6bf7ae5ef61b0e46692e0b30e0e7a,-0xd382e182a312b1ac896faa52c50aa7d0b8a80190,0xc15bc91312ddf19ea350bb61a4103558a16fe04,-0x7db105af33a91a8d9ace102d50ff9a738ccd38,0x3696349441e39504ab44b61c239c35bca84e4,-0xe83734d88426d6126e154e5cfa1e371ba50,0x2140ded9e2af8e883efbdde60f1842549d,-0x21902b3a32db7a63233bc0d0cd38ae3a,0xa7ad2a3e79c7124f714e99fa080f5,-0x756a72d7f6951208f765470000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 20 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 44 indices rho q16 m16 16 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 44 indices rho q16 m16 16 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r17 : List ℤ := raw_ints% [0x5aa11fb785adb42f1c1d9633743e600000,0x8906d09202fa3f57af157f1f316a3e0000,0x612a4eaaccda97e006f0071eafc1280000,0x2af799ba79d37d4adfc4f247ff71490800,0xd49ed56bb53637fa0efb814b674963600,0x30e22937ca84fe97fb434f310befa4080,0x8aad1f5b3cf07647b206abe4a05f00a0,0x13696614865a0712d048aae50fbc6ed0,0x22d832d3ffe8b8ec718ff17ed4ad4f0,0x32979e6e38dca9c2ed658c5f784f50,0x3bb0337e6cef9525ed8e8cdcb749a,0x393f0542353244fffe88fe2c84e9,0x2c788f94071e5fbb0d0fe11b9f2,0x1bc08551bf232c6916bb150c27,0xdb7b1e6320097a2433438860,0x540689037be273ff44e25a7,0x180af2a5cede43be511232,0x4d7eee46a9be21f25789,0x9d05ec7c41d3921fd2,0x96a6ad4bd8bbdfa0]
def m17 : List ℤ := raw_ints% [0x0,0x2a4f3069b8c383f6da30aa9ee0fdc6105c507dc1000,-0x3d6f564aa5c054647cceceb5e1a607ba26694b821c00,0x2adeac9060b1bf300fd7ca156c64b855821870da5bd00,-0x1323fd3e0eab3ba9c0532b29a78449b60ba5318bd05bc0,0x6245513823eb11f334df77a510bf0c75dc834b44666180,-0x18223cbf61bd9bfd965c54ca1de168e6567f53541276770,0x4b77120ee36fb2b011ac0d6ba69c171f6d2e911986e3060,-0xc0c7ecb5082218dbc1223f4ff9e55ef9d335644cf36fbb0,0x199d99d5c2d2be68b885aa5de4c86f719f44b4d8eba4ce00,-0x2defe5602544107a3a955bf0d787800c4c81f9f7935815ac,0x462f530ce361cfae4a5cc2d1b2296f439b4b16cfe1dec418,-0x5c0849d04fb3e96b2094f30f232162c872a48e805208420c,0x68217bd077948300c7adfb39861c76d4f584c21605ab0ac0,-0x660abcbc0d8bbf2cc18074e111e29032cb61fa9bbc775d20,0x56cf1430dd1b28a5eefcf5af9918301ef844796ebaa9ff80,-0x402f7c40f7d8430084ed83cd3a59f38b7fb30ce99dfc54d0,0x293fcab9ff457cbbb41251544d091a856413913d6060c920,-0x170472ad03795defbe9852e20f98fc281298571254ef395b,0xb20fcf762f7fcb4188a522ac72b8a811912e6940ea7c746,-0x4a5bc6631e380bdc9a68a5e09ced152569d3b3107ee1b73,0x1ab3bf72f03c8a299e5c8340d5e32b494b5d4895d840c50,-0x832c8b35b65640b8217a3db1cfbcf3ab3315504d28a81c,0x222f75d1fbaec0c68b4734713187961b6df24664a1b028,-0x77e6b8af39ea82823e2057c33f5a1f242e780d19ae4ac,0x15dc5ec015e4a6c2314d128c2f70de90430fb72e62f70,-0x344e04f96269f5d69abaf407a9835894db26b0ef3c36,0x64df29e1a66b5a2841c604b285134a40c31c421d6dc,-0x99695dbc5b308c498b23ec682fd447facbf84dc7f6,0xb2f44f12ee49ae182892b4c31dd1ad378542404f0,-0x9a78483917ba7d914c4a6f245071134422a23fdc,0x5e1c585b75dde4066946adf428b54c4b662b208,-0x25f71f28b7456670c1a014cc45db9ac082c25c,0x94678566247d5f24661c20238f9d47022cf0,-0x1345a38263e407084aad97a00f56fdcac3b,0x115c2530fcb7658d42ba31b4d55f5cdb6,-0x4be798ab4d92a9794c4f0dc2598743,0x2d5f11a421cc081612ed1da0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 20 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 44 indices rho q17 m17 17 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 44 indices rho q17 m17 17 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r18 : List ℤ := raw_ints% [-0x101b9abd3412bcd354d1d559347e9d000000,-0x18554f2a334d1b508a6735e3af2f00700000,-0x113d036f515a2a3ee4c49320e3b5017e0000,-0x79d6f46e1e918736ec8588a67768d80c000,-0x25a394c3a08471f9ba8dbb6619b0bc55800,-0x8a481129564c61b7edcc6ea3c6678bce00,-0x187bcfe0440a7dfb2019f647029770e580,-0x36bfff855fcbfd1abc865d20c45616d60,-0x621bd0be999a06fe75c5ea48a6646a30,-0x8e2cfe197fdf14efd87df4a3234f950,-0xa7613edd3cfb714b36050a2307b610,-0xa025fdca867567181b2b8d184b226,-0x7c1355bb0850223615324bfc5b37,-0x4d31df65339e92bc91ec034e88e,-0x26068fb6c69cc80b57bba4bf99,-0xe802780e7cb7a75cbda4d320,-0x42166e3cd65315d736bab99,-0xd3e8266c6ba5fddd3fd0e,-0x1aac137eceff4ddee757,-0x1967e95d969feeabee]
def m18 : List ℤ := raw_ints% [0x0,-0x421bbba530b17e31b4ec0a983f8c8579903dc47d9000,0x5f15ff0b4d300cfd18d715e55692a412dc0485fb4bc00,-0x41b3635475aa23200667ce65a980bbb873d27259f1ab00,0x1d08e0eb43466451317e2d309ba4bb3b5fc1d0b39d03440,-0x937bca5560fc9acfa4028b91e79d1931d450279c465de80,0x23d16cfb627ac2062e5c6af9d032c1baa5649459d9edf110,-0x6eb4955b556bf0ae718017b468eaa16661fc742ab91968a0,0x117627b69181805940c23e9588ca060f199e86364a40dcc50,-0x24a73d8e53d7187e6938d7c8f4d4c997d1e9602b6588c8900,0x40dc14281305600af28b86cf0e12d6beaac401524c2e895f4,-0x61b794fa5d72a9f464cb083c77f2156d8ec6cba6ef3386628,0x7e430696c8eed7ed7435723b2742dc99786021a7815d2e314,-0x8ca96865865aa00871dab69d49f526cdd217c142bfeac4740,0x879a8eae9d5352ce838549935746daee653706139f2e2f8e0,-0x7162276a9e0b03b14ab5c7c49852ba735be60422dd6014a80,0x5250463a2844907067c072d4a8abfed4f985f724c4297e690,-0x33e1a29d390fd1265777bc90a7948eb620bd88324ac7cc9a0,0x1c5ba18482c9d4d2665ee33da1de2fe044eb37aedc81763cd,-0xd6979a3d012c214d8b6636b0749d82643d507575fb3172ca,0x578660c42a63c38b95455d1f4c3ef7a80999591f12fef995,-0x1ea51934ec1e65942e0d023bce20f7bb7f6bee1e1dbd9830,0x927f6eca07854330b58cf9039af22aa0886f2463e5e0304,-0x2512618b96d5a7acd23ba22535abe71077a7647c9f1ff98,0x7df0a68a4147c90ab11b5ec5fa8a4d173c93919f45ae34,-0x162d500b96b59e1fcf8a446cd491f51ca0b03e6ebfb890,0x33143c30d4774485e061aa7a1a68ee50a7fd1e67bc51a,-0x5e772e7491cc9a63207fa79521fd74f886be556df4c4,0x89283fceed88b33185d4b74aa7bfd4fb1ee99bc0b1a,-0x97eff8f78d1c0042a86cac1d31698954b71910d290,0x7bc4307fe99c238772ad01d62e8ea430fb7598a44,-0x46a0ba301c816977c01a9686fbb190245553c0b8,0x1a72943d89566f30f8b8532ba29d6835f716924,-0x5eed2e9fe142b76f21f1c764fe1d54be10b50,0xb2bf0ecb7abc02da06e6e2786115a900ded,-0x8fa0a10f5abf1097ed60eadd926e3dcda,0x22580112e4356c2388a00caba4e19c5,-0x118643124ad33d690eee993c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 20 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 44 indices rho q18 m18 18 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 44 indices rho q18 m18 18 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r19 : List ℤ := raw_ints% [0x2b76855ec06d98014279f946cfba54d700000,0x419b0ea4dfeac450dad0afaae798fe7c70000,0x2e6fd1cc0ad44315178e72ddda25924834000,0x147e6d749fccc0ba9f09b7ebc2e153adda400,0x6530c3c6ea8443cb681712b2d00673dff200,0x17355f2fda41b445508d451bc409363c48c0,0x41aa06476b175824d9576d80cb7441b2920,0x92a1cea2da2e9760617ee5e632c6108f20,0x10659782cc552dadca8384abc68ecb0b50,0x17b895a7d053d0e2fbed530e8bcc0a07c,0x1bdf7c2de8c3a07c85cea0b57c3fa5b2,0x1a9cb75976ac989f098d4cf2f8f4d34,0x1491a653f1d03d282b2bd0c061d1e0,0xcc3591b02cb2c21a025a7f83eb41,0x644a33cbd37ff5938d33fb9f9a6,0x261d32f3f1c07730017156298f,0xad088985489d8f4ed2ff881c,0x22859c8dccfd255d9232b43,0x452a22aaa82f806d794bc,0x417c11885665d254add]
def m19 : List ℤ := raw_ints% [0x0,0x674b55321c15552daab0d08de34b908df160830431000,-0x93366ad3a7e861fb978dfe941043f45d77c71158a65c00,0x64bfeef6e21c3fb519252e62886e6b434c42719360c8d00,-0x2c14fdaedcf975f0e8002604c5e61a8dbac82631100bb7c0,0xdd99d777a172331f83ac2614cb8821a5caba38bc0c8cb980,-0x353cb0745e97697a840abf8acb997e7e9fa0bf67ecc71de70,0xa2af9f6fb8d1973bc5abd19b0a1104e1e44e4c3bde3eef660,-0x195b77c960e35c8e1270b4d827e07f17dc0f2bbd1c3596feb0,0x349179d8bb79acefbef2224eb4ae4bc96e6d3b1532d49efe00,-0x5bd0524892a2569fc6769b7988877d0eafcf895c7c58e8906c,0x887020d9dd899251a6606e72bfcd82a1acf73af2095b1dd598,-0xadc2ed23ffef5524f2f58deb5f9427f722a9afd3b43fe642cc,0xbea5c1fc7fda46cb31472f81bdb8117bd937bedc40f0dec6c0,-0xb4da6e13a836d105148b2af49eaf3f454ce17b468aba70e120,0x94a8f5afb098238d745f37ff4b6a7637ee01eb67880eee6b80,-0x69fce58b6bdba32f434571b217c8f9f30926a807efdab82dd0,0x4187b3f9482ab79f77c586ac9d34b06dbd8830db3e995ebf20,-0x2317614f5832d134cd9d9f119fc29d34e5185ee2729640a78b,0x103cace743559631f52c3d76cde13df1f621d6c7db0cd3f0a6,-0x6780accf7bc2fb8901edf59ab3bd8966623e85d213d35fd23,0x235628695df5b0ba6a94d11039ed0d968c3ea103b6aa57950,-0xa464c9cb3f4b6e96a52605c0b0c2601147e06e935ceb3fdc,0x2864d18776b696f2e4684e965122e3f11f39573d758656a8,-0x84e80e8e85d158c273168cfc3fe4be8df8e273e0e29596c,0x1699deec61c1c12e166bdd3336e85d6cd1268fb7a3ab670,-0x3219fb7665d5009b592797cc340b9a06fd11194b8ade96,0x58d4d5cec97120070a75053868cadfc855dec70e0c29c,-0x7b1654d6979e7a0e28f720c5cba70144efb333267256,0x816d5bd5e9698146487da006ff2fbb724c224d7fbf0,-0x6370d1098b35321183ab7a94388dd445e28be2419c,0x351e42d74e208a54972068cbec548d85cd335b288,-0x1273717c409dad35318b9001c4972b7dcbb9d61c,0x3cc42f2faa4fb61a0ce2afa5c4e92679ba97f0,-0x67a1d0d9854829415b823aebce3da3e44c6b,0x4a3f45e19157f533a48a36165f86de6e16,-0xf8810d669ec18bf7902bb2b512e39f3,0x6c40d11b96c6e2059dc3b2280000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 20 66 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 66 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 44 indices rho q19 m19 19 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 44 indices rho q19 m19 19 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r20 : List ℤ := raw_ints% [-0x7007031f91c954c2926a3f7aab2a4b33e80000,-0xa8fac2512717956da4931098f5bdb967768000,-0x77831cdb60610654c5abbb4070faa5aaaae000,-0x34b2c9b3b5d79eb1238f962b34b60f49924600,-0x103f4c8a72c75fdcf1694fab7338d292d8ef00,-0x3b8f4ecb9397547cbb13dd9835c94a5994a20,-0xa851e32604748e143392f8fa9ba773d4b270,-0x177648d0e69802d652717b46ad95c7fe9450,-0x29eb410d70dea84ba01fcb7b761a13e4aa8,-0x3c8cc609cb0c19c9d6486dcd69c6c7efe2,-0x4706cc5833cd507720cc823ac44a14acf,-0x43af61ac82e36a932b1ca962b9b5e5c4,-0x34344cf510f627a5f6ac0133ad4ab2d,-0x2051016c1cbf606ef45f5d847e9eb4,-0xfd4390c2083cc4c7a0ab83b1845d,-0x5ff684c00cbcbe92f2d4952f7b6,-0x1b2302701953fa1a063b1642bb,-0x564a98f869f7e4534d3ae81e,-0xac1f005ab58444070f8254,-0xa221a90706fcc45112e2]
def m20 : List ℤ := raw_ints% [0x0,-0xa165b51e4be155175ab445ddb32611ddc926ccb68c9000,0xe3fb1965b54f0da14deac053eee86bd20b270b1a83efc00,-0x9a95c0a4a17f365d53518db4c126c75998a1a5e21c8b5b00,0x42fc3d8be839548002f8dae684bf90518bcee492bd38d1840,-0x14d5916b9950de6276e0b4a0d86ac7dad210b28e080c9c0680,0x4f3d96caf1381db4a46d6e24cd8d012203518f3d8e2cf74210,-0xef7bc4f3b8939d89db2e7c2c906a5aa987b1d884889ef232a0,0x24e590f020d9a9b31292f113943c86b24d76c57ffae3de0d950,-0x4b90884ee5690cd92677e71a754cee0356372dbe224dc1de900,0x824c913fe18946086809a844ae725482e5961fc0a96566ea534,-0xbf092bc659334403f9a1be69feace5fcb0c0229aec3028078a8,0xefdc7d860016bf0a93bfc507e9f5ff60ab8a79d16560efcb454,-0x1033fea1acc4a06a4aff1e0ef536a4514265b639e46b892a2b40,0xf20e2a982f3db5f1a81129d81797ffbbb1b9405b86e4bb854e0,-0xc3a512a1f7cef8a1c8390bdc87dcb703e94b82db4f90fc1fe80,0x8903268aca0d7dbc89344154bd8d10bb78c77e2036cd8498790,-0x531cf41b48823e027283c217edda849ebaa3202f36e68ad47a0,0x2b9c69dffe12899fc15afe1eb5c85cee5d4d42125f6fe9f641d,-0x13bea16f0537dd72557a39564a3fdacddef7fa58ef9e5a59a6a,0x7af4b63ebacbaf0528e16a973c37dc2ec7944197d67679b065,-0x28ef7d3ea3b69923725c6370dc7cb639680ab9b6c0014dd330,0xb95672b019e2fa232ad056f36e871ae7bd9dd6be9fb250d44,-0x2c37f24161ae1159d6df197190dcbbb661eaef21eed0dd518,0x8ce6e0e26545aa126aeb56d245da1882903e1e51c3614f74,-0x1722c954b37d491a7200c74bac17011934f0d15dcb7e8190,0x315a0bb156bfd10ee823d8a6dab56834ee71af85d930fba,-0x53dd7b77089bd1c24510119c0cb1e76411ce5f68942304,0x6edbe16e81255055a8d4073fd309d5c9ccfc1b78bf1ba,-0x6e99617233ff9e11b02178d0bbae3f5eec7e521cb390,0x501aabf804fcc51afc71ce46d9bfed3ee1ac8dc1a84,-0x28075d336568c65c9f6e08442f31eeb977eae46c38,0xce3a0e13f9519643334b771c3507a1b846abb164,-0x26ecc618daaf55b1ca61d6c961d7733f4bb2c50,0x3c16a7e04a2c72b3757e39710176ccac82c3d,-0x265e9afe1433c96e77abcf13337d853d57a,0x70540b6310711cbac41941a8cf522f95,-0x29c6dd660d120693cca9af1700000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 20 68 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 68 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 44 indices rho q20 m20 20 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 44 indices rho q20 m20 20 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0xa221a90706fcc45112e2,0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r21 : List ℤ := raw_ints% [0x1155d8427f50a4a847810dc9ad41d17779100000,0x1a21861484ff9bab1023c3af4541201676390000,0x1277cc26186c61f4861542ada09abb8bdc144000,0x8230ca845a2590ff36f0ac163b5779eac6fdc00,0x281a8d90bbf86fe5f6b7d0f2745226590953800,0x92df9c6301b87bae44ad90c01bc99ea55dd240,0x19ea3bbbbef497e7fa32b9f85fe1243f2b61c0,0x39bae0f542cc180be6a063abfac9199dcdff0,0x670394bf0b2059c31f1bf805b6740e717780,0x9497584ffa9e3a2480772b9a377d25fd7cc,0xae0868e6808ea50f9cfb8924d021dbdccc,0xa590168f7d3ec2a939aaf3b95dde4374d,0x7f744bdd82eae5535d3213417d00c146,0x4ebba7992c48a2373c8be8705effb9b,0x26794d97ff938a30c80f4a4f780ef8,0xe8a1f239dd3a1327a7420292743b,0x4196efb0590dae7e973dbf263ae,0xcfddc9677c04e98d63e7c8c09,0x19d0934a6cf1f45f0dc69288,0x1835c253ccf1d1b31d5b58]
def m21 : List ℤ := raw_ints% [0x0,0xfc2eeaff569014f47db9ad2a67eb7bea8a4c9fdd3ba1000,-0x16129736769b97418536a205605888578316d01596e269c00,0xed51f7f965cd9a34a7e1e6a43261d3ed219bb48c4f3f05d00,-0x65dfc8ae934f7f97c76d72bb8eff61446543efdc1d6822d3c0,0x1f6026757d02c05eab25f83b9843a21183fde9a9f2aa9d49180,-0x761c63c3a7a00a9549c956364630c4ee93e76d7bd06c6bfc570,0x1612044cb2af28585f9a4b66a283f468b58fbf59374bcf481c60,-0x35cada59f2bcb4bccd9dac8250fa7b7c953874ca8fd8a71ab1b0,0x6cdcc51e4556e63b6a59f533cb1410af5eeef507932c19bf2e00,-0xb9606aaa1d9fcd2499207c003f77f5c505685d3254717b24b72c,0x10c37979c0fc64eeb9f08eb84606b70025b5aa9f320ac773eff18,-0x14c197819f68408e969268de49b2da702c68e09d3c654b296cf8c,0x161ae4abc663dfbdf4755a083d7c3495166010ec426d1e22642c0,-0x14518210fbb37e924a13227eabd244e2658b80d73bf2ae63fa520,0x1026e1971fe299bfda3a7f7fb52eea4debf0f045b5a38131f9780,-0xb1ceca17d416b3d794ed5ab2be853e7464cc0834c84a0553f6d0,0x69d7fd2800b6040da16accdbfc8bd7dcad8aa323301c5524d520,-0x366dc235a8b663f63d4b23a860a81159a04311c67002b25668bb,0x181d6fafc9006ea19b6ffae1df76cf31cd76a730a0f005dbd006,-0x92b80f3e028a2363993d987d64e5bfeeef48f11ac122de309d3,0x2fa31105572932d4595d9e10a19ed71d466ff3a8f4fa651b650,-0xd1e7864f36e23f429dd75ee5ad804233f1e9b8ecc6344c139c,0x30a01b605b17b6f1fce1b9084a9c1672b0c89e62650dc0e528,-0x960ba9cadb1239a826fa56bb8507a6f09140634d4d3b21a2c,0x17c92ba69a5de348a6bc2e40b8974db0ac18ec670b9da2d70,-0x30d02d2da040ebc5c381539a8b2c8e3b1176297469aac6f6,0x4f7ab12550b00905a639753a3214dc1e3d759b9a80e2a5c,-0x64308db913071cc9b4c3ccac35735313bee7aae32ea2b6,0x5ecad1fb6d8f49fd567d15c88aad3f068a1ce48ab62f0,-0x40af720e5896933141e5413db60ab5ee9faec6d91f5c,0x1e385b1d3f7468a2c807755158d1e66e1b765ca3b08,-0x903bf299f34c01fe2cba8b18540575a5ddc93c5dc,0x18f2b9a06ded3b1707962f1a472043c2128972f0,-0x22d792ad041e6b40485a5428cdf0ab2e6ddf9b,0x13d279af3253a1f4e613caa8f70ebcd83476,-0x32c0138f33e79d757069802ec6d1f27a3,0x101da9729a3a9bdc8c49a71ba00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 20 70 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 70 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 44 indices rho q21 m21 21 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 44 indices rho q21 m21 21 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x1835c253ccf1d1b31d5b58,-0xa221a90706fcc45112e2,0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r22 : List ℤ := raw_ints% [-0x296ac5d330d1e65325525e834fc02c71632c00000,-0x3e64b5282e6d399c9eaa20074bfeeac215edc0000,-0x2c112535c3eff914a2e247959fa85b07659d00000,-0x1366cf71563c84cddaab48e171988db88f96b1000,-0x5f8bfedbab1825ffa6aa1e92e5ffab4695954c00,-0x15d9ea635328bb984dec9ef9913ea1a7ac8acf00,-0x3da11f9d2426d1d107eee40ca490be5f7d87040,-0x89255d82c0ac11f87340b49edf8ccfc6111ec0,-0xf47166032b5fa76ecde944238954bcaf8bbd0,-0x16025c002f40328d13890f9c53712e6803970,-0x19bde042788e77f415f8c4b5df4987953d9c,-0x1873846aacde64469d5380219fba199ff04,-0x12ca8997fb289e19405d2d40e1270c74eb,-0xb960a1240ec6f59e2483e5c47bf5ab1a,-0x5a65a69ae7870da19ec718a2d6060f5,-0x2214f0a8789a86bb58313e74318128,-0x99581c6f3f62a89bdf37f64021f5,-0x1e48b74bcaadcad53a120719f02,-0x3bf9766bfee4a397627035dff,-0x38086070d3adf8fd7c60a08]
def m22 : List ℤ := raw_ints% [0x0,-0x18a094f2ef74120be04721e92425ff19e7817b9c9ad2b9000,0x2233a6de652d6ab9870d6d042b9015c0bcd3a521bbc1c53c00,-0x16c8943e6757032d1039d27b3785ba337e7000a0e0fa0100b00,0x9b0ff7dd07f798dc0ea1d629361a994b32487a136348c9e3c40,-0x2f4d69569c143e0e675ca06fc8132dad8755902d4f559d30ae80,0xb04a4dc8cde5610cfb3ca9c52cc5a478b2f772031c554fb5a310,-0x2098d6c22136260c41d63939a2584098421f4abac258a382b9ca0,0x4e93358874806075be8b5eb628637cefc113ba85873a5c5583650,-0x9d2cced2894a161c7814ec3ad06aca860e1c5eb1f15fdea404900,0x108612e39ab0a7cc878d79f4c75e21092ba168d5565f4bbac8a874,-0x17998c872e3679e9304df76d34867c0325f96adf79b578c570b328,0x1cd2981ba6227126cfbe7e805d889f22921464b368c53977af1994,-0x1e40b7a984df229bbc79654693ddf2bb9ef428b17300d0eb224f40,0x1b61c2ace3085354507736a3aaaed20aa1f8d8ce45dc7b166170e0,-0x1569a11eb7f34135083b11c39958f2855b37ffa957786c9c61f280,0xe7a1ea8e5b852651b66bf1bbf645a46ed1f13047df20c7d8b9890,-0x875497c9b70dbb36df1e7bc54859545a3d6d52a2d29e401f065a0,0x44365d280d9739c1364270492936c66269db05fc76a02fea6b96d,-0x1d9436727266af0796746c1fdc2a4e04e2b6b1d07e2a8c67b1c0a,0xafd7ad9454c35cc0df15a0edbdc9d9e78f164dc5a8a5b3f7c435,-0x37ae9bf9e4298a60c49369049a5563975191c0d57e2f99f7be30,0xeeca01cd013f254aff18ea8851eaf96ca6c48688def6ba2fb84,-0x35b56a74a998108b87faf769ab8ea8eb52a4cf36f1f98758298,0xa07a3a4263ff1af70ff76b18ca32e2d8a8deec8294d31784b4,-0x188e825521da26b819d5fc4859f251bfc7ce61c17b8b9c5a90,0x3078f495663e0df62c3c3abf1d037663254d6a33d1c60645a,-0x4b9981ace6a424d06259db64406c832b3474d1194c7b7544,0x5ad871871a49564dfc5718840bf3a43e76ad8b0ed60625a,-0x51796cd6418291e6c4d16559c9a5e1786c256e2b36a490,0x345a97204cd2dba7cd0570306a5586de510a8df30eec4,-0x16da82eea438fc2dce8cf22227bb87e919cf3b724fb8,0x64fc1001857199e016855a80018a2ac6cfd80b9da4,-0xfff67cb85c2c5ced8f483a3a45f87f0fde351d50,0x1433e96896e91d11903c865232d9ab89fe8ff8d,-0xa3ca44f1bf178332c3603f22db228336381a,0x16eb21bba2d4eaaa888a128c89e07c9265,-0x636e440d471d17d0f4d18067c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 20 72 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 72 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 44 indices rho q22 m22 22 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 44 indices rho q22 m22 22 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x38086070d3adf8fd7c60a08,0x1835c253ccf1d1b31d5b58,-0xa221a90706fcc45112e2,0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r23 : List ℤ := raw_ints% [0x5fdb8aa25e2e68f58ccbc22a3f346a46aa58400000,0x90533cdc62f5a1d42966d43c5aacfd6e6c91040000,0x65def6694bc64265ec6ded860679730f04f63f0000,0x2cd23b00f64c603dd64eb7ddfe03900dbaa8bdf000,0xdc91a01597b0d85b606fdcb1cf114a9823d2c6800,0x32672672e7ff5816c05f3181b6a770c00d1b5c900,0x8e08454c4ec3f5d3e7e9ad6868d146a9a0507880,0x13bc42af23a210f5224e29d343d236249a5b9140,0x23237893527b55ddce18950a0f0597b0b9c7480,0x32900e46af9d03974085b0d026ad7ae7c98700,0x3b100ced93850d65f63680dee58e9859ecec8,0x380611e3294501c732db35bcfa454c38e5d4,0x2afd3092d0d4a14ed13b11bec5c93b35da4,0x1a75f9c4c11755580aa830b1f9ca91b035,0xce10a1c713903cc883b6d28c6be5ba96,0x4d876d0c3952c5fa5f5f7a5aeebef6b,0x15c0377f1bdcb0dbf84fd8f383b168,0x448cd6bb9a703c07731b3fe3d61b,0x875bb7b58fff95bf3e53d00716,0x7e0ae5ca17007eb922ccc7b1]
def m23 : List ℤ := raw_ints% [0x0,0x267ae8bb96255c328e6f24fc487b5e9879ba5124b1e9411000,-0x35029ca16fde6c569d6112202b99c311270ab204b55ec42dc00,0x2303f433c44cdfa0cc4ec83a76a7b9072368363a308e1a212d00,-0xec35d3762b997aa34b79122abc3674bc6239179522a79771afc0,0x4763fe81a834d8b3e4325f148a96872dde56c945322bb0c15e980,-0x1077b3acd90a163da17105cd9f8b9c8ca1f19c1e25b17e7ac81c70,0x3038d641df91beb6d2d2dcee31ef5dc82bd04088715c0d6a9fa260,-0x72fd985f9849aad1d8ad2ffd3bb0bb4265c9915b1f9444bd0514b0,0xe369edb017457bf6062e66a28b5bfcc67843e39e4b54075a155e00,-0x179f4734a1fc4a60f8b22143f37147ec9fef89c93965176588f49ec,0x214fd22922be0fd3edaaef5648ea0cae0298832fb7a8aad02dbc098,-0x2823bc23f1859b5ad8f948ae3e7c32004be0b4d1f220c97a50aa84c,0x29887fc5de8bb3b433acbae8ae23841e0c2c60e4b9f215e7d257ec0,-0x2506493591808125f1c53caa9734e61261f3638a12988e860a9a920,0x1c7ce61a97be0a1b6f92faf007b18664bf9b6ec0340ee48f07d8380,-0x12ee24735f9aa6fa0ea63810427f8af70d1446f07decbed2da2afd0,0xadb6406f147f55690895e5a7b99610f7d6007352f968c5ad090b20,-0x55d5e63b386df7d7ad2d8258e05ae4400ac08f5708eb7ccf8daceb,0x246eff5f12c4857e039d4ad93f91bf4379e6550ce0a44b7764c566,-0xd3a730b424a0ab2983244e0ebe03dc4f3d6cab37d817322b1f183,0x415e882ceb069c1a173446b7b6d8efd9201851f93048bc693c350,-0x110d5afa1627037f63db006ed016b701d9eccb6059262e6dae35c,0x3b947e1f2c3f3694d1f1b74cd6c4994e2e7c68b85b3aab7fdba8,-0xac5c71a8e6c75988e8d250e98fcc8a498550f9fa0a285b9e6ec,0x1974ad767f2dc2819ca294e0678ef5f6fb3609ae9316b139470,-0x3051ae9dec7ea6b87c4c92d4d88280b6b48c01ccfba7135556,0x4829d81061799f2a598203c9a2799e54c9f674a24af45ce1c,-0x52a1bcd6a11f1f0bbf2ce522d00f3fc77e09886d6afab916,0x4637045c6f31a9d74e959b98d6de0a5cead33bf826139f0,-0x2a76c1454ea639bd8341ce962721b00f6f38443266991c,0x114f3da93ab804d733eb61df718033d72b685b184cb88,-0x46c573be2e53656cc461384f6a7c3edd2512872519c,0xa432c01c380f3641ecefdfc7419a2381b0dc1bdf0,-0xbb6b47c2541be8c3762ef57c76c11b43aa895cb,0x548eb7ae26ae42cea5a091ebe99d63caf80d6,-0xa5859333ab93e1bfc4873541bf80920053,0x26539f9779fc54471529b435a800000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 20 74 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 74 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 44 indices rho q23 m23 23 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 44 indices rho q23 m23 23 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x7e0ae5ca17007eb922ccc7b1,-0x38086070d3adf8fd7c60a08,0x1835c253ccf1d1b31d5b58,-0xa221a90706fcc45112e2,0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r24 : List ℤ := raw_ints% [-0xd7a05e381b7c7c8f6944f81ce2c5ed3299bee880000,-0x1447bbbf0811496baa9a445561a890b15bc561f08000,-0xe4e79e5581e1d4dc16609b5dfc865cfdb90acd96000,-0x64a6be92824bb28aef5e57c67e2586bc5cc1561de00,-0x1eefab3cdbf42364022fa615990caada03c91c38f00,-0x7106acb9522c4deec2061d5021e7783c4247e860a0,-0x13e3e845200c6980ba8f35eefaea0e521f19fde8f0,-0x2c2e616d1d4edc0072c1716d295961ed1cf1cfcb0,-0x4e969a223a8ca0161313174b87657ac09401bea8,-0x70f74275281abf77c32844c33152379399f5f3a,-0x83cddd255f6164d819f40f35505eed9e97a317,-0x7cdd3a0bc9ac9e2589c68d17ba6e9750851c6,-0x5fadf3cc23c7874424c8ccc6dab8b97958f1,-0x3acd8b5ceecfa005f82db4d34a83e0696c0,-0x1c927b06ce3d79c18d8b71342281570821,-0xabacf715be587d4557313c0a39e7ecb6,-0x3010415d73a00d48ccc729e37cb8ec7,-0x97202f9bd1d522f62231174cc527a,-0x129a2c45d0d560980a1fbe93e1f8,-0x11457a8d27db03b4f1d029c940]
def m24 : List ℤ := raw_ints% [0x0,-0x3c200ba51a9a600efe8da9ca3140c3ce3e331ec955fc75a9000,0x522ef0952976b9a66d71d000bf6d3268cd00b6275b6412877c00,-0x35d7b577544dc3273d665b92dd9f8706e43b11453858c622fbb00,0x1681baeb4b77deadf94074cb5b8fbc3606a1cf6121e6234de7a040,-0x6bdbd66ffcdc8c6fd24eae177b40a0640de96bfd006efb874bd680,0x18a505f49b71ae9453694f0861ff01a73c78349a29024087b3a1410,-0x4772fd39f8b9413639e8ee768a344cccefd9261ac2dc60568cfa6a0,0xa8979b617ffc895a3956565a17992cfd1471f8ab96d84431f40e350,-0x149bafd22e4c94b5bafa318414f27816845462e46c7612d03a93a900,0x21d97175d9753c6390fd68ba732da875ec4748319cdfbaf7301ddfb4,-0x2f2485b8f1f4e4543e296e8f2d361d2124d549825d281571c1db95a8,0x380f04d8038a47b0abb805e2d3d194199d16ad81f1bc412941eb52d4,-0x3931db44791d7640c1031cc26280048ea89eda5576f7ea63ae38b340,0x323a49308dcdef723d75e96820e5647ea4d877133ec5d885b6204ce0,-0x26089845d264409609af904654ec45ebb512674fb1203789ba712680,0x18d8377bc1b20818021511c90ad5c13bf0c0285024d225131c0d1990,-0xdfd6eea94578f910342873dbc422a4f98c6c3bc9a2b202583c423a0,0x6c71d81eef4bd0d17a64df7390bc7f29912da3c2dc4de340df6b3bd,-0x2d0fdbe93669c25e131c4cbbccadc2523da8eb950280748352f97aa,0xffd4972f5735cb533a1678dd59f9f197f0f88efd260faa14b10505,-0x4d11acd99b56a60b7a05a109e3145c9ce82024a463c683f52a5930,0x13910bbc701d049b59d24c48ef3e2a93db447efc53d30da4a60dc4,-0x425f589e251426e32091a6fb46c378f37ae991f93e01cfef68818,0xb9e32df4a3f77a4086a953aee067afa579c48779436b64458df4,-0x1a7df63e834a2e07396d3c58fcb5391b86ceb4cad13041024390,0x30584926946daded534068ace21f1785d10a357c4d0d18862fa,-0x451e034daca52acc22f05011086834b2a12c25bec3dffe2b84,0x4b62da2bd55734cb98f2f537eba37ec4d40796d709309fcfa,-0x3caa21ce09f392c3b414256b6f5f463ecdea29970277a590,0x2282cf1e04f6acc36423480ce573c736ec1990c35f64704,-0xd210d7f06231ad4d1973dcd7aa1cc933c4d226804eb38,0x31a3bd81f7cfb4ab12e052b01e0bfa7f9569b1276de4,-0x695dbebe0dcced842a9383621595d6d53ef70fde50,0x6ca80fd8a133e6f8248250f271e3da50ee5dd7dd,-0x2ba33c5ee96332f9ebb3987e0dfe010351a4ba,0x4aae5bd4bf85a15c976f926ccbcf3f01235,-0xec495cd815d0c45e6e4ad8fe7000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 20 76 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 76 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 44 indices rho q24 m24 24 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 44 indices rho q24 m24 24 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x11457a8d27db03b4f1d029c940,0x7e0ae5ca17007eb922ccc7b1,-0x38086070d3adf8fd7c60a08,0x1835c253ccf1d1b31d5b58,-0xa221a90706fcc45112e2,0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r25 : List ℤ := raw_ints% [0x1d8c037b64eebe1e793e468564879b9821c978a000000,0x2c712b31ffa9e95a6ba84de60b06a2807fbd604180000,0x1f55bffcf04b32c71c0791a3c0e109ffc674c67478000,0xdc53756e973e21b9b7862d297d892f8b685036e42000,0x43ad6023ca34b2480b9ffbe3882b15a47ec10490e200,0xf717a347dfe2dbef5d04b39d1e2661724308acab900,0x2b73729dbdbd5544594d98942fe6cb9e926742f4b60,0x606ff553459eadc20be04df58a2b5a099a3f8cd310,0xab638e0ea851d8a6506df3fbe302e953d2558c550,0xf61faa907c4d465a836105ddc148c345224061d8,0x11edd6de2d7f5a2e1e5388d3e0d2d12019917186,0x10f7265d990305c788b1bd6a451c4f65591f669,0xcfbcee2483e02cac591d07713531e84f0c07a,0x7f7e9992691d7c197a2e1dd4f8f86b48540f,0x3ddabc2bf77c284b95ce9c6fddd25151cc0,0x1730606c85b8f9473517970508fa2026df,0x67ae1681f2eb7dca34d658b33f4de9ca,0x14552d0388ae607879e9145087fa3b9,0x27f3a924b1892f1c42cb0dfd64946,0x24ff6211d6dd5e512b25405d188]
def m25 : List ℤ := raw_ints% [0x0,0x5df21231f99136176dbd594becf531f2412fe01a965a77d81000,-0x7f71a1ae70ca4aa2ae510a86e40e0930c0511c9d7ecc5cf3b1c00,0x52d5cba40145fdc6252ff2f6a168723e58aa2202f5fb25b86efd00,-0x2256a61d0edef615ff8a197350405b30428600d543da495f3144bc0,0xa31f8677789ee574f4d1a8e298654c2edd5e5c85af0e222e328c180,-0x24edee2672fb3a187dc6e9d8754b726920426259ebd5bdc5d7b1e370,0x6a070f3e67b466bc9a71c6448b790ce41c4798cecea7fec26d9b8860,-0xf79fd9d370ff6d393ce097c621453861b32fd7426cc43d0b1d8927b0,0x1df0fedc2b9d21a74e1ddc520176bb44d6a35ba96b749e80562d18e00,-0x309dbb7a4594179614bb4c1afa48626d1d2d731652e1a08938d1708ac,0x42e2cd819f4f8379fea00a7df9d18e46b443fb854181b9d7e5f4d9a18,-0x4e82572aad6ce9bf2d972433c5ede17b2d30a0e03ee6a10d5c00e8d0c,0x4effd71788759c669a49abab2697e6c2d11f5b10643ec2de1cfa87ac0,-0x445bf89390e5e32d4b1cbc70af27b13b7aa431ffaa319a237d9e4ed20,0x32f3c72c961215ce2188367f481e158a1282ad7e6bf3103604da82f80,-0x20b9931f14c4b656bd8e6dfe7dd55c1e8d29010c65849cd86b75758d0,0x12186a0fdf7fa86153264483b8c344a8706bbe54457c5e96c98c16120,-0x898c5ae5279003c9a66ac24fd27226195ad9c3cf7a83c7c51ae6a41b,0x37f5a0aa3d797b92cdedcc02ced0d72aeaf344bbbab57d95741430c6,-0x13681bc2677a8e7ad7b488d828f069dd6be916917e844d2ad52e6433,0x5b3e09eb1abd79ceb1e109eae2514fce457e16f65e9ce2da120a050,-0x168ba58ee2e7b7f9f1166347c4053c41498af6903420b5e400b6f1c,0x4a3e72540e8943393d7390a9c037f5fc3437078a59f8084e71ba28,-0xc94768effc7eafcc1781d53e45b3ff280dd63fb2a434059697fac,0x1bad16666a6a38b4a02209b41077df1471095bb7e51c69a0deb70,-0x308b40cbe81d4460301ab0330682fd543cb0c413a7b8a1b6e9b6,0x426a5112043287af215805829824b41271e79169cea09836ddc,-0x44f8f0532b3a4129856544c3fe24d2949fb499362b9a551576,0x3489d56696acb053df547ceb3f2cc45982763d8c4cd8080f0,-0x1c1989135f1e26dfa178911e7203a7fbebbf4f58f3ce6edc,0x9f8a662447c62c5ca5de0aa081d29c485d625408a9e408,-0x22d8094d99151cffdf5c853c7411c3c4836bd3a4b395c,0x43a19105664c73baaaf037b24701521e8017bce78f0,-0x3efc5dc6cccff6326be2ce3c5bea7730dbd5e9efb,0x16830eeaa9ae485d4922216754201258cd0b336,-0x21ae2b6f13c0b0eb5a87e709917432437403,0x5b031c9fd5243022bbcb780b9a000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 20 78 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 78 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 44 indices rho q25 m25 25 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 44 indices rho q25 m25 25 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x24ff6211d6dd5e512b25405d188,-0x11457a8d27db03b4f1d029c940,0x7e0ae5ca17007eb922ccc7b1,-0x38086070d3adf8fd7c60a08,0x1835c253ccf1d1b31d5b58,-0xa221a90706fcc45112e2,0x417c11885665d254add,-0x1967e95d969feeabee,0x96a6ad4bd8bbdfa0,-0x34fa0429f11be4c,0x1187722f670601,-0x5666c0f55c1c,0x1871868cd60,-0x63c10b67e,0x165b5f1d,-0x43cf92,0xa398,-0x118,0x1]
def r26 : List ℤ := raw_ints% [-0x3f4b1a1a65d57ce562e9a54aa2168ea7c1f17014400000,-0x5f2886996cf79faf26ff68ff9d482fe4b1310ef1840000,-0x430fa534c149a8e3ffb566840a5f310406f9929e530000,-0x1d7474d98127168fad9365726befe9a2b61520eb977000,-0x90adba01d60001439bc87366fbee811d33f18c953d800,-0x20fe565feed41f73a40ab2bafc7af568ce1481cd9e300,-0x5cc442cd9717cdc71c5949decf1de74acdb79b1d9680,-0xcdbce6d7fc25521d9be579ab9117121f3697c781e20,-0x16d57802cad866740cc847027afa99b2f0803f1cc30,-0x20c2fbc2226977266c2069c166b08379448e35e080,-0x2625db02239f22abfeb1d52eb263e215579aafae0,-0x240f3841fe2370cc94221c78ade81434a90b2aea,-0x1b907c1a37feb49a6419d423d388e44d29023bf,-0x10e546f6c69234ab034bfd020a5156c7e5b2a6,-0x82f81dc559844f342c2497222605d35aa6a1,-0x3106538e73a408c545dacf94ddfb5ef0da0,-0xdad2fcb4e9c0b68036d0fef2f546f32b1,-0x2ad564b32e80903a5617e97c136b5d46,-0x53fd4c8f3163255bfdf2e9f970d8df,-0x4d9979ce8a6e11a07740df35716a]
def m26 : List ℤ := raw_ints% [0x0,-0x92ca3c6e15f2e4849b77db86a23f1e0a85dace298aed5b4199000,0xc5adfb48a03d4174255570bb59c30dffac7ebcb6161f513cc5bc00,-0x7f80b5726cdf5de53079af2b0a02e7139e1dba3e68620c20b9a6b00,0x346dece5947a1578258dd69003d418828440f49081443374988d4440,-0xf6f38d1e3dfd0e16f9bad0223fd683c74e11401cfe8af4a889957e80,0x37684ef02423c04df69eee838ecb59fb5efc108a498b5dc5743a59510,-0x9d93f95b5aa2c292d6321b0b840c14e601a24522f8a8351fdd64850a0,0x16c588639e2b741f366851f4c604a3686c54788ffe0e957ea75837e050,-0x2b96cb6012cc9749ec16b5b209c38d6bd366766a0ebe95faeb90780900,0x45fb828d103466e383b4e748d60e57d3a4d0a7caea861c7b2416c98af4,-0x5f227da820302bc3174a95048271c3fcd22f468b6b85fec63ff7aba028,0x6e404369a4695285a2e24ba6ad2d24919020c84f7cc1f223a54c26a014,-0x6d707f034fe3864bf199ea82dbfbdd8604bb1c529d2beae8472dc15740,0x5d54d0bb4552a46c6ef716ee727640f82507689e557198500e4a86e8e0,-0x447d41cee3cda62694fbbb077df81727bcc83bb2c25ed12ce501df9a80,0x2b4213c62a59fffceda563df8e9825198913b2e0908fb86b93b53d0a90,-0x177e1e5afb41bc734cb034cf8f5edcbf42e25bea490c469dd6e8c681a0,0xaf22f18c31a4d43760c0d786a7ce65bfabcc5ab48b1d6ff2db59da30d,-0x45c4c7c9a99bcf94dcaeee38ed90d8c8152793605d2007010fd96ad4a,0x17a656200a7d30d38ff691517193605a090796a3add2f83c0b88242d5,-0x6c76cb9907677a12c4f22e1e9eacb9cdc644ae1ca68ff48dce80a430,0x1a157fc2ea921fc7ac773db8ca53e5ed23afa0a45da778328ed88404,-0x536206d4d46fd1b80ee44d0903ba3cf05b52a459876313262966598,0xdacb8a66a678f7dbeff5ade8f8eb53473fd83a5eda4cddcf14ab34,-0x1d054193dee1ded20d96fbcdc45da85ab0b377c29ef7c05b193c90,0x30e992256a6bc94886b1ce9f0436d806bf09daf0c002a7df1ab9a,-0x4004bac719919d3321a7821d256e912ecbc246c48526304285c4,0x3f46af2f0d6e98014fbc41877aaa13f2ff521b63dd0bc2b619a,-0x2d9a6d3749f45f49395d269d44fdb0cdbc9f09cc7b1c80b690,0x16eb507dfaa68041377997072f35db736bf67ab947aa66344,-0x794fe0578d1a16204452f31d3479545f3e9767c7b7bbeb8,0x187975f5db7b94f5d6e3bb3ee4a689f525d52c6f116224,-0x2b6b3b18d0884a085460f49091b6b6f94ba652cc6f50,0x24817fd5c39dc0a3e929afeb11c1af450f4fbf052d,-0xb9bfb3b3f81b0c016b166aa555c7dce95e2bb5a,0xf2ed852b86501654ffd17e0fcb19a34c7f05,-0x230b1bb075818a6b3698838efbc000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 20 80 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 80 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 44 indices rho q26 m26 26 12716506595025820348489728000 25=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 44 indices rho q26 m26 26 12716506595025820348489728000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_26
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<27) : intPolyRF (mz e)=rfPoly (C (12716506595025820348489728000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^e) := by
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
  · exact moment_source_23 size
  · exact moment_source_24 size
  · exact moment_source_25 size
  · exact moment_source_26 size
#print axioms moment_source_26
end
end CatalanCore.Li2.NVMod.FamilySource.V6C26
