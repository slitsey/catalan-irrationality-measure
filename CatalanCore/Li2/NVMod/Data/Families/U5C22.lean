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
namespace CatalanCore.Li2.NVMod.FamilySource.U5C22
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,5,22,size⟩
def bases : List ℕ := [1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def num : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x81fd1b38f7350000,0xb6f4dbde6d437000,0x77db631799366200,0x308d39697e16a400,0xd9fb237613459e0,0x2cf9e81d5294b90,0x7114fcfa2715f0,0xdd3a9d18a1ed8,0x1550519b50f3e,0x1a0a85c55381,0x1939609fd78,0x13439af98c,0xb75d4f24,0x5334d36,0x1bd168,0x6754,0xee,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0xe,-0x23,0x15,-0x34f,0xc4a,-0x2cee9,0x18f65,-0x22f27,0x27478,-0x5377f,0x12c4a,-0x17e107,0xcbc48,-0x19789]
def rhoDenominators : List ℤ := raw_ints% [0xe6f1900,0x57fa8,0xd68,0x507,0xb0,0xa,0x3c,0x31,0x380,0xd8,0xb4,0xa5,0x18c,0x8f,0x1b5f,0x3aa7,0x4100]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 23
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
def r0 : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x1985d29d75f0899eed14600,0x274434762a2d066ddfb00e80,-0x1d0c895d77568a4ca0a524e00,0xdc2005b2f87bd517f6dc9b7a0,-0x4af6ef9792426210b781302000,0x138c25c532f9c37268d25da8380,-0x40ecafbc09d0a6c9bbade1dcc00,0xb0376692380dd4754ac45524868,-0x18e1acaf9a79024304f26188ee80,0x2f6aaee21c47289da39ee2538c40,-0x4cf8cd6d7767bded069c5d479380,0x6b31d548d60102f362a46f1b3280,-0x80b8bb988172bcc14d133b23c080,0x85bab0cee2c47aee116d3f3779c0,-0x786d146587680859bb334b702480,0x5e0dd947bdd04c495f428ae265da,-0x3fa9c13ba5d304a210576eaf5420,0x2545a42d03b90e77b7a5607ad870,-0x12cf8b8c1f72e6c4d53c860fc060,0x824e23744b22a46c44364acc6d8,-0x3013ca73d19806e63e583275820,0xefc4b4311dfdf7ad035cd21590,-0x3e6c0dcd0b59b6000d65632960,0xd5fba3aa245fe3cf8b4e68264,-0x24ffdca4c168cfbb1255224e0,0x50792714a1b061f1efcb1650,-0x84b73382c7e63179467d8a0,0x9d8b1fa29dbaa00c46d0f8,-0x7c510e9a7fff0fe3789e0,0x3915434a400bb1279c30,-0xbca2cf825f052953a0,0x91704110624bfa6a,0x1e0e688367800,-0xc8600e16b200,0x3da766cbe800,-0xd3628504400,0x1c2f44ef800,-0x1c2f44ef80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 17 31 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 31 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 39 indices rho q0 m0 0 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 39 indices rho q0 m0 0 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x23180198822abd3a85fc0400,-0x351b8090475ca4e7bcad13f00,0x26a0d95608d2aee2216c5ab400,-0x11fa9b52c17e68604dc3a2cc7c0,0x603a04226b0bb8710387ba8c000,-0x18a229ad44b1179a9c4e52fb8d00,0x504721543797d2b14333a4094800,-0xd5a8f2ec36826054c6ee492c18f0,0x1d90622afeb908c49674a6e8b4f00,-0x372c3498b63f45ff35cd173025580,0x57a3f12b066aeb75d1e1b49488900,-0x7755fa9a147beac5ea60986c49900,0x8bfcd207f1e309f9824aa4158db00,-0x8deee257d06f005212fb9ac4a0a80,0x7c9ae1e05d5b036707c918c5f3600,-0x5ec3730d36dd6ac8b7ecd78f1633c,0x3e60e554b6c3e45da0820bdcb2ac0,-0x2376b701bc05a73cc39a5482785a0,0x115a27bcf8afece80a07881ab9c40,-0x745212b34b0a49c62995c1f0d890,0x2971cd2a40310cb44473c14eb2c0,-0xc71c96ddacbc116f1fb961ffb60,0x31cba08bf4e5ff4d06b20c65840,-0xa36cceabd7c3b5304e15649398,0x1af1c02e0cc8c96f758c1ffb40,-0x379a692b28fe833cb106cc2e0,0x5676701a716b34c6127225c0,-0x5ffdcce3f35610247e9f550,0x4610c20b4d2a21d573b940,-0x1d4babdcffdd28837ca20,0x5612b973ef01d1faac0,-0x38d536413f3f2879c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 17 32 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 32 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 39 indices rho q1 m1 1 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 39 indices rho q1 m1 1 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x30410231b2fac430783a85800,0x47dcd2d67fabb99481616b6a00,-0x336ac281f36ee16fea07fff7800,0x17879754b4352d3b5505dc412a80,-0x7bc29b09d892a6e52b149d2e8000,0x1f1e409be48a1c2c9aaa8d2d81e00,-0x638cc868e64415e6f4945d5647000,0x103eea2b5ac7a219a28161f002a4a0,-0x234313d0c28ee262f12caff4421a00,0x4078bb0d5926e2199afdc227dd0900,-0x6441f2e27df5711dce66c2be748a00,0x8588c107b1b2e60feffe82b7cfa200,-0x9915488187f53f6a6aec9578788200,0x97889a7e97de94c10fd5ded7a6b700,-0x81bda58f9b3fc2b74f9d04c57e0100,0x601cab66a600751839ee851f0e3a28,-0x3d8b63cfb02975865f363dbea77480,0x21fca1e621cca8b20579be92abd3c0,-0x102040b4881fa23ac7cd8d6e82c180,0x68a107acce2675f4a4f0682dca860,-0x2400e394b45a608e8efe3fb963480,0xa6a2b065f8ae2ad59f2f7f3b6240,-0x280797bc682d0f43ca5accbe6380,0x7dc13a892cdcb592ad24fdca110,-0x13c383fa21874d4e88e6f2d7f80,0x26ad7e517150bd740666ea3740,-0x38aad368a8e350771d72ade80,0x3ac7593b6f0112b0760ad4e0,-0x27a19c8a8b980e24e29e380,0xf0ffe724914c417e2c6c0,-0x2745d739bfc5f11b0980,0x163026bd4531a2ba68]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 17 33 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 33 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 39 indices rho q2 m2 2 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 39 indices rho q2 m2 2 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x425963045618cdc2a550779000,-0x6149d49c16545124e53576b1c00,0x44818369bdaa5588c54a7e285000,-0x1ed6ae47b28af1bfb2ac5922da700,0x9f7a454d5f04b27cb73cb87070000,-0x276767b19ab75a7be9453cc9009400,0x7bccff4d7e99e3e9f019d9927a6000,-0x13d4595cc2692a9045bce749dd0e5c0,0x2a375adc85e637505945a166a962c00,-0x4ba75aa618d652101962e519228a600,0x7338975462efd01c995935998af5800,-0x962c6fe4e0d8a075274ac4e3e3a7400,0xa84fed80cef0cf103b0f68011e67c00,-0xa2b8eb93ce088a4ade3e1a53a4a9a00,0x87eb8bc63da1e742b4a4fc4da854900,-0x621ca49de0df0ba9d4d970567b41970,0x3d2229572e29caeb06035ade3ae4b00,-0x20cd021b92adef7c113e77511ceb280,0xf185f5227c0d14af9af0b56ab9bd00,-0x5ecf90bff917243261c9de2a28b040,0x1f8309323b5cf2df8d61ec699d3b00,-0x8c81f3c263558dd69bf70b9901180,0x206b597eb66ad7880f108b334cf00,-0x6178b9df086d506f8de9f08b0360,0xe98e9a8850a50ba5342763c7d00,-0x1b13b8d6d2035ea5bda51629f80,0x2559aa7e8e987dcd7870078f00,-0x2428c8f06a3e8b20ceb66bb40,0x167d80f8877c3e82dc0c4500,-0x7c1b776ac636ef77b35480,0x11ea9bcabe2998f7b1400,-0x8a7d29e0e0377ccef0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 17 34 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 34 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 39 indices rho q3 m3 3 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 39 indices rho q3 m3 3 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x5b3ae825f6621aeba34ea466000,0x83c5e6e4619ab1292681df246800,-0x5b5c7f44dc9b5e21b8adef87ae000,0x2879b33a0035340b78bf33bd785a00,-0xcde42aa0d74e889a3b2b4047e40000,0x32035b03dcd4b7570bcfddb7d54b800,-0x9a640a2d20a8dea41b8dd7218028000,0x18484c9a17688d450c87b300849b7e80,-0x32ba701fa37b8bd2d54e80a2eafad800,0x5923fc6cd481f26adafe597eccbcc400,-0x850481cb956be9dcecdf871bea591400,0xa9b815b68958f78f51b25cf19f5ae800,-0xba0a37226427997011fa9f312aec5800,0xafbacf6e8858fa42680a7db3fc9bfc00,-0x8f404fd7797b09018d25ba40cf890300,0x64c9c1c6146cd464472e80d263378ba0,-0x3d2090599db116337fc77b88f8518a00,0x1fdfa13490f9188216cec0a0f91ea700,-0xe3aed7f9d96d1d36d50ebf2537e0200,0x5688aaa581a5141a3f74d23e8242580,-0x1bc82b24e2a9670006c77cd9c1eba00,0x775783cd7477afc37675b68cf29100,-0x1a71fc4eb0f0dbe0b5bf96b243c800,0x4c1428041d41b60951d6b3a0b4240,-0xada68f0e66d2ce26b367ffa15600,0x13125dae3c44232d33f0b2ce2500,-0x18c001c898a8f3ed898f1affa00,0x1657301391bfa15fd01f058780,-0xccd07ca42cd043b7f8f95600,0x3fff5058e67e64bb1c13300,-0x82bef8751b054ca224500,0x35fbaf66768cac254a0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 17 35 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 35 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 39 indices rho q4 m4 4 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 39 indices rho q4 m4 4 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x7d70ff3432c6e504008c220c4000,-0xb2909ed4160391ae01d68b7d0f000,0x79f4ba473dd8c67e72cb3b96e34000,-0x3532a9441df2a033d8b4d509ddbbc00,0x10a4e6a91177bdb2a84cdfdcfa480000,-0x3fa00ea49d3d353690504f082af3d000,0xc111c15db6ceaa79f9048061dab5c000,-0x1dd486038c144ee146ccc06dafefe1f00,0x3d2d5b3abc651f297a101914c725f0000,-0x6974a573dd1c2d356e3859ff15f059800,0x9a3eb586ab4a92097f596344a9f2fb400,-0xc0bc3d3b83a4b99de04330762882e1000,0xceb48d4754a64f5255dfd41a34e3ce000,-0xbed4fda790d6b9c6a1aecd3767673a800,0x97ddfa6dc4bfadb9419014c7c0cda9500,-0x682dbc8a5b578495c34b6d07426aa97c0,0x3d84213bdb27c82c3e318a1d4752f8400,-0x1f2e12f448e011d8d6cdc4be320796a00,0xd81d24fe5b0ffe47edd20dbc4b77e800,-0x4f88ada911be97a65f6776f64ac74900,0x18aac50b1767a05eb3e8419abaa71400,-0x6614f2bb46f75c7ffa453724d320600,0x15b8efff1534f39eeca537ecf995200,-0x3bc81b211c10cc528553ae7e3cb180,0x81eed3cdfa524323b6ef4d5398c00,-0xd82ed1dbd710909ca529e8601e00,0x107bbe8ae9934cd937f9e3bf4c00,-0xddbb72ab2e9a579ea5c627f500,0x74e37a261dc8186a684233c00,-0x2109c312ab294e7487681200,0x3b9d4298352f45a848b100,-0x1506f8581928ba4fedc0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 17 36 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 36 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 39 indices rho q5 m5 5 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 39 indices rho q5 m5 5 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x81fd1b38f7350000,-0xb6f4dbde6d437000,-0x77db631799366200,-0x308d39697e16a400,-0xd9fb237613459e0,-0x2cf9e81d5294b90,-0x7114fcfa2715f0,-0xdd3a9d189e698,-0x1550519b40e5e,-0x1a0a85c35b4d,-0x1939607cc24,-0x1343996fc7,-0xb75c98ae,-0x533147b,-0x1bc5b0,-0x65c9,-0xd0]
def m6 : List ℤ := raw_ints% [0x0,-0xac7b5ee7c5d17ae580c0aed0d8000,0xf2158429d3046bcb6172362c64a000,-0xa2f21e31f1a6f96bc95d8f4766b8000,0x4603f7362a571bef1c00b2f77e8e2800,-0x15913b4f267904b01f458b053318a0000,0x5120273eb1882d639d4666d3274dfe000,-0xf21722ccf3691033e08f9037335b6c000,0x24c298f4d9301acc29f72a8381cc136a00,-0x4a0a4e09e432f276d031182d0775001000,0x7d402d4c3749a16651bb9d11e2280fd000,-0xb3a37f104a5a77755c0949a3ef1863fc00,0xdbe8c746abd760bd614eed91d1d75f2000,-0xe6d6571666c343e5b52fd587e2c4a6f000,0xd05c2d5d226d843f3f2abda63235cef000,-0xa1edd35df8ec550c7524d090a68d5d6b00,0x6c55d5ea97d44f6f78d047edfb7913ca80,-0x3e4c682ebd16214611573fb98a9c6ab000,0x1eb36a21a9b84b3ff77c94ec5e01144c00,-0xce82544b7746cf14ab797fb7551c5f400,0x499977da45b271adc326efa9aa5d61600,-0x160d5eb9e9a22ed4c877086634c45a000,0x57eab7ac479cea87015d5adb925ab400,-0x11f692cf2b57c9a6c76dd0e0a9080a00,0x2f47d5f291ccc4cc4b49192a7b6d100,-0x61d09cb6031f630b4a271c82466000,0x9a00e520ca2e0d4c9452317c9e400,-0xb07afc6e101d98700bf5a230f800,0x8a0e4a13c4e629e6fa6cf213e00,-0x42deb540afd5695cfca0af5000,0x111250cf344aae66d6caf9c00,-0x1b2be230d1e7f9fdcf8e300,0x82f43193e1d660f19e80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 17 38 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 38 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 39 indices rho q6 m6 6 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 39 indices rho q6 m6 6 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0xd0,0x1]
def r7 : List ℤ := raw_ints% [0x699da61e48db100000,0x9424f5897fcf960000,0x60ab4ba74e0eec3000,0x26fae3429ed92ede00,0xae13393957c726200,0x23b111745d0590b20,0x59116f096a988770,0xacae4fd4611f990,0x107407b11927bc8,0x13d387969fca72,0x12ddf625a9633,0xe1357e2f59c,0x81b836dd79,0x382522332,0x11671005,0x382e90,0x5b97]
def m7 : List ℤ := raw_ints% [0x0,0xed29a27eb00008fb9108f05f290000,-0x14858d48da76170ca8e91c1db9d5c000,0xd9e8b60a99c881e87e2f424885f10000,-0x5c46231cfb0d0ad031464e69dd75b7000,0x1bff2862f71bdd4e11b04603914efc0000,-0x67ab6af4532647ee889cb90b8c4f714000,0x1305cf41900f48547d32144331d34714000,-0x2d7070b496faa36114ff1bd8cad854e5c00,0x59eb83ad407097f01611bdfaba35c2bd000,-0x9556c51f7dbe6544431dab5bc9736f02000,0xd21b25fb0b9393e7d6ebbffcae7ec8ba400,-0xfc14344505c24af5994ebbdd3cbb0cb4000,0x10312fb0efd1494bb2ad8dd8e3463b6bf000,-0xe4b5da366012d16363db679b81e72ed2000,0xada18fa259f843e7afbcd14a3d8d431a500,-0x715322abdceadcf746a66059bbf0a567700,0x3f7add8fe80b7c620cebbb7a025709f4800,-0x1e6bff4d3095b01304ad1d3ea375bb3d800,0xc69f318cf10f2b650c46ee4d757120b400,-0x448f8218a80d794c01e1dccff95c0f5400,0x13d8ad2ffdeb5837820389cc8f19475800,-0x4c38787d6b4c5fefe0b369a1fa8a0c800,0xef37e1f670b2bd1bed960d5e09cc3e00,-0x25a0931ee458b70a6ebf1eab99b14600,0x4a10f526ce72d135ada43e83a79e800,-0x6e491101a2506cb005c23c4646c800,0x769f0569e8a13f579daab830c2000,-0x56407a721e589762eff67b852400,0x26567491ee5955825559ca63800,-0x8d3f04d63175160fc57f2d800,0xc6114ffdab0fead0a23e500,-0x32f007722844f4b3c3f00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 17 40 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 40 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 39 indices rho q7 m7 7 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 39 indices rho q7 m7 7 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x5b97,-0xd0,0x1]
def r8 : List ℤ := raw_ints% [-0x2e81a4f84e79a7430000,-0x410b56efa2c090871000,-0x2a4d89ab4ce1e453ce00,-0x10fe2b69b5bd5cba8c00,-0x4b8d2a88b9918a4c520,-0xf6949b11c4ecc55ff0,-0x263a1836dda1813570,-0x49953c79d46d671f8,-0x6f37112840250e02,-0x849d946fa80a04f,-0x7c90db765e5f56,-0x5b68594c35f61,-0x3386fb4884a0,-0x15a957ddf61,-0x671865926,-0x1390be87,-0x1cf7d2]
def m8 : List ℤ := raw_ints% [0x0,-0x146193f6e32000c59e76c4a82d860000,0x1bd8be6b93703e497554b9b3a194e8000,-0x123ab8f1389a1bf4312f26603b897a0000,0x79c4ff5e14da3e48bad5588c7bf467a000,-0x246814c075f05af10d22397169ff2220000,0x84c475617d2ef577ddd7de0d31ac3578000,-0x17fa6509742d2ce1a87c072a754af7cdc000,0x38562f275c4333ed8ab62aa1f81ff794a800,-0x6d9414e617ba60f4f0a95fa3cc8faf41f000,0xb2bcd27dd61d981097d492b98979e8188000,-0xf6c4e2694f119cb22e6f66160545fab29c00,0x12244bc5c82e551597eadf684e9f204308000,-0x124300d05e7df36c1f1b0174ff599f6f85000,0xfc5baa565450dc98293b96636babc80e4000,-0xbb34c6a9fab7d4c7b4fb734205d13532ab00,0x773af5728c1d2fc1f5cf6befe23ff9838a00,-0x4112dec9cf961e9931a2172fcdf001838800,0x1e5545d1eaf25da5108a107b4511b81f4000,-0xc040fe4cd0ed161d2c0ddeb3d68e20afc00,0x4047a4523f1a1a631111923ddb9ba284800,-0x11fa2ad90af9f2370d544da853b8bfb7800,0x42817ee011f628af97c42eb1e34de1e000,-0xc85b8d94a68a0298eec25361f8a4c9200,0x1e1fed9b89579bfbce5a65a2ea055f400,-0x3865986c8c423af3a6ef47054c1c4800,0x4f5f39f8ab760fd0adda90b57aa0000,-0x5010a59b40eb99f99014f2737cb000,0x360e9750df5e71141ed12dadc4800,-0x160597f1154044dab2f60e36f800,0x491550c9e0b404fb0c533f2000,-0x5a32bb6eae91621eb5ca3b00,0x13cce5005f417f97be2a00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 17 42 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 42 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 39 indices rho q8 m8 8 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 39 indices rho q8 m8 8 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x1cf7d2,0x5b97,-0xd0,0x1]
def r9 : List ℤ := raw_ints% [0xeb584d11f550aec7a0000,0x148562bc5b9cc84b1ee000,0xd4efa7e382d614ea35400,0x55424d41c5ec9527aba00,0x179a994988c33b76e4dc0,0x4cb523ca1016dee32700,0xbd52f13976263b52ef0,0x16a4f0b2eb7e52e7fc0,0x21fd5ab22d2c2ce0e4,0x2832514200166e8d0,0x256140a576601421,0x1b17a1fd0d86982,0xf093085134827,0x631e3a33ebac,0x1cb3fbf3fef,0x53fb075c2,0x75da6b5]
def m9 : List ℤ := raw_ints% [0x0,0x1c062b73784c010fb9e34e673e9840000,-0x25cd7ac7a1fc89cc927f02551ce06f0000,0x186bcf667da699de625baf41bb55e900000,-0xa0e6de88789ffd8716d1ca1f3a505abc000,0x2f6c931ec21afa7229f22ec7255d6a9c0000,-0xaa65677ff4562df4be680f3b58b126f90000,0x1e4d2ea7d7818452cb388217bf3f032794000,-0x460dcced6f03a7e6fc6d0a319624ae469b000,0x85fb55f39ffd61cbaf0365a9f2a8a91251000,-0xd6b8c74732d57bf943ef8867fadddde854000,0x12304b48bc12eb4ba4a2f0f6de010687236400,-0x14fbbaeba5dd6b18800f5947ddcfa37a130000,0x14b1cf4c510e5ead27e97b5f43518ef2803000,-0x117df9a61fe17d8fbf609f4866c721ea800000,0xcaeebd27c4342265aa8810329f031ce774500,-0x7e2769b52e281a3a71df6de24c6df3542cc00,0x4319b681cbbdc2e07e2a77d8a8e6e87ecd800,-0x1e6dac50c84a36cd1538421717571e2ffd000,0xbb3f385f88bcf49fd179554283898836e400,-0x3ca55d519cfb07a227eeabc32c77ad032000,0x106307a3ccb14c4a13aaa98088896980e800,-0x3a642e5b1f14080311e227724b32c7f9000,0xa8d3f8e7d6fa85dafb943d0a8c134aae00,-0x1841e62c6b23c1d117f828b2f57a8d8800,0x2b2c03fec1f2c50d62cf439bf5708d800,-0x3964cdcecdde783c53c3781379183000,0x3640b71b40377fda4e231facc977000,-0x21fa40ad6973f9036db0d92bf80000,0xcabd1faf12fef40a689916d7a800,-0x25d4e5f35a89b1b3c03d2b53000,0x290e3c93f822a42004caf9500,-0x7b11f198e95666b9d21c00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 17 44 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 44 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 39 indices rho q9 m9 9 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 39 indices rho q9 m9 9 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r10 : List ℤ := raw_ints% [-0x3bd79577a0f70d426790000,-0x534ea96455ce3a1bed43000,-0x35e5312e8c5e5afe5e06a00,-0x158508326a13ead19b6a000,-0x5f059d9d2349e020301160,-0x133aed2af946e229137f10,-0x2f43c0a83c2c7df28fbb0,-0x5a035b5f13936f6aafc8,-0x865959586bfeb3d7b16,-0x9dd31587f93959cf51,-0x919998412ea9d1d08,-0x688416ef4fdf23db,-0x39527581185e2f2,-0x1744f1f2e15307,-0x69c8ce0892dc,-0x12dd90e4675,-0x199608684]
def m10 : List ℤ := raw_ints% [0x0,-0x26887bbec56881759f988bcdf611580000,0x335712525f4221ed37f66f2290006fa0000,-0x20be69006f12c6917cd5ffa647d0c8040000,0xd4e14ae8d1c4d53e29214024e831f32e8000,-0x3de14aa3d36cf3e8a72a9805acbfa39c20000,0xdb25df2080763914f030b4d76b2f830220000,-0x26636000909335bf44128041e0cda55547c000,0x575d057ffd2477f0bfb88d2f72f2e37765e000,-0xa45b7f49450e89631cf2afd028126f53f97000,0x102e4d200bcfd39bac3fc5650c9ab7713554000,-0x15894e9278b4ebda580189b474419d58e9d1c00,0x18603b187fcbd3c3438c7c62467274319080000,-0x178fc6b89f8b6c2492726038c1f5ea66b9bd000,0x137f11e12d0525d271cea81e027044e11898000,-0xdd24972fd0ff0fbc862b89d8ae3d7d81504b00,0x86381408e9ef65ffd720483f9ce588a79b1800,-0x4596b39e21b6fe234c9c7801f3c602c50ae800,0x1eb486a0272047aa23be95c98ad3942dda9000,-0xb779df69ee0d65434fbfbd9dfbb5b91139c00,0x39917dfb0eff923d442c1a0bd7910d3e2d000,-0xf075a2b4885897eee01502b9bd4f5bb4d800,0x3393a82c3deb886e6f2dcff3490af3bf1000,-0x8f17ec9ee15ae96a53bd49c478381637200,0x13a42a663e6bfd2df8d59539bb520532000,-0x2137768d5a684d954f34425d4caec3e800,0x29afe02338feabff24bdaa9ecba00f000,-0x24e5903fe867fb54090d9b4d917e1000,0x1569c78867733edea6d472c82f53000,-0x74d3dcf923ace67e2c39f4b719800,0x139708128cc4f1c279f91e26b000,-0x12ad8c14ee62e36a2888ad3b00,0x2fc7ac51d58144c87616800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 17 46 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 46 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 39 indices rho q10 m10 10 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 39 indices rho q10 m10 10 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r11 : List ℤ := raw_ints% [0xcfde63b5bb123ba535540000,0x120d4b5e3d74212477cecc000,0xba75c7fa3a41e5b278825800,0x4a459c1f1e1a613677a42600,0x1470f642c610b9fb0052f780,0x41fbdf561214fdacca844e0,0xa19a3e4ad83733f28f70b0,0x132824e8dc83892133fbb0,0x1c7525fcd57c25d2ba030,0x213f0bc3d51ac197196e,0x1e78fccc25d2379b28f,0x15b4ac8e0d506ad728,0xbcb51fd8452a82b5,0x4bbc4fbb19830e6,0x15371a5a131699,0x3b735bc2ac74,0x4ebeaec843]
def m11 : List ℤ := raw_ints% [0x0,0x34fbaa264f6fb201bb71c03b3257d900000,-0x45c12da919abfa7e5605147748e423ac0000,0x2bf0789e99ab3d55d09104a75fab0f0cc0000,-0x119fff90a29e69f461cf1d3c8bf2b8f9630000,0x50e0347cf0667fe88e89c019c898b7b36c0000,-0x11a6d46736a8e8d9d13f192abb9a75db0800000,0x30c08a6eb658d1728f869819819f89757334000,-0x6d4245c281409fca2607055a76eedbb7cdc8000,0xca449dce4e11b43936a3e0dd589887d23221000,-0x1394582fb1361d84539f239571558b3532edc000,0x1999c504c443c095289dc46f96bfb39f82346400,-0x1c702a62b896f5514ea67a6aab7ee9749c1e0000,0x1af30476d12e1876c07832ca0a58b796ce033000,-0x15d636f89fea2c80a5de171a9ad2fca468ff8000,0xf23c07e8d6d5f124d9eb60407e0847cd7952500,-0x8f92ddc4987a641e08954a566d4f4950a868000,0x48934f55acaf6c09ee5d9ed670d20b0c4fc1800,-0x1f29ffb94d7be3f025770135da1f01d0566b000,0xb4d81dbbe50bff3ee201cc0d30d3edabea2400,-0x36f9202be9883ad38255e190c84598cea6d000,0xddd8168cee5588f4afae0bc28dfd73fca2800,-0x2dd306b3a24ccbe97835207d52f414b17b000,0x79f7a45a340b7748500815b80ebe1cd2ae00,-0xffd036e182889bb0276c3aebcd4d05e5000,0x19ae67bcb4b30a10fb0dcb1a1ecd16b9800,-0x1e681becea50f66c9ecafd48ef2b6ad000,0x192dbbe5bb7fa96aa9273292ccac53000,-0xd870cb555cdd2afaa66f5394d85f000,0x4368a7e2cc9510290eeb9466d06800,-0xa257108f73a82c38e7f776659000,0x87e3251b4487226b010011b500,-0x1289f127de203db328a8f000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 17 48 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 48 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 39 indices rho q11 m11 11 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 39 indices rho q11 m11 11 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r12 : List ℤ := raw_ints% [-0x27fbf0e547dcd9fd101adf0000,-0x3777033ecb439b85e432d25000,-0x23bd4a23b878e5a84ab4dee600,-0xe34bbacbe8bbd0486af8a9400,-0x3e68884390fa8d5c235865fa0,-0xc8e958413523be8e48644f30,-0x1ea8e1e7526089c23dd5f8f0,-0x39f300845292e87137f61d8,-0x55bd6b899f38266d3b718a,-0x63b47f92082e74e640293,-0x5ae5482e8136a89bfcfa,-0x40562bf50b22632fd15,-0x22b2560084154cff44,-0xdccc06d9ba48e26d,-0x3d2c11d95f8dd52,-0xa917489d99463,-0xdc1eabb81d6]
def m12 : List ℤ := raw_ints% [0x0,-0x48da09f4ad3994c261bc68516538ca600000,0x5ed007a5cd14d7f96c2eea703404566b80000,-0x3b02c511f3eea031c173bbfd21efaf7b0c0000,0x1760455eaee2ce61a6fec5b6c4753b6e3ce0000,-0x69dfa8969cb592c9dd008609129822779020000,0x16cb593d2d50533a8aa1b41966fc66d4ad9c0000,-0x3e1003c5ebf99d87001396fc49ef300fad1dc000,0x89058d92a04d34eff29981e718d45459c22bc000,-0xf9b5155f2dcbe031a76ad83c6069f58095637000,0x17c66d7a7a5a4c9efe572edb7ffb7d2221f284000,-0x1e8ca76a8132333985ed32813681e121146171c00,0x215102baf4c36214cca7fd3d883de38defb6e0000,-0x1ef682b536c8f657dd8fdce72590f6d14f283d000,0x18935565fd3f7cb36a2c08affedb8807bdcce8000,-0x10aae9a9c35803b8ab64511bc8f8fa12159236b00,0x9a6513b0892bcc30ce42813a6d405fd57acf9000,-0x4c1b631a02a97f7b0f029cdc78ea719177a36800,0x1fcf129e50c8e22ef47127cf3a9f1ba5cd9fd000,-0xb3473f9b05cc6237e350158c49cd413c99f9c00,0x34ccd77ebef317140a95260a5a4fa8e50a1f000,-0xcddaad307d425934345e638d01e842f9c35800,0x28f1c49379feee86d6f0410c0d5003ec9fd000,-0x688706900f50c45e947928bd111c08228b200,0xd14d42e5ce2863f1d17344c4e0f0bb405000,-0x13f28468583b8173bc24ee794d7b79c36800,0x164468e702a955f761e0a9779fec6dcb000,-0x113c9318186ff23665de35510daa5d1000,0x89089f81ffffd307b0a9589f2a25d000,-0x26f024705866d7b4944117206a11800,0x54174b029a0ef9534d59eafc8f000,-0x3dc18802d07d732ca53a0e1db00,0x73064d7e41fcacfc8810a000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 17 50 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 50 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 39 indices rho q12 m12 12 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 39 indices rho q12 m12 12 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r13 : List ℤ := raw_ints% [0x6fc5163fb3238d47be75b4e0000,0x9ad0994fb952e81c89106f0a000,0x6397750fb65b3fab657de059c00,0x278359d2679d9cbeedfe6b23200,0xad393472680ee5db045a226d40,0x22c59e69742b6bd2fb9c425ac0,0x54ad0032e49fe7582eca5f770,0x9f8ffe5d841d81b77cf2a7a0,0xeb463cebf4b609f74d399fc,0x110852f068d70c6be075d4c,0xf750cb5071786fd5757bd,0xae21383b8ccf33f42a0e,0x5d53fbfc5f0ddfa4f03,0x24d907a6e1dfefc1e0,0xa1e8a25768759283,0x1bac7f4e0cad6e6,0x238d3b0792091]
def m13 : List ℤ := raw_ints% [0x0,0x642bcdb06e2f2c8b46630f6feb2e164400000,-0x80ec74266ad3a65e5380eb1e463fefe0800000,0x4f50a2f2257e26f7f5c79261fc97e271adc0000,-0x1f0a652baab8bede45773e550ba3ad31aeb80000,0x8ad1363d46b055065187f80cec0b25e533fc0000,-0x1d7e3f3c3d9453e90300a95883e373120e19c0000,0x4f314adf18005b9ee534034ac69bdc7e267054000,-0xac4e81de75828e889237854d82507b33a7735c000,0x13539670a8c5ae04ee5cfc8d1b5b69956986261000,-0x1cf818c9989bfc803e3fea696103f4d4e7ba27c000,0x2497b939a5b3007d876eb8599ddb1e406897366400,-0x27311fef3ed86fa6dc03b49ddda16ff71cc83a0000,0x23bb3da5a1769d2cfa4cafa2d0dffbec1857893000,-0x1bc9ac2124b1d8633056d9417784bd5a14836d8000,0x1270db7cabec35d723eea2ef6766f73712e9dc0500,-0xa6e4b1846585e1eed897caed63ffcd5265a2cd000,0x503d6fcc9d9cc69a2718f8fdae3ca2ef475dc1800,-0x20a5898dca10ebf359fb7147866467d91fcb43000,0xb2b9e94045c8c4a688eb0dd8cc951f7dea07a400,-0x33000ea86e5779cefc6366291b5fa4d70c519000,0xc0173fe8e54591d3bf86f327de8769e614c2800,-0x24c901a21f95dc12fade9174844385ac0123000,0x5a0d7b90ffe4c624b8b61a3ae20e37439eee00,-0xac165e4e110f74c1330c2b97ec097adfe7000,0xf8fde5516411ba87113c53ad8e63d3d39800,-0x105e2dabe410294f2250174efd6c25935000,0xbd59dec69da7a8adddff32e206b4e2b000,-0x56ee716b94b668238e2c403c5e165b000,0x168386e98722aa92486aebab104c6800,-0x2b8f5dcd37b00f734df7fba2551000,0x1c0d05f424f1aa0bdcd8f5cf9500,-0x2c9474c5fb07b42bea415c000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 17 52 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 52 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 39 indices rho q13 m13 13 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 39 indices rho q13 m13 13 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r14 : List ℤ := raw_ints% [-0x120d5119f5853a453d237a5050000,-0x18f8a4061a7ba89ad2c9ce5e47000,-0x100a4d6b996e021e3df07df1ce200,-0x65a805ef76b54545539ee54d4800,-0x1bcd61d1d994687ef1cd2e10b5e0,-0x591c18b5504fb1e135242c35f50,-0xd87e752203f5b15ff1550f1230,-0x196e3fc2c36ce553631a8880e8,-0x2562d50f542670a8b88d0ba7e,-0x2b287d9ee1df9f0f2259d215,-0x2703d72042cd975cb0833ac,-0x1b58e124fb2a09dfcd808f,-0xe94d6fab76b379ce2956,-0x5b8e06e688f1c412c93,-0x18f697def72426da08,-0x43af2f1f3b637411,-0x560cd92fd16fe8]
def m14 : List ℤ := raw_ints% [0x0,-0x89bc3ad29780dd3f80c83539e35f5e9d800000,0xaf600a5a06fd31595f2dcccadeec00b55700000,-0x6ab02c04859a3d0c7cc14b9833a6ade1734c0000,0x294421ebc239aa6eaef5022e67103b4236afc0000,-0xb64af5d2d1510862fda86995979c0bee66b420000,0x263beb217550116ea8eabd8f2429b2d223c3e40000,-0x654862d3f7e14c5804588047485ad80e234593c000,0xd94152f506ca66ef24f2a5c2b159f0eda4a77f4000,-0x180157401ff0947731a4cf2a739fad80f1853377000,0x236ab2830de87a890b5cf0453e71635005b32ac4000,-0x2bfe65d21e7198f53b7338733770c0e9d03f83b1c00,0x2e49fd24ce9dedc9714eb40ebd2d280d2f2ab260000,-0x2969a212d77ea4f533f93fc1012f7630f86d7edd000,0x1f908ab1023dc5d5ba1d28e539458dbb05c79628000,-0x14807917a0d6eab68f4b1acc04718412e23e59c8b00,0xb551f66b686d90defbe1db50cc35c9d15ca4387000,-0x550af85821379e0d5a83cc61381e596402744c6800,0x21b003254c0416d97256099076637f55cfb55ed000,-0xb3277fb1f58bcde533584140e83c854dbf67d1c00,0x3188876875cac7bc93bfe50d4c75d712902187000,-0xb43a123752db8d7bc91981a4aa00c1eca0025800,0x21396d12983c3024fcf19aeefe1a061e9d0cd000,-0x4df9dceb94be6943b9ae29e86faf4cc0f137200,0x8e27d0b83e2ed943682b53909d9376b6511000,-0xc3112b685f8766728e5763c3fb82280a66800,0xc12f2ffbf59ae137907a1926dfb78c81b000,-0x825c2c06d40d3e7419ff7e482a0fb129000,0x373f032ac1028e36a5fb7484eb4eae5000,-0xd0726366afd7c378e641517c78a81800,0x16904e1cfb846b846c133a25d2ff000,-0xcbc03d9aae8fe5f787f202a0fb00,0x1144be2719fd45c608710e8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 17 54 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 54 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 39 indices rho q14 m14 14 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 39 indices rho q14 m14 14 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r15 : List ℤ := raw_ints% [0x2bb18d4a3d9b2342ffec1503080000,0x3c5e9b7d22cb3d12f9665a0da88000,0x26ba2d018b406bc831ff9889e26000,0xf513c422f071f602402d61a83be00,0x42eace3ef516e069fd8d464fc4b00,0xd615fbbd9f2b697067ef07af34a0,0x2070f85c79a446b4e1c75c1b9230,0x3cd4e3e385384cfc65449d48990,0x5932946e49e713fd8d86c73148,0x66aaa3562aba563c51c88e16a,0x5c802b2a4d839b282292eaab,0x4097020fc174f521ae9a734,0x2249ab612ac056fa76d411,0xd631518c30676e40399a,0x3a0ddec2acd1aa8b1ad,0x9c4cfba89d0983618,0xc50c2cb3952959f]
def m15 : List ℤ := raw_ints% [0x0,0xbd62d0e1905130375113492f98a322189000000,-0xeea762349dfe7e61f5186e109452df0032d00000,0x8f9e036b5838a984ede7144cd10627a4be4bc0000,-0x36ec2a6502a07bfed2a50d831712b14f7b354c0000,0xefbeef0238e2d9de112ea8b9a56363a933e08c0000,-0x31a8a3548f0d3dc9ee6c118c0e7eed8e141736c0000,0x81d370c0bc85433f9718a00d0890fa9f34f35474000,-0x112a4a282a04a9ed396c89cd9a907f4daf86663ac000,0x1de7a2918cd13c7b974b2c674327284063ca92961000,-0x2b713eec0e3c4425044664f4c48c49c87a02d537c000,0x351569813249494832a37002789c20766903a1f06400,-0x36e30aa5b71fc861b4dd7fccc24555c2d66d14aa0000,0x3033589afc4408ba7404802cddb511c92969f35b3000,-0x24043cb87cf51e6f633c89b11817a9375131ef058000,0x16e6d2ca22c82ae768bf430a0f0d3dd48e07b296e500,-0xc5f951c7a4d0201f06b750af1b47407f672920e1000,0x5a98f28093eb63ec6d82691f7d963e0c1c4b9971800,-0x22f1fd551491d4a5356c8fa57c088520f9f30683000,0xb48bbb9e636f6b70d0280a1421c4b724b7c33e2400,-0x305df57516db08949055d68fcb8e33ed5a72869000,0xa9fe399771ab554884fb2067b251ef0b60b792800,-0x1e29ab69671914269465b83278e2a6183742a3000,0x43d965698a0950a6bccb517411f493fa54242e00,-0x75f58fd0aa3e06d02f606eba5005d2f50e8f000,0x996e2aa1f43feb10da59b21438464c8ea89800,-0x8efa885f29fe151847ca833be6c1bdbf75000,0x59f912cc9b03e3bbe58ae4ecd3ab3bfb3000,-0x232a80a6c4d1827551da359d6086eb2b000,0x78b3e96836ef361c9e27c0e4d570d6800,-0xbafc552c81c4981cc1631ccb53d1000,0x5c72c30a0a31c7652df9040547500,-0x6af89be9fd0819b93d87df0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 17 56 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 56 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 39 indices rho q15 m15 15 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 39 indices rho q15 m15 15 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r16 : List ℤ := raw_ints% [-0x640df482cd4c82da55d0c3d62eb0000,-0x8a1807ca42425ae95f9ec32fa0a9000,-0x587b9cbfc519b8e6205c6b826285e00,-0x22f359771b2c9f0d70889147ba17c00,-0x987763dd6b0ad2c9c6b88a670f7420,-0x1e6fc64c0371f1eda3af1d4cc47370,-0x49a927ab70e65d15bf8808d3c1b70,-0x89d7a7e81c020186700b25d14df8,-0xc9a840ae1dae45b9e5abf5b03f2,-0xe782cb44d6985d10eee0b3c0d7,-0xcffb03db41475b403cca2641e,-0x90bee17c9b80ca6028c48f49,-0x4c8c843b52ea7e774a27428,-0x1dc1f049107f24dda28e79,-0x806629b9e7aa0f385dfe,-0x157aaf383f1eea35f7f,-0x1ae455e657a2ee3ba]
def m16 : List ℤ := raw_ints% [0x0,-0x10467df36266fa24c0f7a84a171e04ee1c6000000,0x144e2853eefff0497f8ed00367050ce09458d00000,-0xc178d1bc9104b12149716446879e1f7de1586c0000,0x492de50d768efa1007cffb2f5c29fceb07458940000,-0x13bc570d9a668a1041394fb365553588df2fc2020000,0x409da398593450e898bf533ae6996d548fb078a40000,-0xa6c7568427bd05636fb79feeb3945500acfcbeb9c000,0x15c134936e27a31e76c2de67cd24e779e710915954000,-0x255cb6b23c7bd043a9a310457865085fc71952f637000,0x35756eb942df894558d132e3905c4efea537f44544000,-0x40478128884e94fe9e12062be20bf435ec28d0f831c00,0x41554644c275e19181dec76418efae8792ab168060000,-0x3855861e0b94111ffbe3437f9d6f0e9e8f663c71fd000,0x29472e71da0af36ff0c8457eee7ec430fe8a28ed28000,-0x19b39cb106ca891fa51fdf518ae45d8c3ef3f16cdab00,0xd935bb1ca6de13a0796dd108239e52f8d33f709df000,-0x61005191045722d0d00a7341698d3cee8eab21f76800,0x246fe642fef97b59618e6d4512f6bbe2e05656ccd000,-0xb6e65faa05c9f24658208041bd0c0b9406697309c00,0x2f79ae9c4f3fd384013f749c23002aab67efe207000,-0xa12ac980a5390aeb04d4852b460d55b79fb9135800,0x1b8519c1d0e0bf47402dece67cbe447cd5f822d000,-0x3b50d809ec0b1e28c973b5ecbc0ca0781896c3200,0x624dc7d68f6657fcb78f6eb8fe1532755ece1000,-0x79233c554d0a6f35ba279199e1fc0871ac76800,0x6a2672d035b9fcdac59ad43352bde77da3b000,-0x3e3df6d3e5b0e37c24d00a9f9c70d37b61000,0x166a9b44f13663db3faac5459e6dcc1a5000,-0x45eed781d73906b016a5fa5e57889d1800,0x60d505173c62884a4ee8ddf47c91f000,-0x29ec9af186af187a96310a18c21b00,0x2964ee66590a05fcb9e4dea0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 17 58 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 58 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 39 indices rho q16 m16 16 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 39 indices rho q16 m16 16 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r17 : List ℤ := raw_ints% [0xda7a5ce07c7abd9de8fdf81d9b820000,0x12d3ffd7d204e8f86f845e3beec646000,0xc0d17a48c5b6c26ae9fc1c472c5ea400,0x4c12a49ac8dffcdbf8b0a0f501b6ca00,0x14b6b8d2a672976b20542df6765970c0,0x42107d94913711136633d0c4ad22280,0x9fa01efae1c5d013f73dab6d354cf0,0x12a2b3e937e1faf4c85a6ba547d580,0x1b3535164fe9bc2bd8ab75d63bf14,0x1f2a3716ce4a4fbb050de63d0ac8,0x1bed095c4acc56abb45b9dfd059,0x13611664b01bcb4bef4c660f9a,0xa37189352396b46c2eabdcdf,0x3f4cc2bb472090a6bce8714,0x10ff5619e295c711f2cf17,0x2d44ee03e5cae5ca310a,0x38598a3e65a8f4576d]
def m17 : List ℤ := raw_ints% [0x0,0x1660ed2ea74d97f289548765dfc946c76704000000,-0x1ba6eb2de2fdc1443a4aad9f0622b9b468f37900000,0x104d2277a58d14ec248113808df195486fe30edc0000,-0x619c31f127285c6a0e9fe597897bfa44ba1091fc0000,0x1a080ecaeeadcc993697afe21706f0e5a6819661c0000,-0x543a8fbf4855f84ce88b349e847de264d006ce48c0000,0xd6b5991800ee11b16d4871a96753d1ead45ba22d94000,-0x1ba3dcc79d66b3e61809aadc51488b22bb8b36d8f6c000,0x2ecfb5588aa135234bef19bd3d92bc665c0818f6e61000,-0x41fe183b104ed35b60be0f4aaa74a115d22de43edfc000,0x4e1b6cfe43cddb882ade922efcf6b71bbb9db3753e6400,-0x4e0fccc57e34ba68e28224c70ba182b9dfbdcc382a0000,0x421ba0b9396db4c5ed8f53e508da81739b1aaf857d3000,-0x2f83588fda0afa78f73a1df7d4e2d1c93ff5783f058000,0x1cf9c09f5a0021daaa5d53b1749321441424c93fb1c500,-0xef738c968f5069169ec4e876ca10216ec79a14a4d1000,0x685eaf843fcf4652871dd3fa002edc81b6180428e1800,-0x262f3373b2e90753085ef4b2f2914955f08fdd1a63000,0xba3b0d746548b8d223bef3226f35f88de72a7500a400,-0x2ed66baf87ad0fa1e20d36fd4055ed5f7133ed9c9000,0x999097027d60ac6f4ffe3c9db2b8d5936ce45122800,-0x193ad7d0b29ec09179a4d91d5a0efe45550cec83000,0x34174bc463d7906c39d67f13b2b3007b8a01ed6e00,-0x5243087b3719e302e9a3f92e8b108b4d6a0d0f000,0x5ffc1b5cd1f6760a01fcd4ad4d0a865070919800,-0x4f09a8a0c2244e11f3e15c3a0e131a994195000,0x2b2657e0b61c5fc8f110017864c7a7b163b000,-0xe4eb58a42654b834dc4fd3b07344654cb000,0x2889407f9cdca33e41c508964cdfba26800,-0x3222a24929d9899ef01db5c0350371000,0x13008664be4732e6b473677a3355500,-0x1002aadd6b598ec1424b8c9c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 17 60 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 60 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 39 indices rho q17 m17 17 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 39 indices rho q17 m17 17 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r18 : List ℤ := raw_ints% [-0x1c9cd5250c797c646a0f7459c844910000,-0x276b13a8ce38c3080a8c6bd27f9544b000,-0x1934a9ae99bd3b8e57000ab48433115a00,-0x9ef0e65b6ea9b2cd25699ecb185013000,-0x2b3a037dfe361ccd0a89dc8e8d59e9a60,-0x89afa649f5d61d53cdca6384da29ab90,-0x14c31cda42ccf939d9488703e906c4b0,-0x26b83145d79b576ab9f6ef3e0f53d08,-0x386db0a431e9c9a4f4ee860c15b9e6,-0x40815aa4bdfbf6d954dfee5f5a5d9,-0x39abc4335d1203f46efab787a950,-0x27eb638d6455762589d735b0443,-0x14fb7560b17b9be4c28a89deba,-0x8198ff5ebee477397ee15d1f,-0x22abd671d6120f6eb53fa34,-0x5bf2de694ca8ead66bbad,-0x71e50821cb82d5f164c]
def m18 : List ℤ := raw_ints% [0x0,-0x1ec54620260ab0ed7cd43a2c13b4c1522da58000000,0x25ab8b43d8b813c2b874f7353c9235d78e560dd00000,-0x15fdc8510a059bdd0752d0519ffa490a19e75ec0c0000,0x82559b3b231add0d1da2f0013a5db3c53116e4f940000,-0x226243208c2c74e5fdd5fd5d337fa3fbba08f0f3420000,0x6dfcc1ae39fb078ef1b090121fc2b60874457039440000,-0x114fea7a27c234895fb0a1b6010fd5a1693ecc59a4fc000,0x23340950879bda7ed85402be7d61a5dba51f6440c654000,-0x3ad017b0b0ac4e52b5cd38a4078db6f2ca8e447585f7000,0x51b79b918fd91ffb691b91e2d6c69555c360d897d0c4000,-0x5f3ba9da9889dadbd1e084b2c5a65065e5e3e971d771c00,0x5d9daa812e31e82f0b879c73cde54ed9424369085860000,-0x4de30163876e2a21f2e75c8e5b5524d1ea54b1f6b71d000,0x36ec05d4d6978f1580e748f4017f5510dfa7bd936328000,-0x20d011e99fbec5836b0111762783180dac8931a201ecb00,0x10933fd46aaf8233bcdafa4116f0741d7d59ac21481f000,-0x70d71a6c107ed1d3bc8ce7145a8cb32dea4781597a6800,0x28367fca676c4a90a688f5d47e54b257a0c99c23d6d000,-0xbe91360b70e133f4f7430d1d168b25ff59888cd6c1c00,0x2e7016d78fb8be4573a342475222e0f0603693c7e7000,-0x930872215192df184c72b377c0265cac2db85d4c5800,0x173d07d4979c8ad32db6e36f79af67cb178e69fcd000,-0x2df23169c89c1ff3b07675c69ff7feb2794beb4f200,0x451c02ba00eef8fb4e2028d5dbc83ef9ee41741000,-0x4c5022ea80fae956421353f92f82c5f0ad2806800,0x3b02b0b0ea861e8c326dd08b0346a6427359b000,-0x1df8e1da139589eeb063ea8038da2b9fee59000,0x9246260da593b2d39b9f22eac5f3b63645000,-0x1781391f988a4d5e71ab9a043fbf630a1800,0x19f39ba9de1f8d4fe261a92e79403ff000,-0x89bac6d91212a55f89a281e71233b00,0x63087dec20c736e10e71a8680000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 17 62 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 62 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 39 indices rho q18 m18 18 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 39 indices rho q18 m18 18 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r19 : List ℤ := raw_ints% [0x39d5048e90e3f53aaedef2b07d2f1bc0000,0x4f9bf693594be0aa619c599f05a87144000,0x32dc60912f823eb2330a4b87a14f14c6800,0x14067b9bd5027446dbfc8570cde09bf5600,0x570bd0d4bffb2c7c4f87f81d539062be80,0x114eec37730420cf6dc25cda0f59923460,0x29b474a3ad2a20f6183cd4cf1196377b0,0x4da9aef32d0b462ea132bc5594c8f370,0x7100277840a4f6d49c75933de1c9d60,0x80f163f447e170533328b8498b2666,0x730cf1cd0b35d3f899639a851e9c7,0x4f7573b3a14569dc3f8ce2e07440,0x29a8d8ac6a2391dfbc4b381926d,0x10094cd265f40d751d8e5db14e,0x446c226536d659aaeaf7bdc1,0xb4caefa6de65b939d7eabc,0xdf00f261e8ab80fffefb]
def m19 : List ℤ := raw_ints% [0x0,0x2a4f406c344eb3468ba3cffc9b1889d0fec390000000,-0x3355c9d986c8c2522e87930a15b6458fb91fe0c100000,0x1db01193689dc90421c65a46da96e5f05bb209d4fc0000,-0xae354f6793079f3420cbb16241dcf6921c15532e9c0000,0x2d7a707cfd2bb450ebbdb24bba84eca12ac735e1cac0000,-0x8fde720f9105d13e882f710a65e26c83386a5322bec0000,0x16614a2b033942db06c1dba53af0cf26c283456a29bb4000,-0x2cf15a2e93542b3b96f2face99c4c914a0050c71e8aec000,0x4a176ff25c0014f318229cd4c608e23879804149c6e61000,-0x657ec813e02dd4e3e3260c36e0b7d51b6adba713c6e7c000,0x748062a384e1526e8c413849e0a3146425d51f7a81b06400,-0x70ad4606c47811a2e1328b6b13a83b815dc0707a7a6a0000,0x5c1f6580659ab95fde0eaabf20d228dfe79622736f7f3000,-0x3fc009994dbfb5e8d663c73fad299a368db28be2f3a58000,0x25522b588200e0d8ed240fc9632f9d9621bd85f39c7ca500,-0x127115f320d2ccbb855663c7096a20b1ca778aa0e24b1000,0x7a930d3c1d12a289d0e6b7ac2aaba89b1b47d4ff0e51800,-0x2a8db12c0a3dde4550f7426b07bf1b97a707a883f0c3000,0xc3f423b747699e246d6687ea96fa09f4fb8a92da0b2400,-0x2e43a4b71f3122b61353271b9d6fd745bd41ef13d69000,0x8d71bb223d9098f44f158edeba22d252130eae57b2800,-0x158037daccc6a21a70cd0a3f1f9826984dbe3e0fe3000,0x28b24556ed7a904b1e21c40571ff395200e5d3d6ae00,-0x3a475abeabddddd116c69d9d5922b430ea4d8bef000,0x3cde2c502e938fe2b05d04979f9626e13d060a9800,-0x2c2b7bc986819857c31098df10753180826335000,0x14db21b9ac37de9e1ebd1fd04304b717baa03000,-0x5d8ee150108fa3c3f98731bdbf56a3c53ab000,0xda2000164aaba39a72bec7ef41033de76800,-0xd6e022fff92fcdb940837907335af91000,0x3e5c41bb1d99a915d1c5f7ca79b63500,-0x2644b5796b640f31ed9b042f00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 17 64 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 64 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 39 indices rho q19 m19 19 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 39 indices rho q19 m19 19 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r20 : List ℤ := raw_ints% [-0x713bf5c99a1ecb831e5d55ebf3ebf6f70000,-0x9bc2a87749078acf4e2827cb99d7a882d000,-0x636ecd63939d99d7f036ae11e5f84479d600,-0x271d6cf1e3c691ef27e3e594f201819e6400,-0xa9dc16aacb92df0b7e1691eaa95bbe108a0,-0x21bd1eb9afed217ea8797651091ac8337b0,-0x5132c7378be7163f5ff85399638c946df0,-0x97026baaccabe4f1903bedabf1ccb1618,-0xdb670552ca68b76093a5308f739e825a,-0xf9f40b747cf43a8c7e33850c0b5401b,-0xde9fccddb3c04dcc3f53b136456e42,-0x997271fd6e06df63efe65f6adaa7d,-0x504581d9108d023a41a54efddc0c,-0x1ed27a3bf850e3461303530b585,-0x832371c31fcc3afdfbd45cfaa,-0x15966b6fb5e6ff82689ee99b,-0x1a87f1b027e9b8b427229e]
def m20 : List ℤ := raw_ints% [0x0,-0x3a2cf894c7ec368100013dfb5541bd7f5e4ce60000000,0x45faf924291f5693742945090709fdc73ea65f19500000,-0x281aba02d622134f9184892ff8c4267727aeed6c8ac0000,0xe915742c282eb62ef874865d847e63a13e1103360340000,-0x3c3b9584f27c70659c9babea59a05dcc57a609eed7020000,0xbc806bf10a30f47e99cdc0734cf5db80d3347bf506640000,-0x1cfd42892953e7651e4d2f5669f7c1f61f6a91d15b6d5c000,0x3982ab64da67c611fa2a5ca02f163c1b4ead00e1eabdd4000,-0x5d963391f2472963480936522b60816caa1e41c46e38b7000,0x7e6f084815e544c6c5298179bbb9f3468bddfc7a069044000,-0x8efc42e2a61eef08993bb09890565b56b60ce7b1823171c00,0x8819da28ec525f35af269572c14287836a904e322b6060000,-0x6d60a242b586e008f338e71158089b4b91fc59274b243d000,0x4a4c84c26b044da8f979c6e1b86c7db8436256f535f528000,-0x2aa181a70db315c0b4ff95108a68c94d067bedd39488feb00,0x149c44e0d51dc0eecf424df1935ae0c891530eb56194ff000,-0x85c39ccae2c1538ed625d8326fb19f03c5bd5064302d6800,0x2d3e26d4e782ae3375bd17cb2395c909f6ff49d63390d000,-0xca731c0c9e77b3e3bbcbb0fa178ab0a9c0688ed3f679c00,0x2e4ef65bc8315bbdc69adeb39d6ac4cce41300c3f347000,-0x88b13ffd3e5c012241170f718c32515b38d19562c55800,0x13faeadce5f33e3aeae72888596b090ef3cb1163a6d000,-0x2431332d80a36accd586d9475b4d8f909276f92a5b200,0x31527b277f07c22e4c5754ffe771e8655e2dc85e1000,-0x30b22c2c4f08beaaf03695737eaa7fbc6c130b96800,0x2123c1d5fe37d04cc892405d7fccaa9179d21fb000,-0xe89396f81817ab976763a97650b794cbae091000,0x3be46cc86d416127a8b1a6ecd680e3b23265000,-0x7e8967771c36ef2cd20846daa1c3520571800,0x6f29c35838ef2693549eeb38c70275df000,-0x1c388242a8417caabb5adefbaaf6c5b00,0xec7f733cd9016644926304ca00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 17 66 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 66 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 39 indices rho q20 m20 20 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 39 indices rho q20 m20 20 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x1a87f1b027e9b8b427229e,0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r21 : List ℤ := raw_ints% [0xd78bbf5dd0d5322b3594af66b4b109cb60000,0x1284ca3927a43d47e5efdcf785d9e47d882000,0xbd02b4131857acc36f637315fb5430e11ac00,0x4a4b156f591cc88a33a042dfb8ca58b476200,0x14256c05fe03a13553e8103fc7e40a1c0d440,0x3ff67bbed6465834b9b5a41f49c71294ba40,0x99c5c99c71adfdb30fe7c3c48ab00163270,0x11da4246485f2b1ffed10c6643ab1ab4b60,0x19e77586bb1cd5d160ebace7adb76c8e2c,0x1d77eb315f9d6542cf504d531bde92944,0x1a344d71b085d2d64776a2b12a671ff5,0x12078c71a7d6f18ab1353df8cd92e26,0x969b23b91597e115f4b21f7e7f5bb,0x39b34c3a2dee52ce40f97226f748,0xf4e29d5fb0be4d5d0d94a258ab,0x2832fbcfbdf5e51371e7f1e2e,0x313f7420f344a3513c34549]
def m21 : List ℤ := raw_ints% [0x0,0x4ffdd5cc92e4caf16001b539953a648f21a9bc40000000,-0x5f6dab4a9d45e9fbf8363e2c0fbbe87e184797f7b900000,0x3636010ac10303151294deeb211833ce3c2ad055561c0000,-0x1382904600999454eb31c3be3e4a418af74d7125017fc0000,0x4fe0adf6938d1cd0c51930fdbeb29f2a024ac1773e83c0000,-0xf761ea41dbae8f8b4f7fc07d5721567f32c9f811bdf4c0000,0x259fa8c53a093c910f140b984aca7bf15078df72adc86d4000,-0x49c27e09c9ae65c88643d710efd5ab53aa97dd1d9edbd6c000,0x768485de779a62b164dba85693b01ed75ee074d9a468561000,-0x9df4d82a5433725a797445cb50d20aa4d1c25ec8d4b76fc000,0xb00d07682f682ed519a484c9b11f18226e8edbdee7f5266400,-0xa4f797bc1f86f6a7426c01c6dad42a0b70f60f7600252a0000,0x8259de7fb478c534808f6abd604fa6767dc4ea46ec67a13000,-0x56f05eb30399ee2edfa843e0b42f579707bf67f18086c58000,0x30e6b7a058441d37c2b7850fe30feef4e4adac828a90578500,-0x1722a066dfd9b713a6c022ad9ab5f18fbedc09d0b0d6251000,0x92a2e3e7d69cf05374e8d871be6a293cd83fb525d506c1800,-0x3052f1bada76fe960ce81872b668089d1f1f6ea8f73523000,0xd2219a193a6e3c5b62482906c89ea74359d40fa7451da400,-0x2e90c273e88b7458136e9a45ce82ddfe13a110fcd3e09000,0x84b052b7d953e14b1521b888cfec6027270b2c94f442800,-0x12a53a87ad16a92bd7e01c8525faf6931e1e09167d43000,0x204fc0aa8d1903762213900693c9e9dcb4f5fc9edfee00,-0x29e2a2621b56a3abcfc0b28d4043341d3f73a1e44f000,0x2711d376ae4b6488bce1c49b37a591069ca967439800,-0x18eb287174e4dff4402f246eba3bf81ac2b1ded5000,0xa2567204c3e940550a3e7c3c9512da1aec510b000,-0x265e9224438c31e1cb46b2722db23551dab8b000,0x496a0584601ad1c4f75cdf3bf04339204c6800,-0x397d91069cf93755c0a269531368e09b1000,0xcc3c2275d5ea5efa772b8ea2afff71500,-0x5b4ec2f01ae642ca0508ef3dc00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 17 68 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 68 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 39 indices rho q21 m21 21 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 39 indices rho q21 m21 21 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x313f7420f344a3513c34549,-0x1a87f1b027e9b8b427229e,0xdf00f261e8ab80fffefb,-0x71e50821cb82d5f164c,0x38598a3e65a8f4576d,-0x1ae455e657a2ee3ba,0xc50c2cb3952959f,-0x560cd92fd16fe8,0x238d3b0792091,-0xdc1eabb81d6,0x4ebeaec843,-0x199608684,0x75da6b5,-0x1cf7d2,0x5b97,-0xd0,0x1]
def r22 : List ℤ := raw_ints% [-0x1901aa7705d54d2da065c03c0395a3ec71d0000,-0x225aab96d0edb69d1b436f30e89c67e08b4f000,-0x15e666b02ae04f7bdc3ae00ebadcbd48163d200,-0x89a0e107cce119754127413d2dc638ec971800,-0x254a682238c708c3c607c13f4e7b445e7f9ee0,-0x764a494634d236bc9ca9af94c6719871387d0,-0x11c1a426465ca2a67cbe3553a3edf514a3730,-0x20f2b13fa1b02f5dcc8a510c87738124d128,-0x2fc03e98e772fafc28ad2cc5309a64bc34e,-0x36400a963868b459b5fa827996cb9d069d,-0x302bd5b88886dd9b0aaac9698b6a975f4,-0x2117232e927dfce4e4e7b5935bb0c4f7,-0x113ec2d897c9fed81964127d783171e,-0x69809f878b9e1aff0134329aa9cab,-0x1bec54b6cdd55e9e4f514f70c760,-0x49286b561a48b657507850c249,-0x5960226e433eac21410b4bb0]
def m22 : List ℤ := raw_ints% [0x0,-0x6dfd05f949fa970be402592f2d304a44ce4962d80000000,0x822bceb9447556970f6f4c801f94f8d54e3028ca12d00000,-0x49534f2dbaafd560e5e4b5f2edc5c50e70d55f6b7504c0000,0x1a275a5fe9b9ba1203f3a965c8a27dfb85efd9b4f45c540000,-0x6a1050ebff98d37aabd87744e3d25331ae532cae012d420000,0x1452b80a631d414a8a7fb8ae7555fd3b5ebd9aa9dba36840000,-0x30ec362d71893730ccc7880c0c8811bffd2bef8a74e99cbc000,0x5ecf66ee442b6c0f93bba459b0b2b48a658c9e2a581b1f54000,-0x96784bb9867aa94e8dbf06ff5a9fa3ee9cf0f23fc5878e77000,0xc5e5dc0f5dc23ae73078dc6448160d9310eee276f6dfafc4000,-0xd970ee06cad58b1d9bc83c5a7b8a28c8562e159c5883b431c00,0xc8a334b5a901cba83d15161c106835afa1b3d3747bab5060000,-0x9beabfddf8dfe8c8b06874208dd3fc5f2441f45ef6d7015d000,0x6620a210cbb20f150e8257ab381605c95f4d271653d63728000,-0x38534458fef6d82b1cf8b777891f08fb27e8baa17c0b3810b00,0x1a14c2ae8627af30a2c6c1896408045d2771718aedf17c5f000,-0xa175bbe98f47a58295da2f25588024e55b6153e16ea3306800,0x33d918acb05b73921fae093700f8ddba8b2849c9e039cad000,-0xdb17a150db94b45956d2d42ee338a9b3c37a27881bfb31c00,0x2f08849c84b06170d4bb12c6b9c959a1e20d04c99c50a7000,-0x815c0cdc975a15405cca3106010cc92031082b3a145e5800,0x11788c33978995c507eb980ca0f7425bd2fa8e633ed0d000,-0x1cf45f9337740b0b5291d7970dff6aaa5c24e50650e7200,0x23af98c854374d9259020a22b2bc887bd1035c8b981000,-0x1f6e4416c2917e3535a2506911b3a3bb1abaddcd26800,0x12c66c1a2bbfbd113c0f93951f5299d53e9b0865b000,-0x717641000561bc015aef741dcc5f39b3d184709000,0x1898c7d10a5212c538e3148142b96d08dff885000,-0x2a9890aad3db9d2860fab187dcc7b0766a41800,0x1db8f4ab823189477f04b14a026ef88fbf000,-0x5c554921b26a3c013c39f2eade482d7b00,0x233ccfcee552e0d0786312a7e800000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 17 70 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 70 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 39 indices rho q22 m22 22 78739978916568547049472000 22=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 39 indices rho q22 m22 22 78739978916568547049472000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<23) : intPolyRF (mz e)=rfPoly (C (78739978916568547049472000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U5C22
