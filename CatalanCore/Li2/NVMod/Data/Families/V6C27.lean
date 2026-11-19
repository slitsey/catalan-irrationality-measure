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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C27
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,27,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x2c7ab485a10ec1ad00000,0x45e17f578319141050000,0x33b37494e8e1eccc04000,0x17f69d262636fe1d9ac00,0x7cef50878d2e97790400,0x1e70faac74650c7ae340,0x5c2458a8892ed144b00,0xdde9e2f1fc62b429d0,0x1b0476932882702ec0,0x2b0840b4f5db05c8c,0x386b4ab2f10e4f10,0x3d1718c179e0473,0x36a423aabc3d90,0x2841469f3e7fd,0x18461683e720,0xbdb20e686e,0x49dba7660,0x1660c506,0x5156d0,0xd07f,0x150,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0x5,-0xb,0xb,-0x8f,0x743,-0x244f,0x4fe1,-0xbec9,0xbec9,-0x19789,0x7f5ad,-0x19789,0x1182e3,-0x200db3,0x200db3,-0xb194f,0x1277f]
def rhoDenominators : List ℤ := raw_ints% [0x444b2709400,0x11d707100,0x1e0bd60,0x8e710,0x1ad00,0x3cf0,0x618,0xb7c,0x1e00,0x2880,0x1fa4,0x22ce,0x14a0,0x2184,0xa43a,0x29e5,0x30c00,0xcf300,0x2bb420,0x530970,0x663300]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 27
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤26))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤26 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 27 omega6=padCoefficients 27 (omegaCoefficients 26 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 26 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 27 omega7=padCoefficients 27 (omegaCoefficients 26 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 26 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 27 omega8=padCoefficients 27 (omegaCoefficients 26 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 26 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 27 omega9=padCoefficients 27 (omegaCoefficients 26 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 26 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 27 omega10=padCoefficients 27 (omegaCoefficients 26 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 26 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 27 omega11=padCoefficients 27 (omegaCoefficients 26 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 26 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 27 omega12=padCoefficients 27 (omegaCoefficients 26 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 26 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 27 omega13=padCoefficients 27 (omegaCoefficients 26 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 26 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 27 omega14=padCoefficients 27 (omegaCoefficients 26 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 26 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 27 omega15=padCoefficients 27 (omegaCoefficients 26 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 26 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 27 omega16=padCoefficients 27 (omegaCoefficients 26 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 26 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 27 omega17=padCoefficients 27 (omegaCoefficients 26 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 26 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 27 omega18=padCoefficients 27 (omegaCoefficients 26 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 26 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 27 omega19=padCoefficients 27 (omegaCoefficients 26 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 26 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 27 omega20=padCoefficients 27 (omegaCoefficients 26 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 26 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 27 omega21=padCoefficients 27 (omegaCoefficients 26 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 26 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 27 omega22=padCoefficients 27 (omegaCoefficients 26 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 26 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 27 omega23=padCoefficients 27 (omegaCoefficients 26 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 26 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 27 omega24=padCoefficients 27 (omegaCoefficients 26 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 26 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 27 omega25=padCoefficients 27 (omegaCoefficients 26 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 26 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 27 omega26=padCoefficients 27 (omegaCoefficients 26 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 26 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x12,0x99,-0x330,0xbf4,-0x2178,0x4884,-0x7c50,0xaaee,-0xbdec,0xaaee,-0x7c50,0x4884,-0x2178,0xbf4,-0x330,0x99,-0x12,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 20 li0=padCoefficients 20 (liCoefficients 19 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 19 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 20 li1=padCoefficients 20 (liCoefficients 19 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 19 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x68,-0x1b8,0x4ec,-0x9f4,0xe38,-0xd68,0x596,0x596,-0xd68,0xe38,-0x9f4,0x4ec,-0x1b8,0x68,-0xf,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 20 li2=padCoefficients 20 (liCoefficients 19 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 19 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x2e,-0x32,-0x15e,0x7d2,-0x160a,0x2956,-0x37dc,0x37dc,-0x2956,0x160a,-0x7d2,0x15e,0x32,-0x2e,0xb,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 20 li3=padCoefficients 20 (liCoefficients 19 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 19 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x3,-0x34,0x1e4,-0x7e0,0x13e8,-0x20b4,0x2184,-0xe86,-0xe86,0x2184,-0x20b4,0x13e8,-0x7e0,0x1e4,-0x34,-0x3,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 20 li4=padCoefficients 20 (liCoefficients 19 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 19 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xd,-0xc2,0x38e,-0x776,0x1ba,0x1f96,-0x5cba,0x913c,-0x913c,0x5cba,-0x1f96,-0x1ba,0x776,-0x38e,0xc2,-0xd,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 20 li5=padCoefficients 20 (liCoefficients 19 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 19 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2d,-0x13c,0xdc,0x10e0,-0x4d38,0xa654,-0xc474,0x5aaa,0x5aaa,-0xc474,0xa654,-0x4d38,0x10e0,0xdc,-0x13c,0x2d,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 20 li6=padCoefficients 20 (liCoefficients 19 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 19 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6d,-0x4a,-0x109a,0x50aa,-0x9266,0xe0e,0x1b65e,-0x38aa4,0x38aa4,-0x1b65e,-0xe0e,0x9266,-0x50aa,0x109a,0x4a,-0x6d,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 20 li7=padCoefficients 20 (liCoefficients 19 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 19 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xed,0x74c,-0x3fbc,0x5a90,0x15578,-0x5b754,0x8a444,-0x46576,-0x46576,0x8a444,-0x5b754,0x15578,0x5a90,-0x3fbc,0x74c,0xed,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 20 li8=padCoefficients 20 (liCoefficients 19 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 19 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ed,0x278e,-0x62a2,-0x259d6,0xa9ada,-0xc115a,-0xb872a,0x2bf69c,-0x2bf69c,0xb872a,0xc115a,-0xa9ada,0x259d6,0x62a2,-0x278e,-0x1ed,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 20 li9=padCoefficients 20 (liCoefficients 19 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 19 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ed,0x9b54,0x189ac,-0xfff00,0xeb868,0x441c04,-0xa8ed84,0x63ef2a,0x63ef2a,-0xa8ed84,0x441c04,0xeb868,-0xfff00,0x189ac,0x9b54,0x3ed,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 20 li10=padCoefficients 20 (liCoefficients 19 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 19 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ed,0x21ca6,0x11f896,-0x26f156,-0xae90e6,0x1ed907e,-0x288b72,-0x3e757a4,0x3e757a4,0x288b72,-0x1ed907e,0xae90e6,0x26f156,-0x11f896,-0x21ca6,-0x7ed,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 20 li11=padCoefficients 20 (liCoefficients 19 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 19 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfed,0x6ec9c,0x709954,0xbb7370,-0x57d24a8,-0xdb8ce4,0x1502dd74,-0xfdd3536,-0xfdd3536,0x1502dd74,-0xdb8ce4,-0x57d24a8,0xbb7370,0x709954,0x6ec9c,0xfed,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 20 li12=padCoefficients 20 (liCoefficients 19 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 19 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fed,0x15f47e,0x247238e,0xc8960aa,-0xa252b26,-0x5780e1ea,0x464b6f06,0x9ea4141c,-0x9ea4141c,-0x464b6f06,0x5780e1ea,0xa252b26,-0xc8960aa,-0x247238e,-0x15f47e,-0x1fed,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 20 li13=padCoefficients 20 (liCoefficients 19 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 19 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fed,0x443c24,0xac0123c,0x6b9a0ae0,0xde3e5148,-0x20a2b0d0c,-0x3f1da2bd4,0x4a7284e6a,0x4a7284e6a,-0x3f1da2bd4,-0x20a2b0d0c,0xde3e5148,0x6b9a0ae0,0xac0123c,0x443c24,0x3fed,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 20 li14=padCoefficients 20 (liCoefficients 19 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 19 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fed,0xd17316,0x30157e46,0x2eb58c62a,0xe033b461a,0xb05380b6e,-0x2d039defc2,-0x2e87931024,0x2e87931024,0x2d039defc2,-0xb05380b6e,-0xe033b461a,-0x2eb58c62a,-0x30157e46,-0xd17316,-0x7fed,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 20 li15=padCoefficients 20 (liCoefficients 19 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 19 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffed,0x27dd7ec,0xcfeb0264,0x1239e94750,0x8f2c27c238,0x1927ab2a18c,0xae9c63aca4,-0x2e34f9131f6,-0x2e34f9131f6,0xae9c63aca4,0x1927ab2a18c,0x8f2c27c238,0x1239e94750,0xcfeb0264,0x27dd7ec,0xffed,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 20 li16=padCoefficients 20 (liCoefficients 19 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 19 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffed,0x78c866e,0x36f160ebe,0x6abf69972a,0x4c4f31a0ada,0x170b8c015286,0x2f5e2f7e4a36,0x1ce11babf39c,-0x1ce11babf39c,-0x2f5e2f7e4a36,-0x170b8c015286,-0x4c4f31a0ada,-0x6abf69972a,-0x36f160ebe,-0x78c866e,-0x1ffed,-0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 20 li17=padCoefficients 20 (liCoefficients 19 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 19 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffed,0x16cb91f4,0xe4bec33cc,0x2578b4704c0,0x24cbb5a98a28,0x1041ce20558e4,0x39398ee0788dc,0x6a08ef18049aa,0x6a08ef18049aa,0x39398ee0788dc,0x1041ce20558e4,0x24cbb5a98a28,0x2578b4704c0,0xe4bec33cc,0x16cb91f4,0x3ffed,0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 20 li18=padCoefficients 20 (liCoefficients 19 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 19 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x13,0xab,-0x3c9,0xf24,-0x2d6c,0x69fc,-0xc4d4,0x1273e,-0x168da,0x168da,-0x1273e,0xc4d4,-0x69fc,0x2d6c,-0xf24,0x3c9,-0xab,0x13,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 19 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^19 := by
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
  | 26=>omega26
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
  | 18=>li18
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 26 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 27 at hb
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
  · exact omega_spec_26
theorem cache_li (j : ℕ) (hj : j<19) : coefficientsPoly (cache.li j)=liNumerator 19 j := by
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
  · exact li_spec_18
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x948164fb91f20d4aee7e400,-0x11bdf023ccf6d6ec224ff3300,0x106e5767b911a425faa7266500,-0x9d209dcc3e0b429a00b0b58ac0,0x441cf92a51ed0191dababc53040,-0x16d1698fd0f15eed8b020f700300,0x62577299ac9badecd8dd6ab6bec0,-0x15e18579ef7abbaf28bfe818d07a0,0x4198d6d9b80b58a5e43dd2f18b960,-0xa7fe928c3d1b0d90c4cdc60235e60,0x1738fd81ca678a7f4a155c51e14290,-0x2cbb90c4aaf2103775826e4db5807c,0x4b890be9fe3ceea02373400a5d6594,-0x7060a724555ff15efa4f2c909a1bd4,0x93df1aa4d5526188cb18f7acca9bcc,-0xac95538cde3712b9861475ea1f855c,0xb302794d0dec843be1e8c932760794,-0xa53531d3b9119797181db8d8edd514,0x87b960b5fb9e9ea5a510cd4f9bfbc8,-0x633b25544abb674bcbd81c68e281ef,0x4081267faf83a06fc1cc2be5bc4dd5,-0x2537f625e6e79a09a1070257874ee5,0x1303e46bff9a680d03eb11d192b7d3,-0x892fbf00be132f0931cf11daae3b4,0x365d631fcc95a627eb242db9438bc,-0x12d556fd2e02be65ed4c9efd52b8c,0x5aa6f5d5c62bc81390af017e264c,-0x177cf1b35e40633c990a89806f9e,0x5301c0e031bd46db5b366b41e6a,-0xf6ddf895206bc96a4c62b22e1a,0x25fd6f89c36cc7e5ceb2d838a6,-0x4bd204a31579370ce92425818,0x7744ed583a76c2d920451668,-0x8e50bd384029f5fb648b1d8,0x79f130e0e6da44c07edea4,-0x45078186cc16ad246eb6f,0x1678b677a07ce69a50d5,-0x338dd9d08842fb6f55,0x1aa1f70ee411c5b3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 21 36 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 36 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 46 indices rho q0 m0 0 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 46 indices rho q0 m0 0 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xf1524418cd295599c38d2800,0x1c66ceda4710b778896c67ee00,-0x19e73e8fef3655b2e1f17599200,0xf3dce1b39e9731f23bf9b997b80,-0x6808a99cad7805a17c5f2db14180,0x224913bee8883d5aaf48266d6dc00,-0x914eb629f046a1d17371cab23ef40,0x1fc7b87d3175eee9066d5bbb5bbcc0,-0x5d9c41a5323112eb823150b74e9dc0,0xeb7121c4093a1013160d030b87e540,-0x1ff28c8cb35d7c0f34414be11f30bd0,0x3c6018d4bcd0aab442f1f5bfe184eb8,-0x63f763d50e658f836ea023577171c48,0x91becd753b66dc368e6b7db25277768,-0xbbd1335ff8ff8ec27c85e1bca320b08,0xd687e5302acc56faeb5fc531a812c58,-0xd99d7ed7cbdbdfea691ee43293b0d48,0xc4415febf83f40017ff28ffea385a88,-0x9d6afbf00c746872bc3d100154ce0cc,0x7043f1c99673e3b10b53174af57344e,-0x471ce2df415013efcaa8cc9dfb5e172,0x27f04ae3be24693655d61d437528aba,-0x13d64515128e48cdf5e5dd6d74f1bd2,0x8af1653dc078f6a0be6db4ef175968,-0x355fe236e5d34f1e0d086680a24118,0x11e4be88e81aadc084adac143dbb98,-0x533034a13ab4921b038b2a22a3580,0x14c5cfa6a4288e43472350dc5299c,-0x4692026711234942acb4c033d0a4,0xc92a4465115c495c4c70cc19394,-0x1d9176b16253eba7b37bca0dcb4,0x382114f2b7e7ee5ac5ed60de90,-0x538cf1fb06b62c744dcf9d4d0,0x5dbbaede26ec1dd633475bd0,-0x4ae2b7aff57ce735a9e4f74,0x27161bd37b9a13e64f38ce,-0xb8c7f4fb762a4dfecd32,0x177e2d5d88cbbe5c71a,-0xa62fdc364c0c43a2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 21 37 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 37 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 46 indices rho q1 m1 1 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 46 indices rho q1 m1 1 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x18825aea84d632b19ddc561000,-0x2d7b6f9cdc1a8b1ca6ea8bcec00,0x28dda2eeb256443e18765e8b6400,-0x17ae335ea783d7e5360a5b7241700,0x9f20b6cc658ed4dfe91cadff60000,-0x339bef26b385ff2b922683c1437500,0xd72b2feadbae69df6107a9849423c0,-0x2e4646fda52ab3217fb35dac1efa4c0,0x85f8d76099d5df5f3c68f1900af1cc0,-0x14b0975217280c7ca3fdf72883f34340,0x2c1ba4bc4dc3fc0b0521e5ceaa4cb330,-0x51cf199a9eab6515ac4be90c1b361a40,0x84dd903c1563dc6b94c999a71ad32f20,-0xbde4beb23ae583859d5d3102534be840,0xefbbed374ca0e9ee59b49a5f1e937f30,-0x10c146a2948f5d42d219193c68f629b70,0x10a062fedb37a60485b15c5a3df04f010,-0xea82bd4cddc6c9c984233174b794c410,0xb7b51cb7195ec217d642127ac50f7c1c,-0x7fd4f3b96b059c8febd72439796d8090,0x4eecaf9f5b0ae7d44631f9cbe580be48,-0x2b27c852a98b0012b151d0b21daaa410,0x14d7b2289819acc8f51c051b5e35d5dc,-0x8dc18ad9881037d24d9f80fb7ed8820,0x34cb97976033cd61b2db2869e9e7e80,-0x1121439f2708c98c86c0d899fa2db60,0x4cec9d6af06b7295dc059684e5db68,-0x12831a64b506b041086210f7207e60,0x3c73f539e9a5cc7b635bde92b4310,-0xa524adca2b88f7de01f3b775fce0,0x172db273327d7d99aab0ff90cd48,-0x29d56151e75c4a09008975790b0,0x3ae471908e3a1f0562f89444f0,-0x3e1237f5b12ae8a7f512e1350,0x2e30d25ddae6c615557923cc,-0x1633394281832ca020be6d0,0x5f1ac43f3328671a5f748,-0xab436bc8c67d9ceafd0,0x40c381c2146931f6c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 21 38 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 38 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 46 indices rho q2 m2 2 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 46 indices rho q2 m2 2 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x27d3d3bd17dc1260a0860bda000,0x48dc6a8dc5242993471e5dc0b800,-0x408462a948b2d0b83e53e78d23800,0x24d4e5eb1681eeccab3c3a78fc4a00,-0xf3bf0f82c1828a95d6e09667613f00,0x4dd323d02c7dc35660260e92c04ef00,-0x13f4cc43cc7006a60559302b6b326640,0x438c264c1c55b61dd1fc221b6850f2c0,-0xc04808c84c4933c71ebdc533dc6a63c0,0x1d2ee4441884a558ea24850ea06100d40,-0x3d1cced66be831a2dd9ea45355d0a80d0,0x6f47f4b5f749c25d9a6b180b2303a7790,-0xb155c1b188c3f46dfa508413c6359f250,0xf8899a9e525a40a4910741f64e62e87b0,-0x1337d31a782c00bda01c705186fce8d9a0,0x150ba600032899052ea09d198f277ad7e0,-0x146fbaed4833faf89e5e08be0288c4d260,0x119d70f79b410b84eace1fdfa33b94e7e0,-0xd7af47a68338dee647a0575f2b3627654,0x9279d3d5bf506e7de06420a664e8689a4,-0x582b4d51d19e6523bbac4302d2bedb954,0x2ef29e6a5bca81a3fb3f1043f1e753f2c,-0x160d5828d4bfef452ed1b58e67d979798,0x91a94fc242de5a34f7abd06e03e38250,-0x349a6f8406ca1f8a5531479de1630ed0,0x10852662a5fa29cb8b9d9db5a1959b30,-0x47a92c3be1cef71c8be1f3a54748988,0x109eb79d3390508fe47eae2bcb51b08,-0x342a7cb6d81b7cedd1d2d96d705828,0x888af62db8519ca8995e14d70cd58,-0x124b6f3e54bbbf7b11d6c311c9560,0x1f616b91e4f4b79dd9206ee36370,-0x29c193b6bcfef2b285213115af0,0x2950829c7b1736ac1dbf2bc7d0,-0x1c9b96def6b3bd130bf14b234,0xca4efa561ab4767e1cc0564,-0x31029b88b2104022732954,0x4e0393a7885a2d9e50ac,-0x19386987ff502a7c48]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 21 39 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 39 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 46 indices rho q3 m3 3 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 46 indices rho q3 m3 3 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x40b8381346c59ddd04d9d3424000,-0x74c32a3f9d87df4eb2e143db57000,0x65edd3085f5aa3355f9d6c2f654000,-0x3958e123ee45f7d7f9437c565ff5000,0x175e3b6b2742a088df91b81c392aa700,-0x759061a898c4b91658f9282a30a84500,0x1dad3811750abf7ea1041e358edd0cbc0,-0x62d79c8a340a3c948967bb85ec6f2cd40,0x114be0e0dfc1d05055bea49864bf10ae40,-0x294ae26293115e32feb190e900900cbcc0,0x54f7a3ad6e5ab22476d0f670d0e482a2b0,-0x97f29bb7d96d8c37fa30f27e8c92c9f3d0,0xedaafc434fc12cb131920ef175636532d0,-0x146be32be58d905959360783496b546cb70,0x18c4693e63398ca133898f1d8efbb087840,-0x1a91a5e5c4fef2833a4c7f0b9e10f514c40,0x19411eaff68fe8df347143de868bd96b780,-0x154a32160eb1e5174c071b009e9320f2600,0xfeba7cd3ca43f83d9a4581fee7828c012c,-0xa8e04edb6d621498d339633772f61c96b4,0x6320dc9dfa832e36b3829f8dec14a31874,-0x33696dbe205378f244c70de67ce6525c1c,0x177dad67e8b55069f4369d7b0555aa3ae0,-0x96b7e2fdc962817bc599f214f94704950,0x34c8b3a39a75b816acdc7ceb38b3d9e10,-0x100be0c82d5151381a3c1fbffa7220a30,0x433d2d64bb86b23074381ebee41638d8,-0xf0748115f0354557adc48f244e354a8,0x2d5575fc7968149ff574f5cbf23c668,-0x71ac8e940203692cb49596513fc6b8,0xe8902a35aa4b0550036b7ad923290,-0x17af5076619d3c7db4630ab092210,0x1dc586889d3d9f5abe99d9e74210,-0x1ba1857e345f44526a3f6d6e6b0,0x11c8f5035e0c00c9c782dc79ac,-0x73841e7b33a1d453d6e917f4,0x19485f79885df1ac489ed74,-0x2386bfd4d5b13bef4bd1c,0x9d08217fba07448c30]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 21 40 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 40 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 46 indices rho q4 m4 4 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 46 indices rho q4 m4 4 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x692b5b1f5301208727e1f74ba8000,0xbb2e701ecf93463ae79aee3fd22000,-0xa125d28722026f0df71a882bde99000,0x596237664dc05c42621d9884c3455400,-0x23e51e4b1c5261fd71cdee0b42fff3500,0xb1e77257a9cd708f860863ecbe9c3ab00,-0x2c39406e6a91d5da690d1deae7e41d9640,0x90fc8b5c54515e334c9c494e5730abdec0,-0x18f67507a2ea616e62b51a4fea229b9afc0,0x3a9b80af1605662644d47740df74f42c940,-0x7689d4da9bcc3c0c39a5769e2778091d5d0,0xd040f5ce72497469cf3227020c75cf97af0,-0x13fd2e521e24192ddcf5c9aca8960a832c70,0x1af708279c98c425770d465c17d7745720d0,-0x20117ec92610587a57d288fd9f3d69355100,0x21b58d76fc004943d25ca51d965fd9568300,-0x1f5f62de71ca511d5c36e59df35155bae1c0,0x19dfb9ed9d86d491c887d7c154cfd9765440,-0x12e960161c056bafe45803e992c8faff0db4,0xc3e128fd3b911b78f14f3d348b14c710afc,-0x7026161dd4e2c722a80d79b210c87f7995c,0x38aa385a8e4f19b6c5ecff9b5ce3f11d2f4,-0x1930a6bdf4ffe6d76a9125c0ed36b975cf0,0x9d02ce07684e24e2410d3e69f9c5605ff0,-0x3554ce4000ef07758162a6f64cb29cf9b0,0xfb1ecb595c812527073578b43590a0f90,-0x3f8805939e5dcdc57f51a7bf52a718128,0xdaf0dbff6ed2cccc60f91ff6c56d54b8,-0x27aa7b4db8d2256d783b0aa3807a7f38,0x5f4377e1e3274a43fd94a1c37d7bc68,-0xb9f116bd4b63e49283dfc222c4ef90,0x11fb4ddd69fbe64eea3b2b5a2a33f0,-0x1556cbc49696716ed9bfb6484a470,0x12900879bd484b30f5b15d3396d0,-0xb1860af3767ba34493fdb12374,0x421b5749805842ca7db915fbc,-0xd0dbd1e1d69b83e14769a5c,0x102c25bcf8705cb2073cf4,-0x3d1152d57723d07f020]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 21 41 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 41 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 46 indices rho q5 m5 5 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 46 indices rho q5 m5 5 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m6 : List ℤ := raw_ints% [0x0,0xaae67412e6e1d4dba0cf31daf10000,-0x12c2c7c1cafaa72ddf00de12082e0000,0xfef28bc8e146f2c275bf8b3d3a733000,-0x8b760da21da32e4ff28d3b63cd5191400,0x37368be3be9ab90b57c322448632379300,-0x10dad144ff9aec7a4165457aa83285e5500,0x42096741b19f117d035bdd4e1a9e74f77c0,-0xd52e66ecf61df8914ab8e0f7e141f6df340,0x2420025d9a3a6928c46ac19c326874066840,-0x536fbe81ebf52e94e3b21512be9cce449ec0,0xa5ee657b8b1c3891d60a828cc9d7a0cddfb0,-0x11e7a5e5e9d5ae1dd59ae8418cf5615003510,0x1b019fd27544e5790fbc837d048ed7b331090,-0x23c232a585a44624b95e2e7cc842cd624f930,0x29b68322836374f5f9301394a8eab42d39a80,-0x2afa43e543493abf17186504bc23425800180,0x272caf01b287909effe1d5d75fe207fc8bf40,-0x1f9db09e3804338b05934ec7d544d5accefc0,0x1697a6d7fb57e00ac0ae6906949dd297a4d2c,-0xe48ba853eba192625125646b13a70c8c9404,0x7fa85be270e21de24312b7d033b925c8d2e4,-0x3ed98f3d16679b84476ab196e35ff846868c,0x1b2ffa931d22cb043d0977662ff43fccb970,-0xa4a6784fcb83a89a23ff23a21af6a602510,0x363f2407e3a515a01a41d6e544c442d3b50,-0xf7497ecc45d547401580bf629abc4e3670,0x3c6f809ad69dcf7b5a83a711cd78d87818,-0xc8b1897cac9ece118c8ceff0d623de348,0x22ef9463bc4c66b7df95ea817355fb748,-0x50583c02215d610d4ee2fa5b03dafa98,0x959163a892f7b78ba83c760ee705db0,-0xdba77df33e81f1cc462862ce6cbc90,0xf5f19b2d0315172c8acb92f60e390,-0xc85e32c7e672b3fb6e3b4cfcbb30,0x6f1aa846b062a28c5ca86556aec,-0x25e82d9c29f6db3a3008f9e544,0x6be8e91f1d1b5216a14887e4,-0x75bf239c0772391128348c,0x17bba81902f8dd7c9ac0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 21 42 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 42 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 46 indices rho q6 m6 6 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 46 indices rho q6 m6 6 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m7 : List ℤ := raw_ints% [0x0,-0x115b67c9eb72ef9e4e550b103c7a0000,0x1e189e2ed34e35dd1dd1cdca995a4c000,-0x1939ed6d94c30f493943a32e6611eaf000,0xd9d11c40a57d6e07607b1742360f687c00,-0x550b0ac9a4e6871debf087885339242dd00,0x1997b1129081cea17b6f164fe854bdb20b00,-0x62cf075a8903e44440eea45ffcc2c0982a40,0x13a3084f36ea762c6d096d6ad918f04e02ac0,-0x346b35afb90576bd3ec24c56fa94550be2bc0,0x772416b4970302d4c430b9bd86c970c6e7d40,-0xe90b03ecd689f4fee7932b30233e15ffc32d0,0x18b83f47087fd3cec7840922d078633223c770,-0x24a17d3dd8f5bd1563c67db52accae5d3623f0,0x2f9ee3d8bedd73cac4752553a7347ebbd1e250,-0x3680ead115442d7708bdac4dc5b18e6c598280,0x370ebcf40bf67a99abc239fbbec88641fb8380,-0x312a33daee3ff5d7a339faca1b3a393ef90f40,0x26d693394310fc2e0490e94f19e57c81b5fdc0,-0x1b23cfcdeec314050a7d4088a5496cf9caeb74,0x10c345750be27039fee5da9e6f8417da5a5e1c,-0x922ee0f5f541a2a742fb2f3e80f11cc0f433c,0x46240b96d18874f975146a362c5e1e68c0b54,-0x1d8775170019d5933ddf765696d190d5f4050,0xadc6e616f194a4aaa72db0d8405039447570,-0x378a0112f13dd213175e720ec2b7e8114830,0xf51e29d46b76bb1840be85a76e32629aa10,-0x39de8516ad92e3b8e046a5b730b4e669028,0xb92a6f1b5733d39ab793af8d11f5b88af8,-0x1ef7492f05778450d0ae79b5876a252ef8,0x442db2ac2a8e0669cd3e8b0959a006b28,-0x79021c249ea05161aa15c95fe8afb350,0xa89841f34a73c0b1ca6fa23f6b8f0f0,-0xb2007ccc4c64fe6fb710fb619ce570,0x87b4edb20cf88ba296629f4305bd0,-0x45bd6014dc3b613a1d33554e80b4,0x15c6710ef29d64d1c2809f722dc,-0x37c8864041d3354464c5b883c,0x358e838b633487ae4ecf754,-0x937bbee51643f53fdc80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 21 43 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 43 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 46 indices rho q7 m7 7 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 46 indices rho q7 m7 7 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% []
def r8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m8 : List ℤ := raw_ints% [0x0,0x1c3488a81e9ac5613f4a31fa624640000,-0x304be9033428df3656d48c1c000b064000,0x27f6c18a6be93625674fab1f0c62955f000,-0x15489f0fbdb506b56bf49c64e85ef145e400,0x832a35f2e27a36cb3baa68402c52ef1ab300,-0x26eccbd106ba1eac2f81c656e9c451b2f2500,0x9423ae20e844468191c5a7de1d0ffa182b3c0,-0x1d02178a0cc7f9bbba2be312c9f7664938ef40,0x4c432a1ca508a5c4ce8a8788de74e16c37e440,-0xaaa07d41fe34ecd3c0d74a49ca9cad83ecc2c0,0x1485e0bf49c86d7036dc414a565db85d0bae2b0,-0x22400fcdfb061704822b65ecbeb07a120cdcf10,0x31e0a37523f0941d2a83df7c4f2cf1bd7ce0490,-0x3fae7b3105641e2bf6bc1360699a919b8d0cf30,0x47885ff8896ee13b598a0de179cd7c6ce125b80,-0x46dd9583b620c66d6ffef18c0d5b20d90679e80,0x3e02901a26fe0ade30a76ddde039d0b97d0ea40,-0x2ff5a304a788e294241235dd3608a093b5f4ac0,0x20c7dc993788217f7109ae4fa05b951e62696ec,-0x13c880cc5dcc1b22e6f2e7290dc36f4ce9de884,0xa86134fa2313984b1dedced70755e2dc3f5de4,-0x4ec02748df8d462bd60cb2db213407e2620e0c,0x20456154945f2a0f4d5c04d70b35d97d2828b0,-0xb890b899ea60ad4e0d13d622fafa69fa32110,0x39399712feecad3bd85b79946451485135150,-0xf48664abf06615bdb2a8be3c647ce3ef0270,0x37c4142ac1d87b9710f78bd91d788410b498,-0xabeac53cf0a14c1125d547d8093b93b2848,0x1b9db559a1c2c3fc0a26721633031c7fd48,-0x3a324af087bc93a63cdadab9f96c46b598,0x62723cb80c34afb078b4b9f21f2bd0d30,-0x820fe4c1c402920c142819d9462dfb90,0x816746b4ec8fbca0af31f7ea4701690,-0x5c3fd397849a2a9c95cd90e08d5c30,0x2be4a788f8a3f313ff1431434cdac,-0xc872bb5b4776a20909022e58dc4,0x1cd93ed9c02c4169db3a79b2e4,-0x185953b6d5e88b9ad834a00c,0x393f25fd0182d4c9ed300]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 21 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 46 indices rho q8 m8 8 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 46 indices rho q8 m8 8 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1]
def r9 : List ℤ := raw_ints% [-0x2c7ab485a10ec1ad00000,-0x45e17f578319141050000,-0x33b37494e8e1eccc04000,-0x17f69d262636fe1d9ac00,-0x7cef50878d2e97790400,-0x1e70faac74650c7ae340,-0x5c2458a8892ed144b00,-0xdde9e2f1fc62b429d0,-0x1b0476932882702ec0,-0x2b0840b4f5db05c8c,-0x386b4ab2f10e4f10,-0x3d1718c179dcc33,-0x36a423aabb3cb0,-0x2841469f1efc9,-0x18461681b5cc,-0xbdb20cdea9,-0x49db9bfea,-0x16608c4b,-0x514b18,-0xcef4,-0x132]
def m9 : List ℤ := raw_ints% [0x0,-0x2dd55e1131bb80be06d89136dfb2280000,0x4d87751751bdb2b9c70eca14d6c3def4000,-0x3f5a7b52cff91b5278fb99ccc5f8bd997000,0x214eed20a7e30c0d8733a0cd6b429dbaedc00,-0xca911eb28887fc7e5b8a8afc4b55d995f8d00,0x3b4cde3b5c171f7fc9cadc943b7241da80fb00,-0xde88f9ecd8df9cbc3ab9675a32604dd7638e40,0x2af31bd8e8448d14be723c8bee5b7b9e381d6c0,-0x6f3d6594d4cd64189364f79cda22563907487c0,0xf5129e47012dd4ef2bd8e004ce8df6814a8b140,-0x1d02b7d171062e54c13d6b71e139b7a5b8975fd0,0x2f9f32022c775661b668022bddb3fa4192b30470,-0x442c4237e7276dc47b5c4c94ff56b19535d054f0,0x5581eb8a48bbc3ee99df2aacc55becdabd5e8950,-0x5e4ace5d61a2ecaa44f046fd44ee6580f96a1880,0x5ba279332d1362f780bc17505f1bcd051b979580,-0x4e97dcd785c91d6d280e9a89e728e38363346940,0x3b86cddc0d73f03cc16b77223b6b947fa82dafc0,-0x27ce47e3bf996a136be948de21e9c037bc7a42b4,0x177a487888acfd16d737a2e2c4d16d48c174f35c,-0xc30f993fb890617748a98eab1fe6d00782afd7c,0x58f08d76e7f0f8b1f0d6c391146861c093a1f14,-0x237b0bd7d34948a75f40a1ac075d8c97ca692d0,0xc53a787a1f4543ab38a43844d9a0eb00948e70,-0x3b540b8e4fc71beebbe14da8d0554b74677130,0xf574352477a2b4f2c5315f3e33eb37062b910,-0x36128310aa0a5f59fb7a5deb3fa389b7948a8,0xa0974b5bdaa988aac59a9a8df2de96e94978,-0x18c657201c93eeffdffd797a7a62a953b378,0x31f544749ed529f7c1f94609894990bdaa8,-0x508453847ebb38c74a959904008ca64b50,0x64d22ba72fc1aaf7dadf843ce823287f0,-0x5e77f7731ac4e4db2ad27d8839c8dc70,0x3eec081c50f0042daa050eddb02a0d0,-0x1bb18459e81a9f32828431363299f4,0x737b8365f5d6aa04f12e125d841c,-0xeec6ec218e2eaf0c284612527c,0xb108df16cf3564745b416314,-0x16352c0916d07ecd5c6200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 21 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 46 indices rho q9 m9 9 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 46 indices rho q9 m9 9 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x132,0x1]
def r10 : List ℤ := raw_ints% [0x352aabc7ba83a380ca00000,0x535b0f821512eb39d2a0000,0x3d869fdaa6daf3f7cc78000,0x1c71146304c4d9d296f5800,0x93d6a46fa45e412ccd1c00,0x23e61c519b939a536a9e80,0x6c3c624eacb3a55c6c2c0,0x1037f4bbab71b0e45afa0,0x1f6d6bd8f46f8763b7b0,0x31bf95ef1b57a5e7098,0x40bfbb3e94c56a2494,0x457ee6ec149d30266,0x3d7ec115fd63c9ed,0x2cb3c42fad00fba,0x1a7fb27fb85477,0xca78beb71db0,0x4c6d6d4a017,0x1621f1c142,0x4ad93855,0xa7ecb6,0xc2ac]
def m10 : List ℤ := raw_ints% [0x0,0x4a7ab8dbf0d0b134cb1febf92b818100000,-0x7c7f0798321ce2f032077863547458cb4000,0x647f6c913e8168eca9eec8c44e128d15df000,-0x342d6c05ea1024e299bfe1f37945172f926400,0x1393e893eca8c589b2e65bdd2a3d7f3e2da2300,-0x5a7cb9ac73ffa0db76d31a32f6cccfc4246f500,0x14ef06b80fbec1b6fc18419fc0e401cfb227efc0,-0x3fbc01b376bcdac3450dc22b1a612a6530be0340,0xa2aca9fffa427a0a7880d91b58019bb60f892840,-0x16101c9bd17e763dcb8b6585a5b7ff19ee2a92ec0,0x29235b33f3b0cca8f4c05efcc0659bd8381ca6db0,-0x42714b746c16d7b65656fd85ca0f410bbde870410,0x5d8713176d8bbb80acf05b68eac8ce753e91c5990,-0x73467bd421fc5c977d7223740bbf80a6fec7f2e30,0x7cd37652a7ec38ebe67e6aa1c64e09f6ea8043f80,-0x77078be7694dacaa8debe7762adcf802d964bf280,0x6416b942906a6f067704ee2ff610a8e37937d2a40,-0x4a413f93a675c1796ca4477e01c3c726d1990b2c0,0x30970416c57067a254e75950a1fe8a3e9cf940bac,-0x1c03856c07833309fe8752a20e86a408876e437c4,0xe33da325ff3aa6219890aea5536a37ee5bcadd24,-0x650703086690f4c9b8bc22b8801594d059e8f3cc,0x273d64e19b9df25167438a1b269a8d53fdb8e4b0,-0xd40636853b0853b060c88fb4d96a5ab49cfc610,0x3de195cd03624482c7f656394c4b600a2286250,-0xf7e13cd40cafecc8988d986f395c13f4752570,0x34bee0e89fe5314afa31bad0e28c98b16f1618,-0x96e5d2221b3988430505b02e66cf97d16c2c8,0x165a67d03ff0e98e5767e188994a1819ffbc8,-0x2b1ebcae245cde51e4e69ad340f0564c4118,0x423012fc675d4b529d15a785bb364119230,-0x4e833b40ed1ce518d537fb105655c55c90,0x453cd87fd817d5fc18a8f719c7f111f90,-0x2b0dd1ce1f229eb46648f3fa282dff30,0x1182ecfb05b773296bc3000b249326c,-0x429c64298bf0fa082225171d94104,0x7b8b52bafae149fb3cd7d739224,-0x50689a26fa70ab08c25bfa5cc,0x89c341491b3f250b5fec00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 21 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 46 indices rho q10 m10 10 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 46 indices rho q10 m10 10 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0xc2ac,-0x132,0x1]
def r11 : List ℤ := raw_ints% [-0x21d2df3e8dd564af3a3c00000,-0x34eeab56186a926a56cbc0000,-0x26fd5fdbaa729a527a4810000,-0x11fb7628a3f07e91335d01000,-0x5d3a3a8aa3c3dc7a50e75800,-0x16923b3aac6e691855fa1300,-0x43d311d62f786c6570dc580,-0xa1fc90faf10d2482f4f500,-0x1388098f74daf598873960,-0x1ec253d70c9e3113c8e60,-0x27cb3d52d9315328ce28,-0x2a689093570d81ffeb0,-0x25352ae098134d7a5a,-0x1ac4974ec0849ce0f,-0xfaa2fe41af579c6,-0x75c0b00d193171,-0x2b82888452ad0,-0xc3d877e4bf1,-0x27b87e327e,-0x53b31aff,-0x57950a]
def m11 : List ℤ := raw_ints% [0x0,-0x79076c6567531ff5ca13df74e6b271a00000,0xc7faf8e7ea306b91ec0c42a3b3e586f054000,-0x9f85bd42cf8e470c1765edf66ceb904e207000,0x51d085fafe6d25a3c7513eb1a2a3c6e55a11c00,-0x1e50337cece61114613880edc93db7218d165d00,0x8a4bbc13db795edfd65e12d1817e762a548d2b00,-0x1f91452378c7a110463646e7df522b118c73b7240,0x5ec96c2db6edad8e67477e7308e7883879d1942c0,-0xee7d5f1e4d5a7b18562b59306bcc7c4240fc0a3c0,0x1fde89ab7289766bc68b1e01c92e7a9b6b188ea540,-0x3a8444950860128ce41b743047e9012c068f91dcd0,0x5d0427e669493f3d137ba85fa590827c6071e2a370,-0x80c8b6a9eb9338aca01e158cfa5067cc0001816bf0,0x9c051d6813d22006d412f891bb37daef5e29d22650,-0xa5f183e80aa40af19dc4829bc233b82152235ab080,0x9b4df5d44a121dd48e4712d45b9e52a1f95b205d80,-0x80102fe313318d8c18b8a4a459322945e6d14d8540,0x5d158c0b1d4bb7fc3a03dcd0890cf89af4d81b93c0,-0x3b9e13edb693045c377025d8a0c664849e0b8cb3f4,0x219ac56ce5deb55e09b3d5231cd3dd5b3ee35a791c,-0x10a2fd78f72ab83f0b08fd99aacc7530029434f93c,0x73680ff43a3f76cb33cb28e2898bdb91163f0b854,-0x2ba5c9c0e256ac0d04a08b0d5f5c8c249c4da6dd0,0xe54392c918a9b0d144bb0348f9013b0c108c3570,-0x40ecacdc49830e89b35c3e688bec8e3404a6e430,0xfbce2e7de5d520cf112d71623241892f1819a10,-0x33c07eade756903370d91c450d2182237047f28,0x8e99c759d1ea12aee8777c0d15d7577517b8f8,-0x14479a1a7cd5555467c23d3e292f6fbd920af8,0x2569c7faaf6c433f3cb54ee8c0d479fd53d28,-0x36ac51c84cb2cd4fa07c06fd8440d70ffc50,0x3d6813b1f6dce9885445e0f7491592496f0,-0x32ef148c7b9a03fdca8d46a1531841fb70,0x1d8bb38003faf1d53997f31bbfcd7d5d0,-0xb1867157bf4690ea3b9d2b03d244734,0x2675f77358a13143d975e43c7005dc,-0x3fedbe014d72582ae2accbea8e3c,0x2480c361aa939c458641116c54,-0x356208425dee154cfc74800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 21 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 46 indices rho q11 m11 11 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 46 indices rho q11 m11 11 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x57950a,0xc2ac,-0x132,0x1]
def r12 : List ℤ := raw_ints% [0xf379881468ff9b31841c200000,0x17c67e616be86924843cf720000,0x117b276b2245b97e91038068000,0x80bc58134a9f941ca4531bb800,0x299e5926bec6453308803e1800,0xa0ce3e861150ebd7eece9c880,0x1e1cdb2ea166702873977db00,0x47ae7ccf13835dc29601eca0,0x89c4262381b9a7bc3e29e80,0xd805ae08419e9b29cde018,0x116129cc0a33448bc6d840,0x1269b668e26ba14af4d56,0x100b0ec0fc4c4eff38f0,0xb724be2bc2dd3ad688,0x6a1a9efbf2a42d931,0x313bc30cb9c4a086,0x11e89a9ddb54e4f,0x4efc19f39056c,0xf9653e6282f,0x1f9c0cdd78,0x1f408221]
def m12 : List ℤ := raw_ints% [0x0,0xc4ac1024c7e713ef68604b1df6e1f8a400000,-0x14155701acb3cfeab41601cbd98fc34a9fb4000,0xfd5fba1a57715a03547e1089010ac1bf7f2f000,-0x80683e4af4c937cf347caa21e26adbbc229fa400,0x2efea6246a270d0bee0034e57892bf729b0f3d300,-0xd3b2026dbc4305430dd007c47a97fef7ae937c500,0x2fb12ceb95faf184ca370c7ff6ae1f04226575ebc0,-0x8d4674bb96a83bf92df0e313a5d5eae4f4f247b740,0x15e811d3bea0933513831ebbf2f48078441f24acc40,-0x2e29675b70c439e46dadd46bc05437765bdf7847ac0,0x537dbc4f40c1214b7540723ceb29bad52eba8d208b0,-0x82a7213ec4c58b16a176bcede322e945db2f47e1510,0xb1f8bf790373de30e4385577c5e47ba6c5d99d46290,-0xd3fc4e0817e30709a8a3496c92cba202770eb2b0130,0xdd848a83bb212572be4c378ac0103d4c9f4acc44f80,-0xcb85f23cc70f8fe0df209b58753699f29071f8e8280,0xa49d064e08f69620bc09751fb74cd4f765b2f0a9e40,-0x7540b968f0921b76c6fe2fbb1098019e8140e8faec0,0x498446ad61bb5eed7d4f3f5f850dad45603c87d286c,-0x28859c9bcf54d6b0d91fdf6f025620bdd3aacedee04,0x1397d1fde2ad0e2b4c2c820875904e6ca3b72e0d964,-0x848f9dd9dfbd4a7c4642818ebb759089de3166868c,0x30d2feef1aa0970f6e6ee959b77f4bd42517436bb0,-0xf9523e598df19da7f701aef7138b79a754af9bf10,0x448246b9b6393b35879abecbc65d0a7b6751a0f50,-0x10142805430d27e9c7a924d4adc218162632d7470,0x331091b827b0dadfc9f218ff4c61d0d5e1a56398,-0x878185994915d7c876acc7a48a7cc1ef4846b48,0x127f243470f8e1a0181644efd7d60dfd42d3448,-0x20a0085d57b00de854a17a3013bc42cf96f698,0x2d5f06f1e6aa7b29c814fa45a50889c58ad30,-0x3039c4ea2b5dc5c9aadf6bac8a7cac1f9590,0x2599757e75a8663b2749c23696bbee0d090,-0x14549f658c8047c4675d9400ace4819a30,0x70af5651a11ae988f8333a16f4457b2c,-0x1639f8ac74d3fa72750047ff98edb44,0x2114bbdffd64ba2a950c70c07ee64,-0x1090123d691523787ff0fc2c88c,0x14acc6e77d6d1f53157e3000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 21 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 46 indices rho q12 m12 12 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 46 indices rho q12 m12 12 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r13 : List ℤ := raw_ints% [-0x56e11255b662e279f80d14d00000,-0x878b2b872361a93ed179cf850000,-0x637fbc4975751338257e35d64000,-0x2db6bb5cf9f921e78b4b6e60ac00,-0xebfb9be1a6f87944505a785cc00,-0x38dbbb9b25272d71e9212ffb340,-0xa9ed06a6262a9833fdb0c9e280,-0x1935700e805dc8d73ba0fd28d0,-0x304aab867686c5e6822319a20,-0x4b7139fb06d7ef9ef5d8678c,-0x60b2fde116ee005e13070f8,-0x65f1e367809dd3c79a2093,-0x58509ba6e991658d7c23a,-0x3e95b6936e34d78028ad,-0x23f75d826abad243498,-0x1086b2bf5f882078fd,-0x5f079897836161da,-0x19cd1c324512377,-0x4fe409d58cb64,-0x9dd96d53630,-0x9689dedd8]
def m13 : List ℤ := raw_ints% [0x0,-0x13f979a3bc4d78065099c7a10b12f340a800000,0x2047d19588f337aa15f0b3a68b0df1f3f9b94000,-0x192b103659392b07673fb342ff0e6ad2c07097000,0xc9b8bd5da624239ddb0ea2f7d4622eab25adadc00,-0x48f23754e8f988bb42b1ac46ad6709693023a2ad00,0x1448cfe0152dbaf598d72cc9654721724a6028d5b00,-0x482f9a882b82593c9a198f972800cd3013f20da9640,0xd303c0ecc0051f9a19742c011acc83adbac86256ec0,-0x20462529801bfed28fbe411dce6adb58c2f335427fc0,0x430bc40139462e3ca54bfff78e245df47b720f85d940,-0x777b8d1b29a1a9cfd5ae9b62031c980868ba003829d0,0xb81edf4afb02685669d6807ea661c9e950c1fcc03a70,-0xf6d1d7a9003e48eb77b82143b55bf2c4058febb68af0,0x1211ffd36277afdd6bfdfb74b4ee5a60a7c04e81aeb50,-0x128e7f891691fee03b8131c19c1e371300a085f9f1080,0x10bdc884862de3b0537023bdd66b7b1d0327ce4ffbd80,-0xd48e0750f4b36f7cfe7f007c4e12510e3e5d0bdda940,0x9465eb11f9094dbd405ed1c8a21a4ce3bbf44879bfc0,-0x5b1ad214826765dfe85b6cd8ab43bd64460c4ee7d134,0x311d1124a53fd4be2a6683165350d44ebd296a897cdc,-0x173253e6365f1f13ea77d58a1901c3ac367239c736fc,0x9916cf89272a63feeb3357b067fe1316dc6086d1b94,-0x36ea671ffe7a8c4521a4155bb2353edfb5196c4ead0,0x110a5119a60cc35de50483918d0ffc45328a1648470,-0x48b22a6a69771c699841b03b48758f8716982e2f30,0x1084c53ff74baaf8a02bbd2e64c01068e7cec2d310,-0x32a9eb12338f935b1ac83b8ca22add1587a8cb5a8,0x8174396c2d51d4a0c0b0ada168702ff6fdc8a478,-0x10f502cb5c635fc0b74a2d8afb399f11f4e52678,0x1c965c2132495e9c7d7a3ffac26ad6e066ed3a8,-0x25d18dec8c9b4beb5cc6e9e38e36e69dd60150,0x2605a173a97ff2afc5af9060fb85c94c635f0,-0x1bd8b30dbe58ae7b150a0bf5842020fcea70,0xe06436fc261b4c4b1b2e070b636a1fdad0,-0x47a4d128a811659ed9059bd9c0e548874,0xcdaa584f150f3c3dbcb4bbe7c37859c,-0x111e1791bbedbbca181ccaf5e3cbfc,0x782e579450e64f848fbdefb9f94,-0x800d039c86a26b5173bc2000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 21 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 46 indices rho q13 m13 13 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 46 indices rho q13 m13 13 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r14 : List ℤ := raw_ints% [0x1a27da29cc98e9aaa9cd992f800000,0x28c0e20e19f909327f3bc468680000,0x1ddf732f77e020c96f87f82df10000,0xdb3e82ec28144e5df515d5a0ee000,0x469c164f568a02488e916dc6eb400,0x10fa9c3ba0f8f810c0dba02cc3200,0x32a12fe3be95429e69cbbe8e94c0,0x77dfbdeaafaaf21d220867ef500,0xe4fd36205a77470a3ef4b20930,0x16495812a53e6501f8d2261800,0x1c762cadfe3032dfbaa3c1df4,0x1de13f2e6e7875cdc8c8c710,0x19c27c184693dd8cd8820ed,0x1226e3a11af6f2e8e2343e,0xa5cc86be74b003637a53,0x4b95205d05aa127be38,0x1ae7c82f5cc5aa4803,0x738472cc39596936,0x16078ff2b3eac09,0x2ab6a9a3fb2c4,0x27bb872f550]
def m14 : List ℤ := raw_ints% [0x0,0x207565aa11fde30a42f9e465b1fecb4911000000,-0x33e6bd226406b38438af5c1344d56d5e327f74000,0x280655b68c422b6d5ec43e4e3586db80c1d80bf000,-0x13d2f6c8a3210fe6b9319f03f14deb10a3052fbe400,0x715dc4ad442d2a77c622a3d4b01d7d07617c9158300,-0x1f252ed4273cb58bac1cb145e844d590f811839d9500,0x6d7518f59bf4752961f454a06705f946d88d71a7a7c0,-0x13bd7fe8c0447ad6e5c613edf427b6932f068fc022b40,0x2fa96a7ef8647182dc1a3cd8d4f42088660f0f67d3040,-0x61a3a004f996d3cac01ec60fa6a4d92485b4d173706c0,0xab7e9ec57a6f33839d1d3c79146d0fd41fe52143cd3b0,-0x1044e78c1377aed71f5b8d16fc67422e8d424c90c2e610,0x1577f263485b1f63fc9485b6a3e3fb86a462c5a2e00b90,-0x18bd003e76ab37f96b0abfcf698975f7d48d563dab9430,0x18f8a779eb2770abdae979eb44bf21111263c0ac4b8f80,-0x162079b089b892ae2ce7392d4a1b5bf8bb4379c8a38280,0x113ae3d11efb449f45fc596635316d77e4094efa562240,-0xbcb1156d4f8950ecf6c6305897a0fa5ced22f0d7bbac0,0x7172c5fab2482cde4b64ba29d38ab78e9cb4f11eac12c,-0x3bd3670c05f97a818c5571d0c62f1b74342f195acb444,0x1b9adc40f90e73eafcef2efff12f111e28a8882be5da4,-0xb1bb68be61ef09d507c6ab8abfc4464d2d4dd6f8a94c,0x3e1986bad7f2eea6e7f0f67625de241fb74bf6072eb0,-0x12bc5d786a5e85f5d3112c51ad52d312a0d40901d810,0x4d8f577e4468430fb36373942859adfe502c5833c50,-0x111009003180589469f1bcd0704f2ab5f5fec2f2370,0x3288bf54084c5734f2327923af15cdf95e9fdfd918,-0x7c503956991e8dd876bb15d17fce55c50c9dcf3c8,0xf9f66cc1af43982065b6ecb3dc92c4bb9c737cc8,-0x192a5b13f79c98df78c23ac8727aecca0ef80c18,0x1fa7ff96b520e40158f42bab4589f747f6ed030,-0x1e1685f65b78aed01e28e8f031cb29b1c17e90,0x14afae5dff0a6c984af764ca9dba6f3ac7190,-0x9b2533e9b5ad70018afa9dd5cf234658530,0x2d9de0839f3798d4375dbd7108c2506fec,-0x770398b29dc104f1c565311b19cec584,0x8db40331b7344a0709cae062d5d2a4,-0x3679939c043aee98895e0df73b4c,0x318b1c6d88170743c6222c000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 21 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 46 indices rho q14 m14 14 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 46 indices rho q14 m14 14 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r15 : List ℤ := raw_ints% [-0x6e7469f27a43fb08cb0b01171000000,-0xabe632b05da62f1d3273f3eeb100000,-0x7dd7543fbbe12ed31d0c36c10ec0000,-0x39a4049e6534517078e48b24fb0c000,-0x1288bb8ada40dfe1365beec94966000,-0x472e6b447685afa789bd3dd7f49000,-0xd3d5ef2e9f8004c1d6f05e5523e00,-0x1f471d9cc69a0041ce8c1a4628c40,-0x3b998d9774ca62d09d2c6acd6700,-0x5c8ca66043689f37d89f154de90,-0x75d170aabee10f5487e91ced00,-0x7b3e21c28966c8137949d54fc,-0x69cf43cd29370000a31545f0,-0x4a346f132067fd8e25f7f23,-0x2a20737ebad3bc48c7a5c2,-0x13144d0280052fc0a6e0d,-0x6bd3eee7e47d3271fc8,-0x1caa6020aae1ce07dd,-0x56787e0fe0c6c7ca,-0xa5483ebd1a06a7,-0x96f77ca2463c]
def m15 : List ℤ := raw_ints% [0x0,-0x34bec5345d3c90f0acd61325413e0a56bba000000,0x537920b7f11bd0df98f9cd588e56e446c8e5e54000,-0x3fb06e767d8239f1a55457ddc8801a6f4d42c6a7000,0x1f3300fd16548d8ede1c87f5d33cf188d2b0f70e9c00,-0xb064ecc9376a3c36d07d8fc69261710a85deabfdfd00,0x2fe479f7838b215568f46e3cf46bccc7cd9a28edc8b00,-0xa644c62ac0e8eff28a95132a818614c508140691ffa40,0x1d9ba6e857b8cfbe9255fabb120cc179560d542a245ac0,-0x468d41e266e487551246aa1a0ec7a3888448fc4d781bc0,0x8e90f464443b773201db0adf9288f6b245bde12eba4d40,-0xf6dce8e4b978ecde1f720c3e58b77e6335ee942f0b46d0,0x1712f289aed70ad8ede738da198ebc74616d7f3c5a66170,-0x1dfae8186612ed15d3b5f3670705be02b348ed8ffd6f9f0,0x21fdd261257182d50182f5931316e3700d0c3dcab986050,-0x21bc3c1a8f31b2f64b5df468e73cf3eb544088adea99080,0x1d5dc941de4527e44fd2c359d1f8d734ddc0561b0447d80,-0x1671e06c54174a2b163572ddb2a9a4377fb1498e007ad40,0xf1060ab69ea2146e225343d29a594a68d745519dc04bc0,-0x8df1afa30a1b0339831f72c5ae96fdefb9ea118a976274,0x493bbf0681e385d92bbc5cc4bea8268f927cad54e2c49c,-0x2104782fd4137f71178219458f2db0e765c8c0b2c2e8bc,0xcf6936f037eebbda62f74f7a7146516e69e5727b88ad4,-0x4697e761213040625ae8ea090760f7ca1039d016bbfd0,0x14b59f6a96343c6efc38a9f8fd90b64a06753f0cea370,-0x5330865086801af0ef3252f3bc55adaee0e3be0bca30,0x11b7b28503dc87ae9e8379eb0b8d7ea8e957daebbc10,-0x32aa7bba2a22aca3681b800945df21af33795753428,0x77f9b698b25870cb854e67f16d292b666ae83257f8,-0xe7643a815d4744629f55579f0d36e024c889d29f8,0x16406d32c3284a5a990d0295da40188e4b2830228,-0x1a9ac6ee45779a15fa09364549a607b7995de650,0x17e483f10bd5397c17af26613cb16d5a9cd44f0,-0xf693145cdc493874f56a95c126972a41ec970,0x6b7e750f1588e1f1a215c48253fef147afd0,-0x1d151f888a4a4f7ef0004c4fc25e6d91db4,0x44e7c21122546c90824d55c711c46095c,-0x494df98e1a7b6b32241da2a36357dbc,0x18adf24171c3a3a0ae61ec3375ed4,-0x1328ca4882217553fc358c8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 21 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 46 indices rho q15 m15 15 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 46 indices rho q15 m15 15 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r16 : List ℤ := raw_ints% [0x1a3ae5d21a97fb6a266d23e4b28c00000,0x28c73acab752ed85c3c4536eb2a2c0000,0x1dd13b6dbdfa8384be3c6ec9e237f0000,0xda3d35c5f383031c966e719d3b205000,0x4612c09f55e895e3dfc6e028cfc43000,0x10cb14fc4037a5597a8f58c2c0da6300,0x31e3792c06ceb5ac09caa30bb4f0400,0x75a034bacc3522c1183d11b5f66ec0,0xdfa4a161efac1c85d254a3030e8c0,0x15a6d6fa45b9d6c37c68e246e91d0,0x1b7c9e5ba33ceec0141a3fc40930,0x1ca9807d7d85f3cbfde59e98ff4,0x18851dc26f943ab6b49d7678c4,0x112035b8c23fdcd933d9e475c,0x9ad41b126953e0837fd6c5d,0x45bd4418da153ec0c2e806,0x1879cdf6fdbd860c79073,0x67516c62d517732b1a0,0x134d201ba11e9f30e3,0x247b7bfacccacffa,0x20dc94d7e22819]
def m16 : List ℤ := raw_ints% [0x0,0x55b6007517826b8718dbdf1c8a04d0ccf0e4000000,-0x864a3c10fe8fa5faffaefec158ef0ff074252e34000,0x6567a9181b66c897497e6783416b31edda164ae4f000,-0x312516d53f925923b43e402366bac2d6344ae43882400,0x112c93982b998b9e934f32ae916f42a787ea5a3abe3300,-0x49c0b2f0e88d1f11a9047421eaa559ef1cbd685e886500,0xfd021fb95313ae46b0f70d5b4bd918d93d0db4bb0523c0,-0x2c7fb07171e2a2dd2af07dca9e9d557b1b79fb68619df40,0x68ad241f8d9fb6144414f2e7fcfaffbef1c52ddf33dd440,-0xd0b43cdd6ff94b8b5f3dd90a0e8f015e77188233fe652c0,0x1645e5869c4c4459b45fae8ba4c5a318da8817f10b3e4eb0,-0x20d3bf1e9ca1058cbda40a8e3bdd246c4d57ae4b199d8710,0x2a01e625c72c37adcc5c48c47103f500df5f5bc451568490,-0x2edff63681ed437b02d4cae272ddffae4c7ccf3b77339730,0x2dc038097077209ca05d4b47be78a1ace5ce1b35e31d8f80,-0x27223098b220375dcab1c2aa0c069b07f04a46346f004280,0x1d5d0b8a14c54f0b4f1f2c1dc12924491ab856ad708ca640,-0x1354073d1171d113b99de712c7e888e3ad257f54b09846c0,0xb26d3e35ef1b467e75eab34e9a8ffc0be289dbaea1e65ec,-0x5a142264e388583a0165e43f80a710fcb9f3cf040284e84,0x27aff1b45113456cd4cbcc71690ceaf55629ecc8be475e4,-0xf3460d74a5eb83610a908cb4dde4afe95a5a11ce55480c,0x50a9747f3011fef8ffec16de5b652bce1cc460bb23d1b0,-0x170282ab8edc3138349204ea5f9847799bbc44cfd0c110,0x59b0c546c0db335f23f5d64d3e8e224e878f4e729f950,-0x127df95c74894d05e269325746d9be9f4531b73b18270,0x330da5ffb001490736a833b67992723678ef6e916698,-0x7459b2ebde684fba9e7546aa4cfa7d484cf3bf9e448,0xd72f662e7f350ca42fbf18695c02c8ceea390bed48,-0x13c2540074a500dd7c2111327700eeaa3e3d8b1998,0x1671d6a0f33c77d7c9138052f8b133f024d608330,-0x130911f142a7204bb56bc20bba50676f97e77790,0xb82e67882595f1345798bb025b9da5e19a2290,-0x4a9f2627fad0a4d85a41c278b2f9dc5782030,0x1290053a10e34f3cb581808986e7b1e4f0ac,-0x27e8f1d48f4e85a47a2f9f2c721f83c3c4,0x25e9f2af4f796b6aa5b697da290a4ae4,-0xb2cdb15f342ec3771f277e22a2a0c,0x767e3441e157d96afc03f30000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 21 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 46 indices rho q16 m16 16 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 46 indices rho q16 m16 16 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r17 : List ℤ := raw_ints% [-0x5b5a9e049ae691d04b9ea4e6df1e500000,-0x8de2b6fd939c2d7a45fc63e476f8bd0000,-0x67a339f5b269287dff1de6b18d5e9a4000,-0x2f5a8472bf53d3fc42e878e636c5a2cc00,-0xf2f532816197a1c504a9c4acc00511400,-0x3a2475f581d7bdcd06646e1fffa3e0140,-0xac73e943526addb4cc4fa588c7d8f000,-0x195e3ad0e1c10bb24227c54ba8719150,-0x3023628ede5be01cdd1db9113cc2200,-0x4a67791e7a9f99050a0074cc1600ec,-0x5e398e886b0129e91c2ddde71a6c0,-0x61fbc9099fa91181dbfd41e25e0b,-0x53901411f27375b036d0536f31c,-0x3a2867820e6ba84b441ff4b6f1,-0x20ba9cd476d794ad77ba04ac4,-0xeac736b315caa54fed7f661,-0x51f44605386b60e9b1a75a,-0x157c3ed723e06e6c09d23,-0x3fbd91f5ab299ef48b0,-0x77666419dbb270384,-0x6a607608c09d0d6]
def m17 : List ℤ := raw_ints% [0x0,-0x8b47c0be4633eebb88654a8e6047d34d07728000000,0xd81b1263213940b8549388a572116332b81ecb314000,-0xa18c8073ddde837fc82a834d9ac956878cfb8255b7000,0x4d7ad9bac8e790eefbfd4e1de21a656b76823e56565c00,-0x1ac8dc92991593d9ce5858bb8f985611718a0e3ec8e4d00,0x71bd6429ed9fa975223124741f1857d5809eeac6596bb00,-0x181a9044c9f76940602caed9691e7db81cde6d00d79b9e40,0x430319e514153879eff64d7ff1b3daec1a75272c72a206c0,-0x9ba8b2ff8f29f6b68b839541899326ad8775ef172d0d77c0,0x1324cd7340bfcdb08fdf5488001f49105f0c471094e080140,-0x203e49142afb1f4b31f5e78f478606dd990bf5db25fe033d0,0x2ed88ad2d8bd678da2aded137639fbbee49fca3b768777870,-0x3b0e0d88a101144c0b637327ba650f234ec2a271d06c9d8f0,0x40df02722c45b1cac8096c9998a41dd7651d5cac1c1f8a550,-0x3e47f6f2719d0df55d7fddc87d34ecee90cecef6aa8c09080,0x345bc0de97f4fc47388ab3364df6d85bf22069ac1c516bd80,-0x2693a5aa868efaef5efd694a633ecbc373627328e0a71f140,0x18e8b099622183ff5e1de80fc5721c630754c71a2914a97c0,-0xe150636635ce976c0c4c8e2cd6a93fb2a6289c5bf3f3c7b4,0x6f52cb1219ffa479125e1dccfb0b593dad68799919ff685c,-0x2fefc1704c08ce4af2069692ff77f7353dee3e70db93567c,0x11ec112f727ba1177d69c82db8ec421ccb99682f2ae40e14,-0x5ca170bf3082a5d9d0f6503fc4b23ead92b2826ce8e04d0,0x19b1f8e9322ba70746c7bf22823ea483a1bb83797213270,-0x61303867fe40803b7b6b1a6b0a86eb0a741c667b759530,0x136597e2b63d8f0ee727e6ba254fa139a11d62a027b510,-0x33b1c51b844f19a5ead7110b5df8db9680c14f66a9aa8,0x715d2c27a9eb26ee75147a2b8fbaefeda7d361b60378,-0xc8fffa3577ee95daaf94d2aab64dbf21176c00fa578,0x119e0a0bf478259a786a8522fccdb64b475d5e758a8,-0x1301106bfead376f25b6d24e22ae0b073ea4e15b50,0xf36742b73d5aa39710b4b1b354c246959cb643f0,-0x89ea6506a75a7f1faf753d70fcd8784b6d51870,0x33e497459691610e258b5dbf021a1d1d7e54d0,-0xbdc2746e0c2fc970c0a0bead81b4672f46f4,0x171f7e3304c494a7fbe68297a1945c5a91c,-0x139adaccd4b17203f3092b997aa13eb7c,0x50ec9f1ba3b3e318dc4a9896323214,-0x2dc8055d19f46ac2a447d220000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 21 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 46 indices rho q17 m17 17 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 46 indices rho q17 m17 17 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r18 : List ℤ := raw_ints% [0x127b91451b4f0f1bf0891e00ac7769e00000,0x1cae58e44cd0f4c181ffeea4928e4bde0000,0x14ede6b0deefdbc8e44c7fa64566a3f88000,0x98d815f429ad8d9198c8ce9d031551b8800,0x30f48269bbee1ff215fb183fb3f50c68c00,0xbb34b000576a15a3c3a04bb869444ce380,0x22a77d73973796712488f9382d54a8b0c0,0x516f376a7cfb05e4b917210d7550b03e0,0x9a4238d52f897fc1f022e00f2c118330,0xedf6b918a392a5716395b3659befb08,0x12cb379b957c3e03b5d37b9ddad1674,0x137efc2b9a6d401b8f0a8b4f4e8162,0x1094d0f2feabf3fce4cd5538e1855,0xb813106c3526796020b3d0f8a62,0x673a45411182746aa67e387dcf,0x2e18975ebccc2c344e5226130,0x10045451967ba1f90494fddf,0x42d3bcf6966846a07debaa,0xc505957a7e914116f4bd,0x16e593cbffad89d317a,0x143836d1a11bb155c]
def m18 : List ℤ := raw_ints% [0x0,0xe2549935321463f0bda499275c74b75d2c1a10000000,-0x15bddce18d38dc2dc4063f0b86fc86db923fbc05cf4000,0x10182bb01ef6f9ab2d6f430629f4cf6ca25a51547edf000,-0x7a417128619b382b1aa2c0a47f98f6de49b9b8dcda86400,0x29d2004dab24d169b0354314ed79b833b4b4d0ba0939e300,-0xafa788a2e62fb54e1467e6848c224bff82df13c20d083500,0x24cda70b4e6255025c874e2bf22701499cd3da80b76ba5fc0,-0x651d0fec233af1a094cf9643b56a75bf37b4c9cfaa4c4d340,0xe7fd36f7fa3ccd01b63db48bd70501a00317d559a7a76b840,-0x1c2a83eeb3b50cbfa8af0d3e865acf4f01ba929c9f53a45ec0,0x2ece28d08fb64ab076317bcaad838c724247e9dbd3d10379b0,-0x430d712e1b86d2c2fdf7b6d86d5c6663f567a3510b73d93810,0x534a7dbcbda40e859626b8eafe3a60306ee58f0eaea2738d90,-0x5a172088f85f987116ea15dbead1db7db82c7c4beed93eca30,0x55197cdefe38b183293827a3b7961477103e0992f1f8de8f80,-0x4654151734990fd7461796e4f155888f062baaa6dcb5b40280,0x32e409ec3605535bf94d799b20c120544a20a4a3862293ea40,-0x203d6d6da4282384447c9c730245b1079a1e3f2f76e24d12c0,0x11dcd54c5540124b944a719c4e9086b2979ab1bb1c9c8216ac,-0x8a37be6fea31b9f7f0eda21d0b7cc8b0c333b888cdc248cc4,0x3a2d32a1817bf26b6e8da103d9e9feee3906fb41089411224,-0x153a657860e7ca0daf5c7e13af87a66624b175a3a6e3e52cc,0x6ae62d06d049e3bf8aff1184b00aecb5102fceefa4ee64b0,-0x1cd60466579e8b4ded8579ad578c7092623c1ddf75903a10,0x69d501f4d2080d364d9a8285323eb7dfdf9ded84d358650,-0x1471d8fbb5e7d93edeec4aa047f98a2b8cf124ee9f2d170,0x349751791ff272061be68972a4290bb49c47763a274c18,-0x6ef47243181948ec17b41d1f4346155b0f88ec726dcc8,0xbc8cc6ea1bbdb7db4c3b81fe1e29a4253a3cc8de65c8,-0xfc4e39dde79960ba69b927ec32c6c8236a1c09aff18,0x10258e27bbde0f5dc47e4294cca1e30b5a37765e630,-0xc3173b3b40d4d70f5b8f103ef20030a80f6200090,0x678227494e4c458aaa65a8c67287fc0547b76390,-0x24250d776fe7e0f31d7abb2edfa46946871eb30,0x795925acf6631fdd138c7dd4fe0dc31643d6c,-0xd666d816da68387ab6a2df03159a1a1a604,0xa2286f7b0590ae09a0c328a495fd34724,-0x249b7849683a594024dcec3ad1284cc,0x11ae32aa1fee2360b34c506c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 21 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 46 indices rho q18 m18 18 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 46 indices rho q18 m18 18 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r19 : List ℤ := raw_ints% [-0x3835a783c0feeb64d0b3cb720d8fcb2c00000,-0x5727aac3637205ea8974b8b2fe1b85cec0000,-0x3f8b1166f1ad1b81af6231e1ddbfdce790000,-0x1cf99744f06c0ac04bd63e0ee8ac2055d5000,-0x945494f098234592a1a6b077d5a3f3b5e800,-0x2368e4ea75accf3eebade6a3be727fc75f00,-0x68bddebad9b0274b6e658c18ea462251080,-0xf5c889260acde2da3f39e3522046746600,-0x1d0d8cf1586a5b8136220a5ef7a55b8920,-0x2cbd5da701332d5dc7765db56dd2b3b20,-0x386ceaa0e3195f96a87c0b324491beb8,-0x3a68497b40692bb9ee93df5787af1e0,-0x318e2a1c8516e665f3a77f05946e5e,-0x224a35b6f529055e4b77604f00797,-0x132bb3977f2d154fc4f0a0ad251e,-0x887ec5e2321336dfc243e00fb9,-0x2f3d77b7aa18d1e24edb60950,-0xc43415348dab64647bd4e49,-0x23f68d90189b0e62cc5716,-0x4275b15dcfc58c1363e7,-0x3a4342723c6ceed746]
def m19 : List ℤ := raw_ints% [0x0,-0x16fc978f671612267342b78dff63da9f767aa5a0000000,0x2301e443f6ff87eca067ff657d0aeb7df5b34453d3d4000,-0x19ab4154bb490bc811939d9dd19ca2c902c079ae7a3c7000,0xc11178a0374a74774e69500fff6e4b31b72e55d0621a1c00,-0x415e6eafab473fc97e70afb836a90bc8bb99e7d1564bb9d00,0x10fa5e0a7a9384ab0507ac828317696e6ac9918b51769beb00,-0x38497831d0f4f739d72fa37d6ed9e6958ba30348a1b0618240,0x98dcc1b0f2e1c2aed55419f86a56b39825f23347193f6a72c0,-0x15a81ac039e147de59653754e3a3946752558d9da7d28fe93c0,0x298aca7a821b48c698d4d7c6388328a75868903ee12c2a2f540,-0x4420bff0a97efff404e511c579bbabb2e9f750676651533f0d0,0x60424eb43bf1b5b4e9dfc5f2cb3dc3eefa49916039f897bff70,-0x75d9782b5d2af9736f0ae2ec84aeb96627a5fdedbafcadaa7f0,0x7d8b1c32dd699a588f43205474bca4683976ec4117076713a50,-0x74b41b9cca52897c57cfc0663dbb311ec612a7fc09c67699080,0x5ed4e40bbcd55afbd5c9b7d92972fe3cc6f0b082e4ec272fd80,-0x43689f8ef84a6fe2d32ca9081c25ee0f51c89be8215970df540,0x29e7eba15726a217285a1a86f96c349d7c63e0ba5404e3623c0,-0x16c2114967db1cc362243421e1ede3fe766a31d2776c9a2c0f4,0xac64338374fd1191d8a78f1c5f38bc171243bd16831a05881c,-0x46ef1aaa5b022c0d9d18be1a070b04ba2721142608d4d3603c,0x19437f5c27b67d1fc1b3dd6cdf2cefb234ebf5992763990554,-0x7bf5b50122bba9de3a1f3638944d9fa7505e17c7f8e0e19d0,0x208462df9e028805535d399a7df7dd8c0b9fedd994a65b170,-0x73cc5c3c8ba8682b617a660276fc3bf16513dcfb9f161030,0x15a6a95552b8f4f6d83308847cc74b5ab7be8fc2aa3d3e10,-0x35bfaba286eda247b4622880b6fc0e0367f80bb3f57e928,0x6d129ecee23004c88f80a12285a6ebabbcbb3b8bafe6f8,-0xb198a42e8c45dbc894cc8370b16bdbe237ca9b74e58f8,0xe2ae0ed298682d2bcf5a7e5038f6fc45077b97bc9728,-0xdc392509a5ea5c6c0d5567d38f09fea9711d80a2050,0x9ccbf514a31c94d24a6e2458036422910801b632f0,-0x4dd9a3862cdf6c7bd1558f9a56cab936f2938d770,0x1936541ae2532f288e1699fc61e8c4253920c9d0,-0x4da8f41eb8744378c4cd72a0c8b85803584434,0x7c44c3dd764ce962223f5628f4c84d5c84dc,-0x53cdfdd35fff034a90193466a6238df53c,0x108d43a26eae315b04e9c5650d177954,-0x6d33e7d965aecb9d0b1c32480000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 21 66 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 66 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 46 indices rho q19 m19 19 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 46 indices rho q19 m19 19 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r20 : List ℤ := raw_ints% [0xa1f7c8f012505585df2a5fac67987404e00000,0xfaf3d59f597da2209718692d0240fc479e0000,0xb6d1621d2850e5fa10f416b2394e6495658000,0x534a04ca4b098ed90f24d6e5346835aa800800,0x1a9f71d9ed41cfff36ede151110163c015c800,0x65943ae7308bd9f39861984261096f03efb80,0x12c1e33538a05e35bc5205ab58b5818c22300,0x2bf56d4eddf319ec41e83b47c526899c0e60,0x53053826e95a28626724f6cfd8411fba280,0x7fa542e2e0d08ad7080583ea3c30bf5928,0xa0b4bcb7db9af1022726aa6725204d340,0xa6079d879246ff8d190488ae8d4a0dba,0x8c906a1037e43265fba4ae94a91d380,0x6107ae6924bd0d980a0afe34287bd0,0x3619e633e4ef6db43c83f49fd0b29,0x18007a827cdb7f06d2b3a73bcaf6,0x8473f375ef88cccdc303c6ee87,0x223f64a611bef6f2a29cbe054,0x63fc8a1d4a0defc93c91e97,0xb7cffcaaf296db69954a4,0xa0295d81f896d6727f9]
def m20 : List ℤ := raw_ints% [0x0,0x255a76490783dd7e7b4c6a46bf02434320874d240000000,-0x3861f4c3f2bc22360b93a20039d5a037fdd5966472fb4000,0x28f634417fda9efffa8118d1f07471ade48c315b9b7e6f000,-0x131256153879ce5cd3ef6c8fc135644de12e061bd6d0aca400,0x6649e0211875a720f8f7ac18fe322f0d0a2322aa5ec1289300,-0x1a4abe469711b10293a5e0f4f51041882d20a98bbbfcfed0500,0x5639a53a86a06ec083f7fb85623baea70f32ed9afd2f6035bc0,-0xe7884481b8daa84ddce666dcb81b9193b35ae66abd2a93f0740,0x206aaa9556d54b912d1c95030cffb1f3ee3c74d61fac2b63dc40,-0x3d6b062669351184e3fe25d31299fa3655d8325dbfbaf8552ac0,0x636d93f479542fa551880e0d4108c351d9d5234f249498af54b0,-0x8a96b6e630a559131f8ad4e4149dba6a8f7804e63bc1e617f910,0xa745662ea21863465076f908fd284bf210352a4add0a7de32690,-0xaf89e0241dcfdaa125f855bcb76896ac61b3a3440644381b2d30,0xa09ea91d85a4c98dc93d2994e5181d82eae4586ed7f91e7f8f80,-0x805baec7cfea88bdc8b57b05d510daf4faad5acf1a88043bc280,0x59a50e27b53fea49d8cfb56b51fd9e158996d1d480d31666ee40,-0x36b282e7cf8e484d7af58fb3ef2c04305a9ca43d08e6dfb51ec0,0x1d1eee6d9c3cc00cea0f15c4325f406ccbb805bb3038c213936c,-0xd7f9c1f15bb0bb4c8c93f4e391af5fb4eba5502fb3fe6f3ef04,0x56e2a5b38a0d5030f8aa50e5b40d8b840c3e91cf92fd4b13264,-0x1e34e64d4f861dde564a104b9017b1b5d35da8102c30065498c,0x906bb3da420bf27c5451ba549ac6a2f259ad14bcccd62027b0,-0x24d76088ea8bf499e8b85f04408cdeb362d5df0d411d744310,0x7f4beed5ec1911a7afe6c08466f06597c5c6e8fe7de83e350,-0x1708ac9d0c55100a5494bd8b957bd443d2ccf5546a2671070,0x372d189b611b522ec621957530a639f4f7bd8964fb7e0998,-0x6bad27080886f0832cee63b06ff0e4f2afa57997774dd48,0xa7f040e8644bbb940986c0812968a17bcc98c3cd64e648,-0xcc6262dd43e6f2bc001453ca9210ddb5129628946bc98,0xbc4f590f8af8ccae5cc45b1b75097eef02f2227a7930,-0x7e580bbcc8f16871388e19a5d05ad3c5ddcbea21990,0x3aaad14f323611d74f639f1bc243ecac35c50f3490,-0x119c0595636d307bc8662adc5a2724ef2603be630,0x31bbc77146f2afd01e001bec694651e068d162c,-0x4808aa209fad19bb44b6759830010842eec44,0x2b4c3b087a4c0bb9ad24ee20e06bb6dc764,-0x77af18aea1174cbf6317199711a5cb8c,0x2a23535ec8c370582cd9330300000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 21 68 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 68 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 46 indices rho q20 m20 20 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 46 indices rho q20 m20 20 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r21 : List ℤ := raw_ints% [-0x1bd3e0b996aa9b4b5b891829f7e7c76bc4500000,-0x2b1642718ca0f0f934a1d49d95db08befbfd0000,-0x1f5d8fa78f0929956f70ce633e4128c3e9204000,-0xe473015a7773fa65debfeceeb1e0da67486cc00,-0x48f521fe576c67b0d3c6a8fd0a29f93b5d0dc00,-0x116190c4cf1808b5379082f2ea84f3fcad00140,-0x334c573511b1e4cd2af37459675288eceaf780,-0x78142625ffa9579d744af837242c7bd893850,-0xe27d0dc5f93455f11e4137010ce9fbe0aa60,-0x15bbc8f8e082533d1095e7445e3cc4fbb5ac,-0x1b51d84c3e415842eeb3396548513a6fd68,-0x1c2d02b0cd6323ceb8f827396d7aa0059b,-0x17cef0b1519463ce694dfc708461ec356,-0x106646aaf9b605a715418d63fbcd5c95,-0x91f3f434259a9eb01d073668393250,-0x4094099bacb3a6127d183f23149d5,-0x1634bd455db2381cb99dabc9f86a,-0x5b8d998730ed7894c451c69e4f,-0x10a401f7138bdf8e3073b3ffc,-0x1e748661b366f1482de05f0,-0x1a664e0fa3af1e0cb222c]
def m21 : List ℤ := raw_ints% [0x0,-0x3cb30036ac3647ed885c2cb2f663ad4d14dbdd5a80000000,0x5ad56e9c0492dded759e85e908db34c4a73fa3e356a894000,-0x41667f188a42b1f4479d4ccf4880973a6782285efd458d7000,0x1e2ac113b209e625d322d4217176a85cf18320d1045d1b9dc00,-0xa03b1c360bd0d5f79faee09d78c124b5a18e246a088dc35ed00,0x28c50a895ea0269adea0485fdd2c236bcafd02f2416d9adc1b00,-0x844c2d5ad7f200470850de014ea9a01bb80714f7f3b07cd5a640,0x15f56f427e71f66dda4fe38d84fd579641c977252499d42299ec0,-0x30a00b29b9e2e104ff88fd3435d641b5212b581f4e33327a76fc0,0x5b04b0057e790634fe082493657b797a1ab5bad77d47f30bf2940,-0x917cca6e1d9ddef3055af7a21ae34c32854e4f52b38778ed37dd0,0xc81a36719275f5f61ba035ecfbf9de5b31644ac6f96b66bc0f670,-0xee26d4d1d06dd9151fb5b669b534c17e0f20908130d1b6b4a66f0,0xf641d422207a33d42c69aa5b593e6f7efe5df401d0bcdcfb91f50,-0xddd7b931fd852ccaa82326ba5feb029480d172e49ae4877429080,0xae62fb3c26d02090e1611bb75dc645871f3d5450425bd48833d80,-0x77af12890762a378a1f4fcc68bcfdd480beb98e5aad7a258db940,0x47af92a3b7d3fad2fc24a93fe7436f23873a3684f9e51a51cefc0,-0x256bc81a7c5f187c504b1c5a8d120f11c52c41a30e9d7a3ff8e34,0x10fc40d0570e22f85c7e5e89f8cb2b5dab39616c761ab9f6263dc,-0x6ae6e53c1337e3d4420a5f759711d40195981ee24694678d45fc,0x24482237d5d7c2e6201786622838655753bfc578240caeb33094,-0xa908e6be9ca96f12fab90bb1634456e7f4db84c7786064a7ed0,0x29eedcfb9f7c18945609e59f04f11d1f2624dafffead9d52070,-0x8c936bb835a5b5b6c0e5b640c4bdb08873b8b554bed0b63b30,0x189d5732e61aff11482f41a87c0262ee0b2563ef7554fb5710,-0x38e2c368c2a8cdd5c952ccd2cedb30aa6dc617d86556d9fa8,0x6abb832a14bf551f597151cdf386cbb461faaabaa6ce8278,-0x9f6861883621605707f6523dd6eee078523294c59bdc478,0xb8e90b4080d8adad0b5561a916e58016937f0130023da8,-0xa17f217b2071079f1edc58ea2a92a084d38a165003550,0x660d28d4bc6023d703e40f2f8eb3c8ec70f5516c11f0,-0x2c4a970ed9dd3f0e45b839e2fd6daca5db224490670,0xc5058019305b3e0c767260b62a0b61229220c0ed0,-0x1fde102729927b049373031ca383207db4115574,0x29c1cc5ae92879b432b52087342cd0ae93dc9c,-0x165cd79f49bd8e6d652dee244b21f02ddafc,0x36103656a53f73650859fa40cbbaaf494,-0x1040d2ba75e70e56890cd808200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 21 70 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 70 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 46 indices rho q21 m21 21 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 46 indices rho q21 m21 21 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r22 : List ℤ := raw_ints% [0x4963cc99a3b847ebe8f07dabec63987143bc00000,0x7190035e0499eed5743928597ee1df725128c0000,0x529ccd8f786efc7adffc17f65e79650307d8e0000,0x25941f7702d05e478c9543b55a216449135215000,0xbfdc89f0c5263764fc7c90e6913f2aefd2cde400,0x2daae9faea7351b48caff28d672fa8fcf53cb300,0x86a6a88d832a126140a8e450e5709351fa2e2c0,0x13adaa7480af36d5b2df12f497230371f89d840,0x2512be90d69d5b590ca57d016f841ea63450b0,0x38d8bed87cf9dec721f171bd1e2cb6dbdd5b0,0x475b4fa84de28fd2a1dc3bebf61f41aa0114,0x497a4d3848826446163e55107271f4a0c5c,0x3dfb183d9bb0e9a476307f6713af17af25,0x2a9c86993c75d7fe5483dc91faa3bb626,0x17a6d3284e8b3a4a4b0d0799adf09ceb,0xa70a4fced8af5e00da53652b595c98,0x3949270c3f20a01a03709cbb3ceab,0xeb798fa08b281228b2682c4b09e,0x2aa78ebd86942cb18c60abed71,0x4dc36365b349cbc0894e73d8,0x431c012d36ee6287bed3d0]
def m22 : List ℤ := raw_ints% [0x0,0x62a2e058d7d834e1fd95c8a2d061f99d41e547b3100000000,-0x925f9917c8427487ad84718239624f64aa9a8a899847674000,0x6879670d4375761a32dd85a6e2f9ecb263a2eb5c2e7eacff000,-0x2fc13c0d057c927fa3603a0b846968a3b2a7362ddcb7a314e400,0xfb41ebb437f1e4b9c615c5a8efceedc4e633a9cd6c372bfa4300,-0x3f4d566331c7e454c6ac3567b50fb1ac360cb99c903805306d500,0xcb4e0ee7280c88985e60b6a13a728c21092d9743f8c0fe21c17c0,-0x2161c8f95af1f93e60ad88362f91a245d27f4560886384ff9c7b40,0x4916d0bec924406277b63c16a4764a086c0ecb20138458c7494040,-0x87328593892321fab86de2cd4ab78272fc543b59c0d88be264b6c0,0xd56e013748654447686e418f5ade6b5100c86e79dda3d4dfacdfb0,-0x121bab84b1273b57ea8811b8abcf845609cb3bcf468283001ceca10,0x15418c49aba34b1e5aee392ef92cdc4a071eebcc66548b1a0da4f90,-0x15a975d7eb5876bd91a620134480aa267c9dd7e9714abe37a07c030,0x133770c85495b32e5030e8346383bcc5bf66de47f1dbb9c74cc8f80,-0xedca5baf9c969684c0dcc28bff20b5ff2ce81b9e3dd97de1e38280,0xa067bc57e79343675ec2704d09d4b9d29491bb79f2ec3de75db240,-0x5e5446b90e187938f17caff0b1303edb664fd33536ac4bb3806ac0,0x3049b237b8de0fa9b513d748cdf54a44a253d886b73d7a12539c2c,-0x1577096ca094b05fb95ebb3d6747bced51aabbdcf29877cc11b544,0x841c07b50bc77d2b210c119af2468285a7912e5cd26e6797016a4,-0x2bc61915787c99f995321a1c68d948e0f3e52f03f05a52a13ec4c,0xc6bc8b30e15628043362da0185ba7b2846f284be71e78f3d1ab0,-0x2ff18e772bc220b4efb99f43d0a598659945f50dce78f6a1dc10,0x9bee838f0c3236195a4f92183c0c89c393b858ecadb95861050,-0x1a6b0d05d8bf1c39453a884e14b375a63951c82b07b92913f70,0x3ae4c3726ad7dff52375387d968792db7de58401bde6bf1f18,-0x6a36e6d46f1802e74bf9ff44f1d9b808ec967175b8e8665c8,0x97dc75fc3d9da3069b09271e4a7d17202dd515e63c85eec8,-0xa7d628b9d508047545b43927d78f3f5f7e428a77331d218,0x8ae35b04acd8cc660ce3cc29059cdfd906a29f0bab3c30,-0x529daca97a6aea131c5371f5c9665d1555ceec836c290,0x217e78a45245e4a9398a223d4e62d1b0d26e80129590,-0x89eb0a67f5deb9b8bbf8f39b8dbd257daec6f11130,0x146de4bfc1e0580495c4b9447dcb5343b36703aec,-0x1834ada35abcd72a05d5d2eb60272ab598ad684,0xb8bcf4651bb6ee757a51d69c19d31d550ba4,-0x1868fd888eb18a1d33d360adc4606dbe4c,0x644429fbece3478ef58ce2aac00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 21 72 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 72 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 46 indices rho q22 m22 22 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 46 indices rho q22 m22 22 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x431c012d36ee6287bed3d0,-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r23 : List ℤ := raw_ints% [-0xba8fadf0d9608b26772ca5ccc1ba1ff04f39000000,-0x12084583745f8c01e91067b857ea94b5c3db7500000,-0xd1c0f5d3050122a2fe93fd43f1b6c6bd133e680000,-0x5f58d68cecf3f09411f708ee6508aef31f1411c000,-0x1e670adbd8ca1dc9163ca2606d35ea9d0f937df000,-0x73b09906decf17fcdda90e64821333fff03d88000,-0x154ce8fa8a30c2e6a03e344919180c6680f113d00,-0x31c212766af0a00b8eddff6662963e9949958640,-0x5da44fdfdb322c917caaa757df2219f44a463c0,-0x8f6b22004a94569fc3c5a6739135e059464510,-0xb3cb49ddb1b7df2ffe4330a34e3b756ec9750,-0xb8e054eb474bbdd8b9c5bf273cd11ebe655c,-0x9bb4ab65c1ffe0dae5f9b8b28d96145a8a4,-0x6adcb4aea6e852089968d9040d0810556b,-0x3b33741f7c126575065da3368c22f73da,-0x1a1386f5ccb9f215370dea28617ae675,-0x8ebec2ffab9f90057273ec26f7f168,-0x24933cfaf4ade2fb87f7e89c43835,-0x69b05546bd41cc131e2e83f4862,-0xc007d1bcb7bc39fa0031826bf,-0xa515e25a4cf1591a1278d28]
def m23 : List ℤ := raw_ints% [0x0,-0xa048ac905ebf55ef3c136608929f359f8b149482fa00000000,0xebeecd23aab6ebf38c71a9cd666cc9158f2503775b5b9154000,-0xa6fa75b1fe0c027d854293c07a01af6ff2c6d3b4a5212e4e7000,0x4ba7956fb2d9290a7c4f0918d19e6362cb82ef6f8aec2eb759c00,-0x18a663412b636ef7d2b7a3805ad1fbbda10458a57ba846f9cd3d00,0x6269cc30986948b18fb24ff417145fe6ab4323c247ec3d2a874b00,-0x138e6fde92cccdd8975a92ef9dbd9334ab25c11a2abd04274dc0a40,0x32d698ecce2f9b5317bb350b5625cb97fa04a997c28f60b584b8ac0,-0x6e15a2403328a61dda8081c60f698d7f0f580dab19f79446f240bc0,0xc94718b8a30545f3ff6e0ab2c5fa1665a5d91e7983f3d6b46509d40,-0x139e3aa34e18df37a26e0afa2622b6d45b1a1b91575579ddd2dbdad0,0x1a4a7e43482db1ccaabff7f06f835ac6d98a28a6b25275862a855d70,-0x1e72111afe5267b413c223b5c57fb7d959312af4ac97cc1d8fb015f0,0x1e95dd437713a168d9b99653c47511192eabd3cf76edfc4aac6d5450,-0x1ab965b6c9552df4814cad26d4d31361d9f4a516ee93c3f3be7b9080,0x1456a983edcba3aec0a87e1a2698b720aac7c1e4b9fd74aef9d77d80,-0xd7cbe2555338d5074d71b166010d0df6d6fff94cdffacd378f53d40,0x7c9db0bdd5744b5ddcbbcd590709fab4d10e54fc22f50e6455afbc0,-0x3e90e677a90bf6506494ab652dcf5698cab698ee780b059d0af6f74,0x1b3d9bc872f1c86bdd3ba70b9368fd6992ba0eeb0717ebf5327bb9c,-0xa3f76ee78d848d5d883464e163a9ed8cfdb9cefec71146c468c7bc,0x350b6b03c757f826f1a835a73b7ea59fa2c74b42478a1c2f4fcfd4,-0xeab057130cdf252401da6caa11fdf027d04c8c27e9f181c1e33d0,0x370e930c85c2a4f1430015274b3f96f6399573837331cba867f70,-0xadb744297003951f7b8843c55b5612febb8c2301b834c8991630,0x1c79466da9c194bb613b116b4ad0b71234575b289b457cb30010,-0x3d382793d7514270fdde4bdab5e9233533e8f004edc4faa3e28,0x6a1a073cf2b4a063dc7bf03d4fb4fcd331ba93488c487955f8,-0x912d74c335c540282947bf69979498c967a2af595a06d67f8,0x98cff7c45c3327f70e77a250ab97440fb0604693c742cc28,-0x77c2980d40fc9c9c42e8004ea4c0e360c544a5a5f4c9a50,0x4305e9706211b619b99dca083740c80e901ede40cee0f0,-0x195e254cb6838a5963342247cdb43e267d2cb7c0ca570,0x60a2e8cb2248b5ffec5ac073fb8f30d4e45f76d23d0,-0xd1a1115711c74608e39bcdad8336d4a59ad0bbab4,0xe07ea9953ec8b7815388b52cdf6704859a9705c,-0x5f59910bf3a0555a1d62013ae85f930ab5cbc,0xb0435898745c235ebc5b3e4d242669e3d4,-0x26a4ef28c80cf6831cff0fd3c800000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 21 74 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 74 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 46 indices rho q23 m23 23 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 46 indices rho q23 m23 23 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0xa515e25a4cf1591a1278d28,0x431c012d36ee6287bed3d0,-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r24 : List ℤ := raw_ints% [0x1caee3bef3a484cad8673a8f16183a099558c0800000,0x2c55c0aea186645b9c7be5dbda51f7cedbf5b0c80000,0x2036913afc9735e4bc0798acbf8f92dc28e1e9fa0000,0xea23ebed2604e77b78383824815b7d925222356e000,0x4a9b5f9781152c63e952cfc4a05f97d3889da0ae000,0x11bafb1273c8a83a596d465a1392060617ded9fd200,0x343044080f0f192fb5f8c3ab7ed6cc5fcca1a23800,0x79cdceb1cc9a9efe5e665dd434f6d21f2c6ccdb80,0xe500e86a4ddc04e9fbcb6bf266d2b6d0c0f187c0,0x15e5ba706a90b8877351302d819d70bfa7372e20,0x1b6b47b510020040aedcb7143bad5d14df1e570,0x1c28673fd0a7044c9d6bc0ed1bf13062bc71a8,0x17ae7175717de554afc90feb521c02d838924,0x103a38c0e59d4114bdbd6c18690df827efe4,0x8f9746e622b1e0629260eb4ce078b86795,0x3f20867f1bb9954a6f61bc17a16577356,0x158d5c41a3d7caf68acdd9aa5f7a788b,0x5825c865f726a7cd76f3776e952588,0xfe0ab1f6fe9b1cdbf07b5971e84b,0x1cc3587dec0e780d44c2d103e76,0x18a4e759cd408af8380d11dc1]
def m24 : List ℤ := raw_ints% [0x0,0x10476186a99f6eba4c19f85cdee42b72342017154d6400000000,-0x17c62732b4dae5437d118050a10c7235f1f19974b168e93134000,0x10b02b161b59a74e1f50e8fc007801fa254de1937c04c205a8f000,-0x77f1c07dad7f0b310dc58dcd1b25c6d8267fd37a3011fb6a212400,0x26bb59105215b461e14cafdf9515a35af140066ba5c97037f5ef300,-0x9930d8a482d075592f8f7b285542153555738b04d2892818b25a500,0x1e24dec20b85c2b444791b5a762fead1a0208d1c94029241550093c0,-0x4d8eedba28a12fc3ed7ae87bbf9fcf4856346e59985bee390b912f40,0xa622e703b5c4e9b1d5aad1df747b03f9a58f11d042df8a8830cae440,-0x12c5371b2cf3162a4e1a9a99e062966047c27c461fa1216f3561f02c0,0x1cec695026239e0fe0fd2d3ce3c55c7e9f75612bef90d72b575771ab0,-0x26465f3201ebb1e07378ad9aa87e50e70ccde10b6ef0ebcdd2d2eab10,0x2bbc54add7b09f24f896a5a7065b8ddb92ce6d6d7732ee9a379e20890,-0x2b5212df5d3e8c1d34d09c0054c1c18e8cf6327edbd14085ad7578330,0x254a1d956269768c472fb207986c1733399310ec9bb549938045d8f80,-0x1bee93c41f32071add76e8926a4e291bc6e572a5e0b6c89eb08d34280,0x123658299320d7cd10011408564f7e0fe5d8452000d7d013fee643640,-0xa544549b95c1b713bfb5b1ab3dd1105da6a5e86a9fea1969f5d2f6c0,0x5164837d24b0e639953e52645e6a198febd9a44e3ae353ed760af0ec,-0x22b6bb35ace8f3e495b1176ae50c1f0548114e661d47a3c8e7181f84,0xcc5e45335ba5317b3a91b0458ba5a5ba932188ad8dcce4be8ddfee4,-0x408e1b748eb5e1ae00a26b903f8c8d3041357683df98ef294a8fb0c,0x11657b18e337194daa92fd7a4349115aef9f5ff10f05dcd4e6c3db0,-0x3f7f63614e3697652fa77f8355639493b189254ec4a09b82920510,0xc258f83b2caf3b1a701edaae68ba246e783de274d081487090d50,-0x1ed0bc03bfe36b7fab92da5a924003788b0367d8d007fda205e70,0x3fe305d7c870f3cf2f0805b2453df3b3743c09c9c6daac400c98,-0x6a60ec9c5b29b3cc5beb868dd23179942f58ebf8fb89d5bf648,0x8b40ece7f8f212df68429068d2f84161b61b8c7dc83e11ff48,-0x8b8b7a3b93bc58ddf666992fa1f96610deb80777fb199bf98,0x67862a8894776dadfc3cd9dd041542c7e6571ce38e2b2f30,-0x367af8eec4769f5c197fc26c340124f78fc7accc69efb90,0x133d78b87175d285785903d6fd1f88e300b7e191fa8690,-0x43c4aa2c3a87d5f41831c6817a9b601922a6e5046c30,0x867c05f083e7ab19155d9bce07a3fbc8e9eae26bac,-0x821e077a0332ed6a51b46ad6efb20087c853a4c4,0x313237aa3b814fa27dbb3108ac739c284953e4,-0x4f83796eaec75793a6dd9b69172c9591d0c,0xee37d24ec99a73c34aa587513000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 21 76 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 76 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 46 indices rho q24 m24 24 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 46 indices rho q24 m24 24 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x18a4e759cd408af8380d11dc1,-0xa515e25a4cf1591a1278d28,0x431c012d36ee6287bed3d0,-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r25 : List ℤ := raw_ints% [-0x44827ba7feb5fc703058c05b72ef7866b64d9c6d00000,-0x69d78a906bb1f6e062ed49881e59e3bd8d29bd5450000,-0x4cdcadd07a27bbc8c67bcc2599097d229cf68b3684000,-0x22e57cef4c9a1179829bab393befa0ccfb7c26f9cac00,-0xb1cc5d823f53dccd8da9e4ff053244c5c9f308592400,-0x2a39803c9c3dd37f51292baddccf96ada5c20198b340,-0x7c3132c901af793da2fd577007f7dae4e33562bb900,-0x1219db6775c27d15ece6fe6b9342c62e61653bdddd0,-0x2200495917af8e8208aeb06b1cc74b27946fd22340,-0x33f7d558b6e6ad4fa66736ba7e188888769cc19cc,-0x4100b1235834d09e8afbf7587e387edd3f973cf0,-0x42acfd7f3b810559d16c84c90b5d18d88937c43,-0x3800f6c250a9a248e1ff877c134b30eab747e8,-0x26525b9da79d187691d500d18df3a3a330599,-0x15291667df6549280ac0dcb24ef5a397ef3c,-0x9496e6ad90a009138d6542f392a7c6c959,-0x32a22bff83e272fe5bcdcfb699704ab0a,-0xcea6ebd8f88e8383ad8bc854fb1befb,-0x2522c18bea2ebeed2996d1e562dd48,-0x4318aa84c679220dfa6b7678aa74,-0x3951727f1563e5884ce566ceda]
def m25 : List ℤ := raw_ints% [0x0,-0x1a73fe7ad3a313eebbaa3396ea32c69994b425829dc2800000000,0x2656d7a3d7827395987e3f6ec8f6a8a2e75ad977249eff5ce14000,-0x1ab2d8d64917c76761aec9443c07e1a82d8171ad909ac678d7f7000,0xbe4d43f22ce48a88958c3901d1dda413b1bad96974840bfa90d5c00,-0x3ceb007d4e5486858596d4b8f786e756c6e61c65c03aeca12dd18d00,0xeec010b032ec26529961f967d1c31b3aa140e1447b703abf79cd7b00,-0x2e8832b82a986711ccf9afecbb0be0ab166a1d6b690f75e526f98ae40,0x7686620ede7292e28edd4cfb2cefaeb4789ed83b7527fe8b55bfc36c0,-0xfb37e379e1f1c7edb234a3aad0a3d8f1e4b29e8aeda92442a535067c0,0x1c11924d838d0cbadb88036fca5fc38275ebe3c144700e8733ba8b5140,-0x2abf04889d5ebc83d3ac11760f7e33c2ca529489ac90a992d9983a07d0,0x37de83619b3ab67e5f75114991457807a778525084bee2e643af403470,-0x3f0202c72b51132bb1af301682402cac376902858b88ecf67e156ab4f0,0x3d8c4d28bdc888d899545ecba17c7a9a7f9de3715105f572371c12d950,-0x3433fd399b60fcb1f7cc0cd1056bb97e3381a9244ed3c455749a8c9080,0x267e7681732d5fcb02524c6c4b8aa17cd42e80edd26b0cc0aa1a17bd80,-0x18aebf086f83a0ffa11663e458c6044abc8afd1b84a7c2e43d74508140,0xdc03f97ce7cecbecd0d9c16dcb95d429c2e4f29d551fd2c567b1447c0,-0x6a4da623b7801657f0e23b60e6cafab720f1a58825c56a71e9a83a4b4,0x2c6ace2696085cd3bc31ae9a00e7654ae8f35c33122c4b4b239754f5c,-0xffc8c1c03e18099026bf9d14f80c7388832fec73fc5328c7e0ffa57c,0x4ee4ef4cb4f495df5af5bcc4567f47524900f28dac93c90a54062314,-0x14b8319cb8547fc92ca1fd5c34e849a3f61f1f1f2a118779f2b638d0,0x498a3fe6380edd387e9deece9e2cd6c428cefe7d1de50767a98ce70,-0xda53a5035d7439e202f6d817a8320a4a3c3d3ef0cc0b6df639a130,0x217b9ab218c06d89dbccdf929061c374cdda080b0070d33dad3910,-0x42ec8ff97e0241111a2375a4f2f7b6cac00a61bca7a200bac44a8,0x6b08cccbc91dc36b7a93718d0641640b930c49a651221cd3e178,-0x860043cc7010190bf5cccb6cade862781de4fd5523d5130c378,0x7fc9cb45ec9e06f2e725737b1bf575e878cb4456605b7cc2a8,-0x59b322ae0c6e5546d4f6f19fd97e69260a76dba5c07cc4f50,0x2c5dbc908c91ace8cbe3b10ba81c7f1221ce7d27d4859ff0,-0xe9c86a00e3dd0ed07bc009525e36fbfb64f9f6dbfab470,0x2f8f3276fbc7d9adea8342d2071287bcd2fc61e2108d0,-0x564c8925764ecc42d752160f0260cfcb083ee6cb3f4,0x4b682c4c050e2516debba7ef9992f276376c9001c,-0x195fb95ed0572b3f0a73dc59163e704c6503a7c,0x23da8b2e388ec9573c669ba537a7584b8714,-0x5bbf01b1ec5606a74f6f6ca5e2000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 21 78 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 78 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 46 indices rho q25 m25 25 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 46 indices rho q25 m25 25 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x3951727f1563e5884ce566ceda,0x18a4e759cd408af8380d11dc1,-0xa515e25a4cf1591a1278d28,0x431c012d36ee6287bed3d0,-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r26 : List ℤ := raw_ints% [0x9f578e9981ebaf27d3956b2d5e21807e1f258235200000,0xf60ee793a4c438417746fa7b598553de5714279d720000,0xb2990520ecf5623f76cffd4592cd85bfe98a3ab9f18000,0x510ac0f1e6db5efec2a10fed743364c13da931505c3800,0x19cab0b84b8f1ca9eb4907042bd9045e56ca9986a8bc00,0x61f0acfa0744cd29b40f60f6b463ec1a1016346a9e080,0x11fdd06fb750efd522fca1140acac34acc34f18092ac0,0x29ec9a9c7049fe3d9bc0fee3025355ea411569c54220,0x4eaf92f377ef827053050e54fc74db736e365e871b0,0x78282ae3c05bd05104c672c750b97048035e9d53f8,0x962597ab810999f23b5740a5f686ee300306219d4,0x99d8912506d5ec4450c4b46743981a84a95f16fe,0x8111e789117b720778fdec5563dd907aca2d05d,0x58347f5b574a492608f4a0d33b48435377db8a,0x30a2e51e68b90aba565344626c660ccdb8ba7,0x154fe8fb65bcccc1f11d97ea3dab96898270,0x73ff9634eeb4deeb13a3cd8ff6be834467,0x1d887bee844ee7043f4f43f403451f012,0x54bc66b49f424582bc46c8d104d8e25,0x98bdae3243e08207381b770aee0de,0x8223bc20599fb34ea81a076d3ac]
def m26 : List ℤ := raw_ints% [0x0,0x2afc7d8797e90063f0f493d53c9282b991a4bcf4405c1000000000,-0x3dd7afd37fbc064f7a83fa6467a89f8a492225897a466de11ff4000,0x2abbfb68b0d227d2798d8ef6bf0139fde614db98c40943fed171f000,-0x12e258c769eccec6d2cc2385a87cef027a4f1f13f5d40751092116400,0x5fe79092cd1e57e2096fd3bfdbac6e3e7014a16a2b5f38db54106a300,-0x1748adfa2b829e91f5e280a19feb01b2bd78b96c42d9c37101a2197500,0x47eed4682ee5405431102d88ab8ae98693528a2bdd319b1630bc6ccfc0,-0xb56f3b8c4864761f82432f55e4f621f33b4757c16fcf2ae7c5ed912340,0x17c99c770aa3ad8530cc31a9cbd8b631f9f6cece0698e66403d974cc840,-0x2a1032047a0faec60b1697a18914c08c24ba9323bfc905ed5f6eb100ec0,0x3f5340cf3ee219dd6c3ea537558225caa1b9e138bd8c56a1e26b7b905b0,-0x51c38acaee5da070199b195398fedc3e63c6a91eb01e6da697954a89c10,0x5b075da63065069e89485e7eb0ad53dcb46d87e114b659f6a3bb9a35190,-0x57b5d1c508302be5058b89cd7befd396378251e956eac30b3419f9d7630,0x49514f443e8274a9a4bf94b17c1c158d35c76bd5bef757c6bd6733a8f80,-0x353b4597581e5c363f48d9353b6fd2e369c4880c9c33176a1638f630280,0x21926b5fcbdd1dac84569d793ccac21845e871a9df33432dc316c367a40,-0x125fff8f0475a94fabe7ffb2fa694afcb1fba1b06d4927c35c63e20c2c0,0x8b60b24c4bb951897e7f73aa93a4d69d0de8fbc7b0f30b2139a83e51ac,-0x390f67577fe8d8e4d8b9d09bccdec8d0651771281d5f80ef06aa516dc4,0x141710f5096b602f92fec75305d62aa73689a6e1bf27ee4d4720c32b24,-0x60d10963469d73ed404812ea7fb3f554d25054251ae6848234a7335cc,0x18c78ee923b867c33bcbe72de0fab4b938c5dd8420e5ac3750f1090b0,-0x558537f4ee53c842e797a0a8c8fdf275724e5cc04063e80551bdbe10,0xf6404909a5f7644bc62a85a963994d4e3f89ffe0664877de4b9da50,-0x2485c16ea82e7fd5f6d41de33be370411498d4ed8dfd0e93e436d70,0x465d2ce5799c99827e8cfd46f9ba766556075cdb28e950841e5218,-0x6c0fed76dc57d57cbc735bd72e23a7d81230eb396e0c18cf60ec8,0x8158160f317a72014752da4e0c90de7885b889eddc89720997c8,-0x7555f93da6b27c10436babf0aed15908fe7752b9b012dfc0518,0x4de4cee5146d1320ca4a4127518d2c4e3f8265cb05b0955230,-0x2430fa13002d50ab4dabf4bf9a07753f35cbad487dc2bc490,0xb1bfcbda0899da5afc4f47747dc0b2d2b516db91c500790,-0x21661c6b130a7dea1c8bf9c41b8f26368c7338d558f730,0x3763ae20e7e0774f893242b7bfa8c5eed035bf84686c,-0x2bb1aef062deeeabae7a047025808cec1844b79704,0xd1518f959c640c4032e89b18e3e02793692e024,-0x1028fa1c5f6f5f9a54d171622e9030266a7cc,0x23527ef9559e8ea47656ba7f0ec000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 21 80 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 80 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 46 indices rho q26 m26 26 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 46 indices rho q26 m26 26 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0x8223bc20599fb34ea81a076d3ac,-0x3951727f1563e5884ce566ceda,0x18a4e759cd408af8380d11dc1,-0xa515e25a4cf1591a1278d28,0x431c012d36ee6287bed3d0,-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r27 : List ℤ := raw_ints% [-0x169c852245899e795788e7ac3005b189d8dc549b73c00000,-0x22e6ec4aae32e96b55760fbfc7b2f5f07698f8fa993c0000,-0x195249d34d1f5ec149308b8b7993d2bfcb1e93e9e8790000,-0xb7bfb1bdd5189995b65095240cdf5272ac84decb5121000,-0x3a724b5d4297001df7023d766395ded06fb113d0b3e7800,-0xddcf41124d488093e8e6e7372f2916867c4480e4b5b300,-0x28b846e46a293297cbfc426ce25a362db19bf64ec98380,-0x5ed1eedcff85845790b4812a3d75a1e88229afd595d00,-0xb1d4003dac472f94f56c0248db268f804d523ca266e0,-0x10f5396d05b58fa96243f6d60a506c5cd05611652060,-0x152bd961c4dfba9a78a6f2d3af92e15e9f7d389fac8,-0x15abe82498bb459e772a8e89a9ad42e027d875ac70,-0x122971a2b5589ef939b68b53da7ee91f99437f5c2,-0xc65a5e5fa885010e1802d49e64a27eb9a10949f,-0x6d3b2e4e3bd656251c0f037b7253c30d66cdf6,-0x2fcc00f152a9ba9273aa9963e522b97994841,-0x103bf154ed747858c4b5637837bda28f2610,-0x4204a56918555174d70c4c124e9da90da1,-0xbd0f455f3c5052fa1fd59b9310c1d3ae,-0x154131dffd9bf2672053c2216a1342f,-0x121138b831c119500486b2b46f0e2]
def m27 : List ℤ := raw_ints% [0x0,-0x45da4bfc56daa0a2678d703a826e146d8cabb30ce8959a000000000,0x63c700ec25f61aa381542110c027345b29b02b7db2c4c9dbc1ed4000,-0x446ee7434bf37d2a59fb3826e5ad1d7cbd77d1543fb48ccd674207000,0x1e00fdc99b6c34049afc36f16d5b7d8616417370e33c56e22d2e411c00,-0x97205389ceafadec8dea0b398edf1d9a6b46ce086e5eedd023c792dd00,0x245fe0de01ed2cc0bca8f63645094d7f179d468e13c21aa57e3cbdeab00,-0x6f5b428e239441311bbdb5d7a4ca0c4e52d8d9ac55738afecf71a6f9240,0x116310b1e0fbbbdb9a3acd82c66972281a4c78fe8cc849e3eb741a27a2c0,-0x241b36a1f6bd4972c77febaafd62bc32ee386bcd1f2880723959bbc883c0,0x3f2b1abbfc861b1d9b52c9cd7686151326b4946e8ea6a23c3b99b1e34540,-0x5e07db3a3f73562c4329e436517717805169bfa0108aaed5d6b597ab04d0,0x77f769859b90494125801371cdb423b918d6d4331f78800d9a8177f87b70,-0x83e04118ab482ce3f08a18007f613e1b8583bba4a782b35e84278e2943f0,0x7d5da5afaa384663c9690bb2aaae83aa4292973e8336e7ad4630afdeae50,-0x674cb69401ebc23d442bfd838f8cb8a39c20dcd8835da0628d1a4e4d9080,0x49dbe7a323fad004aa87688f49cd17cf0e3b243e27f6bdcea11a980bfd80,-0x2dd2fbcc062c373d90d8297af5ce36b258248a108838aa6a7396af4b8540,0x18a4fb5dd04f0868b2ca4f952893cdb5b149ad96d896b0b0b9cdf70cd3c0,-0xb770c0eb4d1a185afa23c91b379928dd2993af29895d4d11b7eb6816df4,0x4996ed737ab953a7eb61378a353e9570093309478d9664395c74c2edf1c,-0x19591d37ed3c8845266115f01a0d30d90e43ffe685c5e74ccd719df9f3c,0x774a7bb1510f49cf9d1dfd7cdd26b7b536fbaed5756ba1ed7303796a54,-0x1dc15257ab242898304f1b3db963593261fa71cfa120e35adc3cb78dd0,0x63d9f2b1bd78c150bf9781e695693dd3a6015913f4fd454a7709b0d70,-0x116d607559f24c977e0a88751c9bdeef1241c0dcd53ebe9855982dc30,0x27fd0a643ee076f61949b34efa87e2c11aad70176941db5507430210,-0x4a3e979122b3b733d2227cadb405a512c7fedc160cc53d4763a3328,0x6d758c9ad3089f080b3c1ccc9ec8bf5f06d7ff0908695ab4e9a4f8,-0x7d37b4b0236450e20f9a8afbd00bea7a5ea69d8912aab1c6356f8,0x6c0349810c50b42711685e79795bc5eecb9ed76cf031be26a128,-0x43c865654d2ac5f4a8aeb9cebe9815d8f6fdd793d5c201c5450,0x1d91cde8f9892229308a093e7ac7348cf968a2ec7921c74ef0,-0x874a559da873bf884fcf5997e0e4765831133b9a8d1a3370,0x1777d4b0cd91e80c975d529e5a424d417d5234e85b4bdd0,-0x238e4f36a8ede02608950699fb77aad15d744c08d8134,0x195059816215b0ed27f5cd9011d4164c1210a024bdc,-0x6be1ee23c09a46a4ce39fa5bedd68e2b133a343c,0x747dc38d1fa26ba38d1f627ab5992cc731e54,-0xd982bb8983fbac53c0e4a9bbd48000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 21 82 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 82 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 46 indices rho q27 m27 27 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 46 indices rho q27 m27 27 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x121138b831c119500486b2b46f0e2,0x8223bc20599fb34ea81a076d3ac,-0x3951727f1563e5884ce566ceda,0x18a4e759cd408af8380d11dc1,-0xa515e25a4cf1591a1278d28,0x431c012d36ee6287bed3d0,-0x1a664e0fa3af1e0cb222c,0xa0295d81f896d6727f9,-0x3a4342723c6ceed746,0x143836d1a11bb155c,-0x6a607608c09d0d6,0x20dc94d7e22819,-0x96f77ca2463c,0x27bb872f550,-0x9689dedd8,0x1f408221,-0x57950a,0xc2ac,-0x132,0x1]
def r28 : List ℤ := raw_ints% [0x3239eb23a86c05592cb14202581744cbc4d608e72aba00000,0x4d7f1e41545795255fd09058f7c2e9fee127238f2a2aa0000,0x38331a5601ddd6e88e56d391ac5d798a79528657be47c8000,0x197a1727b34db4d0c96575b7518470fe7c6d84e0092f0d800,0x8197b8a610021a4ba4d87467ceb74bcbc8216df98f837800,0x1eb8b940654ba2aa8267c2df69439ec9c663753111ca2680,0x5a2f1cee9f62af2706ad21ce5e3892c906ca09cef848300,0xd1ddb39a40f54e806ecd272a3c0b109c2bdb9b1a566620,0x1894fafc604fd657c7b1ee64470466d921ce385e03e880,0x257a5a18c14947936b456707c4665bada62dca21a8cb8,0x2ec0349cae597a3db5dbb2a47e538b05c08175bbabc0,0x2fcfe3925007f2627532d84b6625ed5dddeb293c2be,0x28079014e6cbdbb19caac6bc5eba48006560cfacb0,0x1b4b51df5d30d03cbc87eb3cc64af3ac88cc60798,0xf0353f315ed708b81e25116bba1e55381cf75a1,0x68f94f8d8ed467d466f490156bdc16ad4c8326,0x239a9a96574c6981bf6e76fc1f2c4f43d387f,0x909027778f0bab951b1b02c4660b938693c,0x19d4912c22f2336697062b76c0986895ff,0x2e6004ad8088e2cf062564c10b274c70,0x2756891c3b17ed1e59d086b67af471]
def m28 : List ℤ := raw_ints% [0x0,0x7182bb7a0d234507e845d65f13f2e132049702f4f9f31a4000000000,-0xa104ae81b6ad0ce35f290fa2754ad1cd7730d751995c706edf02b4000,0x6da2ed7f360483a685040736f30684239f2cf5aaa94ffa29b9572af000,-0x2fb435c2f2adcf720f298a983d9621d7c28a654f7bd0890f8b99725a400,0xee5ce3e523505c60c98ffad4fdd9582c95b9acbb3673b0fc10f5da15300,-0x38e3e240597b894b3499eaecfdf8fe60870bc62cf666d6752a03c6b24500,0xac9fd9c6b7413796347afd5ddf00725f5375e94e09bc424a729fc1dccbc0,-0x1ab3c4519e8a2c58ae26c697799fa76d4d1a9b51232c41f82f5bf53505740,0x36e7c98806b4b582f8140eb144d56064d22137a090b9efd9c8d2d0072ec40,-0x5f0f225176049d0a1fcbdfeb8b052c536563f4ae2d9bd4f5fc9711d83dac0,0x8bf1e174a8af702eaada964a583ffdc3c3f5c6f08a5140ac6a75d01cda0b0,-0xb075e54795930c638c3620596eb2845949505032562d40b0303196d7d9d10,0xbf92ac333eb498ffe373d8010904de8a8774f5dd96c68e3c78ad939972a90,-0xb3b65efc3bd77b2155c2c4e1368d045b40ece2967ef7aee6d177057dc9930,0x91ff39e7272388b295efc32417a65dadcd84af7cfdd94c90f9cb18ceb8f80,-0x66d18aa6464cf5d76da7749617564a0d6dd158b48bf2259c8a2fb77eac280,0x3ec3de71d125de5b96f0325f76169bf479487e636eac63240e39be1d07e40,-0x212c3cdce25678b1cc7c967735a08c899ae8631713e880167d955ca1dcec0,0xf256bf525ab1111c7dd385bbd29a3440cb81840a0d01998fc1cfce3e7e6c,-0x5f45e75a6c765854bcc2c71b1c662d62051081c531a22a7a6a208b1be004,0x201b9beff1a4538098f1fee05d62e2874b6bfc361fc145b60aa4a03bdb64,-0x9390bf8562167fa9c78adaf817e3a0d6fc1e54c3573ff5b86240b7d5c8c,0x23df1f8477c151bca8c0529a82909591e5363bf22c7f1049156610d13b0,-0x750a6c47cebe1ed2f3f6f23beba1526620e7135c7387d393fccbce0710,0x13cf074ab948dc1d72169f5e5543a1589db530f0778021d29411b57750,-0x2bf1a1a3161dca2e7115545675cd1bc2f1213e642341fd5ae99796c70,0x4e9c039e42de1a6e1b84c7f785b36eeceaf497f90ddcab2fb4af6f98,-0x6f39ce4e1a6e80ac92128bacbcd2cebecbd6cdf14a49460831d2f48,0x7990b90719b9a2df98681f358a667826df947a079f51feeb753848,-0x63abd0526e35fd12e7be27537db9e163a3dd556be94574d6e2298,0x3b1994ec92012cf2a2febeedf7e606848026212ba424acb4a530,-0x1831e01f10edb26e070464f3040febbee2e006f69044f1e1d90,0x6712d5b0d27524b9d0318bbccba022dcbb81a94f7560c1890,-0x107f95520b910bba46e06ce5081a2556d762716c30a1b230,0x16d3990a09b30e20995879ef8dc8e18a026b325da2f12c,-0xea99dedc100bc52fb0d416cc6321d2fafb1b1d8ed44,0x379519dda0b6132f312724a26c7a4a0ce1cedf064,-0x347663741c9f325d441b16330778f08bb11e8c,0x53af6355d1f574a5453dd7c5a230000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 21 84 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 84 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 46 indices rho q28 m28 28 254330131900516406969794560000 26=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 46 indices rho q28 m28 28 254330131900516406969794560000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_28
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<29) : intPolyRF (mz e)=rfPoly (C (254330131900516406969794560000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^e) := by
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
  · exact moment_source_27 size
  · exact moment_source_28 size
#print axioms moment_source_28
end
end CatalanCore.Li2.NVMod.FamilySource.V6C27
