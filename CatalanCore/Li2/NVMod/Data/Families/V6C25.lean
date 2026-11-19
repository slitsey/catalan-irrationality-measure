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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C25
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,25,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x11849c2b2d50a480000,0x1a25d721710fc248000,0x12489ff23f163d9e000,0x7f68bfd8ab6f110e00,0x26c22134df58404900,0x8c08cb987f7be12a0,0x185930d88e81086d0,0x3562df1f9428d460,0x5da4429e0eb9d48,0x849649fb43f962,0x9832f2e79eead,0x8dacd7c4f269,0x6a860b073cc,0x40245afd98,0x1e7c4044e,0xb2d8c6e,0x30cb04,0x952e,0x11d,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0x19,-0x4d,0x4d,-0x743,0x4fe1,-0x7ccf9,0x4fe1,-0x2fb24,0x5377f,-0xb24bf,0x27cc61,-0x65e24,0x1182e3,-0x200db3,0x200db3]
def rhoDenominators : List ℤ := raw_ints% [0x2e021fb00,0xd5a980,0x19230,0x861,0x8f0,0x208,0x3c,0xf5,0x280,0x1440,0x5a,0x1ef,0x294,0x596,0x1b5f,0x861,0x4100,0x22880,0x15da10]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 25
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤24))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤24 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 25 omega6=padCoefficients 25 (omegaCoefficients 24 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 24 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 25 omega7=padCoefficients 25 (omegaCoefficients 24 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 24 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 25 omega8=padCoefficients 25 (omegaCoefficients 24 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 24 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 25 omega9=padCoefficients 25 (omegaCoefficients 24 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 24 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 25 omega10=padCoefficients 25 (omegaCoefficients 24 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 24 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 25 omega11=padCoefficients 25 (omegaCoefficients 24 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 24 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 25 omega12=padCoefficients 25 (omegaCoefficients 24 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 24 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 25 omega13=padCoefficients 25 (omegaCoefficients 24 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 24 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 25 omega14=padCoefficients 25 (omegaCoefficients 24 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 24 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 25 omega15=padCoefficients 25 (omegaCoefficients 24 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 24 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 25 omega16=padCoefficients 25 (omegaCoefficients 24 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 24 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 25 omega17=padCoefficients 25 (omegaCoefficients 24 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 24 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 25 omega18=padCoefficients 25 (omegaCoefficients 24 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 24 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 25 omega19=padCoefficients 25 (omegaCoefficients 24 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 24 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 25 omega20=padCoefficients 25 (omegaCoefficients 24 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 24 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 25 omega21=padCoefficients 25 (omegaCoefficients 24 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 24 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 25 omega22=padCoefficients 25 (omegaCoefficients 24 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 24 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 25 omega23=padCoefficients 25 (omegaCoefficients 24 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 24 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 25 omega24=padCoefficients 25 (omegaCoefficients 24 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 24 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
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
  | 23=>omega23
  | 24=>omega24
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 24 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 25 at hb
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
def m0 : List ℤ := raw_ints% [0x0,0x23fe281b868f9d6d79000,-0x3c74e75e3c053a6de13e00,0x30fe7b88af256d470d0e280,-0x1982a50e8d571ab903793b40,0x9969938319e94ccdb14cf6a0,-0x2c55db9d06e0e2ae7e8dbdf50,0xa3f184a1637fac2c0b89ed9f0,-0x1f1d8469f69a9b4eb93ae59980,0x4f12270c1105f995a21b4d0b38,-0xaa7e7963e41d1d2fc26a91dc54,0x13b2b0185676ac225f86494529c,-0x1f760cf2c812618f3aa0d859d60,0x2bab37fdb66583ab332b2ce22a0,-0x34e66155a3d23b821f52ee77000,0x38175e1de587a48134af8d0e440,-0x3426baff5539c35b069a6431b10,0x2a8c6b9d494a77dec8119c9645e,-0x1e743956ab191c0e7f7f2a70eb5,0x131956f590c2a965847f4fd7de7,-0xa78b2893d2ac19636fce71ba88,0x500a5ad71662f4e0d5a68e1c20,-0x212a9b2df45a654f046169ed3c,0xbd9839057498c63f84b2e3b84,-0x39f5bddf54868167bcf50ca78,0xf038c7dd55205b7ac0dd1554,-0x3413c354d0f4effde55a4b72,0x94c80432461e77efb020f76,-0x156e6df7c9c16af025fa6d8,0x26c237211dce69f6665770,-0x34f31f44abdd92b991f6c,0x33bdad2da9c45771f6f4,-0x2147204b9471ad08678,0xc4360bb83fd5b13c6,-0x1fbaffd2868bf00d,0x126c2fa436975f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 19 34 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 34 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 42 indices rho q0 m0 0 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 42 indices rho q0 m0 0 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x35fd3c2949d76c24358000,0x5942edb74355698add73e00,-0x472cadf0080f498fb0705c80,0x2472dd136f9627e36d1732b00,-0xd77d123b22b065517e1c224a0,0x3d31dbf1bae5fecc7b180333c0,-0xde40c9fc35e9f312a7b2dc9d20,0x2968b1778216ffca36a17bddb00,-0x673e7e2cdd57e2694377f7fec88,0xda49f0bbc5a70c6b2f9caeffcf0,-0x18b6d1f5c116be11185647b4e1a8,0x26a7b0440f89837617996a19f580,-0x348122cdf6d760b3b3414b1066c0,0x3e310bba1b9a23e5fb4971928f00,-0x406ccdf2093825fab2140faa3d40,0x3a7758923c2071984389ad6d1500,-0x2e831605b7a893494618bee73a02,0x206ce3fb17ad0cd5fc0108330e3c,-0x13c8494f312a8de63f5ec2f41c4a,0xa89742ad55296bd5bcf4c6b9aa0,-0x4e20495bd7a7c3860be4f59aee8,0x1f596901ea7e9408c68878ada10,-0xad3473b3cca83364c367a134e8,0x331051a3610acf242816d02c60,-0xcb95d58cb1fc3a353b65d2044,0x2a5466a5d0597c5145a319618,-0x7394d9129d9eaa8c2f1e1734,0xfd8695fec02b607de13cfe0,-0x1b21e89aec8038c824685e8,0x22de5161759ca9bf062dd0,-0x1fc893f7a946e8dc3db28,0x12dac6d86faecac722a0,-0x64eb7498f5ef5d5d02,0xe78689c6ff4a8c1c,-0x73034f0e7ebfea]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 19 35 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 35 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 42 indices rho q1 m1 1 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 42 indices rho q1 m1 1 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x50fbda3deec322365040000,-0x83d88767245fa00afcd6b200,0x677bbd20cbf295665d97f6980,-0x34248ae489139ca52928276080,0x12f30985ade46281660e8a645e0,-0x54a4411ec971a23ce49a7dc5ca0,0x12e0df0f694a4d6063231023c240,-0x37449fdbe8f5f76c209dfb880380,0x8740ce2bf4bcb06bff377e17eab8,-0x118844250e3318d986e0209305c28,0x1f226f0e797cc927e3a4e849bbe30,-0x2fb4ce4c1e76a280687514daff7c0,0x3f6efb23a2cb6829d46bd9239d580,-0x497ee7d9af7a5678146b6c2dc3a00,0x4a6859ca822e3ceb1712f79975ec0,-0x41ee666897de1a0b1e430f07d9140,0x3328e560c39dc4907acc2230bf5ee,-0x22bf8bae2ee39935bb9f6b401bb8a,0x14a0e84538ac710b442f8ae63bdac,-0xaad47c6df84c0b255ef5aee699d0,0x4cce3fc6a5bd140f25f0957a2a08,-0x1dd96ae4b5fbc253ca3cb0ad5438,0x9f693950e122a5c819ec31853e0,-0x2d534942c693c9fd7c564730870,0xadd31ac555a4d2af98379cd5ac,-0x22a8d239bdb540aac7e56a4e64,0x5a6dc9f9d75b1e7bf308b4768,-0xbcb5a6e987e1abdd16dd25f0,0x131c8c7e3caa5dd18db880e8,-0x17162b7764e044d1f909518,0x139c42eb1e933c8e7a6ac0,-0xab736d2c2dbe0b6619d0,0x33fbb667e41ce86285e,-0x699107305d47e98fa,0x2cd798983ac4e9c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 19 36 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 36 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 42 indices rho q2 m2 2 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 42 indices rho q2 m2 2 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x7979c75ce624b35178600000,0xc2d3bd2bd1a8ba8cd934cfe00,-0x969552469cdf658ae83c32f680,0x4aafe0d26f7203ea1d40a7f4880,-0x1ab4a1011cdca831070a6a1f3420,0x75503043d00ec6fcbdebf6bdbea0,-0x19b8511f8ebf2bd68e6deb7635400,0x49fa08f0399ac8da2b4e03b27d380,-0xb1c33e6597597ee303deaefcd3188,0x169cbed77d9037e608379c36cf00a8,-0x27616ab7d53c0889ac5910b9ea3060,0x3b22b406a3737dcd6253bba249cdc0,-0x4d007ee9e28bbff2519cc6962d4a00,0x574c41e7ae63d1b80d54f5e36d5400,-0x5667906fc70d8cc06882922059b540,0x4ac71953abf89e3e6525f2d8d59340,-0x389cea724a20ebf41823e1a8f4ce62,0x25793e3d8fa53e0d08fae4bf71ceaa,-0x15a71a95b170af5ac32bbcef3f1478,0xae475f1d71212a7fca12334e6a550,-0x4c094812350058cc950aa1129aed8,0x1c9fc9af775dbf2a8cf0cb2d0ba38,-0x93c70ba1ed7f0006db9c9330ddd0,0x28862f609df20ec6628b1d32c7f0,-0x957c7dfdadfb6f527d8968935d4,0x1c94861ff897e01d4d4e4729024,-0x473bd3985da9c674ef0efb2180,0x8d5ed9b2280ed875c39773670,-0xd8a85cae07a6f744e4d46438,0xf5d3a04676639bee1a82018,-0xc2636e03f1fd3601431ab0,0x61b6a6efeca28b5c27e50,-0x1acf351226a39d8f9212,0x301f35935f7004169a,-0x11786e83b2b44868]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 19 37 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 37 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 42 indices rho q3 m3 3 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 42 indices rho q3 m3 3 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,0xb636ab0b59370cfa349000000,-0x1200317ba517172e60cdc32d200,0xdb4cd0cdfce3d76bddc9484cd80,-0x6b1c0faa8733f7f9f1c5dd7a8180,0x25b2a5c60e97182e6a8e84d778ce0,-0xa2ed1311132f17e5b1b2e77d96de0,0x232040089635050dcdd77ea217d180,-0x634c19f4546a08e01ea3a21f0e2280,0xea618a7fb34cabd40833d188890538,-0x1d44c81e4260ff3f8f3ddfbf4fcb678,0x3201e83c0ac0d391f12f9a78eea6e00,-0x499e901dbf16070cb21f3fe04aca140,0x5de8b08878bc4e9db183397745bd100,-0x683615dc6508493f8e62145d2efb200,0x64def35fb8c3b42153b7341e27530c0,-0x554a2e2b6f3c789df4a1f1d9a89d9c0,0x3f04e2af2e77d31d36c62482edba84e,-0x28a9ce65a91b5f2cfc0be5a3b07df9e,0x16dfcb5c721041e10479013dfd80020,-0xb2facd6ae345d1b95c5354e60fadf0,0x4bc9c92277309541992902d5345628,-0x1ba3e42f04eac37090f9d347237f28,0x89f4c5360226c695400c4922e1cd0,-0x247ca02de61a6fa0e267a247db3d0,0x81742216585ed46cba5fc747314c,-0x17ba6c340cc6a1a2730f4e0c53ac,0x387b4b00ced41aecfacfcad41f0,-0x6a8f5310445bc9948008758950,0x9a5e27c3a12e0ed62f0a5fb48,-0xa462f9fca4ca047d5dc822c8,0x78e337f7c16f37061c2c570,-0x37d43e87bb3bcbf2d182f0,0xdd7379af1e1cd82c34de,-0x15edd67ae76f359f56e,0x6cd349f33eeddaf0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 19 38 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 38 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 42 indices rho q4 m4 4 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 42 indices rho q4 m4 4 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x11152009105d293774ed8000000,0x1a9f085ccd3296f44116cf50de00,-0x13fa20a7b1762c6dd192ca02ce680,0x99cafbc57705bd273fe7ef01f7680,-0x354cd143149c1aad44c6a41384bc20,0xe2b9e45834eeec8e869f5a8c058820,-0x30161d91c6cb5c57bd99e2e103ecb80,0x85a77094a5f8a4487bc03fab22a0580,-0x136019e2e5ea54f165631f3990682408,0x260498479620670237bbafdafe89c708,-0x3fbfb06edf39e2d9323592e3f28da040,0x5c0a09927d5c6d67d4dfb43b1a5d72c0,-0x730d8f48370f061a7852745fc83e9b00,0x7d03407d94b12d08569f4b88f695bc00,-0x7660041ab307b9d0be3990cd0931c140,0x61d13c9fc22d4f5608c11eb09936b240,-0x468eb91e56cc20c78f078ca930c72e82,0x2c645f14fcb1fb2ec6c107078ba96f42,-0x18510e2edbe58715a1ba77da004a9270,0xb9002103742eef1062d3370e1748710,-0x4c0b1ffe737e5a9822c17340c117818,0x1adee4b545c95850b65319a4c80e958,-0x81aaccf5c8e2092e13941eb36cd770,0x21137c25b51909a3e15e7c0b22c730,-0x70dce1e3d1066aed29a689e313c54,0x13d4683f38238da25b119a77fa914,-0x2d1129f2bf955ed7c4dd99159830,0x50cb422652c0023e46bcf058db0,-0x6e91f6cb2304b1e7d807d864f8,0x6e6c9388a42779149d35b3db8,-0x4b712c1bfacb926301e620d0,0x1ff856f45a686886acdc610,-0x726c5e6c050626580d9f2,0x9fd40c57cc289b69472,-0x2a56b1f92220d2ca0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 19 39 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 39 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 42 indices rho q5 m5 5 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 42 indices rho q5 m5 5 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x199fb00d988bbdd32f6440000000,-0x2762bdddfecad1717e7754243f200,0x1d23d9e860738c30e0f11ebee65580,-0xdd15fb4be44facac45e3769e9bdd80,0x4b7a976b48e1685c3297e97e4aa9ee0,-0x13c2178b0bac465efb94bbfcfe41c0e0,0x41fbcacceb93ad1df386f1015ce7ae80,-0xb46399b6c88455d40d0076284ce0c680,0x19b4db538addfb0223a44d196725164b8,-0x318dbab986a19b4ac5511d05d99bf5338,0x51938a2a900d78e1d412c69f51f961740,-0x738bff0bc4c0b9df05bc4377f2d9d8b40,0x8d977e04a675fd0131bdae48a4e39e300,-0x96b06c92c590f11ec2a1df1d5baf86600,0x8ba104a035043f90c2e23158dc9ff94c0,-0x70caeae310e5f0659322dca332b3117c0,0x4f72670865d975dc6d63482c33e28242e,-0x30c0104628a90dfd09cf0841e81ed6dce,0x1a024d5f8e442151e8b6eace4c481ce70,-0xc06f7f28712ead6301de70533ace8d70,0x4ccb58930aac1e20bc89acb7d7c49728,-0x1a4b6f4e6f9287090bb21698c37c3568,0x7aaf6ac2e4d5bceae5e8819291d7f90,-0x1e2ecd92145a4e77e2cec5bf778ae50,0x630a8239b52db7ae12a9df934b538c,-0x10ad4c2a15ddb0cad5de55bab4578c,0x242d4d06ba03130803dc543716010,-0x3d9a431faccc6d1b886d9d144bd0,0x4f98d44908704cf94023041f348,-0x4a7d6aa1f93f805f797ee82a08,0x2f3ba3f9633a4b46d5e17d930,-0x125819bef67f1d65636a8670,0x3b29893661e44d9f68023e,-0x48c68b16e76208011a1e,0x10760244c6a0b1ddc0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 19 40 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 40 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 42 indices rho q6 m6 6 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 42 indices rho q6 m6 6 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0x11849c2b2d50a480000,-0x1a25d721710fc248000,-0x12489ff23f163d9e000,-0x7f68bfd8ab6f110e00,-0x26c22134df58404900,-0x8c08cb987f7be12a0,-0x185930d88e81086d0,-0x3562df1f9428d460,-0x5da4429e0eb9d48,-0x849649fb43c122,-0x9832f2e78edcd,-0x8dacd7c2fa35,-0x6a860ae4278,-0x40245973d3,-0x1e7c34dd8,-0xb2d53b3,-0x30bf4c,-0x93a3,-0xff]
def m7 : List ℤ := raw_ints% [0x0,-0x266f881464d19cbcc716600000000,0x3a4b23b401feb1beb72558241abe00,-0x2a8a095c6210a58d7a9969679bd6e80,0x13e3226558f9faca4ef29efce76db680,-0x6b0d8fcbe5946f0c1dbccc2ed18c1620,0x1b9a4e97a07b8ca38a954e95f8b47d820,-0x5ac054d1a78c9889c59d9fdb007067180,0xf41e89549b6308a0698b7feaee69f0580,-0x2235d070d9959ac775947132b968079c88,0x40cf34640c5518f64fb5a6c23ff87cbb08,-0x68c7f0932915f9ede1c9db9a9bf9073fc0,0x91a6dcb3d4eb5d78fdc03988d0f36e92c0,-0xaf058d5cbeb50a347aea88f3bdb329cb00,0xb67f96e267e994aad62a37778371e89800,-0xa586ebe144a506283f8c4944bf3a41e540,0x82c040e4cde5c6a56f7fd627cf887f7240,-0x59f44d6309009967e301175e62da5d05a2,0x35d8d54ecd35a0bf4e7ecc721e5f97bb42,-0x1bfc84310f8412f62c1e951f0c7d784450,0xc9686526ed2e887187fa924495a1b6b10,-0x4e0b00d045575af258730c56c02aeec98,0x19e562f6025eb552d7b3926d2b212b558,-0x74d3f50685060dae5b4154c5522cb4f0,0x1bb8318e5ce45ec0635f66bdcf03bb30,-0x577600d1785adf2c2721a43b45e3894,0xe1c7a7419315880d07f9b451dd6914,-0x1d358df19912e795623883a81307f0,0x2f38bd1cb1c317b818cf291ae59b0,-0x399290697b4fe0bab20eb99c1178,0x3272ca730fafa723b3ab602b5b8,-0x1da8c8f72d49d11bc749433e50,0xa8b5e4c14700b5c0035b0210,-0x1e9b14048ed67337f0a8312,0x211f4fc26ae4bf8044472,-0x66553de98e07a37e80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 19 42 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 42 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 42 indices rho q7 m7 7 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 42 indices rho q7 m7 7 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0xff,0x1]
def r8 : List ℤ := raw_ints% [0x1173178f022353db80000,0x19fa2cae247161e138000,0x121c317b2b66179e1a000,0x7dc4cd19aed23e231200,0x261bf653d1cd78f7a900,0x8910a0b99906e144460,0x17b4cedc1d730b83690,0x33a7e932ebac9b04d0,0x59f0706977688d658,0x7e376f8767c9cb56,0x8f515b55030fd31,0x839bfbbeb488ca,0x6140b78005dff,0x393bd5f457f0,0x1a5b7e6d5df,0x93a9b93ba,0x256ce549,0x63d986,0x8840]
def m8 : List ℤ := raw_ints% [0x0,0x39a74c1e973a6b1b2aa19000000000,-0x564fcf7a1876d683814c657be671200,0x3e25c32df0814d24e779fb0273076d80,-0x1ca7d332221f81a7c16b6034805cd4580,0x981152edd4caef2c43b17eb499593dce0,-0x26a2a8c9f2f776de519380feec8d35c2e0,0x7d19908c682c80338a9b08b6946c2d0a80,-0x14b3c951db119f5239785147b91af6d9e80,0x2da9d35b749963add82704a160b94d7d038,-0x550b9de5e2a5c3f33e7eed7df7862ce63b8,0x871518621d21bb49d31596c1871de489840,-0xb85678c2b9b6b2e0ac006323889d4736740,0xd94848021271842fbcb80ee89d0ea547f00,-0xde0c4ac574e6a31b2dea534634afcc1ba00,0xc53236d45f811402183c904d10b1b71b0c0,-0x985b6c3aed4e75ad704ef9cef05592e8bc0,0x666826cf3d954caecbeae28a4b0b9336c0e,-0x3bd07e9a26f296a99c37a973c6c0b785aee,0x1e4a8747011dc6c9d36dcef831465cf14b0,-0xd412701e041c8779b931f520f8ff73be70,0x4fcd128ddf4b47799adc1d1aa4da1637a8,-0x19a9a99ad4cda7eaa3e818861e0c25c6e8,0x6ff2a22cc32912e3c31086a3f4de86f90,-0x199da269e9c919a01ef9798b242521150,0x4db4deaab54f58233b555cc6e7dff84c,-0xc02b972a3ba3a31031a2082a01f16cc,0x17b6fa4eaaa78e0562af5ee06764190,-0x2461fef08843366129c60d92e316d0,0x29d4496fc89936c9c36ae826335c8,-0x224ae06234314fe39e54c7472d88,0x12acb3a578c8b3ba880ebf87f30,-0x6120d54139728ec0113c74770,0xfd6d53026e9f7caf100fd1e,-0xf11563bee0e140677a23e,0x27bc7c80b7d7992ff00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 19 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 42 indices rho q8 m8 8 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 42 indices rho q8 m8 8 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x8840,-0xff,0x1]
def r9 : List ℤ := raw_ints% [-0x952d41dfade2b8d2000000,-0xdd930a7fd6a7fd2f680000,-0x9a12cf3ffef24e97648000,-0x42adbd035e877b59d1e000,-0x14230d5f4a2fe5f8b72e00,-0x4825eef6acbcd7071ff00,-0xc6c679e883f25dabefa0,-0x1aee9252ccc38a4fe170,-0x2e9c2de1709b9da8d30,-0x40f1f5d96376f19228,-0x491da6cf4fd7dc7ea,-0x4272282141d3650f,-0x307817a2aecca36,-0x1c0f4df577c801,-0xca5e3d562b90,-0x44d4616b5a1,-0x10bd714d46,-0x29f8d637,-0x33d5ba]
def m9 : List ℤ := raw_ints% [0x0,-0x567af22de2d7a0a8bff258000000000,0x7fd86c7a838fe6df10e7e40e1b429e00,-0x5adcf6c7bb990fad8f9e7d9ea97e1d680,0x295632b1b25838195875a6529a2db27e80,-0xd85604c53f3580fb85552bdd23d5341820,0x362dd44c095c7eb2f0f80b09038bc7a1220,-0xacd5b4397ae5cbee38608e0bc7d3f598180,0x1c29bd8d44f9db7be1e604d930fedea6fd80,-0x3d2160559586cd615a658db6eeef53d95508,0x6ff773e0411fa71dd9c42ca66d6fdf0f5988,-0xaec6ef0dc27bff7139dbfed73c85b444a9c0,0xea3818d5fcc208fd8df8be3e01668f6f7ec0,-0x10ee52e650856de731c5fe6d9234f8bb4d700,0x10f66185f641462316e9f36060c9df544a400,-0xec0f739a5e27f8f7dbd9f316c48fa687c940,0xb2705de530b5c81b68c48d6a193054f5d640,-0x7534baeadae834aadfd08a616d061eeee2c2,0x42d0036cd73e924e1045033cd9d03bc8c9e2,-0x20f95e4a06d742a0dd95549362238990b0d0,0xe09e66117f619f77c5c098e4e9417b32010,-0x5216f1ea43688279434e4932f5956f75e18,0x199613d3d98a59f1b65fac9857fe3b3f0d8,-0x6becd6d788f0df44a133f5b90f861b35f0,0x17d08aa380cf87b7c00391883238fa1a30,-0x457297f5eeb7c6b4ccca11f0d09a6f7d4,0xa47e00b95982009276cd7e9c0d431754,-0x135b49d967bfdaeae33f9034ec8239f0,0x1c2b0b6c6a340e3c2d34df98d9990b0,-0x1e850f7a558e6fae0010eee5404cf8,0x1763fff893e6e9bde53375d486338,-0xbc98a4c27f332f7e498a9939d50,0x37fe7d7e338da3ccaea4a19710,-0x8330c97644a0c0aeb0d10332,0x6d9df5968f68d2e1d9ea12,-0xf6ba7dc4e7ee96faa00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 19 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 42 indices rho q9 m9 9 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 42 indices rho q9 m9 9 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x33d5ba,0x8840,-0xff,0x1]
def r10 : List ℤ := raw_ints% [0x38c0b2ce36b23caf60500000,0x5420b8308aca3cae3f050000,0x3a5e2627358831e14444c000,0x19322a22a4d23e0f15a5ac00,0x7965a8f323e4c06cca02a00,0x1b1878c936918e2e2c17a40,0x4a5f2b29f62e0bc72b0420,0xa087e06dd63678fd23e20,0x1146fdd5160be40154ce0,0x17eedf3fb751128d2e04,0x1ac217ffada4db2c88a,0x181ddc4e62f036b560,0x116a809cee05d7929,0x9f549807976ee3a,0x46b3f762123eab,0x17909c183625c,0x593e8131f47,0xd77445c26,0xfbc19db]
def m10 : List ℤ := raw_ints% [0x0,0x81b86b44d44370fd1feb840000000000,-0xbd6fa7489db677a3b2dc7316472fc3200,0x84f236cba3c25e844fc6a0293d56044580,-0x3bb23c40dce97b33efc35428c5abd7cdd80,0x13438c50c633c59aa65a97287c2c4307aae0,-0x4c1db4d05b27d1c39f5c7ff17632c33e00e0,0xef4f1b5e6edd077c5a8513d0d80bc5870280,-0x266901fee9199bed70dfde7f34dad35594680,0x5212b2c3ea83a8a4067a1a29da962c8fbc3b8,-0x93e2c179eb05c3ad97d94c43ec0d2d5f4a338,0xe2f0bf5cdd30b84a27ef0da3e352630594040,-0x12ac0360d21d223e8df4642a9b332e44ef0b40,0x15325d054ce518dbb4f8715d266f21c9ef4300,-0x14d33453fd482181dc4d8b03c264ff58e08e00,0x11becaa124b35d16c4da476f01a866d9182cc0,-0xd207ca8f1da9e4c41312bb848456e9c6ed7c0,0x86d887371c33130436508c0b2fff20b8e49ee,-0x4b091bacbdfec2d780eca1781d439c7a77bce,0x2418b27bfe6b6daf84d3502bb19278228fcb0,-0xef478902463cdaa807f9e2d38a45f3c8b570,0x54f07ee3cb62e1152970de9b72f5ed722e28,-0x19a93df3ce0d9bfdedb90d473a8838122568,0x68a9d39bf08467c6e879bba019f8211fc90,-0x16450e5e34ef9b48146db4adb4430de1650,0x3e6bb5f026e07bf1e04946f15dc2a5d30c,-0x8d91ebceea524391d78db8c604fe3338c,0xfe14e135bd05a378a5fee0f37681f490,-0x15e8bb916866ffe02f0ed976a47e83d0,0x165b615ceb3f3212eeb9b3661267a48,-0x10016ae16d0a5a9429ec7050da8208,0x774eb197bb9e8e76511695cd9630,-0x2051959fb0b5f050785b46afe70,0x43ecb8ae8ddad0086f34633fe,-0x31d0cf820231207560af01e,0x5fb17155bbd391c91c00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 19 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 42 indices rho q10 m10 10 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 42 indices rho q10 m10 10 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r11 : List ℤ := raw_ints% [-0x113a44e270ed138f20d3980000,-0x197e1fdd5acd6775c5e3698000,-0x11a6e81e04f71b2db2f33da000,-0x79a62e2a74c2676f7b1b03a00,-0x248a8427695f0601c4c79c700,-0x82202df27ba0c528c04b64e0,-0x1640559503d93dee714c29b0,-0x2fda5e7de47f9dd8b000a00,-0x520e61ce71fea194f95678,-0x711ca3ad5eb9d38639bf6,-0x7dbe3112641d021ce4fb,-0x709186217eaaf90d849,-0x50a4212d76ffdb4624,-0x2da9a784b3fdd4fdf,-0x140597f6aaec5e80,-0x692dd73363a16f,-0x186b57efdae10,-0x39766c5fd13,-0x40d246ca9]
def m11 : List ℤ := raw_ints% [0x0,-0xc294a0e73e65297bafe14600000000000,0x118cd517d2399b59fe0f38e530654a87e00,-0xc2a99119fe0b5031be8f53a5257ea5e3e80,0x564df35b95fb0b639a7144e4db0ea9dce680,-0x1b7c5fe9c452b150bf25d8d60091e7d2b5a20,0x6b20fa20addcc23b0b2942dbaf8df24065420,-0x14c10c53072ae6cacf0e0d58079c2c251c7980,0x34845462043f46e9bf8e7de715269bc2935580,-0x6e80e935b76727bdecfd5c2759990ba0497588,0xc3f2849d2b602fb657256c1486e0ffe22c3a08,-0x127b38ad626af67b705853fa364273e8140adc0,0x17e82e493e7ba749f009f7fd42c8c2d833cdac0,-0x1aa5679d0a85a1e701b4e9b4538e787dc599300,0x19ade63d0ed88770ba58e8a35d39031483cb000,-0x15715221d2ef4345002a394707d53db551e6d40,0xf86d3f40b4cfc97b19dfc6e0c2c022f44a8a40,-0x9befa0ba1168874f2874e0f60588483e32c1e2,0x54b83df0d09302e581cefb89f72b539f243902,-0x27bb56f36d03ad6c790cc47f93e50b719423d0,0x100553fd27a2dd602ad72ce54b74a70e7b4910,-0x586439d30b52f857b65ff9113378476739b98,0x19e27cc422cca7babb21d64e8f0e44166b258,-0x6615ac7488c6ee4274a4ddbeebcdb92b04f0,0x14f17df8a10bb652353ae608834b2232b530,-0x386a1028dbdae46bf893c2083510b8b0714,0x7a7b9c105b00410b58f876a1c521e91a94,-0xd177ae412358aaa954c8e9987b5781cf0,0x111da286f010155224cd003f0678883b0,-0x107059a10c6a29cb8021be61b8f5fc78,0xafc0d0b248ebfd6efbb4d2a92a8eb8,-0x4ba0c0d3139fb388107b231376250,0x12ac3876857d44a2ea2856a1c010,-0x232bddee0835e09e0656ec5952,0x16a084796d01ca30f8b3cc32,-0x2517fb7dfc934590f6800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 19 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 42 indices rho q11 m11 11 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 42 indices rho q11 m11 11 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r12 : List ℤ := raw_ints% [0x46f8aab05f0f595091a29880000,0x68db5c8fca5f0bc251706808000,0x487ae7e3a75ce9cb5b871eb6000,0x1f28689d1f107f6e27088ec9e00,0x956b8160ad05f87a73f38bf700,0x212c9093e1c2e73f572e5c04a0,0x5a82bedea3774808af0bd5a70,0xc208c4ce3c279a7254c089b0,0x14b855634d8ebdea1d052a88,0x1c7194549b61cf703e3a33a,0x1f77f660b00b1c401ff03f,0x1c03b1d672fa9f0ef6e56,0x13efe9c9b3e93a75a963,0xb33843be43c4924334,0x4dd7ff3be03526f9f,0x1943810942dbbe1e,0x5c7f7943081435,0xd5ab10cc354e,0xeb3ac6fb12]
def m12 : List ℤ := raw_ints% [0x0,0x123def15add97be3987d1e9000000000000,-0x1a0625eab0482138cab2019ebd919b235200,0x11d3bc9f0a83969c2645c72ea1c382e1f9d80,-0x7ce82faa8c094392ca72dd05f5804931eb580,0x2745e54cf436e72cb6635a5c502aabf50918e0,-0x970b9b7f437eeeba73a98605b9fd9f001b0ee0,0x1cdc06bf584b676cb2c42b7fe95758fef906a80,-0x47fb29a5a3f2febc037ee189814612f3672ae80,0x95329eb5ea0060b5c82bb05ae7d863066612f38,-0x1046fe5c55d8f235f43d2c36a8854b20ba5996b8,0x1829e15b4b1dd9fa3286f682772fc27fb581e440,-0x1eb958f92411e0fb0123f6f329fd621d7dda0f40,0x21a19cdd32959fa08aa6de05a042899177e1e700,-0x1fcd2650d34d7332480cf58eee882b29922fa200,0x1a0758376e1c60bab1326964bacbef75cb63e8c0,-0x1274132b812fc73faaa022b5d0dca2b17edb43c0,0xb53b24d1a91eae2ae7b15af44a272a06d1c05ce,-0x60271b95d0e91b4edc960bfc3c30a20ad4cd9ae,0x2bf7f06bccaae1974fb6c57872ff3de6da9e3b0,-0x1141d244066791b436d7bc7ca7dfb8b6bcd3470,0x5c7f7b3e0d5cf6642a1d80f1613c409c1184a8,-0x1a41d0a516b2555c4221fd180ea6d2e42c1fe8,0x6420797b7723eb38e70c301ef28f6ba182d90,-0x13cde7e469d8c1528a8442586fffadccff350,0x3341efcc2e6a28c4ca33f0dfe2d6043b81cc,-0x6a8159b4ad378576ce41d5a91e2d7e4d24c,0xad7ec8db434ef87c567f7fbfc5b42e0d90,-0xd6d4a06a09875477f8e5cf776d3ac48d0,0xc2146cb98be2612fc000e4ac9709aec8,-0x78f3160bb62e4ea3e789d7cddcfe288,0x3007139c55bc1241f523c855a44130,-0xacc432bb75c32206c2a3d85efd70,0x123638d85da3ad97ba8f757f0de,-0xa45a9b0872780eab0dd192fe,0xe5ef4bf732381b874f000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 19 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 42 indices rho q12 m12 12 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 42 indices rho q12 m12 12 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r13 : List ℤ := raw_ints% [-0x1018c104c36b21a39b7bf51100000,-0x17bfc4b6a95279ed3068a5a890000,-0x106402212734a11c5460bdd714000,-0x708aba611b0b08ba3a97ea019c00,-0x21aa940d65ceaef5a60d292b8400,-0x775581a536b369aa71d7bd43840,-0x144cadef7ab5357ec14bbdb6600,-0x2b65d8c97435bbf1c3849bb450,-0x49eabcda2dba8f8fc74b61d60,-0x651c11a162aa06ae4911745c,-0x6f68227db880a1c9980c3f0,-0x62b63af89e6a3b4c9c0e23,-0x45ddcf73d6df3a4c9ba02,-0x27002fd4ba9b1e24334d,-0x10cf8a9be4ab7c28448,-0x567e0f73df7a54a1d,-0x13920f8e84b7742a,-0x2c94011cda8307,-0x30355eb94dbc]
def m13 : List ℤ := raw_ints% [0x0,-0x1b5ce6a084c639d564bbadd8000000000000,0x269a63e60887aa9cc79a12141c814f02c5e00,-0x1a23d7260901ac77c6ac0a036bc41add472680,0xb4f76670e8b471fbe633b60caef9fe5fbe4e80,-0x38319973f318d3d63f4cd936941c45bfbe33c20,0xd5562005f31fb2799937327e3735b5b67075620,-0x2836c2814a895f4838301086b4f2bcc7dec59180,0x62e5bceb712fb42d838479b3e0cf190a90c4ad80,-0xc9fe3949f466bfc31334a57861c16531530a1e08,0x15b35ca32d100ba809b0d75ba68b22b5772a84a88,-0x1fb3052ab40bfd75ecd263f713c612802ab5f99c0,0x27a1334c9f153f89e70f34083ffb48958c896b6c0,-0x2a9d89195ee286faa5ba0e0c15eaa07a603facf00,0x278c9efcddce283e771b1ca604280147135577c00,-0x1fbcaeff6a41f4d1da101dc335a296ebd48b35140,0x16090432d0442133169012226cc39f77b1fc8be40,-0xd3aaa8cab29135fcf9f3c9385ff56c09e811b302,0x6dafbb964a9909c6f28cc8c61f082c5829f78422,-0x30e9c41de518f922f906b8e98d4461efbb2770d0,0x12b05896e86bb4c67ca6d9b7205cad9b3e701210,-0x6152c04499d6e2d55f304bb4980aef3f5f98118,0x1ac7de2c499bba9572e66a91661892fa96283d8,-0x62bdb48232ffb1497ff7217c813d574122fbf0,0x12d3c2600f3b2f0c2acee01ba31588711cb030,-0x2ecfdc565527abe129f2a3abd763418d03a54,0x5d10013a71da8b8b1f72600d64797cf635d4,-0x9057e4391b0bd47b1414fcc2c9ac50953f0,0xa93244bc023017e683246911819daa56b0,-0x8faea36b8cc57de0174603d38ab3693f8,0x5371fc3602efcf27b04fe439b37dca38,-0x1e8cd6d288d215096212e0b85f68f50,0x63fa93fae5a6de355492afb990910,-0x96df5b402e32a884162e10d4172,0x4a92c25df2a6a56fc1025ea52,-0x59090b8406178c6768a000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 19 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 42 indices rho q13 m13 13 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 42 indices rho q13 m13 13 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r14 : List ℤ := raw_ints% [0x34c8437ccedf6bd168469334e00000,0x4dc73179ca345bc9e971f1543e0000,0x359ae05b915b759891827661d78000,0x16f7f3aaf5614c471cd4b8f24b0800,0x6dbf007bef8020f5d453afc290000,0x18442e8e7fbf4fa422da327a44980,0x41e7720721f84e4e25bbb52b5880,0x8c8e030183cc8df760913617080,0xeebf498eed1e2dd3919fc27490,0x1459263df2f07830e6b7098098,0x1657874e81cefb6848648dbb0,0x13b76f81c1d91bcad3ebd62c,0xde3f38c6d401c55e3957ad,0x7b6535aecbb6d7f27399e,0x34da4109d3e2cb786bfb,0x10de63bc55b106bb280,0x3c85bde73072400d3,0x885aa2a5ad2ef9e,0x9176957710745]
def m14 : List ℤ := raw_ints% [0x0,0x290b59f0c72956c0171984c40000000000000,-0x394843b1acf2fd8a1544c19ccaf9e193fc7200,0x265b1515f8b7355d5b694e3fc4b31adbb047580,-0x1067503c0ac36212e95cb50b9373444d73190d80,0x5083e6d808590959dd6ca469e6e0e518977866e0,-0x12dd4f2a9a56c22d9bb7dd3120ac782e77edabce0,0x38266a71ff3438611a69ad2262a70f7480cca1280,-0x88335bc2aef607742b8fdfed6407b03422a7f9680,0x11234c209d52f39f60158ad2e594579e7439df52b8,-0x1d048b0cc3ea1e3689e15ac3de22277b82f0d23238,0x29b8f9a3ae2aab773be384823c849af72eb6ad3840,-0x334cfb6f386c06c69062ea7bf42268f3f67c4fd340,0x36357856a47e1c033df036ea470958c0499d984b00,-0x316386eae58067e387bca43754b738bf58963ef600,0x26de095823774e00479d2798d53840ea391c2564c0,-0x1a6f12eaf6b29d991da196c78dfa02cf9018c7efc0,0xf868388315cdf102cb6a11f8f3d16074043c51fae,-0x7dc05de1800f356f57609f16910a8a0465dc9918e,0x36b1b6fd838b92dc724e3aa9786a0c4d4072e56b0,-0x1458893748da1bcb5ccf89f439d36deabde610370,0x66f20db035140d29288851784c0276a43485a328,-0x1b75eba355e004e7624aa8bbc772f4c647749268,0x61e3ba1b1a5437b40d3d16a3fb40d71e4723e90,-0x11fda78cc9995e824c121104ee83b44ffc8c050,0x2af6e8075b388d7b8843985ed5c8af13f17c8c,-0x51b25cae2f4a94d7670ab921b6e32b648350c,0x789a4f3b95ca4ce8847894b024fbdf2bce90,-0x85c15388a2d129626d45a531ead57d37dd0,0x6ab373e8e7545b21deb0a91bb9d3574b48,-0x39b44c4362431ae614ca1bd9627ef5b08,0x13761b91c4d3f5716a9bde3129adac30,-0x39e4676c370c736e33afd045334c70,0x4e1ba1b3a850226d2f20bd717bbe,-0x21d1976a1f00efba66e8d6ffde,0x2275751a8ac71509905c000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 19 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 42 indices rho q14 m14 14 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 42 indices rho q14 m14 14 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r15 : List ℤ := raw_ints% [-0x9f439cec53b891d3a6e087bbd680000,-0xea6c34bcd20e0ffa3a19b8240768000,-0xa15d38d3ba1a9bcafcfd6256a9b6000,-0x450bab4fa76def45cbc241133234600,-0x149669b09598ce0bbc94512d207a500,-0x48b5e919b91e7e221b6b0b95346520,-0xc518915810132f43f3f080a4fbc90,-0x1a3743fea99b6e8efdc66b6048560,-0x2c6c89ee4b1b080b6362e234ebe8,-0x3c6a95fd9ff0f71ce3157a370da,-0x422235afa5add6d8fa4ab78f09,-0x3a28ff4afe4f53b59b3c6599d,-0x28cfd4b7fc78c2257fd9f3d0,-0x168e5a3224b743383542a4b,-0x99c2c1e350366bd3a1168,-0x30c55ff21160d5336fab,-0xadb33985d24b0c2194,-0x183e6a65f78667693,-0x199661bfe022833]
def m15 : List ℤ := raw_ints% [0x0,-0x3d9106e92abe022022a6472600000000000000,0x55075f71e9a540e39015c1c136c73444bae3e00,-0x38518440a4f5db2d82d92cf5103a1e7081268e80,0x17d07961b094aab5db28bbd46682ab511a1783680,-0x7384d5ae1aa629f1869fd5ed67f8e228b3faf3e20,0x1abc0c28d47cac1323e67d891d765dc619681af820,-0x4e8efe069136f45eb38323747ef1ce8e7162cea980,0xbc02a1bcc3ff0ce3e975efd9d126292bf6b4a18580,-0x17537c5a83a65b1d16cbd20bccb30b3e27681be4e88,0x26ea9987f64ef31804dd408a384d203ce5d4c1c0308,-0x3717e53cd45f4d41f5289c85d2298a4be7dd240e5c0,0x42a4b996e91a95559fed04119bcf3531aaaf4ff52c0,-0x45380b93ce9506c9f750c36814963944abd75c1cb00,0x3ded580e06760cf3087ce7b871211c874d8ebfe0800,-0x2fce05c530bf5c58edb0218c8d4ab9c115a44a67540,0x1fdab9143e006e64a6d54bc5b1b47b11588b6b33240,-0x124e79f0ff589dd152164cf3ab1ce638fef2a569622,0x90e05c7c10b3b4d92433a22640604235fbd21c4942,-0x3d778924af5a68e774b8e07162577cdecc56c4f5d0,0x16437fe94ef0e7cc6300553a411f629ec92715ab10,-0x6d756c89bc4857487a8d06c1fd89cd8f07fac7e98,0x1c4de302c954a3160f3200cc12038dfbc3cedcd58,-0x618b66e9477f442ce292c9f607cdba49f6b842f0,0x11471fb5c28a9fb26cde371a0cc18385828b1b30,-0x279f5d3d8bf859790a2d2c1c3806049b101a194,0x480a8ec8a4102944f5a7693f941067a5065514,-0x652d8290a3e3041012a1d61e31735657e0af0,0x6a1cdb5774869bb9841189b9c821c9d219b0,-0x4f77aac5151a1efcaef9fd820d036bee378,0x27fd318a82280d3afa6907e7288b039db8,-0xc69e69d78363e588230bcc5e54e5ec50,0x2189eac1c271476ce9a0d22c76d2210,-0x286e277a657e3f485ac1790dacb92,0xf54205285d316e4a6bb9d67272,-0xd547163b2b3fde2c4ee8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 19 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 42 indices rho q15 m15 15 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 42 indices rho q15 m15 15 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r16 : List ℤ := raw_ints% [0x1c03da4192cb2efeaa9306e9c4c580000,0x29319f072815e202de20ee69531dd8000,0x1c52e644d1924c7d4b7ffd9226ef12000,0xc1ab589ed5d41d11d22d61627bfa6a00,0x39aae1eea7df3d3e10507625ff134500,0xcb5b7e670c380da96332c9020ff10e0,0x2264d6ab673cd90d764f950a8c6f650,0x490eb89f3f5dee66dc7491c3c19290,0x7b89841fa3b01533c1192940f0ff8,0xa79c74a506a460d5dde9fa11129e,0xb6fb850798b13c8257a7b4c239d,0xa06f7165c785f3e14c8a3723e2,0x7031a561cbb01ba1671109807,0x3dc3d626e69f2faac1165178,0x1a325152daeac6bb600e13f,0x8440e9c61e9a4d7a61882,0x1d426fab59e26245a221,0x40dec51e0c9abcc696,0x43e006ca50004a34]
def m16 : List ℤ := raw_ints% [0x0,0x5c598a5dc01d033033f96ab9000000000000000,-0x7e41d66781697beab963a7ad7b3e5b22cca79200,0x52bf84966d392eef01fe3cc9e9df728630cf6cd80,-0x229b856f2fdf33d31ba815522154523c125b34e580,0xa5f5835ec5f5f0fcffac0cc297cc09bf9131c494e0,-0x25f3439a27c20d579c66028a2e090fe209b9bf04ae0,0x6e203770d9c77e4d0ae367ed75c6a25ce0e9b053a80,-0x1041ea315129e47ec4a98a3e5e7de609d8fd0ee6fe80,0x1fd4bf37e419ebffabe98da5123812ffa024e4a8ae38,-0x3457b77732beac0b448acf482d0801d9c3c7a41145b8,0x48fb107117ecfd621f85d87e052a86103644e41b8c40,-0x56e0006f095ededb20def8f590880ad2056b0f55d740,0x58b72afb651cee5f1de805577b911802e0482bc5ef00,-0x4df568217b354ac9b3eae60783a51e98810d39e28a00,0x3b0bce29d8a15687d04424042c27547be6056a1ea0c0,-0x268ea198ae64e29f44f19cbb21a02c6b4090e8bd5bc0,0x15af9ec388a49d19caa96e80ace11745f1475609f78e,-0xa7b64e9a0cd508525627237e6b9a5e56a9ba061d76e,0x456b5c43bb62587d8afb411e9d7d1cc19b6e68ce9b0,-0x187c1bc39c21dce3c919ab6d0c6367fa050de554270,0x74f98404be31b2aad0de891dd994b605178717a9a8,-0x1d5258373b9fc6bc68a3d84c44a9d0f73fb05bece8,0x61afcbbf424cb23f9af3d39c45031dfbf90be9f90,-0x10ac769f9b911b904a823b377204ebf02fdbadd50,0x24b5b5bb398857f9f108dd360926cd1f365e634c,-0x3fcd09d48d8c4abbeb1c502260dbf09a5dbe3cc,0x5536279e2043719228cfea8efb503db836ff90,-0x54770de7f56c19315bb4fd9207d6e4cc682d0,0x3b583a0ce999a45c8c4360eb864f910cafc8,-0x1bc43d17280161f0ca39a9b7cb2d5761b88,0x7ed6938f35c9682cb1b72296b44300730,-0x13700adf2db4c86d8219ff8d20820b70,0x14ec5321144203c92b813b2b2e549e,-0x6f1b7d0028881b5e5c54852cabe,0x5276c446cd0bea688a9f0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 19 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 42 indices rho q16 m16 16 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 42 indices rho q16 m16 16 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r17 : List ℤ := raw_ints% [-0x4a5095ee66974a077ba344683ee6a00000,-0x6d2c5414959a64c2086b3f91b978120000,-0x4afd0457a16899cf713a87035011240000,-0x2002bada6a5243bb7fe018182b0e91b800,-0x9850e3c73f3d87f1905dd9c4e062e6a00,-0x21862a9303c82607453bc5f2744eac380,-0x5a94afa58ddc2981bc4d9094c9547160,-0xc014ae84ae2475544ae100b3ce7ed30,-0x1443041b8ea15b56e10eaea87913010,-0x1b6ec41fd22c1ef0e42958bbd5ebf0,-0x1de0bee6524d6c5b8e832c5b16a86,-0x1a207f26e1f18eabe09b16c773b7,-0x123755e98213ea37001db19598e,-0x9fe8afd6acf2af6a2beb8dad9,-0x438f4f6d58d3d89b5bf91a60,-0x1538ed2634af58019d77119,-0x4abc65e6f9f028cf24c4e,-0xa4b26899f0828f7f737,-0xab1a2712e7595d54e]
def m17 : List ℤ := raw_ints% [0x0,-0x8a864f8ca02b84c84df620158000000000000000,0xbb8980026c598816d1e5d2c4fbe9a3020630e1e00,-0x79a8f1f45d72a1be8df8249f923a91ef0a012c7680,0x32575aa559daa6f3c05619e8bb7bb844890c5289e80,-0xeebb4e847b86d9a7dbb269c38224770feec12076020,0x35f53c32b3dc2cca492798ffe1bda67249c1f376ba20,-0x9aacd6c0e447676519d951da871034553eebe01b4180,0x168b0c45a9552910b8599fe94552781261323ab2bdd80,-0x2b8c19fd6a85baaeac4e101d66063928ce81875d88708,0x4699c60d8d02ee76d0768fe587603ea6ab135a6f8c388,-0x60fa50bd8c1dfacdb32fc54b2a085ce6ed4701a3f71c0,0x71a24205abe231b6f3c3df5c79fa4840220ceef83aec0,-0x721ee5d8e1890826e3faa0853df4efbbb5450c04b8700,0x62865fd3451c276f366d0fac948c7411fb1e7121c5400,-0x493bd0bed99eb2069d6881a023406720f72d106d3d940,0x2edfbc0d732517bdd034ae4cc83edbf3bc29e3a70e640,-0x19ce672c897d1cbe142461d87c33215f9ce1f4b3b8b42,0xc30fc51d2ba0165e31d4e33748139acb77c94debe062,-0x4ec797cf5725e973138ece1810d8546ceb1958dd6ad0,0x1b0f5952b52d08103dc09cf7b97bcb09f7f80e7bd410,-0x7da055a09666656189e479addc31068edf27767d418,0x1e8693a970ab3d9656e42aadf1cb25df0354484aed8,-0x624df461f30b63f4c73add234b14bc7f63b87d79f0,0x102a99774a56d2becd5c178f9e2125268407e73630,-0x2229ca9fa1b8fec0789a394fe27240f13a62fbcd4,0x38bcafef5b941ceb725ba997497d245795b5e854,-0x4807de0b8b1ffac515f76606f23b5eaa04871f0,0x43723e8e73675e0fb4272d45236e396df10cb0,-0x2c6dc69a0485086c1bb111a5ea5481121aaf8,0x135071f05516a0da682921aa4f06935ea938,-0x5114e0a6ee9954f8496840974803189950,0xb44c822440846c5e4f4a8e5888e3cb10,-0xad3471ba5a33df5b913b421778d7b2,0x324eeb4217bb181cfd0fe579fc92,-0x1fdeba3d15866fbafc76a0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 19 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 42 indices rho q17 m17 17 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 42 indices rho q17 m17 17 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r18 : List ℤ := raw_ints% [0xbb55e753299cd6aea348cbfa25f09f00000,0x112fa1f2f394e97887a15dde3076caff0000,0xbcb34ad6427b9e8810b048d2b169bb04000,0x50782bf61a298e639851cfc98a81cb44400,0x17e7762279a594ff5902e1db516cec18600,0x54132006c4e03774abaf5e1524925a62c0,0xe2dadbdcfa98f40c04a2d5240b7595fe0,0x1e053440697ee95fe81641f63cfb023e0,0x3294fe90fd540432a9082fcfc7a6e6c0,0x445aeacf7af380d0d94ced585ad55cc,0x4a4ad08890a255b99917d5dc97bdc6,0x40d02e67f0aded85f9246ea1ece78,0x2d11ec165bbde0fb056cd1109071,0x18a780596697bfe69f4ff1762c2,0xa6191364be35a4eda1dfb5aeb,0x33f9c2bab5164d29f3c53524,0xb63aa96bb4b28f8b44be1f,0x18f8918a0c1c6c9206db6,0x19c9b4e61b0bed6809f]
def m18 : List ℤ := raw_ints% [0x0,0xcfc97752f041472c74f1302040000000000000000,-0x116a5f1b7ef3b8c90e8d43994923fda52e8e644b200,0xb2fbbf1d8b670194f8d6ed9fcece92130fa94fea580,-0x494c344be3c0343b827f08672796d46fff181f6e3d80,0x157d980a2b33294e015d66d4cc1c1903144d0f89fa2e0,-0x4cd6c10ce25048e5902baa54f65dc6258553d00f6b8e0,0xd9a7ee1374445489fe3f6b1fbc6fa703b4339d2a6e280,-0x1f53dcec27f5d11a09bb5396b79ae4099339a08a6ce680,0x3bb96e95820ca02fc4e79871662d4aa99d35c58accc1b8,-0x5f7e10a037c48adae8d3e510a8682ea82a68b666959138,0x8142b71cf974d51b09495028ec567de031207a87e82040,-0x952193c31df519b9cdca6ca8c0b120b37f802096061b40,0x9354657d2d1d16edbd0e2008d1c820d8795a128d18d300,-0x7cfee7c430920074eb99fbe10853e7d3459c9951fa5e00,0x5b3343952a11a456d23be7c324bfff02519c067ac39cc0,-0x393a8b89bd2f87e7c4166d9c770da36a5a3992db5987c0,0x1ed8adbdf6fe6d1ea101f196995a2e0fe735648ce46d6e,-0xe3eb10c2b6866bffbb3f71037a9bb2a0dee59ef565b4e,0x59d342954685c8718e54fd3f2860710f22ef5c8b06cb0,-0x1e0cc0c0319d1394c3fc17bcb47b5f8e531e6994d7170,0x8792219cd8a0672278a152c9b0904a4510f420389828,-0x1feea129f92d2cd1e31172329156984e0d52c79a6f68,0x6364bdc55af4be11e78d0d1a151323039d307261090,-0xfbefb87556f347ab964b7cf28c2262c6b0d6dcca50,0x1fee301950ae7570b86b90fef12c445241b3b0760c,-0x32a7d3f507a13bb440a3099e34f967ed1fe00be8c,0x3d1a80f7044dc11a77d0e0ad12865fe7609ac090,-0x3604612951997780f52927b44f909175bb3d7d0,0x2156f955eacdce397082b10cb294164ff5dc48,-0xd74e98634c7e9090c79fe229f76f89216408,0x33e0b3bbc078521a0d28c2dcc80c38d1230,-0x688c72ea574a7a40b6ac90ee36652ba70,0x5996b96ba48778c7fa955d20ba1db7e,-0x16c47c59a5e30e8390047b38c239e,0xc4fb662f87e150597b39c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 19 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 42 indices rho q18 m18 18 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 42 indices rho q18 m18 18 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x19c9b4e61b0bed6809f,-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r19 : List ℤ := raw_ints% [-0x1c3c0bfd21fec733961bf1e8f9fa562b80000,-0x29696d3d41fb6a63e4ab099930cc2d0bb8000,-0x1c64fedca0daa83be2ed1912100c469532000,-0xc18eab82010a8583134368b53f919ae77200,-0x39706e19c141b57672644c21961addb91300,-0xc9cba5ba56e704d7485ac111af16b5c0b60,-0x21fd1e1123a4e3df77f8c3b87cae5315870,-0x47ddd48e9a34cae0b26bf19631807287c0,-0x78e7f616141735ae6bfb674459b7a8bd8,-0xa31d5016923a3dee50e0390e782dfd1e,-0xb0f3698ff570b6a06d43fb73a0267a7,-0x9a0d4dbfc3c9a0aa744e2331b55171,-0x6ae02b1de02acd4d4725791e71d3c,-0x3a4f80006a35b4b4115e0f4ef0f7,-0x187af5a5d9515c647c9730249b0,-0x7a284cae77a0516b0a179dd67,-0x1aaa919130be29253d62e258,-0x3a35df1b3cba459822e973,-0x3bcfcda1fffdabacc34d]
def m19 : List ℤ := raw_ints% [0x0,-0x137ae32fc6861eac2af69c830600000000000000000,0x19e26fa07151ddf787757daabae6bc9d72ecb02bfe00,-0x1077acf4d7c1092ea847c5417385176632245dee0de80,0x6ad268aa9c147ae5c8cc2d44f66953579e99866cf8680,-0x1efddc83ba5cfe37a8474706c2e19e96f26289ab05a220,0x6d9770111fe5eb2f4e34169b157d8423093aba2f9a9c20,-0x132d8f78ec0cdc7e0ec6a87f77d56c908d227602ac15980,0x2ba0ea1e084eb4c95659459b37efc503f8507a898e3b580,-0x521c66983d0da4afb446a53d49ffd7687558d096b014788,0x818349e8c93e25413ac6d590b2cc787601cb7b5fb2e8c08,-0xacceef477738ea5a246e73eb3a987439361a46cbd46bdc0,0xc45bd67304e0e9435d17d8dea738f9be8abc5abbde3cac0,-0xbedfe4f86b59a2c8baf424d228f5b8756d511776bcc0300,0x9f2d5d5f97e332ad28beceb081f77ea5f3f73d46e726000,-0x720760a42821074c57d7b11672af7b808beffe68ecf7d40,0x462a146011f6f775afbabd61802b6b8e66ccf12e611da40,-0x2508469e3d90e64e385b723326e0f5cb1639bee3ab9b262,0x10b83a28c441fc3c754dd743d9d5668d349a85501574982,-0x66e4efaa19255216eeedbd614b326fb1a7a7428145afd0,0x2186ec946bff418e0123b2cb6b99af471b96e0eaae8d10,-0x92fe7b57639c7aeec85fa4bb22a96435491a195440198,0x218f6386ad4e00d1b1981f00dbc33c5ec55458e232858,-0x64f4b95fa3e1c1021ef566f11b6d062205dc663420f0,0xf6780470e0e134eaf5aee04d78371eddf188f6d0130,-0x1df7b2fd6cdd5301c014e76c032a32c22c103f6cc14,0x2d65e51a15dfba7501858d6ecb337bc79cbadaef94,-0x340204645f252ae8ae24574a48881339868a648f0,0x2b6218e6faccda79d2ed16a7aebf037b340b2fb0,-0x19129bc5b77f45ecd965de83b86bd66b7036a78,0x963b0d9e41fd9c31a9163cfbf78cea46aecb8,-0x2137dc7b934698366f9a531c936ba3f01650,0x3ca20bfb37c2af7f7408e011bf00e10410,-0x2e533d146d1ecb371f8d49530bbe85d2,0xa4c6cac160826bab4907e4de188b2,-0x4c0f9f74e49415feb776680000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 19 66 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 66 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 42 indices rho q19 m19 19 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 42 indices rho q19 m19 19 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x3bcfcda1fffdabacc34d,0x19c9b4e61b0bed6809f,-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r20 : List ℤ := raw_ints% [0x417c84a815477ec56881d2d3f11148efa80000,0x5ffb622852ebc880ddcbbac7bb8a8c41c28000,0x41c2ad8a63330fe8e0634438dfa0e9ad6ce000,0x1bfe4053c7904cd46743e9b7c99a3564781600,0x84ca51682a8e4adbcd66a25cf28c8f4098300,0x1d20aba2d235351d3575d4b60fbc5d2226720,0x4e68649822a2ab208d8536e6a0b87c0cf130,0xa594d5f94b0e6fccadb5beaf6ba955ba870,0x1163011b2cd94f3d8b8eace793f63999ee8,0x176bc3b199ecce780e23686779c2c51ca2,0x195d746d7e85c83bc9fb40cdc4e8893eb,0x160a9fb0ecef2137fda5b4a4b26c7cee,0xf4287a25944934cd5d6cab5ca1e6eb,0x84e6f31daf14cf3dcb86396c1f17c,0x37a69c49ac550a74fc67f455c47f,0x114e2d215a3c3cc0adb6f90bd66,0x3c3e07ac7321140ccaa873ecd,0x83020750c5c7b5b2954067e,0x86078d21d432287328346]
def m20 : List ℤ := raw_ints% [0x0,0x1d3854c7a9c92e024071eac489000000000000000000,-0x267bcad40322f59596888762ff502f2255343d3f3d200,0x18419dd549e722f52649f53112e2f303d236fdae33fd80,-0x9bd218a561ebfd5c6c48b8cb7ffeae0b6f64a7fbad1580,0x2cbf4c8ad6182f24edb6d75d8ef8e9108d99dd13cc790e0,-0x9c8a9951765927169875b53fb302f37612bc9ab761006e0,0x1b15f00318f392486f6da3acad5de77a0c5705d341eb0a80,-0x3ce3309bcab1214fdf26d41dbbf6e6ea3196c7b20a294e80,0x7128b08d1b2b929b21a79a66817eb6c1e0db387ae8070d38,-0xb01fa2866625a7e6ca8e8406e857d538ed4cde78adc794b8,0xe7b584e75ac21b276b015d35aeb1892d9e26d096f65bf440,-0x1035fc1cdd92580e567cec9167a770ebb03e562bc4b3c9f40,0xf825baabc5e829852ae5b08b880af496a5a41df6fdf8f700,-0xcb7509b0875816f1442544447bebfa7afca39f46a1e67200,0x8f219a7f14de207b95d542d478e33a8045264a9cadc058c0,-0x5660ecef876c409099e7f21c014b1a58e11dae05116073c0,0x2ca652c99131d0818805ab449a023024a87b49bde9aa614e,-0x13b61c0d027cf26f485a6d66a86ce957ffa70c69a1443d2e,0x766664a8dbd0c7e4b9097ac231a07e6637007a2c1b11fb0,-0x25942ec97c7ecf1e2036349cd3b60b56d5024dd3dba9070,0xa01d96ee9a8c57059456480bb2b383aee12801d7b4eea8,-0x236ead367a666aa02158fa653b737b9e468923777599e8,0x67001bcba3690aebbe13601800dd730fb0af36b109190,-0xf2269a9abf8aad4b5f6ab8875d8c3750df0422e18750,0x1c3cf0c71fcaf027973d910112617168aaa6462c74cc,-0x28d59ce0c97b446f94fc10474c4f4e3c47de07a054c,0x2c6841fc052c232db13c2214aa746f68e85c5c9190,-0x22ef409e2ae028395d8693436b925516d5a667cd0,0x12e4b8aff88a5f85e802ec84b89f379c1fdd50c8,-0x68f6a07ee4655a25c571e4b815cc0e7144b488,0x1548cca2797cb6336836e0905c334dff2cd30,-0x232acbc250d0aeb533de4ed639619c65970,0x17f24b4e88b9aab75e34bee46c6c8f05e,-0x4a7f5fc239b0f0dc0bffb2a1cf2a7e,0x1d5b716afdfcf91e936cef00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 19 68 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 68 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 42 indices rho q20 m20 20 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 42 indices rho q20 m20 20 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x86078d21d432287328346,-0x3bcfcda1fffdabacc34d,0x19c9b4e61b0bed6809f,-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r21 : List ℤ := raw_ints% [-0x92bee0739879cd49d2e8adc4857e493a7b00000,-0xd6f178a070dabe3de7a74381bb06d03afd30000,-0x93292676eef3694b04db3497cc9f53b4970c000,-0x3e986bad8a3c68c91765a281d70e3832766f400,-0x128ade0964520aa121176514726fa12e476e000,-0x410416ec3a9564e37c688a760e1e5d10b774c0,-0xaed5cb3daf550bda9be245cea285c1bfee5c0,-0x170ccda3a223bfc7cd8a3617d5773068a4110,-0x26ad709cd1d2c9daf59bbf0c04572c9d3140,-0x340792d2aa9f7345e7d3db42b5c7cbdb7e4,-0x384364c0741a585e20474df6dd307eadac,-0x30cf32586a4dfd5e445fbd00f30df6fcb,-0x21baae7911b65091997dfb7f3aec90da,-0x125264596132a8b21230329d3b438a5,-0x7a780a66adfe99bbae0a5104725d8,-0x25fc22560b8487b5ade2d876eb95,-0x83d876a0594f5ebc5c5871d1b2,-0x11dc72d399743e81806f415c7,-0x123460cde37421559e81e70]
def m21 : List ℤ := raw_ints% [0x0,-0x2bd47f2b7eadc50360aae026cd8000000000000000000,0x393b631cd4de2ac9ae1bb6baaafa03c15a7b180ae7de00,-0x23c0115cf78fc239316ea0fc70a6943ac01ec7d16abc680,0xe37f3281e3dbb52edc6c3a73653f66d297357c8c634ee80,-0x40af4ef9fef8a1063379cd7216d70ae20170979524ac0420,0xdfef83e0559fcb423b37892bd6d3f62f3da31426a9809e20,-0x265261ac3615b81989ed2976d1ed7c4ef8626b4f7ffd0f180,0x55261ab77b26d7aeda6284f395a0bc7efcd443f48fe010d80,-0x9c500a3d085875312d326141634b6c99eba3a09f037611008,0xf0233b082c79c631c0cb334fcf0f13ea05d7695ac7afbdc88,-0x13795c72d4fbea3cb0d3e31795c533950b904210401370c9c0,0x157b17a8d42968662b3a92699926496360e54cfc484a8ba6c0,-0x143b408f3d75b7abde59fbf2a827e3e399495f4cb6f3933f00,0x105003aec949dd16d6614889c4fd9a9d38568c87b45ad02c00,-0xb45a7927de208e4fcd927cb393483b570c493b45f18ed6140,0x6ac52180fc16df9efe99b731c90fe2c38420ecf795f6a0e40,-0x360f8c43e56899ff7fbcc74103899d4740edf558864102b82,0x1756e81de0d09243b2c80360559a514a053a1ae87769b24a2,-0x88d929812186332baa348ed42a1c70a588e622bf618644d0,0x2a4f5b4efbfe00265fae2ddabd529dbd1769226e5cb2d610,-0xaf31dba51d50e7959928fe4b8d62c6a1afef26a9d0e8718,0x25935eafef72b7c51a47998252c93258e29f0f69110b9d8,-0x698ab570caa04dc63466829606c8dadd1b34f1b40d37f0,0xeee49d1e17450613bfb46ba1fcfa26732e4f1b07b7c30,-0x1ab6044396f833d79ed440bd46fe875eafd8c6e3e0f54,0x24db912159c4a7aae34b1e08eba61af8f6c469a3aad4,-0x2608391fed75f27f2552a64ad9a02a02e82a6918ff0,0x1c336f686b85ff650d8e61dd6dbf01e7cbcac782b0,-0xe4375dd5d963268f20e6a77267eeeb52e71fa1f8,0x496c92b6ac2e4bb8e18c15ad613b2cfff85e838,-0xda545a2d03d9d16ff65b76a423baf498b6350,0x1465c99fe0c85dde3e08cfea7c9f3309cd10,-0xc5fd1527a216928ae36df04cfb011f5f2,0x21aa432ca722ddc6cc62ff94f24b6d2,-0xb538a368ef880b7a87424a00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 19 70 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 70 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 42 indices rho q21 m21 21 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 42 indices rho q21 m21 21 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x123460cde37421559e81e70,0x86078d21d432287328346,-0x3bcfcda1fffdabacc34d,0x19c9b4e61b0bed6809f,-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r22 : List ℤ := raw_ints% [0x13ee88a9346a85cf204ec197b9faf8da8ef800000,0x1d2d6c53db9c5bce660f6a4c75f51e1faef480000,0x13f69d1ebfef0f059e6db2942253e329e87bf0000,0x87c45cb7d283d4f41c025a6b4b84a81bfda96000,0x282fc00c13f799644403c736c476bb2e2546fc00,0x8cc972d697b06019b1cf39ef046804c45e00600,0x17a3cab4126e428c99dbd04b56a95a2e2cfe640,0x31d0a2a506d09a0b18ec9b5257cb8755c14440,0x537e89b53b9927cfc6f5e837b99578e38fe70,0x702dad3e2990b9836c2aa2e577cfcb2965a0,0x7923fcdf8ac6a7b1ce0ba737165945af9cc,0x68eed8e67fe2583ae2e1673d697a3bae44,0x48645232937b12113822be4d6a6c52175,0x2740321f750c68bda9ce36eb005a31a6,0x105d3036c59a1dea71cdc5d8f3ecd7b,0x51054fedbb2b1a0c4f8ceabcb2e48,0x1187fd2ceb41268f2443544c5e2b,0x25e3a5734cc80590cde8fad66e,0x267dcf19cc40a9ad1075cce9]
def m22 : List ℤ := raw_ints% [0x0,0x41bebec13e04a7851100503a3440000000000000000000,-0x552385cb8a893c25e2db04d6dfb98565f210f28fad4f200,0x34b898d7736f513d32e3af0bac4bf20faed5e092a96ed580,-0x14c6e74ceff9d576188768342f270809b8daf257f0d896d80,0x5d9d26710a76a6889dc6044c8d5e4b65a20f3a9ccb50a5ee0,-0x140cebecec9dc590724a28d9ff3c964b8868edc8622ffa34e0,0x365022a750677cb075e1e1b9b4dfed174200ec475b3009b280,-0x775157afeb5c4b91221244650f07ba0acf67c80eb454843680,0xd86b5c823947f6092fc5ac1698ea0e9e084585157fa89b10b8,-0x14842a9bcaeadfb3761460524cd83343fbc5b2694aa25d6d038,0x1a42f901e67cd3a122f58d077314f037e7fadf8967d277f0840,-0x1c8d55ee6d26d97b12ac2552d4ecd2507ae4cb167a49fdd6340,0x1a7accb9cc58467f66d0e047b45c001f61ed3b9073e7dd65b00,-0x15003de39e83669f965bfacac465f38bed9c8de243b2826c600,0xe41d65c1a9f7cd24abfc5934ed5359cc51a358f6ac4ba0d4c0,-0x847fd5da37a7cc052b3f52502f4877aa7ae828b6ae74ae1fc0,0x41b9d75744154294cfd654637da94d5a6ef2aae35e1d67b32e,-0x1bc0d44310a34400168b75f5e097d03ffc49571601d9a25d0e,0x9edc3f35a1219f3815adad16a7b471a0b0b14bbdc236f02b0,-0x2fd8c0e29c768c90acc70c2a1ca2231deece234f5fec39f70,0xc089c91d60cdf129437e33ecce81f02c699b9455826f2d28,-0x28058b2a4f69b78c127a6160c306f31b4f3887c9f2d7ec68,0x6c99f44bd381e2fd9bdc4cc0dea4a164c8e32328a0b2290,-0xec9f77e7e0c33da5559d4a33b05d0ea4d7c4ce9cee1450,0x195c42816ba646858b0dd5ecbd07042cc12e1903ad1f8c,-0x21611348bdb55bd5726201462ebce2d06c2b772b4780c,0x20aa66d906acb7691b625584c4606f6fc164cccf7290,-0x16d167d35110ef71fb3c48a8206e3a4a7f3059b71d0,0xac95edb4211bf565abd4babd80a5ad1aa3aaf8d48,-0x336aca6ef5052b9a2d732d1ba7744ca2627c8d08,0x8c0a3e7d2f384723d68c8ec83e736a74283830,-0xbd4ad50515910a006f5ce2afbb781d63e870,0x66464f9f51fe4ae1f36aabf8d73f1c733e,-0xf34b72aae6d02ae5b11815911d3bf5e,0x45e3a8ce7bea6dea5fd72dc00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 19 72 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 72 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 42 indices rho q22 m22 22 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 42 indices rho q22 m22 22 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x267dcf19cc40a9ad1075cce9,-0x123460cde37421559e81e70,0x86078d21d432287328346,-0x3bcfcda1fffdabacc34d,0x19c9b4e61b0bed6809f,-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r23 : List ℤ := raw_ints% [-0x2a24b1aa8035bdcca218b3aacccf60baffbb880000,-0x3da8907946aefeb9d648ff08666f38fe6823b88000,-0x2a296924bcd7c0c356c2bda14f5d36d0ddf084e000,-0x11e8bfe07441d71d81fa5a00fda015e7968beebe00,-0x54c18b638e11f3e3beec50f784e10206fec051100,-0x128b23cc8459bb8d6c7c8c184f7d4cc2650af77a0,-0x31c6b0cbaef259d90b9591d9bf976cc6b9a86d50,-0x68caceab4ed1c16f37993d049dbd0fa8f75e520,-0xaf75caeee8e98361d2af24f0e1f4fd83ee4248,-0xeb78f04fa5648bbb9123209897319672913c2,-0xfdf813ba2e8753b8f78c4ffae3b89113b1d5,-0xdbb083ba7dc60163a235ecd4afa190e53c5,-0x97551b52c8eaaf78780b9c23a0cee04668,-0x51ea602c578a3a6f5c68477aa5898cde3,-0x22169bd2dfd47c99b75ce311fc21e158,-0xa86e1d6e472592bc97a582f763aaa3,-0x245c8332b4acca73d00096b38c85c,-0x4e626f84f432fd1136a312210b3,-0x4f66a1c6b9bf754dd6a2a48f7]
def m23 : List ℤ := raw_ints% [0x0,-0x629e1e21dd06fb47998078574e600000000000000000000,0x7eb04b4fbbf4146c6af79c34b085dfc28bf85cae8921be00,-0x4dcab2828a33b5b66bbbc77ae41e600ffbfcb0a88f8f52e80,0x1e62dd3512be992bcaf1df27ec9e3896373c15206295c0d680,-0x87a24f0054f2f9e72f380695e3e9e8424ca06f436ca53c8620,0x1cc3c2176dd9b645640374dcfab91f573a4840465b1f86ac020,-0x4d1b92aa20b54b3f1d6ef6768011ad5d5d495d12745f2820980,0xa7873d889db0169ad0ed87444001311360298809e2bec1be580,-0x12c502e4d386a9b65e9f03eddd579846bee79c73a7c7d2086088,0x1c1da3c4429c100a99444c56fc75f83acfbec1890d9712713508,-0x238373b7164661187f1603100e6b040846a09b113040e78195c0,0x2610ff1dfa10e701786ef1ac1cb543a39ccd207aa54912d742c0,-0x22c56ece266fe030aa82e3329bf090061a8fb68566f9e4013b00,0x1b21aeb5113cca08e91b052a841674eded5e4993afde1ee5b800,-0x1219879e00a03b542a9684fb1232056b43785745ae5d69c18540,0xa511de24d566dd446babd7a878519784cfb31af76ffe69d8240,-0x503b7d2bc7a79894d860b4ccf12d19dc1a5cf38e9d2572016a2,0x2123c38f648c24579482f939806f4403e763df3619265f891c2,-0xb9334bcd3731ca1d1fbb43d2f0341e8d5c4512ee35a37229d0,0x36575b5a74716b7e42ea6e1091e3ec22a8210583d67f21af10,-0xd48240af8936d44cc1f1a22b555a4d451eaf38d0cbff0e498,0x2acea4b94e9c9f1e60a7e48f3d04aba068581e23fd2bae358,-0x7034ee4780f4b05c36591906004ddddb90bcb6284037bef0,0xeb484a9a855ea813cf922ae32fbd13d649d95fb018da730,-0x182a049a550dc063494b8f74adce290641c2a64884cc694,0x1e534b752233fbcfb548857adafff9ff7ba9bbd1eb5a14,-0x1c21f1bc525f490e3736725520f30258b2f25cedd46f0,0x1280ac2f592b24f088c699f00db003bffc1b19e905b0,-0x82b89efd0100ce2235cdaa8ea953d9b7572175d178,0x240a7b77a07b1ca10d51ade9c3995482819eb1bb8,-0x59dc128b877c8165b105310dafcdd9cdf5f8050,0x6dc8c2fbfdc84912dc13f82cd6d21e6b72610,-0x34d01f7247a99fa131f898d7b036ebf4812,0x6dd7564771f1ce8952ef4648e3eba6f2,-0x1af160aa4ca7c901c72605e800000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 19 74 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 74 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 42 indices rho q23 m23 23 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 42 indices rho q23 m23 23 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x4f66a1c6b9bf754dd6a2a48f7,0x267dcf19cc40a9ad1075cce9,-0x123460cde37421559e81e70,0x86078d21d432287328346,-0x3bcfcda1fffdabacc34d,0x19c9b4e61b0bed6809f,-0xab1a2712e7595d54e,0x43e006ca50004a34,-0x199661bfe022833,0x9176957710745,-0x30355eb94dbc,0xeb3ac6fb12,-0x40d246ca9,0xfbc19db,-0x33d5ba,0x8840,-0xff,0x1]
def r24 : List ℤ := raw_ints% [0x56ef2198badd09c75bc817767ecfa83f6412b780000,0x7f2044b774006241ab56d76828566e3484acfaf8000,0x56e1548e0bd881182ac0770bf6621978c133a7ea000,0x24e1d0e1c98bba09ad563b3f1a42d41d25f50dfa200,0xae6e618b1e05182088f73a2755e2750a7fa89fb100,0x2622c21d31ac5c94a73aaf793fe05b0c72dfdbe760,0x66496c2805ba067a0dd8b1916f299504e7b4d1b10,0xd727eef89e64b43a8c571af495a4c9df4d377b50,0x167e8e439b7ac4a3f1d3a27f1862979f55eb1b58,0x1e282bd0868074d41f1dbd64e8dab1286deeb46,0x207d2e6b7897ae63e9f423e50450ac85fedd29,0x1c11a1bfca8c232f583e602f8160f4159b97a,0x134f09e4f6abb2019e550ee850ae493ac60f,0xa6f9d63fe4600094cd817494a2672d2740,0x455ea97e5bc399c11caa692a26789495f,0x1561fcf0a7ec9e0dfdce24b2325b8cca,0x49b541e417df28bd15290fe7715639,0x9e87d670725053991e8a44d81706,0xa02d29548972886714fff12a48]
def m24 : List ℤ := raw_ints% [0x0,0x93ed2d32cb8a78eb6640b482f59000000000000000000000,-0xbc9144bb5565124cc90f186b742139a7a935053ae52081200,0x72d8f266ccd2932d1ce2391818525e19f523f2f830de072d80,-0x2c79eea5eff92c7ca102e9d58ce97e786a3f35a8dfc02db4580,0xc4bb7ed2125b365b0e72ed44bb6bb4bba2b430fd358a3d60ce0,-0x2952bc01964c70832b88dfad61f9e2cf29dd5982665e45c342e0,0x6da68bb9b33bf44021b2d95b98ea3af703878229ce8b472ada80,-0xebac44020f6c0c6f753d2b0b6ca5a5973058e7d47c3fc5a59e80,0x1a1a5779c9217611a6a61cf9a7992e2f276b4c581165d6ac44c38,-0x26a01aa27563fae51305d830f63dcf6e230386ebf96293186c3b8,0x3027e387deb44a42a08dce54eafd1ecc5236123eb76f35db55c40,-0x32e6fc2a143f97fa2eeedd13f8d64129c38aee223c622fc2c6740,0x2dce52b5f5bffe8486a9c2bd9b66a62e641882a2872c354a0ff00,-0x232c24d13659806e0f61525eab080a70c54c7248a375f1f1b5a00,0x170fc80267eb0905e4524eaa97770016acfe7f144270ca4b110c0,-0xce6ef3290ff0dca84d7ef6476d5910583a1ad33ad66240be8bc0,0x6254942e2cb9df705c818451832d5265bf756e7efbedf766430e,-0x27bbe0f217ca67c7e1d6ef5519283d77d144b67eb59682dc9aee,0xd8cf9f694daf355f9a54677a6b8a8d4f13ad5d94e6a072115b0,-0x3dfa4d49ff16118caeaa5a66524db1f3377f2c0291443579e70,0xeb8947fe52196b2247139be528319e64e28f6b3e66e6f9d3a8,-0x2df9b0eab3fe270c47df39a0495c5bddeadd2cb3d29af7e6e8,0x746473dc390159f64e9b7a35d2bbab36b91b8d2c6e066c390,-0xead36f0c8967cc87964fe14e992ca4d0ce0beb46ee3f7150,0x171a7bb0d582f0f258d0e728f0cb58fa0b5e3f24a8f1364c,-0x1ba2823555f3061f0eef4c468d0790d4b4a53cc87ded6cc,0x184a7728c8f892c5b60694f4e7e3f05071b77d8c9c6390,-0xf08a8bf468248df4281103079825475900e4f227b6d0,0x6327a7c1bf457b8933e0e508b6ec188062efa9911c8,-0x1948dff1188361ce3e0199f983099f5f1477216d88,0x39add7e04835b74bc226417266f3e9a3c8a85330,-0x3faa5a59db3a31bd6f9c31d854a353b63a6770,0x1b4307eda61fe391ddb41989b7ff836b441e,-0x31916803c6daac3792a7f2b11a74ec23e,0xa61fe268297885e15bdfe3f000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 19 76 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 76 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 42 indices rho q24 m24 24 1853988423243303739392000 24=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 42 indices rho q24 m24 24 1853988423243303739392000 24 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<25) : intPolyRF (mz e)=rfPoly (C (1853988423243303739392000:ℚ))*rfX^24*(1-rfX)^17*momentRF (key size) (X^e) := by
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
#print axioms moment_source_24
end
end CatalanCore.Li2.NVMod.FamilySource.V6C25
