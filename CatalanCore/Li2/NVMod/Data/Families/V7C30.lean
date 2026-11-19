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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C30
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,30,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x27adf6cab58d8a06b4e00000,0x3bfb532cd12c24514e960000,0x2af6444d607350a319d50000,0x136753c45a4d01be70f42800,0x6342e0e8e8952178e2b2a00,0x17e898b06d696ea89172e80,0x481e3fcefa8dc60bd1f860,0xae9f2c3848ab8d27089d0,0x1595507c49ffde17070f0,0x23482641398fd11e1ce0,0x30101f3db60286860a6,0x36d756f2ca3dd5e171,0x348b8ba8dd4f54174,0x2a4819a747d33ffa,0x1c82a3dae1f5b72,0x1008510ffb54bf,0x775cd0b886e8,0x2d6c78dfe4c,0xde60d382a,0x355c501f,0x9aae74,0x13e3a,0x19e,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x5,0x37,-0x21,0x8f,-0x8f,0x861,-0x2cb,0x832a3,-0xbec9,0x10d0971,-0x7f5ad,0x17e107,-0x2305c6,0x242f7713,-0x602919,0xfa6b067,-0x904903,0xa6377,-0x1277f,0x584005]
def rhoDenominators : List ℤ := raw_ints% [0x283e926e9800,0x75131e590,0x8cf5280,0x983bf8,0x2e9e00,0x15950,0x7080,0xc4e,0x1c00,0x1e6,0x17bb0,0xbd1,0x74040,0x1e2a,0x3e90,0x4ffb,0x5b6800,0x15950,0x68e380,0x994c8,0x28600,0x1a7f0,0x6430380]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 30
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤29))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤29 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 30 omega7=padCoefficients 30 (omegaCoefficients 29 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 29 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 30 omega8=padCoefficients 30 (omegaCoefficients 29 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 29 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 30 omega9=padCoefficients 30 (omegaCoefficients 29 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 29 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 30 omega10=padCoefficients 30 (omegaCoefficients 29 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 29 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 30 omega11=padCoefficients 30 (omegaCoefficients 29 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 29 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 30 omega12=padCoefficients 30 (omegaCoefficients 29 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 29 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 30 omega13=padCoefficients 30 (omegaCoefficients 29 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 29 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 30 omega14=padCoefficients 30 (omegaCoefficients 29 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 29 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 30 omega15=padCoefficients 30 (omegaCoefficients 29 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 29 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 30 omega16=padCoefficients 30 (omegaCoefficients 29 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 29 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 30 omega17=padCoefficients 30 (omegaCoefficients 29 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 29 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 30 omega18=padCoefficients 30 (omegaCoefficients 29 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 29 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 30 omega19=padCoefficients 30 (omegaCoefficients 29 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 29 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 30 omega20=padCoefficients 30 (omegaCoefficients 29 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 29 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 30 omega21=padCoefficients 30 (omegaCoefficients 29 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 29 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 30 omega22=padCoefficients 30 (omegaCoefficients 29 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 29 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 30 omega23=padCoefficients 30 (omegaCoefficients 29 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 29 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 30 omega24=padCoefficients 30 (omegaCoefficients 29 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 29 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 30 omega25=padCoefficients 30 (omegaCoefficients 29 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 29 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 30 omega26=padCoefficients 30 (omegaCoefficients 29 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 29 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 30 omega27=padCoefficients 30 (omegaCoefficients 29 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 29 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 30 omega28=padCoefficients 30 (omegaCoefficients 29 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 29 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums29 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens29 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349]
def omega29 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums29 omegaDens29
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_29 : padCoefficients 30 omega29=padCoefficients 30 (omegaCoefficients 29 29) := by decide +kernel
theorem omega_spec_29 : coefficientsPoly omega29=omegaNumerator 29 29 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_29
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x14,0xbe,-0x474,0x12ed,-0x3c90,0x9768,-0x12ed0,0x1ec12,-0x29018,0x2d1b4,-0x29018,0x1ec12,-0x12ed0,0x9768,-0x3c90,0x12ed,-0x474,0xbe,-0x14,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 22 li0=padCoefficients 22 (liCoefficients 21 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 21 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x13,0xab,-0x3c9,0xf24,-0x2d6c,0x69fc,-0xc4d4,0x1273e,-0x168da,0x168da,-0x1273e,0xc4d4,-0x69fc,0x2d6c,-0xf24,0x3c9,-0xab,0x13,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 22 li1=padCoefficients 22 (liCoefficients 21 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 21 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x11,0x87,-0x297,0x8c4,-0x1584,0x270c,-0x33cc,0x2e9e,-0x12fe,-0x12fe,0x2e9e,-0x33cc,0x270c,-0x1584,0x8c4,-0x297,0x87,-0x11,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 22 li2=padCoefficients 22 (liCoefficients 21 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 21 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x45,-0x99,-0xcc,0xa5c,-0x270c,0x5d3c,-0xa092,0xd0ea,-0xd0ea,0xa092,-0x5d3c,0x270c,-0xa5c,0xcc,0x99,-0x45,0xd,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 22 li3=padCoefficients 22 (liCoefficients 21 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 21 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x5,-0x2d,0x249,-0xbdc,0x258c,-0x5064,0x76d4,-0x7242,0x300a,0x300a,-0x7242,0x76d4,-0x5064,0x258c,-0xbdc,0x249,-0x2d,-0x5,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 22 li4=padCoefficients 22 (liCoefficients 21 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 21 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xb,-0xdb,0x51f,-0xf54,0x1434,0x14ac,-0x9a2c,0x16a46,-0x2106e,0x2106e,-0x16a46,0x9a2c,-0x14ac,-0x1434,0xf54,-0x51f,0xdb,-0xb,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 22 li5=padCoefficients 22 (liCoefficients 21 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 21 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2b,-0x195,0x381,0xdec,-0x6e1c,0x151a4,-0x25e54,0x289e6,-0x11f1e,-0x11f1e,0x289e6,-0x25e54,0x151a4,-0x6e1c,0xdec,0x381,-0x195,0x2b,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 22 li6=padCoefficients 22 (liCoefficients 21 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 21 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6b,-0x123,-0xf99,0x7194,-0x14454,0x18384,0x107dc,-0x6e952,0xc564a,-0xc564a,0x6e952,-0x107dc,-0x18384,0x14454,-0x7194,0xf99,0x123,-0x6b,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 22 li7=padCoefficients 22 (liCoefficients 21 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 21 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xeb,0x573,-0x4d67,0xe154,0x609c,-0x807b4,0x156864,-0x1b6552,0xd09ba,0xd09ba,-0x1b6552,0x156864,-0x807b4,0x609c,0xe154,-0x4d67,0x573,0xeb,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 22 li8=padCoefficients 22 (liCoefficients 21 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 21 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1eb,0x23b5,-0xafd1,-0x16d04,0xeebe4,-0x23a0e4,0x173664,0x36f396,-0x8f6afe,0x8f6afe,-0x36f396,-0x173664,0x23a0e4,-0xeebe4,0x16d04,0xafd1,-0x23b5,-0x1eb,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 22 li9=padCoefficients 22 (liCoefficients 21 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 21 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3eb,0x937b,0x56f1,-0x127704,0x304014,0x16ac34,-0x1226d24,0x1f9e636,-0x10cdcae,-0x10cdcae,0x1f9e636,-0x1226d24,0x16ac34,0x304014,-0x127704,0x56f1,0x937b,0x3eb,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 22 li10=padCoefficients 22 (liCoefficients 21 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 21 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7eb,0x20ccd,0xdc737,-0x48c5dc,-0x4eb5a4,0x323c0f4,-0x4b23d54,-0x1a8b042,0xb8d7b7a,-0xb8d7b7a,0x1a8b042,0x4b23d54,-0x323c0f4,0x4eb5a4,0x48c5dc,-0xdc737,-0x20ccd,-0x7eb,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 22 li11=padCoefficients 22 (liCoefficients 21 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 21 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfeb,0x6ccc3,0x62d009,-0x1ed29c,-0x6837234,0xada2fdc,0x113cd294,-0x3abe7d02,0x24e012aa,0x24e012aa,-0x3abe7d02,0x113cd294,0xada2fdc,-0x6837234,-0x1ed29c,0x62d009,0x6ccc3,0xfeb,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 22 li12=padCoefficients 22 (liCoefficients 21 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 21 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1feb,0x15b4a5,0x21b5a7f,0x8110e0c,-0x20f0c8ec,-0x36ad2af4,0xeb2807b4,-0x4573abda,-0x195a0cd4e,0x195a0cd4e,0x4573abda,-0xeb2807b4,0x36ad2af4,0x20f0c8ec,-0x8110e0c,-0x21b5a7f,-0x15b4a5,-0x1feb,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 22 li13=padCoefficients 22 (liCoefficients 21 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 21 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3feb,0x43bc4b,0xa37d9e1,0x565e228c,0x11ca4dc4,-0x35b0da4bc,0x100ba3f8c,0xa80b19906,-0x899027a3e,-0x899027a3e,0xa80b19906,0x100ba3f8c,-0x35b0da4bc,0x11ca4dc4,0x565e228c,0xa37d9e1,0x43bc4b,0x3feb,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 22 li14=padCoefficients 22 (liCoefficients 21 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 21 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7feb,0xd0733d,0x2e731807,0x28bff3cb4,0x85c9f380c,-0xe15e5ba9c,-0x350ad2c084,0x3684e0dace,0x5e931b40aa,-0x5e931b40aa,-0x3684e0dace,0x350ad2c084,0xe15e5ba9c,-0x85c9f380c,-0x28bff3cb4,-0x2e731807,-0xd0733d,-0x7feb,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 22 li15=padCoefficients 22 (liCoefficients 21 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 21 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffeb,0x27bd813,0xcaf05279,0x109c911a74,0x6b884035fc,0x865c4c646c,-0x1e72cd9d43c,-0x2ae0da5e9b2,0x391ebf4de9a,0x391ebf4de9a,-0x2ae0da5e9b2,-0x1e72cd9d43c,0x865c4c646c,0x6b884035fc,0x109c911a74,0xcaf05279,0x27bd813,0xffeb,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 22 li16=padCoefficients 22 (liCoefficients 21 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 21 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffeb,0x7888695,0x35fff01cf,0x63e8ca001c,0x3f2e35ceb44,0xdec6536d3fc,0x60c0a95b004,-0x2acfb74f4e4a,-0x27452385909e,0x27452385909e,0x2acfb74f4e4a,-0x60c0a95b004,-0xdec6536d3fc,-0x3f2e35ceb44,-0x63e8ca001c,-0x35fff01cf,-0x7888695,-0x1ffeb,-0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 22 li17=padCoefficients 22 (liCoefficients 21 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 21 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffeb,0x16c3921b,0xe1e590fd1,0x23b0a3a2f1c,0x202aeb07b474,0xbcdd01f94954,0x1b02adfa6613c,0x7d79f77690d6,-0x30cf60378c0ce,-0x30cf60378c0ce,0x7d79f77690d6,0x1b02adfa6613c,0xbcdd01f94954,0x202aeb07b474,0x23b0a3a2f1c,0xe1e590fd1,0x16c3921b,0x3ffeb,0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 22 li18=padCoefficients 22 (liCoefficients 21 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 21 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffeb,0x449eb4ad,0x3a57c339d7,0xc518ed03244,0xf103b4a15ebc,0x7fd9287e5f2d4,0x1fd2ffa0baff4c,0x3a2e76af5906de,0x218e92263048da,-0x218e92263048da,-0x3a2e76af5906de,-0x1fd2ffa0baff4c,-0x7fd9287e5f2d4,-0xf103b4a15ebc,-0xc518ed03244,-0x3a57c339d7,-0x449eb4ad,-0x7ffeb,-0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 22 li19=padCoefficients 22 (liCoefficients 21 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 21 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffeb,0xce841c63,0xef00b9b7e9,0x42669ec18a84,0x6ad95c78ce72c,0x4cbbcf144b17fc,0x1bb31cf88b659f4,0x5648af6dc568e9e,0x96e4a3c9265b98a,0x96e4a3c9265b98a,0x5648af6dc568e9e,0x1bb31cf88b659f4,0x4cbbcf144b17fc,0x6ad95c78ce72c,0x42669ec18a84,0xef00b9b7e9,0xce841c63,0xfffeb,0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 22 li20=padCoefficients 22 (liCoefficients 21 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 21 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x15,0xd2,-0x532,0x1761,-0x4f7d,0xd3f8,-0x1c638,0x31ae2,-0x47c2a,0x561cc,-0x561cc,0x47c2a,-0x31ae2,0x1c638,-0xd3f8,0x4f7d,-0x1761,0x532,-0xd2,0x15,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 21 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^21 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
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
  | 27=>omega27
  | 28=>omega28
  | 29=>omega29
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
  | 19=>li19
  | 20=>li20
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 29 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 30 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
  · exact omega_spec_27
  · exact omega_spec_28
  · exact omega_spec_29
theorem cache_li (j : ℕ) (hj : j<21) : coefficientsPoly (cache.li j)=liNumerator 21 j := by
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
  · exact li_spec_19
  · exact li_spec_20
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x1aa8fd1e39cefebd3b37e9000,-0x37abe80962d8ab5af3bd8bac00,0x387b5a469edb1edac7e53acf800,-0x25179ac850a0aa41a6c0e254e400,0x11b9233dcf55e03d05700630a5400,-0x69102425f1b25d4e74e02026ec640,0x1f69521e25e9a683964cee16a10440,-0x7c97fbde865428b31f3578a929ba00,0x1a1e13a1cd7e76f0e9c462ac223f400,-0x4b28d954f8a3d4e3ae1e194fbcf9500,0xbbad16f3fa6ff485d8199e203b68200,-0x19a37c6969b19570bcea57b487a87a00,0x3165543110012d6e0ebf985d6ed8b400,-0x5458913ced154932c1fa83e4bdf561cc,0x8034c51d674a1a8ae0bd4b574898bbbc,-0xae1018b000c508947fbc5a0702e72888,0xd3a32d57b7bf270e395c53279431e748,-0xe6e36ef90d17eb925d784d6af9372f60,0xe24ed9633fcb75eaa0637bfb3aebcb40,-0xc76f731bc064a1dd14b870e127c74d88,0x9e0c6375bfc412c8dcf094aaa5326188,-0x70981c9e9d2a0ad9995cb00a1a8b8557,0x480b75b5e27e342d9abfb17e0eb96fc3,-0x29589fdf26de5028036767cfd9be2126,0x153d64845a1e3e99ad93ad3552d99306,-0x9bdbe4626bf1ad991e3719fd5b1c92b,0x3f9b326f22ef190438a17a07f5e1c9f,-0x1700dc8363733f279e082e419fef8b8,0x755dbc88dafc45acaa115ae91c8978,-0x20cc6c7161713c734ba95d3dc918da,0x7f905c4c0a3c3600ebcba9cc12d02,-0x1aba64c842e6c72a490197067828c,0x4c5fed4038d54f1f0d88ad0b28cc,-0xb7717e17917dd041319df7d5c0e,0x16be7e75a0d82ddc0267c1933d6,-0x246e2da79377af4be7558c6650,0x2dbaa40e567aae3d5717f1f90,-0x2b2fb61555ce5065d8b176e3,0x1cf35c33953999286bcac1f,-0xc9cbe3435d1c3f8f3c536,0x315b2124ab08ea501c56,-0x520e8679bd5109d747,0x1d17fd14b5be0b6b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 23 40 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 40 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 51 indices rho q0 m0 0 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 51 indices rho q0 m0 0 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x30524ac6c8c72db6fb55565000,0x63960894a02ab30501187c8fc00,-0x63b09dbb5a7632acca5331d2c000,0x40940466e9c5d325611b33ccfaa00,-0x1e6dc6e7b92ba09c2dc3607bbc1a00,0xb1d499ab0036ac3b1aea744a7d14c0,-0x34662b99bf1f2934e2a463401cf02c0,0xccc5f76a56bcb59075b856d9b436680,-0x2a46e2c29a8a196fa2c5fd7f80b4a080,0x77c886d38f4c1d14a285d1666b5bbd40,-0x1265faae4df0d2132da6a61134831cf40,0x27902c22777dc50fff72344cbec71c780,-0x4af4fcb09c015446e5ec366421c22d180,0x7dcfb42e5447ded0e4ee01bda874dab94,-0xbbe2cdefd8bf8ce7bbc344e76674d4724,0xfa7fa63c446af88752ced1e9259cbd858,-0x12aef058d61e430da8f0e1fa9345d1c098,0x13fe7cd601b487abc88d1ad887806acd70,-0x1336478712859432fd804b664a94803150,0x1096427f67f11a51084cf4745d47cfaa98,-0xcde706fd15fde08169211b4a15e0f1f98,0x8f7f8271c1130b2f21fd70bf594313961,-0x59c01125873e9aded454ece3d7854aed5,0x324d51bf096cb8c3bbed64f8cdb961eca,-0x193619bac203a2693da88c5835bd8b7ea,0xb44e478d09fbce2e6dfc9537abf76a7d,-0x47a18eea8ec0e6d4cc25bca97f1324e9,0x192f88f390581e1cfc1e324bed65b048,-0x7cbfd81ca298c6576d2f52e87de6b88,0x21ca12f36ecf406d19d8e0cc1bb5b76,-0x7f245b15a9513fcfeb70c5dca7798e,0x19b82a4f754088a86bc7a6243f35f4,-0x46c8a5a4ba1b70c10cbcb40761ab4,0xa34b174345c7f0d89d067e3d44d2,-0x1361bcced456bc7677a0e85e008a,0x1d9a81876427d29b4592d127b90,-0x23440a1a431c2938b472987950,0x1f6b8f5a2d6a3643dab4572b5,-0x13b88177c22260147420ffd9,0x7f6b412e9fc7a46f7d7e7a,-0x1c7ebdfa0945ad62ae65a,0x2a7c5846077fa23a821,-0xd254eb0133e54ddd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 23 41 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 41 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 51 indices rho q1 m1 1 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 51 indices rho q1 m1 1 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x579527884be902dba78aac71000,-0xb2313a93b510de3d56ca04ba8c00,0xb00d82d907b76733b1ecdee8a5800,-0x7087527a9a55ea9cd98bd421343400,0x344d8d59357d8c702156917fe8b5c00,-0x12d6da6dc042ed67bf0bdf71dcf84440,0x578f55e994f159e8d8213d90c8ad9240,-0x151395044d3a3a65559090d124b079800,0x44972ff3f83bda054e0e9134a9bd63000,-0xbf63d0644d146bf8d99de38fd01e23180,0x1cf0a8eae0956d880e644e7edf68e1a280,-0x3d3d82b67d6a463c052bd0bbf9b3ba4500,0x722159ccea562a260ffd29980d9df96300,-0xbc58bcb6993a97c0ed4d05241d8279c10c,0x1146c9e06934ad9f789abf305d45ca2b3fc,-0x16a00d69ccb83bd99ed1e66eab07ede7588,0x1a81b172b57c683b423499fbd41d91a1dc8,-0x1bd4fd96cd9221cdd6e97190eff7028cb00,0x1a393e289742daca20662442bc885da01e0,-0x162f92f79fab656b7c87eb0d2d6e53e54c8,0x10daea28bccd9ce7a0ce35510c68ca139c8,-0xb7e6c03b7e8eed1af7203bd5cfffd90a67,0x707353b704adfd88d93f692a97e2777e13,-0x3d8f95aec95423a1cb3cd6fcd4aacc1286,0x1e1b9a0d1f503d91e35b5ae00306fa1ee6,-0xd1e32c49e7f4e942ea6cb7c76df489a9b,0x512e3a997695f6377010f4ab2234f37cf,-0x1bc0a6f65342ff7d7eb14f5979b6a7db8,0x8575404edea36839cedb4532fc8e2c78,-0x230966ce1ddca4592febec58554b053a,0x7f8b029be91d3a7fdcf56e822de36e2,-0x18e83e6297b5be32c1875a688e322cc,0x42033ed9751306daa20f5d47912b8c,-0x923c05fb7cdeca810a861a647910e,0x109c73ce612c325390b933c272756,-0x182f08d032a8e7d0640491e4a210,0x1b537511c1d7fce2ed1ba568050,-0x16f3c62ba804d60bb8791ab633,0xd79d5022702120cfae08dfaf,-0x509f6d4c9ee331cdaf9c596,0x107735139cf7f3964da836,-0x15fe333247d6e59e8ab7,0x5efcdf0c7d5a9d39b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 23 42 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 42 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 51 indices rho q2 m2 2 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 51 indices rho q2 m2 2 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x9ebe57a70996552e1fab588cd000,0x13eef7d76c904a7e6a5b605c09dc00,-0x13716365c5487bc55187c41c01a8000,0xc44009e52d3974774868e410056ea00,-0x5a00eb3daf3c121e0ce89db7ab303a00,0x1ffa792ffb392b385fa28fd7f06a736c0,-0x92900870ea6d7b6ff1e371194b7f29cc0,0x22c716e1c1c64cc70e5a7be36fabb16c80,-0x6f887171d65169a6be56e3a2e51103d680,0x132937dc5c462309a4e4dbe95aa8ece18c0,-0x2da63e191b2b4853650b0ef8559e4c2f0c0,0x5f15e44bf50a04137ee737a66eb32be1480,-0xae5b0a1c8fd8c3ed14ad1f917170489f680,0x11afad8fd87af4084d10f3c3c2eeb534ac54,-0x19840af0fd63f06890fe79578b21cf9fc2e4,0x20d4a62b2799f04a533e5b2b953d7105d858,-0x25c4f6aafc12ccefe7d66218e8d086001898,0x26eb9b5803329370a5012231b54767e527d0,-0x23f77c48e9f1e3534eb591e15a68d24f3530,0x1dd3064f56a856bf74a68fae8cc38147a958,-0x1631324ea4f7fd82c361eebdff2cd9b36458,0xecf76d219f07840b076ba1a00d9ffffdc51,-0x8dafea063a2c6a1603bc3dd0db7cdf09585,0x4bc714191bc415741b74574f6adfa2dac6a,-0x242b7545c3cfb6ef491a76e69fa4162718a,0xf5cfcb39e3e0c04ffd86d0d753a117470d,-0x5c92eac1b9147bacf5af3c7c51b4472339,0x1ec5ecedc6dd67529867bce4be12144748,-0x8fad9e17e2b3025ef3cd099c07ca34288,0x248f74e9798d548aba16f483cacf38f16,-0x80c059d66fa9c1c85bc81d4a6caa99ae,0x18453c8c1c45afcce8ff4f9afff9e0b4,-0x3defa271a15724f4ef54c5085eb1174,0x83b895bf0b602018bef56d2583e1d2,-0xe50a47a0726e03b35e73c960cfa8a,0x13db4a7a1c5c0d1ad1b8d4e1595d0,-0x154508a92a8c2d9f9c0b6da4f590,0x10d49caef190de9983f939b6b65,-0x93c53ee2d9adec6fcd2230149,0x331c00f384ea1c7b6b55631a,-0x98585bd7730df62986aafa,0xb61cc95c1aa1395246b1,-0x2ae045e5733be3f22d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 23 43 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 43 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 51 indices rho q3 m3 3 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 51 indices rho q3 m3 3 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x11fb8fedec1607a639966907f39000,-0x23b01092aa9cf153b1f0fad7e7dec00,0x22600a101aede78b85f81d3844f6d800,-0x1568ca44f7a0bc200af00a3a9447a2400,0x9b0da2429260d3df7250f71fedde64c00,-0x365b762d9f613ccb360a58951f4712da40,0xf5bc774f02af53e8a11efd52c7e30c9040,-0x397f67a4467c7e020f125ea18cbc56d6600,0xb5c38b9128046ae72c6f77ccf23597ea600,-0x1ec4fce9fedb9a827be1c170ec44b853a400,0x483489ac4685c8a16013df62692f13daa700,-0x94153155675e75caf3163709eb841e0b0800,0x10b3cba2008961ce794d91fb09c37f21f9e00,-0x1aaab0976a76726e47a2132e5edad99d5044c,0x25d3d7d0103ddb07d007cae20948809842c3c,-0x2fd5024e28cc10e572e717fc73f0dcff49688,0x360c5c1192391a5d4c23a41b889780299b4c8,-0x36ac0f0a22ea00442eece4d4a75da973c4a20,0x31904f1b22d478c1f42c42038ded56d974580,-0x284a988a3ba1747492fa6abe7d0c1e98d3208,0x1d5eb4333801951b7288469d1841bd6af6508,-0x132fa75921c7d8b6dbc7de3a900cd08422877,0xb3834c2eec8e245b07fb0a64131ded26c463,-0x5dcf0fbe62e7da8244fbfd126b6c090009e6,0x2bb4b913fe912257ddde85ec7609cb38d446,-0x12199f40998defdf29ed73ccf20f3a0aaa8b,0x6a34c40bdc8d224ac1e92635e0131fc97ff,-0x2254ee385a1dcc66458e4fe41e71b0e96b8,0x9ba2ab4b8e967e353ff4318692c9e34d78,-0x2662b9f49397fe46f60edfa64716f27b9a,0x82c45c57dd3143f14da00a4680d5e58c2,-0x17cade4f8c5e2eaef369d09964e48c30c,0x3a73abfc665ed27d02f138a6feeda1cc,-0x7750b8d2f1acb1eb1b75bf45be5a68e,0xc66d03c453fafbe3b8b681798431d6,-0x10620d1d665a9d117fb1864356fbd0,0x10a079191f2bf7dfcd7b363ab2c10,-0xc62cc7156866b2923d1f5778683,0x658cd36381c2869362ceeb533f,-0x2074879ea007e21f27f78dbf6,0x58269839d4d5560f8e56c96,-0x5e390abb5ae49748235a7,0x13582416e50c169aecb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 23 44 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 44 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 51 indices rho q4 m4 4 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 51 indices rho q4 m4 4 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x2097f4df3be7eddd48609e5e6975000,0x3fe940eb33756f713090a7fd3ac3bc00,-0x3ccf2a1ad1352db5aeca692c42d79c000,0x25668d1a2f432bfe48cf4c8cb49dc22a00,-0x10b69eb5f3248bb5a15edcdda345bb8ba00,0x5c8668aa3854bd90bf78704c519de7d68c0,-0x19cb32096f205ab61d8d331c0dfc0ea5c6c0,0x5f3e653fb19391de7024e056f3f09b98a280,-0x128de72cc6eae948bcb0f3445dab4df231480,0x31885330b585a9da04e8bb3ba4b84dcaf1840,-0x7285584c05b80df82cdf1d7f75d0483e5f640,0xe74eb4d9e4295e38f2073c94e9265f30f1180,-0x19aed098a5e50f8c06be64cc45da9fe16fdb80,0x2859062f04142fee013929b1f2d630dd0d0514,-0x384a1ed0b01f9b7557870808830e6dceecd6a4,0x45f72b6c3affcb3c70b55473e31c56a80e8458,-0x4dab63b4e28009f62a4e9e9418efada3fbca98,0x4d23d889eba93ef1c0fa14aeb8a14c523b9f30,-0x449e853763b1665fd6bf3b5b36b7e20aa8a610,0x36b27001fc892a34692de8c1284028e1336418,-0x2710f46c2c217478fbb5371d5735120e85a918,0x18fc3b1a9634e53634b483583c52c44051d541,-0xe4abb282ff928d7329af69a938736fb8c4235,0x74c752eaa71e2a2cca314d06a1b8cc0b4da0a,-0x351d43f27b244dd371ec81908fae66371152a,0x1572ea373efe87f25a41114d3b4bbb45b029d,-0x7a915068beb58e0da4da2325e59b06883089,0x2687fc2215e97034b610c6abbe1e11e60648,-0xa99a19b10f1e10185e9b1e9a2ee6d3e6988,0x288b4ad4ce5d41e73536fd40ddc2c3e3eb6,-0x859acaca0b0d88df48d8e329ccb58195ce,0x1775cbff42dbb35d65c6663969426eb774,-0x3779f9746c4a6772ac74a17af1b4fb634,0x6caa0f496aff9b31e1914636560cd9d2,-0xacc7489201d07018d8f52162d843f8a,0xd947513fdaf24a86e696252c235c10,-0xd0cf2d53a9dd64673a6cae8de81d0,0x925587a2aeefe53101ed45d74a15,-0x45f682e22df179d73efdd9ed8b9,0x14a422ca5948da4731e3d15fba,-0x330835f629baa54e09e7f59a,0x30bc2cf744da29f41dca41,-0x8b93428e733c051cb7d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 23 45 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 45 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 51 indices rho q5 m5 5 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 51 indices rho q5 m5 5 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x3b136bd49c945f21132f1f0b1f241000,-0x727c82b4b2288f8dc49afad14de2c4c00,0x6ba14aea5e3f970c69fa053f8572835800,-0x4163d9b2a937956326ae9b4197a27751400,0x1cdb3f5104e3bb418fb34989e475f96bbc00,-0x9db550879159b742495a03b3b7d449fe8040,0x2b63d5f9b83e3aa89269cf70167a35af31e40,-0x9e11d59b81b407b4e934c75d0215c72a60400,0x1e5eaed108881182035ee374c84ac0982c8c00,-0x4fee505c724b5f6c12cf096b001e1936ff7a80,0xb61fb857430c8a9393aff01ac3429937712f80,-0x16a5e8c2b7aa575dbfb877ccd2e08ce4aa4d300,0x279e4802a4e807b6f15c1e02a9dd26b6ac37100,-0x3d41f8e046af721b58647e6f3bcc9500c4dd78c,0x5412141d249d8063b00c59a1e147fc38191447c,-0x66bdeb1a9420679b878ed1ab9949ea54e439b88,0x7013b93cb4b04fe78d9d5315b56201f90ca97c8,-0x6d511cb97dde0e243a3651533b057d65c7ea640,0x5f6faa712ae880d6504b788657a0f9dc88c6e20,-0x4a9bc57e08dbf6e61dea0cda17b3af4bafca948,0x3438e90535eade40d6eada7f7f69f90b71abe48,-0x20b47abf1ce5ec056edf09198be94d37707d287,0x124d703abe2d98b524e275a91812f8b6ee84ab3,-0x922af8d7a5e57171758a7cff81530ab9c8a346,0x40e8cfc3c2519c81f9dd2e3b788e59ef792fa6,-0x198ff57f4e3106c513e96ccf25b7155bd37b7b,0x8e44d16be3621a270fb20db5aa5fd501a5d2f,-0x2b7f3f5943787551e83aef046126c4969dbb8,0xb9e7edc44e28842d2c78841e7c87e527b278,-0x2b13099b3e59932cd5ca8e7acf3679f941fa,0x894b1a70d28a9ab47bc7408daa8513222a2,-0x1743782446245573c962f7e86807e09cb4c,0x34f0fe1e23b5a9d962a7a02cb5fa43f00c,-0x637b51123c3d23d34579ff1474fab5b0e,0x972e6f323784b611a9eca58270d7ab56,-0xb4e704edd6086b5c398546f141d6790,0xa4880b0f500b86ffc4da2292c6edd0,-0x6c65abf6375c09dbd2de95a509ad3,0x305034c3f05a00b79a99430a2ecf,-0xd2546515c4259a947252ca5456,0x1d8e2e27e85e595bdec1356f6,-0x1932fd4f4d62cfa24c47f97,0x3ee9f96f0c44f56fccfb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 23 46 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 46 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 51 indices rho q6 m6 6 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 51 indices rho q6 m6 6 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m7 : List ℤ := raw_ints% [0x0,-0x6b1333715bccec6bf2c5684428715d000,0xcd23b7b9b37801ee065d48b26f13049c00,-0xbe9ad37edbaa5ed439ff0a1671e15d90000,0x726b4740fb6468d4a5c6f279ce0b421dea00,-0x31e043812ab794f68417a0146b52773a5ba00,0x10d2cf945daa0c104b596d6afd57c24c28cac0,-0x491bb2543722b834c2f2e0fdbfadf0a29760c0,0x106d4a4050edc609ca43cf7fed87f795da26880,-0x31d0e5d735fc1b6380763ff2124d482398da280,0x814b5136c2291d43169f104ca37c07b435cc3c0,-0x12266e152ebc0199445d9ec66b9223ac6f4277c0,0x2395726f1c0d1c8e1cfd5e7f7398ee33ac9f1680,-0x3d4eb63d1c8830216eb6ddb7f96c59b890cc6880,0x5d51ca6eac9ae03019d2f8a9f50e9b157455ddd4,-0x7e04ad33ba76afd3d5438476ea5dfcb6d32cea64,0x9774745bc69310f167ede073c059cfab520f2458,-0xa263259404c6f1620bfbb8bf0599bf70d3ff6098,0x9b94c5a8b2f12998e412676b9016e39830aa2d90,-0x8554d9634e7ef34b0d08cb3b6a1786d59957f1f0,0x663f34a1cf87e0cd97f2a51fa035b4255e0d38d8,-0x46266dd71034a784ae093420af72a6b47d1fcfd8,0x2b06cd34c9af342346b25e96cf784028c3929631,-0x178f948c074c790378da2556e981e167c900b6e5,0xb7ef33619a377f477555e786fcc572b03a3c9aa,-0x4fc249399f85b583f3fd868e16cf0e4ccc982ca,0x1ea284473b78d4f7131f8b03c9d7000838f7d2d,-0xa61253ddde0b614862e160ef89c0eadc9b00d9,0x316218aaddf6820d7f1c834b44c23239a1b148,-0xccf166fb375216c22ec4c1b536054056f6c88,0x2e05e8a891e94879494b26eac0997be53d656,-0x8de080ff9e77f0cd07a2ca1bc8c26f2999ee,0x1732033f7c1ac59c4ffe3b69cdd0f91c0634,-0x32ca48557312edc75de47f31a5c7998d2f4,0x5b88c36811d6bc3dd717e555e595dbe6d2,-0x84e786ad0550b53e044ee69161ef7658a,0x97412a2adae996a897e313112ab0f450,-0x821e47f800171b20caf56554dfc0810,0x5088af3687166f18fbaeb3fb7148c5,-0x216f44307261f48db46dc7a8cf029,0x861d9001b116ef815ccf7f33e5a,-0x111f5d3742acee2e74717eea3a,0xd0670e25d18cb52080136d1,-0x1c58a084a0d23d7cd29cd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 23 47 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 47 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 51 indices rho q7 m7 7 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 51 indices rho q7 m7 7 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% []
def r8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m8 : List ℤ := raw_ints% [0x0,0xc212cd3d76636c83a805ccfb894d789000,-0x16fac4ff06a42df8a4b10bf6bc8a8785ac00,0x151ba7279b3ff5998e60ec834a41f15bdd800,-0xc85ee98b68bddbed245e67b2cd3d580330400,0x564c86dc32d6dd7c5f65d71d062504235e2c00,-0x1cc0a50dad1cef2c07b493be44379f39efd3640,0x7b608c10a29688fda97ed3c733646d604a8fc40,-0x1b5d51a6fabbcedece95f6109f0df14ab0f33200,0x51e2dff1b06f9b01afa7327e108ec442c00cc200,-0xd1a335d0fc2a5beabb8b51ee30aa6d8f0a6b7500,0x1d043dbc748928317f8500ccb3c690d6591676c00,-0x38115bac5953161531b99cfbe4564b30cf0f7f600,0x5f2a37d9f3c6723687f4882373c15a05995221c00,-0x8ea31ada675472f457019e479735520cd00905acc,0xbd92263ee9eaa5132f52852fdc529db200b94acbc,-0xe01cc1d8a3d67d403085b0cd27464130915193488,0xec39fa87412d605bb825667deb0d6f04860aafec8,-0xde5c7cca59be3b2c49797f3a887d40add91ac6f60,0xbb195e135ec09e0db1e581647be701706e02377c0,-0x8cc57e44ba3f9e0040afeaa6c85f2bf7e122b1e88,0x5eaf5c1c0fbca9fcaecae91c4cb623ef942e0f588,-0x38e309eb7bd0e52ed4a73470631275a3028da5097,0x1e7c3d42f46e0c21e51e702d80d8025317d628d03,-0xe8acfade082b87c90abac26dbc169fb93fcd82a6,0x62883de7b82d77dca2f46336750dd4677b5fe106,-0x24ea2332ea25e8d3cca4131fe8be6314aa235d6b,0xc2ee07ec0ff9d9bbf4e839c640bfeb4abc9df5f,-0x3860dbe74e1edc1164040281a18b482f84ce4b8,0xe330961d440df59dc12f7a2c02d160393a9b78,-0x31723e36be463a668a1b6808d8297519b2285a,0x936a1b5f7746e33f87051ee607785f862dc82,-0x174026363e0c35e55bdefa91ecd3180fa538c,0x30f9eea2c3bf262f716a6b80954ad071ce4c,-0x54a178c5234b3c1b2220ed1f796e875fe8e,0x755cd54612738a2461a9053de88910dfd6,-0x7efa070f751b6b4163c494f776ee71950,0x674293bb9a6076997f88b1af94fdd590,-0x3bffc6ea59650d2f2e89f4e3d13fb23,0x172f02a8d00d67aedb171e64f33e5f,-0x559c5f8a8238aa7a5c6debfe82b6,0x9ec0aac28620833b1bf1c12756,-0x6baec0d2a117208e5bee3887,0xcc41d561cceae72395e2b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 23 48 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 48 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 51 indices rho q8 m8 8 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 51 indices rho q8 m8 8 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1]
def r9 : List ℤ := raw_ints% [-0x27adf6cab58d8a06b4e00000,-0x3bfb532cd12c24514e960000,-0x2af6444d607350a319d50000,-0x136753c45a4d01be70f42800,-0x6342e0e8e8952178e2b2a00,-0x17e898b06d696ea89172e80,-0x481e3fcefa8dc60bd1f860,-0xae9f2c3848ab8d27089d0,-0x1595507c49ffde17070f0,-0x23482641398fd11e1ce0,-0x30101f3db60286860a6,-0x36d756f2ca3dcdf871,-0x348b8ba8dd4ce7ef4,-0x2a4819a7478015ea,-0x1c82a3dadb7c852,-0x1008510fa7ace7,-0x775cd08a37c0,-0x2d6c77becb3,-0xde6083310,-0x355b5338,-0x9a8c00,-0x13b23,-0x174]
def m9 : List ℤ := raw_ints% [0x0,-0x15fc213ff669434aea08a8387e8dc6a85000,0x293289207754d963daf3bc75a0287da247c00,-0x256bb0ff1e4a2d7c1e96eec077dd6b76d04000,0x15f2b060824db13a6e187748c9c4887812a2a00,-0x957a5e1001c7a4ef72d0c8cb5880bf8ed0b3a00,0x31346a580ca315a7df9af23ed09bc16a93f5dcc0,-0xd089dab875ca5f4756dbcc4f5523dd5054b66ac0,0x2dab0cd8ebede5c53d342dc593d473dd66b39be80,-0x86e1f4b3abd1a7d99269aa4753aebeb4b2d8f8080,0x154b2de3ecf42d81312d963a808dcc667fef6f3b40,-0x2e8222080b4bc686df55276d65aae625f224a83540,0x5897be68f34a2ae43624b3467f72f7f2b5917d0380,-0x942c1061ae43ac1b8fe854b019fdc78a24d84e1d80,0xdabc5c318c45d1edaa5d24f947c69f81aa805dd694,-0x11e2d67ee33ee29a7d696b45ca5763977c45856fe24,0x14cddac036b2d29bc6589fa99a6f29ea1024ed6b858,-0x158fff1012a0ae19ee502b95a74eb4dac8b2224da98,0x13f209eda67c61e3840bdeff3ab96351c035da4baf0,-0x107b169d3eaa957af913bff74cc17be379b583dc8d0,0xc2b116feae699c19e7c91a05c89efa406184bb7f98,-0x8067626ff30c9f580f07c4346ec3c7716f7b6ff898,0x4b943a6dd8440898eeab96df1e7eadf590904a6721,-0x27a49ffdae9b7b658e1271fb2fb0d0c805fc80b395,0x127d9b42e1dfa99ecdcae114d2966e61115e13034a,-0x7a5d731ba6fbae6e6acd86d8517160384af00da6a,0x2cb83db9b377e365b5e4b445b56aa5027f88ab6bd,-0xe60a89af584afc2826a27fa6309ad122eaedc429,0x40b6fd1ac2ebae34ae688d4224b77fd02d0b9848,-0xfd38ca9c626963b94efe3d7c84ffbfe53ed0b88,0x35692b2347d6e3d169278c982a0fa96b31b05f6,-0x99fb2f268dab1f22fb85103cd935930141a60e,0x176d22251c3e969c92445bb651046ebd04dcf4,-0x2f761b463e5c18852f6ad09ff3285afcba7b4,0x4e9d2b23550353f094502c592042f70af0d2,-0x6815d13fccf2996f8568348fd6b62127c8a,0x6b0188428c03379a5399ae172556975690,-0x5236e418b566b0fc83529c2042eee2850,0x2cd0f8e189f031123682d2e46ac8cf75,-0x101ac62d2d20b33e7565110ae378799,0x36b36a6f6caeae0784e830632e6fa,-0x5c020a4c7e33e6b890e679328da,0x379ead2e60404806ab71f1c61,-0x5bf3a281a0d91f4cb15d1d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 23 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 51 indices rho q9 m9 9 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 51 indices rho q9 m9 9 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x174,0x1]
def r10 : List ℤ := raw_ints% [0x39a8ca9e8fd1ac91bed5800000,0x570186e6553e973c1f7d180000,0x3e31dfed43566508b03aee0000,0x1c072f7505d773381908f52000,0x8f06b9962c53e487c25c4e000,0x225abaff76149fab7a7846800,0x674d6b2dbd3f6cdea405bd00,0xf93d6844d9f06cbbfb649e0,0x1eae59c8633f232c4f392f0,0x31eb828f0304fdfe518490,0x43a2eb0198e2ae68e5458,0x4cafe864f281b263378e,0x48ed518234f3695241f,0x3a280c8c868a2a7854,0x26c9547f9be10cbbe,0x1583eb8d8b7f5d3a,0x9d6a8e3c7c5c39,0x3a8bd29cb4eb0,0x115b83b9b055,0x3fa41c39fc,0xab6a2d58,0x133e048,0x11e75]
def m10 : List ℤ := raw_ints% [0x0,0x27d8fc43ee9ec9f7c82fb0e66560f81111000,-0x49e09faac00d84a311a2bd706c88d9b6220c00,0x425ff08f407958efa5431f24a887a515de65800,-0x267efb364f1753abbcd9a31d8f873c2cc82ff400,0x1032e0c175dec8ef7a7c325d0b8e80db017659c00,-0x545078cdce98ef6f53fdbe04f8b84451693d87c40,0x161079f9176f62708e3761b9d607db0568cb4eaa40,-0x4c5a2d926d7f7f88e6b8af0ba689e2b0ce31167000,0xdea25b0bdaf912224272045c455fbf20542b2dc800,-0x22af82fc2401447a5baf74345082da73c91ea167380,0x4abbe1476db7016c69b943117eaf52279362ba3fc80,-0x8c5fdf9286912e06ddfb869a87055ed55a6e89bf100,0xe766557ae4fb547c306bb54c461a6999128f19a5f00,-0x150858306a10daa44769ae290263f6220156d274ae0c,0x1b1831ac907232a3fc7d326be727349f65faeb95c4fc,-0x1f036c65196ef78d1537b678e5fc2572dbc955730188,0x1f9d1d841f0093445f50b4e011078d81e9e5f38c49c8,-0x1cbe0d2305e601f21aec80c854cfa508c9214641bd80,0x1753c27b1035cb06efa4ef2ad449418d7fd300cdaa60,-0x10e77c83123a4062066fd55e2a877d5ecc7b0b4c31c8,0xaef00cac9c809bd53ee970e40d275f3222007c13ac8,-0x64e4ed8634343b9debb8e191e9acc28a56a72308aa7,0x33ce5ad06cf0569d03673b2494b4c54acbc61878353,-0x17a1468bf4489e04cef9393526be0399e6f024e1806,0x98bf1aa4cb9b12e23e9f5a96f9294f748c29064866,-0x36757b1949b115444d5b999812be56a8d36072105b,0x110e9fafa99ffb3ed29213a7142f3e78e772b1be8f,-0x4aadcf1921ca3eaee19b316749a9066c7efe4b1b8,0x11bbc0a621e6ae5ed5d740af026037f3c4209e878,-0x39ff1894fdfbb669848e933ffa6dc959b8565eba,0xa1ab8789fb4be503513370ae2ac91c58b9f1662,-0x17b8b4a36c2edc3cc282ec5b9164bd46ded9bcc,0x2e36af846eb72fc779eabd39fcf8cd4c9c1c8c,-0x495a8c7054c0ede551a3512ae6470bbbae90e,0x5cb0f3ecd2e3dc4135d5047b2eff277a1756,-0x5a81b432ae11af20e574c24261b36607110,0x41a91d17c69506dd028d6f4d628e379350,-0x218e6f1673bb2cee0fcb1de7ea71bef73,0xb349e238038fc86fc75a9ff5fed19ef,-0x22faf28f7bd047a20506922a931716,0x35548b97ed796fb2bd69ed453db6,-0x1cb7c4667d320dac16a5635077,0x2960b6d4adebc6bd77e925b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 23 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 51 indices rho q10 m10 10 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 51 indices rho q10 m10 10 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x11e75,-0x174,0x1]
def r11 : List ℤ := raw_ints% [-0x2c667c38417919e39322ea600000,-0x42e487fe769b1812dd35a90e0000,-0x2fbbc154c2c8aa32d54747410000,-0x15781beeb85bf6bf858a29584800,-0x6d51a1ddadeb7059d7f29b11200,-0x1a31c1294cb176eb5dc67c66080,-0x4e8d156c6e219c120052ed5be0,-0xbcf0cb733b14e74b3435f9f10,-0x172d6fc05e9fbba17e6d973d0,-0x258fd519d3ea08277211df70,-0x32a9421c485ab19155c1b4e,-0x392374dde159584e0df24d,-0x3600eb472c43aa0d34a76,-0x2ac10a8478629e706523,-0x1c4479faa311253aec6,-0xf840914ed587a518d,-0x700c530bff8d7ace,-0x28fd48b9981c483,-0xbe49fbefe4882,-0x2a5a00f98fd6,-0x6d717b1908,-0xb8ac0f2a,-0x9b60ee]
def m11 : List ℤ := raw_ints% [0x0,-0x4839493b207fce111ad670a197bfc19eeed000,0x8483eddd51af06fc3456a91b6aa7191a1db5c00,-0x75caf3ecea0cf388710a92d8a4352aeca36f8000,0x4392a4f942f27888f2ecd776a42afd3290886ea00,-0x1c1da8436a1daa226a952ff8302df0cf9be8813a00,0x90a936a77df7289a6f25de3a8e1494aa70cf011ec0,-0x2568cdcbbed6a8019c50a158ac793c033a5fb0b64c0,0x7fe13a1a5030ce21f6d6d52e6e10fbec3e42c512480,-0x17037f6ff10f99f8543fd080811bb58faebd5e232e80,0x38a0bffde7404720c1242b35b09cff72c39c82de1ec0,-0x7863dfcba54e500652a3eac74ef05d21fed9223dcec0,0xdf080ee0d9db8cc783a31e2d82356717e79475631880,-0x16a72e4789f6585caeaa5a95fc9a453e0f1dfd341ba80,0x20762efd0cacde13bacd15121f3843c4183885ea8cf54,-0x292f0fc739145621a645885de9f60639d8f7f57cef1e4,0x2e66758e44dbe0d1cc26eede6483350743b9c6e0da058,-0x2e87209764557e4e24442f650fb43168a56f9d9cd9898,0x2996023492fc9fbdead754b5be1e240991dcfa461cf50,-0x212822d1814078be1d64b6cd6887f6a9daeae4ba572b0,0x17962fda00451bb91063049d05a066cd027b05b33c858,-0xef6bd32d2c210040637b78d99261fbb7e06272d3d358,0x87529bdf3debedc1f363a084f6a023c85befa681e011,-0x4407532125104fa34030a4b37a76ccb3362e004ed045,0x1e58f5b66f217f66e76c099a12feed2c90533050c6ea,-0xbfa2a2ec37bbbb42e601fdb870a1ff44cc21b5cbc0a,0x42a8ce8ec465999be961dcd64e4cf05b758bbe1af4d,-0x1457415c199575d635b90f687332db79080d9b4ba79,0x569ffb33415cabf2eb62a4503c42d520d762bbdb48,-0x13f91d4c1f2c5670f6409a895737558c8245352688,0x3f4c50fd37538e3a0ef028af3f7e8ad450b901d96,-0xaa97ef8d7a9d55183445d304202ff5c62cf80a2e,0x18230fbf996ee363b308771a0b67b64307bbdbb4,-0x2d34f9939f7bef67f0fe1f278bc3d500fe89474,0x44bdf20cd8d36cffc79f51403f8ba84d653fd2,-0x52def30e8d29aea444057757c5cb3b3c80c8a,0x4cd16c951faa4e8c5bfeb8cd8edba9ae12d0,-0x3497bc01aa3c02a80d836b632a8247a1290,0x192e92d754c726f2d33ff94f6ed4039625,-0x7cef8e4c41819f9b39a9b01549405709,0x1662b52209de95dd2346c92bd45199a,-0x1ee9b9cef2ce08f78c8e260cd517a,0xed275416ebd453308216760af1,-0x129cccf51581b39aae66b56d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 23 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 51 indices rho q11 m11 11 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 51 indices rho q11 m11 11 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x9b60ee,0x11e75,-0x174,0x1]
def r12 : List ℤ := raw_ints% [0x18155a8d03613c6f6859b028400000,0x243b7ae2c2865be7ff42be65140000,0x19d07b1d6b7351a41fe8133af80000,0xb972cc0076c40385a97f582bc3000,0x3ae791ca9dbc4bff6b5cea088c400,0xe15904474adf7d13a4fe22cc2900,0x2a2282f3c9d9219484d2b4b288c0,0x6513ac77dd555899ee0f650c380,0xc5ca2fecd02234fcf2ded36010,0x13f73408e3f651554349996470,0x1ad2f853742487197c7b83ae4,0x1e1e914009cf549c1b70dbc0,0x1c522b6f7b136de47bc678b,0x16499b2c7c4d2119edeff6,0xea1d40c25b3d63075ed9,0x7f6d37b245658c1bacc,0x38ee5b115b94221a23,0x14911ae6fbdd56fda,0x5dfb8a63d463289,0x147e78fda4d450,0x3388307c2002,0x53b42080e4,0x429ab1ba]
def m12 : List ℤ := raw_ints% [0x0,0x82e7d4bb2ae7a57f00a4ac24e30b8ef010d9000,-0xedc184f2d9d4a82d3e84899113b136df55d96c00,0xd1261a89c38a20c11d7f775d67f654bb38cdcd800,-0x76b3c8e4efad4f1cca93e65cea7801cd107ed7e400,0x30d97d0649415e425014467193aef37fe39a55e0c00,-0xf88350aa14ad2996f4e9c3a066e77dec9e909a1d240,0x3f85a5e0b76f671cdd5e2c92315c1c5d0b6ab9efa840,-0xd68e9596a36e4e519c53c007cbd52e627f1dbf383e00,0x26237cc5c0d845c15829d2569c278b4415f30208a1e00,-0x5ca85766d2901c7bb525e992642a5dd0cc27725545600,0xc26aca309e0aa1e939012719152a0859acf3cac514100,-0x16350d65b4a0dad06c9a30e7bccc17ff870df6a3700400,0x239602184d39511ae3f4c8a72a462aaca9afca553e7a00,-0x324242e146762d836615046d1e0714491e284cd069714c,0x3ecf615c4a7a640b1769520b79c86e5a9e672c0a79ad3c,-0x45ab38916446868acc499e1788a8660b78aa11ca536288,0x44bc69f461bb7e38d27cac692c67fb3409385f4ce958c8,-0x3c683a2bcac901adac70694b30b74d964b3e851f8968a0,0x2f52df441f67f53d5c0ac953572f2a2d7f99e3255afe00,-0x210d849fe06b2b216b59fcb246d80bb846306c3e733308,0x149240c5f2f4c1759c6c53c823a56d165dcf06bd289e08,-0xb6569911241b245f2a3fe697f72c1d9ff28c9bcff08b7,0x59c1717784d765e911a82fd6b60ced73ed6780ed5d5a3,-0x272a0d5b6cf2530604391302c189686cace86a2b68366,0xf19ddb80be59ed35fdb21e176573eebfbf0c9e9745c6,-0x5200cb72b43a4e75ec4d0383d8cdb52122efda4f544b,0x18612bbac4b361f28de29faf0dc7f2089d9d8f98babf,-0x64fde55e56e6f81b934308b61f7fe300477795562b8,0x169bf81fa3350562dfa335087460ebec2d619d43978,-0x456dba096642944cce4d30134523ce636918ae551a,0xb4e2cc2feac15ffb792c9bafd8a49a3915ce80042,-0x18acd52bedbfa77f46ba078fd7de353835518840c,0x2c6b79391610014c2d26146d58426bc702afbacc,-0x40b046ca16953edd878ce81de50eadd934db28e,0x4a5f0a5a9ec648f7b5535f286dda02515209d6,-0x416a6200f4de2892092170691b48151013ed0,0x2a3dbaeb65b2853b6c8067cb75d3dde8b710,-0x12efd47333c089e20d930cfa4afa58e5fc3,0x572dce4264ed312f8ccf6fc2471f4497f,-0xe55a90bd252c841b1237180f451b176,0x11eb2e9c2a97de576bc6684573fa16,-0x7a5aec60d96361195723a56b767,0x85e7af14744072b35262998b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 23 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 51 indices rho q12 m12 12 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 51 indices rho q12 m12 12 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r13 : List ℤ := raw_ints% [-0xa52d3d2d4c72b8987ef7aae4ac00000,-0xf82f4eb62fc3fdddef232f4a6bc0000,-0xb093819a2ce59b475508cc0a4ae0000,-0x4f28cbe6ff8588d5bb6ed93b6151000,-0x1919c654b3b40a5bdfffd3ee4aa5400,-0x5fd8250bc4a2f7d6b98b50fa758500,-0x11e207b2c7e8de792c896aca3cacc0,-0x2acc6632cd336aa11aa30877a6860,-0x53875e1e91d8f4c9c33563d73ae0,-0x86821926c227668d4b001c47ab0,-0xb41bfde371d1ccc23f2ceb9a2c,-0xc9778826a825c20e2c686b236,-0xbc9d15a34f9d9d1778c9e688,-0x93b00a02993c0e7e75fee19,-0x6064eed425dd837da852de,-0x341b7c78624bf381242ed,-0x17173b07e331da26b1c4,-0x84284425a527933515,-0x254a3c42728de68aa,-0x80252958bd772fd,-0x13bff93f241ff8,-0x1f430f553022,-0x18020ae9e8]
def m13 : List ℤ := raw_ints% [0x0,-0xed4431933dc3dbf6312a7802db84f3131e895000,0x1aaaef32728ee6cf938b549b1dfdd4fdccb9a13c00,-0x1738b3a914c01bfbc8b0f9d88ccd9030406ee46c000,0xd0acfc0b6bd971798ba87e8221d98fe2f0aa2942a00,-0x54f533bc4f1b3cc3bdce8899baeedcf006c45857ba00,0x1ab736faa074b93c6a9cb1d678ca260e2db2fa52b10c0,-0x6c05ba13fc09159d3412b26ad4459821de6433610cec0,0x1689b2041df5a3a0a4befb43e062823bf4836ab37d1a80,-0x3f54038be8518deac9f847d44586a9343f0c040b9b2c80,0x97f1dcce0f15dc729c895b9a8a44207707a763f44c0e40,-0x13ab9e988281fc63be22377d5d75727f1cc7571a84c6440,0x23790ba042be443470794169b286329207bb53ecfc31580,-0x3810426bab10fa7b961a67ec51c591c980478bc17e8ff80,0x4e0def51ff89707447076f85a16a80cf763b3f39de8a814,-0x601c0eb5302e6b70b51346a4ebabadef6c3ce56ec9b25a4,0x68f940f5ec2b1f6550c04626a492aca41b9a3c5c53cbc58,-0x65ebccf9406493c41b09ea18d6a8db4a5e15a8d1deffa98,0x5816aeb4442e0a14033451a7c340e9d002a435d5c12b2b0,-0x43d1b75f5002b9ab873daacfc9ffc47bbed8d067d595790,0x2e83c0cd0dcb1607773a8f3b150a41de3a5e2e25fc70318,-0x1c6790158a39250b0ddb00ff7391a7a238b6a809a645018,0xf6cded04a106df657455633b31f9c4fe562147e9901901,-0x76f9757b02fd170d0f800dae27fa4b985993c8543dc4f5,0x32c8a5951783f40de51057a84eb509b666391ef597348a,-0x1321d2ab44b4f69b8dbc5e181b5cc3e9f3ff596f19c7aa,0x655fffe31805903313d388761729eb94b8bb8d69fe6dd,-0x1d5d70347fadbfd947c21c82871a5d038f2427cf5e3c9,0x76533ef4bc64bb7d4cf7b1bca672d13d92181ab2da48,-0x19b82a5d610d9d907b460d4e697ed4b162d142621d88,0x4c85b66ac5b36c886b2aa02a1375967a4ad38236d36,-0xc0b4da59f77814136d7b9b599519957d17dcd2d64e,0x195714392d7e08b56a67d44002524e28930dc8e274,-0x2bd5b00b0b8a07171d3ddae0739a196894b4ff934,0x3d1e33c364d5db9ab4eea0a12c5dc00ebfaadbd2,-0x42fc14d172c70e5aeeb024fa94b54a73af63d8a,0x37e16a0f89b273f888485e6b31c0e03f599910,-0x2203b0f1be03b1a26673693dc9fc6614236d0,0xe449cd31e9dc98aa909b27fc14d8aa0d4d5,-0x3ce84e850b18c49b3286b89b3b99d0b679,0x92f203d6e3a419f2706b2de3a972f63a,-0xa62d30b8f02bc2e1b5f6299af0041a,0x3f1a5309cdb7607620237b659281,-0x3c300fb61803dbb6157b282bd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 23 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 51 indices rho q13 m13 13 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 51 indices rho q13 m13 13 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r14 : List ℤ := raw_ints% [0x3b8a02ffb89e14a2ec1920173cb000000,0x595b77da67b35eb16a0f9ad6373300000,0x3f7eb33be00f24d77567dffaf9f4c0000,0x1c6ce44ba43ab914d9c456e7d80fe4000,0x8ffe70aff3cafa958486bc2e0e430000,0x224e5605543b061e583c235842aa5000,0x6639125eeb82fb3f8e394104aa2f200,0xf42305a379bcacf09d6a955b4e87c0,0x1db5f3ba2b5ca5b3f5abd966966120,0x2fb84495978d60dc968db687ad020,0x3fb63016c3cf5d1bf3a0af4631c0,0x470842e12805468900637828d3c,0x42408e43b7e30a6570e6d732ea,0x33a7bafb1abf9571157a69e08,0x218c98ef16fa4918e5b9b337,0x120836a46cdfbe18bb4513a,0x7efef9a17bf58f7012753,0x2d1146d2e9bbc1f2ef1c,0xc9855ce839e229eafb,0x2ac70bdbd96ec6a6e,0x67f443f81a63a23,0xa1800c5e30e98,0x7903e51150e]
def m14 : List ℤ := raw_ints% [0x0,0x1ae0b99dadff2feae391cf9852de0f892a758e1000,-0x2fded708936e2dec857b97231830e5276310743cc00,0x2945b95e27c0b7e556b3b3a5b7aa1b0b2e3848015800,-0x16f1e39885b4c9a06213970f2841ddf61030eca16d400,0x93e6cc4a0c349faca6491b629159d9df48d419a137c00,-0x2e02188269cc45db526b28a2fb393a8cb44a82805eb840,0xb7f762686e9a756251f48c8b263a93b5c5ec7d8e277640,-0x25f1a1890915a9e5993a70eff90e1808e9f945d7e011c00,0x695bbedc3b077823dc2cec40b3bcc931d298bd989984400,-0xf9b505339b8be587adc87fbb51554dfe9aaf9a0282dfc80,0x1feb48749f6758368762ac3c9bc952da93f8e430ad6d9980,-0x38cfa35bc8677ccfd13f191bd6beed8cdc66b0e962006f00,0x5893446e37e867805f935e1d8a4e2d5544cde4db44ecad00,-0x79979d02cace4b58c42b8b259de680133165b9509354448c,0x938ae1f6dc2eacf489d9365cf5f88f00b19a1e35b915857c,-0x9eb768ff796f791514a2f9a43274e0d0a9603bf1593ab788,0x97adffd342d459dea1d1a5ad7911f663b9de9529bf700bc8,-0x80f2ac6fcbe636cc217364b1fae1d156291c4141b9b288c0,0x6194bc2c3fe92d0a9076451d208b8b019eec080fcd946aa0,-0x41bb8b8809c2c9dc55d1f0b5a638ff7c785fa141a2fdb248,0x2763e5869ffbfca0978341879627ef0ce4c5b682bc232f48,-0x14f8da3be2b8a55ce9b7fa863d9ed8f374a0bb0e669312c7,0x9e6d7cfdb85eb67a1a88ec0240198dea43790e65d142bf3,-0x4228b75d4639e2fe199424922e52ac3af84caa99199a4c6,0x185acf85c78f60e019056ff2a5ab5862ff87aa78535b926,-0x7ded5caae2d109d89472f5767f54223262110148a5693b,0x238a96821ec42a9e543fe6475e03eac86cca8bfbda93ef,-0x8b4e1d8f0cc2058f3318bc6860040c02e6446c4fe97b8,0x1d65df6d7c658cadce1be934c191dbdd546cf4be22e78,-0x54bd37f63096aa8cfc64dbae7142f872d5b6331afb7a,0xce3e157105c30d58e83b5e5ecbdf6f7054c6546ca22,-0x1a234a5a9d5c3e38022f0a18ac9c95b0217b8bb6c4c,0x2b6ffafad38d2c6df56cb032b757df9e01452c890c,-0x39f7741fc4e5fefdc21244548894e4614df43330e,0x3c8a45980d002401c12d52988d84558521ba6f56,-0x2fe09f84ae6d909304e3c3c42a5a84eb2fa9290,0x1b74c3eecbb2adbf8d77a15500379fafb0d0d0,-0xac4fbd3159b1ecdb8e0416559b675288f413,0x2a999f9eda12795940cfc786e4967d5550f,-0x5e307984fcfec8fa1e0b49861dc67b1d6,0x604f988098c4ed76a3f21250d57bc76,-0x20882a4219f34d26e2b9db7b25d57,0x1b0b21b2a094d626438ea3a3bb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 23 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 51 indices rho q14 m14 14 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 51 indices rho q14 m14 14 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r15 : List ℤ := raw_ints% [-0x12c1d4310109d41abe8b3fd941444400000,-0x1c1f29eb08b65597612caf4d7e6cf340000,-0x13f5b224b81d3c56d85799edf0b6f760000,-0x8eca3774c07defcbadcde816ef3d563000,-0x2d2550a388629352a747490d4a19d00c00,-0xabd4ed92c69e362b3c24f677d0e520b00,-0x1ff27fab2e75332afbd85ca0b72912540,-0x4c2852de629491dcb241374a6da2a760,-0x93fc41513b0238b9b86cfb90e0b5560,-0xed24443916b2a13c3519b0e44d9320,-0x13bcd5acdb7adc571c718625ae16f4,-0x15f13aafb099dfa002e56f0ab676e,-0x14663d7bc2e0ac320ae759f98b1c,-0xfd8afe97d825e8708f250fcec2,-0xa3fb2cd78f34345c84ba2bc34,-0x57b633315acaa321aa679a3b,-0x266478e756a1ddfe0dc1776,-0xd89067240ad0876aafcd5,-0x3c0ddf43f64ed9ab9530,-0xca11be4436774401b7,-0x1e57c36c06c8ca3ea,-0x2e79fd754dfef09,-0x22344013cfe0c]
def m15 : List ℤ := raw_ints% [0x0,-0x30b7506dcb5e86d9bc78484416327c289cf5117d000,0x55f3af5a89db3f80338a5a11030d10c74b8dd2ae1c00,-0x4963f6794951a5d3d9a060f4ca84a2c004b9cf5e60000,0x28654fb0e569abcb73627472cb4de417a6653fd1d1ea00,-0x101ba78a149c5eb781ba6b0340d47bd0ee5e9ab5a5eba00,0x4f54033d537d9cebf8c59bf81d78ab14440b550046032c0,-0x139c0f899a0cded049cc94375a682fbbb9ee18f2003528c0,0x3ffce4f2631ae4a4d6bbdb2679892304adf5a6f5073e2080,-0xaf9e2a48027adee03f14c2bf578e9065a703fdcc035dfa80,0x19b3f1c331632867c76e00a7a1099240b88b8d132876aa9c0,-0x33eacb8a51f39d04b3ca4381638eb9fdf823c091c1c9615c0,0x5b3843b1c49f8caa3a3b1e241363babe2b2bcc465ecf6ba80,-0x8c54fc3019fee90f347fe281656a52e2780ac66d3eba3ac80,0xbdfbeba283f8873e4193cbe02487f42a613f98646eeae40d4,-0xe339fb24b2bd8e32d70c3a6a6500efcf9c88ebb849026f964,0xf0ca81d249c70b330a39fa86c4c118f4efc0a627bcbd5ec58,-0xe28adab2026f3b8dfcbdf4c9cbf2900cef06875ec7ac16098,0xbd78f158ba665c6de8d5e372ea81f1a2d14f90e04a63f6d10,-0x8cf5266f0e4edeb39ddce47172e09669964ef5e3756831f70,0x5d45a363631429c363d09f0b9b7ae3b933cb1c6865a9e1fd8,-0x36db646592ee2e8071a784943982fd91812dc9cf5cdc1ded8,0x1ca37437b57690e729d28d368cf1113135cd196829790e9f1,-0xd3e9d2b7800eb73c4c7b924b09a4c77440254a1b990c89a5,0x5695e1dbdfb4ff4955385d841a46b852e7ffce463239ec2a,-0x1f25d64f8b974060048083d03ac34e9e1cca069f24969d4a,0x9d2a0dbb4a8e8170a7be9f6906e4fd7aba71d1413a65d6d,-0x2b3889ef4172cc163c2fc668e815fd90f86c1972007c019,0xa4c804aac0defa399a211cf3b7539dceed5788e50ef548,-0x21c295d664b23b669981db23e34f02dfd13795a2ad5088,0x5e450c98ca29ffa1eabb04276c5abdfe48ae1879fc4d6,-0xddb6ccae7adfedb62d1224d52bc6818970d296d79a6e,0x1b136607c921ca97aa08d0db8dc8570474471199d134,-0x2b377350002bc3fa587931a3cec608ac1971adf35f4,0x372e4a8b56c8ed8951e9480313ae11cabfae0f8cd2,-0x36e55bdf8ac530736a6477c89b7c183d8915d778a,0x2922dbdf00eb319e8cbea0952de4cf00132c5950,-0x16366684686fa9a60a5da0a787fff39b9388510,0x82463bf5ce38bf67ec1c47e7a7d6b3ef58385,-0x1dd33cce2b7a50769aded6fb9dfb11153de9,0x3c65745f559828801b6940f8244b851cda,-0x37cfed18b11ab44e68dbe2c7c3b7e0ba,0x10c3d966c314e37869e39c607e4311,-0xc2599ee297547838e8ba07150d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 23 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 51 indices rho q15 m15 15 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 51 indices rho q15 m15 15 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r16 : List ℤ := raw_ints% [0x54d340b9d1e2c0c1ca9bfd5c6446ba800000,0x7f0dd48210891bb244bb1c51ccdc3ec80000,0x5a15aaf1fbb749677d1ca95ca64bbcc80000,0x283b9464886587bd2a45031e37557babe000,0xcb45a15903db30ee2f67343c682185bc800,0x304a031ceaf58e6bac13087cc56b9692200,0x8f6e7be054d5c0a8ca540b6e346a74d980,0x15559fef10d895bd0886d3e5943031b080,0x2961418fc6b298aad624544d51bf0c3e0,0x422cc4fe23b3e854d7dd012c44844520,0x57ecf3011a7963f5bd0d5d7dd63a8a8,0x617fda92eb608a250442553d829858,0x5a62e60c4986b9ad467272cf4c202,0x45fd0cafd6fbf8eff75e95ff809c,0x2d1a070a06fee3e8c1501db9696,0x180654b10f7ea3e5d86dfebec0,0xa774d4042b803db5ba78e8a5,0x3ab65e6769961a641eb3c1a,0x102d38f979bf58c3855123,0x36048cb5a1d4246aee44,0x809a1aae22604343b9,0xc2ce40319ed7d2ce,0x8d6822abc2e85f]
def m16 : List ℤ := raw_ints% [0x0,0x584c41c7009b546aa59a02fb683b81099c7c2fb29000,-0x9a5d4ea3577b988e8038dd794a2374ed0ef10ddb92c00,0x8290bc48d52b138d7e42f3859d2c711ab03a318e33d800,-0x472b80bee9b5d4bb1caafbd6968df56ac7344d48a18c400,0x1c189763cf3aa930f55d5dec0d0afdc12268dfcf7fd1ec00,-0x88f107e294f5d26239283dfdd8c2f2147c621a29d2b8ae40,0x217dd9538d9b56b792c03a1f5a00a80c67c9922f892759440,-0x6c1609621e29b5c6b6b3ef6e5f6db8af66e2c4323f57d8a00,0x12547c3569960fb4b9722ae45058ed06da84aa1140e352ba00,-0x2a6b65349e8a9b9806edcfff915bb54fb40c562f9e83414700,0x54a40872b6ffddafa4b556696fce21a66fd6c730553ebc6600,-0x92d73e41cdda45528bebf50f791d3240a3d90608a808c37200,0xdef17cc2050fa99fcb25c27b5d781a89d7eb28a94625393800,-0x129b8f68e07a26776a32ddf7fea772ae66f91a7e5467f83c7cc,0x15f0d2f207b707c0e1557d34117cf8aaaec5874de1508d76dbc,-0x16e885e5e2cb50cc0855c1a302c1320abdf1784bcdb9dec6088,0x1538d435e80cf1ea339170d5f45b5f65246e1f60f0a736142c8,-0x11770aaa447e295508d063e08e254fc476b91041d63010e75e0,0xcc681f0bb2dcf97dc7cd23e5fb446726c280473412e9912840,-0x84e24b9f4bf0b72645c596d4f0b0707341523c0796e04fbf88,0x4cb7620556ee01c2cbde699a9cd1a98ec7d16249c8983a7e88,-0x2746a157227a8c0d86623b642db7642852ea3ab8a0181b30d7,0x11cb572b08925d18b69cdeda2dd991f423fe06f4ba6cc66e43,-0x71d468641cacd3e6543db0ea0b422eb0245339bd9bad35c26,0x2804a1b6e336c933213cc11548630a0ebe648260c34928286,-0xc50ea502e5f3cc287956755d3339a76a61b29b8c53730f2b,0x34cdbb4e2f839be63293110d4539ade6ef1fe8027a438a1f,-0xc3d171bf14b44f7ef3fe510e0ca6248ef1dff4e5898f0b8,0x26f25f9d5673932b816bad06354771275026edb12776778,-0x6957730e4282f4862c8932d609a88cfcffafe07d72c1da,0xef60eec619d51769141b6edf89b4a96ceed7973e22402,-0x1c29cbe5322be7b42fdca62e34a92ae7f348057edb48c,0x2b29d5a3b9bfad828c704c3fdaac657b1caf1e93674c,-0x34b711502e6046020a056d6cd19e365043b3c15828e,0x31ef36314883bb4a25abf53b3edf3266471bfe3fd6,-0x237036b2766a68876c94cf1cff3b8f4acb7e7fc50,0x120225bba0528693a42af2c226bafb165bc4f090,-0x62a4493eac0a528b429b700132d7b70bad9463,0x14e654938f10a7904630507a6a64aa98d049f,-0x26bd40e6bfe4c3cb55625dcbdba0fc77836,0x2056a086963934a9ac170edf71090e4d6,-0x8a2ee65252e0c7e93e6fcdc4073247,0x5743bffd3d7499ac1b8dacae0eb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 23 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 51 indices rho q16 m16 16 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 51 indices rho q16 m16 16 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r17 : List ℤ := raw_ints% [-0x15eaf4f9a2895570aa17f5be42fe281f200000,-0x20ccffc85f2fd0f3f7d3a2d7f684c95f2a0000,-0x173c0fa763c5ae878f841d33b1c97d5f430000,-0xa5db812f970546dcc38c4633d957bc212d800,-0x34507d36d95039e2aa2dcd2d8be033868b600,-0xc699032c9c50d5757fdcd2e9536486627980,-0x24d15f0184fd05d654d314927da44b5909a0,-0x577dcbed3ebbca3469c7efafe0e09d2cab0,-0xa96aaea860e77140ab331d007644c1b890,-0x10e7030fbbeb59be4884dfd8e84a26f340,-0x1669a1f42f98ff1d25adb29d5719a087a,-0x18cc1a9c5f82ec1ab3461dec3beb6847,-0x16ee3e11598cb9e5562874722b9d1b4,-0x11b4bac4bbae7b33a9500a65de8bc4,-0xb5fbc639cabc87c6f64de4e6beb2,-0x60979c1f802f95ad7eb7ef3f44b,-0x29e85823c75e8e1b83748d9158,-0xe9feb8b0b5292d667b45558f,-0x401f6b8b85aec1ab5b6ab7c,-0xd4c53e235c6ae1ed6825e,-0x1f6c750071dff2fceec8,-0x2f2d49fb14a68b63cd,-0x21e027e0265bf6d4]
def m17 : List ℤ := raw_ints% [0x0,-0xa00a3738b11989014c272567acebd9e16ba11673a5000,0x1154b77f2ba64e211054fbf522270df546194e91df9fc00,-0xe8644b6abf149d11969b00672ba37e6b49efdc300dd4000,0x7d7a102c314d6ca67f26af17c633e6f5cf0c9902f4602a00,-0x310d46bd2d7ca4706eee9d08d3c1487dad053309f4b863a00,0xecac791611f93911d4ee5229f877ac6cc696ad045f6d904c0,-0x3947e43b435191fc3ab670ae82c27f04f273073f7b4542f2c0,0xb6df30d3d8e12c9dd3d20a01a4958b07dd91844202ea08b680,-0x1eaae61d0ec252a4a5bea116ca055138140660d45f203d61880,0x4627346030e2b5f40215d18435a1cbd237455caa5cc54729140,-0x8a4e492a37464fd260b4483a4082b241278464833b11ca80340,0xecf7c0bc1fec8b3b6681472e9d59b0bae5ca37b8abc3441c780,-0x163258729cfe38f4fa6e38d67051a7956dd06efc5a031c438180,0x1d3eb013e86a65ab91957057144670e5e3badcd05be44cf57994,-0x2200a8beafae89dae8dc953cfb8e0926f2210b03384a3f04cd24,0x22fc771ec4878d9fa973799c68fdf97ddde6c3c3bdc8165e1058,-0x1feb56a4e7602b1c24e38a9bc73a1c2e539f2ba57fc63eae2a98,0x19da289dd06efb92281979bccc2911967aedc9c7e5df3c78c670,-0x1298c808da46d04277f6e7c33f310b1690cdecdb2ffdf2623250,0xbe122d4577b0f69598d64c013bc3fcdb70dfd7dfb51498c8e98,-0x6bba2f3283df7c6a140a1ae15fab372c6737fc27d2bf4116f98,0x3617b215ea31d9a74cea76e357fc111ac215f3305ec3987eae1,-0x1802bd0e31086fea74bcc8143b3299f43690804eb1b070cd655,0x964f1f29ed15c8b6218ef302a33bd9c9bc27fd4beaf5c08dca,-0x33a53d54b715f07d9b54d4bc711d893bdb29c35dee6f0fdcea,0xf83226770eadfeaec9374f34118d27063e1df919732c392fd,-0x40cddaa4cc5ecaba92282fdf61cf38bd19685a1c239004f69,0xe9c0a571243e5234463b7a5ea5646f7edb8d69ea0a338c48,-0x2d217275e46d8519d8c4f04a9541df437cce84bd1fb11f88,0x763a074830175398da9a1024f2a951e9ced0465fbd07476,-0x10389950a34e7d81417fbab18279134b6fe438fd67e668e,0x1d695e2f105d60d60853f191a4db0fac08a8953dc587f4,-0x2b456dba87ed48346372e8892e6781609e2ff3f04aab4,0x3287df8ccffd450e7d05d20b316a434812f9ed20dad2,-0x2d8eb008a9e1ab86468d33ab1163d63c7e3a088e28a,0x1e9b4c6688ac89d9fb9496ce9f870f6178d99b4390,-0xea0fd19aa0c98cf04a25a533f4764bbdf9136d50,0x4acb385f7d2d25a060c1547c618618bf2df5a35,-0xea82a66e496d8676c1a2b1fc36fe03bca4559,0x18daa525a6f7bf23f2497c3a01caa2042d7a,-0x12bbec44283b4b809e566931a9a17b875a,0x47286bc1cda6489e8afe966cc11aca1,-0x272b5fe698eaf3967b0b3dd3bc5d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 23 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 51 indices rho q17 m17 17 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 51 indices rho q17 m17 17 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r18 : List ℤ := raw_ints% [0x5402b3651890165e747a58dcf144afd09800000,0x7da0004631ca391f7cd059a7d026a0319180000,0x58e8ffb17179cfa94a7f51bc434c9d1b33a0000,0x27a132baf23af5c928be9887ef20d7d015e2000,0xc7cad77bbd7939e39a56b50201ba376207f000,0x2f59a707ffe9bbb3dfdee72df7f8171cf8cc00,0x8c472ea17c9f4c86243d02c87b67a924b7600,0x14ce553cff7b82c480ad09ee4c617fb36f6a0,0x283a7972a3146953c85895e4ac8e79215c10,0x401c6e01b5bcb89b656ac200f935b8d70f0,0x54db96dd8c845604c1e85bf040782a9a38,0x5db2d0cf06c1a500e5de3716f33523f1a,0x5673da0769134f6f5411b691485043c9,0x4296d19ee5d1afd26706a9c318f6554,0x2aa82332876d61a294ded45b7ebaa4,0x1692073119e75f6a10f3a548ff97a,0x9c200f419bc5fb82a210ff6b3d5,0x3643c0fb0114a2bbd4ec6a0d98,0xecd471553dda80f5ee938939,0x30da8b12abec72d44be7830,0x72b99cf4db84840216db2,0xaafa951068efa745540,0x79b368169622dc70b]
def m18 : List ℤ := raw_ints% [0x0,0x122128416c0fe48525a06f3cbe96b7ae89313f8b19b1000,-0x1f23ce5e29e8b5d78a437bb17e389a4bcb03de6865518c00,0x19dd2a8d23e36e5e51bbf96abd7aba51f751065163fd45800,-0xdd605aa657a6228b1fa86e782d0514fa2483b85361349b400,0x55b77e7b56a861bb431d5019d530cd747f2963b656afa55c00,-0x1998267b98679ab7c4b7670217671399d3e526eeb9ced9d3440,0x621a352d00a7faf45babcf6cd95a2bb58e6e508347d546d8240,-0x135e5ae9eec72b3bade3cc45e94a028c466c945264a64bce0800,0x33671386453fa9578c7fa69fc1350d439c052228f78e41f80000,-0x744158c33895145e6cec195522544ea0c5b2edcd183840991580,0xe28157ef3f3f5861f7a6b8478aacfdda64854e0d6631c0e20680,-0x17f5aa399e5c0eb9331fc4768a761559636aab783255595fd4d00,0x237413c274c9f7e61f438d62d613658f8743278e687ca84265b00,-0x2e18453df1ac008231d2f6a53c3e2285ecf31f9fe246130cf9b0c,0x34db592cc2c796f47978c26571019aad6ba0be10e1916d04285fc,-0x359b0848c51afc5c215257594c275d35ad1804a7663d78d7abd88,0x302c65db814848d96e2b18e27fbff68e757e91fbb8d27ace8ddc8,-0x2667a709a2e82dcafcb7a2bfa50a6bf3560ea8c5888a0bf76c800,0x1b2c30a6f9c2a77443d88b748612d7ca4dee361d55e35f879aee0,-0x110ee6b9fc24be494a822d6fe257ae48862b641ab9ca74a20eac8,0x97e2aab27570e84376c458c9c3a8fcff9cded60a81360af39bc8,-0x4acf12ef41211378fb5dd2e527c7aa71cedd89075ca633472ae7,0x20897673bedf24588bb86607af96cbb70618fd1b1da5f9e0c493,-0xc75787d21fa633572bc88a0cccd6407e36099d586e97c798986,0x42f1e7609e0913bd06e869ce64032c23e57a9afdcc3298481e6,-0x139fe71699f6b210073f8ebe8102654ac4164edc4c1c8d7861b,0x4fe2ac9b66c014c8f52d482870feda46eb3a4a421968e25d4f,-0x118449d065442dc071d70bd5ee24a20ca7c458067c55040db8,0x34861c89f23b91e7d0c0d9ff4ae3fca570a0f5fb9671e8478,-0x85401a2f3b16648b990bc3f4f5a308c5fb4d2a6a5a79983a,0x11a8ad9281eb46a449edf4e7098dfa82ae1e84e85f983de2,-0x1ed58671716bb514214463a4ca5e1dc42367dcf16c3bccc,0x2b8906581190e8b08e28d2643113bc5080b2e4d826358c,-0x30983f3d34e2af90daba604e4dfe239aa6d4a3d59f90e,0x29aeb991eebaf16fea990fef70d3ba92b1afa950b356,-0x1a7f1d8b1147345d47e6ba337528331b1751ed08c10,0xbe7cd0cfca06e6842aea64b9229493b9d525da650,-0x38c89c4ac910c7a4aebb508920085d52ff5a68b3,0xa49387a0a57818e51561f6d0f4ba9174af602f,-0xff2dc61f79a7399d498a72dbd1ecd6556496,0xad9ce00ee984dd6332035ac72befb5d336,-0x24a11fc62dbf10028923e8cc767d2637,0x119367de57f68e48f1a97af5c811b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 23 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 51 indices rho q18 m18 18 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 51 indices rho q18 m18 18 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r19 : List ℤ := raw_ints% [-0x12dd086b8c07bd424d31c0bb3b7abb043e5a00000,-0x1c2fd0bb56ac57890e45db238d1f2b4f5f0f20000,-0x13eee1f1e49a9b1371332d5add58cea84960f0000,-0x8e086bb5fd236ee211af0e79fb790d65fa5bb800,-0x2cb6194196fa14600c89d14abe3386b40a22ae00,-0xa95e6af4560335a75fb4ce5a02c9dcdb39c8f80,-0x1f533c3198f8b516711b08862dec6f905ff8020,-0x4a3f29487ff7a6a934eeb86c8653e5cd3b25f0,-0x8f5cde4c619cc0687ce142181627ed69873b0,-0xe422c48d60dd02f6b95098239966befc0190,-0x12d786b4b21568e3b0f168c876660d3dc032,-0x14c47d8906901dbf508247ddbc05521eca3,-0x131f9ae5dacca8ee856a9071f2827cbce2,-0xeb2781a8fc3078deda7d229df770d1f5,-0x9644d48aeff75e4177be8ab60e92692,-0x4f4a872de8d7850c048709b6c16291,-0x222c7de44ba826dfec93e9b042a7e,-0xbd6197e5100690bf2b3af2c4d6f,-0x3373db1c958b7fc5a530320236,-0xa90c0078e962dc24121f011c,-0x18ae50a0f4e8cd811e732cc,-0x248ed0fcc818cdb7d54cc,-0x19d58d441ddcb938e8a]
def m19 : List ℤ := raw_ints% [0x0,-0x20dc18f693dcce315432c99e19712cec58a9432c1e90d000,0x37f6d92816d987fefcc2d97ac955c56808e5831d37a3cdc00,-0x2e13c19834ccfb9e664a63a489f09cd4ef457c756e51bc8000,0x186d6189b33baa1099082370f4ca0e184151aa8c858c5feea00,-0x95ec6a60382c395cad03234d3a8a79ac20e9b75592d8a5e3a00,0x2c55cdfc3a67f0a996c483b2a531b1080028a997f43441ba06c0,-0xa83e3168fe2f5634d0bb6532b0e2cda32b0e1ba1cc202d20acc0,0x20dfb703743784675a3e7b146a06899ef3b69b7e7ffeaae055c80,-0x564fbb50123a1ff4c737d50c7617a02a64d61d7bce643fe520680,0xc10a569f1af882b605808ad468f3065b769a99212549aa34b64c0,-0x173c5e2638c8a0571f957048b98f04635a44e26356ec0f824a4cc0,0x26dac6ed7f7b9f3dda82cb74413487972efceae29db926f9c9fc80,-0x38c6c5364a1e1faefefbf799843653619ebf05d4f5b930de0c3e80,0x48dbbbd0df6e0c2a66530628aa174d017ed57c6eb9be4274dd3254,-0x5269da8d5f98cc913c41fcb553ad254c2c889b09933db6761e00e4,0x5265a09e819ec24a4454d7597bb0eb9c749192f5f9a51f37cd0858,-0x48f33ae0714c12eabc173e3e22da314bca7435e30d3b47da91b898,0x39413eadbc586260128a934b2e4640b6298fa29e2a3964c2ba46d0,-0x27d99d8c5af064b67320577e4d42924c59bd5b48144232c757b830,0x1896bdab8f0497071b1a5a961df57d351edbab692974f509563f58,-0xd6fef2c0c8d200e385ed915be4cf931d0982a06e6146e66dc7258,0x67e1ed9dc86641d8359127930ce8eb53cf50ea39aec81a80673d1,-0x2c4693daa254cd3da8f0f144e413d7926eec47aacc1143d5f2305,0x1097f935c64fc3a50e80126fbdf59583b949909904f18de80b96a,-0x5726e0fc838c882c2fecdfee3b40ab505f52816a7071d070268a,0x18ef6c959ace5fb1956b06f92cc46787e865d198b20661df878d,-0x62e7ac16533b368bad05ae04b521c8cc71a6ca46a6011cd11b9,0x1517d79475bf6b601796677d1ba96c083f1158207cad95cff48,-0x3d6338451c4006800b4f94e7579abc6647fb2237a25808ea88,0x96cd8d03ac57fdcafd0a29508c1d52f5262050e791aa54c16,-0x134ce02db2cfcbee6659bcb5fe8c6ef0e0485e8408fb9caae,0x207241a7fad50cbd88e62ae0b75547abeb8af2173a7fe6b4,-0x2bf3dc581b81ec2740e89df6040c3d178ffe6ed59f7b774,0x2ee0f0b97eedc2bc6261622d444ed633a5fcfdfda00dd2,-0x263d9d1db1ed6f9ff2df87780852c972cf4b8cf6a668a,0x16fd637e3715a07ff70f00533faaa0323ebc1c8bc7d0,-0x9b4aa3f311f04153100dfaac7d9cabd348178ddf90,0x2b290dfc55e9d88bf94af39d6c0bf81e65482d0e5,-0x73918f587e27b969e34c5a84025aa0dd287e4c9,0xa3c4b139bef256ee4190dbb9f42cbc2aac81a,-0x64891215db8b5ff135eae6a802595cb97fa,0x12d93808a4444a84b0616df702fc25f31,-0x7e24ca62e7a247eae15aa07d4c8ad]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 23 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 51 indices rho q19 m19 19 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 51 indices rho q19 m19 19 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r20 : List ℤ := raw_ints% [0x40116bd822800404416b5f9beaf9839c91c0c00000,0x5fab74c8bbc4873488cdc666fdc7c40f49ab3c0000,0x439b376b981899c98e81c980e627f5f79921e00000,0x1e157fa0024e1da96324ac02e233c8a8b6b3be9000,0x9764cf669bb1fa7c08fc7c2ff5046633fb834ec00,0x23cf2887c8f0c0ee55289e14c5a63aa73eba76300,0x69dbec732efdb791838c45b59573bde8e2789440,0xfaa025a525f0251dd9d6c029ceb61d9e98c2a00,0x1e356d7cda5f2bfe78fe3bc3641ca5141d6db70,0x3001d5e06dc013945d3d9ed9d12d96cc475d10,0x3f5883822d66008f702086d5f8cba10362bec,0x45b4e80f51d783f8d1b9e962040df9fd74b8,0x4012de4f7d217dd6e564f4919b412fdb3e5,0x312562546bc2be8aaa4f2fa2ec5d6e6be2,0x1f562ec967945e8547f07962632a5b57f,0x107eada4fa18666256a6ab4cc4417a64,0x716fa06b1b0efcdbecd7fc96c4067f,0x272b440ff95718f3de4050439127a,0xa9adc6fec768bd785c837394535,0x22b4961f2521a4395e5ecf6080,0x50b51ce33afc337e36a3616c,0x76ecf3ba99e24958968478,0x5388977603225d232e60]
def m20 : List ℤ := raw_ints% [0x0,0x3b8eed3eec0035b9689c0d6e8e1d216c60b2c9bff76679000,-0x6499d30c2478d3b4b9e81a6e70e605da37c15da4f4d8e4ec00,0x521fcbe3aa72c7c6deaf360315aa5ffdc633b628114a6c2d800,-0x2b27a1973caa10b37f776a57a8677f7790b412db19725155a400,0x1067557b7437beed0ea56688f34f6350aef02566dd52f7159cc00,-0x4ce24724154422abaf261011c8f339c919fa136c5f759409dca40,0x120ea7c98a1927811bfbdb65f817df2b0784b4b7f6d19d78d6c040,-0x37e1eb952ce258cb7e1201d0bac12ed9af108b4fdce2a1b1871600,0x912eda39be9155aa835ab6f118a7f2e2b355ba82e9823f0d2a9600,-0x1412c74fb98e698322ead549efb65e037a396d45180bee6cd254800,0x26389e3a0034125fa240ac70bc5f85fdd1abd344563047b9c4bdb00,-0x3f28e04eafc232efe08ec31333b3880fd13aec52b856368b1204000,0x5b28b9935765c88a4d4cff97beaadc57e8a546df0d6c73b3dd45600,-0x737b45c1be3078e1695ad48b2a89112ebb52f3e9e5e8b4701f05e4c,0x80e11b19eed026def59bcd5f870c6c2317305802451847549d6ee3c,-0x7f0d1c516cd89489743eef6770a5e6a1bdff74f04249cea998f2e88,0x6ed657e177f8e38841c55de0ad72ee2e748d1ca7a05086d0bf5bcc8,-0x55a794267e12fac72849412cfa456f03bdd1487dd79c8f25e835720,0x3aa7b22055a1b7902a1dded091500dd827f91cffaeb142970e9b680,-0x2393fdb45e569c9f84e59de284cbc50e478f22c6319b26832244408,0x1318523b5efddcc0a9491bb78a73ded5d2ff8b9281f9e1cd8bb1708,-0x90d5f4dcfaac2a33e5b2944036bdc72930257379d63ac7f6a608f7,0x3c7f643a81796a672d11c213956674110c50e8f11eb468c71996e3,-0x16317a705b4c3afabe6e798348a3ceadd43c10f24c7d9a76400ce6,0x71f0795221603bd4347af0153e65fe1146137aa86dd3c14289746,-0x1fd17018a119d018dc95317c9b676ca73e5da7a025c2d66c68e0b,0x7af9642c523f3e61dee422e930bd9a270aec5aa8ec0d7ea44d7f,-0x1981bf16db9e9f88954f5108115cdb13ea41093e178ef1668eb8,0x480b40c361c2c431716a4670e0a3f8015555b63f4b337412578,-0xab5a4e5b845f75557be96f8bf4e3f07bf9f45cdaced244ee9a,0x152ce1da41d50da4df5c44387143360f777436fae1095ac7c2,-0x22442eedfae0eb7ffce88727ecf300faa7454b6a6f1aee50c,0x2c85947d74c231f1b16540eef315458f30e94f235acfd3cc,-0x2d5bb90526dbf962d9aa820b3c30a495bab76e6d1ef2e8e,0x232c68aa5d57ca435223629a8b8ac9e2a68923e37741d6,-0x13fd3fadc3f8a3be6bcf4054ec57414c5af37d0ded1d0,0x7eccfa70e343a93bef532cb4a84ea26a9301c230210,-0x20d71be12b938d4aba12de3c9f836fe0888eafd903,0x5132b8984b5fca5bc499997b1d5564885df1afbf,-0x691cc3b7e7b2f4e11f2751834660b6be9bd6f6,0x3a34669486b3cf08ec6ca4ffe088e2b2e796,-0x9b2080e264196f2594ff35f874cc32927,0x38911cd4febe8f84ba5de8c907b44b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 23 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 51 indices rho q20 m20 20 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 51 indices rho q20 m20 20 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r21 : List ℤ := raw_ints% [-0xcf292e8bbcb06e6798995721e64784111a414000000,-0x13526b8cc421b46c350843bdbe901826da8cab800000,-0xda518efa6f8a29255e0524c5b8f4ff065a34aa40000,-0x6113f50a24516688ef850fe4ddf44325c0690df0000,-0x1e824d3333b32f66187f067bb3f738e0dd31bfd3000,-0x735c6682228fe25b4db7818c660ece3065b6578400,-0x154b56e49b188eaa100120c54ec17617a012d70100,-0x325d086eed1d416c966d094a62354e249a7ee79c0,-0x6104d0a6e6f635ab88ba1e949d0db72375b95000,-0x99fe0c37ceaf25637ecad7c87c3a08be5443890,-0xcaec1c33e61f2875ed8ab1ad629728a0ecb530,-0xdef8bd111ee48ee9aa17de61b415f6df3ac74,-0xcc9f8ff84b07cd1e783654f9b11d0a99eec8,-0x9cac1bdea3791d5b17abe5d914262e735db,-0x63b3b3ff00586d0c8e64eff7247b585ade,-0x345dd42f458c38a26c8c714a2edf16421,-0x167419f48107a5b1b182fa0f62e6cc9c,-0x7bb6daa0844fbac451584d2290fe01,-0x2164c7855e0a6de03d55190918946,-0x6ce8a26bd77ea0f59ba9907586b,-0xfc481aeaf98a294aba466e300,-0x17217c33ada531fc96f06054,-0x1029f1363f2f49464e7ac8]
def m21 : List ℤ := raw_ints% [0x0,-0x6bf30e020bc061600d9ad8586194cc946f440dabf069bb5000,0xb4e10710197476d70c90d457fb9766b36a68e1bafbc91eebc00,-0x926f8c88674c3390bcaf163fb7a7ef760935ca6910187b13c000,0x4c4a4d25ccae964f7663f9d4820ca9484c476a8ad5074340e2a00,-0x1cbddacf89a4ef4a8c9a119664a660bcc8b2dbe477885db116ba00,0x8579552bc09961380f71afba3541fef886c341250fa30b1833b8c0,-0x1f0ca8777c27b7b9309c06589a15344947580915fe4769015f0d6c0,0x5f23b64a57a39200d8e5bbb9378d5f5fd570431c192b81debb09280,-0xf4a20ef7f601d8b97ff6ba43e5882061bfd334c247e855fbda44480,0x21765083ae879014bb24012d4ac3b49af697371bae10af652e33c440,-0x3f01844b8fc41e03370ab77bc840dd684f04ff99f2518385dae81240,0x66e8def072cb8340f313ab5783f9f682acfd36e5359df8df08a71980,-0x92bc58bcefff10b5035ac5115e2f815254cb50cc7e445ca38463a380,0xb78a812a000782a964259fea31e2d330dce37c39a860780dfe4f4b14,-0xca21e61f9aae165777b02cd25e6e711aa16038ce5e7969bc941af4a4,0xc4835c278c353ab383052d518bc98ef8b0d88dab147b4dfd9f45b458,-0xa8f3dcb58a857eb756f4cde3e8c7a191a6699b785bf7a930002e6a98,0x8094d4572bd40744b743ea45f3380cc5c0ba8bb8b3373d56c3fc3630,-0x56a4bf3d8870e989882b246e11af7096dfa68999a10d7d0b7c689910,0x33ab9c7ab38dbf020d0a8367dd81a6e77c8936a0525bc5908a93a218,-0x1b3d4846c52561534ea9aedffd68287bbf677f2007959210437cd718,0xcabb965468f465b9101be20711f3c52456d6859ea8439e920ad9cc1,-0x52ff5ca5fb2bb4cd50f27d2df5f38bf2806f2bacf64c69581a4a7b5,0x1dce009c0cfadb6dd77012123bfc620debb11c1f619cab063e60f0a,-0x95948b17ac1607f702e22b5a7957b9663301410b8a020a63f01a2a,0x28c543a8f4a306aa8002f54a8c07c2528334dfeb3817cd3997bb1d,-0x9989bf600325116a89a34e8b1c93b6f11750f186a734f77af0709,0x1ef89f101405b836bea6fe368814ecfb18dc6a2b37a5e1a48ae48,-0x54e431bf0f1d2a53e0e376b18ce527f4e3072048d11870691188,0xc3769dd6ccaffafca84d9025a3677b91ee2989d938e2e2e9bb6,-0x1751b09c4a8eeaccfa3097b8dc0a04a08e60a202e8c6c12d6ce,0x2450a0f5ce34cecf824d804df4b237f85fc99511545fb1cd74,-0x2d3e3384edfa087590654740a35564a770ed9c38687c0bc34,0x2c0338d79d7ec80d1ab2a7e3868f00bfe0373cb65edc2dd2,-0x206e740a6ba2fee02fed28f8e48ee8c8b6eb5f27864ab8a,0x116a31220f1f84c347a3e0089885a2dc42b27fc4d7d610,-0x67b0b42667db70d946715092b97b89f0d12227d34bd0,0x1903081850d6dd70ebd08f3f38c770cddd2a1451f95,-0x39138007fb2c80061925e59f95dffc9486cabf439,0x4377d4db195d89e331cca6c3976212a4f8d8cba,-0x21b07a2fb25ec006730aca42cf25a2a12b29a,0x4fc4549b01f872a30eeef172a0a113eac1,-0x195bd5cbab3345b610fe4b1f36389fd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 23 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 51 indices rho q21 m21 21 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 51 indices rho q21 m21 21 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r22 : List ℤ := raw_ints% [0x2815fac5fa1f3ffc42ce1d14ec7ffe1bb63b00f000000,0x3bc966485a321761d7dc27d7149363a930308cd300000,0x2a31bc52a81503e31b16ffbf2a2b4d9dcfc1504e80000,0x12bfdf822e1d55fa57856b817a5616aee4e4d7f2b4000,0x5e35d568808bfb2c6691d081f503c94718c3deddd000,0x163f20550995df4893171708bc560f9b7d0435482400,0x41a586267ec80a1804b80714047b12d6b3983504700,0x9b1d95c292a90c08fbd97892c26ba1bd56d421c980,0x12a813f5d3271e1f0040420d5b2662cd1216dc21c0,0x1d9455ff314fd9992e3480268bc5919d24fcfff00,0x26ee3c60120276f05f792ab3d400796640ea6520,0x2ab857c3d702958ef772c3e7bf6d35832094518,0x2725bd95ba2fc64ca82feee70ffd9f7c30be2c,0x1decf6d6dc81e95d2bcc55cb1dbf399193088,0x13029eb14631c0afc3cbbc5575f99fe88f35,0x9f71cd364a5b1fed37d6d9fd04d396e05a,0x4437e1dad2af91cb0b84d849c9d32911f,0x176f71acff983a197dbcb14e726016c4,0x64f0e98481421fc243c18d7d52e6cf,0x1483699a528019c4d4e26012dd4f2,0x2f5b4c8d8b60eca2c78764c3a35,0x4534173592e6b2743c5e55e50,0x30257e20c8946831bfa2f1c]
def m22 : List ℤ := raw_ints% [0x0,0xc3a88963b54cb07e18a8a82030ddb2cd09ab58c7a3bfa381000,-0x14549bfbed6ffa7dcdf17c0a32231c34f023c4f22e85c880b4c00,0x10538df55449a23d91e8fcf9fa38e2512dedb2e392b730de5f5800,-0x86f47ce8fb0e78c7097456e6b7c1b50eb610e8273c79f49e289400,0x32672338c13dd2b38df4a64cae63436daf1974b2e3b27eebe7b3c00,-0xe7f73085e2409b0ce5db13366ff60bf79127c7eef7cf44c6e4ff040,0x35754a0cdc7beb3ea0cae2ada38b06c39a746da2953718f0f68cce40,-0xa2376c39a887beb6dce0aeff9230b2ea92cc815dfb00282a7bd13400,0x19ce8948c088925156adb6ae3c9f38e43d18b0388100a13368e90fc00,-0x37e344d000e80f89b0ff8ca1c64b7eac5d97ac8e146ed00d318f2be80,0x6814f89337cd36de15cba0bb28aa5a4523f39379a1d0c85198c084380,-0xa81068714e1c19164648ff07cf4c687416ad00973ad5da11cb31c8b00,0xecc994f8b0979e1956656668402d419cef43037d05c8e862fa9916900,-0x1247f70abeba33761ef64b397eb54786c743d2bdf265c9d322fbf7b18c,0x13def15b0c37f926d9de029343eae6d0ded70f8bd91b1daf5a9769c67c,-0x130e13f876acf06a97281ea734afb1359c1b0b245ab8ea7876a0e21388,0x1025e8f79257c4ff96343520756c1df265fc740f601fbd332a45d1bfc8,-0xc1ac886a19bacd19682d2e0504b38bc807ff83a7650d9dca477503b40,0x80705f7f0002c0e312068dd4234ad6394105aa18d23bf4bc283be3720,-0x4b50f685280332aabd5268828c7c4dfdbe7d495ffb2852c82c75c5b48,0x27012cd0ef9318599a20b4eaf6fb3c4f5f5803568c235434eaea90048,-0x11ce0adfb57b4248b364a29ca6ac2b539f615cc5dddf5a22ec98c1307,0x7251779470c1934a5682ed8fcd90813361423035e3ca864405a78d33,-0x2830364ff90c60083094e632db3290b89006dcad2ad3209ece88c646,0xc52bf060c34542847f8b67323dea09cc451432b9451a1775721a2a6,-0x3474b7a80456bffc730292e4553f63304c5e6f454b69aee8e3c66fb,0xc07af629c4406d9e8c466e0f80a3309e7389300dea1511e7b91aaf,-0x25c1f28cfd7c3a6b0a4f0e932cdd043ad1097d554ef5fb7f9613b8,0x646c69b39907cdec540332eb474a6ffca93ebe3c7e526602fea78,-0xdfd0447745fa18b185dc4428e56800e1df803d1c1185f42fb4fa,0x19c5d1f8ed0947b7d30c1bfbcabbb9b2462895cd1d0ffdb2f1a2,-0x269db28d5b71bdb0528d05adc5fa56953236d61424813458d4c,0x2e1e1821c247069572ad727fdc9506ff99df8204f59fec220c,-0x2ad2cab5e6e346ea4d1fdeab41c6109059fa258a4499afb0e,0x1df8fdd2b75271b40e304a1e6de4aac554b331d29dcfa356,-0xf3340cb3ea3ea8ddddfc3045bff2c0c0119f6f7cb4dd90,0x54e87a47be42954b9a4500f8727cbd6b55b1d53b093d0,-0x1310ee0cac8048ae49e8f16c9230b155a798301e8d53,0x2822e7601ec4f7c08f51c3b7ab13cb875dc5707b4f,-0x2b4e55264594bbf5cb93b032e35b0388e5fb2f56,0x137eac79952d6c69ee98e002be7498012a81f6,-0x290088eef7c02748750d9b3ebcc1fff2b17,0xb5d69bfaab185fb7a88dcbe05d6aa7b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 23 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 51 indices rho q22 m22 22 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 51 indices rho q22 m22 22 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r23 : List ℤ := raw_ints% [-0x7766df761a44f8ffdccdf2416e320c261296b0e8800000,-0xb1fd27e0811f62f3cbd7798b6a5f9c5f36131e13680000,-0x7d8ae2acefa4a0effce9bc295c6996e6d7718e211c0000,-0x37c0576f1007e81d67a938c03d0d9beba5b22339246000,-0x117f15c5ab3848d1c6745114af602310bae0f4fe435800,-0x420e731487888663dcd13435b4802d97996194a34c600,-0xc2c49d8d6fcb78d4c2f6e3979a9ccc366a2f5008a680,-0x1cbd12f23e50fb12df574ebc96a9f30e757faf6bfbc0,-0x3740ab86e7468850d0fcb409ac257cfcd591346a0c0,-0x57830bc6c838b8e2717dc2025195ff5121227c26c0,-0x730ca7e3a0386932895dfef875870dd2f29750d28,-0x7e184ac1891103cf5c2878882fab6a8ada38023c,-0x73656c204d0c016da80d81306efaa0947162f98,-0x5815a369dc662544f362f520da0bd5ffcd272c,-0x37ddc393e8969fb2bb85e4b9c665d8772bdf0,-0x1d3be61c78be561977b117cb09f12ba9c6af,-0xc7bc588572bec4df47ef3cde9a17ec7906,-0x4477f9afab978d8184ce0fce4a23d3331,-0x1263478a32ba30b563b524c66b65c3d4,-0x3ba110f612f319244d9abacec18d95,-0x893f3921d985cab296c70f0c8bbe,-0xc7e2e9dc134de6a9fca6e73a23,-0x8a88ac371794e0c378b2d0f8]
def m23 : List ℤ := raw_ints% [0x0,-0x162a17904b89affe48cb1b0ba5891d413a18690e9d8cb5859d000,0x2491cf8b0cd315d10bee93cbe17cd0e0862722def4527b69479c00,-0x1d22ed9fa52994c75e114678cf5c232d2298bfe913fd7d033730000,0xeee1eaf6dca60294438c35cac7cb61aee6e947ec3d600f7618dea00,-0x5876c18b76adeda041bf18e32081baafe86fd808c50e69f1857fba00,0x1938f608d35c29f1432226db2295491e719e2e2eaee91141367a29ac0,-0x5c27ddc397a7c01e43a34c104ec6db8c54b1192e787bf619d3ab1f0c0,0x114fdf1a39c955416a5658c2d91c722103c0a80edcd9dc5b5098fad880,-0x2ba1a661981d7f6688ad2dc9c1786fff497aa4fc42593e68bdbcc35280,0x5d84907f8a37b48fa79ca2dfb74a37cebc2a32d68a2ffc36529d294fc0,-0xac4b51edf62f0236073331599f4087ccb242bb6f2053555fc5979773c0,0x11317ee4c1d2e6cfb07a6dfc801fe126c27bc2362d43fc4354896d2de80,-0x17f0bcdc799ed86bcfdea20998f1423a4a43c6ef6939e4cf25139c17080,0x1d35f34a9e62d179439e5ce5b283f6b8954eb3920a4a210f86c9128a3d4,-0x1f57eb3f5cc8b7b47239566bf675bdca77c0c6db6cf454f9dd5ba6b0864,0x1da6d763f78502b05da4c327b663cc7b9e983f1257ff61fd11c21edf458,-0x18c5cdec401b2a8917767b44da54566ed8af1375193a93d6bcc0865a098,0x124b096feec4fd1ba2e87a8da84f77beaa9829ab12e6e620b464ef59c90,-0xbf0ea26233edd522c792e95ccc5d1ecadf7b5ba9b85cea68751e877cf0,0x6e2ddccbd54c31d8a7f8ba88997f51bd433cc432a6094c14a6666da6d8,-0x380f36900ed681b42a830dc37fec4196e7f0eb204f2ada6a069bd90dd8,0x191d699c313367fad0ee71c3e00b8fba1b268453b7cc49277193903db1,-0x9e12ec8fd551ebc1816aabc5c3d1fec54462502223521bfa060795c65,0x366796af6a347efb29899b4c3a358b41bba2ba72d2949805ff9322eaa,-0x104f246e80b4e1d139db867893b961a062224fa4a41574161fcf657ca,0x43c2f0d14d206bcd07f11a69991749efe7283fed0299d296863b2dad,-0xf2435ac8c62a32c93098e3bed0aebcfc0aab20bddfee8eae1e6af59,0x2e3653ad9b178ba700cafef820e86155c6cce560eb384e260ecf948,-0x7740d425098618102de2911663bd2689363d76ad2fbf0b28d6f488,0x10138fa85023be024c70b2ccc422f032bd537655e402b673193356,-0x1c95980a56d7b3be2295da072af155d8a1f4a241d3a1332351aee,0x29325e84ecfcb5b02503f5dfaf87b5ac1f651e1bb442d9611c34,-0x2f25f69b5a22b0cafbc3faf82a541e5bd846db66e8da3c118f4,0x29c666cb0d9385d37c981849fd25d84fa2746d5111573c02d2,-0x1bc2da7f226a4c4df9af7f0a1f8c4751d99d8628d29bd198a,0xd4a58a59b1f1e2320e47643a99faf143ad49332c609de50,-0x459dc106568322c97f031b35be069dfeae018aafbba210,0xe8b942f53e18551b914eaff1d3e3a6a7a934cc663e45,-0x1c3bd8049e1c6a3c2e2789a7c3a94556b39ccec0ba9,0x1bcbdf674521727f46a065684e635325f86db1b5a,-0xb472d8a6b73ef7fc0ca32750b941794635773a,0x15119b9e9448aababa40c63283c9fafadf51,-0x51785e1b2cfa3f7326cd9c4d11c6504d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 23 78 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 78 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 51 indices rho q23 m23 23 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 51 indices rho q23 m23 23 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r24 : List ℤ := raw_ints% [0x1578f625cd66abb672e04b7e4cef0fdfc555ed3539000000,0x1ffe19d4a6de17a78ac767a7d086a473d3d39c3918d00000,0x168db364d35a0cffbbbbe8a43a6efcac54c75dfa02f00000,0xa028437455254601591c38bb769f4006d846f397beac000,0x323b061463baff16898f36fa9fb1a5532bb0be4c6cc5000,0xbd8349949c495b4ca6e1bd0229acbbe0747d0cfaf9b400,0x22e5e7ca08906e06723bb482ec122b977380e875c1d700,0x5252be05841488e6d639459e0dea7849c30214f95db00,0x9e2320b952af1e1db1b7633f92178bd64b8d18246cc0,0xfa3aff71eadbd6c50d8547f5c349ade52fb0d1b5840,0x148a29009d44152cc7f0bc8a8ecf253392dd4945a10,0x167c91ab53b94b115d93f8892a422b82713d7b2850,0x148dc2183118d3903a697b897a073f0749b35a624,0xfab19d1536440ee7f249d73c4288cad9d5eea98,0x9ec4ab25518b20b55c8da6b1b129e52e240f44,0x52f2ead792a03770d7568d08d1f1d9db08b18,0x235bdc01ee2df8a4fd8f12bd63d182056a11,0xc18f3cf38c8a8f0c88d190e76d0917a09a,0x33def15e0572ad4864c290affb567557f,0xa7cf89695522d5e3bcb8e2384af0a34,0x18138e4e0cb773f183b573217db2cb,0x22f5efc19a407c3b2570690adc72,0x18261ca504d4dcd2208a46b6ed]
def m24 : List ℤ := raw_ints% [0x0,0x282c4ab588e98efce3f021051c088506394c3e6a7d8f09022c9000,-0x41cb149c4890cf31b147f915fc454aa7f439f78a1ad57faed1cac00,0x3404e3f573b88e13563f094bf87fbc5d0984c45a4638e7131b89d800,-0x1a71b38036804c7c69398dabb65e142bb11291264c429a5ad98ee8400,0x9b65120c2e7581e3835017b2ba7b2088cd3c83c1fffc98b590155ac00,-0x2bed11c02f343f7a567b9bedc8833409e43f4fef329530a742b9ad2640,0x9f101f0d4721eb9bb3ad0d2111754879d754ccc1903693861fd55f2c40,-0x1d9a8d78d9b66da2025b4357a1c674794d7eb0ca03795279c5e6688e200,0x49e397a564986d85d7bcad5040c6c38fe2f1465c6bc953db1653f75b200,-0x9cc6158e0eee79917bdaa2a15279c96d398bc67d51101bfcbcf68a35900,0x11dcb38e787a22152dddadd36d1e1820a5eb9fb191db80af5eaa599ea000,-0x1c34a62fb225d26a5333ffda313066e58cab01aee1057ce2418f79f06e00,0x26d2640da1009d0a51523560dd11b73cca8a567aa3f1d2e4df7531e9d400,-0x2ecbf30c30ed7ada8951dc3304556548d79164936579a8661790208834cc,0x3193e08443c03a1ab4dc250d7d21bc5eafd8e32a9f165c33ed9bba7d2ebc,-0x2e472d6e4e04b1893985c1544f00adc2474428e8eceae86906336732cc88,0x261f4f1c20c67a4762edb8d93dfd3d8f04627d2900010258f969d179c6c8,-0x1bbc6ecf4f4029d4e9639282d6d754868810628341073c41d1bb6053cc60,0x11d2cf87769edae28ce318665f1aeafe2a04949ba43111ca3e0d702368c0,-0xa1c06f4d55ae58fc11185421a54cd5f7958d21091e3053a2cf04dff4088,0x50dde5fb7bbba0ebf4e1f9a5ede847a9668766b7d4fa65e1df1cc04e788,-0x238f3a8096fad07a77407610c8c0a4bbfbd53026e5c3acfeadfc268d117,0xdb6ac796908130504e144706ac008b8c8b455d8f5342f0609fde3f8f83,-0x49efe4d1ab7ebf7fd5ecc49cf2253e95d498afe96e52ffc9de91a395a6,0x15ab4fa058a438d0c51bb6b506a0e831ed7d4736976a6abee35d588406,-0x57e0a0c17497f74958968bf9774a5765d7daed54e237c0713b751d0eb,0x1321d0921c40d45a63c7b4b8ae5799bb9e39c92b599ec2493bc7704df,-0x38c705120f6ccd7d86d56d195a87ffe1e6c5fd8d0d8f79b18d5f3cb8,0x8e24b592621c214c7756b03353b1ba93c89f1de7f5be4453faa7378,-0x128ae4197e312ee8119eebb7e44bb8544c070cffe5e39fdbc6e5b5a,0x1fcf7383edbb5463ec2288c5bd9a340702e2e7ef1523e59fc56b82,-0x2c169b5e65826461cbf4d30e23481e2d28971abc32537dbeb158c,0x3056d5d31d3b048c011ff75aa1f9df110632bf4bbdcf93d0004c,-0x28da8b7101d8a5081e0989678eaa9ba3ac6f81ebb1d5e78768e,0x19c4323534569b57957aa5e66feb52fc334c3670ed4e95cfd6,-0xba3bc84d48cc42d8a54c4f96e4ff802e68a3336fe8103f50,0x392526753ef625a0f41b28cc1ccc8e6a49d817837d96b90,-0xb1aa96d995d4671bd0145e6a65236dd7d473fa9256da3,0x13dddab13ad172e36fa44a7d9bf548f5169317358adf,-0x11d72a1c7eab75f774722b93838a584c6e4e49cdb6,0x685d53f373fbf7bbd18405c040b37d470d50256,-0xad28c338276b645129a56554fe9308be1c07,0x247dcb669d2b26b79de927ba2355e93ab]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 23 80 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 80 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 51 indices rho q24 m24 24 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 51 indices rho q24 m24 24 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x18261ca504d4dcd2208a46b6ed,-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r25 : List ℤ := raw_ints% [-0x3be37663dfa2a9b39d0ee9e5956c5398e6b7fc20cb3600000,-0x59304da8dad1937be0f9f0f739d7cc881e3b1d8f32bde0000,-0x3ed7daa30e251120dfe066f5d219e99605f67e1613f610000,-0x1be05a941e97c96e62db62f4b1dffafb5ee0c23f513890800,-0x8bce3db109f60135ae6a58acb7ae320d92e6b4194de72200,-0x20f227dfa1f9e55e80cad03734b01c78804c341a55b8bc80,-0x6100f411770665177f62a865f9954810f4fc700e73d7ce0,-0xe4a8cd32f5b2f2d6dfc3b95414396a82b860de2d479e90,-0x1b6e361d251a3fe87ed53fd9cef72b4a0fabce976d5330,-0x2b5e11db41b98f33d82123008a692a979030f8e838ea0,-0x38e6fb3b9057f207e49c9998178c96e9b32879a0256e,-0x3e3b7b088821f81115e327e24dc213068260799b18d,-0x38d1e94fcca10143d66035d7dafb17cf1bb3d2e814,-0x2b431b51e920762d7d46b0d6c3eb953f95534504e,-0x1b5cc546d1f9bb6929972a5377cfde5555d7c9f2,-0xe465f5a1252a2196d5f0a7e6eb4acb6e032f8f,-0x6134a05e6c72bbebdabcdb5bd1660c07d49b0,-0x21330c3f4c8f12f3985263412c4cb0010a4b,-0x8e13b465b581f0f479561a8822568f3a48,-0x1caaa196a87ace070bc90e76ff07ee134,-0x41a697d6cb9ee56b6a8f5213e42ef30,-0x5f141e96cac0e958851b009c224e7,-0x417b291438fc0e0ab2f3550f6d4]
def m25 : List ℤ := raw_ints% [0x0,-0x48d047690827532a5d233bd942cf711b47da312103934053f0c5000,0x7664fb1fb5d658edf5b7aa93a37ef36e2c8a5f40d0a2f76cdc3f7c00,-0x5ce92321e4272d38aa279eb063e26f3bf555c72f0a22d7660a96a4000,0x2eddbd950612fe9d1cc9d91671e6550c86301572e427eef0d6131e2a00,-0x1112fddfbab17e3cd9ffa87e083cac6da54073063d70424ea3729093a00,0x4c93a95375295d7da275620406b80fa12740f645da1d3524ebb06af2cc0,-0x112e185ab585ca12fbabfbd8bb25ab9ae6281b992b5f778837fbf6de7ac0,0x32b1ce8c49713f7e163243ca6a5bdbc2de17f2d8ba03aeeffcb72368ae80,-0x7d550bd72c6338d560fc0ecfe69fdfafb5ad6e96c9062be0bbb60a69b080,0x1074b23cf91300c147367f3453ab984844d4d1927793ca9937281d910a740,-0x1db03c47d98dc2dd4ed7f2690638f6f58129be3bdc1d875245654bf619140,0x2e5f89fe10d89ff8a6aa3df808adf53f041bacd89242b3aa34aca03190b80,-0x3f1a9ff5bf10ee3398cbd334e29c77ab5361b67060d3a7b9be1842f1f6580,0x4b29a24118c75498d3b149d48261aaa3b051b4b3399efaef639e784211c94,-0x4ea2905386d72ee821b77d8f020c56987ea886d0441fd0192a819d68c9c24,0x4870041ef342a8959b5d88876d54aa2f13d41b420be72162bb77eab06a858,-0x3ad8a4681912dbd8cfa0d2b2a59781cb86d5aa74685fb377abb10552fba98,0x2a306e1092778db0044c047d7ff21569a155ff0f3630509184611418e41f0,-0x1ab177e0d87d7bbda81c56c6bba972a44d90224fc14bdef4eb85fe2aecbd0,0xee4b3d74d7b19f9e743a2fcc0e018df3267da13524dc78eb7d790f59bd98,-0x75129255fb0acd09fc0f38fa2ee4107f508906ff4ef6ed3fa080d7000698,0x3288b82f32216438da2f5f6c814033e4c1ca515fd483fb4b7bb12984eea1,-0x131b74a105aaea424e8b626db87e7b98a41af2b09c536eec2c5fcbbdf915,0x64ddf6185290ca4cc6dfb6e41c8dc792bbab64f72c77c426bc7de1cb84a,-0x1ce6e3bbc1a00f08bc2834f08be569cb225bd41e0bd28d32aab45f77f6a,0x7267a6adadb1e17549e9abab4140dfd49f66d9bdf87572c1d28de65f3d,-0x184459294d5443a1f44e67a8bc7f2f834cd9c2aa23d7526efd7d400aa9,0x4605277d26b6a17ebe91f9f8e0a32b5c0d6a699cdb4a42c3232b14048,-0xaa0b8bd4f84590425524b37ea3848e592eb438a8e6f031af83a0f388,0x157630a6b7098932e4e490e75797b1a3d484feb7c53692fdc04a62f6,-0x238455201de72eb4ccd4a850a9647b0396c105e8d45be5aa9daa70e,0x2f537b3d0fe086392df8b0c3c4a4aac19e4e1f100b9a41fa98b2f4,-0x31b20d84edab64348e3f61b0979f55d3d6967215a0229d27b2db4,0x280c2990c9cd6aa88940a4db5f1e7a968b0111aa14abd03814d2,-0x17f64a4d89f9850a041b521b96b90a77d4eb8411b6eb31dd88a,0xa359d6970f5bc8fa956db70a4bcc992d7a7befb749998d090,-0x2ef5651f491650011ec4c869b86abd4e26ef9d0ecde75250,0x87b85ec081d8b4d513c5ac599879f4ba601cf185cae4f5,-0xdfb7e016a3ffd6bb48622fc3a2d269a96df638778319,0xb731c73de030e397b36cdf5f50f09d817a7dfc13fa,-0x3c581d28adcdf7acb5a70b4cdd66f944b13285da,0x58eae345bba581c69c6b331082393786ccce1,-0x1057259ce128cae5d1275326a6fe806b9d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 23 82 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 82 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 51 indices rho q25 m25 25 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 51 indices rho q25 m25 25 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x417b291438fc0e0ab2f3550f6d4,0x18261ca504d4dcd2208a46b6ed,-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r26 : List ℤ := raw_ints% [0xa26429d0a71095f5298b76588774fb4a2fb683a55d09800000,0xf1bc808f113c8a6bbd6ab018ffe9d4778b062c0fac84d80000,0xaa40241a38db383199f1341497c456408ec7b5d480e6860000,0x4b7ba2c8c057e4752d20e98d141501707a347bc17369402000,0x17a5b6817e635c7c14eb7bcd2775ea73c747548d594291c000,0x591c11e9b74fbbacef41dfeae69000d3e5ad1533b87fa6000,0x10633dd0c693850e495faef5ced6acfccba3866ecb6d53300,0x269a5d78bb714aeb41fda31da1e11c1239cb0128a3628360,0x4a0a2d6a5e7edb5f56590a1dc8f0b61bdf1da978b5c8830,0x74f67a876407cd776f8776dd07fddb9a51b4c0eb41d650,0x99556465ab7aabb31c47957f47af2f4a9ec80c6abfed8,0xa789fa384f0273ffb8b75649c40343212d001a712226,0x98cfe3ff1c891657a2cb6c82edd75b7336f78a5fa83,0x743875bb2f94823f99f68e5aeabdae199986b84ef4,0x496b13d5bc36e76c8f47fb2ecf98ac4162c42f61a,0x26406d22d9229ccd2497a83096f9154e7069ee3a,0x10419e645bd6c6f62862be5af5fe8d2ecef7891,0x58b1b12fbd23d57ac5cefa5dcdd3827365540,0x17ae85a990c460a8460f377638bec609d47d,0x4c4e0fc0278d5afa638599df710390e964,0xae614813c28b78f257fcd2e5bb7d0edc,0xfbf3b17a1bf1d210e277cb68b054d8,0xad10dd7e966b55cc84a82f2d05f1]
def m26 : List ℤ := raw_ints% [0x0,0x83f9816e5ec746bcc8cfdc79c917fd01723b790bd67ae49824651000,-0xd517994141a04b9e1d0e059c3a487a6bc405162cda2760754f3310c00,0xa603435a8ddb9d3e07831231812ea068b40627b33991e721b3d4a25800,-0x531bf40ec0c2ba0dd19556f0ab3364445f991deb5cc7e99f3dd6d137400,0x1e0a6a36a3976997255fd7845929bfb662b44331e6bb3c729e0093f51c00,-0x85a15f4280ed8193b02ede5f76dd43275a8167aa5da077453a193c72ec40,0x1db98e34b7b4baa36b2beb6f3b7c96938923c308ccf33db0f8c5c85f15a40,-0x56eead29447dee98eb8441aa7f739298c6112455a9249a7ee4138f75ea000,0xd4ede9b21d07968a2c488623849fd142e69dbe94a1be933d366575f673800,-0x1bafa2449fdbb1efa3cac90ef2802c91ced84e4f27e9e2df749533f825f780,0x31713b5381f5d2b3ebc7304c5141525d042600532fa139c5c89b67e6275080,-0x4c685d9d6741d2255992f4cfd67f8fcad51a8ba3fc1dd762f3ba1cb6b82900,0x66d0a8e68ba651ee57ff2688df11cbe0a75b996813cc09ac87f91ffa37d700,-0x79072a61f0969e8e3a4e2d1c037cfd54967dc289ae63a7b96a3424234d880c,0x7d0f5775c51cf320a41b4802d9ca8609e5407ef7bce0b49c1f08210bd846fc,-0x71b5a726de72be303bd6bb69aa24e134ffeeb4417b25527d625f9ea5ffb988,0x5b1c75106a1bfb864919df369539e42913e026a08debefd3ff2f79f8b5b1c8,-0x4060a9ff6de2a21f29d44531d810664f637ea0e82afcb7639802c35ac4a280,0x281c06b5a1335bbf95ea86afb0a5a56417a1f51fe10862887675257632c360,-0x160438a20bcef2ce6516c79c499cc98b15186f87882752931634c9f6fa83c8,0xaa17008bfd98c15114039aa3edd4685d2b56fddebd2dffc2e878c9129dcc8,-0x48137c5b7cddfd2af4c63baf19cc3449b7e54915fb4b629662f1807ad0b27,0x1ab89f58b49ee6edcbb91193dc744c694576a268693302bba6b0498a2c5d3,-0x8a1f9f4698430d9b53c2017805cf330ac84700deab23573117b327ce5b06,0x26b1ddd2fd81cbc172abc9180d4bca80da0a3e6a02cd5d7ac1c55fbc1b66,-0x9580e6521a227611446bb91d6e4aa4d602d6f19da82c4ebbd3724b00bdb,0x1ee5331e52dbafe0f8055c15a00cc42e02b7cb761c5de0f9b0c9d9ecc0f,-0x56ab21c6e535ffa0f9ad4af63b34ae560a455341069f24f18cfa0da9b8,0xcc259639c32d3e0ab4650c077cdf788daca170949b790266941276078,-0x18ecb936846dfe5cd1886580a5360a7bc15d60ae0d11f522df882d1ba,0x27c8216e85bb0453b7f0ff1335a8a2ee61e2fa2e2442382c53366562,-0x32f350a2830b734f46f2654341f0715375ebedfe8d9fea71637ddcc,0x3339459e86d73065e8d0d7a5a7bcf4b34df5bc1cbcf37d27914e8c,-0x2758942b0d1f0d2fc7a5b620e479c55327124c2cfc8fc8d35f90e,0x165358635a6ebe9d0ecb1a3f853fe867a262a4d8589339f9ff56,-0x8f7c1d92ba483f1a811d5beea4160c561208b1f156fc0e0710,0x26a041d819d9a2b264dbedd88bd35ca83737c3a305b4c1950,-0x67bc5c1232a4fd65b2f1be2181a6c756bc31d47885fa1f3,0x9d7c5e8150bdcfbea70538c45b7b382fb1ade600de66f,-0x758f10caaf324c71c8a4be2ec9b30fe0fe09d341216,0x22e1bfb6dffb53911aa1972e19b754f1dd9e0c8b6,-0x2da4f61e8d41d352dd9f83638b504a21e3ebf7,0x750a9f361d9f7c2676693198d10bef9fdb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 23 84 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 84 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 51 indices rho q26 m26 26 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 51 indices rho q26 m26 26 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0xad10dd7e966b55cc84a82f2d05f1,-0x417b291438fc0e0ab2f3550f6d4,0x18261ca504d4dcd2208a46b6ed,-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r27 : List ℤ := raw_ints% [-0x1ad32cfb3659073d17b4f506161a8aa2bcc35f53fd38a6e00000,-0x27ea66a64b3fe03bb55f3f8a5eab78cbf1ed4ae87c14dfb60000,-0x1c198437d75d71dbd651d6146725527acb58ed27aed0f5ad0000,-0xc73dab69ea53e24683a36913b3ed6d996f8e5e2763f3c1ba800,-0x3e6301e0b91c6415a84380d011383d0aa53709e76cca7346a00,-0xeaf67004b68a593783a695bc27a893b1ad6937f8bbeca98680,-0x2b2f704a07258856df68dff45a248368ea7e2b21f2fb6a5260,-0x65a9d419c82bc974984abc53aded1be7f400d24c3015d99d0,-0xc2dad8e0cb6e74054f25752ede7fd35444b9b53fb3dc7e90,-0x1339720c8d560fc94bc7626b953e2abc3667e17a1bed06b0,-0x192ea80be0bfd7e0415bcf888b908dbaf77fa96a01263f6,-0x1b7dcc642b6652175ba0343645f2de4d7bf03cfcf17189,-0x190d23ecc64b997805d9d10bf06c2869571eef81cc00e,-0x1308842cdaafb0b7a48a55882e63061784636a6b21d7,-0xc02a23455e8feef52921ac6a52c0f706fb02a0015e,-0x63ffbee9d92d616d46ff0081bc5bbb29ebe928cb5,-0x2a7128fd0b910f1412e2892518f6d299f6b79a2e,-0xe73ad5f9a2aa61931d6cd24bf32cca5d1068fb,-0x3da464344e1001deba28d66ebd68e42b65c4a,-0xc64606b78204803a8b693f7acc609e133b2,-0x1c4405602f56cfbf982a68edea89d995d0,-0x28c0e0e1aafbeff3252225cee217a7be,-0x1bed94b89b4fc2afdc1030e21f46e6]
def m27 : List ℤ := raw_ints% [0x0,-0xef343a980bc930362bf8bf9cbc7b7a929f0bcb6574bebe53c1f72d000,0x17f9bc56fe5072b50801f62f0450b87fe750b38de33675ed49f8c8e5c00,-0x128bf451fb523c7b145312cb0e3c204970b44743022861824db057898000,0x9377658e73e59c89e4a33b2db32db321e861f83d4611927107ab62feea00,-0x34e542f3d03ab1887b4ffa174ac8e84d63f31fea9dfca261e72d4f0c33a00,0xe96b78290088f3791d946fa59516eb16f1c320fb4ae31abd8e589d76deec0,-0x337d757f6150ef8722fe96bb3bcd1a3233c0a09183e5616c0c310b010cf4c0,0x95471fd6c281f0af2dcaa58637f83724f753ee1ed49d0a846a19a4cf329480,-0x16a50a0d0b12c8c4bf128da8d077c4c85cad06dfb57ba82d7a7f24ed5b5de80,0x2ea9797d59170d2221079e97b4b522273d89d019978747d4774410c749d6ac0,-0x527ff9f92f6744963a9079ea79e75975154fad2328db39a1eafb534184a8ac0,0x7e299f8d793a2ba432fc2b37d1c0886f173169ab9f72fc67e6800967d876080,-0xa7e73fc6a561663fbf5b5f4e4dc212b485c5fd43959036502d0380e77e94280,0xc35db4d1bc2bb0bce63a6513e36b5b941fb45318a1e371f19bef1af59739554,-0xc76c2737d2eb888eeb892e0b8b98aeb8cb7b75b547ef380ae9d37cdd4150fe4,0xb3003d9fa62dd3adaa591c2c4a940a4a480fdee0b61b280493c24aaccc3b058,-0x8d7cb717599b567532c60963e79eccc79a6e8b98e86d8e8c83e515a95541898,0x628af1d2af28015c9edb6c546151a68adff119d927632df774f2b27e780ae50,-0x3c772b8c2fef1793bb1bf72dc1a9a1e31424c076f1055bab9180568fa6aadb0,0x20a8173e5ed60976a2855870593154f8f45ac82bbb6b252049e0ab2da75d658,-0xf7fac646c30695efb50ba893f507997ef46e67cbe5369fb0500c8fb8e53158,0x672b66bfd36aa3f49a36385121442b8327d048374a4894c294413d60280791,-0x25816ed82437790334a81dd546222149b00114718991b00206876e7451f5c5,0xbdd72ed3c24903c35e33379f8b3869c31b13fd2e1ff075e36827433f34bea,-0x33ff97faad90e096579623e6714c995df1c0cf4aef52d0497d3f21656310a,0xc4183b25a4f30042ce9e8320ca474475e04c7629954fab0e2c1455bf4fcd,-0x277a70f649f24f34b26a2238d0c6eeab7f3a39306baedc59e13cc43e98f9,0x6ba8ec8b30c47a947a9434eaac3856d9101282f29ce7e2b4b4756e5e348,-0xf5efc2a6be01f5624d4c09c1146c16a0a84cd2ff56b3afd9d53e966e88,0x1d0ac075d396b33384113cac169d00690d7944969a81d30e96791bfa96,-0x2cb23a8f6c1d6fac03c04b2a8b71c451af79d360c66f8263ca0d80b2e,0x3701d89ba79f4968f45b6504d4e7181f7ac31c5ec5dde03fdf9071b4,-0x34ee7691d0e77057f7f3366b67c3b0c679eaad1155ae1a58c9a5a74,0x26bd727b7a563f078f01aa3c2208d70bb22332895fbf2b3f44abd2,-0x14d65d1edb3ba3d66ee2bf841738305ec2e2bdf03dd0afa47d08a,0x7e33ee9e27ea6abf61ee4d62947ffca2105fe9a6cdbbec41cd0,-0x1fcd00fe12456054bd0c6cb3d8fe460265dba8f45584fb4c90,0x4f54201e37f72b8050303a3bb510024fc727e47e41b68ba5,-0x6ee0cd3ffdb744a86ab0db3aedb512c1eebc4f6fc97289,0x4b6e378f9fd73fc0e1bb7ecc324afb999373c833169a,-0x1428661a30294a93b4a9872d5d87b97b7a7bc27e7a,0x176c5d7e66dbd613240497cc7a23f6757f04371,-0x3461d2ec2ecf5bb30e64295fd9758a22bed]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 23 86 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 86 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 51 indices rho q27 m27 27 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 51 indices rho q27 m27 27 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x1bed94b89b4fc2afdc1030e21f46e6,0xad10dd7e966b55cc84a82f2d05f1,-0x417b291438fc0e0ab2f3550f6d4,0x18261ca504d4dcd2208a46b6ed,-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r28 : List ℤ := raw_ints% [0x4542c220a994588ca5836b3d253cb56ecf4d15d657e9bc1400000,0x670591d4c7481574910d92edf734b51ce822ae99bcf7af7e40000,0x487edc0191185c8acd385cb02d1a46f8d2d5bcd3cba4f93a80000,0x201ce3fc4edafb9a1ccee39b58046708b968d6890ae0c209ef000,0xa0ceea19c8d71e0240715f335d42e032a249e503ee1862281400,0x25d5551cc1b525b5c7292f6bb9a7bab48beb521f0a427bd65d00,0x6f3283160b6ad38e6924be2de6021f1af997976ec1fef85dfc0,0x1059e173313c205813c901a0c6d2b38ce857b77b5ef2b905e80,0x1f51d6e680827d9c28b68df489988067796981c24bd5997dd0,0x3167f7a9209e8297a7f93944e6981e611e697a747a836b2b0,0x40ab703a04d418f9d4b2970b338f03054f410b0cfc613274,0x468b0e2665e168a923fbcdb31b3367e726b1721786a0d90,0x4039eab68e0b913f4af20c3760c159266f46a6bc5914af,0x30c05c5c45a066bbb15e8f4c6d1e9825327eec673168e,0x1ebb4870fb96ae89228eea4111ef000b568a4f903295,0xff976cd480964b832cb4c113d65b334047f37b5c3c,0x6c59459cf479c1aba29fde661f23ae4c8623217bb,0x24d85ff2b151a2e6d361268fa3d467df0997a61a,0x9cee9c3536ced594dfb6caeaec5ba8d14188c1,0x1f7fba605dd06be2f9f6a9a2b22f1fde31990,0x47b932e522ae9b0996a6c28e9e254d74086,0x6736d30d3697428f7098f760b8b4e2e4c,0x46955a0e02f0ce540c0093ecc7d0036]
def m28 : List ℤ := raw_ints% [0x0,0x1b18eaa33955ca7622fb2db4c159fce29c04560a7e399b8f7cf90019000,-0x2b2b41543a3c11a75444756ac6d1b302caf37d841532b5be1612ec206c00,0x212a313a601aab122910807afad0224da1bcd3cc94f8e1290e98bc988d800,-0x105cf6065144e8ac9936055596dcbe161ce0724373a326471cb73d09436400,0x5d35b2b8c80fd4a6d3a5466470aa3d34fa32459831e804dc2110c54f258c00,-0x1981e71cc8abd7fde78fb0856b8654fa02771ff1607be3934e292d6ce82c240,0x594b8c482486191effb4d116f5ed76562aaddf967d1b80f834558bc5e9ad840,-0x100ae24a3fd9cedb07a2ff0fd038c08d6744f7a56ebd4eb6ff67e945edf6ee00,0x2697391ac49c4682044cc1f229835942a12af1ce9c840aac4aae39f603d80e00,-0x4ec78e7b5c9d8d4abf18ac6525f255ea86ea21cfcb33e9096e0441a924ae7a00,0x89ec4c6f2391c767ac0645dbaab52813547a61e97585030ab8c1369387a3b500,-0xd0c0bc70226843d6cf5597e7ab5a2a36ec3772cb6a4a8b2191cc10182f3dfc00,0x112d1dc815bd6c0077849609bedf1dc907d110b640401035c4f835094bfb3b200,-0x13c22e936c81a439029713f66d718e955976d0a4de0881a6451da18daaab44b4c,0x13ed5aebe6df79ee253acdd47d5d8b2861ee4f1ee30a92f750f568815e15f2f3c,-0x11a90d6011ece58aae143b24e318f892b52ff24af8c8eef8144c55f2d08fe3a88,0xdc5c7f9eea35521f5d740c39aa6204c5a6e36c4c22a53d06aa9148fc93f060c8,-0x974dcc5e533f2680fca74890e8756e49104e4701eb157af7b9f377b0990f95a0,0x5b72021f2992fec1317b035d6ca59230f4587b0c55a02eb1366330f0a8e0ff00,-0x3099ae84baa101c3c54f2fc8b1f981a312eebfddb97052eb449232670a573508,0x16ac7c9e59e0dfbaa04fd07c238c2b79984062e5afb1dd934926b27c634a7008,-0x943270563754149b9f08b7817165b3f29efea0cad10645c89f03d508740c937,0x34d4de57e351680596031177ad7a0fd943c9103b168ceefd83ed5ece27c9823,-0x105deabb9ceae997d3af525d3ecc9fe467e15ab79bda64a42603f9b7634f666,0x462185f45f823cbefed411332eacf196cec355f2a9cdaee750b2c2a90148c6,-0x10223f60cb14386a8ebae5c3361a90d5529a6d082ee7f27ab28a072d64d7cb,0x32a06d46c2cc355b2b913d3cfc3e13482ebc172a3380c1489f487ce7fb03f,-0x86342cb236d070ed40f30aab8830281190c04d601530c39da2e7f3b3fab8,0x12947f370aa61c1f6a9a356c1df841b492f8d6c4056eca3355551adc5178,-0x21f2a851104249f056e5937774f1bdfc9d61f839049fd7267d13090881a,0x325e241db12024843e76993c5d66452192671965a143b4326e736d8f42,-0x3b8c6b1a5061145199869f0b89faee75c571aaa10433da84e41a1460c,0x36d3ea8ca8bd448db4849dcf9eecd8a76adfdcc7f8891c75620eeccc,-0x2638b44428af828f8bfb38e098c6ecfa7831847cd5409d1c1a31a8e,0x137b054b84421c1a155c2839b59263ffbb6e65ec66f2e3b6c6a9d6,-0x6f23e9de6af002fb6835fc95e79cf73f943424f06e25ac4ec4d0,0x1a340ae6f2375a1e1cf92a5de1c4353bf84fdf3e4999d16ad10,-0x3cb0d750690f7d6bf398d18f550d607bc9c8e24d021e29243,0x4e1293342b04f5947ef8507f6c2b9e964b55a63846fd5ff,-0x30648c1132b71e0da60e3768daed857735d4e489c5c76,0xba54ee2cfb318c90aeea7a61815ffe49f181523516,-0xc042f52813ed4d52a88a8e0e937c37f1a9b8ae7,0x17700ecf1c1b3bead820bf3bd71f68c4ff0b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 23 88 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 88 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 51 indices rho q28 m28 28 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 51 indices rho q28 m28 28 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [0x46955a0e02f0ce540c0093ecc7d0036,-0x1bed94b89b4fc2afdc1030e21f46e6,0xad10dd7e966b55cc84a82f2d05f1,-0x417b291438fc0e0ab2f3550f6d4,0x18261ca504d4dcd2208a46b6ed,-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r29 : List ℤ := raw_ints% [-0xaf0b7b1665bd108d29e1534a807060d91ad0d7b783eeca27400000,-0x1044745d2d4aece00934873586ad899be6dfe15969111c8d2640000,-0xb71618e029aa941cd289d2a73d186882dcc5e085868bed7b0a0000,-0x5111402d3bb309523c1f73ecf105f95a239a42cb8b0af3c7d87000,-0x195c6417c41889302137f95962aa5eac15d98ff61f9f775e7bec00,-0x5f6bda0177e5a2414dd5ee8ed2ee1a9b1b936064313c03d3bbb00,-0x1185031a84c99ab323e09bf7c6e57bdd8e4aee86f7c36c9540740,-0x29323df8442c3c2885d73681df93a437d5f3108876017ec73220,-0x4edcd6a4e34d772b809bb8db3e322b9a794d7d281a4c7577420,-0x7c5326efd787236e8f841aa104959e62d2ba6c5b00e0209970,-0xa29f35ac910758cd5be9ea38881e928acb22cc53056dbb054,-0xb1429631348be0d02c8c36da12302f7ba6965f0f2ee95b62,-0xa141f01fec3eeed835bc0586b84b0f74b339ccad8f5c0e8,-0x7a4c32eec9264a41789bfc660b116fe699d44fdf486a0d,-0x4d05518f0e86dcf27613262aa87e70013eade72d4337e,-0x27fec1e4a703c3a3647aeda02e41afc0bd11a4b6adb5,-0x10ef8d47d213daadbbf2954b0fa1af9b716d2b918b4,-0x5c094d06287ed8e8d02f98cf8a2fe8de770dd8c4d,-0x1877d67857aaea2628ba677643f48c7161b432c2,-0x4e775a528724485da58421421fc0d0435a5dc9,-0xb26374af248c93cefdfed2e8bfb1c161b2e8,-0x100450ceac252fd18f4cad5305b45bddfb6,-0xaeeb495722a2b1c7acff7d8326d82908]
def m29 : List ℤ := raw_ints% [0x0,-0x311d2947d7eb7ef61f6742d79e731a5abac7dbf304c869f41283502d5000,0x4dbdf75820ced30de6cda96f429b0484414f75a07ed3e96888024bfac3c00,-0x3b53a929cca094975c2b0df0f4a5c4b6a5f11ca19e3819d22778385860c000,0x1d1136a05cd0a8d5a481d453e25da7164daa15eab72a71ac37798263d102a00,-0xa45f6bf53dcedb5161426f479d4154b83f16d08232a553b23c217ce855dba00,0x2ca3d6a8519dfd1cda9cac898ea898e435e56c2272ded4cdf62b2838847f60c0,-0x9b0846da576908b20d309d12b42bd2cf46998119555ce633efa241ba4c8fdec0,0x1b9f046aa32210646903ea6fb32d3f78c9f3e5b1ab66a5078837432650b650a80,-0x41dd615f243aa7797edb6237f07fcf63e3b3abf8f554c5163564691b5dbca5c80,0x853a8b9a5964efd5144128095ee60c2d8246d3b287e2a07e68c36061ff4fa3a40,-0xe70314e38dde5b2f4ebb7b772d17f174204c55f0581ab4e468ecbf70063198040,0x15a1edb6aed6bc3e3abcbe3bdc8260bcb8907cc83658c31804d7bfa18a585d9d80,-0x1c2d2dc86db7f5df7f4fa6a55bb4e5c0ac39f122c10292bce713db370dd26cc780,0x200cbdcccaf5fb055dd1b6cfa32bbcc2d2251e1fc3c782b0fad9a331e5b745ee14,-0x1ff10335a7aefd69b6af8c01a5a3be00a87020a42148c3aae75d04128ef378c3a4,0x1bf4570da2c1cf071ee6817149d2398de2c838eddea2577e1b87fbb26759e3ec58,-0x158326661884d88af284b4ec109ae9e741f0f59b32480b5cc4af0b92fe87e11a98,0xe904c31bb3ca08fdcdeb32b73fe4cff246f7936755f4d272f9c64b457c4ac29b0,-0x8abc4476237b7b8c0378d766472743969c8b387c9eeab09a683e7b6a41dd30a90,0x4890c323206a5376af527726f211cc05851ca008b710b59bd0c6d9afe63046118,-0x21486064f15287cc3bff261aff9e5b35b62198be999422fa8db7396dcd93c7e18,0xd59d55d2e7ed5272d3d5d57054a3b8676eaec5b57341b718267081f9b10da081,-0x4aaecebde67e61496a8a6e3914f378b4253f899b6570440c3ddd154a0a3d8a75,0x16a849eadbc77ac777abe11fabe50024a473141547c7c716f4727555b5b9898a,-0x5eece6de9f41b2abc2e85345c253246dd4eba096477c0c52d2cf2558b430caa,0x155077a0f15dd29d680f3de0cb24bde0aea8edb7eca234b02d841d83d517f5d,-0x4126b85124a966bc979de58c28b752fcd50f92c2671c2946ee1de085e95a49,0xa7dd54e3c9b9c5207af1798af1b7f34f6a7a830d67958628ea2a3177c4248,-0x16886d7d2dc4ac6072b665e0512f000ac2165a009fb96aae53f45267fc588,0x27ce561d2d113c215bdc8db2f86c258c5cde69fc9fb5209015312b384a36,-0x38ec4660d65d3b9d0543ec353f518c1ff5e27550f0d8c58bfb08b48574e,0x40a2325484f5b0c317b2c0990bdbb1d0f918c9fa4b7cacf1189c153874,-0x38ec3f85ef0f0fe022847106f8b0e3101bfea276ce0530569993aff34,0x25c887e3672429e155ac5f7888e975636005814618a261141a2bcfd2,-0x123d9013d301a500f2abc00fe5787f37bbfa54971af623705f4a98a,0x61fd0e95ad45c37ce53958c8fc635c754e55cdebc98ff928fb310,-0x159b7beabba728f9a32bc27900b15a649b62bbe54e230bfd00d0,0x2e7323f87d06e5cf274f290fa7e3fbf5c4c23eb9281cf56a55,-0x36fa36816f59c165f9bd6e06505e848342c3e945982ab1f9,0x1f0abaeb31c1451e877ab6ff08563c08665b733d3cc33a,-0x6b9e8429cc4c536e7b14d76f4a4adac5109f4f8011a,0x6299f4b7b847c9e4b75c60d6df113469182cd301,-0xa7bfb074e1db7f1e2f1e653bc7c2b118e13d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 23 90 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 90 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 51 indices rho q29 m29 29 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 51 indices rho q29 m29 29 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [-0xaeeb495722a2b1c7acff7d8326d82908,0x46955a0e02f0ce540c0093ecc7d0036,-0x1bed94b89b4fc2afdc1030e21f46e6,0xad10dd7e966b55cc84a82f2d05f1,-0x417b291438fc0e0ab2f3550f6d4,0x18261ca504d4dcd2208a46b6ed,-0x8a88ac371794e0c378b2d0f8,0x30257e20c8946831bfa2f1c,-0x1029f1363f2f49464e7ac8,0x5388977603225d232e60,-0x19d58d441ddcb938e8a,0x79b368169622dc70b,-0x21e027e0265bf6d4,0x8d6822abc2e85f,-0x22344013cfe0c,0x7903e51150e,-0x18020ae9e8,0x429ab1ba,-0x9b60ee,0x11e75,-0x174,0x1]
def r30 : List ℤ := raw_ints% [0x1b1cb5cd7057dbd2a59f4608dd4aace5e819f232baa9402d87000000,0x284ce7f1cf28d2c2dccb55437f4a12894da559160eb4cbe653700000,0x1c56978650bc8567d15a65a5d8c55b611295c64a5d65fc2b19440000,0xc8afa3f8c1614c33d09082baab394b7e52771a33c15060ee6ff4000,0x3ec19bafcb727daa3d5e3e46364f35ebe3c96c213782635033ae000,0xec04ae40ee2d9a6ea9ed88d63f3e20889cdc208f0f0fc7dcb00800,0x2b501a2c560991195cfa41bd6831a7b750d126117a2f7c931b6800,0x65cbab182799e66f4af0630d92ae5ca415759922bcc1cf7c29740,0xc2c2f14c4be6a939ca36fc83b96ad37cfc0a5ba8157b7952c560,0x132da9ecb9fe5a868f08b9b0bb1b26d87e99b07463a9313952e0,0x1911ef5e96c74023dc2eb8dd13114d834b8346affd54aad01c0,0x1b4ed1211faa74ab0615251a18cd09e3f76454aac8d6467434,0x18d2fab09481dfc416cb4af7ee5aad3d4875a657d321c443e,0x12cfbeba3426733410ec0745f8da94dea653bf9b51d348e8,0xbd63c4737ea9c6ff1312b7cf734be21a8f65deab87b383,0x6240e3a29b349116eb9aa69ec74ea42c4be9a28c1097a,0x2990085e76477fdb792c921c730e0a10abb2b268b18b,0xe19ec76b567d42168f4a5f092bfcda7606ff9105ac,0x3be8e554167857e727825ff07cfe9fd5b7cfaef03,0xbfdf303c33a53801b1a9694c86158c1462b4536,0x1b3962fa5a269cdb06d3a049d9a10cf14ba9d7,0x270c71b9b6375de35223bce29a458e8f88e8,0x1a9b73b027b01e67f4fa57c9bd8bd47b3a]
def m30 : List ℤ := raw_ints% [0x0,0x5904dad2375ad61e18eb2926cf309fc4728a3ea878ab400a618e015221000,-0x8c078df2cc2a47e2c6f3872daea71c4a4ceec0ecd096170d768429b682cc00,0x6a2a5a80292b0f48a64d249efbfa31890e5dabab1cd98fb2f67f9c5eb9d5800,-0x33a9bf94e4fcaecb2f407c3e3c8c25896d498318d8de6ffe30b004ae066a5400,0x122147a23b2f00ec75935ac0a758c3f9ec1255ac7b86179f3cc55f8482972fc00,-0x4e320c45dd97533dcc0aec90ec6deb1d0b93cbae06c599411b53f852eb6422840,0x10d7653752f5cede1ce9972667b9b753defca283486137a1a5e074f42e45472640,-0x2f9e4268077600f72130cc8d86362ea7e535703edd1cf1f77e43db2177990a4c00,0x7094c03fc2300380e645d6ed098257a51eb4f5902289969b05e0fd64af68beb400,-0xe1af7ecf487ca1e6bcdf9bd44ef62b1fdb07cb08fa2ad2a34ed056ee087bedc080,0x183a4c7af4aeb1522e16ce12b5477e5a0562ea6df6e27e4193a75addd4b74962d80,-0x23f0af79f8b51712dff320cc3d385c64e736c07b635b3a149ea93993e358b0a2700,0x2e52c3e9e404a241f444b96ce6315984bf481ff01a9baf25c6375330649e203a500,-0x341c3c8c4c7a9ee043f254391e8f8caa0bb2d3722f139950a8d223254b0fde21e8c,0x3354406f22a74672fcd13a9820de6415354f2ac88b18b9fb69c517d50616c2b077c,-0x2c5e3df4d682a29bdb2a5512989246c02e402d7a0ce9066456b047d1df5b852af88,0x21b274ab2fcaecb1d4a387b1e3835da7fd965e9c8572ed02897e829a5b2f6cfb3c8,-0x167efc4391fd50614d61329f79a7268a311e08447492b2a84cd410b396cebddbdc0,0xd323079559958f978728c8abb8b54132ff6e1d17af6ad413502eb8f7c537bc13a0,-0x6cb2b70dd3c00b8ec4bc0a0ee6c5a8980fdd4d537b04d982631c7224211e7de448,0x3104ad4190d673c83eb60475e268b858fb77da91a583a8c0c6212b0ae7f014b148,-0x134f5ab46a5c97e20160ed8b2d800047b8637e996e831e69675600f64670095347,0x69f0457d6b14c62d4b17ad35dff966e6357e91f0c4a999de79938c743ae10ae73,-0x1f79c50f570042863f983a3d372d53dfcf020429214b5cd0a549412e7abf147c6,0x80f00ac63961f382006432ea6cba40edba45f89c8f088aaa5951ccd24762ec26,-0x1c41b9244638d97e3aac7e48d2f473811c8287cbfe8203680ba4d8235e1674bb,0x54218b161594c4f18739c8fe0be9de3cfb21afc178ebfdfff74dae337fb716f,-0xd2ab6cc04d5e3fe17a5e5b71dbda630c9094bbdea63384e3eebde60433cfb8,0x1b6a0ec10bbfb954b422407e533d9f09ef666013ce44f224a8c57b4085e678,-0x2ed0ead19f17b9078bed3437d9c70f30741021d7cb1d159e4411396906e7a,0x4082d6e4b04931fcb5c79f21da7b148d8d06f0cce4e94a624e28373a1922,-0x46546a231fc4abdbeb866ef859ef4bc18ee9adc72d89cb9cf55cb61ae4c,0x3b3a6a14241f8f71402d1611a70b3ddbbdfb8d604bd49a9ce3ea38bb0c,-0x256b51e78111488fe5b4506fb49dfc5782234e473f975a0f65b0eb30e,0x111ab97595c41f2bdef59d33c8ad6ff224ca55ca5ef602d78f168756,-0x567c547a70c59d25a57691814b8498011eee236a98739936fa8890,0x11d46c2c1b4c0b9153546a078c74b1a7ea447d0c96f38d50ab6d0,-0x238ff5acbb6cbec48cd1d6c3cd0689e325cfe0decedc36be693,0x26b74749e8a787cf5ca74d882f1b93b2d7df1a0ef7ff0e18f,-0x13e8a962f764718de07a5a331809ffe2102e72f24fb0cd6,0x3e23de28bb7d542cf3ec14ca43028e4f825d6963a776,-0x328d6fca756a994284d3d6ea9dbc6fe198746e8d7,0x4b05212508edb436e4733b581a1b71f34e13b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 23 92 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 92 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 51 indices rho q30 m30 30 2397969815062011837143777280000 29=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 51 indices rho q30 m30 30 2397969815062011837143777280000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_30
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<31) : intPolyRF (mz e)=rfPoly (C (2397969815062011837143777280000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^e) := by
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
  · exact moment_source_29 size
  · exact moment_source_30 size
#print axioms moment_source_30
end
end CatalanCore.Li2.NVMod.FamilySource.V7C30
