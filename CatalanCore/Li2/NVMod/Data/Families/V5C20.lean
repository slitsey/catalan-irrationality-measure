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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C20
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,20,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0x1201d0caf06000,0x1a5ea4a2f09a00,0x11c6e3432ffa40,0x752430dc68810,0x20f9635d59620,0x6b8f9de427d8,0x1069d2de7c94,0x1e8dce610d1,0x2bbcbb9ad0,0x30292e71c,0x28794d98,0x19803a6,0xba9f0,0x3a84,0xb4,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x7,-0x38,0x15,-0x15,0x34f,-0x4410,0x2cee9,-0x22f27,0x22f27,-0x93e0,0x5377f,-0x5ed4,0x4c69b]
def rhoDenominators : List ℤ := raw_ints% [0x5c60a0,0x2eec,0x420,0x129,0x8,0x1,0x8,0x31,0xe0,0x6c,0x60,0x21,0x252,0x8f,0x36be]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 20
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤19))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤19 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 20 omega5=padCoefficients 20 (omegaCoefficients 19 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 19 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 20 omega6=padCoefficients 20 (omegaCoefficients 19 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 19 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 20 omega7=padCoefficients 20 (omegaCoefficients 19 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 19 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 20 omega8=padCoefficients 20 (omegaCoefficients 19 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 19 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 20 omega9=padCoefficients 20 (omegaCoefficients 19 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 19 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 20 omega10=padCoefficients 20 (omegaCoefficients 19 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 19 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 20 omega11=padCoefficients 20 (omegaCoefficients 19 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 19 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 20 omega12=padCoefficients 20 (omegaCoefficients 19 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 19 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 20 omega13=padCoefficients 20 (omegaCoefficients 19 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 19 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 20 omega14=padCoefficients 20 (omegaCoefficients 19 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 19 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 20 omega15=padCoefficients 20 (omegaCoefficients 19 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 19 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 20 omega16=padCoefficients 20 (omegaCoefficients 19 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 19 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 20 omega17=padCoefficients 20 (omegaCoefficients 19 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 19 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 20 omega18=padCoefficients 20 (omegaCoefficients 19 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 19 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 20 omega19=padCoefficients 20 (omegaCoefficients 19 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 19 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x42,-0xdc,0x1ef,-0x318,0x39c,-0x318,0x1ef,-0xdc,0x42,-0xc,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 14 li0=padCoefficients 14 (liCoefficients 13 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 13 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x37,-0xa5,0x14a,-0x1ce,0x1ce,-0x14a,0xa5,-0x37,0xb,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 14 li1=padCoefficients 14 (liCoefficients 13 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 13 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x23,-0x4b,0x5a,-0x2a,-0x2a,0x5a,-0x4b,0x23,-0x9,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 14 li2=padCoefficients 14 (liCoefficients 13 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 13 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x5,0x1,0x33,-0xae,0x126,-0x126,0xae,-0x33,-0x1,0x5,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 14 li3=padCoefficients 14 (liCoefficients 13 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 13 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x3,-0x31,0xa5,-0xf6,0x7e,0x7e,-0xf6,0xa5,-0x31,0x3,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 14 li4=padCoefficients 14 (liCoefficients 13 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 13 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x13,-0x5f,0x4b,0x14a,-0x372,0x372,-0x14a,-0x4b,0x5f,-0x13,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 14 li5=padCoefficients 14 (liCoefficients 13 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 13 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x33,-0x19,-0x2a3,0x672,-0x3ea,-0x3ea,0x672,-0x2a3,-0x19,0x33,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 14 li6=padCoefficients 14 (liCoefficients 13 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 13 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x73,0x259,-0x92d,-0xae,0x1b66,-0x1b66,0xae,0x92d,-0x259,-0x73,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 14 li7=padCoefficients 14 (liCoefficients 13 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 13 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf3,0xcef,-0x4b,-0x5646,0x48ae,0x48ae,-0x5646,-0x4b,0xcef,0xf3,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 14 li8=padCoefficients 14 (liCoefficients 13 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 13 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f3,0x3331,0xb35b,-0xfea6,-0x1fcc2,0x1fcc2,0xfea6,-0xb35b,-0x3331,-0x1f3,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 14 li9=padCoefficients 14 (liCoefficients 13 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 13 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f3,0xb2f7,0x5804d,0x6d542,-0xd0c7a,-0xd0c7a,0x6d542,0x5804d,0xb2f7,0x3f3,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 14 li10=padCoefficients 14 (liCoefficients 13 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 13 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f3,0x24c49,0x1f4b23,0x72f822,0x5b5756,-0x5b5756,-0x72f822,-0x1f4b23,-0x24c49,-0x7f3,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 14 li11=padCoefficients 14 (liCoefficients 13 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 13 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff3,0x74c3f,0x9b73a5,0x3f3f08a,0x9afbd9e,0x9afbd9e,0x3f3f08a,0x9b73a5,0x74c3f,0xff3,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 14 li12=padCoefficients 14 (liCoefficients 13 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 13 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 13 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^13 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 5=>omega5
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 19 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 20 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_5
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
theorem cache_li (j : ℕ) (hj : j<13) : coefficientsPoly (cache.li j)=liNumerator 13 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,0xf3abb7f1c1b04400,-0x135ef86414bc1d4300,0xbc08414b21d2279300,-0x4863fb8180eef4af2c0,0x13d962b79d47df2b7800,-0x41fb98d111b6937ae170,0xaca09a20b4c84b037670,-0x16c720ac0ba8f537b07bc,0x2779078ee9c574ae9ee2c,-0x38d0aa03fee8a8dda9eec,0x447701fd7c4919fbbfffc,-0x456b29f765f524a068673,0x3b5f19afed4852214526f,-0x2ad84e601d67f99bb8b93,0x1a0a302809d80fdb89467,-0xd4656cbeb37cd1297c47,0x5a3b286a3c5daf2fa4a3,-0x1fa4fcf49b4d17050757,0x90b02fbeefc5a70c7ab,-0x2118d669efe9460de19,0x5e9ea62f81e53736ad,-0xcc2beccc9df7753a9,0x13c5a38ee6665ed05,-0x145f950526b7e371,0xc45a1e8f5f10d5,-0x35d25c8465751,0x387a1e984bd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 15 28 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 28 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 33 indices rho q0 m0 0 786174614646220800 19=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 33 indices rho q0 m0 0 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x1215bea6f160150c00,0x168d04472bf9f961900,-0xd674e680f61c4f5a900,0x50d4ecbb77ee405a5a40,-0x15aeb4ab31e17ebba3300,0x4674606eef28c765cd210,-0xb404b7878fcaa768ab010,0x172cf2663eb3a3e69b9f24,-0x2724f08d18bd556169a054,0x36d9dabfa73d4e5ef751ec,-0x404426bce9c88b7db7d29c,0x3f43fcf3f19c2feb7bfc8d,-0x34738494aff882277d84f9,0x24a030622939d92edb20d3,-0x157ee444f3dcd63e3f3dcf,0xa8eb0546d4836eae0190d,-0x44f315ec4acce16d07f99,0x172916e7c8f4d06f37efb,-0x650c44d42769a0b06777,0x15f4c02f6e0a31747a9f,-0x3b4a30c2a81dcacfec3,0x77fc9435248325fc61,-0xacbd1e71b3a2aeab5,0xa346bac2a5189063,-0x588f0797c2e0357,0x153b84a154acd5,-0x12928c5dfe59]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 15 29 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 29 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 33 indices rho q1 m1 1 786174614646220800 19=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 33 indices rho q1 m1 1 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x1579d2663ea218fe400,-0x1a453a0ee1fec19a1b00,0xf4ec5d1c607fbaa66300,-0x5a703f143e5330c6b60c0,0x17bf873d4c81ec18714400,-0x4b7a8353a189c50f2c1b70,0xbc77819d1ac82b9c45daf0,-0x17b01da99e5a11342e228bc,0x2704efbd28722d730040ccc,-0x35426bc6af8eb413ccefbac,0x3cb4a7c2eea5f51ac90925c,-0x3a0d51c77cec10da7079593,0x2ead49c8258981d18338897,-0x1f8d66316e10b44ab8baae3,0x11e39b24f302c2ddfa2f41f,-0x877a00f9197301549e91c7,0x352524490f86a66ffc7b4b,-0x1119b0c1fd32fb5ed0e847,0x4730b0014b8b371383f23,-0xeb0bf89885d81fb8ebb9,0x25748348cfde73a812e5,-0x4709e12530f7cdaddd9,0x5eeb68a52d5d1a7c6d,-0x522bb55822f856431,0x280b16ca26aedd2d,-0x8603b9f7161c21,0x6198e8161745]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 15 30 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 30 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 33 indices rho q2 m2 2 786174614646220800 19=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 33 indices rho q2 m2 2 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x1980a9d96a607dadec00,0x1e9fb28b55dd2c8c08100,-0x118168ba2a55361e156100,0x6562fcc128d7139dc52c40,-0x1a142895561d9e05b4e6100,0x511fa1d790f42fb0b782c10,-0xc6134594c2da0f641dcbf10,0x1851eb91aa87db0ec3ee9ca4,-0x27176e1efeeb54252eb2a094,0x3401489ebfb4c503f688cb4c,-0x39b220b066776ee48701b53c,0x359f90b19990d9125e50922d,-0x29d5a79276cb0a7e6b104289,0x1b63112a124fdd81a4f87d0b,-0xf01624a3aaf1fc76c4037d7,0x6d8bef43f22116a6be4f6fd,-0x294eae742cc8d4f976fc4b9,0xcbbaa59d55cf5ad5f9c8e3,-0x3293fc122eb95c60fc2c6f,0x9e8ea017dd6259b00915f,-0x17d855b95e004cd44e653,0x2a5a7d0f71af13bcaf69,-0x3476fbd71bd1ec0002d,0x2987b50e822f0da993,-0x12251f5dc4bac61d7,0x34db0a32f70254d,-0x2004088c7a941]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 15 31 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 31 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 33 indices rho q3 m3 3 786174614646220800 19=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 33 indices rho q3 m3 3 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x1e48c9b22e52953e88400,-0x23b8d15254a5205ff29300,0x140b7c0c9994b6086951b00,-0x71e16bf9aecbf550b2d06c0,0x1cb62b968e2d8b95f9c8c200,-0x5777f943076a789b11c82170,0xd0f69288a4387eb387c968f0,-0x19140df47e7a179a96c31613c,0x275b9d4f81b018375fb010dcc,-0x330f359d56967b5ccca63664c,0x372a4e5180cfa576b67840cfc,-0x31dacc77884cfaec5783a6ff3,0x25c158e3570dc9e1811a9cc97,-0x17f23983c729e91e88d53696b,0xcaeed01b7e41a8321f3b65a7,-0x5948a60871858ede97876cd7,0x205e0163d1588be8b43e00fb,-0x98f0a54a94c3fe51a75941f,0x2439a2d1ac4d6dadb73b0fb,-0x6bcc5a9c84a4a053b10cf9,0xf4ace580d18821ebd7305,-0x196ae09c056309ea71511,0x1d2803adab65e15e9fa5,-0x1511fa74e3f0016bc01,0x83c9926892468195d,-0x14d6c1b5d55904e9,0xa7d8a8f1f4b0d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 15 32 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 32 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 33 indices rho q4 m4 4 786174614646220800 19=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 33 indices rho q4 m4 4 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x1201d0caf06000,-0x1a5ea4a2f09a00,-0x11c6e3432ffa40,-0x752430dc68810,-0x20f9635d59620,-0x6b8f9de427d8,-0x1069d2de7c94,-0x1e8dce60e91,-0x2bbcbb9170,-0x30292d6c8,-0x28793e0c,-0x197fac5,-0xba6d0,-0x39da,-0xa0]
def m5 : List ℤ := raw_ints% [0x0,-0x23f66f839702113a41cc00,0x29b20b883f08615ace2e900,-0x16fb5a7b0a3c46f147292900,0x802845ec57ffb86aad47de40,-0x1fb09c3bb2d7676ab8ca9c300,0x5e9ac9b7eea3d46c6974b7610,-0xdd44c711194925361e8d3d310,0x19f8a5ab848466652e77737b24,-0x27d16b872c4cd7f5dc55eb1414,0x32668b4ffdff7d6096e2a373ec,-0x350e4b39ade4b52ba7414ec65c,0x2ea52a2ae84f98632c9b0b1f4d,-0x224df90b3a2612982c2c4c97e9,0x1516628d13b0abb2168d035e13,-0xaccf4fb05b087609ac08edbff,0x4954785caefc7c45fa3160d4d,-0x198fb012689c97562b97f92c9,0x73b7fcb6456df1c2b25636bb,-0x1a25afbe3c98dda74754cee7,0x49d68de3d985b25de5593df,-0x9e024b08b7e4f7671b3993,0xf590c89a400ed1549ef21,-0x1048bb12f5909a7a77445,0xab9f735184f88cd3823,-0x3be8dd68cd5b918aa7,0x83648c3e43d1f715,-0x36efdfa3202c69]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 15 34 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 34 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 33 indices rho q5 m5 5 786174614646220800 19=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 33 indices rho q5 m5 5 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xa0,0x1]
def r6 : List ℤ := raw_ints% [0xb41227ed63c0000,0x106925150b6fe000,0xb01ef655b0bce00,0x481a30558e50fc0,0x1426b9e97b74bf0,0x412a2c78c350e0,0x9d6942d29b4a8,0x121203cec060c,0x196d185ab36f,0x1b5df14e010,0x16493da838,0xd68909b4,0x5b23b3b,0x18ebb0,0x36a6]
def m6 : List ℤ := raw_ints% [0x0,0x2ab4a46c435274752e22400,-0x30b2d30714aec7e1cebb4b00,0x1a61d1e2b7db14ad5c4aa3300,-0x907e239f40578aecb255b3cc0,0x23103cc439d82ebac861707800,-0x66a2cce6e6929ea946e11cb770,0xeb26b7bcb48347829887b04cf0,-0x1b024b18fe1e30803b3eab237bc,0x28797c825919c39cb4bf4fd604c,-0x320300dde1dc95294719f70296c,0x3351f605192682382e055179d9c,-0x2be9a58a002a380998877d32953,0x1f600a852a279e4243087e2ebf7,-0x12b30477398efcdd18561b48013,0x9439f5bdcb580934b057c15aaf,-0x3cad610657f211106ca8b051a7,0x145705b7ee47b58f75f66e044b,-0x5838f1be93e908c41d096cd57,0x1303992b896949f57db21db13,-0x32f03de418a113036a8893b9,0x66b6fc703161fc992cdcfc5,-0x9522c48c8bd5b96116ef29,0x922f7a41aae36e276bbdd,-0x57a23c7ecc955bd16b91,0x1b44076a3cf1a43b26d,-0x33bfbe8061c1e68d1,0x11f66056a354215]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 15 36 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 36 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 33 indices rho q6 m6 6 786174614646220800 19=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 33 indices rho q6 m6 6 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x36a6,-0xa0,0x1]
def r7 : List ℤ := raw_ints% [-0x3d80f38324c1e4000,-0x595cef6a19243dc00,-0x3bb11c274a475e580,-0x185178cfd7463cc60,-0x6c1e27bc9d450900,-0x15b39ecfeaa21a20,-0x33fcced31c8af18,-0x5e8503979148de,-0x8350bb7623cd4,-0x8b118fa710b9,-0x6edf5f18080,-0x40d019b96c,-0x1a6dfc7ec,-0x6cb8e5d,-0xd8108]
def m7 : List ℤ := raw_ints% [0x0,-0x32b683408ff1ea4b26c8ac00,0x38e9ac985b9efc2ade9ee9100,-0x1e529160df303a961f111b7100,0xa3352a4e83dd143d54723e2040,-0x26e3cd3b275e69776b1c7d1c500,0x6faec063c82ba72b5301c5ea010,-0xfacb72283c46ca8feb309a08b10,0x1c34191082eb39585dba595305a4,-0x295526db9980276c37d23358ec94,0x31e1829b94e2370dfe6c02f47e8c,-0x31eb7819a080579f4c8064b5f27c,0x29971bb752c2b1593e0172f17c6d,-0x1ce176a3c116b9bb951727e07a89,0x10b1ac2df5a3f65f40ce80da1e9b,-0x8009976e81352f9dd1b8bc92be7,0x32926f630f2210914f82da0969d,-0x104de1554a990b499e9c790d619,0x43c0dca9ed0d5d78ae7728f913,-0xded14a2ee58180c559f2f571f,0x236171586458a7500e9b2305f,-0x43300c92a1921a3d57a4da93,0x5b0f881f97058a724d58759,-0x525d7dae901d44fd4b859d,0x2cddc2eb6dc377daebdb3,-0xc6b85ff2a30cac41e37,0x145e4c2d0c32deaa5d,-0x5de007450f981d1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 15 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 33 indices rho q7 m7 7 786174614646220800 19=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 33 indices rho q7 m7 7 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0xd8108,0x36a6,-0xa0,0x1]
def r8 : List ℤ := raw_ints% [0xf32b1492fe57e30000,0x16040d0f945db009000,0xea79822ec369963600,0x5f23044ca9bd1e6b00,0x1a4f745cad7a8f04a0,0x5406397e64fe80dc0,0xc7f1ed0d1c9c5e80,0x1689d1587e7e2870,0x1f01bfbb3de5da2,0x2070ce2016180c,0x1977dc4f4f407,0xe97e01342b0,0x5cb2158614,0x16f529034,0x2b32b43]
def m8 : List ℤ := raw_ints% [0x0,0x3c38bbdcaaef46393e0e4c400,-0x428d7934de3e281b78a144c300,0x22e4ab1e678e1d7fd62cb038b00,-0xb8ad0295416681494e4c63ce2c0,0x2b3c5f253c0e54f99b3785147e00,-0x79e206ec9dbbc17665c515c8ed70,0x10c692127f8bc4398c06f32be58f0,-0x1d91ba584c853a671186bacf6663c,0x2a66758ac4e9724eda1bd5f5458cc,-0x320012b0273520617e6c1d1ce8f8c,0x30d2e5f02fff32652a4f067b7433c,-0x279f8bb2642d365a04b9d888880b3,0x1ac067711f8fb79634430dbcca2d7,-0xf0094248dfdecf9e64a7a266c27b,0x6f5b7faf78bb5fe7d32a6ed84ff7,-0x2a724d94852181ed509f6dc658f7,0xd298d54a531a10c6eb12578c59b,-0x3466dd335f00e42ff20381715cf,0xa451604d24ebd3692175625aeb,-0x18bc097c3583e199742b370779,0x2c354bfd4b2cb7e74bdb08e05,-0x37e13d3259886387ae8ea381,0x2e95a00670a135ce50937d5,-0x17060d96ddd1f964dd1da1,0x5a94698b955fed59b67d,-0x802eda78cddc953c79,0x1ea2436d47b9ee5d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 15 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 33 indices rho q8 m8 8 786174614646220800 19=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 33 indices rho q8 m8 8 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r9 : List ℤ := raw_ints% [-0x309df198528e9d092000,-0x463ec01ba8e664f34e00,-0x2e9e97ac9afe4456aec0,-0x12d9ce37cafacd6a1630,-0x53148975235725f3f60,-0x10817601845b6e0b0e8,-0x271006a8c182bb68fc,-0x45fecf0febc902333,-0x5f8c0130490c4c00,-0x63058c275f9d2b2,-0x4cd57548f9bebc,-0x2b6190782e26b,-0x10e5cb558720,-0x414a19f678,-0x76a7dae8]
def m9 : List ℤ := raw_ints% [0x0,-0x47835f160afc2363f9b0fa8c00,0x4ddefbb6b78957de418ca3a7900,-0x28332d675eac4dd19de1610bf900,0xd15527b90e8679ea3096e5493240,-0x302db77675a1e4dc4e2738c8f9700,0x8565648ba1bf4dc9cf9a1b4666a10,-0x1203e17426fe959024e365fd9b2310,0x1f1f7a09d57c57c50d339ec5616824,-0x2bb02d60046b78b8028b904f6b8114,0x325db22cc16c9fb92a7c0ba7bb0e2c,-0x3001f3941ae467a275c5cb64a9f39c,0x25f78023fafa447c32cbff5bf7db8d,-0x18ee6548abf93a6903ac187016e429,0xd9195dbb0f94d3ef8ba92cf74b763,-0x617f3870315ed0517bf1ec7c5c80f,0x23deba47214df290003a35087216d,-0xab2f8d890577e98794eb5d95c7e9,0x28ce2796ae08655f4d3b9b5b0c2b,-0x79fa4fba483ef4b99ca06d6fc17,0x11662b4946b9094d927854b87df,-0x1d4008ceebd8a50dc1100a3593,0x227375e8eda1ef343821c2951,-0x1a705c03168fd22667d354b5,0xbd6ac00472a408e186a4c3,-0x294e6e4a95329521cbe47,0x3261a0282253c13fde5,-0x9fcca1f856cd3379]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 15 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 33 indices rho q9 m9 9 786174614646220800 19=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 33 indices rho q9 m9 9 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r10 : List ℤ := raw_ints% [0x858a4d29ca1173b970000,0xc084c3b66d75666267000,0x7f715f2970deb1961fc00,0x336193d1a8abb69e23fc0,0xe1af5cb9d0858cdd36d0,0x2ca970d99e997c3acc60,0x69372e401c255623d38,0xbb86558437e66cce6c,0xfe5bf0d19ecf9494d,0x1059cf616d026fd60,0xc921abf322fef0e,0x7047c0812eebb4,0x2b1e16d557f15,0xa396acfe880,0x1223ebf4a8]
def m10 : List ℤ := raw_ints% [0x0,0x54ec00ea2d0b6a06b8822986400,-0x5b2aa629e786919d446dc896fb00,0x2e5dd74b6d8a91e869d60f74ea300,-0xedaf9eda9861cc3593bf30370f8c0,0x35cec15002ef770ef02a37aee0b400,-0x9267da2d074ce909a2cbfa115a0370,0x1369205ae19c3f802278f6e00ced4f0,-0x20e2572a81dbdcdf48e86ecd116d4bc,0x2d35d672e1ce427a09068e9b4d9294c,-0x32fa515ec7ddc241f57541d174e4aac,0x2f73b9449b74270f6757fa3b0eb41dc,-0x2495992106f92d92d402b8084016213,0x175fa79ae3ba4f6cb9e5b98dcf669b7,-0xc595ceaa7f44667cfb1bd73ae35923,0x55ea895a35fe9105d59c874d37427f,-0x1e837d9fcfbe628c745cee0c8ed1c7,0x8c1413cdeb0d83ed9fa1b07e92a6b,-0x1ffbf7c3dfc1f203e56778daff307,0x5b1f171eec6057fa9a3ef84cb483,-0xc4fb749a7b7eb3b310731cd3e39,0x13746af2ecd184990b151e00145,-0x1554e89c28f80635da2a99e599,0xf0d6a8546f974bfd36b5948d,-0x6190702bcc60a9c91faa931,0x12d7863c72feefdf23120d,-0x13c9814674e9508c5c61,0x340d9f5549c6191e5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 15 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 33 indices rho q10 m10 10 786174614646220800 19=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 33 indices rho q10 m10 10 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r11 : List ℤ := raw_ints% [-0x146a786b0dc1a3a693f0000,-0x1d6022d3939b22c63161000,-0x136724220021e98e49aca00,-0x7cd89fb304323041468e80,-0x222c7e5c5f07feacbec540,-0x6bd818388974aa21ecef0,-0xfd14fb73c3818c6004c0,-0x1c10ae129bc9ec7afff0,-0x25de1f91160512f0a14,-0x26b4b585bec2691113,-0x1d898623d5ff0ce60,-0x1057677dc86eade2,-0x634e1b73c159cc,-0x1739c8dc2b78b,-0x287d7181da0]
def m11 : List ℤ := raw_ints% [0x0,-0x64d84116157d8de7fb1a914f6c00,0x6acabbface35b558c2abfd3b4a100,-0x3589edcbc5d97a65a7fe47b4a3c100,0x10e5428aa67e6af12a7dc9937f89440,-0x3c3a147a8e1b676be54c85edaf47900,0xa11fa6110406f6a736f775ed7e8d410,-0x14fb7671e26eeb46b2b03265abbc0b10,0x22e01be93e53c64859f3ce03492f12a4,-0x2efbc99bbf900f055ee1d684a85a2d94,0x33d6c676f84f5b9be58503188c75f6cc,-0x2f24851770690f3cdfc482f9a6a619bc,0x23722ecd7f3d51b2087a3dffdde374ad,-0x160a8c93d0546ef845dc107c00befbc9,0xb4ecab92c642a0400f44cad7aa1156b,-0x4c3084f01e21b78619142bcee308477,0x1a1fd570662f5280becff5fd04c13bd,-0x735d3fcbd61abaacb36adc53016939,0x193aace8f7c9f28232e7eb59ac0f03,-0x447c011ba97f7c06770ab2a9eafcf,0x8c2a4d314ceec063fc99d85ed65f,-0xd00e8e934df8e065808460ba393,0xd42df27c24803175e03c3f8009,-0x8980cc11ac567256df201618d,0x32538f3f981eafb33de24353,-0x8988958ef1fe86e442add7,0x7c3effd0ecf8d7adc6ad,-0x10f10cd88fc162db61]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 15 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 33 indices rho q11 m11 11 786174614646220800 19=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 33 indices rho q11 m11 11 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r12 : List ℤ := raw_ints% [0x2d91b7e980fb50a5111c0000,0x4174b2894eb441051e934000,0x2b2695e7266769e5403f9800,0x11509bfc907fcb3166641000,0x4ba474b362367c58938e580,0xee05d96ec59468fe9d99c0,0x22cbbcd8af214456ebd190,0x3d80c0d933cf6adea2ae0,0x529e0fb1f8387ccf5210,0x54026befd6e1d6f936c,0x3fb7df45a23571a5ed,0x22fefa7cc990b4760,0xd2ce2e40f9bb81e,0x30c6aaeb642cb4,0x53e6af321cf5]
def m12 : List ℤ := raw_ints% [0x0,0x77c0cd4a398518837a2f8c8e50400,-0x7d29d8b8018e6cd528c30f9f67f300,0x3de337873d43389ff7050e8192f7b00,-0x133f403a33fad8d2237da88f0d4afec0,0x438e931858773438709ec0e636361a00,-0xb1cb6f77869c7c50c0d1db037575f970,0x16c0d26f5cd2db1a03c681107faaf60f0,-0x251f7904d3c34fb7a318488e5f37fa33c,0x3107422b61cab48c179325787f7ed99cc,-0x34f4c9e3368784cef0e3c79dccc298acc,0x2f11b735f1b616b560bcbc0cab29cf17c,-0x2287077ae1f4e8b5269c82ab3decfad73,0x14e72e7bc3d330c287401fb296ea93297,-0xa6a7ea39b97fc31a5d65ec868a82780b,0x43fad1b75e8d66cf82d85b0034e23047,-0x1681a3e8ed8011059ebe8c22fa0e3417,0x5f9ac7488c5c5511c82c91ae4d5c4bb,-0x1405c72d5e96504f648ac3027c180ff,0x33c54e99b11200a4696daa7e53d5db,-0x6444d35a8d07cee3b95bbc1a627f9,0x8bb5b403670aab2eafa65ffa2f85,-0x8464773b45b7ced44f375f6e171,0x4eb42afede0dd4a2913581dc05,-0x19fdd7e005cf13fd48382a641,0x3ebe880b685f09162a4731d,-0x30b8dea44e1487aad9c89,0x5826d0e6e4e6673ead]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 15 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 33 indices rho q12 m12 12 786174614646220800 19=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 33 indices rho q12 m12 12 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r13 : List ℤ := raw_ints% [-0x5e6d0a6266206c797428be000,-0x876e0bcb0e83ded0143ff6200,-0x5920bd6ddd29e72c40e363f40,-0x23b1e127953987bf228c25f50,-0x9b98817b02e2538aadb01ca0,-0x1e863589d8e9dfcdf6acdc38,-0x47313d3b52ee383a6d7cfe4,-0x7d6c66c42b73f462eb2275,-0xa7d8e44bf57e1e32fbe30,-0xa9edf09102c65286ebbc,-0x803a617d971f2d44f0c,-0x4600fa0ddf21dbfff1,-0x1a2abd146f9949b50,-0x600a3bfa0cab836,-0xa378843d82f90]
def m13 : List ℤ := raw_ints% [0x0,-0x8e34f3c8244e0d1c211876e8ff4c00,0x92c5ee08741d9b685a314fd36b70900,-0x479d25ed37ef8cb792b9cf2bbad0c900,0x15f5e58cd1add6209f4675615a9a8c640,-0x4bf022aae5ba126f7c48ce9678379eb00,0xc4b3a503feace2ddce85953a8a740de10,-0x18c008efeaae9d9eca42e3018781f78310,0x27a825f8b9d5156394126695c189368524,-0x335e74317490030f3cbf2c0413f5a02214,0x3656f7f0d76ae06134ed40afc6207ed06c,-0x2f39a6de3415c8a6e14757e8c2da02ccdc,0x21cf1d23f9ba492f47d8c1f1f16def97cd,-0x13ef0ff3fff36344ff19497c4ba4a78d69,0x9a6798637e8495e77a5ac08604e11b6b3,-0x3d049867d119b56d02a18bf842e8cf31f,0x1381e2100aecdb0f8b0c829b27f8cb18d,-0x4fb5871111b48f0305ea9c45c23a0a09,0xffbf132f1f1e954f6f516df362a6b9b,-0x275ab5495d5eca7884f32dc32028047,0x481792664824a50d87e5915fc7c3df,-0x5e38f96ad2c492f99d7ec1e390093,0x52e38f0ef01688659f9a82415d81,-0x2d265970760984c5dbadca27a25,0xd6feb42965274a006207e1d63,-0x1c9f218bd39f7848c01d04e7,0x1317590b3ef38d8972f2b5,-0x1ca51e6df9c33baa389]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 15 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 33 indices rho q13 m13 13 786174614646220800 19=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 33 indices rho q13 m13 13 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r14 : List ℤ := raw_ints% [0xb7fa218597ba117ea548d60000,0x10783fc5ac1baa4f23e8110c000,0xad2931156a765c9d243bef2200,0x453b24bf2ec81c701a21f139c0,0x12d332210ddf39cfef60f1f2b0,0x3af58c527dcce0cea2c36f4e0,0x892b8006665aea6358386308,0xf0f98d549765e93bb0004ac,0x1416fc17135f29b4788228b,0x1443567c41a097db806590,0xf396b235cb26f733a1c4,0x845005ae24161693854,0x312a1de0f43b66a70f,0xb32db05afcaa8af0,0x12e68101336b90a]
def m14 : List ℤ := raw_ints% [0x0,0xa8dee17dab1caf91674d0d34af2a400,-0xac33ceedba7031fc8c1d71b9f395ab00,0x52f4344bc5601540dc977c3625ff41300,-0x1918571c9dd5ec3d798079d1b7859c74c0,0x55888545674419b70367a38112bc8e3000,-0xda2c16aca2bf1f307efc65921805adcf70,0x1b00f8788511fc96d781593d6b585fcfcf0,-0x2a8306ac3410c315898029c409398cfd1bc,0x3608a7c14c6839ac916ee6d93241a164a4c,-0x3800d77d52709b105377efeab3214df37ec,0x2f9b8ec284e4012983579b3626497bc3a1c,-0x21466f1da670f209c870f2514a7417d92d3,0x131cd9e13c68604f943efe1f55d86637577,-0x8fdd606bd024af06a0dbdb7626a96cf133,0x3716a9fa7c271c07dbfcdd6991e5e76b4f,-0x1101fc8e7e68ab90d30e2b133e3fcc3be7,0x42d89021683cb9ec0fb684802cd06988b,-0xcd52f28b3f66c5d7cc9526b20fa805b7,0x1e13556a475c2c86f054c1e1564504f3,-0x34151e6133260770ab47392c8f95cb9,0x3fcdbd846e69ca35c732d6fd5c88c5,-0x340ea76c9fd63874143f4cf73b509,0x19f3e33cf8c8003831446218ec3d,-0x6f3d5f58d8036cf852260150d1,0xd0db6a5cbe9078af2da80dad,-0x779928cd2f24868b919ef1,0x94d20993348f4f556b5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 15 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 33 indices rho q14 m14 14 786174614646220800 19=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 33 indices rho q14 m14 14 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r15 : List ℤ := raw_ints% [-0x1545762db10b7b249aa3e2c3c000,-0x1e6e643179631dc707b76fda0400,-0x13f85606fee6d8dd6de154274680,-0x7f8dbca193f2f18b368a985bea0,-0x229fe84e9a361004fdd5ca3c380,-0x6c3bf33b4a56caa75c1a52b3c0,-0xfb42a02d20723f8081bb8dce8,-0x1b84fcfd1664e112e9a014e22,-0x249ad3e6a2e327954f145774,-0x24cd2c742b97e42cf20208d,-0x1b8c36df32a082085f7a60,-0xee6376b87eb60a6378b8,-0x582368a1cd9b579db0c,-0x13f5636bb012bd0619,-0x21737af285cf9018]
def m15 : List ℤ := raw_ints% [0x0,-0xc888abc53b32107caaab7fae90022c00,0xca2362867403e5fa9b86365991c1bb100,-0x602f86968d8ff77eae394be30ea3e51100,0x1cb84dc8a22bce8d5ff1d90d963910e4840,-0x608858a519cbfb3f6015df8c93a90de6d00,0xf295d59b381ad013d9ee3ba1f497ff58810,-0x1d8cb37f1637b0336ee2c2c631d192510b10,0x2dba57824b01dbad6fe0e084e1b0776c7fa4,-0x390e59c4786ba7585f5b2ced6de016f4de94,0x39f6e5a5d589695548a22d2ed868d2b4830c,-0x30377fba9a26712227ff32719d6030d114fc,0x20e9dd8f5bbc3f6dfdee1f81b38087d174ed,-0x126c2716cf54033fc541b4ae744e84533909,0x86c90a9321a23d0a80c733f795d3c30ad3b,-0x32048e2fac0070abcf831e40aee9c396e07,0xee9db350d95a795288e39578536d0b96dd,-0x38606f85ac2bc226357d1d916159f4d659,0xa5beb72bc2c8773f774faade8e7d8a7f3,-0x171a10c49160c006f7c650a41dd225b7f,0x25cc4bc244573b948faf96fc0137685f,-0x2b5e8f4d1a066b66db21f552cc33493,0x20c97a2253d2cd1a5e8e3c326c5fb9,-0xef1b5d376b64e960b0d5173e547d,0x3997f21ec8f3b2833d708d04ef3,-0x5f3a8158618630b7e4c414f77,0x2eca8fcfa0dd7516d4423fd,-0x3049de573c47b31bc5f1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 15 54 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 54 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 33 indices rho q15 m15 15 786174614646220800 19=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 33 indices rho q15 m15 15 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r16 : List ℤ := raw_ints% [0x25a5b60e0c7fc98f357f7dc890000,0x35cd2f0de3ab94b2d3501406ab000,0x23439c92e8004d2cbc4b073297200,0xe0efc7025472722c877ff7ee7b00,0x3cf77f020378dc1de9e78ad25460,0xbe40a01c4382c655cc936d178c0,0x1b8cfa727d25abdcdb470483a20,0x302cd5a918745fd664314d46b0,0x3febf28caa2c518d4dcda355e,0x4015b5f5ce79c177fc55132c,0x2fd1227575c219aedcca5b3,0x19c44f1ea5331fd1283d30,0x97c76a209ee89f5b75c8,0x22332dc3a845031e154,0x38fcf06d603344ac7]
def m16 : List ℤ := raw_ints% [0x0,0xee224bfa364b73940aaba79f4b0294400,-0xed649d655537210c247707c0b5a60e2300,0x6fa2d3964f68190b99334a6da1961426b00,-0x20ea8a7aea098ec8e0ea915c77e3ef9adac0,0x6d2841f1b4290739a6b6ab47afcea2a07600,-0x10e616640c7a4d81b6d37a52c3b9673a68570,0x206db1814c7b25ae6563b333c1345dd9e28f0,-0x3159e0d1b137b7a718e9f7210000bff55e03c,0x3c79630e23cbb15ecae3bccda43c4f8793acc,-0x3c3ea68d5153addc5876e7be4489701cd5a0c,0x310e59013d8ef5e7c03a654202630429083bc,-0x20b70cd4fabb0fb9d4a975fa7d29f4a800233,0x11d95ac4a9b089d2bd169714765f9fe13c257,-0x7ef5bfcb2d1be59a0a72e8be2893edd5de9b,0x2daa4069d927cf91c68f97151f2276bca597,-0xd2665b708c69de755c2715e0a672b5e9537,0x2fceeb52f68fe3defe73a8962fe378fd1db,-0x86801f561e34f4b55ba7b2d496b6b8df2f,0x11d4ee1ad8f6d8895ea6e0cb199b3697cb,-0x1b8cab73ae48b74f3f0db7c4586f6d479,0x1d957c0ab176d40d59434e5c3bf16505,-0x14b42a060d7a294529b6c3c5115f661,0x89e54295088e31dda04d751396335,-0x1dd55f23ad882144e928a48b54e1,0x2b67b477fc0ba5ebab22a68dbd,-0x124aeccb61a7bb951f860d99,0xfa8577f5b118fce20bfd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 15 56 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 56 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 33 indices rho q16 m16 16 786174614646220800 19=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 33 indices rho q16 m16 16 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x38fcf06d603344ac7,-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r17 : List ℤ := raw_ints% [-0x402305f51a20fbfa800deabc9aa000,-0x5b91c3ba587a86a0fe77c9a102b600,-0x3bf4501682a31f59cdfe416d3757c0,-0x17df6e8b1b8f89ef8accb678bef270,-0x676326b1cd7ec5b03b0b87cfe77e0,-0x142238fdcdae700a353bfc4ed1488,-0x2e91d165ae9d4ff108cd0e34264c,-0x51465c739e9286a83cda4df4257,-0x6b9b28b980a069c2f5a1883100,-0x6b9d8c4fe82bbe034dfd58966,-0x5012b05485285bf715442dfc,-0x2b02cca3b0bea8bf0242c57,-0xfc6dcaa26a0dfebc83c60,-0x38a3a42b642ae08c2ed4,-0x5deab493f5f092b298]
def m17 : List ℤ := raw_ints% [0x0,-0x11ac8ba392079993fccabd70d2913100c00,0x116ed665ab612472f488df551fb5730c9900,-0x81b0a8594e5786f497574e4b25020f529900,0x25c75ea7a48d9c8fd964153b99b61c8c19a40,-0x7baa4e216640c6664e8d8efc5e36cc9a87f00,0x12e11530f3611052d70f0965cee7fd08f5d210,-0x23b00860086037f4dee43f5352545af79d2310,0x356f32faf3fa85804eca502a7b03e34094c224,-0x40552689c2fdc5a0e3ce847ddfc66a18332314,0x3edebb75e80c16c96d4653fa2cfb4bedc876ac,-0x3221c573868f4a40261cc2e634339fd280ba1c,0x20ac4f59c3cecefde5d4fb7667deb36c713c0d,-0x11617f5e1104a5e7be7c20edaa69c3489a6ea9,0x7837e17ff506db8ccf094b219ac9c968e6b03,-0x29ea700a382f96da2f75e3722574740793f2f,0xba864cc1ede7cc921eff251abd19ca2b1fad,-0x28c1f5a3f50c26e3ef484569d6e39964ca29,0x6db315859222d4b6a4f6f915b69f972ea0b,-0xdd3fe7ad49401c9441a730717a09399f77,0x1429561825f7de20645256bb37e3695bdf,-0x143f2ebb53763d68ec5af587b35211793,0xd1abfe45c6babcfc6b59bc55f01c4b1,-0x4fa1e012573624262150567ff2f695,0xf759ae1add7d3d87fa478cb2b403,-0x13c6c51592789294e58d6804987,0x72565c36250c8f4870acdc85,-0x512d6cea4c214f3e70c99]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 15 58 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 58 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 33 indices rho q17 m17 17 786174614646220800 19=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 33 indices rho q17 m17 17 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x5deab493f5f092b298,0x38fcf06d603344ac7,-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r18 : List ℤ := raw_ints% [0x69b2b3641f8d6231675382a61790000,0x96c6be582ae33eb1e4e7cb92154d000,0x629fb21879312ec91102f1657fa6000,0x273a467479f0f0d0346db3b646491c0,0xa9add6773d2af32fc4e3159eb47090,0x20ff97163dff937e0f23871f5d6060,0x4c35a599a91f50d610d05ee33cb58,0x84c6a0ee96f17813c90c994927cc,0xaf743bd7a7645461c9626c94929,0xaf16af0f941cb5c8dc185a7fa0,0x81f53d8d585d2946c40d438da,0x459cb61d99a2e12144336894,0x19740f55f7d7e241dd19a29,0x5b0bd447b62715c524a00,0x96562cca4c24699640c]
def m18 : List ℤ := raw_ints% [0x0,0x14fce5d23d69065fbc30c0f5fa0c6a30e400,-0x147e0926c65329e771f1142f2228dc9ef5b00,0x96cd154c3c67ca67f13db10733ea988d08300,-0x2b6b4d48ce1c9b09d787fbc7152452e2d7b0c0,0x8c5b906eaa48f11902a90eb856840d40386c00,-0x1523d30e32d7ed0a9d46231762c568a947d1b70,0x2761af6cceb24470787ba4551d88702666364f0,-0x3a09ec8ac37550cc6785d223e66ccf47b9a4ebc,0x44aec78c40ed741c2fc50a1b75e6871970deb4c,-0x41defe8fb614703221e71acfa852af66492b92c,0x33743d7764d1d8ae11c579ef998e9cf05b2765c,-0x20c894d1959cb8ded48b989abe6a2a78bf06b93,0x11022c36a92ac96e8dd9f7d4afdf2947e308937,-0x726b54b77a157fc516332aa811e1f71cd14a43,0x26ad24928cbe774690567af711a80a7e8aa11f,-0xa63a7efb7e4be1b99e21570b73e7d024f8c07,0x22ecf39fdacfa9acbcff77a980eb5ec9e1cab,-0x59e88f5958cbd69b7c3039c18e98886c3b67,0xac565acf773b10f1f60810511db1e385463,-0xecfb6911c51df7ce417d6d5b345095c739,0xde6238d0285d87da343d890c40ae27c45,-0x84fedc66623fac13483219b1e4a4cb79,0x2e0a154ad15b520a7abf0313b8fceed,-0x8034ba5fbcf1838b9a59774d4fe71,0x901bfa3a4f68d72346795c15f4d,-0x2ca23f9e14fddfd5853248281,0x1a498d8744ebeaa8dfe085]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 15 60 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 60 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 33 indices rho q18 m18 18 786174614646220800 19=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 33 indices rho q18 m18 18 786174614646220800 19 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<19) : intPolyRF (mz e)=rfPoly (C (786174614646220800:ℚ))*rfX^19*(1-rfX)^13*momentRF (key size) (X^e) := by
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
#print axioms moment_source_18
end
end CatalanCore.Li2.NVMod.FamilySource.V5C20
