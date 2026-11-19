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
namespace CatalanCore.Li2.NVMod.FamilySource.U4C19
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,4,19,size⟩
def bases : List ℕ := [1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]
def num : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0x1201d0caf06000,0x1a5ea4a2f09a00,0x11c6e3432ffa40,0x752430dc68810,0x20f9635d59620,0x6b8f9de427d8,0x1069d2de7c94,0x1e8dce610d1,0x2bbcbb9ad0,0x30292e71c,0x28794d98,0x19803a6,0xba9f0,0x3a84,0xb4,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x7,-0x7,0x15,-0x4d,0x5ac,-0x374d,0x4fe1,-0x22f27,0x93e,-0x4e8f,0xfce,-0x4059]
def rhoDenominators : List ℤ := raw_ints% [0x1cde320,0x11988,0x420,0x129,0x18,0xa,0x8,0x31,0xe0,0xd8,0x5a0,0x21,0x252,0x1ad,0x36be]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 20
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 15 li0=padCoefficients 15 (liCoefficients 14 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 14 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x42,-0xdc,0x1ef,-0x318,0x39c,-0x318,0x1ef,-0xdc,0x42,-0xc,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 15 li1=padCoefficients 15 (liCoefficients 14 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 14 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xa,0x2c,-0x6e,0xa5,-0x84,0x0,0x84,-0xa5,0x6e,-0x2c,0xa,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 15 li2=padCoefficients 15 (liCoefficients 14 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 14 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x6,0x6,0x32,-0xe1,0x1d4,-0x24c,0x1d4,-0xe1,0x32,0x6,-0x6,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 15 li3=padCoefficients 15 (liCoefficients 14 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 14 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x2,-0x34,0xd6,-0x19b,0x174,0x0,-0x174,0x19b,-0xd6,0x34,-0x2,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 15 li4=padCoefficients 15 (liCoefficients 14 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 14 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x12,-0x72,0xaa,0xff,-0x4bc,0x6e4,-0x4bc,0xff,0xaa,-0x72,0x12,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 15 li5=padCoefficients 15 (liCoefficients 14 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 14 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x32,-0x4c,-0x28a,0x915,-0xa5c,0x0,0xa5c,-0x915,0x28a,0x4c,-0x32,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 15 li6=padCoefficients 15 (liCoefficients 14 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 14 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x72,0x1e6,-0xb86,0x87f,0x1c14,-0x36cc,0x1c14,0x87f,-0xb86,0x1e6,0x72,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 15 li7=padCoefficients 15 (liCoefficients 14 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 14 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf2,0xbfc,-0xd3a,-0x55fb,0x9ef4,0x0,-0x9ef4,0x55fb,0xd3a,-0xbfc,-0xf2,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 15 li8=padCoefficients 15 (liCoefficients 14 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 14 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f2,0x313e,0x802a,-0x1b201,-0xfe1c,0x3f984,-0xfe1c,-0x1b201,0x802a,0x313e,0x1f2,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 15 li9=padCoefficients 15 (liCoefficients 14 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 14 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f2,0xaf04,0x4cd56,0x154f5,-0x13e1bc,0x0,0x13e1bc,-0x154f5,-0x4cd56,-0xaf04,-0x3f2,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 15 li10=padCoefficients 15 (liCoefficients 14 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 14 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f2,0x24456,0x1cfeda,0x53acff,-0x17a0cc,-0xb6aeac,-0x17a0cc,0x53acff,0x1cfeda,0x24456,0x7f2,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 15 li11=padCoefficients 15 (liCoefficients 14 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 14 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff2,0x73c4c,0x942766,0x3587ce5,0x5bbcd14,0x0,-0x5bbcd14,-0x3587ce5,-0x942766,-0x73c4c,-0xff2,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 15 li12=padCoefficients 15 (liCoefficients 14 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 14 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff2,0x16942e,0x2b6c90a,0x193ac37f,0x59bdf604,0x879c5ea4,0x59bdf604,0x193ac37f,0x2b6c90a,0x16942e,0x1ff2,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 15 li13=padCoefficients 15 (liCoefficients 14 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 14 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 14 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^14 := by
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
  | 13=>li13
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
theorem cache_li (j : ℕ) (hj : j<14) : coefficientsPoly (cache.li j)=liNumerator 14 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x1fe67b1b59240b1ffac00,0x2b693fcf1c76c7bf54ed00,-0x1c40f0912646d69ec21c600,0xbb411da6fdaed7ca68f2940,-0x376b88c6a92409bd0a78b640,0xc78c1c345dcfb2a594d85810,-0x237a5653644e94fcf0fad1b60,0x51c88fc9d361adf83a43f6fb4,-0x9b79df263d653cdb5ca58b1c8,0xf6c654bd2037310872b517600,-0x149d7443be05ab5540f5f09cb8,0x17563ef7476978add1cdd4dc89,-0x16736e90fb3393c29218996dea,0x12615eafecc77aef9d56e9ba1c,-0xccc9472e318f769cfa1c8b47e,0x7900dc33dd6ccd017dc066cd4,-0x3c673d26c3362f94e9ad9f0ea,0x194e1eb3b15aa5b0d1707bbb4,-0x8d07d66f27b28c6ad2fe2efe,0x285414882bbe3e96e8cbbf5e,-0x94e403722f65b55f6ae987e,0x1b144bd07be8e39aa7c0d34,-0x3c1b2432e118ff0dc5dffa,0x610a8547c89e0ccb5ed40,-0x69f20e73d61aa5742646,0x45355289e0f2687cdac,-0x15517a4b1eab8d2fa2,0x1aab971631e231f1,-0xd425b2c1a0f0,0x4d24fb2f2340,-0x13493ecbc8d0,0x2f79381d020,-0x364164b370]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 15 27 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 27 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 34 indices rho q0 m0 0 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 34 indices rho q0 m0 0 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x25e1b23079dacd35f9c400,-0x328d08e5b80f50503742700,0x203e4ea1c5ca89875c9d1600,-0xd14bc6761cf6e812ef39adc0,0x3ca0730b2310e5674db2f72c0,-0xd57f88ff6e300891da05d2370,0x25184aa49d351d349e5f05cbe0,-0x537e9d79cc147e27c5132cdeac,0x9ad78d7599dbd1d4fbee8e0ce8,-0xef81942cecc9b69e4141909618,0x1379efc9731f50043f3820b15e8,-0x156f892c08438edd44510be640f,0x1405a2490aa7189c6dc656e45a2,-0xfe40bbc5cd77412f1fa0fab6c2,0xab57fdd646b9f57f9acb9155ba,-0x61ca7a037df23275781374f9ee,0x2f0c115af1adee8da5aba5f0aa,-0x12f2727d2897cfffad461661ba,0x6534ba848b987353067e707c2,-0x1ba38f7e4dfb62453ce63ff44,0x6109058e5afb25be6d57a706,-0x10b190aecfdaf007af78f296,0x22d0965781ca733a2e229ee,-0x345922069f9d46fc6404b6,0x3495a139ecf2180045686,-0x1f0c5d2040efe274be66,0x866cbcff9de59f894e,-0x8c7b15fda80ce79d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 15 28 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 28 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 34 indices rho q1 m1 1 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 34 indices rho q1 m1 1 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x2cfc039990b3d3b01898c00,0x3ae78954899cbadfe4550500,-0x24d882194ea263c11058c8200,0xea668b65c557ad8be44a83b40,-0x427fc7b1d9fb647a9899188540,0xe52e71516d9cb63df54831ab10,-0x26f06a0d87d8a5f7fdd1249ce20,0x55a20859fe7a00870c1e38d72b4,-0x9b03a70f33a18226ca523d8ac78,0xe9cdba03d703f6ac41e0d86ca40,-0x1284ab4587eba7cd7216c0313788,0x13d38e3ef7e12ff389bcb4f52a89,-0x11fd56cf91932ed8229abf2adbc6,0xdd91e06475d485704eb9dc9624c,-0x90922efb16cf4d3026dc514f362,0x4fba89aed542c56ca87c99b395c,-0x24fabd439ed08f116259ed81ee6,0xe51d42eb4fe9beeada3ead6614,-0x49518aaef1190252c43c1b2932,0x131f5b2eed8618eff6757d3256,-0x3fd4ad256547a8f6d85571622,0xa621758ada556b8ab18dd8a4,-0x1454f0cd9ae9565668271756,0x1c70d9d621f26431f50c418,-0x1a3e68894cde0d5acc317a,0xdf94dfb3a9b6299bd0ac,-0x34fe7d5056ac51d846e,0x2e32733b3d5db4bb9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 15 29 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 29 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 34 indices rho q2 m2 2 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 34 indices rho q2 m2 2 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x356b44465bd58b611d356400,-0x44af03b09a55fada9631d9f00,0x2a29104dd7e1a5eac3aad7be00,-0x1070860852d0841331467f82bc0,0x492180edbd76ca281c9e4236cc0,-0xf6d0f757dc26380a2aaf4be6970,0x2908979f5065c450f32c4f22da60,-0x583888c6d8d53399f9bf004a742c,0x9bfa513f04379a0c9077239aa888,-0xe588ac50ca537e79621fb0fdd578,0x11b7a00c272b3caede131359b3108,-0x12765c96703e6a076f6ea01e2958f,0x10480a158d26cb979fb9729d5e5ea,-0xc2965377d0bae0eda228600db93a,0x7afaffd0b210d7287d6a1cadd7c2,-0x418f0b4bf7c04eefe48269910426,0x1d52d4f71214c1073cdc0ae84bd2,-0xaeba72442779b65c86532691252,0x359a4ea8285b83b4c692006672a,-0xd59e82d742cebeff1fa10c8d5c,0x2a5d2082ba8f7f6b65ecb861de,-0x6835a8b48959d7bc326669ffe,0xbf7525ece6adc11eda90fc86,-0xf8e08a938244ceee7a403de,0xd29dd1f31cff944335ac9e,-0x64e7e0a3cdcca392e9e8e,0x14e4bb4a6df99d3ec1a6,-0xf2c362f3f166ccd25]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 15 30 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 30 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 34 indices rho q3 m3 3 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 34 indices rho q3 m3 3 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x3f6f61138d0d958352af66c00,0x50236711750f72726049b34d00,-0x304dd26d9b77fc918e75522a200,0x127bb6833265c10a27eddb1e8540,-0x50a147d900e604ba68e779b78540,0x10aa79ba85af1c1476d47a7143310,-0x2b67a79c34c73fb796ffdca6a9720,0x5b4968219ea45fe5be080378d2f34,-0x9dbaca44d93842f2c3e97bf68d238,0xe297e0ce47c30a3fafe4fe49a5fe0,-0x110de993f4ca2498880f3b849f1388,0x114e514d3c4f6b9318f2d35613bac9,-0xed711269f0cd317374815deeba0f6,0xac2e7926d1fcabc1466223b868714,-0x69725b2c82744f495d20c450ea1a2,0x365ad2aa8f09d5a0f49caa9b3ae54,-0x1773bd6591310903ce10b616a27f6,0x866b840122386cd396d8249af81c,-0x278901a66051f2132cb0322d4c12,0x967517faa24d38b588ecc66130e,-0x1c5b4e9bc5eba17b3be19d23272,0x41e580fda4462693b3548f8c3c,-0x718196644a45815393d040fd6,0x88f5056e8a39e4513a7251c0,-0x6a1f6b9ae88a3f07ebccb2a,0x2da5bcd7976dc0f7fbe4a4,-0x83c8b4d88d95bd606bce,0x4fa2ca5bddb76deda1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 15 31 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 31 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 34 indices rho q4 m4 4 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 34 indices rho q4 m4 4 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x4b5443473780218bf2304a0400,-0x5d900f6a7084db887a03d57b700,0x3769b70556ddd471f736fa10ee00,-0x14d202e09df2c88fbf38611b3c9c0,0x591f0d36a0e67f0776c72525a10c0,-0x120fc867ff23cf75696edf7d336d70,0x2e157fb5506ac592cbbc543f09ee60,-0x5edd9dbc799dab85aa58d917d5aaac,0xa04747e261b52f713fa7d134ce7208,-0xe0e7584a39ad6abeabf9e6873b1d18,0x1083912e5021b40013f6451e8880e48,-0x10539ef0e7bccbb2bed60d59b24ca8f,0xd9ebb50c6983ef1949ab9858bee84a,-0x9979dc76a3fa31ac05e7813f490ec2,0x5b1cb2a1854f6dcd538f5ebadccdd2,-0x2d6dbdeaa1ee09fde906a690c029be,0x12e982670de52467db80f8c44ff492,-0x68495914321bcd733b70e23d236da,0x1d68765ac9c035fd90d3b9769e6da,-0x6add68d6ebacd10221d714766974,0x1322cc55ab9c9e2f8c12e98ee73e,-0x29fd407745ca0483af69ae31856,0x43c18fc290fde008e995e480f6,-0x4bcc8760022405403e8ca01e6,0x35b0c6311bf94c3d6767c09e,-0x14b0c186a113b4e22f64086,0x33efc0a8f95ca1fc85436,-0x1a1801fc95199a4cbed]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 15 32 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 32 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 34 indices rho q5 m5 5 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 34 indices rho q5 m5 5 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x1201d0caf06000,-0x1a5ea4a2f09a00,-0x11c6e3432ffa40,-0x752430dc68810,-0x20f9635d59620,-0x6b8f9de427d8,-0x1069d2de7c94,-0x1e8dce60e91,-0x2bbcbb9170,-0x30292d6c8,-0x28793e0c,-0x197fac5,-0xba6d0,-0x39da,-0xa0]
def m6 : List ℤ := raw_ints% [0x0,-0x59740fe491e827d62f9957e4c00,0x6d4dd7f4d1d098c6cd8668249500,-0x3fa5a610c6ca7ce6a67f2d4ead200,0x177f1718122097ef3b45d9cb5abf40,-0x62bfbc062c7bd4ebb0616811cd1940,0x13a25077ed5fc4812753742bad35f10,-0x311b3ce5b64396df7ad34359e003520,0x62fff47f1623ea9c74fa64a374211b4,-0xa3a4e91fdd8fc3cd7d26426fc7ce438,0xe068d62af6edcdb18c73070ba618800,-0x101564fd342ee7ad1c60221786317548,0xf7fefaade84c668617a83901dd1b109,-0xc95aac96ebae5df209a59da57757376,0x89c82ea37ee739b51718a2268b5047c,-0x4f51794a07c99da60423045c36c58d2,0x2643f540f5b7ada7199b866b5f8f5cc,-0xf5fb571987137e96a9df37b39d3056,0x51922a1ec1b73b60e354adebb28b04,-0x160e07ac2afecc4b021329bdf83a62,0x4c847df5fa2292d2abcb4186f3506,-0xd03aa83234e55bf5329c7fd2b032,0x1af350d0b0cfb5d3221cf22fdc34,-0x28b52f9bbc16a5c7dd41735f1a6,0x2a2c2ef2e21cf8672e99703368,-0x1b435388a514cbc5db7e6c68a,0x964bb35e908649373b9f83c,-0x1475c1ad600a40de39dabe,0x88a6708f3a136937fc9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 15 34 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 34 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 34 indices rho q6 m6 6 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 34 indices rho q6 m6 6 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0xa0,0x1]
def r7 : List ℤ := raw_ints% [0xb41227ed63c0000,0x106925150b6fe000,0xb01ef655b0bce00,0x481a30558e50fc0,0x1426b9e97b74bf0,0x412a2c78c350e0,0x9d6942d29b4a8,0x121203cec060c,0x196d185ab36f,0x1b5df14e010,0x16493da838,0xd68909b4,0x5b23b3b,0x18ebb0,0x36a6]
def m7 : List ℤ := raw_ints% [0x0,0x6a39d2df6d43af4e5886185fa400,-0x7fc58ecdf2e0e4036845b1a1b0f00,0x49318dd7b2fd70df48d579ebdcbe00,-0x1a90899d4c67bdb2d577749075c57c0,0x6dae0a68f47a0837a0a1958f0787cc0,-0x156835519cf7f1ae61e23652f35c3970,0x34835fc7fa41e94766359e65bfcb2860,-0x67bd39fa26d774a198cc3b200f41552c,0xa7dbb9da0b4e2d3231de68f3d7e6fb08,-0xe113496bd2bfa2c3ec5cf5cc8247ceb8,0xfc0d7b682a98022a65d065992c44ca08,-0xece1c4858d4b14c083c97ec509e4d48f,0xbb45511873defe55518a439b3b3b090a,-0x7c8e1719cfde8ed94af1a623a1fde7ca,0x458e61828ad29200839b6b1983887b82,-0x207a05b8ad8cba6c8a725da90180d496,0xc9859db8740dbe8873169498ed968b2,-0x404f0a6b1097857f7a644f62f8e8662,0x10abd60a4da99d5063d2332df52482a,-0x3736eaacf3982b5960ed1016f28b4c,0x8eac23f3260d43a2031b5fd361abe,-0x116ad6f419f02e2f588d1c814002e,0x189afb35cc7139d5be738ae09546,-0x1793ebb4aaa1d1fc6031a8498ae,0xde37fcebd0ddda1612398c53e,-0x4452d324bc502c11ef53ba7e,0x80e514cd4b38279aed0926,-0x2cadfd0526ccc009c5f5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 15 36 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 36 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 34 indices rho q7 m7 7 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 34 indices rho q7 m7 7 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x36a6,-0xa0,0x1]
def r8 : List ℤ := raw_ints% [-0x3d80f38324c1e4000,-0x595cef6a19243dc00,-0x3bb11c274a475e580,-0x185178cfd7463cc60,-0x6c1e27bc9d450900,-0x15b39ecfeaa21a20,-0x33fcced31c8af18,-0x5e8503979148de,-0x8350bb7623cd4,-0x8b118fa710b9,-0x6edf5f18080,-0x40d019b96c,-0x1a6dfc7ec,-0x6cb8e5d,-0xd8108]
def m8 : List ℤ := raw_ints% [0x0,-0x7e24aa6951c0602d091f3cf192c00,0x9572dbbb315b632e4a8f9ba50a1d00,-0x54459fff8e4274a00093c3d6662c200,0x1e162f15b5f76a2511f72e15456f0940,-0x7a1b6e24c01235b86477050c9774dd40,0x1768896998ce23515cf3c65cd6c4f0b10,-0x385a006be968083584c72f5384decd720,0x6d2477ddd916bcb0c10d54367a1054434,-0xacf6c74e9b37813bf1a12188c38b36738,0xe2e25efe9401b5b2d730266a396931720,-0xf83e75a0e873780709161912651df3408,0xe39f33f19933bf5698e53cd8e0851b249,-0xaf4a114300e7316e253db2dae99d49b36,0x715ccd2722583d528b29ac2e6f538b6a4,-0x3d6e007298b123d795d42c4a1430cd342,0x1bc45d0c7a91b7ff62f06b0562a2fe404,-0xa6590636728dc58724a7ad88da1538f6,0x3316920ad98391c920dbebfa65328fac,-0xcb2b551e71968e25b260fcf0efc3af2,0x2823dcd4451d58eedd2d139399ebebe,-0x62736ad4eaf8f42673d6eac991fdb2,0xb5476b372f5b4304a92699b5b2a6c,-0xef4f09bde7d0fd1e0cb43e53f136,0xd3d9981bf3168aa764a47a74150,-0x7187f260e77ff690be7b69cbaa,0x1f1766ddbd45b4c06610ff014,-0x32b89f87ed1bcb0f31f656e,0xe9813333329c48d3bc31]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 15 38 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 38 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 34 indices rho q8 m8 8 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 34 indices rho q8 m8 8 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0xd8108,0x36a6,-0xa0,0x1]
def r9 : List ℤ := raw_ints% [0xf32b1492fe57e30000,0x16040d0f945db009000,0xea79822ec369963600,0x5f23044ca9bd1e6b00,0x1a4f745cad7a8f04a0,0x5406397e64fe80dc0,0xc7f1ed0d1c9c5e80,0x1689d1587e7e2870,0x1f01bfbb3de5da2,0x2070ce2016180c,0x1977dc4f4f407,0xe97e01342b0,0x5cb2158614,0x16f529034,0x2b32b43]
def m9 : List ℤ := raw_ints% [0x0,0x95cb8a5d111472357ad5185ede4400,-0xaee7af59bfaae4be7f1efc9fa502700,0x6123c7956c64a986fd45c471878d8e00,-0x22227cbefcb8fa23dd01b95ae191e95c0,0x88413b0237d3ab1bc45064023202ea8c0,-0x19ab7456931419fa83e7b542da7d92f570,0x3cad0ae18d83fd6cd0cf263036fff62a60,-0x73473909f25aba7d078fe1a9bbeb877fac,0xb304456cabeca1c474e77e1ebc52c4c208,-0xe5d6378628b242d579813e8faad4c82958,0xf5d09707d4337590d603d7b7c18c243dc8,-0xdc00c05af2f717d6c3445ddaf1b1b4b18f,0xa519ba6847f37b7ca43f633e20469a6f4a,-0x67dbbee680a97b3c23b528b86d35b4bc12,0x36a0e2fc94e531adbd77572cf29af6d532,-0x17e9248be8a1b59c1fde080776c2fdaa2e,0x8a5239e0532bd9d6b6a5c217bbf84ed52,-0x28e2eb9a44eda94907380b3cd83809b2a,0x9be3ad28772b7ba67f93449fad2dee7a,-0x1d63f9700e5060dbf670ae0a11c1f7e4,0x4465b45801b37cf4b1f242091120cbe,-0x76a689c1295e45f1524487ead28bc6,0x923ccbffb11ffcb0fae5b596ca396,-0x777411d139f5efc3eaac915a69b6,0x3a2628ac5c4e4e6dcb62860475e,-0xe28da23cb3af19faaf0a01736,0x13f23c5d6f44fb675ebbc316,-0x4c32d2edc8ee3a7906d3d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 15 40 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 40 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 34 indices rho q9 m9 9 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 34 indices rho q9 m9 9 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r10 : List ℤ := raw_ints% [-0x309df198528e9d092000,-0x463ec01ba8e664f34e00,-0x2e9e97ac9afe4456aec0,-0x12d9ce37cafacd6a1630,-0x53148975235725f3f60,-0x10817601845b6e0b0e8,-0x271006a8c182bb68fc,-0x45fecf0febc902333,-0x5f8c0130490c4c00,-0x63058c275f9d2b2,-0x4cd57548f9bebc,-0x2b6190782e26b,-0x10e5cb558720,-0x414a19f678,-0x76a7dae8]
def m10 : List ℤ := raw_ints% [0x0,-0xb1e1b44e8448479f81dd0cf0a7f0c00,0xccd053f3774b1a78ae5bce42b212e500,-0x7019627008ee29e3a49d03201e6893200,0x26cafc286ebb0a4503cb03ca981b7c6340,-0x9861f2632a0fc5613b1319e1b48c434140,0x1c3a5f4b60d73b077f191b2394bcf7f2710,-0x418c85e5fecfd87eea65dc300002eebf920,0x7a39dbb7f86a8c7ae72b40c38a8558a2eb4,-0xba15c5336fb110e070e0f7d20a1b304fe38,0xe9f33bfd805eae3994eece2d1eb32834740,-0xf4b1bbeb50dfc2b863773f333bf75290cc8,0xd5da3fcc6df19f3335427f027fa7da32a89,-0x9c73cfb7bf24da04d088cf68ddf4715abf6,0x5fc3bd5294bcb2696b76c8a0bcb062d800c,-0x30e867ac124343c91d37545aab655172232,0x14bbc95ff0a5a9af1b711c52aa0111747fc,-0x73d6009c630c66306a50af07368efef196,0x20f4e5174b3c9947aa55a2abd48b4c4b94,-0x7876402e9b09a00ad76b5bc019597b902,0x15aaf86f203a0e7d7d2706273b4b60836,-0x2fd36519b73d53cb30609530c4d1a032,0x4e1ccf431403dce14c64b0a68e3a464,-0x59cdb9f575a7b78aabd708af158846,0x439ac0e74e6d33350a3137f2b2678,-0x1dd93ae66343453a890fda5a7eca,0x673c20c40aec0e157f611e5cac,-0x7d6a5c4bf8c5a08e9ffc9c9e,0x18d7c04a707d874033ecd9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 15 42 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 42 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 34 indices rho q10 m10 10 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 34 indices rho q10 m10 10 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r11 : List ℤ := raw_ints% [0x858a4d29ca1173b970000,0xc084c3b66d75666267000,0x7f715f2970deb1961fc00,0x336193d1a8abb69e23fc0,0xe1af5cb9d0858cdd36d0,0x2ca970d99e997c3acc60,0x69372e401c255623d38,0xbb86558437e66cce6c,0xfe5bf0d19ecf9494d,0x1059cf616d026fd60,0xc921abf322fef0e,0x7047c0812eebb4,0x2b1e16d557f15,0xa396acfe880,0x1223ebf4a8]
def m11 : List ℤ := raw_ints% [0x0,0xd33c061d3d15d50d6a367f5dc76de400,-0xeff83de11dcf5fa09560e77cf55a6ff00,0x81814a31ba8f92a7e5bc088c3cc1e8de00,-0x2c28d35b0af822f021312cb77d36cf703c0,0xaacaccbea5db58f61c3bbbae6b7f7db74c0,-0x1f202910a51dbba13261ed7336fa927cc170,0x470ae55f7279f343867ea55e552064867c60,-0x8213f2928bc1ab9a8258fca4d1a9646e5a2c,0xc2407ce7ce2f91b0c898b1863a93b195a108,-0xef420e2eb02db16975ee2d792445762490f8,0xf4d589b105c88735b610bdb85c5e22829f88,-0xd1082d2acf4998f956395ebac2f199b5918f,0x9523b04240793008ca0534d72fa3400f2f8a,-0x58db4a90d6981dfed193ff6736a73ffe8c9a,0x2c12e31a7cb76dc089d2fa67ec547bc81062,-0x1219b6db56c117d9fa2261b1b62df2df7686,0x61ad2bcc2bf90aff838b86c5507ca0c66f2,-0x1abfcfbe82757622636aec021142ed90032,0x5db9363eeb4ae4fcc69933116ba043734a,-0x101474ef661b55aff24d0e59169be6c93c,0x21a5d6371347ed06da2c87f3c9f6f76be,-0x33b53e23d5bc7862ffb1589d79fb621e,0x37668284727ab148df5a742d03d9066,-0x2663a846d2a99a61cdef0ae3ecccfe,0xf59c32d27030569dc3e213eb5a7e,-0x2f0f3d49ba751ac3b04b03a7fae,0x314003e379260b283acb11086,-0x817a1da1f9348a3b1dc3c5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 15 44 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 44 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 34 indices rho q11 m11 11 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 34 indices rho q11 m11 11 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r12 : List ℤ := raw_ints% [-0x146a786b0dc1a3a693f0000,-0x1d6022d3939b22c63161000,-0x136724220021e98e49aca00,-0x7cd89fb304323041468e80,-0x222c7e5c5f07feacbec540,-0x6bd818388974aa21ecef0,-0xfd14fb73c3818c6004c0,-0x1c10ae129bc9ec7afff0,-0x25de1f91160512f0a14,-0x26b4b585bec2691113,-0x1d898623d5ff0ce60,-0x1057677dc86eade2,-0x634e1b73c159cc,-0x1739c8dc2b78b,-0x287d7181da0]
def m12 : List ℤ := raw_ints% [0x0,-0xfad74742b889ecffee20b73f5cd27ec00,0x1194fbef1539137c6208171c3dd7be4ed00,-0x95c63b749c80983631bbf9b51f805952200,0x3259651d0da782c82fc090f1379737eb4d40,-0xbfd58740322528e1845aa4fb133117210540,0x226962caea2a9216e62e1f40d911fdcb2f310,-0x4d3d6aa22d20881b356538a37fa7b41260b20,0x8af0b6eb5104b9c0e32428a751ac1af2db134,-0xcb9da367a9f6b4024ea4958c577e4acb5f538,0xf5cf92f7184a6f33155480754c65c6a7a4860,-0xf634e441f1080ea0b478cc47816e63f86a388,0xcd6e4ca551b1027ae7d276791251d8799a1c9,-0x8efe5b967aa7ba5b3a61a6a1d5d17ef24a4b6,0x52f3c2125edae2a49c9c3108226aaec07f4b4,-0x27f8b712a87ae1df274fc9c1a1ac72f7966a2,0xfe7ec912b505b3dbd2462be6f9aaa66b1bb4,-0x52ea9b41895c8bd1d077f8998db9296a6136,0x15db6365bc226a9fcc14eba7c9affaae5ebc,-0x4966db7743e0e4dec59ba01a9d6c25fa592,0xc023678561d0e708f68daada2799fe7f6e,-0x17cfddb68665e987db566de3e2f3630cb2,0x22681876cb1eb785e39a6265fab9cce1c,-0x22526b50bf283aaea37e315d983301d6,0x15dd945ac4ab4278d9a7f6aaac3f8e0,-0x7e84a163cd66fa3038add1d92d8ea,0x1574ec86f5ff4bfaa6cb93115604,-0x13536c800415400443f0928f4e,0x2a23f76905712a2790d6bc1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 15 46 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 46 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 34 indices rho q12 m12 12 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 34 indices rho q12 m12 12 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r13 : List ℤ := raw_ints% [0x2d91b7e980fb50a5111c0000,0x4174b2894eb441051e934000,0x2b2695e7266769e5403f9800,0x11509bfc907fcb3166641000,0x4ba474b362367c58938e580,0xee05d96ec59468fe9d99c0,0x22cbbcd8af214456ebd190,0x3d80c0d933cf6adea2ae0,0x529e0fb1f8387ccf5210,0x54026befd6e1d6f936c,0x3fb7df45a23571a5ed,0x22fefa7cc990b4760,0xd2ce2e40f9bb81e,0x30c6aaeb642cb4,0x53e6af321cf5]
def m13 : List ℤ := raw_ints% [0x0,0x129dfa49f3b23c96feac6d99b3e39f68400,-0x149f2c6e3536cc739a39be1d40067afd9700,0xad65ac58b8407f29934294a717075f08ae00,-0x397f0da92c4f575566cffe01d5577b9ad21c0,0xd7ea819f63f921637ef5cd3aaafe438e360c0,-0x26249715109a471c09bf8938826f8e21c09d70,0x543c94d197e1fedbee05ed10c9a36406cbbe60,-0x94ef8ead0949e98f5b65a7a48f361e59d7a4ac,0xd64ae062f80941c87068819ae17ee58d3e8008,-0xfdad15455676ff9ba905b1863382f75115fd98,0xf8cd8c02c17fc086dcda2e5b6002ba23367748,-0xcaf69afc568b9608e49d0f4cfd3e63df37ac8f,0x89e0b0c56400c265881816e47b8000cedadbca,-0x4de7253af224068a17ae0470cdf9e33432bf62,0x247a1d3727ff85fd0469cc7e1fa2e85fc31f12,-0xe1133624fe464ce105c8330b9c45ba362ef9e,0x46d864d00f24d1e79db09001b8eca06a69f92,-0x11f9c57552bcde9387e961efe2a83f037a37a,0x39da3c5eefc2823a21877a6555722a81a09a,-0x905cc6263f6b2ac399393cf83cf1f4a1d54,0x10f20c8bc8c3c2977d262819c67d7ab8ebe,-0x1701882e025e86e5edbcf1dc7fbf557536,0x1558c4e231bb7e6ea5d2c914e0cb3d1b6,-0xc7ceeb1a09ad181a2e307aa8b2f2486,0x4142d22aa8a993ba4099f83a59849e,-0x9c8b1640a0928443d76aa2da35e6,0x793eaf721b53aeccbbccd01776,-0xdb44a285a04fe101f6b9b8d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 15 48 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 48 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 34 indices rho q13 m13 13 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 34 indices rho q13 m13 13 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r14 : List ℤ := raw_ints% [-0x5e6d0a6266206c797428be000,-0x876e0bcb0e83ded0143ff6200,-0x5920bd6ddd29e72c40e363f40,-0x23b1e127953987bf228c25f50,-0x9b98817b02e2538aadb01ca0,-0x1e863589d8e9dfcdf6acdc38,-0x47313d3b52ee383a6d7cfe4,-0x7d6c66c42b73f462eb2275,-0xa7d8e44bf57e1e32fbe30,-0xa9edf09102c65286ebbc,-0x803a617d971f2d44f0c,-0x4600fa0ddf21dbfff1,-0x1a2abd146f9949b50,-0x600a3bfa0cab836,-0xa378843d82f90]
def m14 : List ℤ := raw_ints% [0x0,-0x161b9937d163a7f34e6cc226859e4d4bcc00,0x18330e2d74b478c329aeb8c3e970c42d23500,-0xc8f326d8766d76a1d4148033fdfacbdce9200,0x41c200fcaa1bcd0d64450f4a35885cc2f64740,-0xf3833a7327417b9a62763f6335aeaec0242940,0x2a629d3cd2d2f5f542ef570495c87a1aa6eef10,-0x5c24a41a21aa1d2366557fc7014efaf57a24d20,0xa034a924c394f8de9160feb01913b992ae68bb4,-0xe26ad3cc7185add4791d575aaa8bdab961dfc38,0x106f081922e0c35d6f1975085abb4df9fc77e280,-0xfca1debe3ea37a2addfc592c43d1d452a69f848,0xc99078cd8fc07e1adaecf1a158a7d91c0cdd009,-0x85ae0c7a53a8145f1cf77809d7b44fb28262176,0x4996650d4fe4984b5c3a79136f244cbfabd1e9c,-0x217d7745d9a198c8e0e90c0fca8cd0d866fb092,0xc84c654ce6fbf9c99959c9b064765c7d24752c,-0x3cea0fbbd527f97bafa932d850dcc1dda29bd6,0xee06f0071530a5f613ced5e262e4017cb4324,-0x2de085e6dfeff4ab4ad7ddf2e25de346b78a2,0x6d18f26753021fd86930e6a8c781cdbc1a66,-0xc1f83d8c6d3a9bcd31feae6ff1348334732,0xf74149235b85780ecf808e0488a6619594,-0xd5325be2ea73bad4ed15279ac5e76fde6,0x7264fbccfdec8d0765bc7fccf7d1ca88,-0x21b3a35c96ef45825004880f360f60a,0x4760f8fbbe4341ddad3bf51a1221c,-0x2f813a7e5639af61782e571557e,0x47406119137714d73de822e9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 15 50 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 50 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 34 indices rho q14 m14 14 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 34 indices rho q14 m14 14 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r15 : List ℤ := raw_ints% [0xb7fa218597ba117ea548d60000,0x10783fc5ac1baa4f23e8110c000,0xad2931156a765c9d243bef2200,0x453b24bf2ec81c701a21f139c0,0x12d332210ddf39cfef60f1f2b0,0x3af58c527dcce0cea2c36f4e0,0x892b8006665aea6358386308,0xf0f98d549765e93bb0004ac,0x1416fc17135f29b4788228b,0x1443567c41a097db806590,0xf396b235cb26f733a1c4,0x845005ae24161693854,0x312a1de0f43b66a70f,0xb32db05afcaa8af0,0x12e68101336b90a]
def m15 : List ℤ := raw_ints% [0x0,0x1a40c5f248a65770ed21268dbeabfbca02400,-0x1c696b6de2ca2220e05ae749f84c1d5999ef00,0xe91c3f0ab279d61d670fd86b2c6c495c98fe00,-0x4b5150cfbcf6f5d209836fd3e4c1ac3d6306fc0,0x1132d3ad80642b93da1c88c2ede59fdc26b16cc0,-0x2f36fac1937d2e07d5e8dd810e39ed1f52590970,0x651632fcba4b5b78e4a879ef8654c8332933f060,-0xace9b64ed24bd0a2ac4d8eb308eac8735c7f5f2c,0xf025b769aec4c98d48d6e3dc6a6bdc386cbeff08,-0x111b4ba58950576276012566736d1737a4552f738,0x101b8b77776babd05d02b5f98303f8351a4fc9508,-0xc930069166e6929cd92611767bb0a465969e1a8f,0x824f3169e5474ad948885f36c4610e5f52251c0a,-0x45e80b6a080e698a19f951e785965befd3ac5e6a,0x1eee037057151b3dbc80fe2b8571acffa07ca542,-0xb355054ea6d78ebcaf70568f562e747eb8b6376,0x34b273e77827b04d2a0742bf4765dfc3a8b5732,-0xc6314c98ed5584718854dd98ccb0fce0548f02,0x249883a980731e55701c12686b1c2f2336826a,-0x52e8193a53953630f0eae99c68c666dac122c,0x8b780b0f734f650974f251938f368f9e5cbe,-0xa6cc4adaf6eda8f574177eb9e27f689930e,0x85858e550d296f99f3fa258a946876e386,-0x41a2af55c5ba6feb254a7727dc7ba4a4e,0x116ba0bff4db8f2fae489ef90fab35be,-0x208ac3009b0b27981098be707a4fde,0x129942c1c1b01f7f349aab2d5be6,-0x1722cf38a3f07e33887a11695]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 15 52 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 52 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 34 indices rho q15 m15 15 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 34 indices rho q15 m15 15 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r16 : List ℤ := raw_ints% [-0x1545762db10b7b249aa3e2c3c000,-0x1e6e643179631dc707b76fda0400,-0x13f85606fee6d8dd6de154274680,-0x7f8dbca193f2f18b368a985bea0,-0x229fe84e9a361004fdd5ca3c380,-0x6c3bf33b4a56caa75c1a52b3c0,-0xfb42a02d20723f8081bb8dce8,-0x1b84fcfd1664e112e9a014e22,-0x249ad3e6a2e327954f145774,-0x24cd2c742b97e42cf20208d,-0x1b8c36df32a082085f7a60,-0xee6376b87eb60a6378b8,-0x582368a1cd9b579db0c,-0x13f5636bb012bd0619,-0x21737af285cf9018]
def m16 : List ℤ := raw_ints% [0x0,-0x1f2ceb0fb64587d619975dc8526c3affe2ac00,0x215f937d628a55974d22cc0554535dcae6cbd00,-0x10ead41ef7fb28e2b0fd259e52de74ade8e18200,0x566421685277963ccae2728685347a8a9413d140,-0x1378d854d6241d6be3e0c809842d3cc0317dfad40,0x34b855971741cbec273364654e231e7bd9d089b10,-0x6f36e976fde215888922d0b5ab260169293db3f20,0xbb3ebcfe614c4018721862eb0abcd7fe8dcc4fe34,-0xffaa1e117553a46c9d87d6ce24ebd0810e4815338,0x11e1a06cb79dbc5d9a4b43451c61d454a162597da0,-0x1081d6a60e4654bbeb1d97d6cb0b485952f3fcfb08,0xc9cda8a3fbe7fb58d8bfef84b43e0d90a7dfaed49,-0x7fb16b49cbcc16ec477aa658bd682ecb754fff236,0x42c72dccad8ac455e8b3bc7adefb63f9521d46fc4,-0x1cbadc214f717603d755622c4076f895bb4faec02,0xa1828a4aa78eb9f18c0f0288f6b2c4ec41c88a64,-0x2ddc3998bc7d229ea5c13077ca1d0d24616a6976,0xa5ff93db450b91a97981da4b1ef2de0ed156acc,-0x1d5bcac31417682764fe8eeca8adf6a30392632,0x3f56edec522d72780ace4d94bb454d9eea1f1e,-0x64c2d233c379a6194da36a5acc69409e44fb2,0x70f9587130a5d06855ce49c71c2e92c7c0cc,-0x53e0aa4807ec2f0fe126d5ae54265835076,0x25bb51a7bb16227179c450b0feb5d92d70,-0x902eeba9c97382de443af4ce680f7e2a,0xed5369fc24718e7f28bbe03a3d2ef4,-0x746af2adbfae863e616e56034b2e,0x781ce0874f203432026f90c51]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 15 54 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 54 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 34 indices rho q16 m16 16 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 34 indices rho q16 m16 16 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r17 : List ℤ := raw_ints% [0x25a5b60e0c7fc98f357f7dc890000,0x35cd2f0de3ab94b2d3501406ab000,0x23439c92e8004d2cbc4b073297200,0xe0efc7025472722c877ff7ee7b00,0x3cf77f020378dc1de9e78ad25460,0xbe40a01c4382c655cc936d178c0,0x1b8cfa727d25abdcdb470483a20,0x302cd5a918745fd664314d46b0,0x3febf28caa2c518d4dcda355e,0x4015b5f5ce79c177fc55132c,0x2fd1227575c219aedcca5b3,0x19c44f1ea5331fd1283d30,0x97c76a209ee89f5b75c8,0x22332dc3a845031e154,0x38fcf06d603344ac7]
def m17 : List ℤ := raw_ints% [0x0,0x25055722a872914e3e63bf5de1e0860fdd2c400,-0x27382f8d26e5dc55f6a706cf814b19af82120700,0x13a96beae3d2020f3c3e56f00c60fbf8b98adce00,-0x633b15c85534879b42238edf42a2f3f2197ac6dc0,0x161649f4921ced1b17849a1d6cd6099e39fa1298c0,-0x3b00fa20e1d225fcef746cb711b7e723de4f528570,0x7ab24e7fa0e2ed91f481e98adb21edd3b4169a9260,-0xcb6b14fdd39dc612c3bdfb212832b13744957a89ac,0x1112dd4e3c89136de13119a5ae5d9a3f8340d3b9e08,-0x12c469dc125d03e2c89863b1c84ca0f9b0ac04285d8,0x10fdfdb48a3367b14013fd5f9533a502e487dc468c8,-0xcb65acc94de4d2c2693956341b60a928920566338f,0x7dc5e03adbca16f8b66aa4173f6b18a66d31a1704a,-0x402298e246cd4dda2fb6bd9d1341530c5c14a4d3b2,0x1ad630f0de4965edb36789a8feb8fcd6930079eef2,-0x924bddc7391d248074df4635c4cb41c7a148f700e,0x282442125c90804257a7bca88384f50922a3565d2,-0x8bd3f37eb08721bdef1261cc2ccc0a632f250cca,0x17ae928b25c470d3b52333b2bd0c7e94fea14cba,-0x30a337ffb75d8958e224be466b50f33a3d835c4,0x49202eb2e8bb40c83cfb3e7dc85ffcaa0030be,-0x4cce3d7285b5c88e4f7260953c04e3928e9a6,0x34d69d4c26defb0dc7c36c9937de614e79d6,-0x15ba3942e2d99bcb2a5d25e96cced954856,0x4aa1247ad4cee62a692d6bf93c08ec5de,-0x6c24b991875c17ec67da8e048c96396,0x2d82ba8683a0775c740779daf39d6,-0x26f2568e9838068a6bc6bf26dd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 15 56 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 56 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 34 indices rho q17 m17 17 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 34 indices rho q17 m17 17 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x38fcf06d603344ac7,-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r18 : List ℤ := raw_ints% [-0x402305f51a20fbfa800deabc9aa000,-0x5b91c3ba587a86a0fe77c9a102b600,-0x3bf4501682a31f59cdfe416d3757c0,-0x17df6e8b1b8f89ef8accb678bef270,-0x676326b1cd7ec5b03b0b87cfe77e0,-0x142238fdcdae700a353bfc4ed1488,-0x2e91d165ae9d4ff108cd0e34264c,-0x51465c739e9286a83cda4df4257,-0x6b9b28b980a069c2f5a1883100,-0x6b9d8c4fe82bbe034dfd58966,-0x5012b05485285bf715442dfc,-0x2b02cca3b0bea8bf0242c57,-0xfc6dcaa26a0dfebc83c60,-0x38a3a42b642ae08c2ed4,-0x5deab493f5f092b298]
def m18 : List ℤ := raw_ints% [0x0,-0x2bf6577928080c8cea16733f7c3a9f32d6a48c00,0x2e1c3eece84ebf2ea955c330bc564c18cc7568500,-0x16df412707407de455c4d997b7787121ecdfe9f200,0x7221fd47da472ac349395996aa7c526118c73e6b40,-0x1919351463523aa28fbce9b5f297dd3f71bdf129140,0x422f7862f2a0726cba0bcbc529ffc987d0d50057710,-0x87babd1a216ff6cc24039e35624d3161430aae46120,0xddae8b2fe7064ca351f6545a6e6be9a93f4f87948b4,-0x124eeeb9f38ceaa201a12e5b0490f564d081d9ee7a38,0x13c674f8b36cac3e9397124fafa129ed5c112f1a41c0,-0x11914adb7ab64282a8da2c4af5469c20efb49d12dbc8,0xcdf80c3efcd620238d3db2a66b4406bde902a15f189,-0x7c81075f73d76f442524f389a4986c1a206e72eb6f6,0x3dec285ba9bb5f9559c7f20430133bbdf6145238a2c,-0x1934ab3407e4adf27c3133dfd0aca8ccad9832554f2,0x85423bae4b5bb31dcfc428ec2eba2aac4a7763415c,-0x235575d0cfec9f7b6d7ffd8c238dc4294607782216,0x766f4360cbcf55dda477268f869153f44fb40b7b4,-0x1334327e2e8bdb4bb1b5d8aa24570bccf73c1b242,0x2587c3bf2dadf6f1833bb95312f0c4d0d423c396,-0x354c1542e2152c217d0f22df248eb8236d29632,0x34662bbf51eb9739eb2114daba93d37717a5c4,-0x215eac0247361b00f12e5f9d4a38307a0bd86,0xc87b070659dd0743a5c08af2533cbdec398,-0x26a553d46a91a647c69f7b7096d862094a,0x3142e50aa357e986b29756b4be40fa8c,-0x11c73a1c1c861d084093117d613c5e,0xc9eba8cb292847647f73e4b1f9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 15 58 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 58 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 34 indices rho q18 m18 18 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 34 indices rho q18 m18 18 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x5deab493f5f092b298,0x38fcf06d603344ac7,-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r19 : List ℤ := raw_ints% [0x69b2b3641f8d6231675382a61790000,0x96c6be582ae33eb1e4e7cb92154d000,0x629fb21879312ec91102f1657fa6000,0x273a467479f0f0d0346db3b646491c0,0xa9add6773d2af32fc4e3159eb47090,0x20ff97163dff937e0f23871f5d6060,0x4c35a599a91f50d610d05ee33cb58,0x84c6a0ee96f17813c90c994927cc,0xaf743bd7a7645461c9626c94929,0xaf16af0f941cb5c8dc185a7fa0,0x81f53d8d585d2946c40d438da,0x459cb61d99a2e12144336894,0x19740f55f7d7e241dd19a29,0x5b0bd447b62715c524a00,0x96562cca4c24699640c]
def m19 : List ℤ := raw_ints% [0x0,0x343487dfdf898ee755faa8db63859d0c5ee366400,-0x363c41fd473f05c1101330477ccd3ba8e10b6bdf00,0x1aa132673f9a3c3b9df13de5272324f8722119b1e00,-0x8371ce84a638dd9c9b092bb15ef6e030e0eb6389bc0,0x1c9203e1fb8dede3751c8c5a5beab89cbfd28143e4c0,-0x4a675c8566576475c670e7397e5132e738afe2c59170,0x968a8334db1e33e8b257f0ade9236ade828983fd2460,-0xf252b6cc6a54da8322ecb1765ed5e983fa482b82242c,0x13b34ea3003f435dc50118888702468d36a2bf7345d08,-0x14eb0523d8fab7e1945bfbbf76f3e35890c636935f178,0x123d58ed748135cd7c256bc40fce4a2066006a3cf6288,-0xd18846bbbfc0f2c588445b291ab6bf52e4cb662b0f8f,0x7bda3d7e7468b9f380734388e5346fadeed76453b88a,-0x3c1841604238a2f41d5b4cd6aebd17a365b267cc593a,0x17ccf3fd33fcc821f443180560fba4af3d69f9544822,-0x7a0bb222dc0eb3255e2751251068977f5428f6f6366,0x1f459a1cf0cb10f31d446629b7d1d533ce69d98c372,-0x64d9e7ee5683ce994be2dff869b642f49201d7b6d2,0xfa6e119211904b32c0ea8baef7ebd57af2eb5738a,-0x1d1835e4fc05a4d8e2aaae493359d808b6edcc61c,0x2700a737b53934ea9e407d57e65e4150c68bfabe,-0x23dd5141304e5618d349b6387d80f2b7d5f96fe,0x151f85bb5f0a1aa7b8c2a6549ca4bca481c8a6,-0x73c391c2ca9c93aa9bd7cb6c8cf6732ab89e,0x1404ca4d1994026f0323e2f72fb1d9eecfe,-0x166e405ec7a19eb5e57444253d56cb70e,0x6f09b48536a6c0df5027e0127c4d46,-0x416312241eb1ddc1c9798010e65]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 15 60 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 60 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 34 indices rho q19 m19 19 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 34 indices rho q19 m19 19 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x96562cca4c24699640c,-0x5deab493f5f092b298,0x38fcf06d603344ac7,-0x21737af285cf9018,0x12e68101336b90a,-0xa378843d82f90,0x53e6af321cf5,-0x287d7181da0,0x1223ebf4a8,-0x76a7dae8,0x2b32b43,-0xd8108,0x36a6,-0xa0,0x1]
def r20 : List ℤ := raw_ints% [-0xa93201997b1bb5d17e7d68f8c8c48000,-0xf12a22c7e694555f21af671b47f63800,-0x9d9be5799cc4e5a9681686c6d2ebeb00,-0x3ea0a826d17f7632f79ebe6b8c0a40c0,-0x10e9955db7c7910fafef64ca0962f7c0,-0x348f7e2cf49effac8d29343c7a5cd90,-0x7938e88f87cf9b899c0cfe982e4690,-0xd2e058f1c23c6f59b90a97e0fa274,-0x1162e4ebd29facad4f8cdee4b59f4,-0x115113bbe90d80ecd8c5221c7c27,-0xcd3485afce5535cfdc1f7c8380,-0x6da63e537866f0cd8c5eecaee,-0x27fb45f33354de337b2a4eac,-0x8e8fb3ef5b7a0709f0b407,-0xea8c3368762847880e70]
def m20 : List ℤ := raw_ints% [0x0,-0x3dfe6159d97359b2b619a884862eaa7eb0ae096c00,0x3fd19c89366889e61ef3cce234ff504d67459018d00,-0x1f07d98bf747257483df8839eac2f1530017e5a3e200,0x9792fdc0f0add97cb2ccf4824f11b53273095c349540,-0x2093e788581f2baf54b737e8f0bb042a6aa5924e3d540,0x53d207869c98093738a8e9e20959c70c8f80e55b70310,-0xa76531a00b7963fa8bf3f70db6c60373760dc93313320,0x109ac8816a81faab7b05d1a3cfba9280d679088f1dab34,-0x154523ab6be2a32c1f164376a6baf41bef5f2f7738f138,0x1635e34c4c8fe042fb6307008ac507e59ec1d487ad96e0,-0x1304199f6b59be2bed4d764928a049ea125165d2c54a88,0xd61d53cb333abd80abfe1fa754c8284f595d797a094c9,-0x7bcb7239c7146d2c3f49eef4def217ed9375582d14fb6,0x3a9d68477589f6fcefa2ab2b3c10c4305462e5381dfd4,-0x169753e69adb3fb1f0b94234560f25c0a007dceee4762,0x705ede28e5ea0d44c0cb6ec7a855996265b93448f014,-0x1bd2e9bade7d20d8a24066c631aec7bf1faa9d101db6,0x5652acf80154d76e56356fc60719744d48f8fa0dbdc,-0xcd1be2868702616b83970b013626c2d84651f780d2,0x16a7bdd3913c58e6802a495d8bddfd4c0fab922dce,-0x1ca69b96adff5165e0836e617b52312f727edcab2,0x189f1c76dfe70fbbb5c55fcd9d7e8c4434fc8a7c,-0xd661aff1985720064cf5220ced737251cfe916,0x42eb714d6582156c4eb36e3156e197f1fff00,-0xa5f3c46d362f921ae59e210f34d526faf6a,0xa35909b81cac52c0f65f2632847af32e4,-0x2b505f578fc8cf59666ac3a1093150e,0x15292ad1f80b4e2cd22aff65ade1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 15 62 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 62 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 34 indices rho q20 m20 20 2050520284285639246080000 19=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 34 indices rho q20 m20 20 2050520284285639246080000 19 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<21) : intPolyRF (mz e)=rfPoly (C (2050520284285639246080000:ℚ))*rfX^19*(1-rfX)^14*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U4C19
