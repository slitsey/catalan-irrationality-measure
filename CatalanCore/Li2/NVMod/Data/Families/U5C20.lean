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
namespace CatalanCore.Li2.NVMod.FamilySource.U5C20
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,5,20,size⟩
def bases : List ℕ := [1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
def num : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x4807432bc18000,0x5eacaedecbc800,0x397257cd941300,0x1559f4e8394e80,0x57002120c30d0,0x1015c18528070,0x23b19963e098,0x3c84be3fc10,0x4f0feed5cd,0x4f9a7c3d7,0x3d4770a1,0x236d463,0xee467,0x44c5,0xc3,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x7,0x38,-0x69,0xe7,-0x9ed,0x374d0,-0x2cee9,0xaebc3,-0x22f27,0x9d1e0,-0x5377f,0x709bc,-0x2fc20e]
def rhoDenominators : List ℤ := raw_ints% [0xf6570,0x6b4,0x84,0x21,0x4,0x1,0x2,0x31,0x10,0x24,0x6,0x21,0x21,0x8f,0x1b5f]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 21
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤20))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤20 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 21 omega6=padCoefficients 21 (omegaCoefficients 20 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 20 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 21 omega7=padCoefficients 21 (omegaCoefficients 20 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 20 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 21 omega8=padCoefficients 21 (omegaCoefficients 20 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 20 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 21 omega9=padCoefficients 21 (omegaCoefficients 20 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 20 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 21 omega10=padCoefficients 21 (omegaCoefficients 20 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 20 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 21 omega11=padCoefficients 21 (omegaCoefficients 20 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 20 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 21 omega12=padCoefficients 21 (omegaCoefficients 20 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 20 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 21 omega13=padCoefficients 21 (omegaCoefficients 20 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 20 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 21 omega14=padCoefficients 21 (omegaCoefficients 20 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 20 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 21 omega15=padCoefficients 21 (omegaCoefficients 20 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 20 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 21 omega16=padCoefficients 21 (omegaCoefficients 20 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 20 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 21 omega17=padCoefficients 21 (omegaCoefficients 20 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 20 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 21 omega18=padCoefficients 21 (omegaCoefficients 20 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 20 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 21 omega19=padCoefficients 21 (omegaCoefficients 20 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 20 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 21 omega20=padCoefficients 21 (omegaCoefficients 20 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 20 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 20 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 21 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x7938a09b1f88f7131f4000,0x9ee22dc9f89deb3fc203000,-0x637be8fe828cec6a4d256000,0x2798d849c8d30eba697a94400,-0xb3f0261b0071c9c54129ae000,0x26cdd380390a31b973aa544a00,-0x699e8c1404479912a31c5ea800,0xe89457893b790b4b9ab6d62180,-0x1a59c7aa021e997b894a6c8c180,0x27cdbb6776b0bb36be64a183860,-0x3285dcd23b2d1689801a4329bc0,0x362f6d9e01039bda8a41fa1d960,-0x3141c50057a800faa79767ee6a0,0x25fe633873a0a2cd52084ec2cf8,-0x18d844ef6fe077c3dc3ee2f15f0,0xdbc07e3b02e62a70a3d1733b68,-0x6631e74b04ea0f4d6834e0f840,0x27b097e7c15c68c95d5cec1ff8,-0xcbe36c646b10bc3d538f61c50,0x35603396957f82bfe96447338,-0xb2eeb1e7265042faf9b8dd80,0x1d407be044309f349349c858,-0x399ea9788299dfb58806c50,0x512f28dd8e556109ff2308,-0x4b98fc72e4a746b93de20,0x28bda3529edcac38a4b8,-0x9d2c3d7b5d06e576f0,0x8cbb51e8be6fa048,0x1a84b658341e0,-0xd425b2c1a0f0,0x4d24fb2f2340,-0x13493ecbc8d0,0x2f79381d020,-0x364164b370]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 15 29 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 29 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 35 indices rho q0 m0 0 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 35 indices rho q0 m0 0 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x9786c8c1e76b34d7e710000,-0xc32f61002c2d22a0fd514000,0x780b3050fead68c3a695e6000,-0x2ee770467517119161e67b4000,0xd119dd07b7eecbcef330e1e800,-0x2c3529c45367ade58459f996c00,0x75e09c98b32e38c583e36329a00,-0xfe153450d30b9a02971e5880900,0x1c274c6dd1f6a9f128c222db3580,-0x298d1a6c642e3452ce2d9bc70a40,0x337a12ed22d691d87c5f13349800,-0x35d289feac3032209e815b9b68c0,0x2fa3254c3e703ed51ff216a7fb60,-0x23b9690005f639bcefdc09b26ed0,0x16ace60758d4b77b856b976cf900,-0xc2524f517fbefa663afb0ad82b0,0x575f4972e386688f449c0add620,-0x20ba70ed05c2a084234504be150,0xa1b2727c4538ecaa19eb8ad740,-0x28931c8214eaaa15052d2fd4b0,0x81d8f3a64bb6e07adfba38da0,-0x1429c0120d0fb66dc3213b8f0,0x257ccf822c4217d6edb88880,-0x3171e3e66e1a25b8aaa7d90,0x2a9f5bb2222ab0b72be760,-0x14ed524ec3b1063a828b0,0x47ca282cb969174b140,-0x3707ad3f158ab9150]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 15 30 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 30 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 35 indices rho q1 m1 1 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 35 indices rho q1 m1 1 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0xbd687af26146020de0d40000,0xefebc0789ea39b35c57998000,-0x91054f1d3843febbfcebfce000,0x37a7e1b4ea28df4083c4a46a000,-0xf38c69f563011941ce1e34bf800,0x3281de4b1865391b9d7bd6c2d000,-0x8401072b446fdb9fffa29bcb4200,0x116a947235434918f909adfb89a00,-0x1e3678a111c126bc453aa529c4c80,0x2b96b3953ccdd8b6b35a580468880,-0x34bb2c12035f3fbcbe35d43d98080,0x35c5f6870cd53140b3ee3497ef080,-0x2e5ba255167eb14c12f9ae12d77a0,0x21cfe1ad26dbd8ca986cc742a02a0,-0x14d6b1ca4fc29c584c54f27586020,0xad11c54138daffb1915741118020,-0x4b40620c3615b2929ff42a9c6020,0x1b30c3254e31da4045298f087120,-0x8133c3604a3b3178f43f2f4a4a0,0x1f129cfcafa07f73f102395a6a0,-0x5ee73ba40514a3f75ab2c670e0,0xdfddd35e36c74d605d8f195e0,-0x188953b7efb1385916291ac60,0x1e43f0dcdc1a378c86fe3060,-0x181e49a1d57d8f44ba4eae0,0xac4f6125366c0525eb5e0,-0x20c9c44ffc0f7c7e3460,0x157f9418c0a9a6e660]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 15 31 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 31 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 35 indices rho q2 m2 2 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 35 indices rho q2 m2 2 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,0xecc299aef9978291590900000,-0x127145129c11bcaec1953c78000,0xaf650b36c70ba37e4ac71092000,-0x422724af6cc178919c484f560000,0x11c4f685e454dde5ec6fb54bd2800,-0x39ddac3612cc5769f6edf226b4800,0x94509fa627bc4654fbdfc25b62600,-0x132ca4f4d6c5f2c40db3386a6d6800,0x2090314c38dc02906a2af79a8fbf80,-0x2df23983cdade3d9175960ea1f4200,0x364cf0903bf262d5f212ac708dfe80,-0x3607b7b557f60e6eb1c02261d05d00,0x2d633b61fa7a5bff591f294f9b4860,-0x20355796b7b87af4e2547252da8580,0x1347ad545d3ba927a8d9d1a82b71a0,-0x9b389cdc083cf57926cdfd3a77f40,0x4147346a8c7c4001bbc3f26ca5d60,-0x16c12127fe70344c011e7103d8500,0x67fd94ff4a510defafcaf49363a0,-0x17f7755e21d3d4712e8efd8d3fc0,0x45d768d700f2159a44d5704cc20,-0x9c5838a746f3cd72f73eea7580,0x1026c0ceb0230d954b072cfde0,-0x129cd02721b60f21d138812c0,0xdb15fd70041f0c519bb36a0,-0x58d08a389b5d4143055e00,0xef8f918f97e1e1185860,-0x8644be6f87ada98140]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 15 32 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 32 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 35 indices rho q3 m3 3 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 35 indices rho q3 m3 3 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x4807432bc18000,-0x5eacaedecbc800,-0x397257cd941300,-0x1559f4e8394e80,-0x57002120c30d0,-0x1015c18524830,-0x23b19962dfb8,-0x3c84be203dc,-0x4f0feca479,-0x4f9a63a12,-0x3d46ba2b,-0x2369ba8,-0xed8af,-0x433a,-0xa5]
def m4 : List ℤ := raw_ints% [0x0,-0x127f3401ab7fd6335af4b400000,0x16b1f9422bb38e43bac9bb8a8000,-0xd45e36c0e694a83e181711d26000,0x4ec2daecccc8dcd0898892033c000,-0x14ca0a96eaba6f393a24ccfd907800,0x427a71d57791841eb3f5c2ed80a800,-0xa72f2849ccb075286812ca2c078a00,0x15307721bcd5dfbc476c349fb2ab400,-0x233ee2ab7d74e471448c0f6f6788880,0x30a8d2df24bbda29746ecfba3260900,-0x383475e78ea91c9ccff5b40e5760380,0x36973089b0f23b5d36d72e4d4454800,-0x2cb3b8e016322f8d232353201ec21a0,0x1edfb197f3076c98ce51101fd410840,-0x11f494fa53cca8541aa2ea3a8f8d4e0,0x8c29deb188c6dad9c30d3eedbe6000,-0x3905cac0d2a365dd001651d8aeb9a0,0x132d494e4905d7b096c101aeca24c0,-0x544a33697ad2a3eb3a97e7a7a7de0,0x129d18aaae87fb1cf4de5bd4a2980,-0x33bd119006450339ef90373617e0,0x6ddbcf0fcd7c2a077e3303cadc0,-0xab0763ccca20bdd2090ebe2ba0,0xb7f16f267402e9cdb3646a100,-0x7cc224db07a44805da9fec60,0x2dd707890d8f70ba3f38c40,-0x6d5d8acb6103d9068b420,0x345ea8c39e574448180]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 15 34 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 34 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 35 indices rho q4 m4 4 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 35 indices rho q4 m4 4 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0xa5,0x1]
def r5 : List ℤ := raw_ints% [0x2e6cae4b33b78000,0x3cbd45726d966800,0x24a805e8a1a47700,0xd898881df5b8580,0x36bd760b9a22790,0xa070599b209760,0x16001bc50d79c8,0x24c67508e9698,0x2f2cf90dc945,0x2e5d934951a,0x2285655db3,0x1301029a4,0x7629abb,0x1d7a4a,0x3a75]
def m5 : List ℤ := raw_ints% [0x0,0x171f0102165fcbc031b1e1000000,-0x1bf1ad09aadb56b1aff2335f78000,0x1016aef46fb9ff23c5aa0e83c72000,-0x5ded083fe8d17a7a8d5af81804c000,0x185ffd306174f32dd8bf5ab47cbe800,-0x4c93dc8822cf1a763b63fe9faf97800,0xbd0e3fcb3d5e8008b7c7e0cdd0a5600,-0x1780936d2a82c8749cb9cf0ea4835400,0x264ec3947d9c6bfdec892bf86d3fe780,-0x33c54f947c954daa1b86f8a418c00100,0x3a78366d728d54f940d3956f45f05880,-0x37751176ae501d9494051469985d0e00,0x2c486b7042e43a2b0186f11298914060,-0x1dc6c2cc60b8038c5ed78e97be7c0c40,0x10d44b84f11fe470f4f73e05af6c7820,-0x7f688cd342678aa324507ac28d61d80,0x32266e6277947d7c72af27a10ef0e60,-0x1045e16aa84b0ae011614e037ea6fc0,0x44c9f34e7110288bedff19e3a5c920,-0xe8d89f28696a45eb35ab84acde800,0x26926bb187aed44eeca04fa42d220,-0x4da57e789eeed5a35db52867abc0,0x71c4beb9944ced7fa7f9a6c3f60,-0x72144e51d0ac9850b978c4fb80,0x473cbd7c13e692b5fff014fa0,-0x17afa71f461ed6eaecbdc740,0x31e9424facc75a979b70e0,-0x14692279e7740e20f500]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 15 36 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 36 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 35 indices rho q5 m5 5 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 35 indices rho q5 m5 5 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x3a75,-0xa5,0x1]
def r6 : List ℤ := raw_ints% [-0x107290899cd66f8000,-0x156ff7dc1acabae800,-0xce16be14213644700,-0x4bb7b93a27c556980,-0x1305320872345e990,-0x3758a539152beba0,-0x7861c9220677e18,-0xc71ba091405988,-0xfc15714099219,-0xf3a922fd6dfe,-0xb1857f65e7b,-0x5ee9c8218c,-0x2367d8f6f,-0x851754e,-0xf0cd5]
def m6 : List ℤ := raw_ints% [0x0,-0x1ce6c1429bf7beb03e1e594000000,0x226ce7c957981c24939aead71e8000,-0x1385bfd3b8b3d6f65f6eb262ffb6000,0x7030a5116c254866de04fcc9e9d4000,-0x1ca3c91b39b04f52a66cd55b90c23800,0x5871702a054078a77d6692ffafba8800,-0xd674ea1deeb77d5f8359f706bf17aa00,0x1a2964d77ef38370b92bebbe41edcdc00,-0x29ce25f3d0430624e99e9a75d9bff5880,0x375469282dfb4549340b07d600d686b00,-0x3d2031ded6ba680ca62237cd58a1fef80,0x38a3511ed37daf5c7d5c69dad955dc600,-0x2c1dfa5f40a1accbfa5fb3643879b65a0,0x1ce3f2cde55284267c4d704f2d07b1ec0,-0xfdf6a614d9a623eaa16c73d6a05c8be0,0x749092f0250ffda5c0794c706135f780,-0x2c65e31fd0e65bc84cdcddfc3fd63ba0,0xde6a68a2c33211475fd52770c7fa340,-0x3882b3c1e71a0510632ebafad82a6e0,0xb738e3e6bce9107dfb391fd00edd00,-0x1cee8bd5e4966cc427d52f625027e0,0x372f8faba7f19bd369f9d2df6ad40,-0x4c0b28a1276e18a27d238d0bb4a0,0x47049b59a5fea9266f7b8720b80,-0x28c6bd828d70fd4c52cce22660,0xc4015e1061f8f0825ec2b5c0,-0x16c4dba57254c83a7709f20,0x7f2f7a17f3d6786fa600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 15 38 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 38 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 35 indices rho q6 m6 6 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 35 indices rho q6 m6 6 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0xf0cd5,0x3a75,-0xa5,0x1]
def r7 : List ℤ := raw_ints% [0x43c0934c146f9ff8000,0x5806a8c6444ce7de800,0x34b245570434f5ce700,0x13475e90dc16d780980,0x4d1a69c5a5f648f390,0xdf0f8bf127df433a0,0x1e1d95d96625d12d8,0x3166deff7909fb38,0x3dec9e569802609,0x3b1f54fb5373ca,0x2a698cc29d3f7,0x163a8369fbe4,0x813759bc27,0x1d47fe47a,0x32550f1]
def m7 : List ℤ := raw_ints% [0x0,0x2420719342f5ae5c4da5ef90000000,-0x2a6eb8206be52fe9669e182aa438000,0x17b6d13413d9615fbd9d428be4502000,-0x86373db183c231cf86a04f81b999c000,0x21b87f37e78ea8d2971e4b66fa5842800,-0x6668fe4e31949e3914ee96ee9ba2cb800,0xf403d525db588eaa3f41d8099ef2b1600,-0x1d3994a6ef962dbc492b9cf636f9a78400,0x2dcdd6f5de080288bcfb296bd29773e780,-0x3b650ffb17c0e1609546ee30cbeeb9fd00,0x403617a0a534e6a5dab88520b0af0ae080,-0x3a252e1adfffda2745441e587513f49200,0x2c323eb11f5622734a6ab82028bf3fc460,-0x1c31f902c41874a432d97d1b53fb5d2f40,0xf0fead42fe01861eb1a2949299ed95e20,-0x6b51642a14969c7a53017fa64e87d3680,0x278f192c33073882792857cb3e3141660,-0xbf3a5074ca285a44b042a1cf5b8972c0,0x2eb8c4f90858128f8f9b188d2aab2b20,-0x911229dd77116e19fe86a52bd6ed900,0x15d40ac7225f30b7592c725d7d3f620,-0x276e49713261e6986bc41381c0bcc0,0x330f01307af4c8349991207f58960,-0x2c5d8e8f4ec6a684284ca4469e80,0x176440f455ee0762f3140731fa0,-0x6572de6642c1a0a4e31925440,0xa61e376240957a32ef8d6e0,-0x317f9f09259b89bbf9400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 15 40 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 40 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 35 indices rho q7 m7 7 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 35 indices rho q7 m7 7 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r8 : List ℤ := raw_ints% [-0xe2959c4c6b6029298000,-0x12596e7c50bc45a57c800,-0xaf364d5d2341bed7fb00,-0x3fdf7aff04110f9dff80,-0xfe678b8ca2add52ea50,-0x2dc7d8dc51497b4f5e0,-0x6257c7b21f5d39bb78,-0xa042f6d97ec583838,-0xc74f3a6f773e5ac5,-0xbc7d558ddb5675e,-0x85a5b03264e3c7,-0x4508447220d3c,-0x189e69de3913,-0x571ddd914e,-0x90ecc319]
def m8 : List ℤ := raw_ints% [0x0,-0x2d288df813b319f3610f6b740000000,0x345438c028f8db029f0766509f028000,-0x1cd5ddaddca169e800bbda58ff9c26000,0xa0cfdd6d4e29f571c8743f4b992fd4000,-0x27c89a4123cfbbc4520fee5e53e8dcf800,0x76e1a619569c38c4260673076501958800,-0x1167a81d6bff5327018869311eb1baf2a00,0x20c2789f1773a6de391b1381670b9c6fc00,-0x326191f9c87fd1f051001b3eb46abbc7880,0x4008c7d5207d3c11bb6893349ea010c3300,-0x43c57bc29d08e97c8f412f48fba1e51bf80,0x3bff3965c0ebe1cbb04d3260df8d2033e00,-0x2c8428a0061a57f81862d7cf7f2d4f111a0,0x1baca6ddd94ae0962aefa1e3fc9830a60c0,-0xe60e246990a69053e55139ae58a16cfbe0,0x6369da4143dba5d1dc5023aab7d0dd0580,-0x2377f132cfff0e98892b526fe960b67fa0,0xa572dc21c04ba56c73da3ec0483d0b540,-0x26de5de954eed34c9bc61fb84bb229ee0,0x738d806f908dba643abc99e89814ab00,-0x108fbd7bd6d0075970622964a59c9be0,0x1c50f19d8c1226847d0e4b0e851c340,-0x226dccd3b9d8860dc39483e81034a0,0x1bce01ceff6c5b836ee9dcfa72580,-0xd71e683027ae182e8ef1c7e6260,0x3489ed29116ee1176d455583c0,-0x4bb6212237d9a640f8f4e720,0x1340407f0aba6c102d1800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 15 42 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 42 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 35 indices rho q8 m8 8 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 35 indices rho q8 m8 8 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r9 : List ℤ := raw_ints% [0x28c6b35f1a0e45aa658000,0x34b61c1903a9c532150800,0x1f5fdbac84cf9807971300,0xb6722a8a48388f38c2f80,0x2d42915e9fe93fc8134d0,0x81cb59fe52a7c1d0f0a0,0x11586ba79583033fc0f8,0x1c1d270723413ca1218,0x22bde5dbb3f7d1cfcd,0x209b915092e848a3a,0x16e90690ed7b3b5b,0xbb3e03440142e4,0x41dbb9140b5d3,0xe5000268d2a,0x17467b0abd]
def m9 : List ℤ := raw_ints% [0x0,0x3872b176189fe0703953465100000000,-0x4090f10443b662b7ef4f5d8537d2f8000,0x23190f5b550a9534478fe97e1da60d2000,-0xc0f793462765fcbf348d81b7df7d0bc000,0x2f079ede06c03f8fda2250760b5d43c6800,-0x8a577b3975988ddf5c860ff75203f703800,0x13ebd8347d018c3055b86b8cf65431201600,-0x24d897980be05c4c4aeee2245b919ee0c400,0x37a08a16625aeb141c9e504f9c5c55d9c780,-0x455416865ae4fb2551d3b2d6855a32faad00,0x47dc1830d61352d9b31d51ee9e4651622080,-0x3e376960fe95ec7bf5e385b03ec6c04ba200,0x2d13adfdca85f517a6f81a868a372866f860,-0x1b50bdf22964a664bb16f80d2e2e9cc67340,0xdce4d3eefc353336e2b10b7cc87079ee220,-0x5ca506859f3c856a7a9b21ac3cdbb6e4a80,0x1ffeca76b51e98839aba2e24b96d6fcba60,-0x90053a632af75a7dbadad73dc00d7986c0,0x2087ae91f89ddc3cd348b0352884b9df20,-0x5c92af36bee3d72bb630964e3ff1b7d00,0xca2188e762bb94ea3676356990779220,-0x146ea4e0c4aa6ab35d7d7b8952aec8c0,0x174eed864ecff244a847a1a9122d560,-0x117a3447886954e63dda540301da80,0x7bdba854126018969e549ecc8ba0,-0x1b389a09bf05d5b50a599b1c040,0x227d483995008e3648dc312e0,-0x77b7267538fead0c8d5000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 15 44 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 44 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 35 indices rho q9 m9 9 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 35 indices rho q9 m9 9 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r10 : List ℤ := raw_ints% [-0x68c7ba3cf156b455cdb8000,-0x872cdbb66ca0021dfdd2800,-0x50460a7ba91276c7dfaff00,-0x1d19601461377c95f48e180,-0x73284a92c5a6972d4bfa10,-0x1491f7fa31642f873bfde0,-0x2bcfd25c02782dcb9cf98,-0x46b0fbf97b3a6799f6d8,-0x56e60600a6bcb62c841,-0x510ed4c531c8fd2bee,-0x38891061efcfae6a3,-0x1ca01cd6f6dc6fbc,-0x9f60da43666327,-0x222e65a48c19e,-0x36aaf92a0cd]
def m10 : List ℤ := raw_ints% [0x0,-0x468f5dd39ec7d88c47a817e5400000000,0x4fb4473d283b2b88734278150c0a868000,-0x2ac3261eff98fc070cfad395bd096396000,0xe7e3f0b2f63b7e15141815426d0a5b74000,-0x37b4198efa672511679e0a63f6159a01b800,0xa15ff97038f89d13c373cfde36559ad10800,-0x16dde10535cc0ff74bc90f2d9e2e713ce2a00,0x2994492f01d55471bbc500a2c33bb4586fc00,-0x3da60ec6fc8887e4cdb6a3cbfa630f85e5880,0x4b5f080ad1654b6c539704cc31fbddabb1300,-0x4c8a1be3f49db0f65fa1c892e20169d6a9f80,0x40d535b47191d657c4bce015af75f52d61e00,-0x2de1c05982bfd34756d49679b31894e84dda0,0x1b1bcf7b0a0f20273f92345c8eb73d7caf0c0,-0xd54e5b2c58d5fe2dffc81d8e528bac8a8fe0,0x56d7b9cb1c82ffb49353d4ac8681cfd0cd80,-0x1d08a6c9d1e5246f1b1da5a0484899f04ba0,0x7e1cc158ac72d2bf7e732a60cf3a9193540,-0x1b6236879667c3ce8f26b550cb28e4712e0,0x4a939190e2e5cc038fdc09c487075b4300,-0x9afb6d180c9922329cc2869e09bba1fe0,0xecf7ee481787470393c287e4a1431340,-0xfd6b8a63d50d077fb70d29529f550a0,0xb04002bfa9e6939ec9560559ed9d80,-0x476bcd23e0faf135e054b59d6a660,0xe1bac1fe5f37105e891183dc3c0,-0xfb3f012d4fda629138594e320,0x2e80061a0f6f657788e6000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 15 46 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 46 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 35 indices rho q10 m10 10 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 35 indices rho q10 m10 10 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r11 : List ℤ := raw_ints% [0xf61a318bb00f06fdf9f38000,0x13cedffa6526955f27953a800,0xbbd4f819c5d1c61a21960f00,0x43ef62323ad2912d8df8dd80,0x10c28bbf0d6bcb98b99c3510,0x2fc2ca1d3b2c295aceadfa0,0x6562d88e5bb954b8cddbd8,0xa2f6e0916bf4517810938,0xc771a2997649b2315e51,0xb915fe5c22ca3f96aea,0x805118afb23a6ea4ff,0x40824d3b7db210ca4,0x1641e1790f8ed6bf,0x4b96e1cb25ce9a,0x775d6267ba89]
def m11 : List ℤ := raw_ints% [0x0,0x583335488679ceaf59921dde9000000000,-0x627047e2bd8d7f9391b835e18e7c7fb8000,0x342670963f11d3951501040606fae0c22000,-0x1170ff9d45ad8169946cd146e3d5c94a1c000,0x421a101d05d42519f0c9835c56c85f5a6a800,-0xbcaf72bdf9003714855998be892ba2d10b800,0x1a52331f1e09b760611ba38eb60966611c1600,-0x2f1276535453dc7a5a93de741ac704fdf24400,0x4492515048a007433ce87d1fee0a0890a5a780,-0x5245cc56f3c8a5bcf92070e6ad916c1ef02d00,0x51e28a529809a3d1f62527b79b9fd65fc3c080,-0x43e1bc99ed07e0ae66a5e474c554fe94a3e200,0x2ef04a26889f94480f2e75c6dacde7f4d26c60,-0x1b0c238c35caf436ee5ac5e13aeb10b8e1fb40,0xcf2022d0d8360b68a6fbb8a7a22794d87de20,-0x51de97b786c40cbc3b675d2ea324ee7ff8a80,0x1a7fbe5545eee0b568d05cf3ea7ce50a8ce60,-0x6f1178db3a2dba2e4abfa045639537289ec0,0x172e6ff3c22784a2b88164e19c22cd575b20,-0x3c66a4db288c59c46f54551cdcf58512d00,0x776af184253c96e682039de8f8149a8e20,-0xac82e2a8c0d04cd94480dddda541800c0,0xaccf2a715919e591623305bdf6be2960,-0x6f5c9bff31ba9c26108d9fe48203a80,0x293d01fd59aa97487f9e5a57f7e7a0,-0x7503b036349011f3c7e4fad2e840,0x72544122fdf079ca89eb72a6e0,-0x120cf90f0e5f2c52d4714000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 15 48 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 48 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 35 indices rho q11 m11 11 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 35 indices rho q11 m11 11 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r12 : List ℤ := raw_ints% [-0x2195a68cb4f664de97818d8000,-0x2b2eb4380361b7bf04c86a8800,-0x198c2d6fdbab0ef341c5b88300,-0x938c5c2e7bbb5b24b5d9df380,-0x2451d5c06d0543a3239b461d0,-0x673d24f1ab24ef68c8ebe6e0,-0xda866e8c62b934987dec1b8,-0x15e19a63307a50813c7a8b8,-0x1aadd12a31aa077621537d,-0x18a6bf4f7eb56e661a5be,-0x11012ff72cd301ddd53f,-0x87fa66603f250df1fc,-0x2e975c02b523b047b,-0x9cec78737d018ae,-0xf554029dd47c1]
def m12 : List ℤ := raw_ints% [0x0,-0x6e40029aa818425b2ff6a55634000000000,0x79a21579e6511259281a59168d6fd7aa8000,-0x3fa87b1d40e614b61b784e78b266dcb686000,0x1504c1b11a25971a1ffb7d042a8b31d4e94000,-0x4e960149055188a0e6ed24ee03a14780847800,0xdd1fb0d6c067c7ca43bb3aaa68b02ab1928800,-0x1e614e936c9d9cee94ec8554dd4f2ac187d2a00,0x357581b70384eb0fdf417fb703c28d9ed9e7c00,-0x4c8b519eda58a412ec45fac52ea75a71c56b880,0x5a2973d337a42d5eee811f91332e89758695300,-0x57fbadec3d59ccce4ce2dc0d5b1c30b85d43f80,0x4767f2750145628eee5c09496cffd83278a9e00,-0x3042326f700b2529352009a7849ec4c30efa9a0,0x1b20a68d20f633ff5273d5279475bfd316438c0,-0xca37bdf88b612c9a676957575d35d0534933e0,0x4d9c94c8528a51b1663329bf7689991a8afd80,-0x1852675493365d3e813198312686c00c7337a0,0x625df64848716622968641a182e28cbf9ed40,-0x13bb26e0aecdf1e28a98a143ff01fa0f576e0,0x312c37f84d952732bd1a502f0e5a08ea8300,-0x5c72d9bfada407e35486c68af8d4bb663e0,0x7e199dc7c9c2539b80312593cbd56fcb40,-0x763956e865ca8cde5095a09880d535ca0,0x468566fa4e80557930bbf33e07820d80,-0x17d685f8e8b8765921b774276e98a60,0x3caa291934bedc569025029144bc0,-0x33ff176017c1b8f767a958a2f20,0x700be252029812eeab218000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 15 50 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 50 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 35 indices rho q12 m12 12 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 35 indices rho q12 m12 12 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r13 : List ℤ := raw_ints% [0x45069667614e72fde5227618000,0x58a0fa9386abbdec9fca28c4800,0x345a5cdf5d72a5abf10ac7ccb00,0x12dd56477b1e17e91d476c12b80,0x4a26e6dff53c931e9d12ac8950,0xd24fc25fe6409d8c5cecd82a0,0x1bc0dc2134c314337c9e293b8,0x2c567f5703952ef313bab658,0x35e29738a9209aa938c61d5,0x319b273da777e7c844f29a,0x2212bb8be1acc20b3eaa3,0x10f2046c7ce512d6be64,0x5c5d345bf4b36fd0ab,0x134fbe553ac1c770a,0x1df2858abbd8f55]
def m13 : List ℤ := raw_ints% [0x0,0x89d00341521e52f1fbf44eabc10000000000,-0x965c69a49007935a4572c92c293fd01a78000,0x4dc6a0e5f4764a626d4328e10f3b4622bf2000,-0x195d1db871f08371476d9837d7a11753777c000,0x5d9893c4a3b08ffcaf4523d82872888ffdae800,-0x103b80fa2a91cacf6cdf9206a96ecb92ca513800,0x23289bc6600525d05718b874efeefda5d6ea1600,-0x3ce660b73cd7a9b882c49bd5aaa51037cf9cc400,0x55bdfad549886ccccd9adb2263e3423550140780,-0x6330d09d655ec4a295f030144efd266c1427ed00,0x5eefa103ab72a2147ad37e4e08856a2789606080,-0x4b74dceb6e76ea67f78247cb37be758bf9dee200,0x31db66e20bbec3d171fa273d5d4fd48f96446060,-0x1b58dbf9c4cc1f581ed22de2a60e0ea0b0c49340,0xc679a2a5b1de524805508fdd1a6faa932bf3a20,-0x49f9c68a620b0e7500e2cf401ba8a32742a7a80,0x16723d366fe9c3d474d9aa5d89645fb8058a260,-0x5797ac9e775856fddc7d0f7d990933f0d2c6c0,0x10e20618ec5af65651b18d3f3834e0a97bf720,-0x283b17426dccc2997321fa55785a25be40d00,0x47e4876827a819b22e5a08eff6606b5a8a20,-0x5c87e42d26c69659ca30170520dd8cfe8c0,0x512025c28be718b7371b9f1c4053441d60,-0x2cbfd375df31e495a2dc357c861cc2a80,0xdcb06ed26cb08e8101dcc7ea01383a0,-0x1f7394d89e0e9bfc4a2708e5810040,0x17a27265f0ad4621995b6f091ae0,-0x2b71d29c9eeea7ba420b50000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 15 52 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 52 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 35 indices rho q13 m13 13 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 35 indices rho q13 m13 13 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r14 : List ℤ := raw_ints% [-0x86d0f0c42f2b554e7d1a1dbf8000,-0xace39d929b960bee813c4effe800,-0x65fbf063ffdcda1670035d3b0700,-0x24b108e410c17460a2b6e5e3c580,-0x8ff99ddc67dae77860b501f3990,-0x1978cfa2a856abf7dc0b926abe0,-0x35a9f1f8d93d5b1fe34208f7d8,-0x55850d8c0a32f56dd8a6d0d98,-0x67a4c66adcaee7cf6758c9b9,-0x5f1c02f436e0a053a47bd8e,-0x41172ce2db7fb92a3a61db,-0x203c50203a2d22a3ae73c,-0xaedb1251c1ab0bba0cf,-0x245a3d3de5cf820fbe,-0x37ffd6372547b6b5]
def m14 : List ℤ := raw_ints% [0x0,-0xac440411a6a5e7ae7af16256b140000000000,0xb9f4a9a02d321fefb1c0ae1e2a99871f6e8000,-0x5f1bb5dc78eb3a4869b7f82fb4e45b5482f6000,0x1ea5c2fb4fe2884f5d3ff682378dc7d0b40b4000,-0x6fab1d4c0f9318f188aa3a358757a05678a53800,0x131b766b72daf9da6c552165fa1a7a0edabf00800,-0x28cb733eac27f2dcb9f47e6f312a2cfdb78ce2a00,0x4595ef39093abf8e14cff16d96acd4ca9e58bfc00,-0x605f7986d542a6b987dba439daec490eeb6989880,0x6d8983efe76cef38c1601be338a37af2c35961300,-0x66dcf14af984ef8809a43ac5d1c236b6af0fd5f80,0x5017db0fc30e2dc3edb03c1473862ccb584ab9e00,-0x33c0ec3d962d00e167234ff1c4ace1ebbdfc4f5a0,0x1bb4d5a75b8ecc2c987c793033a6fbc80ce3760c0,-0xc3d027c6a3c2b237a6950182eb3c8aec2c2997e0,0x46e2737bcd5bd22bc6b997e0d4d9353dba04cd80,-0x14d377e422a48917f46111d9a53d4e09f901a3a0,0x4e69102c107f81cd8dae3de01a6663731578540,-0xe85053ab94ec121a4d0abb25fcd5ce20a49ae0,0x211287152e2738e3720a6130b5629a6c2e6300,-0x3825d0f5baf93a5af846b6c26e824325027e0,0x442534edc6a1b43e1a1294117dd4622f2340,-0x37d331407c2b3a406eab0fe49440896a8a0,0x1c72afac1996311774c25f432eb87e5d80,-0x7fccc80647da5ea0725925ab1f396e60,0x104e19ebe4f6580ff7889877b66f3c0,-0xabca2fb767767a98ffd4d4463b20,0x10d5fb9a4dd4a21abd5a260000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 15 54 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 54 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 35 indices rho q14 m14 14 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 35 indices rho q14 m14 14 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r15 : List ℤ := raw_ints% [0xfc18aefe55b7ac89d7dc400cf8000,0x142ee5dc089713d611235ac084e800,0xbe41637034f533abc42cf95338700,0x445ae263fcacf38e1d4fad6987980,0x10bce87da1e1e2ae428b4211e9d90,0x2f4c617299e0e9ebccde589535a0,0x63746c03bcc11c34caefe4b2f98,0x9e2609da6c2b7d79c7b3cb9f78,0xbf31e7e6ef580538b724ada59,0xaef71c8901b4ef38c520874a,0x775d6736f5d3c6564f45a47,0x3ae6ec40666f0797fd2a24,0x13e2f17b8b47db23ecf97,0x41d5ba1623c0bfc0c7a,0x64da2ee1b961e1c21]
def m15 : List ℤ := raw_ints% [0x0,0xd7550516104f619a19adbaec5d900000000000,-0xe61330a6285eef1e422f45cbfa9b80755338000,0x74670d6cdd6a40d411b0f06d47f7c48103842000,-0x25145868f4d9ac67c5fb8b2fa769ebe4e007dc000,0x8575346253bd06494e03eb0b1b6a4a26bc0092800,-0x168a02bb37ee2910e23b59485352440f556addb800,0x2f745ef293821578a95c694cbcd898c006e0261600,-0x4fbe8b4cb968c9a8348410b912b1d00cb719b34400,0x6caed7c76bba9767663b2e558489836d6da84ae780,-0x796940a03f6ea37168cb7ef0629fe82e5707e3ad00,0x6fe762e46d7799ab19f84a3aa1bf7baffad2de8080,-0x5562fc989034773df369fdfdfce76c9ccf5a7ee200,0x35f8f56499a6ae81223aab58d2a0013c079f4dd460,-0x1c352f021f5f1ff8c06f38f9cded6c1e111f626b40,0xc22abb1c2cc9b8dbd1bae80fa9d773a15e6b69620,-0x444654846584c73cf9f6eae3358c18b24f8182a80,0x136c67cf1c3ef62d54ff913c973ce2bbb6edf7660,-0x468d183e982ad2809beab3f9595a0501129d2ec0,0xc8c7ba336090944561465a2669d906c911d1320,-0x1b5007b9ad43af01ddb5c4a7287841de8c7ad00,0x2c07db1d7790c595d55c9ce95c6be7215a0620,-0x325bc602ab0c6469904945eca725f0baf90c0,0x2683c42c581a01452325d0c55e5869d51160,-0x121d63741c17cb7885fa67b7e29c9a85a80,0x4a0f2760fd399061c8adc016d08ce9fa0,-0x873af026864ac3a967417a0749bd840,0x4dff7ff49b1355ed0772b4f308ee0,-0x68556a2d7a58c9b172ee940000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 15 56 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 56 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 35 indices rho q15 m15 15 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 35 indices rho q15 m15 15 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r16 : List ℤ := raw_ints% [-0x1c60399d1b75770a1ff4a1ecdf18000,-0x24500c0374bea85d4f1803671554800,-0x155eb1d2853dc7ab0df0fef2ba58b00,-0x7ab14cad176a7f1aa6315ed1c59780,-0x1e0084d57e5dba672d9d3a6ab09150,-0x54a66890c73964b69f390b4b030e0,-0xb1b0599dbab53936b922bbab5df8,-0x11a027afe490041a0888a38a0e78,-0x15433ab9d28ded42809a5665bf5,-0x1369122b4fdb2f507d02f2e85e,-0xd34b0451b65ab0db7a449977,-0x67f0a81f4d19728c8f1da7c,-0x22f7ab1dba256a28fb8b23,-0x7349ede7da9cd26599ce,-0xafc779fcc74cf360a9]
def m16 : List ℤ := raw_ints% [0x0,-0x10d2a465b94633a00a01929a774f400000000000,0x11cc79acb3f50ff71f57937ac6b9f248b52d28000,-0x8e9532ddff73dbd4cda8704f82c4fda7712ce6000,0x2ceacef0753f48dff84ffd716d231f2712ed7d4000,-0x9fc38b2e62f9ef03c7a3eeb562a656d8e19cd3f800,0x1aa47501fcb28f1c40d0086aef49bafb15fa8618800,-0x3756a1f9675ba710b835822f2aeea97670d47192a00,0x5ba60849d3318a34de0c05319cb174f25e385697c00,-0x7af6ede234d87930241c0429140b3e6f58dd4ebf880,0x870f4d8d730cc107d3393a801d233faa4be119dd300,-0x7a38d91a58d5b589da09f4d8764d83b3d3173f4ff80,0x5b6b6a97906b50147d85e12c96d212fe318a4bc9e00,-0x388b018bfdb7ed5b3112582b06853ea521e7ddac1a0,0x1cdb0be5b7aa2e72de6044d093d8e2983c534b708c0,-0xc17d4483ae30566100424e774b1f4279f07c6a7be0,0x4217fd467e99bdfd00b894249a9e55e98fffdd1d80,-0x12350e3b89f524c9f1447acb277f322c867f970fa0,0x3fcbc853c34c4e0121842091d3456e31721f69d40,-0xae5acbe7037510e2349326eb2afd41f0ea19bee0,0x16a7d15a991c3014d294f66f6b883d594fb0c300,-0x22a9cd968835fea96953a45aa0f87930c4e6be0,0x25559088ae3c8adb6fde991ed69bad11a7fb40,-0x1aa2c1f932d73da305124924846affd7074a0,0xb8d4e2d403b5dccf3ff7c2eff8277002d80,-0x2af0e8e64048ec5ff381aa265fc99dd260,0x4615f6b43b7e965c68a2c18772431bc0,-0x2364d475b0d22aea845d94a5c4c720,0x2863bed5c261fa384ae57180000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 15 58 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 58 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 35 indices rho q16 m16 16 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 35 indices rho q16 m16 16 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0xafc779fcc74cf360a9,0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r17 : List ℤ := raw_ints% [0x317516e2ae4303e10570766cf2bd8000,0x3f3bcd49851eebde42acbbad89958800,0x252cec875682ed6a020ac709d58b4300,0xd533667914b891affb0a107231f4780,0x3411cc694bdb331ac1af883c004a1d0,0x92b5f90476138f7f227d31be4038a0,0x1337d162a6d4e43abfacd652c01378,0x1e72e07a1c877d3c74b39df8c0898,0x24a957a383e4a5cdd72b3ee4f5dd,0x216567395f887d46161ccdf8cfa,0x16aa838e928fbc300cf045d1eb,0xb1e9d88e53cb3e08898bbbe4,0x3bab28bc54ad2df384e8d83,0xc4095ca4a5064b3fabaea,0x129b0403b132cafd06ed]
def m17 : List ℤ := raw_ints% [0x0,0x15074d7f2797c0880c81f74115231000000000000,-0x160a20d18c66883b4dc194c197e5516657259f8000,0xaecabcaa6a2678f9b66ceee10a43e99edb05512000,-0x367a408a20b3c112bf2a59a8725d4e2c87b32f3c000,0xbf9060d3e7f4890314756dfec38480023bdaa416800,-0x1f8e67c003cc43cf7451a465171b22974bafde463800,0x40b0167edbf9a16d404df95d35653c18f8a51cf01600,-0x69a00c9cf3c96757638dde34e529d69c3008fe81c400,0x8b90b9c89ef406d8da2f552181b8fb516ab5a8564780,-0x96c655295c483335d3c3d02314aa15e064ffb2526d00,0x86026c1715f7b6d0ccbb9b88b2769fbe948bf2442080,-0x6249e4b1919aed6693ecba0acfb9f175b2b2724ce200,0x3b80023a2966d52bab024c387bc355100dbdd50ac860,-0x1da81ad776981e8dc33a58b95941f562095756504340,0xc1bfae9d699f6e7130f5b0a6554048ed33e37f47220,-0x404c630abe51766ec27b2fcecff83fbfbbc9ea8da80,0x1126cb5727fb837272f0b33d0c5fe918cdbf9204a60,-0x39f780c87c7e1b61bebd3e9f1c267c9eca564496c0,0x981ae44090d358aecf3c570e430e791bd6f8a2f20,-0x12df46cc12a71a0e6e433bae9dace59531d0e4d00,0x1b63d8ea822c9927af072fe250b72366f9d70220,-0x1bc320600f6cc95e7bfbbc224db43887e4738c0,0x127615b66a1824f734640b335ece6577468560,-0x76060cc79711749e90360101a4c9466b8a80,0x18e8cf5e9ec297498da1ed137b54d003ba0,-0x2450c2f7c2f83a12aa36c2b1e5c42b040,0x100d57e7b4f391b4a9bf6d1d1a782e0,-0xfa0ba2f7cbc2d2f078989500000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 15 60 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 60 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 35 indices rho q17 m17 17 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 35 indices rho q17 m17 17 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x129b0403b132cafd06ed,-0xafc779fcc74cf360a9,0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r18 : List ℤ := raw_ints% [-0x53c203fe616f1028ff60e39718b238000,-0x6b0033eb8d4e493a9eff58be4be9aa800,-0x3ed9780f1d690e574553be6c207f20f00,-0x1681418cbf4a30c769e13cbb613d96980,-0x57d7d5f25358aa6040d2ea8038dec910,-0xf7333bb18d740766a4b1b12020ee5e0,-0x20563e72afcd431f0f5146e80b24418,-0x3327d9c74298ff362db5b40308a758,-0x3d7d0a665b97ed0cf8b1e872bb431,-0x37e7b0ae2ae8b4cc4d9c017d622e,-0x25dcaaeed85db78df31f4047e13,-0x1287a6e2dcd2bc321e694e1fbc,-0x6329eb9744496406dd632177,-0x144cbcf4c9e0722323ebade,-0x1eb7e4485a94beac18b9d]
def m18 : List ℤ := raw_ints% [0x0,-0x1a4920def17db0aa0fa275115a6bd4000000000000,0x1b4d2b626b1a285dbb01dbada342f2c5877cad68000,-0xd671be0c1c384f1a503521d0238b98d5a94a5056000,0x42267dab9eafa312909279d86ccdfafa76b11d3f4000,-0xe60de9135ea2089105e6b71837f454cc315f61c0b800,0x257326c1fd47614410dba465f60b02ccd05eba2670800,-0x4bcb757dde5ac6c79f91d28bf0d2d638afb717fce2a00,0x7a10f1d8b09d0ad15de0a2e7eabe4e3cc8248395efc00,-0x9ee6334886fed701710b9fcc08dcf5424a137e68cd880,0xa8e6921c5010d4dfbd583b577d6142cba48941cda9300,-0x937db481e9cc2a86577cae6c1566ce62aeace8f9b1f80,0x6a1b567f27a4b3f9e7f8115abeba808af079dea9b9e00,-0x3ee28a06d2a837004a468b2e972bdd913b3a727f10da0,0x1e9e9a8a10dfde40f815f6499f4e444b924323e25b0c0,-0xc2ed8eb1244ad101ae42c240f6e59d3f966b2f2edfe0,0x3eda7bee671f0d5ccc827e55fc48c15b2d6b5f876d80,-0x103c1d39cd9dec2141767a8cb241b4fc30616ccb7ba0,0x34eae761b4ad34bfaf76e09fdadb5f5510a1b3db540,-0x85491728b9b68a8b49b9c29bb1c4d21c981137e2e0,0xfc8d5bf3b45132a754cc82284d0069fc47bc92300,-0x15b81aa9333165f9899ad77a4af9aecde2fe92fe0,0x14b3ee8c025d4b933b28c6b483fce561c5fdd340,-0xcd24997d953dbee72b4a64c8c01d2180f9c0a0,0x4b738204f3b1329007571cc175dc5eacdfd80,-0xe746521d80feda3ad45292b52854cfab660,0x12cff395dc4cfa1dd95d79d2e8f98243c0,-0x746aff58bb535f51432407157f6d320,0x60b3e0ca4460be80471836600000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 15 62 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 62 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 35 indices rho q18 m18 18 328083245485702279372800 20=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 35 indices rho q18 m18 18 328083245485702279372800 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_18
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<19) : intPolyRF (mz e)=rfPoly (C (328083245485702279372800:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U5C20
