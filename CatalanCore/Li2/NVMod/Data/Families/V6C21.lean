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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C21
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,21,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0x4807432bc18000,0x5eacaedecbc800,0x397257cd941300,0x1559f4e8394e80,0x57002120c30d0,0x1015c18528070,0x23b19963e098,0x3c84be3fc10,0x4f0feed5cd,0x4f9a7c3d7,0x3d4770a1,0x236d463,0xee467,0x44c5,0xc3,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x7,0xe,-0xa8,0x20d,-0x9ed,0x3b8e,-0x2cee90,0x13a85f,-0x369acf,0x117938,-0xa6efe0,0x1f4cfa,-0x85b8f4,0x3bb2918]
def rhoDenominators : List ℤ := raw_ints% [0x290e8,0x6b4,0x21,0xb,0x2,0x1,0x1,0x31,0x8,0xc,0x3,0x21,0xb,0x8f,0x1b5f]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 21
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 16 li0=padCoefficients 16 (liCoefficients 15 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 15 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 16 li1=padCoefficients 16 (liCoefficients 15 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 15 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x36,-0x9a,0x113,-0x129,0x84,0x84,-0x129,0x113,-0x9a,0x36,-0xb,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 16 li2=padCoefficients 16 (liCoefficients 15 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 15 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x7,0xc,0x2c,-0x113,0x2b5,-0x420,0x420,-0x2b5,0x113,-0x2c,-0xc,0x7,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 16 li3=padCoefficients 16 (liCoefficients 15 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 15 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x1,-0x36,0x10a,-0x271,0x30f,-0x174,-0x174,0x30f,-0x271,0x10a,-0x36,0x1,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 16 li4=padCoefficients 16 (liCoefficients 15 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 15 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x11,-0x84,0x11c,0x55,-0x5bb,0xba0,-0xba0,0x5bb,-0x55,-0x11c,0x84,-0x11,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 16 li5=padCoefficients 16 (liCoefficients 15 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 15 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x31,-0x7e,-0x23e,0xb9f,-0x1371,0xa5c,0xa5c,-0x1371,0xb9f,-0x23e,-0x7e,0x31,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 16 li6=padCoefficients 16 (liCoefficients 15 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 15 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x71,0x174,-0xd6c,0x1405,0x1395,-0x52e0,0x52e0,-0x1395,-0x1405,0xd6c,-0x174,-0x71,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 16 li7=padCoefficients 16 (liCoefficients 15 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 15 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf1,0xb0a,-0x1936,-0x48c1,0xf4ef,-0x9ef4,-0x9ef4,0xf4ef,-0x48c1,-0x1936,0xb0a,0xf1,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 16 li8=padCoefficients 16 (liCoefficients 15 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 15 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f1,0x2f4c,0x4eec,-0x2322b,0xb3e5,0x4f7a0,-0x4f7a0,-0xb3e5,0x2322b,-0x4eec,-0x2f4c,-0x1f1,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 16 li9=padCoefficients 16 (liCoefficients 15 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 15 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f1,0xab12,0x41e52,-0x37861,-0x1536b1,0x13e1bc,0x13e1bc,-0x1536b1,-0x37861,0x41e52,0xab12,0x3f1,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 16 li10=padCoefficients 16 (liCoefficients 15 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 15 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f1,0x23c64,0x1aba84,0x36ae25,-0x6b4dcb,-0x9f0de0,0x9f0de0,0x6b4dcb,-0x36ae25,-0x1aba84,-0x23c64,-0x7f1,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 16 li11=padCoefficients 16 (liCoefficients 15 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 15 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff1,0x72c5a,0x8ceb1a,0x2c4557f,0x263502f,-0x5bbcd14,-0x5bbcd14,0x263502f,0x2c4557f,0x8ceb1a,0x72c5a,0xff1,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 16 li12=padCoefficients 16 (liCoefficients 15 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 15 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff1,0x16743c,0x2a034dc,0x1683fa75,0x40833285,0x2dde68a0,-0x2dde68a0,-0x40833285,-0x1683fa75,-0x2a034dc,-0x16743c,-0x1ff1,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 16 li13=padCoefficients 16 (liCoefficients 15 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 15 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3ff1,0x453be2,0xbd38222,0x9949abdf,0x2fd84a38f,0x68336469c,0x68336469c,0x2fd84a38f,0x9949abdf,0xbd38222,0x453be2,0x3ff1,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 16 li14=padCoefficients 16 (liCoefficients 15 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 15 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 15 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^15 := by
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
  | 14=>li14
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
theorem cache_li (j : ℕ) (hj : j<15) : coefficientsPoly (cache.li j)=liNumerator 15 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,0xa9373fbd3848a1000,-0xe48c0f8715c736e400,0x93ae4ef0afaec1bda00,-0x3cc21e74685fdf4c7a00,0x11de42cca9c71f0d9ca80,-0x3ff685f8b5658bd9bf140,0xb501c9eba77a261d6b260,-0x19f6214c53fa3959a88330,0x312c9926ab7346db5e7768,-0x4dd7920586ee8742e14f3c,0x67e360e56cc4365984d4e4,-0x75978c40bef987e9c7be4c,0x714ddf3227f01d58076ca2,-0x5d17de3b0cca0ac37cb433,0x41379e6821a054dd95feed,-0x26e2acc3c0b24eecf361cb,0x13a9430f555cd419b6e0fd,-0x861f01caf37eb160634c7,0x2fd5b9c196306747b2239,-0xe1e2936fdb696fb0898f,0x365fce4373e8d05e7615,-0xa785dc9f337b62b3519,0x1922289cece15c21b67,-0x2d509f88f7a6be0791,0x3a312771032dd401f,-0x310f145307175631,0x17aee8ddecf966f,-0x5069173c378d9,0x3d744853605]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 15 30 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 30 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 36 indices rho q0 m0 0 21838183740172800 20=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 36 indices rho q0 m0 0 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xd3850fac865ac94000,0x11926415c90dac075800,-0xb2b23758cc16673a8600,0x484666218af4b9c46b800,-0x14e2234213fb3a99b07180,0x4966ffc292b54b415bc480,-0xcbd15c9a81eea1d134b720,0x1ca9b4b9d7b682a178091c0,-0x35307a132ebf45af28709e8,0x526ac68f731b8157adf3c50,-0x6b9073b6f1dc42e83a2eb90,0x76f0164f1533ec347302a10,-0x6fd21507d2554567dd248e2,0x5987722e77c717a85819a64,-0x3d07d8a15fb9154c4c4aa6c,0x2359d96ea1624bd023dd2c4,-0x1154f6151ec4127197e12c4,0x7266b027441872db1ba4d4,-0x2761eebd4755c5403e5e9c,0xb2fc4af77125300fc8a74,-0x2952f53a7cd94d44a5ff8,0x799b7d6de496a62430ac,-0x11566d4ad53b4d062ee4,0x1d83642faf509b0100c,-0x237b6234634c298774,0x1baf811349d37d84c,-0xc2b6d40b77d4164,0x24b5ab62407dec,-0x180212005f86]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 15 31 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 31 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 36 indices rho q1 m1 1 21838183740172800 20=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 36 indices rho q1 m1 1 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x108665397a7f17b90000,-0x15a0d58451cc17fa3f800,0xd8774256385e864b0ea00,-0x561e174a3fc645ee9d5200,0x187605c5fc309ed6ca72a80,-0x54770b475d416d6f7aed700,0xe64023fb2208bb4aa5cc0e0,-0x1fc3c09ed82acad9454d42e0,0x39c70c8917ae1c5a5c4ca0f8,-0x57acb8a6d38f2972c9dd6c98,0x6ff319e29277db13639dbd88,-0x78fa302d3b61c7467a7e9038,0x6f061cb9adb8eb544d389876,-0x56a79442f4cbd243830b5c7e,0x397fc7f78e7f1f34b9333ed2,-0x205d570ce68c8d85d73d87ae,0xf63d93cd26ae9532c7265aa,-0x624f3e185d0d2549d102346,0x20ab3f4c3363c96c2913a6a,-0x8ee51f1ef3819858d64256,0x1fa3a20ae0e297bfb93a5e,-0x58e83517ce21389d7fafa,0xc0a2202f227bbe7b1f56,-0x1356037ae3c42b1874ea,0x15bdb91945768d83eb6,-0xfadc6fa5a4c2cf92a,0x643a5902958d3c86,-0x10c1ceff5fc6c7a,0x95f17180ffd4]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 15 32 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 32 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 36 indices rho q2 m2 2 21838183740172800 20=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 36 indices rho q2 m2 2 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0x4807432bc18000,-0x5eacaedecbc800,-0x397257cd941300,-0x1559f4e8394e80,-0x57002120c30d0,-0x1015c18524830,-0x23b19962dfb8,-0x3c84be203dc,-0x4f0feca479,-0x4f9a63a12,-0x3d46ba2b,-0x2369ba8,-0xed8af,-0x433a,-0xa5]
def m3 : List ℤ := raw_ints% [0x0,-0x14a7fe87d91edda740000,0x1aa2bbe230f12f17142800,-0x106813338c79a62a6326e00,0x66c73dfc3c9c72520dcc200,-0x1cb6a20d11167849ff8a6b80,0x617487e5f94c365534fe7200,-0x104f0c0c74df049f31c7cb920,0x2354f1b121e3c7baa9e213de0,-0x3f05f1f747d262ffc9095d148,0x5db344287496493b1d6b81598,-0x751b38fae1e018e230010ce48,0x7bbad7f72e11cb4c8b9362f38,-0x6ee25593d509685dc957f157a,0x54660c29183a6e596dd51a63e,-0x3687912bd5ddc58cd474e0f32,0x1dd59ca7667a14b1eaea5d7ee,-0xdc34b1e3b0ad3085737ce07a,0x5518595d1cf0ef9ac280e706,-0x1b4c7a82b084c865ff89c40a,0x72eaa21519ee406fb95ce96,-0x1865d57db4aed292fa07636,0x41723ed0f0cbd5c7cbff3a,-0x869eebe5af1d35a5767b6,0xcbd55cf8f6366fdf64aa,-0xd61fda875b324b97ef6,0x8e85b02412e022136a,-0x33ab1e4420363e326,0x7a5c7ab65b1f63a,-0x3a7bc334f4498]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 15 34 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 34 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 36 indices rho q3 m3 3 21838183740172800 20=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 36 indices rho q3 m3 3 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0xa5,0x1]
def r4 : List ℤ := raw_ints% [0x2e6cae4b33b78000,0x3cbd45726d966800,0x24a805e8a1a47700,0xd898881df5b8580,0x36bd760b9a22790,0xa070599b209760,0x16001bc50d79c8,0x24c67508e9698,0x2f2cf90dc945,0x2e5d934951a,0x2285655db3,0x1301029a4,0x7629abb,0x1d7a4a,0x3a75]
def m4 : List ℤ := raw_ints% [0x0,0x19d1fe29cf669511100000,-0x20d1ed06ede0ef30cadf800,0x13eacd386a5a5e539129ca00,-0x7adb918f06001e6c83165e00,0x21c6b441f5f7676aa63d38280,-0x70bce172047ad009df56a7600,0x128a4ba2b48eb582881b0006e0,-0x2770f9532b89a207c3e552f8a0,0x45069178449bc4cc7900697e38,-0x64981fffd38c1ae2c99b4f6008,0x7b1c1ffc2611ab180584bd0a18,-0x7f3a0ea693d9c65726c5d811e8,0x6f62493efd561fbda3a24b8e06,-0x52b47d45e0d8168d6960c16caa,0x340be56d739e337fa12d2eb366,-0x1bafc34ef2df1619a647996c3a,0xc6496de995310ea7b895fcc5e,-0x4a2d6859e7539c7c172873c42,0x16f9515c5426443a50987b42e,-0x5d1235c4c533ff1b7e296872,0x12f1a8b456b276289b7b2402,-0x307e8b1542ea2e975c3b77e,0x5ea6ce82553a577ace3a12,-0x87032441cbe76c9516a4e,0x845e7ebd71dd61f28012,-0x5134ee6249bdce09c0e,0x1aab4415f9a1d485e2,-0x37d3adda8b730dfe,0x16cb1ee9777e50]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 15 36 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 36 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 36 indices rho q4 m4 4 21838183740172800 20=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 36 indices rho q4 m4 4 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x3a75,-0xa5,0x1]
def r5 : List ℤ := raw_ints% [-0x107290899cd66f8000,-0x156ff7dc1acabae800,-0xce16be14213644700,-0x4bb7b93a27c556980,-0x1305320872345e990,-0x3758a539152beba0,-0x7861c9220677e18,-0xc71ba091405988,-0xfc15714099219,-0xf3a922fd6dfe,-0xb1857f65e7b,-0x5ee9c8218c,-0x2367d8f6f,-0x851754e,-0xf0cd5]
def m5 : List ℤ := raw_ints% [0x0,-0x20467db443403a555400000,0x287622dd232e4520ac956800,-0x18344c658ad9e54eb38153e00,0x9316b44f1a871b67251256a00,-0x27d04c5aaa00852421f379df80,0x82c051e950bdff9e05cefa0c00,-0x15242b441c4c92d99c864cf5920,0x2c2f221357584511924ee7aba60,-0x4be6c70dec62c1b57169431c8c8,0x6c797fdd44c8308ce53b7abdeb8,-0x820cf37e88c3d5a878602e0dd28,0x8382f4565e50bc1e7b7fc66b3d8,-0x70846c54f2b55810ef7324b779a,0x5187cd62107d5a9a50c2cbb9366,-0x31fd237c002df4302c5371e8c8a,0x19dc8b1016cc83d8ad8d5f90056,-0xb3c0ef11d0cbffbe731ce11692,0x411ad6dc5abbea1b1736bce08e,-0x1377cff0a270eb2319dafbed02,0x4be557e0c13e0934c11ad19de,-0xecebcb2c22f89e8dc528c4ee,0x24293e4c3d82e90be9b346b2,-0x42ef8f077626fb2f44021be,0x59e0b54c972ab5c02ee662,-0x52279c1565b544acbaebe,0x2e6440f0363fbec76c22,-0xdc79f16ad8649bf9ee,0x197633439ad8c2db2,-0x8e087e89cdcc60]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 15 38 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 38 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 36 indices rho q5 m5 5 21838183740172800 20=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 36 indices rho q5 m5 5 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0xf0cd5,0x3a75,-0xa5,0x1]
def r6 : List ℤ := raw_ints% [0x43c0934c146f9ff8000,0x5806a8c6444ce7de800,0x34b245570434f5ce700,0x13475e90dc16d780980,0x4d1a69c5a5f648f390,0xdf0f8bf127df433a0,0x1e1d95d96625d12d8,0x3166deff7909fb38,0x3dec9e569802609,0x3b1f54fb5373ca,0x2a698cc29d3f7,0x163a8369fbe4,0x813759bc27,0x1d47fe47a,0x32550f1]
def m6 : List ℤ := raw_ints% [0x0,0x28581d21541048eaa9000000,-0x31e85924bca6e57337886b800,0x1d71b4d9e23b7336f485861a00,-0xb05de49cc92da762f746f23e00,0x2f0668a512e99c9afd8e3541680,-0x9805d8758d8661756fc3893ae00,0x182ddf5408bfb4a12f955e5146e0,-0x31ab025f138e193b4922344117a0,0x53c9b573198ba28b40a09c969138,-0x757ad5e34a11ed01ee18dc02f3c8,0x8a093330082da50b778f5d8d1e58,-0x88a3f96d5fa47970ce45cc8516a8,0x7249f716ea202896c85911948686,-0x50d7aeae27255036d37ec12f8c1a,0x304eaa01b5082b554657d23e7ef6,-0x184f99d37e7e7d55d8dfd178592a,0xa405ff9d9ed5ab34260cdf9416e,-0x39862c4edfb1335d4a9a28d0df2,0x109ba5b03e6289f98cbff84b97e,-0x3e4d2f4aa7bb47eb24e0bab6a2,0xba62182b4600437fb64611452,-0x1b20f0270b6940189ec8789ce,0x2f990253f6f60e948519e0c2,-0x3c1da386d73aac5bce2f01e,0x332d67851d04cc997a0042,-0x1a909e6907009e1ab28de,0x72043ce74210c936e12,-0xb9ba09050b23e6d4e,0x3746ea67cf0f540]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 15 40 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 40 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 36 indices rho q6 m6 6 21838183740172800 20=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 36 indices rho q6 m6 6 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r7 : List ℤ := raw_ints% [-0xe2959c4c6b6029298000,-0x12596e7c50bc45a57c800,-0xaf364d5d2341bed7fb00,-0x3fdf7aff04110f9dff80,-0xfe678b8ca2add52ea50,-0x2dc7d8dc51497b4f5e0,-0x6257c7b21f5d39bb78,-0xa042f6d97ec583838,-0xc74f3a6f773e5ac5,-0xbc7d558ddb5675e,-0x85a5b03264e3c7,-0x4508447220d3c,-0x189e69de3913,-0x571ddd914e,-0x90ecc319]
def m7 : List ℤ := raw_ints% [0x0,-0x326e2469a9145b25534000000,0x3d96fd894b9e20ac572ebfa800,-0x23daa316beb0bfc9b1545a0ee00,0xd3c97658bc177c1614505acda00,-0x37a6ecd12ba8ab3fd0b12a8dcb80,0xb1300e5742c68753a2e114c6a800,-0x1bbbf825090767434b5ea11d60120,0x380553cdee45addcb9c53a3b9b460,-0x5cd8c18f52647aa69b1980895fcc8,0x7fc5ba5cf2cd03557414e20fd2538,-0x93315c5fbdf92d0fa11d80fee7ea8,0x8eaf2574d0cd672b67b3ef9308058,-0x74b6d37792cc529dfda0ad54fd5da,0x509e4622f4775ff3a266587f70c46,-0x2ef64ff29664ef68074930bdb3daa,0x16fee5ffef251171e625088665236,-0x96a0d415c9ad98889bd5494521b2,0x332827573d39d81e68b2fdf2d7ee,-0xe42b60a3996209cf7a7e8fd3ba2,0x3378a8c55d3929ec399cf9aa83e,-0x93898f00d14f2eb7fe2a254f0e,0x1478a3d6c19204523cbd6b7d52,-0x22065c88c1c03e94090c7bd1e,0x28638a4818949b31fb6b6e02,-0x1ffd334b0df5f614ccba61e,0xf3e61f3a0476df2f69ac2,-0x3b00a17bbbe44dcd8d4e,0x54a24fd73f499b9752,-0x157f9467a2f19980]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 15 42 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 42 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 36 indices rho q7 m7 7 21838183740172800 20=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 36 indices rho q7 m7 7 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r8 : List ℤ := raw_ints% [0x28c6b35f1a0e45aa658000,0x34b61c1903a9c532150800,0x1f5fdbac84cf9807971300,0xb6722a8a48388f38c2f80,0x2d42915e9fe93fc8134d0,0x81cb59fe52a7c1d0f0a0,0x11586ba79583033fc0f8,0x1c1d270723413ca1218,0x22bde5dbb3f7d1cfcd,0x209b915092e848a3a,0x16e90690ed7b3b5b,0xbb3e03440142e4,0x41dbb9140b5d3,0xe5000268d2a,0x17467b0abd]
def m8 : List ℤ := raw_ints% [0x0,0x3f09ad84135971eea810000000,-0x4c0b25ac2049b30d0e137397800,0x2bb3a433b28544b52f029f9baa00,-0xfeb0802c9e83ec8ef2e27f822e00,0x41fd0aca5e4287f3fb49d15a97a80,-0xcf030ba843a8fc9415e5102f2aa00,0x1fe712d6cdb03b7b16de1459164ee0,-0x3f64f6cf4680bb24e0e3651e32bba0,0x6744c01b3af44b6ff85974f327e338,-0x8b8b00dc0e43e8b174f3c35c0e0cc8,0x9dabae571b2f61440f40fbe6596d58,-0x95ba7522f3b753319c7c983453eba8,0x77d19eaae6d027be313fb9849476c6,-0x50d7e903482f2d89099195013f7b9a,0x2debfa838771722283cd1a72fc4376,-0x15e2425f646dcb9220bdd979b70aaa,0x8b30c224ea1e35c52dd23e70d84ee,-0x2dc8534dbbe4873c51237f83e4172,0xc5293b097f0719d21eb1d6cf7dfe,-0x2ac9f129b4953340dc3db303f422,0x757ceed96a90dc8feb55f8ad852,-0xf88b9eb8040f2025fa4a8a1c4e,0x1871be25b941dbbf5c6c691e42,-0x1b3fcb55578687520c735909e,0x140ed7eb4d0be58e682dc2c2,-0x8c379d8eb6bbce8f10be5e,0x1e8ca31a10fdf11f38092,-0x268c5fee823c90d54ce,0x85b0ebd104f9c500]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 15 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 36 indices rho q8 m8 8 21838183740172800 20=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 36 indices rho q8 m8 8 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r9 : List ℤ := raw_ints% [-0x68c7ba3cf156b455cdb8000,-0x872cdbb66ca0021dfdd2800,-0x50460a7ba91276c7dfaff00,-0x1d19601461377c95f48e180,-0x73284a92c5a6972d4bfa10,-0x1491f7fa31642f873bfde0,-0x2bcfd25c02782dcb9cf98,-0x46b0fbf97b3a6799f6d8,-0x56e60600a6bcb62c841,-0x510ed4c531c8fd2bee,-0x38891061efcfae6a3,-0x1ca01cd6f6dc6fbc,-0x9f60da43666327,-0x222e65a48c19e,-0x36aaf92a0cd]
def m9 : List ℤ := raw_ints% [0x0,-0x4ecc18e5182fce6a52140000000,0x5def0b7bc274ebf000e60543e800,-0x3551452be34e0111454fcd6819e00,0x132b741f01ebbf89ee5ec17b82ea00,-0x4e6437b272e8e45b646a18c683f780,0xf26b99624b4f00af960262ba216c00,-0x24ccb01c783fe89176479222e432920,0x47f82c3c8d583bdd9fdd79e7f44a460,-0x73475fdbe1cbcf8d3d52f384817bac8,0x990403b043dab50ee36d0963a107138,-0xa9a5165993dd8450dac217faabe3aa8,0x9de051ea9a7454e28998d51e71e7c58,-0x7ba3bd4600e77c8a946ab0797a8049a,0x5182ed98e02cb17dc4039b1553e2606,-0x2d294a5c3d77b6f838fc3881ed6cbea,0x14f30375e2f72eb5c03e21e4db03bf6,-0x81676b270dddc9b29859728ba6f6f2,0x2939b379d71c727449f4c51e41a0ae,-0xab6a4ab721082109b1ffd632f26e2,0x23c91c790e7d539b6b304cd1e3cfe,-0x5e1987bc4fbd980651374778a4ce,0xbd9d48481b3e2507f7ee3c32692,-0x11a51f48cc93cbfa470f3e227de,0x1274e5e62d91da7c9016672342,-0xc9cf7ee5f3f7e6b5de0485de,0x50be58de3d4efd5721d6f02,-0xfd2d673eb9b70ce39850e,0x118c794c9c43bc0cb792,-0x33edb557306f20600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 15 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 36 indices rho q9 m9 9 21838183740172800 20=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 36 indices rho q9 m9 9 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r10 : List ℤ := raw_ints% [0xf61a318bb00f06fdf9f38000,0x13cedffa6526955f27953a800,0xbbd4f819c5d1c61a21960f00,0x43ef62323ad2912d8df8dd80,0x10c28bbf0d6bcb98b99c3510,0x2fc2ca1d3b2c295aceadfa0,0x6562d88e5bb954b8cddbd8,0xa2f6e0916bf4517810938,0xc771a2997649b2315e51,0xb915fe5c22ca3f96aea,0x805118afb23a6ea4ff,0x40824d3b7db210ca4,0x1641e1790f8ed6bf,0x4b96e1cb25ce9a,0x775d6267ba89]
def m10 : List ℤ := raw_ints% [0x0,0x627f1f1e5e3bc204e69900000000,-0x741620122a0f9951a14bcd40a3800,0x411bddc254aec7ad0ddb918ec6ba00,-0x171e0e9506edba31f092eea6cf7de00,0x5d4bcd8255a352ff7b22ae087ce3e80,-0x11c87fc46db4f01d7d98824f7adf9600,0x2a90394fbab6814c840e857783ad96e0,-0x51f6106c9be70131334c406e558413a0,0x8124dd1a68e7ad40a5bb9d151acbd938,-0xa874308f8acf83c6cf49e7eb926c42c8,0xb7524a72c48d2b30fc88c97e03fe3f58,-0xa74026373ab64d92fc8ebc3acf0329a8,0x803981b749a3b8d7f5bc24f06bec0e06,-0x529f8c50ddc45825b0ae250603539f5a,0x2ca95b323f4f7d3d1b47c0f871cb57b6,-0x142bb86e7f87a4932151abf52bc8226a,0x7904ff3669f521ff20c15f08beb962e,-0x25583bd6dceedaafcebacaf1b6b3832,0x95ec0b6530a395929c795f86e0433e,-0x1e1a76930ecc195d01eb3377006ae2,0x4bc980c84213fbdf1b721c0882712,-0x916639472915a7a88fd2042fbb8e,0xccb6391f1ea09da2f04eefacb02,-0xc8c1795785e442979eadee87de,0x7f3d90c4664602d3e50425282,-0x2e901d8b3225749748bc529e,0x832c69d94225a393d58052,-0x7fc135c1953fed72590e,0x14286dbd59df7ed400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 15 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 36 indices rho q10 m10 10 21838183740172800 20=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 36 indices rho q10 m10 10 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r11 : List ℤ := raw_ints% [-0x2195a68cb4f664de97818d8000,-0x2b2eb4380361b7bf04c86a8800,-0x198c2d6fdbab0ef341c5b88300,-0x938c5c2e7bbb5b24b5d9df380,-0x2451d5c06d0543a3239b461d0,-0x673d24f1ab24ef68c8ebe6e0,-0xda866e8c62b934987dec1b8,-0x15e19a63307a50813c7a8b8,-0x1aadd12a31aa077621537d,-0x18a6bf4f7eb56e661a5be,-0x11012ff72cd301ddd53f,-0x87fa66603f250df1fc,-0x2e975c02b523b047b,-0x9cec78737d018ae,-0xf554029dd47c1]
def m11 : List ℤ := raw_ints% [0x0,-0x7b1ee6e5f5cab286203f400000000,0x8f87192091e0777eb7d3547cc22800,-0x4f94445d23948312126bcdeb18fce00,0x1bea5817cdb8f8b16599f275bb3bfa00,-0x6f3b81812b24a26fd368441143f98380,0x14eb2b5cbc6c4fdd3b341516a22967000,-0x315c3e1d60fcd12d5d17b49391c73b120,0x5da065f96bafd3b1c568f0049d96c8c60,-0x912e0dbc9b7631796cffe82ed0c3e58c8,0xba2ae398363617a9bcc31789089f0bb38,-0xc6f11bcb321facb65402df3a5691d58a8,0xb1ff126b38ece7cde82e9e6daf974be58,-0x85a2658e143f8680b1174a24b0e679d5a,0x542fcf2f2fdc38ab5532269b20168e346,-0x2c6892253ae09c0ae6eb8e085b045ceaa,0x1387f33537e1e6eda8910f9d38c8c8536,-0x71d5552532f0988243fe3a41c7d2dcb2,0x2206e2e27cbfccb85710742f8bde06ee,-0x83e28cc865643b067bf5e0355762ca2,0x197770272420a80410b524f7f56433e,-0x3d5da29455ff999ceb334ba605290e,0x700adf99621222474389d67176a52,-0x95129ac9858252bd8608a010601e,0x88f29920db7129f49e6dedc7f02,-0x506ae73d9379b5d4358f87371e,0x1ae2aee201474c2c9019209c2,-0x43f93ac0490da1411f3fe4e,0x3a18dbbd49d4eae584252,-0x7d20763c26fb8e9800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 15 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 36 indices rho q11 m11 11 21838183740172800 20=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 36 indices rho q11 m11 11 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r12 : List ℤ := raw_ints% [0x45069667614e72fde5227618000,0x58a0fa9386abbdec9fca28c4800,0x345a5cdf5d72a5abf10ac7ccb00,0x12dd56477b1e17e91d476c12b80,0x4a26e6dff53c931e9d12ac8950,0xd24fc25fe6409d8c5cecd82a0,0x1bc0dc2134c314337c9e293b8,0x2c567f5703952ef313bab658,0x35e29738a9209aa938c61d5,0x319b273da777e7c844f29a,0x2212bb8be1acc20b3eaa3,0x10f2046c7ce512d6be64,0x5c5d345bf4b36fd0ab,0x134fbe553ac1c770a,0x1df2858abbd8f55]
def m12 : List ℤ := raw_ints% [0x0,0x99e6a09f733d5f27a84f1000000000,-0xb18875a46d23fbafb4a69944268f800,0x6159a3473eeb1dc74c4ccbe36c4c4a00,-0x21c0d0bcf4fc55b0e602281d4e5ae0e00,0x84d8e1440716825f923238f760c71a280,-0x18a8fadd7a3d5358e6c64182fc42b12200,0x3963f77147b17f45b233f3aa3f3d91fee0,-0x6b45c194d280f3504822cae4257d0d1ba0,0xa3c2d8bed3af32e9e6cc68e69b6b2e0738,-0xce85a0a4644438ea457e25cc5c955304c8,0xd8ca0b1bb6ccb3705da6f36c546206a558,-0xbe48c7c4b25ebee5368a0204a2229983a8,0x8bf156b173b63d008b3a61ba4b85c1f946,-0x56378e3bc0be4bc33527a5d8e468fa4c1a,0x2c647817bb88371f4598ca797c345f12f6,-0x13041c66d33f85d21e228a6e50fbe4eb2a,0x6bada50e20b9baac926347557484ece6e,-0x1f2e26125130f568d81a32f57fbf58bf2,0x74ac02b98f717eae485e6f7802febb7e,-0x15a96b205fecdc4cb3ceda66644116a2,0x31f1fb7661a73ca6365e325c512a8d2,-0x56be6a0f6e6b954dafac855a3e25ce,0x6cfec5e332528bd4230a4b424fcc2,-0x5db835e924cfc96f52ea63f6921e,0x32efa3e4cb4cf4ee13ee9b92f42,-0xf8a5d6b6b4ab0a4a7d52649de,0x2339ec338ccd26a7009b2d12,-0x1a67d011ed352c3706d84e,0x308431471e142ba5000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 15 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 36 indices rho q12 m12 12 21838183740172800 20=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 36 indices rho q12 m12 12 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r13 : List ℤ := raw_ints% [-0x86d0f0c42f2b554e7d1a1dbf8000,-0xace39d929b960bee813c4effe800,-0x65fbf063ffdcda1670035d3b0700,-0x24b108e410c17460a2b6e5e3c580,-0x8ff99ddc67dae77860b501f3990,-0x1978cfa2a856abf7dc0b926abe0,-0x35a9f1f8d93d5b1fe34208f7d8,-0x55850d8c0a32f56dd8a6d0d98,-0x67a4c66adcaee7cf6758c9b9,-0x5f1c02f436e0a053a47bd8e,-0x41172ce2db7fb92a3a61db,-0x203c50203a2d22a3ae73c,-0xaedb1251c1ab0bba0cf,-0x245a3d3de5cf820fbe,-0x37ffd6372547b6b5]
def m13 : List ℤ := raw_ints% [0x0,-0xc06048c7500cb6f19262d4000000000,0xdbb01574717e841c2f78642cedca6800,-0x7730b58e2c2dc68d1a9a1b98770e97e00,0x28dd0fc8adfce8514d189aa65b2b858a00,-0x9eee13b186116d3e5ace6d645cf291ef80,0x1d21c52df452d063252494adf49e82d1400,-0x42e51f2d21e1d9bf53f117a180e73b21920,0x7b442c2dbeda651d23382534fec1633f460,-0xb9552fec04c1f906e01a8e54d07b1fd6ec8,0xe5f2be52f714b5bc937f3d02e41e7058538,-0xed322c19f94ab9fb4ff1004418c43ba56a8,0xcc508f86b5aa608680d5ebaf38ca3c1c058,-0x933d1a50c75d7d1a7865f50cce9fe29a61a,0x58bc781b708f63544137df4b33ede190686,-0x2c9b9ded75c2967454b57873867b87f6b6a,0x129d508cff5f4b93d79f121e27e52290476,-0x666abfc327b3a56c8846e22ce33886d472,0x1cbae4b16dab5b21f55208c300faba132e,-0x67c75b02f42a5d6efdff63517072fec62,0x1285e162591095fcbd4fd56d13e87bf7e,-0x28da27ce299d9f29c22293d4ee772f4e,0x43756fde02ca1c44bb8a7fc41b91012,-0x4fff3ecfcda3ae6cd01bd06863b65e,0x4053dc7b7cb78944fed25dac80cc2,-0x2053977e1a1ac42368890da8d65e,0x8fdb7fd558b0f668b6bd979682,-0x12416113bda81daf90aa1458e,0xbfeb089bafa87e7049af12,-0x12cd2226653923f46000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 15 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 36 indices rho q13 m13 13 21838183740172800 20=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 36 indices rho q13 m13 13 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r14 : List ℤ := raw_ints% [0xfc18aefe55b7ac89d7dc400cf8000,0x142ee5dc089713d611235ac084e800,0xbe41637034f533abc42cf95338700,0x445ae263fcacf38e1d4fad6987980,0x10bce87da1e1e2ae428b4211e9d90,0x2f4c617299e0e9ebccde589535a0,0x63746c03bcc11c34caefe4b2f98,0x9e2609da6c2b7d79c7b3cb9f78,0xbf31e7e6ef580538b724ada59,0xaef71c8901b4ef38c520874a,0x775d6736f5d3c6564f45a47,0x3ae6ec40666f0797fd2a24,0x13e2f17b8b47db23ecf97,0x41d5ba1623c0bfc0c7a,0x64da2ee1b961e1c21]
def m14 : List ℤ := raw_ints% [0x0,0xf0785af9240fe4adf6fb890000000000,-0x10ff6a5abc2a2f86be38e28ac5a605b800,0x920cc2d8e65fd85b040b72ee08a3d45a00,-0x31885a2c704f1ed6574b5a541f8c71bbe00,0xbe722a21a8bb1fecbeb43ba80013c75a680,-0x227c35f12f50125bc3bd2b38e6098bc90e00,0x4e2a2fc7d9cd8854154807eca14cbb3006e0,-0x8e0c5571194bc42f619f06bd390c4901c3a0,0xd26ca7ba017da69936956c7b6b5defa8fd38,-0x100f49a56c138c08e65cc0a63216a7e7c0ec8,0x1048d67735a7dba20c1c326a1aa68b9dde358,-0xdc5286357eec69cdc4760f706b34eabfc5a8,0x9ba0c80ccbcc566f797e09bd9c372ca52c86,-0x5bc62682f9bf48fc21905c9785c4d7da64da,0x2d0d891fb526a9e92e3cb7790934afc04236,-0x125144b6dec5314b6f6d628cb32c6b4e1fea,0x61efa6ae2ec6a8f9feb1f0220d09c74e2ae,-0x1a9d7c3d02be3c2dfdca37449a4b69913b2,0x5ccd12212aaa9d02171fd094bfb4a93fbe,-0xfeb8745282ae5b2e877d1fe1fd2da5662,0x219304cbaaef890cf89bf48daa26aee92,-0x34af89ea893939bd08a3922f0f1cc40e,0x3aecf19c929bb8b423ca2c39ec69a82,-0x2c4679a908ea8a1c0fe09e7338105e,0x148d772f3a8e1a498377cc3f84802,-0x534b79fe28dfd6ec266ec59c51e,0x975b7b685d23e9375a035f5d2,-0x5721cd76b06652cd256db8e,0x74837dd5d3e0a0e54000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 15 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 36 indices rho q14 m14 14 21838183740172800 20=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 36 indices rho q14 m14 14 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r15 : List ℤ := raw_ints% [-0x1c60399d1b75770a1ff4a1ecdf18000,-0x24500c0374bea85d4f1803671554800,-0x155eb1d2853dc7ab0df0fef2ba58b00,-0x7ab14cad176a7f1aa6315ed1c59780,-0x1e0084d57e5dba672d9d3a6ab09150,-0x54a66890c73964b69f390b4b030e0,-0xb1b0599dbab53936b922bbab5df8,-0x11a027afe490041a0888a38a0e78,-0x15433ab9d28ded42809a5665bf5,-0x1369122b4fdb2f507d02f2e85e,-0xd34b0451b65ab0db7a449977,-0x67f0a81f4d19728c8f1da7c,-0x22f7ab1dba256a28fb8b23,-0x7349ede7da9cd26599ce,-0xafc779fcc74cf360a9]
def m15 : List ℤ := raw_ints% [0x0,-0x12c9671b76d13ddd974ba6b40000000000,0x150cfd3f9d1f5716d2433ce716b526ca800,-0xb31ac6f3478d99ce2be3af47deed5c2ae00,0x3c1cd6115a36b74465132e79fd062b499a00,-0xe4935fd30f962629aaa2d52b6b734e0a3b80,0x28e751a44dd70b1d836c919c4570b31abd800,-0x5b8d235bd45ca423da3cb36bf0ab5fa7b6120,0xa425769562fbd47d721ebcd67bc4ffb37fc60,-0xefaacf5cb98dfa5f8daebba7bf34283f91cc8,0x1202573b4d093d10108f838f60e85c2df69738,-0x11f512e3aebd3f0b76ac62e563e988bdb66ca8,0xee951469e600ab221f01786ef73af627e2a58,-0xa53c609d5b39c27bc928dd619a8c2d5c836da,0x5f5e3ea1fa4495994b898a0c6c30b612ef9c6,-0x2dbaa7833456ac1275a5b3d9cacb5a200d82a,0x121e30f2ae4bf0aacbd18a0e41362108e73b6,-0x5e246e9bd6179f99a4c851805b09db29a432,0x18c916ae2bdf1a8feb378dd9fc86f96c276e,-0x5369b5d92aede94aaffc55f0a7f50a8a422,0xdc02636c2e7a5182c02ce28a6628cf03be,-0x1bb8405ab98d9d3d968a072a3385fc658e,0x2950d1ebe190882a161cae1116d7695d2,-0x2b8d3eea2131b18428ea75adc06c0c9e,0x1e8d3187b6b08f1a7d47432dd395a82,-0xd167f568729674e646708f7b2159e,0x30427f716416e573603b6d410342,-0x4e6c0c2ba45c3ee928fc674cce,0x27896abc7967870629561bd2,-0x2d1ad0a1647c072398000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 15 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 36 indices rho q15 m15 15 21838183740172800 20=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 36 indices rho q15 m15 15 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0xafc779fcc74cf360a9,0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r16 : List ℤ := raw_ints% [0x317516e2ae4303e10570766cf2bd8000,0x3f3bcd49851eebde42acbbad89958800,0x252cec875682ed6a020ac709d58b4300,0xd533667914b891affb0a107231f4780,0x3411cc694bdb331ac1af883c004a1d0,0x92b5f90476138f7f227d31be4038a0,0x1337d162a6d4e43abfacd652c01378,0x1e72e07a1c877d3c74b39df8c0898,0x24a957a383e4a5cdd72b3ee4f5dd,0x216567395f887d46161ccdf8cfa,0x16aa838e928fbc300cf045d1eb,0xb1e9d88e53cb3e08898bbbe4,0x3bab28bc54ad2df384e8d83,0xc4095ca4a5064b3fabaea,0x129b0403b132cafd06ed]
def m16 : List ℤ := raw_ints% [0x0,0x177bc0e254858d54fd1e906100000000000,-0x1a14876c5fadc5bb9e27742d49f71e107800,0xdbcf4c68dbfdcc8e6f2f15c3147a0772ea00,-0x4909811ea686c71c7d941265968685618ee00,0x112c3bc6d71ce109fd84fa59f99b67223f4a80,-0x309c522ed8de66a6e366237594c8cad7415a00,0x6b7acf1bc738aa3d096f4a8255d77f6992aee0,-0xbe320ca09d4a5be9be829d1c82bbf6c68ccba0,0x111d072b6745e3ce1a484ea123e80521ada3b38,-0x1443c0dd4539813ab959d5e5f515b5c0c7c10c8,0x13e07b5b39c9cebb4b701b2ac44184713964958,-0x1036ab0cb4d399c210facc0c363078e36afdfa8,0xb03584164274dbbfcf5d7c1e0bd1b2a8e2f7c6,-0x63909e0e72c7c4b1d509cce7d8d6c8e72d359a,0x2ea44970634c76882d32c6cf08c039ac465976,-0x1202bf85d0a56c44093538c1ec83f9a46a6caa,0x5af55d0b9e6cfee3ac6d1350fb59a9aa7c6ee,-0x17331f07ef28259c9a7d20103ee46770b0b72,0x4b59ab026cbf717a9877a45c120834a953fe,-0xbeefee0d53333073b2c11dae19086938622,0x16fcaf2f2b26bed34e2b6e0c19aa72abc52,-0x208677773712ce9b97cc9ab83c5e773a4e,0x204aae4d6d3bba43fd1c6cb4ea7434042,-0x15219cfd69a134ff0455471d2de4869e,0x858a568f59e7ab5290f8a4e88db8c2,-0x1bf9cc6b9dbd341017b5a469ce85e,0x289fff9b1f02575c1fd25a8f692,-0x11ee2973cb2a2a2b60f0726ce,0x1173c66fc110fa7d850000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 15 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 36 indices rho q16 m16 16 21838183740172800 20=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 36 indices rho q16 m16 16 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x129b0403b132cafd06ed,-0xafc779fcc74cf360a9,0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r17 : List ℤ := raw_ints% [-0x53c203fe616f1028ff60e39718b238000,-0x6b0033eb8d4e493a9eff58be4be9aa800,-0x3ed9780f1d690e574553be6c207f20f00,-0x1681418cbf4a30c769e13cbb613d96980,-0x57d7d5f25358aa6040d2ea8038dec910,-0xf7333bb18d740766a4b1b12020ee5e0,-0x20563e72afcd431f0f5146e80b24418,-0x3327d9c74298ff362db5b40308a758,-0x3d7d0a665b97ed0cf8b1e872bb431,-0x37e7b0ae2ae8b4cc4d9c017d622e,-0x25dcaaeed85db78df31f4047e13,-0x1287a6e2dcd2bc321e694e1fbc,-0x6329eb9744496406dd632177,-0x144cbcf4c9e0722323ebade,-0x1eb7e4485a94beac18b9d]
def m17 : List ℤ := raw_ints% [0x0,-0x1d5ab11ae9a6f0aa3c663479400000000000,0x2052c22dbbfd0cb371645cc75e9573b38e800,-0x10df7a2b68800ba7603d8891db429181875e00,0x58d7184e695bd622090bc0f128ceb5e9242a00,-0x14ac8aa35896ad98878048b04bbbe5b507d6780,0x39e0f0788e7686e1598b5620b10a1ee15a5bc00,-0x7e76fedf3bd21c37b5893233d4d32aee31e8920,0xdcf59a46ed7882d6f3c27303b011d6dd84a2460,-0x139c3f91829adc48abfceaeea09f51d96953a2c8,0x16e1146df703a178080e54b65fbc90ddfa5f5138,-0x16153d742bb422ffc197221834d95197e3f33aa8,0x11b33f933ea321abedfeb473b6ac845e7e7fdc58,-0xbcb84ced23c20aa075c4373f9df24fee1772f9a,0x686b95223d8aee73fd90070bc620a0a5fda6506,-0x2fcca1c5a56104519618e54c9063f87c2f8ecea,0x11fe00049324131f67f57c233a2ec3c8371baf6,-0x5852337abf774213f6090dce9e1f28487683f2,0x15d2d361aa65c674eaf22878a1b7b88517abae,-0x4465e7b5d9663aa57af14cb200d942ac96be2,0xa678fa0c16e3639a0c66cd1abc3ef5e737fe,-0x1324a3c1f3b9887e400a68196250100443ce,0x19b31c443722768affbee5a55d4f4803392,-0x1803bdc4cde8b755f89ac7bf31f73aaade,0xea5b93baa76b9c75902984abbf74e042,-0x5544b03b014111b2d605e1509d51cde,0x103963ef43d12d5066fdb82d2aa802,-0x150a4b76b728f07d246ffa8a3c0e,0x8208f8898030a2f2ebfa7a092,-0x6bfde5c697b1f464860000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 15 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 36 indices rho q17 m17 17 21838183740172800 20=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 36 indices rho q17 m17 17 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x1eb7e4485a94beac18b9d,0x129b0403b132cafd06ed,-0xafc779fcc74cf360a9,0x64da2ee1b961e1c21,-0x37ffd6372547b6b5,0x1df2858abbd8f55,-0xf554029dd47c1,0x775d6267ba89,-0x36aaf92a0cd,0x17467b0abd,-0x90ecc319,0x32550f1,-0xf0cd5,0x3a75,-0xa5,0x1]
def r18 : List ℤ := raw_ints% [0x8a4974af84e969a73036f148d5662b8000,0xb087c57ac9300e282a67fc7537856e2800,0x679aa0d027122c0db2b46327940e85ff00,0x251079360947d6b897a3b832fcaf529580,0x9086e756da568b239a0fd621a88f17610,0x19642bceab71a07c491573c98b1e6cba0,0x3514086ec5b2deebd6c54b418dbc5f58,0x53da33fa1644153f1fc02947c0c01b8,0x64a2b44dddd1bd27c6b2fb0213c661,0x5b57853b395ca7e490af6d72423aa,0x3dbe8de707e3e8529bc970db1b8f,0x1e2763f3491a2437f7cc99083a4,0xa0fc311470bf95f170d7ee06f,0x20ddd6c6f78a0dc032a3025a,0x31955ee531edb19f2e9db9]
def m18 : List ℤ := raw_ints% [0x0,0x24b15d61a410acd4cb7fc1979000000000000,-0x2813404a9c32dd72e5a211b2bcc17965393800,0x14bcf41f254b0dc0a36111db3d20c01c50bfa00,-0x6c2e2b7f352064f0853a1dfdcc54f3bb6a19e00,0x18ece3342d8818c1940688d52594354270c78e80,-0x450a3475fe5e5f179e98da2dc9b0333d8c9d0600,0x95217cc78bfcc8b522416d210712a259e7a6f6e0,-0x1015bac83463dc9d54d63e2233082f69d54c833a0,0x168991f32b14e4cfbb02fe8225e1f290d8f110138,-0x19ea6d545cf37a651b82122f0a5660d8391408ac8,0x189f5b64a42c952acd2a6903c7cd67bff35195758,-0x1366233f945db7ddb3dfa26596d0002377a2951a8,0xcaf8560ce631939eed5c7f26bb8715968e871b06,-0x6e003028f612fcb75c8ee0bac160231ab72a6e5a,0x3136cb76ceae6a3f9ff4334b30f42fc5f782a8b6,-0x120f5d9fa293f7434ea967dd62146cc3666d016a,0x562d9f064333ef363738cc59845886d9945ab2e,-0x14a0edc82b846206c6dcbd948d225cce2180332,0x3e61674cc7a3edeb1553e95134ef180c4f683e,-0x91ca5b10ff65535c0af3f0debef4f8c6db5e2,0x1001ba06b84618943d4507d92b19268b2e212,-0x1460ae0626af9d44eb2f76eb93871b98588e,0x11e8c275bf461fa357ec934f96cf66f1e02,-0xa2c52286a9e0dff1b828d5c4500e444de,0x3681bb82b9a77f0fdab4a109d9b81182,-0x9697e0d5824406eda69ea8038c239e,0xae4e6c8a0b800af6ac363b2fbf52,-0x3ae8b3127bb28eec3437e1aa0e,0x29bec715403e3e27dd40000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 15 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 36 indices rho q18 m18 18 21838183740172800 20=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 36 indices rho q18 m18 18 21838183740172800 20 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_18
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<19) : intPolyRF (mz e)=rfPoly (C (21838183740172800:ℚ))*rfX^20*(1-rfX)^15*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V6C21
