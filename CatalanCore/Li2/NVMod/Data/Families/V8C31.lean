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
namespace CatalanCore.Li2.NVMod.FamilySource.V8C31
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,8,31,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
def num : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0xaa0e21ade5832af82bc00000,0xee7082e8c2bea939f6ac0000,0x9ea0f9555646fd7532200000,0x42a271b616be135b4e54d000,0x13d72ed2b5aa1429f8869c00,0x474bb133c49d8c5f331b700,0xc8c3b4dd2156316ca4a740,0x1c6548d6327f08c131ec80,0x348a94331d3eb7f7d1f10,0x5072525113d8b2c862e0,0x66c0212d623faa701ec,0x6e0894c822341df848,0x630a1259c6d7e82f7,0x4aef3a13f975bfaf,0x2f8d4f8d0dce361,0x192fd2f6633335,0xb0c45d9a46f6,0x3f767ae01d6,0x125558a70e,0x4280d9d2,0xb645b3,0x162cb,0x1b5,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x37,0x37,-0x1ad,0x1b5f,-0x8f,0x861,-0x3272b,0x832a3,-0x10d0971,0x10d0971,-0x186061d,0x106ab4d,-0x485eee26,0x242f7713,-0x9640371,0xcb76f53b,-0x1b0db09,0x1fd09c7,-0x3cac037,0x19dac177]
def rhoDenominators : List ℤ := raw_ints% [0xa0fa49ba60,0x17203890,0x168da0,0xdd6e8,0x52e0,0x1a90,0x1c20,0xe,0x1c,0x1e6,0x12c,0xbd1,0x4a4,0x35a,0x16c,0x4ffb,0x28a0,0xdd0,0x20460,0xa18,0x2860,0x1a7f0,0x8595a0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 31
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤30))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤30 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 31 omega8=padCoefficients 31 (omegaCoefficients 30 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 30 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 31 omega9=padCoefficients 31 (omegaCoefficients 30 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 30 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 31 omega10=padCoefficients 31 (omegaCoefficients 30 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 30 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 31 omega11=padCoefficients 31 (omegaCoefficients 30 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 30 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 31 omega12=padCoefficients 31 (omegaCoefficients 30 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 30 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 31 omega13=padCoefficients 31 (omegaCoefficients 30 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 30 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 31 omega14=padCoefficients 31 (omegaCoefficients 30 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 30 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 31 omega15=padCoefficients 31 (omegaCoefficients 30 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 30 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 31 omega16=padCoefficients 31 (omegaCoefficients 30 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 30 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 31 omega17=padCoefficients 31 (omegaCoefficients 30 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 30 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 31 omega18=padCoefficients 31 (omegaCoefficients 30 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 30 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 31 omega19=padCoefficients 31 (omegaCoefficients 30 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 30 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 31 omega20=padCoefficients 31 (omegaCoefficients 30 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 30 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 31 omega21=padCoefficients 31 (omegaCoefficients 30 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 30 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 31 omega22=padCoefficients 31 (omegaCoefficients 30 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 30 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 31 omega23=padCoefficients 31 (omegaCoefficients 30 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 30 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 31 omega24=padCoefficients 31 (omegaCoefficients 30 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 30 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 31 omega25=padCoefficients 31 (omegaCoefficients 30 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 30 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 31 omega26=padCoefficients 31 (omegaCoefficients 30 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 30 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 31 omega27=padCoefficients 31 (omegaCoefficients 30 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 30 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 31 omega28=padCoefficients 31 (omegaCoefficients 30 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 30 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums29 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens29 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349]
def omega29 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums29 omegaDens29
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_29 : padCoefficients 31 omega29=padCoefficients 31 (omegaCoefficients 30 29) := by decide +kernel
theorem omega_spec_29 : coefficientsPoly omega29=omegaNumerator 30 29 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_29
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums30 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens30 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384]
def omega30 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums30 omegaDens30
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_30 : padCoefficients 31 omega30=padCoefficients 31 (omegaCoefficients 30 30) := by decide +kernel
theorem omega_spec_30 : coefficientsPoly omega30=omegaNumerator 30 30 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_30
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x16,0xe7,-0x604,0x1c93,-0x66de,0x12375,-0x29a30,0x4e11a,-0x7970c,0x9ddf6,-0xac398,0x9ddf6,-0x7970c,0x4e11a,-0x29a30,0x12375,-0x66de,0x1c93,-0x604,0xe7,-0x16,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 24 li0=padCoefficients 24 (liCoefficients 23 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 23 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x15,0xd2,-0x532,0x1761,-0x4f7d,0xd3f8,-0x1c638,0x31ae2,-0x47c2a,0x561cc,-0x561cc,0x47c2a,-0x31ae2,0x1c638,-0xd3f8,0x4f7d,-0x1761,0x532,-0xd2,0x15,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 24 li1=padCoefficients 24 (liCoefficients 23 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 23 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x13,0xaa,-0x3b6,0xe79,-0x29a3,0x5ad8,-0x9768,0xbd42,-0xa406,0x419c,0x419c,-0xa406,0xbd42,-0x9768,0x5ad8,-0x29a3,0xe79,-0x3b6,0xaa,-0x13,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 24 li2=padCoefficients 24 (liCoefficients 23 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 23 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x60,-0x130,0xab,0xb5b,-0x3c90,0xb5b0,-0x18216,0x26f4a,-0x31350,0x31350,-0x26f4a,0x18216,-0xb5b0,0x3c90,-0xb5b,-0xab,0x130,-0x60,0xf,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 24 li3=padCoefficients 24 (liCoefficients 23 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 23 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x7,-0x22,0x29e,-0x109b,0x3f8d,-0xa758,0x13d28,-0x1b04e,0x18b62,-0xa24c,-0xa24c,0x18b62,-0x1b04e,0x13d28,-0xa758,0x3f8d,-0x109b,0x29e,-0x22,-0x7,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 24 li4=padCoefficients 24 (liCoefficients 23 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 23 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x9,-0xf0,0x6e0,-0x1a6d,0x37fb,-0x2310,-0xaf50,0x2b34a,-0x57f26,0x79b90,-0x79b90,0x57f26,-0x2b34a,0xaf50,0x2310,-0x37fb,0x1a6d,-0x6e0,0xf0,-0x9,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 24 li5=padCoefficients 24 (liCoefficients 23 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 23 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x29,-0x1ea,0x6d6,0x555,-0x8673,0x23bc8,-0x56fb8,0x89832,-0x8913e,0x3a904,0x3a904,-0x8913e,0x89832,-0x56fb8,0x23bc8,-0x8673,0x555,0x6d6,-0x1ea,0x29,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 24 li6=padCoefficients 24 (liCoefficients 23 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 23 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x69,-0x1f8,-0xce8,0x8fa3,-0x23715,0x47dc0,-0x34380,-0x77586,0x1b30ca,-0x2bec30,0x2bec30,-0x1b30ca,0x77586,0x34380,-0x47dc0,0x23715,-0x8fa3,0xce8,0x1f8,-0x69,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 24 li7=padCoefficients 24 (liCoefficients 23 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 23 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xe9,0x39e,-0x5762,0x18195,-0x1af73,-0x7e798,0x25d868,-0x4e3dce,0x593cc2,-0x286f0c,-0x286f0c,0x593cc2,-0x4e3dce,0x25d868,-0x7e798,-0x1af73,0x18195,-0x5762,0x39e,0xe9,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 24 li8=padCoefficients 24 (liCoefficients 23 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 23 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1e9,0x1fe0,-0xf550,0x1653,0x11161b,-0x42e5b0,0x6d6410,-0x1b1a16,-0xe61bc6,0x1e53490,-0x1e53490,0xe61bc6,0x1b1a16,-0x6d6410,0x42e5b0,-0x11161b,-0x1653,0xf550,-0x1fe0,-0x1e9,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 24 li9=padCoefficients 24 (liCoefficients 23 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 23 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3e9,0x8ba6,-0xcc1a,-0x12916b,0x55850d,-0x5c4af8,-0x11f8578,0x4556cb2,-0x623163e,0x306c2e4,0x306c2e4,-0x623163e,0x4556cb2,-0x11f8578,-0x5c4af8,0x55850d,-0x12916b,-0xcc1a,0x8ba6,0x3e9,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 24 li10=padCoefficients 24 (liCoefficients 23 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 23 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7e9,0x1fcf8,0x9b588,-0x62477d,0x509d4b,0x3786660,-0xb4874e0,0xadf8b5a,0xa2c9eaa,-0x245122b0,0x245122b0,-0xa2c9eaa,-0xadf8b5a,0xb4874e0,-0x3786660,-0x509d4b,0x62477d,-0x9b588,-0x1fcf8,-0x7e9,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 24 li11=padCoefficients 24 (liCoefficients 23 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 23 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfe9,0x6acee,0x55466e,-0xdda5eb,-0x5e2fcf3,0x17c241a8,-0xafaff58,-0x525df24e,0xab99df42,-0x5f9e8fac,-0x5f9e8fac,0xab99df42,-0x525df24e,-0xafaff58,0x17c241a8,-0x5e2fcf3,-0xdda5eb,0x55466e,0x6acee,0xfe9,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 24 li12=padCoefficients 24 (liCoefficients 23 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 23 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fe9,0x1574d0,0x1f01120,0x3f00db3,-0x2ef78a85,0x134574f0,0x1379194b0,-0x25270e636,-0x1f916de6,0x47b6ebc10,-0x47b6ebc10,0x1f916de6,0x25270e636,-0x1379194b0,-0x134574f0,0x2ef78a85,-0x3f00db3,-0x1f01120,-0x1574d0,-0x1fe9,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 24 li13=padCoefficients 24 (liCoefficients 23 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 23 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fe9,0x433c76,0x9b0a136,0x42322b15,-0x90ba1d73,-0x328441db8,0x7c89fd6c8,0x5242f7532,-0x1c99ab6cbe,0x1319b41344,0x1319b41344,-0x1c99ab6cbe,0x5242f7532,0x7c89fd6c8,-0x328441db8,-0x90ba1d73,0x42322b15,0x9b0a136,0x433c76,0x3fe9,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 24 li14=padCoefficients 24 (liCoefficients 23 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 23 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fe9,0xcf7368,0x2cd2b178,0x22fe97fe3,0x37313d6ab,-0x1c4324ee00,-0x1082681340,0x9284a0a13a,-0x4381793576,-0xe53470e730,0xe53470e730,0x4381793576,-0x9284a0a13a,0x1082681340,0x1c4324ee00,-0x37313d6ab,-0x22fe97fe3,-0x2cd2b178,-0xcf7368,-0x7fe9,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 24 li15=padCoefficients 24 (liCoefficients 23 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 23 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffe9,0x279d83e,0xc5f9a23e,0xf092c4d95,0x4b1a0e538d,-0x4017a2ed18,-0x2885d326718,0x1a6a85a2332,0x706da66ddc2,-0x63ff99ac84c,-0x63ff99ac84c,0x706da66ddc2,0x1a6a85a2332,-0x2885d326718,-0x4017a2ed18,0x4b1a0e538d,0xf092c4d95,0xc5f9a23e,0x279d83e,0xffe9,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 24 li16=padCoefficients 24 (liCoefficients 23 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 23 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffe9,0x78486c0,0x350eff490,0x5d30548313,0x32e71c7ecdb,0x66a8746fd90,-0x11d9dc7b0cb0,-0x28fb6743da56,0x346655aebbfa,0x4affb3416390,-0x4affb3416390,-0x346655aebbfa,0x28fb6743da56,0x11d9dc7b0cb0,-0x66a8746fd90,-0x32e71c7ecdb,-0x5d30548313,-0x350eff490,-0x78486c0,-0x1ffe9,-0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 24 li17=padCoefficients 24 (liCoefficients 23 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 23 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffe9,0x16bb9246,0xdf0d5eb86,0x21ee44ba195,0x1bc2f4ec660d,0x7ec236240f88,0x569bc6bb8308,-0x225fec5dce84e,-0x257bf12bf813e,0x38a6ffaef51a4,0x38a6ffaef51a4,-0x257bf12bf813e,-0x225fec5dce84e,0x569bc6bb8308,0x7ec236240f88,0x1bc2f4ec660d,0x21ee44ba195,0xdf0d5eb86,0x16bb9246,0x3ffe9,0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 24 li18=padCoefficients 24 (liCoefficients 23 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 23 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffe9,0x448eb4d8,0x39ce8dd068,0xbdd23e87343,0xd89aeec4340b,0x627dcad7367a0,0x10c8de45907860,0x28609f5c8fb1a,-0x32fb5b97c6c596,-0x2a7d3fc337d3b0,0x2a7d3fc337d3b0,0x32fb5b97c6c596,-0x28609f5c8fb1a,-0x10c8de45907860,-0x627dcad7367a0,-0xd89aeec4340b,-0xbdd23e87343,-0x39ce8dd068,-0x448eb4d8,-0x7ffe9,-0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 24 li19=padCoefficients 24 (liCoefficients 23 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 23 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffe9,0xce641c8e,0xed63c17f0e,0x40896bd23715,0x629b78ac38a0d,0x3fa30a23f2d428,0x12867c727ad1128,0x23ae326df34f2b2,0x60661e626ef642,-0x409bf45b60f2aec,-0x409bf45b60f2aec,0x60661e626ef642,0x23ae326df34f2b2,0x12867c727ad1128,0x3fa30a23f2d428,0x629b78ac38a0d,0x40896bd23715,0xed63c17f0e,0xce641c8e,0xfffe9,0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 24 li20=padCoefficients 24 (liCoefficients 23 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 23 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffe9,0x26c9c53b0,0x3c81b748b00,0x158159dec0c73,0x2adc0c7349283b,0x2511683a5e92030,0xf8e855f227eebf0,0x34fe96684e7f758a,0x57faffb85bba59da,0x3074f74488b60310,-0x3074f74488b60310,-0x57faffb85bba59da,-0x34fe96684e7f758a,-0xf8e855f227eebf0,-0x2511683a5e92030,-0x2adc0c7349283b,-0x158159dec0c73,-0x3c81b748b00,-0x26c9c53b0,-0x1fffe9,-0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 24 li21=padCoefficients 24 (liCoefficients 23 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 23 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw22 : List ℤ := raw_ints% [0x0,0x1,0x3fffe9,0x748b4f916,0xf5832bdaed6,0x70f9e52003e15,0x120696e20500f8d,0x1430a3db518b9cc8,0xb5b6370ec414ff48,0x37c03514c8bfff432,0x9d1bd88346c3fe442,0x105e832482f4889604,0x105e832482f4889604,0x9d1bd88346c3fe442,0x37c03514c8bfff432,0xb5b6370ec414ff48,0x1430a3db518b9cc8,0x120696e20500f8d,0x70f9e52003e15,0xf5832bdaed6,0x748b4f916,0x3fffe9,0x1]
def li22 : List ℚ := liRaw22.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_22 : padCoefficients 24 li22=padCoefficients 24 (liCoefficients 23 22) := by decide +kernel
theorem li_spec_22 : coefficientsPoly li22=liNumerator 23 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_22
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x17,0xfd,-0x6eb,0x2297,-0x8371,0x18a53,-0x3bda5,0x77b4a,-0xc7826,0x117502,-0x14a18e,0x14a18e,-0x117502,0xc7826,-0x77b4a,0x3bda5,-0x18a53,0x8371,-0x2297,0x6eb,-0xfd,0x17,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 23 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^23 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
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
  | 30=>omega30
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
  | 21=>li21
  | 22=>li22
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 30 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 8 31 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
  · exact omega_spec_30
theorem cache_li (j : ℕ) (hj : j<23) : coefficientsPoly (cache.li j)=liNumerator 23 j := by
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
  · exact li_spec_21
  · exact li_spec_22
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x176e867790ceede4510c23c900,-0x32a4bab286b8210ede99b8ef2c0,0x353d503d988dd982385fdd49fdc0,-0x24455221c95997f38559f066ae8f0,0x1200662fe749f90881494b0be4ee30,-0x6efdcde4a0c27fe0c9cb982a8e95a0,0x22901f7accb9ce7a12a7d89e492f3a0,-0x8f01b14bcae6962085481f64193ca2c,0x1f51ede426eaa016e58b70189e5f00fc,-0x5e545252b39ef8f5ee7b36ceb6f7a0a8,0xf6f71bec6b9eabc9a77d36a86814c6a8,-0x23717c9f3a8a5dcf7cf785c41d38a9c54,0x47e3364ded00396340bb860498daa8064,-0x8184bd3ccd1041441a05a85db6fb600f0,0xd03a28b707046f54f80a022a9d95c0ab0,-0x12bce10177f15ad7d702bbbcf711b04f13,0x183acdfa383ea288319d674fdd835e0087,-0x1c332f2066447edf0413411269d645c7c2,0x1d965b222c0d8fc6d64e1632536edc8382,-0x1c03996d56d389d460810a588a77699bb1,0x17f31a605eba0f3c496d092f6fc84407e5,-0x127d1e30c019681705c3bdab9e7eed3ebc,0xce22e09b3edba3b3538eef30b3d5568ac,-0x818c28f3ed79ebf1f8a02fa4a9508c82b,0x49540b41dead1452d6e7a726131ab313f,-0x255096baa00e0fa44653a4d3309aea7b6,0x1107b551e335fab5c7f10d493c330acc6,-0x6f329e58e8dcf3e32cae8eb3937b1531,0x286d58c72e2c41c01001cf5adeda9365,-0xd0908db2dff4980f1d7ec42e2463b18,0x3b521d89a929a49efcf1666de6dae38,-0xec93e515bd30f368c5c4c4e128c251,0x3345696d4f16ffdc7b034f0dc8240d,-0x9919c56c68bf227687fce36bc666e,0x185191597dd27c4c1c96a240c0f4e,-0x33d706a89311480a8210775738bb,0x5b00b1f60d227d1d5c12074bbb7,-0x807c26d6db5a855515602fe8dc,0x8d6d2f2d191756d1f39faf10c,-0x7450e1230afb06b766553ac5,0x43472559f620dba42bf30b1,-0x18f7da1440aab848defd72,0x51bebcfc565265d815c2,-0x6ebcbf84290845529f,0x1ec63f0f7bccc9eb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 23 42 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 42 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 54 indices rho q0 m0 0 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 54 indices rho q0 m0 0 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x2bef3c202f83fe0c17f6c318e00,0x5ddfa4d6b44c1f8efdaa735f9c80,-0x6189fd036d17d3f5eae672ffe0a00,0x41a9fa39b46cf21dc4c60316965420,-0x203234368a6581687f3b9e5d3ad7a00,0xc4106f74444288c348382ac39d93d40,-0x3c49755c806da84271eceed966a81980,0xf63cbbba73dc2edd7856b534f78d13a8,-0x35388ac9505030c88658b3a983d992780,0x9e2399dd701d69952ed36be76b8ae9050,-0x198579e44b3b066f1f78db081d5724abe0,0x39c79c97a4c09c1912adb113560992a6f8,-0x7380fead533a453d61b7c673ad634d01e0,0xcd079a4317c732d644342eb871cdbb6660,-0x144a296ac1295df99f0ea679a2cd09b0180,0x1cc24232dfa519c2d798dad9ee1ed59f47a,-0x2497f451eb46abf6f5f595d3533ab5b5780,0x29e3c32d7a2776b4e5f14fc7a2d0c7ab904,-0x2b34effdc8156e343c19bf5e58a8ce3b5d8,0x283218dfb69eaaebf921a9e0e970c6e8d26,-0x21becb34d7027087008b452105cbbeec958,0x1990fbb402b6f5f503cb1cb2fc652134318,-0x1178fcd93b5d992a77da90018e8bb6566e0,0xac3093096c20f1c6c9e8a473b50c5f669a,-0x5f72f79050981f3f34d96ce8e2f5df9f60,0x2f86efc092f469299c12012b449be4124c,-0x153488444b8b72f3f75bfcaeb718224c78,0x87393fcf8478ab154aa8c3ac558529656,-0x2ff5e7381157fac393d0d630b7a6b65f8,0xf116ec23bb1ab92e5c9663d257717af0,-0x42b95cbc3dc2d3699848ed33856a8800,0x1028a5c0d4f99b7c2cf2596a06de479e,-0x365867c53ebac126ca6552e5b0a6700,0x9d17856152a56a3cf8251bfe01c11c,-0x1819c731a584a114d9333744bf84c8,0x317e0e40a07a38bfc37ad314a0982,-0x53710bda1453eef3a1223a9ad548,0x70bb8272e3931034157f2175ad8,-0x7636fde6e5c301d82afb60a420,0x5c1e217fa05bb9f760a6f5ba6,-0x3221f59f020b83f8b27feea0,0x115914a2025c49e8c7f4a44,-0x345206a688fb98eeb5508,0x4037d264de4451905ea,-0xfd0f19d78c393d88]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 23 43 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 43 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 54 indices rho q1 m1 1 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 54 indices rho q1 m1 1 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x526090bc59177c56aceeadcea400,-0xae0cdd5d0302f406bee61ef3c1900,0xb2ca630c94281433fd4c6b4ceaa180,-0x76f7c521c0f0f8b6698b9b052e61240,0x39a457b2d29be31dac9ece0cd6430860,-0x15ac89c2821324208ea0f6162b5194ca0,0x6950f6c4bc6fc24489a6f1ecd8381d1a0,-0x1a8bc790116a5ca3b15dbbd380f0c81d90,0x5a9e52d0a93c5933e9821143ecb0ddfc38,-0x109b67770aa18d953ca6cce8c55cc1f0b88,0x2a4dc225e5834c0e8cb1a9e3082e6699c08,-0x5e7374838b0d00e180fba18b917fe0910e8,0xba22f20599caad624502fbc7410b2274b70,-0x1459b871704c6766950360ce564fbb821990,0x1fbdc8665edf3f638319dfa0e2b95a8a0690,-0x2c4d041eecc553af9cfc61f57601500d287c,0x377b2670dc27b9fb23842668784f88940e06,-0x3e7ae727ad819d8929fed32963c1a20d82ea,0x3f5df07ca72c4cbb747fe2f2f79c1ba3722a,-0x39ef1b8a33df01b8be714f2eb55140d62522,0x2fc54612310e7ff690fc092e287d5cdf7dfc,-0x23868c6d8bfa7562cee2c43602ddc954d9c4,0x17d0dc09ad1967da8f73b0c2ad3a47bf17c4,-0xe60f178d5f448326b8906c5d8a065d309f8,0x7ce84bd8ee89e1c1736b68ca81e3a57263a,-0x3cdda6c4fb9b2c4fedc1bfd607160cfe0b6,0x1a8d29ec4c478436a8c8ab298f1383b4276,-0xa55fec71785d4e17901318605a73f17606,0x39399105a653f13408dbcfc54662c78df8,-0x1184cd5907ad5f621ea9bf27ec511d93c8,0x4b7c975452121266d0c004deda1bdadc8,-0x11c2c945157fb8f43a87368c483556c1c,0x39eec9d26b5b6fda1ea2c05b687541fa,-0xa216c94785201324563a1a57c6b15d6,0x1803a678bbf937b49363a42b4ad0b16,-0x2f7f03db1f4cda18889abdb14573ce,0x4ce18a37e8f99c65c5e2527b868bc,-0x635a121e4e9b52eb72421fe5e904,0x63338a47dcccbf2943a29deb704,-0x493175729d153fadfe4eaee820,0x257333d035277d55507d7824e,-0xc128ea76820e4b47b292542,0x2181fc61ab78c8ce292e02,-0x253be8e8719d0596a9a2,0x82022614798e11ec0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 23 44 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 44 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 54 indices rho q2 m2 2 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 54 indices rho q2 m2 2 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x9a750f61270c0922843f85e373800,0x142c9661552603098eddf4e0bebe800,-0x147e439b6f8a4cdcaf9736015fc84480,0xd7b480126e01c9d4ab3de10672018e00,-0x674d71a4ae9bef84445db3b67d5c6e220,0x266226e5cb4ebb8ff50072dfd768cdcee0,-0xb8414a3fef791759e12ab091511ff80ae0,0x2dde90a0372e5d8b848297062da6ec030c0,-0x9a9a17d5568db7a91f78f7887e1bb7dfce8,0x1bf759d9ebd810b4c07e153fc055b91b5958,-0x464b86961cf11cd73c408ff0c0e95192c498,0x9ad071362c9bb6b7208ef7a98955de68ea88,-0x12cd7e3f2e1261f0efaeb19867771d2b2d3d0,0x206bbf4b5d594eeacd92e63ffddd9bffb1eb0,-0x31d320ada594206b47fe7cf96ffa66747afb0,0x447d0fcb008f04fafe6a749ec9efae15237b8,-0x547057b40183951f6e71b585cfd66d0532162,0x5d9136f066d481aab13433a7d584aeafdfb6e,-0x5d53c9619055f192ec63041061587f1fdda1e,0x53deb96c70bdc1e20df94247931fba6da520a,-0x43efebaf370cbe77ccca6bd17b376ddf9ca54,0x3199d2ab4a1d16bbe28c4540521d73b786f4c,-0x209f72656fa0f3abe555a284fb68829ceb44c,0x134f27e5d3bcb8a0ee2e90fa79fdf22f8e7bc,-0xa450bd2d3f37a1a090122357f38c10f518de,0x4e5df088de14b8425b57efde78a5fca5e552,-0x216d7bdebd8ecd5ed33fe65a6c7f1f300282,0xcb5fc60fd689d78f04adffad6bdbfdc74c6,-0x44a9b7a41c4bfba22bb5b4538dff9318a68,0x147bbc66621d1271971b8a8c204b8bc80d8,-0x55e255b87a13073a79f36c75115a8a1a58,0x13a1c32b371c60a1f7a3bce04ef00dba60,-0x3e19c69fac6f7ac2637687b4c9070819e,0xa827d3a7b950699063757e54133a6d92,-0x180ddc145f61250c1378381762c64122,0x2dcf2d9fba8ebcf0d96a895d1cf5056,-0x472b45c3ae6d54c5e9b3d22b267b14,0x57ef2e446dc5238d24f40119f848c,-0x538f0a15fbf7213161ab0946010c,0x3a5663cb7f595a4338351ca8d2c,-0x1c0a89ff613cea4e0ab701f77a,0x869d4edee5ab81ce07988e16,-0x15787d09cd85c284ed64ee6,0x15958252dade306105892,-0x42c463dc04c3c09200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 23 45 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 45 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 54 indices rho q3 m3 3 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 54 indices rho q3 m3 3 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x1219b7cd629369120b7f71b0a789000,-0x256c6f0248786a9e50065629b9218200,0x259a24d45dcbb7e0d88840c5292fbd080,-0x1876525a74c9229bf1dc7d3804810a3480,0xb9510d40391da434fa134a2487881ab120,-0x440f2066fac406e6bd41a52ad33ddc1e9e0,0x142d6ea280040ee95687e6ab288d5efb5060,-0x4f6533cdc1e4b0d01a632a2497d990c03360,0x10847d568c4d6c43049dca24361ea3070bf28,-0x2f32dd210972377a7c8bffcef37e879552398,0x751788ddd74d33d954c82b2978c408da101f8,-0xfe6ea7eb3716da697391d9b594df67aa3ff88,0x1e7a579291c95fa00cacf799faf6bee1aaebd0,-0x33cfcf6c899918c278c9cfeb26148571d1bbb0,0x4e78bd97343496f960a7b9ace98cba0b174170,-0x6a42440d81b7d25c49ac4d8984f9e481333040,0x80feab0571de35ddd648f52aa1a84aa36764b2,-0x8cad9c6f84f352b8a82c6a85d61dce7a40f53e,0x8a069fa5a47a5efe9e3ae7eb20d06cdc31e456,-0x79f232683cc0ffbbdc472804d3eb3bd30d358a,0x610e3e7e0510bd70d5dcd3c768e4fed53201d4,-0x4594363dae409f4ec8dabbff158d304a36950c,0x2ce77b39ebf6957cb932bc0edd48af90f7d6bc,-0x1a0f801ff227ee17df2e4f283bc38f650ff214,0xd94534a1557a4c6212ecad14a5b7f2d114c6e,-0x656ea4cd11d9a4d385dec5e17bfc148b1ae22,0x2a4f9248fa39bbfaaa8b7701ed6583cec8fca,-0xfb77ffbdf030aef8bf80bfb89b40682cf076,0x52d75ad31265d15bb1f873bf9391cb90bae8,-0x1815108306c09d4801120b094f5e49d32ed8,0x62414189251063bf59cee5c80130b8a7838,-0x15d1c29291aeadd1707e100d669b1bdbb18,0x42edf2d04129234d56e46ad22d0bd3050e,-0xaf5f830ef41328a2082bef82943d3c402,0x18379e0b9ddd25803f329fb612e8ef0ea,-0x2c65a998a055a7a78b10faba8fb631f6,0x422e16453fcd649535e26c1f5f23814,-0x4e261ee78c913e2e7a3dd8a3b65ecc,0x46a29d1efa274a236cbddaa98987c,-0x2ea240f580f3d0c650508ab803f4,0x150abc13200950929a9d42278ea,-0x5defe955d870fdfbe7cbd6ac6,0xdc3829f13e5daf7d9048f3e,-0xc8253e47a29cc4a9a1f42,0x2246dc759d823b1b000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 23 46 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 46 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 54 indices rho q4 m4 4 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 54 indices rho q4 m4 4 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x21f038a118d46501d58ef52b3a20e000,0x45705249a3dcdad54b910f86127028600,-0x45074c9a9a1d4462f2ac25e8d56f38c280,0x2c6b4fa6b479bc884da57c3371975c1ed80,-0x14cc50069c7a038f82fb06cc78980c010fa0,0x78d363b41906a031958a2c3e52da7ad44360,-0x2367c52120d12f247fc7088a28cdbb42f4860,0x89a8bd93f4db9017cb33708542f128d906d20,-0x1c4a4bb92e013cf37cb9f732e97210b809ddc8,0x4fd491d1c7901f1bd8b53eb71c702750580cf8,-0xc382d516cd0f7db131c1f60471e6c44c038878,0x1a3404312b1641093ca3449108eb692033f37c8,-0x318b293018de1401d04423591e4e1e3bc5bb490,0x530e0ca352f3be07c18068b35ae6ffb64256af0,-0x7bfef934a382b96429f77173b2875d81d64a170,0xa56fb3f353388ff7ae11ac9f498bf4e716851b0,-0xc5cade7b3bfd7e8a1bb80d87b69319a17d3da7a,0xd456036eb5fd3bb20c4908de1f3082685d6e276,-0xccf8446eac94aea0f4945bca1e1a46268f51c76,0xb2117c8b1f9b8fcf2c843bf34daee8519c6645a,-0x8b45fa8d0b52a27fa37fd339fb2721065f2c804,0x620e403ba99520157e0cafb69f61a6450a590dc,-0x3e1adeb76a988d43ac57d5d1f174e51aa95fd3c,0x23588a04bea2df73be9a39c96c02aae1ebb3c44,-0x120beb3d3d51eaae1eaf23f8038812b1ffd9186,0x83f71b7c8d591734e8eaa48f2750871c6dda0a,-0x35d6372fc0585ed2270c504f966bb1ab5b1c2a,0x138993a4f4c22e3bbb187daf87ddae2ee35746,-0x647c8604bc74d6ea1d77144f59edf26658fc8,0x1c778db641987f46874442f5a1a594ad4e5f8,-0x71041959b38560a08f6c9955459f14157938,0x18617deff775b8816ec1edf91ac266e3fc68,-0x4883d62db85636cdfea8a44c84c28e1b006,0xb7d7b5b1ba3b021ebad2b1fae60314020a,-0x18809fdf85397f72a5111ace28df5578ca,0x2b3b1cfad505fa3731b5342568fabf7e6,-0x3dcf493b19fae5b88574fa8ca4ffb8c4,0x45b9fdbc774f72100e78cb2b3c2101c,-0x3bea28732699bcbda9b41d1ca3c2fc,0x2561bd61a98e3de453d931d7b1f44,-0xfd2608012898f073f0324155172,0x41a1350e188f80f567bf73f93e,-0x8d38ed4cbae550fad31a605e,0x73f77a05212559ec389072,-0x1197448df7e24a788000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 23 47 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 47 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 54 indices rho q5 m5 5 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 54 indices rho q5 m5 5 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x3fa26a2e0e8e3d63706c0bb10cfda4000,-0x80dfae2dc9f52c9c82b1606c98d5b51600,0x7ec80ec86cd2347b6ca28abadcf103c4080,-0x50b764fa7417e15d7e3b5f081ae3552fa980,0x25620579cb92d73c252495cfb5ff5367d5920,-0xd6c2f2178efb1fd9ae5205e63dcdab993d5e0,0x3e3720977449e274ae169df09e75bae9331e60,-0xef1480ae5cc81a9499627814be02985bcb4fa0,0x308bdbd5fa147315bf3f90816ef597eee655428,-0x874fc3c0c4044331e4f8315999c122b047af598,0x14738f02578ca15092a3019a2a51fb0a71c07978,-0x2b4a0fd945c9ad6fabf3bce12bb0af590a1de248,0x50c337e894dbfd225ea4eb09e8fb4b9048bb5d10,-0x858a99bf1c193175dcb13a9d2b77af4cee795470,0xc490e77a1ce4b52a2eb30e0a333f419d34c890b0,-0x10275a01de4c842196634ebe956f995b53c148f90,0x13063d8a2c0dd88310680a93b7b9dca0b55efb772,-0x141ba47bdaa1747f52683489c2812c85a3d0a043e,0x1319c62e51539f2c79cbf0057216377b03edcaf36,-0x1051dac5fc44c00d32a026134b9eb0d5852ce2afa,0xc8bb876c604a40e64fed6dd5b7ba42b8630b2fe4,-0x8ad0f55c8c6cc27848446aba6e17f606b407ed7c,0x564c6fe68dd928f303b38042c91012cb5eff654c,-0x302bf35b4590bb0260bd457371f957a8664e5554,0x181a38357c168af7369c40c7b11af524c39cfcde,-0xac8fa0b050c124d1cf97dc7cea9642482f69cf2,0x44db45c4e7b8bb334aa628e12fd1fff07796f5a,-0x1869fa9317a1441d790009f395ffb0be7eaac76,0x7a88b72138f80e9d8bde8d892ec428a3def8c8,-0x21d417c94d689614618a3856c7c193825df1f8,0x82aeadd2cc98fd10a6c70ca0a2a018be96c18,-0x1b62c090893c91ed8fa7bfc763dc5ab9d97e8,0x4ef8a1d39538c00afad69c47e070d56f7cae,-0xc1afcd1860975d67c24aa6a0977cfeb88a2,0x18e90a8af5c3cb349353568b766aa60f8ea,-0x2a49735b562bfa8f694395cad6269018e6,0x39f89c6e52c66c4a952493d4155de4de4,-0x3e72811cf231868a0d02d430f4ef5b7c,0x32fc9d193d772d0377b9bbd4e8f6fcc,-0x1e0b40a8124f18cb511a3b1bd16d54,0xbeb49e2c58e31f440eaccc2f0e1a,-0x2de6e670cb4772d0c3a41416556,0x5a9700d1a783cc4719f403e4e,-0x432cdb2bbf92517710c4a22,0x9064df83e4a3b72c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 23 48 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 48 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 54 indices rho q6 m6 6 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 54 indices rho q6 m6 6 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0xaa0e21ade5832af82bc00000,-0xee7082e8c2bea939f6ac0000,-0x9ea0f9555646fd7532200000,-0x42a271b616be135b4e54d000,-0x13d72ed2b5aa1429f8869c00,-0x474bb133c49d8c5f331b700,-0xc8c3b4dd2156316ca4a740,-0x1c6548d6327f08c131ec80,-0x348a94331d3eb7f7d1f10,-0x5072525113d8b144c9e0,-0x66c0212d623f2cd096c,-0x6e0894c822220c5f38,-0x630a1259c54f84a77,-0x4aef3a13e3756987,-0x2f8d4f8c304fbc9,-0x192fd2f011d8e4,-0xb0c45b790776,-0x3f76725409a,-0x12553f351e,-0x427d632c,-0xb5eff3,-0x15d37,-0x17d]
def m7 : List ℤ := raw_ints% [0x0,-0x775087165b4ab31a72ca95ebf85b938000,0xef3d1aa295d784d0431f18ced0eae28ae00,-0xe8f723bfbd46babb0bc63a14dc273905de80,0x92c7797cb9a1cdd8a44d2501056f45382b780,-0x4341c31aaab645d6c36dd95496a9f2680e76a0,0x17e2e847c177a34e4759f9d7b189f34fa74bc60,-0x6d7b760fc1f2ba29e92e2abd9d980c00d28d560,0x19fe914e7ef3b3ee240a2ab20d0f4b191601afa0,-0x537685a200bd45e8aad2d10ec9f4251f0380b588,0xe5d5f59c1f3ca7bd18b0aa800e91ee67c9cb3938,-0x224f17cd3a173ed4fd9722271ea2a5f77bf5e3cb8,0x47b30ae293ad577072ecd77e713f4d79185507208,-0x8404c3e767615b19d12ce62b5ce4c25130b766850,0xd75bb5a4ff2a4cc92fbb98d30eafa67f7c8cbc530,-0x1389a9aba7dfbbb444fd168225c52bdb15ff140130,0x1952924b6efbbc6ccb8f982e367e8ea485992b42d0,-0x1d61f21a45db2dd156bf6974597553925e67376eaa,0x1e9529b9b4fb479535d3cc0fc2d9513770d082f946,-0x1c97a4cc50f75500bfb81ab55eef1d5ff1dd485c46,0x1807c0904c9e0478ce6e7b2e140f65c7dfffb8d7aa,-0x1228feb87bbbdf83ed742d5e5e5f9dca1ed51f0ab4,0xc5667e7efa549331f723eb2db8891f4ac3da35bac,-0x7878bc2c94c130c870fd979fcde497a2e1fb12dec,0x41f6c9162638ca85170962b5e2e73671090c95af4,-0x2058f63fa16dd9a2e6a1bd8440b9b365d6ee2d046,0xe2c5033e6aef9ad72a151820cbd9892723328eca,-0x5883556bd755878d0c5a54b0f58fad563a86b80a,0x1eaa145c49a15237333c294459ab13e14f64a306,-0x96313aa489831a00b06ef85eb3c0781227703e8,0x2868868cb85eecbf2e365d05f28e0da831c7ed8,-0x97e431711f5af0ce84d6e21f8656207399b458,0x1eeb19b701263200e7968b8ded95952b3f61e8,-0x566f0d91ffc3ec7a70620a33f7509f68d3db6,0xcd0d54c5ad81e4ba0e2169031b2f2fe62e5a,-0x197177a7454a35eb7bef9c57e07d2479aa5a,0x298baa84894970f8d6b5b592b7767f6a9b6,-0x36976d7db1374d80e96bcdcca7aa2f4834,0x3821794ea03695fdb584eeea77a5da02c,-0x2b860f22d102f8e909677476d5cc8f6c,0x1834c5705c0439d721c9c9b8429da74,-0x8fea87657338d406e7cd89256d812,0x2022a34badab49ccdd3b8f2da61e,-0x3a1fcaf779e587d0cc8b821dde,0x26e6d4ad3b8feb45159de852,-0x4a0dd189735e8b5200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 23 50 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 50 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 54 indices rho q7 m7 7 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 54 indices rho q7 m7 7 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x17d,0x1]
def r8 : List ℤ := raw_ints% [0xfd17081fce9436f3591cc00000,0x1623364b2bbf03eb04bf23c0000,0xeb27229118a4e88e31a2f40000,0x628d2242aa829bd16e62199000,0x1d449e3de24761ef1b92015c00,0x68de33cce043d8a70f876bf00,0x126568919de536ec8bddb3340,0x2979f9b1ec05b9d61aa85340,0x4c6bea02af5e673fc054e50,0x74717b3f78b59694be0850,0x93e4cc3b79fb35949125c,0x9d56c35b04c39dcd79bc,0x8c8574031acd33c8a63,0x6955684a1def45fcfc,0x42165bc3af548fdd6,0x228357ffee9e3a18,0xede46c5e89c33a,0x53670f27fb408,0x17519dcb5f3c,0x50a484f86c,0xccc8583b,0x15a182c,0x12d2a]
def m8 : List ℤ := raw_ints% [0x0,0xdfb6fd49eb2c0fd1973bd91a71abb490000,-0x1bc392847ec338424135bddc992fbddf75600,0x1ac48d9d58ab0cd879c096091c1d0de0771480,-0x10b19b8ede5d5d022412d98f132be2da1f25980,0x791e3e3875c7460df239b2235d041bfd98e9620,-0x2a8ea1e70278b179e323c35a267fd155789c30e0,0xc0ee02a273e10bb06aeca20bc10f9ad1571b8560,-0x2d4b5c45e24dffb365b16ec664e833dc4f7eef9a0,0x8fc27e171f4e3497046606a4ccaaa30d266b98f68,-0x1873426a1700f0a690a79a9fc5ba89000474577458,0x39b0498add820d5d508763899e0012e0ce22104e38,-0x770db9a7182f70a6bd2fc865e70db9a81a92adcc88,0xd864d93e7ea82bbe86edd57ae17b3fea7636f2fed0,-0x15c52cf1903e72701c70600244823cf1cee35c41cb0,0x1f2b4d623640df811c7c727abad584461c87a842470,-0x27d4158206cc43ac904e8317fb4dcda6cbaf046d410,0x2d8a92dee94d930912fa865dca1ae7b51a32e535a02,-0x2eaff63392dde89750cb9d0a87bb4a9a86183144a2e,0x2af7d736b93e342147193a4689748a36bfb2d435ba6,-0x23873fdd61fe6ef555c6e59bad4a49ddf03bcd8074a,0x1a660e48a790d3dc173ebb8c11c807f2c0257164514,-0x119f1cfce5b70846aab583a8d0190ebbac845db7ccc,0xa8f0f8fcbf706daeda87c42c6c0a3e9e9fd70e61fc,-0x5ac01a4a132a1a47f6f2a34db8e91a8058a7496764,0x2b9f05a7025a473485840a037fd91f3e64c36a2f7e,-0x12b77135334b78bc42f38ca2c25cfe0dfb9507d252,0x7258c0ea1907b24b579b82dfc1801f324bbcbbbda,-0x26b574caa0d26505687286647a0ecf33af8705a36,0xb906d00fe2ec221778dbb7d2f03caf37d3ecbae8,-0x308350712f7cdf14f24b3a22d8a4e241cfb9b2d8,0xb16f393ae620f6d2f47f52637958da702e14c38,-0x2314b5a499e4e1a227440a747f33ec702e7d788,0x5f1064af462b0a143ca8c37c42afe1778bd87e,-0xda1ccfe5581dcf5d64a6e854d7b56141c9d52,0x1a1aef56f4875705203b4bf9ad57e6f87505a,-0x28fda85b9e12658f86b81a4cd3da5db194b6,0x339c12e4c6d10853f4e939fe9d6dfeaf0d4,-0x32a0d7086214cbc5637553ad64c5d8770c,0x25432a93be3b50449a562e2bfdd232d3c,-0x138c4703211f1745d63fe61839d52024,0x6cc8303bd935cf02be28ec573fc8da,-0x1684597c8d5277a3bcf347f8f4796,0x254cda7b5c2e36292f04d34702e,-0x1685a36f0b4ab31fe1e44f702,0x25f79bc731579c8b000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 23 52 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 52 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 54 indices rho q8 m8 8 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 54 indices rho q8 m8 8 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x12d2a,-0x17d,0x1]
def r9 : List ℤ := raw_ints% [-0xc80e83eafd62e10ad827ed800000,-0x117845159075b8c09f73197780000,-0xb93b182d8bb5af69b0dde7040000,-0x4d78c7372f849308f9e2ef862000,-0x16f4b6392b804500d6aaa9680800,-0x520b67e1128709c604fc851aa00,-0xe5a12886de7592b6687332f180,-0x204168b8b2a552b3cea76819c0,-0x3b37ef614b052efb2ed649560,-0x59dcdeeaaaad254ef51c4a70,-0x7199aad3d66ba06e7eac468,-0x7833d794016d30708e5174,-0x6aadab04e13a418f06dca,-0x4f5f3b48d1e98c75ab53,-0x315b9d334480c505dee,-0x197ff728141a32b9dc,-0xad708a45d220a844,-0x3bca7123c2b27e2,-0x105aea4a772a44,-0x36eacb744738,-0x85c955edf2,-0xd49a8c13,-0xa80086]
def m9 : List ℤ := raw_ints% [0x0,-0x1a3771aea98f29da8fb9037119521f28e0000,0x339091c04adc389e9434713887402849c17e00,-0x313ba36352ea6b71ab808d2f76004b069ff9280,0x1e664bd242e1b1d2e8f51bc3542e3207220d8b80,-0xda50bfc1d2c4890ca97a2dd33b7cb25fa0ea0ba0,0x4be8e1ff6f63d38497a6edcc408c7f0eec3354f60,-0x154737f1eb8644425e91c7cc4f9dd1ab494cf3a860,0x4f0d03bbae643d1f6aeaf6f000a76d5c2a1f5a82a0,-0xf81204b398f7b7a65b5a8a78914ea3eca3031b9ac8,0x29b3bcd0b6ecf9281538aacacfbe59418416fb2d9f8,-0x61385f20cfbf1d744196d1bd83e24f9495986accc78,0xc62c7acca3e047a7d815a4563585c2c93edd7dc9a48,-0x163a6569c5486757abd197e4ab8b0e707de27e9f1a10,0x2350420a256dfd1def9f9edd246915ca637fcbc7ed70,-0x31e114e38b30740aae97bbbc353fbd18104f5fd372f0,0x3ed9bc53e6e523c07cb0bcccad0096575f0985504a90,-0x46d5214256adc344c52163129ca85363c1de0e0389ba,0x4788d0cd9d5cabfacd51347402ada92d9b8c544109b6,-0x40d206ae8faef6a71bb446176f7b53856bed76a72e76,0x34bd35d376d7f77bbbec5668971ad5fbc305635c2b7a,-0x2688fb1ba176c1c6a3eae9faf5c57b07b26004ccafe4,0x19471308afad1884e781de8435e2e8fd18c61e977efc,-0xedf88f7ea66720a1f636c7bc7356c98dd0f542e3e1c,0x7d6c9eb950cd0ecc25e236c2c993613b317771087c4,-0x3b19d26046a0fa96f8541e7a92525193a3d5abc4966,0x18d5d3a608798708500ea25b8ad89fb8820f2f324aa,-0x9470e838d088ab6359a15ecd79f6dd8f2a91fbf2ca,0x311acf6bb4c7d5950a4094607a7983a935c01c04c6,-0xe5125fc85e3d3d5a90579dfc4ca81ab47c67ae208,0x3a884dfdc0ba3df349f27c484dc71fed9a27d73b8,-0xd04be846de7f6c7fab81a4b3e1291c60b28b7378,0x27ff6b0a09635980305b8a741ce0cba94c645a48,-0x690dcc171e25a150c44d71d54fa60f990e66706,0xe912b344577909352c67a0a16ad577a916768a,-0x1ae6e8b49300fc714a4b399fa8957a062f5c0a,0x289c18d597b570533cdd48ca4673a26241306,-0x30f955a72373d1ec47c61381bd2869f4e724,0x2dd11c1792c03451cacdb1af6c074fc4bbc,-0x1ffdb1156f46007ee0f63da92473fd885c,0xfd2136c6a02697a02f3c9720ea2a4584,-0x5259048d0c46c48783189cea3088c52,0xfca2a06444ac85fe7cede8f3487de,-0x17f0976edce5434c74e1ebe4ce7e,0xd090de9623bca873dee2da232,-0x1375a8743010f9388000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 23 54 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 54 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 54 indices rho q9 m9 9 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 54 indices rho q9 m9 9 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xa80086,0x12d2a,-0x17d,0x1]
def r10 : List ℤ := raw_ints% [0x6f999f1d843f1a558533e6e6800000,0x9bb24433b955921ccb9d0f30880000,0x67027256ea19e5f2079926a5480000,0x2b01826858e656ebffd8959960e000,0xcb7c855b28a63bf88ac6b86ef8800,0x2d5a8638051078b8e3992ba9dc200,0x7ea021497d63df46099cd7dde180,0x11bce5810e65069a90efe0eed980,0x2076f636899994de392769628a0,0x3117b12af76c52c73b8a7f2be0,0x3dd07d9faf2cb6f1f812eb718,0x411c408e96ec3b8b4f053148,0x397b9268f001db6d1c23bd6,0x2a824aa60608164589e7d0,0x1a3ee163fb948fed15973,0xd71b5cd853e86646fd0,0x5a8142cbf375fe6ae8,0x1eced936ba7644dc0,0x84b64b4116c4972,0x1b49c776cad9a8,0x40b3516c347a,0x630c9bc850,0x4a2e58ab]
def m10 : List ℤ := raw_ints% [0x0,0x3127f5277dec6e79cd7ae6740f79fa6ca40000,-0x5fca7586cd409f9798e4be44c224554a909c600,0x5a980a2db4885e060bb0202323a05188c7371880,-0x3765688466f186f945059245fed83ef5a8b8b5580,0x189df915ad80195f29639d1b0146c160ad88404f20,-0x878e2845b9cd9c20c6e3849f0147028ca3c9a49fe0,0x2599788ac1c3c571ece0b4aa36e73fb7b980fb82860,-0x8a2efae2cc0a85c74fefc808ec88182519b97d082a0,0x1acd7043196c5341eaebe0a77bbf8e61ae4644dffda8,-0x47453b63ee8bc09c196b97cc90af32917bf097c72c18,0xa4350930b6bcbf8bc11e8804e779fe1098b1ac6265f8,-0x14aae85e3582a97d1e0595891e0e2ba19708ddfcf7ec8,0x24a12290e3966307e4ae78ae1309c1bf30264a57f7490,-0x397216149838473de6822dbce170aba9569805d5780f0,0x5010721e952027dbd853a0736ddd4ffc4d2a121340c30,-0x63808b2a7d93e222590ad3f9d6b34cc17a0903176f350,0x6e8c2fb1e487f01b47d4f358fa7d3ffff479ea1f90852,-0x6e00649d152efccf1caabf7a8723176fba4aee0e2075e,0x62282144e820888f98fb97b2a501d0435081488753bd6,-0x4e98d1ee8cea2d3764909b89c8ace82b3370c81db679a,0x387b82453b3255e0a2a4b8b7df7d36e7f728782eaad44,-0x246a226fbae86b792555377948f8686f7b5c9a03fbd1c,0x150adfbfb5d25815ba7e082478f7b664be502076881ac,-0xae212a1b7d8d90bc2e7c4192794633a7fdb430edda34,0x5071b38c2e901de761911e894826aa68c0a6eb32b6de,-0x211c11eed0a96d4e04628b694c0b550237cc582de1f2,0xc19fb44a0b5c2fd1d352d28d1086475d397d0d3491a,-0x3e981231e6556180c56e5ae975360fef89cafc62ff6,0x11cfb2c4de44ef380eaa17cb32095b2c3a74db3c508,-0x46f6ee37780a8a14bb71d2f78d5429d232f5c29bb8,0xf5b4e3c1e249eb5e69e20c79fb8896d78d9fb4458,-0x2dd20a1de671d04f5a2919e672bb751390b529368,0x74a1ce5c9297e1a7d9edea08bc812df0d355098e,-0xfa2c922d0e5f053d398bac4da85a851cad3adc2,0x1bd74c9bb8d2f15b090a1f44922703621ec9d0a,-0x2864526a7d0be9d2f93a217de03080600a5e86,0x2ea404c7bb0ed30674130a152ae248d7d18c4,-0x29981e761629ebe26d00d75751c952c2599c,0x1b89c10a73d920b66768141a33bf779efac,-0xcd4844955e4aca05a4d18edee60d59c34,0x3e6c2f1a8a4876373633801d1b686ada,-0xb1473424585edf9eb1e145d0022396,0xf5dbd3e687f876cec5242c1ef54e,-0x78adf920109c3310a6162435e2,0x9f8820a118391d6c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 23 56 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 56 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 54 indices rho q10 m10 10 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 54 indices rho q10 m10 10 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r11 : List ℤ := raw_ints% [-0x3146df2cc49b6e0adaa05f4f39400000,-0x44a81705a2c1507e73b9cd83fe640000,-0x2d5b8dac8fc8921c574c3b344ad80000,-0x12e802b113f97a4c74a34f2134def000,-0x594c99022db9d3ea4eb9e29b6295400,-0x13dd4cff177361d142d3d3be42db500,-0x375742984bf3b365a074b7fe5bf5c0,-0x7bbcaf58049afeb8af8fadcc71800,-0xe1dc398123fa23b204a77f326630,-0x15482ccfda5d764ae8385b80e300,-0x1ab4a8a112d50c9f186dc203cc4,-0x1c055ecf0dc69808cb091ee100,-0x18a11361f4367e82c3fe331b5,-0x121efe93f07567f2513af60f,-0xb1f503107b2354119951fb,-0x5a8743624aff4349212f4,-0x25c70dc37854e4418682,-0xcbba89d3becc525f0a,-0x3630fbc61e4c4189a,-0xaf9e4727d4165d4,-0x19875def153ce9,-0x261b97f0911f,-0x1b94819397]
def m11 : List ℤ := raw_ints% [0x0,-0x5c2aebaa0c1b4f24614670199d04b58bb380000,0xb1fd420d9675e414182144d77041f1984dae6e00,-0xa6c723f04ea160a87c151c26aeeba33feb726c680,0x6503c9be1fed0e07af3406ce7fe9506540f675e780,-0x2c73ee1c7ab4590af30946033fd128ce6760e3be0a0,0xf256bb30cc26abd5a7d10ec4ac7a99340d478a10260,-0x42877595ad9ec60f4159715534553bc9591d6de8eb60,0xf1ed2ae9f2e3f2ba6b44839e28f7985319cadec67fa0,-0x2e6a765618a4a5afd137a75abba2eded57c277b3fc808,0x7a0bd7b1ea4f904a1df011407db8193b4363a26a12ab8,-0x115f5ce84a82b2b7de27092d35263eac8d6c870e89d838,0x2291e9f08afe937a7ef7cef29f05186691bb09edf7ec88,-0x3c84d660d19f7600fd7605d68da1b969fb060c610addd0,0x5db62856a04d7faa708af2bf0628fdc2097b70696863b0,-0x80e71317af120896245e5eebefc725f9f427a66e5246b0,0x9e07f340e8f30d29199e602750e121be0c49a2ee9bb2d0,-0xad1d35267a8216378802336867ac95299a6179b15cb2ca,0xa9c19f4a2e84974ca93f7cfa168e1efefb2f6c41dd1a26,-0x953136178071e8b047a9945c356476747baf4941a1d7a6,0x7596c8e02d593910e0233ef122793e535fa44afe1633ca,-0x531fb09cea476ef48a2a3a40b2b35b3819e62133263f94,0x34ad9d816b707f3d52d47f83cf5d82c5fbb9ac29ebdfcc,-0x1de641ef04e5f0dd351addc43c17589cd1db13cf2834cc,0xf2d2673e463eb2ee4862170441144d8aa76b5e6b16094,-0x6dfe29ed31178eb26a727b1115deee474c704a5dc1c06,0x2c5862e038df7875a626736f71e2c1cc2874dbc19df0a,-0xfdbf08eb82a8074fa86f2f0b9887b2a2cf4307f5600a,0x502ade5353073cff1f5b1f046f75ef2e13497f9c3b86,-0x16439c423ec88d9a9b41dccf1756d7c95925da9c7b28,0x567250d31679ec46a683fa36b51696628b5ef9bed98,-0x12333dbdf5e97fe1f870276e7f1827a310ca7242d98,0x34bbfe16060d3cee9ee5031be541aa3d0cf74d2b28,-0x82123cd3c1bc8c848c7dd6b30dfbf28d5d7b5f156,0x10db28649875b88c27c80b4064a9e3cb6d0c2a7ba,-0x1cee7ab61c434ac4c34da0576baaebae75fef9ba,0x28543fcacf3813b775e4e9448314cfbd2bbd6d6,-0x2c929d3aa0615bd743abeb2a259e809e6cc694,0x25e00bb549a80b8424164114395ed6f714ecc,-0x17c3b67b64c649e01e7066833370b3c565cc,0xa6cc2418a9ab73d5fa83e1c56fd5284994,-0x2f60d3062daa19c55bbf248ac7fac7812,0x7c79575b3a302a9a89564d89cab041e,-0x9dd0a472fe019b76bc1fc59e2f59e,0x45ce869687ab1d93942e5e41e12,-0x51b7830dc639369200000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 23 58 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 58 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 54 indices rho q11 m11 11 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 54 indices rho q11 m11 11 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r12 : List ℤ := raw_ints% [0x125223cbf921d2bc796fa3e5410e400000,0x197ee8ab378ce9a6194bf677320a340000,0x10d2578fb170bc010bf618c084f27c0000,0x7006e148afd4772f4052c0e9e6c9eb000,0x2104c5f78c1fa2116ff49315a4a1b1400,0x7550af0244c0b621a4b380177f3e9d00,0x146346064dd3df62f60f8eb7043ab1c0,0x2d7d059837924116478a8c3cd6409c0,0x52d5ba7d8dc832b51b1bd415ec6a70,0x7c8dd449f66e81b367c9658a68bf0,0x9bd5bc80799eb86f1f16cb07c334,0xa2f71ced0ef4c6a84ced3668db4,0x8eb2df64f7608619dcfc2b33b1,0x688a2254f6dc0d07644d15b84,0x3fd8d3e3e40804bd5f80db28,0x204b2a2810c1dc4ab065148,0xd62cca81a2d5492230a26,0x479deb7bf872d34570b8,0x12de86e9ecdb8f33438,0x3c71b63f67d21f844,0x8a931fc337a7fc1,0xcb1dc01c199d4,0x8f8e9405fa4]
def m12 : List ℤ := raw_ints% [0x0,0xacd079ded6b33464366412300668d465f0900000,-0x14acbd829fd491aace7614f3cc22bb10636ffc7600,0x1332a2e5a9ba5374c1a05b422ed70a2a0fc10b27c80,-0xb852be80bc66ea2bf890297a27e4643c7084eea6180,0x5057c98d895c49df9a44072ee161c23c4b7f557ae020,-0x1b1b83c63e96b0c899f77a01d1a59f533be8c7e37b6e0,0x75df938303c8f8f02463265fc845ad033037436fc1360,-0x1a834e88142f4b145be18329925eb3e83659db04f16fa0,0x5085c0dc38cc8093d61a4290d53399adfd44a477f621e8,-0xd1680e50af19e9778979f23252d3536bf9263f7eabcdd8,0x1d788dda1ff3e0b5e2360e16d0078520c061277c96ab7b8,-0x39f60e8032848c45913c6ade025f4a8e388dd03e90b7308,0x643f07492d04e2eac0196f3b39a2942c788d586ab44b450,-0x994bc01a7aad82fbf9834eeb834162169ca240e9260cb30,0xd025935a819b03001fd466942ff5e652e56a4ea627eadf0,-0xfbc73e6d36f8fcfa6dc498d356f26d361eb12044af7c390,0x10ffe8bb0ec32e80fd65fbc2b8a313e5331a751085fb6622,-0x106e3b8e927af61ec6fcd6cc20d3104de5af1557c7812d0e,0xe3989ba0e49caf1ed54444af35fb8827c465990982d8086,-0xb099763e64f8509eb77d1c4eb5ce9bca0e8a0333151866a,0x7ad188d2cd352abbc0cda48032e3f878051fc4affa309f4,-0x4c850c76fc14b8fca432abafeba0adde8cd45031047c4ec,0x2aaa3e9f68a7bb0df84e62d62b09440798dc30d0b8c59dc,-0x1541758b94a9d4f136f2b9cfccc3ac66d3a2e8301d15784,0x9711269590e99ac52c5dba965e323b192e9841c025d73e,-0x3ba9edfcce6a578187d81d0205a551bd0286ef34965492,0x14e1227122037905ffa7f8e6cf37a13cf8a9606291b45a,-0x67270386d2c3411544738fa863e64a38fddb5d4a59ab6,0x1bf5c25dff3109267a0565c42df282fa7a004314b2228,-0x69cbe18b55e495fa553fb709e47bd1c3cf27a2c1b998,0x15ab6b33da858e57040ae73064a07530c04499a5ff78,-0x3cf75636a06d888e3c54585feb2ba91c8c8ef83f548,0x91b27894ff64857ab04bfc4cc66ee80b3d16d3fc1e,-0x123f8dc73bca4980f2ba1acaac3781d86743478cb2,0x1e2f50c84c9efc44e985a154a2fbd679ae4ceba3a,-0x286a4ddde03b5ffbf802c4cc0e0229e56bff88d6,0x2abd0229bc132e6b7149699fc3f3ac1d9052f34,-0x22969ed4dde4c477c4e86bc4ff6823e46a99ac,0x148e821491228ebf37b4531d3a02a3891ac9c,-0x87c4fa3fc6712800b785aeb162d95c5dac4,0x24004a7470fb225f170d79da0e4b2574da,-0x5771bd6a2fdf9f21e2b4f004c8585396,0x654d053a9e424d76dc224f95c2556e,-0x285e1b4fc47eb0303425c2a2e6c2,0x29d87d04374cee3b000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 23 60 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 60 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 54 indices rho q12 m12 12 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 54 indices rho q12 m12 12 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r13 : List ℤ := raw_ints% [-0x5f5c9afaf5a51544041b4d64f3847000000,-0x8490832a7f49043787479ed3d6acbf00000,-0x575c55bf0969c4a211ee87e0d7bf24c0000,-0x2450b4ae46aa87db4149ea2ce8eb5094000,-0xab0391b4155c5cccbeae3c3521bd814000,-0x25eab0d229673852ba892d76b1b4a72800,-0x694017bb889f472da509d1a46444d4800,-0xea62fe8dffffe3867135eb51e6845040,-0x1a9edbae95f606c2e12ed676a14acc80,-0x27ef4e4112a8c6ec34ee26d67240d10,-0x31d5af3f9b075a884bf39a7b0d4340,-0x33f6b7b5d242a93ecdc61514e02ec,-0x2d5a574ba58e7530bc24d0ff0188,-0x211a2f811d7726236efb825896b,-0x1421c92b69c2148495a2514da0,-0xa2230b0a458b0d97524c9dcc,-0x42d4f942af33e3b2fa46e50,-0x1633ba6538ef1fa7848cf2,-0x5ce03be82cbd4103c640,-0x126c7caf3f148ed4450,-0x29c4bccb6f3401b68,-0x3c61defc6d21f4b,-0x29f0a2921a920]
def m13 : List ℤ := raw_ints% [0x0,-0x14406e481d290023be5fba21a0c048e3f230e00000,0x266ecfea0a8a8ed414b35c43be48101bb52d0655e00,-0x235f8bc8819dd8da0eb9a0349cf3802ef99deb5c1a80,0x1508edb76a2da2ea15fc73250aa19416fba907959c380,-0x91561f9af692022c779a7864c924e7fb3a0f12d7d7da0,0x3091551b5d188fa6fa282de30304d2281f7d55a546ad60,-0xd11d5394f66c4cb9fb48964822f81abc0b6994fa400660,0x2e8f3cb802807b4bace695d6b9cab0dd4715b64905c4ca0,-0x8bee76d5506083210f0c3ebd5f4efb69b6a581260db3748,0x167fe0dc4d5655e68aa16ca765b14ed030066067177f4978,-0x3219fd32be28b6cd4d9d0c7534cafcd86f8730d92ff651f8,0x61681a4deda27476c6ebfe0c8165f0efade1d7533d9ad8c8,-0xa679204f163c40808569fa84e3aee9cd6a990af4a20fa390,0xfb732455045d7470f6265bdedb6b4b673a65daaedff947f0,-0x151167424711f986c57c284c8d4116d27af9bdaf382a21c70,0x19261f5cbb2c7673a2945d1b46f754018c767db849ad13310,-0x1acc16474c45189127386313b854b816b76d29ab35e115a5a,0x198861ee066e68e590f9883b587305d348bf2aa5ea3714016,-0x15c757f5e73f065289bd47269eb262d689ee03061f345b656,0x10a3972cd088fcee2fce6a6fc239d9444ada9104c3606209a,-0xb62e2fab0e06fb423bc853fe7963dd7358aac683a08981c4,0x6f9a4798988a875d5a44ee6b018bcfc60e597f19ae041a1c,-0x3d22ae28c9c331ae605ef97e5e506538e4d7a9993c4905fc,0x1de5e9bdfcd76b18e13ebccdd644f37ef848586dddd24ce4,-0xd063d7c028915e870a9fb7343bad8369aea048d236e90a6,0x50a1f0706e2bcb8ed224f23169f81c1db2577cb4f8fff6a,-0x1b9d0562937d3c028fcdedf412f830004805abef462a24a,0x855545512fb429835c563a6ce45f6feeb9cf72ef276346,-0x23461232e843bd5d3e422c742006783af7c34762cc6348,0x8211439b93786f8573829e32963d51dabc1c8e3bce078,-0x19eaa9e5050873fb779cf279b62bc505f69a2a6106eb8,0x46cb515992bf8285c91bd0472e20b8e5b565df53db08,-0xa3e63a9de41bad10875ff9af9d32ce07f7322bdde26,0x13d62126eb25e183b6811c8b47c9742cc8eb924da6a,-0x1f9d34495d53d2608379cb5acefe628c2fa01b26ea,0x28a55d437c699ce6823396501136c885f8458a126,-0x291c424aa5660d1e7b1b85dab03e3c6df3cf5284,0x1fac7dca1ba56c1626b8b8b8c46d7ac5074e15c,-0x11d25b2431ee56a407e802ff3b3a808c67dfbc,0x6eb285b6f78599e4667864a8bfe86b00db24,-0x1b628697ded27efa993c585a759372726d2,0x3d756f6ffce693b5bf7805c61ddeced5e,-0x4105da6c002e9005b0956c3e7741cbe,0x17563444917c157b9e1711cc33bf2,-0x156c1d50214fa0188000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 23 62 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 62 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 54 indices rho q13 m13 13 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 54 indices rho q13 m13 13 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r14 : List ℤ := raw_ints% [0x1bdc1ca26bced8becc268864297a738000000,0x26b0c9424e32d435af2e51068740a1a800000,0x19785311a65ffc8629adf72a7657298100000,0xa934a7bd8d4edf5bbe22e4dc72e2a59e0000,0x31bcc2074c518c11b463384c1c1754c64000,0xb03200c4da45dee31dd0f2b06e01184a000,0x1e8563e243f71064ba7f47898b761970000,0x43da98f282aa17e73bf97831abd390c800,0x7b132063fdf5e1db6d1ffa90233b121c0,0xb83ffb78074adb92699bd3109fe76f80,0xe5665cb8759828cd4c15898396cfc70,0xee972cbc9e113ca01d94845ae14dc0,0xcfa49cb1d819ca8f6026353ce6af4,0x9711ab5124b9e599e7bfd5d27b58,0x5b8b172a9799f7317ba0e12ebb5,0x2de390b29a78634b7fbdb81600,0x12d36aa5f7390029bc58aa6f4,0x638517a1dc6cc3927e81270,0x19dab3402f993d50a692ce,0x517222bd24e4d4f51600,0xb700213b2dc8f19d10,0x105b45d38364f40f8,0xb35e686fa39455]
def m14 : List ℤ := raw_ints% [0x0,0x25f8cec736ace04304f37cff0d6888ab661ba400000,-0x477592a51bb287a392b0190545ebb3ac7a277363a600,0x4134a4bb816edd0b14eaccd2d4ee5543487327fa70080,-0x266ec11b3116471d0db06345655a163f08aa4991cb8d80,0x10721dbf9493a826d8d343a98e4626508a6f9f00a8ef920,-0x571c4d574b023f5d1d1b93ba8dae52290277ad3db4485e0,0x1737515a6daa6961200200ae3caa401d7110fd545c473660,-0x51e2a4145492a1c410e0d2c3eeafccca32db5e95440d14a0,0xf395af8f0f2ed3462c9a492fefa2b18a11de4718334ed828,-0x26c0ad08a84611e6f795fc9174e631b882f956b51f3cdcd98,0x555a716372a44d977f27cd4f85f451b9bd85562be68becf78,-0xa412cd1dcc373fb84a4c017451977eb56316440c642a4c148,0x11524785b95e86a933e5ebf74b21d8795719b93cb6c3438610,-0x19d8f11e54c6fbc17e4cbe4ab126d2dd9cd8c93f2f21cd3370,0x22378f64438d311591c4bb629a1e4ce17f66828e212e5a11b0,-0x2850999b178331a6aa266f50ec4d266c3a49bf07161da24dd0,0x2a60c379142266ff3e59795f5d4f505f6874e61eb9cb012672,-0x27cfe9830e8f0c0f1123bed37c4828c8a42df9bd9029a9fc3e,0x21767b58ecdae7a0964ee7549b0f83a58a2dca06765298a8b6,-0x192d34de7b2d449c42e35165d79bda54578aadcc0b3f32a9ba,0x10f46d3542d693885267a4d704e55bfaaaa7d228170f6bcd24,-0xa36b9e60c341c62ab5f81e4b3ea5975dea01acf85979a423c,0x57f667938eb8def9bc2461075f1b24cc18960c5a2e021cc8c,-0x2a3b62c9f1cecfc724daa49d332d4528174d368f27c516a54,0x120b4662965e4bc51eeb97d4d893b39083ba7f10c3c3b299e,-0x6d72f879dabb09eb68feb56309956dd47f2eadacb46de532,0x24ae6ec9d878cee314852c554d6bce7b6ba481e1e8bdd29a,-0xad1d9766325f7e551c59694c2495cb36082ce9f142c7676,0x2cb3344c439d60c0ccc6c4b09b6d5bb673776b0b08c4648,-0xa09ea1c79ebfe9662e97c7e69b4a5116dad4cebf517878,0x1f21efd6348c802b990c55f0b38113d850bfe4397a7198,-0x528f8e13141eaac2da265eaa524127c71b9ff88fc9c28,0xb924f7b309d5bf79411345fd8f0620ca431c9b54952e,-0x15a6133f4ba2bacfebddf8f09ae5bdda432ef1e33122,0x213c1e5f7a3878fbadc0b216af66634a83c41e810ea,-0x2904b6bbf9dfa57c7140bf8c97f6d84aa7ce6e89a6,0x27aa67b4f5fca6b4d7547a2ceb2114cbedc4db624,-0x1d14b66675a57dc503ac17ec28d96be5a037f53c,0xf7bb809dc735af7671e3ed38b89fcf6ff9760c,-0x5a6525a36dffa8e0a6702c21f1b1cbfb1b4d4,0x14d9c87b462354bbae859de7fb6b7884f9da,-0x2b3657571386ca39e84b3f15f84f211096,0x29bc0579f38c8574bef49e089967a78e,-0xd7cb29f4c347333d09b18ee8fe9a2,0xaf6be96c144e44ac0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 23 64 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 64 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 54 indices rho q14 m14 14 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 54 indices rho q14 m14 14 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r15 : List ℤ := raw_ints% [-0x7726981cdbcdc4ecfde5b54660d8f186c00000,-0xa552d8545b390264e1729f9c9dbeb71f1c0000,-0x6cba0194a6395390d5efceef0c3f3a0a200000,-0x2d18a3260592932d427a4f4e93f757e2591000,-0xd3d9230dad7baa4ef695041b77e140543cc00,-0x2ed86ba7a614a0d3cbb575a6c0d3bad878300,-0x81a7c12dc87b55a9baba7c5c2db36f97e840,-0x11fcf475e75c777da0ff38b36136b6368680,-0x20929c6235eaaa22c65a43d3cdc8e1fc850,-0x30ac6854313078e4db533a58c316a132a0,-0x3c7a3bf246589abc29b9a85d5b3eca3dc,-0x3ec22e468286867112685be0b5e81378,-0x367b1e23013a20ef766d067a01bfa43,-0x27869e3a0a755ac582d7a480886627,-0x17e03d33e91ff612e68410cbc17dd,-0xbed08e57de437e0e7a8b036b8e4,-0x4df6ecf77fea6391c06029b1ae,-0x19a3d4a9aa7372001358dad1a,-0x6a01e53e9169cc5df057d36,-0x14bdeb7efa5d1800c527ec,-0x2e43d15f6283c5d48a6f,-0x4196a70c02f0e28c57,-0x2c7bcb0e5becf421]
def m15 : List ℤ := raw_ints% [0x0,-0x473283b58684247da9488a5e392400415f73d3800000,0x84e4f62b764f72c66e8fd0b5392c3fcdd8ba75f79ce00,-0x783f9e7120c868edee3834312f2af8c23985fd907b0e80,0x4643b5eb183ded7f5a4e8991134fedd2d0034d71207ff80,-0x1dccdf9c7e774e5dd2a03531f3c887787225087f2a3542a0,0x9c67bbb24c7933d1fe0abc7e89b54b6bbb315f0e5dff7060,-0x294aa0c22c70b830669b71e9ae575332f15648a24a4165960,0x90398a6f87055cd49ae53932f80bcc35681410b8ac344c1a0,-0x1a8b9ed325771a42898fdf6dc2f9a79d3377a7f2f5a6bb6088,0x42df1afea1972113d413b1314ca881789449b69cb211d19e38,-0x91b59cbe01c0b4adf32f38d1ad0f30b57516e8279ef469b1b8,0x114fe86d55fb6a09bdf1b25317c322a8f95ed9ec8324f92af08,-0x1ce8470038c097e4aabcfa63b396128550422975ba9e2dd3b50,0x2a9faa629dcf03e31e4d67d96b8edd92d9d3a28308093f18a30,-0x37bae0c8f2db621f1a693ec93705d965c075717211b7f700430,0x40d229583f8e3cf24e67708baafa1f843afb373e95cf7b95950,-0x433b2ba93b14d9c2db03e861528d734af8d53bcc0c2b325966a,0x3e4908f25c352db6fdcb1324929644dea7d4bb891b31c945d86,-0x3398823837dd4cb962dcdad84452ba3d2c97e99028421fc4086,0x263bf180ef061f7b7bfc9ce3e4117a64cfabd3b5f234651c5ea,-0x1957afcee47dc1a2f94a3f3051b46911a3d8082776171192a74,0xf03cd6c7eef50d2f62c55a4d62ee5378e1845d624ba18729ec,-0x7f12eaf7e20e80e2e5c7c6f03eeae8940a543bc8f22a18f5ac,0x3be6d21eed8022855e1d1265d7fb38808f98afbddbdf8136b4,-0x191ab59502d61940d1b24ff48bd0b228a2dac68d005fc23946,0x9534680050f03231c3ac5e5d56e5556d5851933004e045bca,-0x30f099fc2387c3a8fc58cc11afe67633bf331be3626421b8a,0xe1c14065a4833428142696e29d1f5e4604601c7eb3a1a406,-0x38e4e7b53ef4c1284edb59aac56347e64fb3b53dd0aa6268,0xc736d4d1ce96b0d1522045eb394cd8bb76d25c952b56458,-0x258f23dc8bc7edefc451be3b0947f8360846b7c97b9ded8,0x60b00ae2e8794daef838a0f7f36fba096d6036aa694be8,-0xd1fe03608742307d243074d6c01be8cb9ec5717006776,0x17b7ca86c5a161d0234880fd7664ac616371c40ae9c9a,-0x2310aa698911718bdf6f2c08b6e845f174d4f3939d9a,0x298801f9bbd1af2a474827e04ab9b65c39d821625f6,-0x26625031dcfc432ed535c537ac6697d29109189ef4,0x1ac4542471a91e95e90b07891ed127e9902bc1f6c,-0xd7a7d67628d3f38582db96fe1188fe001e25a2c,0x49ec310085721045a62f01659a7f9660ae0834,-0xfe3b28361d4a0491c147eb4da7a3dfa77e92,0x1e64a8885745705d869b368c0132789d59e,-0x1ac8e806353c93e1f8f270e114a53f9de,0x7cad7bdf67b746e554cefa1dbedbd2,-0x59c17868fd53c25200000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 23 66 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 66 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 54 indices rho q15 m15 15 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 54 indices rho q15 m15 15 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r16 : List ℤ := raw_ints% [0x1d8ca976d08afb151dd274e113b2a8b0a3c00000,0x28f77d176206f5b793f36e3f0b04c133356c0000,0x1aeb0d2cadf3c90b9aa52dae9ab836aad7040000,0xb276a70e6ba67095e827b0df07f0253a50ed000,0x3457b894f76721f3f1a3fd102aa207d43b10c00,0xb8fa33d013eb3a846c14c5c02dff1d6a90cb00,0x1ff531a1e0cf2d8c1afdd1d196bf6e321b0c40,0x46d7bf38a4dbc4dba74d642bdd2a893419440,0x8016a73751694cf1d08fdf49c9eb4d45ba90,0xbf1631c836901c0207d416ff09a42727690,0xecfeefe9854529dcd3b89e3b54104afccc,0xf570b39b79996512c3e7f3f120ef4fd6c,0xd497ca861d1af14ec0c9855684ee3a5f,0x99da87a0d70e0028966ca31ad18874c,0x5cade658f603040f2a2e440d155d5a,0x2e26263ccceb191350f544eb805f8,0x12ca31bf9fde07e41fc54916e4d2,0x6279e92997041dfaba9a4c82e8,0x1954b7e689122c994450133b4,0x4ee2fc4be762e57f6cabedc,0xaee335584d72eb32c7027,0xf62a3947cfcc8a6adbc,0xa58aa937ffa9a2ffe]
def m16 : List ℤ := raw_ints% [0x0,0x857eb6f45c37c46b9d680370ab23807a92f92c9000000,-0xf732bb6328243e45d32fdc94573426aae80d80dc6c5600,0xddd90b7be000cf1b6bd36d3f5233de7ea093cb27ad0a480,-0x808a91d0500f518ea84cafd5372a837d69bcecc337ce1980,0x360b425ea43a5a9b7e9202c2e2fa908bbcf1ed34b2e969a20,-0x1191cfe2733e9f9e015591fb3f765d78a3432f59a2a9a20ce0,0x4987f407ed37d94c8f72bca0b9d33a2959f1af47f7d01b1160,-0xfe63ca607d4f0ddf9d3ddc087ee9a6ece6e5648792a26d01a0,0x2e5ca5d5291f6a41dfd086acb64041f589b74ab607cd57fe068,-0x739b1b6fef6f21ab1c1f89da7ef34da5fb6d891633611f42b58,0xf9408de95559be272c0a802792c9d053092436a6e658e340d38,-0x1d4ac8336c210d6dc510028aaffa00836a0370215658d4c59988,0x305c0e4a8c001b6b218e8f9e82ba61f38846c9cc53b2988b59d0,-0x4678c2d3bbdabf21797b4f1588e0e19a769743a7c9337bb2c9b0,0x5b0583daa7f4d1b6294824916c1614310347a7fdc8de47bea770,-0x68884564397395b11a3f129bd98d5c5f8a19957898c6eb8f6610,0x6afe732e60f1df3722705a3a6e24db1f7843bc9286163b61d942,-0x61c3ec00f49ee2b61a64f8b41cc8f49c31796a56ca99f37914ee,0x4fd44cdc50f7c630ca8162378afae4709054079d157d2d498c66,-0x3a45e2dd05739abc74aa74facaf0682c6dce31622cc22df84d8a,0x26057c9c1c9245cb6e92f184f926a4be4919822ce01c516ca2d4,-0x1628784990cac8db9efdb7fae91ccb1cd3aaf948c05de07ce90c,0xb84e8604aa17ca99a0d85f12584c2f4fd9073949795f95585bc,-0x554faa9a51144fb47b0f282a3156a73f2f86f6b94728cf67aa4,0x2312a31293079c9cc1ec17f2e41bc16f116a8efdaefd826e1fe,-0xcc433ca26d8497cdd265f558c49a56c70ecea3cdea4df92fd2,0x41931cb1e0ae9721719ae5c8ab687056154be442e207ed3fda,-0x127ab18351b62f008f39fe8cb3737078bd1e4f61846e4a4b36,0x48ba01b6aedd3dd3d48c97327a1a3cb5dcccd9f3a0d0f5968,-0xf823505f6d0e72ae22d1b2d31f3a7efdbe4d825a57a47058,0x2d80bc46e1cfb471b7533e04288e815265c545c7164982b8,-0x71b22dc66d091a51af38500bd01b79b3851014ce190ac08,0xef1d9dd1eba1f42110832bd55c859ed77e09dfdc89ccbe,-0x1a15186069b7396bb9d4f197edcfd7500433d03f407312,0x2520274c202919d2a7d3f386efd62aba1e8f40175311a,-0x2a2f3e7881e33c387c065bc2a39be12b791a75e24cf6,0x253f8c68b883d59844c863fc7e19cc854073973a994,-0x18b209cc054efd6ab04e75291a3ad444b883b4d04c,0xbc1580e1404fa42b65d2e67069ba823876bf07fc,-0x3c8856e48335ee34880f62655764bb0833bfa64,0xc1e4167ce962186f86947d64e10e7de103dda,-0x15620a5be3aac0841a79f632459a02cd8696,0x11303ea80785d84fc2ca6e0174e06347ae,-0x48035417ccd42b9198aeb51987c1e82,0x2de9802caf62302b000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 23 68 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 68 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 54 indices rho q16 m16 16 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 54 indices rho q16 m16 16 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r17 : List ℤ := raw_ints% [-0x6df737bbc3c50f6e622086047f54c03c3a8800000,-0x9856e00b98ad0937c33ceac63b1a13e93aee80000,-0x64043483ea1631311d0322ba8c146a48866540000,-0x29681a14ae752270c496fb4805a5be37393526000,-0xc21f9a363358cc3712438ae8d4430d437f23f800,-0x2ad4eb9b249cf912bc9c3838cbb8ed2e3e3b8600,-0x76433e8a2163a35ca154cbd65c577ffb801e680,-0x105d56364729e8201d3c7ef8156b336ecd91ac0,-0x1d8c4b00452de3ecd109cb3d4e27f233372da0,-0x2c03d7683da72d7196f1aa9af9a231a737fb0,-0x368019c2ef2c8b568b11dca97a88b893c598,-0x38573242558d404c1d29776c062d15692a4,-0x30b4177f5a24a143b8d15001c5cd324ca6,-0x232b4a441e4e4b670c68e681ed15d1643,-0x15222d676edbf437fccb0e129e29e1f2,-0xa7e99010c1398addefee422fa02c3c,-0x442828ca647f65f1bced4cf5d8c1c,-0x163f8b4428d4196b535e9ea13782,-0x5b351b136cec79498b84c0cefc,-0x11ac59e8d806abe4b7b2878a8,-0x26faaa2178c9c4df08845be,-0x3689cd9b517d63b74da43,-0x246b7994c7a008d3eda]
def m17 : List ℤ := raw_ints% [0x0,-0xfa4d970a2ce89049c723067340e290e5d393338e000000,0x1cbe8f665eff3a5931f03be1b2143edc0a9281e45505be00,-0x1997505403a53e207855e5affa3a8213bc4d279e94be2a280,0xeb4bed068ba2dab3efdb1d495e6094275e2fa6ada1bd71b80,-0x6217441ac4ab2b735afb5529ad364ca137218770f48a12efa0,0x1f9c544a5ede80f5fa224052328eae15ff466008bb25beb8b60,-0x831a2e5f10b4a8ea0e61728a55523d9e5af3d8258e0fe972460,0x1c1571cdef5092b5a3e0f3f9667941db1a377ee6e3bedf3f7ea0,-0x511a45ae448d1f82e421dd91340cece0720a678d127f6a4033c8,0xc8380a82900cd644e1ab509648ddd426ea4ab7cb03e71f3138f8,-0x1ab3a7fd6db46cd0713db327ea8b6253ca2a2322c290ad4d90778,0x31abc8cc58b08f6bf22807654cae4f7ad9d9d6fab3809123bff48,-0x511827e5d995562dac018b5be90f50117ac21ce73dd5628063510,0x74d024a61859ad7045a4c4c7f740a1211c8bb8daab27c9d951a70,-0x9511da5466d74df0fecba31bd39de49408e3c65389e0d6a5b0df0,0xa9105eef6ab0e9ccced85d3c2bc378ce9c0a10fd0baf9840d0d90,-0xaacc9a6e001f108fdd1b74bb2488fbee80c0d2cd8b81c991832fa,0x99f44f6fbe13e511a499c608d2598bce3b2c7703e6ba146206676,-0x7beeb7b7a2369298223b03ec7601153f31d8ee9f4699521252a36,0x59211948c381c94f8aeafabb12acebfaf9b53d02fa0e2fd5fb7ba,-0x3940ee4194edb6b4ae818f2f07f74dc25abc645d54b39819f2da4,0x20d2faf28ea11b590077251935d7e765d123c089655bf542c3b3c,-0x10c5d3ef9f9531d0e673f520ecc09fde026e8f28f172c572c57dc,0x79fcbbd76d7504477c32934e63bb1bb5351447ba7ee1b0702204,-0x31334ec553a7f2c9fa93edfd2c64b55d1da2d8d0233115981de6,0x118cd370d333a47cbaa7f1f14c36bda83463f5f1826f3c610c2a,-0x583bb735b5f224269d1e3800f3543a9bac18089c11cad097bca,0x184de98394b09aa21d337514b4ecd23c9141fbbf64f7a38f5c6,-0x5d5b66f0d5fe628a0575168e30af8f8fc3729288a9c3a4f088,0x1365e70ce1aa9f816024f5ba104dd9a86240cbf44e2e2ac138,-0x375a6d3a39e22a10fa122b9c14e9e23a25e768e1270fdf5f8,0x863b19c17b2f2d3fc941067713901973371898a7f986edc8,-0x11153229b7b14f589112cef340364f7c993fb519ea4f6946,0x1cc97832433e4c5f954b83ce3106572c3756eac1b8b124a,-0x2770abc6a39c4d942417f1f3419906a4e6ae1fe674f1ca,0x2afabe0af46f5264a01e882a227e0c776360a15d3a946,-0x243e44a028e7d125160993c34457b65f2b8627c7afe4,0x16d5eaf657ef6c39f35adddb389b527066d9622a4fc,-0xa453868d57743fe0e9049e8c451a667d8a5d7791c,0x31a111ec29d43efdac647f31967d08bc602f14c4,-0x93fa16349ae8965ec1ee76d3a191fabd8a1f52,0xf0c207c78fb5d6e2d0c202ceba91d4133cde,-0xb0765faa8f47659d9d6ef9157d37bdc4fe,0x2995023d2006cb1e3be3503030bcddb2,-0x177aa321cb9e3f188000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 23 70 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 70 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 54 indices rho q17 m17 17 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 54 indices rho q17 m17 17 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r18 : List ℤ := raw_ints% [0x183161680aa754c1fdaa654c1ebba4acaadc1800000,0x217df57577c2a757d0c0ac9f7c1e0f0fe120df80000,0x15f8e4ce71d0254a273995c4021f50194fcc0580000,0x916cd542002e23694e16acefbe20bb38e768452000,0x2a92ed85bf0ba0a82ba401bd5a46efac9e95167800,0x96273d058324f2a5ba1c39fced12ba4956e83de00,0x19e27fdb2d01f5d70765fa5fb6c21fc6844bc6680,0x393e6d1669f6a4a66f5b8665f051f1be26487e80,0x673b653c629d49378ca425b688991be0d0938e0,0x99914e09415f7efa4f2a30559f510108bf4520,0xbddea4e42cfc8d3e0a0067e3d7fa8d9374b48,0xc3f65282698e7f85c0824c5da208aabb17b8,0xa918baf77dd6dbc86ce23d235bb3227c5b2,0x79dd846befb5bcbb436b14fce7b8e25060,0x491213141611bf300aab4683bc63b0857,0x24329c79a0141abee5959b246ce78f30,0xea73a2f50fdd67553a8ed5f86dd540,0x4c4cb641b958df57fffc8a21fd820,0x137ba2447c79c7e7f3698a086e6a,0x3c2b860e94523f8dd44a6389d8,0x841f8f5d901f0193a8873bc6,0xb7ed537ac3bd33d0620520,0x7a1a8efa746cb5a76fdf]
def m18 : List ℤ := raw_ints% [0x0,0x1d5517b3314340e8a5561ac1819a8cfaeecb400aa4000000,-0x357d4a3c4ea6746ed36a92563ea4f414d9f260bb280268600,0x2f4066d36add808bfca316ef2bd1447389f63d80371c2c6880,-0x1aef91da04358628bfff6729fb2cc427716639036d3f43e0580,0xb22e00b21b83c3994736a382bb6caf1a97119b309be08730320,-0x38ee0db508a015616c34a3c8365eef7445cbfc8d3dc766fd0be0,0xea0775b544cd5d4711b66fb69ba89be3f13fee10d880b6756460,-0x31acc3400f69e21c6d1cfca7d4b455a79b4fb7f9a6e0c6811b6a0,0x8e19fa3c16a7c892886364b199e3be97dc76b9c7b53fea0250aa8,-0x15b611466af965c86d1674ea3c6ba7e435b0cc18378e4a6f399718,0x2ddbb77e35b0592c08abe94a51c2f30b61c7ae5e26cb955712a0f8,-0x5468ea9df1f17a12dd1aaace41ad3c6e4e6b1328ad13fbdf598bc8,0x884e69bd290783f1729c760d94a098454ab0dd23f7ca311bca3f90,-0xc21deefbede983b0fd9982597f3cd0f73feb108ad1646da3acfdf0,0xf4cc1b2e592f7fbe2102d215b9b0d9726aa8276e85ec0ff3c07f30,-0x112380c27173356847b7065f21e49711e6730c0ec86ddfdabac8c50,0x1117ba1d92f7cfb26923a1f1b3e136484a7e58c349c4881e04fa292,-0xf33655d6390da26a97d99b12dc11d35c06ef741731ea0ea0c0731e,0xc10baf311c4fb494ba13a42e85fcd76da4a7eba02faca09888c796,-0x88cce761ba1d927a2bd608e372528bf5e43af062a0c468e0f505da,0x5686c7fc2ea1cc41f70c1ceca91a30a58512d3200429b5ed7e1f04,-0x30ce7efb096d43bbe706678710215f305c818ef61f4a4c7ac9055c,0x18843e161aaab3a467da0acfd477fb044203b97e25621681bed96c,-0xaf1eb4b0f6b5b08d58eb922667c428986cc6ad7306c71e6efa474,0x454c0559cf5016a621c182e7229149982dbb79031f1462dbcc05e,-0x183998431184310703903274b1f933d3dece586f3f14118dbb472,0x7736319bd25a976b178882511b0a73bc1b7b7dcfd73f9697941a,-0x20191fee8d3a914f07cce590c54ebcf2ae094c1ffc116996d0f6,0x7855d31febc66a9fdb0945f797de46edb970d7568c852705388,-0x185cbab74937eda83d9aa470426f2576460dae7874b9861e938,0x439b39a4c96edb92d70c9d1164a1e9b3d444299c7d81f7ead8,-0x9f17ac8bb092903902e059540277392ce846d31b5da425ce8,0x139989b7692b8b0f8b5457526cd97c1cc6ff151d714b446ce,-0x1fe25a3c5f1112c59909832f53393e8937235fb4190b4e82,0x2a092e24af6df2f1f0c54bc00d64fa1485bef16308566ca,-0x2beb20deeb0c98c1f30b8061e00d6b55d73a5c17ead6c6,0x235b220cc13d7d86cb82c61083f9aba9f58d1f0caed84,-0x1529325078fcaf0592d6c689590cb1adab1ee026a6dc,0x8fce83e00bc704d0c8496afeb29bb186f32f6f466c,-0x28bc75c8cee1494d937e006f25b2e0226b7d09774,0x7101d808690d12c991a8d9c897175592fcd28da,-0xa9747ef4303271678cef70c1ab14750934d96,0x7135e5b7a4e57f56368bf9616f75215c5ce,-0x1800e74fa4bc30ca71c519ce01a9a6562,0xc01039e4d8e32cec0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 23 72 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 72 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 54 indices rho q18 m18 18 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 54 indices rho q18 m18 18 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r19 : List ℤ := raw_ints% [-0x511c607680dbc8d1beb0018e00f6c0b753665c400000,-0x703744e566b55e04d23cc9fbff7ef5f246f8b2540000,-0x49914c6d21f18e2f285f5a836ee7e82feea07be80000,-0x1e68c59ab83bd5f9671e72a02f3d0defaee6f1b93000,-0x8e52e6aaf1bdb5bbc0816b6b515e0bca68636a0c400,-0x1f58491c0ba6a949dfc45cfe7bf765afc143290f100,-0x565fa46260e55e8efc2162c574b50bb73cf42e92c0,-0xbed0eddbd3b70c74416978845337791c472cc1d00,-0x157b973a47efa0c9c283005aea338c102bb9d8070,-0x1feb1d71576ac76eac99828ea48d32ab72840840,-0x276923d5841a9d91f72a75ef91f28e2d584bb74,-0x289d96eca2c37247493a7232c239336a833370,-0x22fdadecfa56856b179917db40108a3631671,-0x192c3c23f4f609dcf89cba9630ffefb014bf,-0xf106e8b75ac77b8c3bf8f2b82de765d01f,-0x7724644c2186bc996fe9b35a4bdf58dd4,-0x301d4ecd437b5cf2b36a101739baeb1a,-0xf9dd1d9c67dd72446d93b94b8b8e2a,-0x3f9c7c3c8e990219a300b06aabf12,-0xc3cabc43fc00b6bb24dd4a55d84,-0x1ac49a2095ed8a4c2e6360ca15,-0x2519fd682579a3d1ebf0d80f,-0x18820296c5005e466ff28b]
def m19 : List ℤ := raw_ints% [0x0,-0x36ff8c6ffc5e19b43601722ad301c8567fbd1813f38000000,0x638e66687b2e6d0d8be2901d03cf766d17bfdf442a975d2e00,-0x5747b6eeaca5d1e8d584e28068839669927ac5945db9a07d680,0x315d82fc0b053117539e1d8202bb89f38ca6bd0dea08bf841780,-0x143ea051cf0238e18fae7614ed25f29a3ea2796f5764e3d5dc4a0,0x66a14631a3709127a0c884c9895d18575fbd89915f56b9bb5be60,-0x1a2414803023fa4eae15da809c5220a8e98183742618cd477b2760,0x57fc65c4065b4fdaf2ffb85f73aefb6c4b62354bce01f1bad143a0,-0xf95e3a1342f9072c5d47badbb1e2e13737aad501846a2819100108,0x25bc2468c2f6c1eaec1fb4eafd66c296ff8a96fc2ae88cf45e949b8,-0x4ee9357960d8310d605e34d0b5435627115f9c3571672fc50934338,0x8fbfca456587ed881990d51dc27a9e72016f790254e29affd0dd988,-0xe5a3296691931f3f017c7e7914168282feba523d8b56680b833a0d0,0x143616c1605175d389f711da05875aa41d75c2108a696f2cbd4068b0,-0x1931136d72ea74041acd0d99395af79914b253ad26ad7fd9eb61c9b0,0x1be0972835bebd9d9b7e3d4dcb9a1fb54cdb009373e6982979181fd0,-0x1b735bcdd191e16bd101dfae47251307cee82fede179082992a7740a,0x1816dcf4c1f13b5458a86ce72ce852323c141535cfe28ce541d5f6e6,-0x12db151e6b5aba0e5ec9ef908ab0c9846ae3304b9dcb1b3be9fa7f66,0xd2b0c76d4f338d48f3eed97700a977e341d3836fa16ad0f83d56a0a,-0x833b98ba486328c5b78e40ace1ef9f64853887fb60cd223d38adf54,0x48d6c03704f299b264eaba52eb0cf7aef801117e5db82690d36da0c,-0x23f8bc88f07f8595a3df6fa365eeeb55753ecfe0998970a50c9208c,0xfc5f5af1f102e8c8c81748d31407682c9c534fa8714b6b34b89ad4,-0x61fd31b7cc02c394d4c6292408639f5aecb6ba181dc85c91c5de86,0x2192aee1f56c9d18d55f4be67a39d50c8bc269036aa5685ea7708a,-0xa1b84d79bb02052f9b77397a7eb5ff96d9749683c8f358d112b0a,0x2a904cf246c99dcf35a1fac3bb53741e8f0a35fa0b3fc5a34d086,-0x9bbcf780d90cc0142a8eff9c070da6b7702697709cc4869185a8,0x1eb825c3eded4b623e2a94604a6e7f743fa73cacc00d758ebf18,-0x52e553d4dfd15a35e1a149f8f4bf59bf2b400dfe17aebd5ac18,0xbd4697c0e564eea8f153f7d4570aa75ca0f314b9266e1c28a8,-0x1691c0a03de62d43ba488c809a8f0a0476f822f98555b56796,0x236f7c6a9d7cafdec6e5d3354c165e26579fa9a8a6942977a,-0x2cf19fb073d418587ddcbc431cc4a97e775227b0a1a77f7a,0x2d0152c5cc85ff00b46e842d0c1292cab6edbcd4c130f16,-0x22933bda3dd01036ad10ddeaa75879f3f65dab6a072954,0x13a6122403a5c215c745d7a47006564661fc3e6522e0c,-0x7e0b53e6862f223fd8747e32180e3bf83166aadc08c,0x2178cb1bac58914d7d1c24107b989f0a245abfbcd4,-0x5659b8eb03dda5c2d66c918111b4f998517a9112,0x7749658fdab1138102258aca5e1e34b0495b1e,-0x489ea51491009fdc5cbb57c689d18225fe1e,0xdda2acc218ed973fd8581893fc4752192,-0x622bb19b18ae2e9200000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 23 74 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 74 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 54 indices rho q19 m19 19 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 54 indices rho q19 m19 19 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r20 : List ℤ := raw_ints% [0x1047b00dab3b0edd63879370f0ffe12ae8665b41400000,0x1682877124635b5a2ed0fb30f36c19058456d52b240000,0xebf6f74665c9f68354bdefd95432457779cebc50c0000,0x6178086e6d093b21ee3336897fad64e776ba568c4f000,0x1c7d7174b07a9a49787006526718fe20dc9d7e2d58400,0x644fadec06074f1280914a98afcfe7dc69722d5b9900,0x1142c9cc97452fc423e1e03cdcde1a12141575b05ec0,0x2618ae832e4fd5e6a052ce52c69bce9cb75aefdd6c0,0x448dbde37a8f79e803ff1d49c9c225033ce570e0b0,0x65bd92208125f62ca2d2a643e8b5c7cd3e3c7ef30,0x7d77fe008b2fa92f3ec25b77c62d2367e34f1ae4,0x8121d2dd77217f94191a761d857cc4622ad23a4,0x6f164675a5159042126f8055963a99f41466ad,0x4fca0d08e2cb25df85ba9a0de285b15a06b94,0x2faa1f07ba07da75c1a8fd981b1b644012ec,0x1783f68b81dc53ffc133dfd6ec158da17a8,0x979e802e0b817365f1d8f3915f48d85be,0x3118166e190386a38e8a2cc7df466018,0xc772b8888c3284df40612b1c946270,0x26412c2b01af5069c1b80c14209f4,0x5366e408ac0bc730c3006d2b0ad,0x7329c8bf40b2f5bfa44c8c024,0x4bbf10338cffd1c51282f38]
def m20 : List ℤ := raw_ints% [0x0,0x671f2751f9307031e542b6104ba357a22f828d256890000000,-0xb9554f5852f1827151574619e5286f336ae5d28f5315f8e3600,0xa147e4eea7a9befb0dceba2d184cdc1e2eb894963e52c0e34c80,-0x5a8638a2bcc03edc63a19f0cc66dc6b12844a8fc194e405725180,0x24d4d30257dcee6e2c92dcfd7f3e5672393d3baced21b8487c7420,-0xb931bbc51634e641aa993bfb4856babc3a2c7cb8ed25dc716f42e0,0x2ec5e198bd6e8c0bd9ca3dd14e0b84b5c04f8313c10e2f79c1aef60,-0x9c0dd6a7c6076809c94912a32e9597736f67cae84c3326f48a173a0,0x1b647565262f60a6c75f3dba17df8b1bb647a1e208301be87984e6e8,-0x41b2ab4de745fa24892ae41b93df551a8bc4dba441f4174d9a5100d8,0x880bc68f7d2a9077cbde9edc7fff181d5c1424a20894bd9dc5c97ab8,-0xf550d60e11e7aa56e6752dd51441aa43455e44a9edcfd9e59ac42808,0x183c0a3763c3a0f0b395777528d7d8c628fa4f81c22858a84ba8b4750,-0x21c0a45f6b158906b4b1ef558eed59c654a03c6dadf766495f31e4030,0x2996702cc64b96630582688ecec9eb968ec153a993d60b4e95460a8f0,-0x2d78843284a95da4e40bb843c17c304477a8cc78f6e48863e1a0d7090,0x2c371926aa508bd51cc6093acedb081b8cdd96141410aede4046d1662,-0x264b332d5f29db0cf145c9dfa990e2cdfb8654c1aae78b6e007d462ce,0x1d9049f7bb77b0f5c4b2c3dbf2c3942cf0df659f30370721fe6376646,-0x14596fcb5c31a7fcb0383ba1afe5016059fa8ebdb303296a74b9fe6aa,0xc7bcc4afe963cab1e6b42d33cfd277b11821e4424abd3cbab00395b4,-0x6d196b304895fdd7bdc27ed3f19babe125d171b41aae702d5f88232c,0x34f9e03e628a4eebb80b959033bd0cb9a47622f95b1817c7301fdb9c,-0x16d1874d7a9ce2ddfd05616a460351cc0b4a69e38298593437b2b3c4,0x8b19e000248483ded1d6ab955fe5a1fb7596a6321049c2df14934be,-0x2eb64b9c5765e3740091e9545d6bf9d0aa4058c339f112838c00312,0xdc427d50cd432aa1ee6fcb5be44dab7761c893e79586b9040a175a,-0x38aab198a6c5665ef82b6b7463ed6b3b889aee2fdf312cd6e43fb6,0xca5b7071e8fa1301c8599fbb060a36823bfc30fd7a99e6ba52ca8,-0x26e3195ccb9f1271007060016b661d506ea1439495c12d55f2b18,0x66085d6c7ed470df06720c68cd5117e43eba7f9691cba7e061f8,-0xe2052962b46223f5d08f1b50c71541bd4aff81d2d3ad23b76c8,0x1a14acfa9cf5b5326bec4b0e9ad99fe48bcc97545f41c86775e,-0x278353cbb9d0d8fe7f1f1bd358c29d3a2bce60d09da4bc2f72,0x30330c5cb31a2da9267841fac946ba469eb9782753173cdfa,-0x2e3e8998cd8e38277ee1a90a40a0ede989356c1b0e2c2b16,0x21e407451deb5d3e1c223249d396e23d0671037842aa5f4,-0x12478d2f27ee40f1fa52e839c9cb71d5fd9b1030f4b4ec,0x6ea2c10e0a76dc0d74e6697a50415b76fef56056555c,-0x1b878f889519aacf44dcd1c6a2f042678d76ba94804,0x4203d504f485a79e58a5df4033bd3b1f367eff2da,-0x53faeea2bdac924794b195306374cae1d99ed96,0x2e931c374699e300352fc07cb0abdc03f01ee,-0x7fde0cc397253a5f71d6c8ea3b419f9e42,0x322aa5409997625b000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 23 76 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 76 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 54 indices rho q20 m20 20 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 54 indices rho q20 m20 20 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r21 : List ℤ := raw_ints% [-0x32510f2c3390e847c8312e11b5dfee60f338c51d2000000,-0x458870620defe47c36e730c87a200532ec9397c48600000,-0x2d8764b8f5b18395fd454b3e906cdedad379401abdc0000,-0x12cb5bc37b4a52d0da4a61d732a6b2b048e357f6fb18000,-0x57d617cadba551bd9d29a273bf0fbc71872e8e0b513000,-0x13508bcf2b9e5d5a8bcb81d03dcd111211b7c708a38400,-0x352231d6a23e2b57fdcbea22ac714896721f5335dbd00,-0x752b1175b853b2d1cd0937dc10f7587baaee6ba6dd40,-0xd2a453a969e367859b70776dcb1f35984971794e4c0,-0x1384aca24bdfb3a3b02d97f92f4576ba415538be050,-0x180b206fb783c6f2981f528256daff699392fad070,-0x18b723144c409b2c93c066f6256d0dbc297146cdc,-0x153bc0fab97e42abd2390e23aee3b744a8a2db64,-0xf3a9ed6df3acc04fa192fd4d474ac18e36a89b,-0x91542ee876c7a840b3843edef5e7c609820a4,-0x4792d2428d9460275f08dcedf3c67d21dbac,-0x1cc97e92655d0157c1988d49ad9605c9828,-0x94d2b66a455a61d056485043eab492b12,-0x25b2e683ad1524205874b3239af9bcf8,-0x736369ff2d4487e3ff311e9268d180,-0xfad48cf9ac79b42c33bd64611234,-0x159360e075cec7bd17de55630bb,-0xe235de8befdbb55c44cfda74]
def m21 : List ℤ := raw_ints% [0x0,-0xc15a69b9b33ad25d8ddd155e8dd244501914c8a6240e0000000,0x15914a48e9f3aca65d28ddcbce2120d96db7967aed9a29f1c1e00,-0x12a22f02eb9dfbd85dd94e4d59899a6b134fd1e3c574c4fdbfaa80,0xa618499c07605be001feeaf13fe420a2fa63c9541f26e05f7df380,-0x430f0615ff3989cbb0e43fb8a2eb279052d182e7b2405aca9ed01a0,0x14e7f58f61a1d6239e53a9bbfbe85ff8eeeaa1ca1ef6c3567cd0c960,-0x53c8c6acc5b4144219fdcdb82d70edf07d0aaa641dc5952359772260,0x11525ee5f8018eb0f8022a0da6383b6990214f720a07de58903dd50a0,-0x30376ca1af1f92ba2b70d8ccb87bf04b7c829ed45c450bf2da19b1848,0x729397af6600d15158756adb47cbd0d72c58e5c2fd97de41fb6290078,-0xeafd69c3a8076ace992bb5ccc262db2c911d53a436a9d845a229e54f8,0x1a381a4df542d103b10269e2b5b90bcf44bac41edeee93f0ba7659cdc8,-0x290334ad88ba6fa9487f4a8e553ff456715150eaa43833dca01e110e90,0x38807d571380bef65d621e388c149e6ff7bc709eb623fd034145a564f0,-0x44d4f5359d25ec6696bd836d188c955c7241422a815d73370bbfe14770,0x4a5ef677f7947428c3ca6f5856924b9ce844c43d95845c04c593498010,-0x476cc9490251c412e4fa07077a3e291d2bed6aa2c58f156b1ba5871d9a,0x3d0f5246be603ae9faa07d259736ee822d450046ebba1214361e7faad6,-0x2e80211248958896cd2a262d11d6f80b5b1bbe996a94451570771e0c16,0x1f8d3a65a49a4f3ed3562960193118edc4d784dd86d1d06fe679ed70da,-0x1310dd29c94dec6242d8f63dd1f8338901fde2d9b024f252f3513fb384,0xa3febb86f1c003e1cc75b048a4b34c1e2ff5a069e22ffff035a00725c,-0x4e4e451cd0ed0d7fd31ae988bad2d9f9929fb30ebb2800d42177263bc,0x21227a0e9c4e69869efb99d596aaa12bad4650426403d357f0746ad24,-0xc63812cc03fc5d87a08fdc5ace9fa935d6c6011c90d30bf144a5fb26,0x413eec361aef4589e63cb7872d6d0e51b9a8ac737aefe816eb9788ea,-0x12d29f1b81042b1720da1330ec87083a4e273e03c5bc62c71eb6b14a,0x4bbd02d79bb1bbf7d1cb558d91c204f4860de8168df4580ac696c46,-0x107f46db6c1124a9fd328c0b9868313e0a323943e0a1e516ad959c8,0x316a59dd3722d381c18288048a5c3d73090623285b00c3a1cf65f8,-0x7e0ec46ded528deb602e1dd2cd579c27725ffb064abeb1ae9b938,0x10edf8147fee31141095bb9a1d01fed5a251e6edee577ce848488,-0x1e3dfb39a7841a6b9ab6b4b25d784d7041e281c1d4a2c60c2666,0x2c3389de8af6416c6824b8eb6c14f0d214faae843bbb004c82a,-0x33d7bf3106f24ab63b18b7106dfc707921a9c8133cd999a2aa,0x2fa44499452cddef119ef19c056c1486365759d3473b3db66,-0x214b4a3b04199ca3ef74abe697fd23bc0e1f92f7637d4f44,0x1109563baf9791bb472f79ca490b0257f222635d09ed69c,-0x613e07af04fbec62877c1fd20129e631bda919e32547c,0x16a989381e1b5089219d6d33c25b1fa7a9222f1d7c64,-0x327db085a30895cfacbb1af13d22e871adb81abbd2,0x3b20d08189bd97fe71308d596bf40c9b9d76885e,-0x1ddd86dbe624ae2497b762ee0d8ca72ec9453e,0x49bfd56b093c65211d98a6326e432518772,-0x19a139e92efcd6388000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 23 78 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 78 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 54 indices rho q21 m21 21 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 54 indices rho q21 m21 21 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r22 : List ℤ := raw_ints% [0x9644427db3d48a8bcb1ec70470935a15d5512df553000000,0xcf8c6f31bae82eff948aaec330770ae70880a3146bf00000,0x87d2f6512236593088c001751bb1f87913cb742dae200000,0x3808f7a606a9e8238fe837986f594cb872928fe63bb24000,0x105b6e65f1532ea25de83fa18d85337b864e716ff2253000,0x3982719952216bbcc4c688f84e62212b8713a0b760bbc00,0x9e1678e7f2cd9b9a582e9a9cb0725ea06e5db2a524c500,0x15c540d71d8bf12c93b00a8641e3a51cb4dab716266d00,0x271ab41b57de74767027e1ba0d8073c75b284436ed600,0x39eb950b2484fa19328de9de57aca38bb4a4028aa8c0,0x47468fc16a9ec4f9c3390086dd17a689e07b597f6a0,0x492f9a575ae418d2691faac2f52d40a25c723f0030,0x3ecc984da10d6297e62dd2c5d512a3c36437e4110,0x2cfb34f65955d80f65537eed83ee373b207405e8,0x1aca22fba86d5bcd736dd528ca0f2b6ceeff959,0xd2c421ae6abbd63960c5a3d6d66c839d13560,0x549fbab1ef6b21ae2406e79d75ea061dc7cc,0x1b4a749a5450f8b96f30d0be4a41c1678d0,0x6e608783901aa7f54ddfc1ed44b767346,0x1510d844e68e9b981e61472029b3ca30,0x2dac78e8f59529fa1b68b6df46319c,0x3ead517b4e2b4fd6339498858fc8,0x28efe6dd838590c5039179b749]
def m22 : List ℤ := raw_ints% [0x0,0x16a89863c300e4a6f69fe881149ea40162f06f837839a40000000,-0x282a43327c148090a5dfc85bc80db28338c06a4c1ae2afee2f6600,0x22753b61968ba7ff5d8add339d9f0dfed158114a6d81c2af6b65080,-0x130ec43385271e77740e21fd36b5150a86119042dadd6844c3e5fd80,0x7a2f3cda0b7f91edc5aa12885e6e4e22c097429bdd12223fe6312d20,-0x25cbb3cbdce327f87b7cb86a7d4b6e582e755ee04caa2661ffbcc71e0,0x96400cce1f8952f5ce40da9c260307ca9506e8780768f4b0057727260,-0x1ecd96023dee029902d2c26d150cf996a7c73617aa258cdf26616378a0,0x54ff559ccf28a49b7cc19cd4b36b04b7e51ec421e815cc6a2999678528,-0xc8274b92832ba953aa5fc6ad5fc892ab49fbb915ea1178d6152893d898,0x196a4ce8ff324144f13f57795d33f1efcc9a1505995a59cddde05da0a78,-0x2ced636f8c887391d709958cd533195101e0332def893b3aabdc0c57e48,0x458f12f05e9e3ccdbf21871d04ea3e511c5434742575e77d9f1849e0110,-0x5ecf0e7e3b5be4a31af639479c7e1debcfb89e64fad11f54b74b0a08070,0x723688bed6a6b98c7f5d4b9c9bb729cca7520ff7189ac4fabc6deb8b4b0,-0x79f7c96dfbe398d61002de4e23e790e3a7571cb10a74b2feaa943b602d0,0x73b580e53320aa3271d57c2cade7d63f35dd557c393f882b6a52f35a8b2,-0x61a74b385bc852b6e3d4bed181a6873f8f0575185bd2747dea5ba764ffe,0x495ef07ba8d5d9dee59beee55a7849af813eb5ca3dad74964bf78009476,-0x3114de387827dfaa53fe51e4db7b3d9e96982938d4ead44dbe787c2a3fa,0x1d37d4802fa80bd59093af2e736c8daee5386eb13e63b43d876082ffae4,-0xf7617798ba8baf0df62f696b35538fbe00d61ae2787bec07b49b472e7c,0x742a562b35effb7ff95cabc1a690dcb10e5b7df45a7a8fb4993f19404c,-0x304b054490284592e39712ff36734e268d106d6390f43666ee47ed9494,0x11b870153832f979ba75b09ad48a95310ad11df9aba8168240a98b6f1e,-0x5b7b23e37a5a6015732a10fe1f99e89af980e9adff7695f261fc8ebb2,0x19d5e2fe22264351a8fa6014328ba9d88676e35ec7528ef6f9318119a,-0x659e1db83b731c0b5d378cabbbe8c9e57ea7c25b35258673f8078f76,0x1599dcd73f9a58350dc070bf3bcfcd623af0d47892d815a8cac39cc8,-0x3f07ad7e18ce4fc14e4a256953a155272335d6b99f69ed6436bbdf8,0x9c4f38475628bbd98a4d7433a86857cf48864087916b70621d6018,-0x145c5270c85ac4842d5ea2f3d1afd744c09bc814a59fbe9eda41a8,0x232f42630532c7386c42cc182b7c7cfd89132bf6b173e4051326e,-0x31999187e4336fb63af7c4cf51197ae677587964c96ca7a921e2,0x37eb6c195d77a5815409794357bad940af5858c956a9a45a2aa,-0x31344cb434efbed1b7278c20d99fe7ff7953ac842282e86de6,0x20c710122b2e0545105eef3de4f885c111605bee7377e16e4,-0xfe7b534cb9e4deaf450f57797b26af7f91173774f99167c,0x5594001596521181f5a6e860d011c2b6667d5a65fd78cc,-0x12abb00cfae07810a5a88010e4e805a7ca74983abe814,0x26a1f95f3b8ebe1e9815a3142775ffddef0021353da,-0x29a1e5d72e1c5bb45540725e11ab15a7c560d6e96,0x1325ab601d4c4bc56a83fe5f4b6b3e28ce41c0e,-0x2a863157bf5444e454da679e9a6875a2a922,0xd175120b65f7d62c0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 23 80 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 80 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 54 indices rho q22 m22 22 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 54 indices rho q22 m22 22 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r23 : List ℤ := raw_ints% [-0x1b3191d07509083d2d58cd1a87e0798690597315cab9c00000,-0x258ac2437f45e215d29e6f65eab5a41ab80f268632f80c0000,-0x188e41dccce4c8ce087c67b31dac17062ab5153b4bbf300000,-0xa20008de60c5f0576902777c6ef0014a154d2d5c098bf5000,-0x2f42e227c19b51e56080738da37c2f78a7c91bab598343c00,-0xa60ecbfd92564c30e8ad933991875b4a146d20016fd8ff00,-0x1c8290ec5f1c34113fc017b75216e5983535810485b6b540,-0x3ec591321612796c1c89c4328eab38fc3ebfaf46aa72b80,-0x70a8fdcde378b2bd19eaf9d343f0cfc8e1b97e744bde90,-0xa6b94e22147dccc1ce4656dc647ce9af8676b92437be0,-0xccf95e6e4e5b3c9b0350799304d02810c6966e00978c,-0xd240b8101223358bb10ba926f9207add39db5774de8,-0xb4368f072447214060e73d4fbae4bdee630431e93f,-0x80ed07942c20d7793b202a9d319a11f15c3d280d7,-0x4caf0ee042744a5c9b1c2919864c855abeec27c1,-0x25a71237bc2e0384032705724638615960183c4,-0xf181341f7e11217c201f590c0231ea02ce0c6,-0x4dc005ff923e5b4bb44071b6ca8b01f6b83a,-0x139dcc6c39fde5227cdd47a84487d3a2c2e,-0x3bc6bd54125adcdf3d70fa285ad3ec79c,-0x814db258d13af4a5b7bdd1caab40adb,-0xb0fba916bf0d3201fc047cbb11747,-0x734339cd357b04a1b82bc404fd5]
def m23 : List ℤ := raw_ints% [0x0,-0x2a7c1dbb0da1acb90e6bd3f206a973829982d116816c1380000000,0x4ad015565e797d580310510fd32deca0f6679e92dfa9fe32b5e8e00,-0x3fbe90f032e72ed0016e24c6780b92884e1c5041c4cba87082a71e80,0x23018670fce896d2a6874ee23df7d39046f2256252ef0611ed613af80,-0xdeca234838ab5db9a9bb8fb66711ea7d2f62dbaf7e73a027760d9e6a0,0x4464823a82a0f4918b88afcfb5a6ddc3bd3f4363ea9d041885e6dd6c60,-0x10dbd2c67ebc6fa086be17aee9fc72754a158c70f7b043f6654eae5d560,0x36d8c536bfea9fdb6b5cb0f6fd77b505b0643e339d133dfe17d5c5ae5a0,-0x960df274b6b4947b51e6bbf7f64afc1501770022b12a60f7fc83ece4988,0x15e3880ed1b3f690be0f36722d55c15d206627dfa1b733665e83dbc70d38,-0x2c0f6e368a0390350b97dfdd0d39984de0f7db9e3b67c5c03cf8ead7acb8,0x4d23392dc77f98b3f486d92c4cbf1776e80c2cc425f968a46870725bec08,-0x763adf1687d28ee3534c86ef1e336e3c8f9feee04a29e9f1d69775148e50,0x9f75426b24d5460756971edde3ffc1adc3164f5e4a13a89839f59e377f30,-0xbdfcd7a86cdc7822d29062aaec3249c43c684ff165b1054ccf4570391730,0xc88ef9ba73866dbcbe9a1f915142cbc49f62f168768fff48e4641b681e50,-0xbbfa1895c3814958c37d82f7a944aecf1ec99192ee459374fcd1fba593aa,0x9ca3fcf83a567cde32d61d6cca5eee64639a32d1b4d11351e281a04a7e46,-0x7420a107b2cdab0137f018e47ccd07457b171a91db236633225008d5fc46,0x4c990718bd3c52af5c5896b00097fe5cb4d7c404c9fe4e6d2ae8fda4802a,-0x2ced2be08c6057722b8ef0215d802bddb9cfb4409110f11d493a87363e34,0x17675740897a44822570e5e9550f21adf7c2f75dc94a9dab4f11b64c502c,-0xacf197dfacec0e2052a98370835a7d865c06ca8cd2b4a5c5ca13f40556c,0x46a483b99e30ab18cc46a4563a102496e230dc20cb8fa1bba5c7abcc4f4,-0x1970dffc5c6b48d32f883ee75c5851d63b22f9bc3a0c05a72bb4677f3c6,0x80bf35b9df6c7c72ff39529998a7a6972ae7beb6d3d4682f1a792a554a,-0x23984a126ab71b4cbbb4cc21a28d0be2c5d8734c3172cf7bd4aa8b568a,0x88daa4585587d81f8cf0f4cc42a67d7d89e0575e4f10046d2671cc106,-0x1c63c10b7378837097166395ee6ff405c91b2bd5bc7dc9c770f6864e8,0x50b0e1bf185ddb3ec014b0d8a5b72e92a16d7be595fe9d67ab91fdd8,-0xc28383301587a26bab0e71c1ff2bb1722f05895dd06d2c30e679558,0x1892339caaef368b8485690c899969fbe0cc02bf9ec53c272844968,-0x2911587b5d6fd3b289b1dbe59285a8baf8651d6696f70ac92209b6,0x37d358451b371c425bc6afc462c5e31195c547461c6c9c695a05a,-0x3c7b5fd2abb79457bb0187e5d001110fe291691fe138c299975a,0x32f0b595d1fe95b7062971d2b644ead334d0f8dc419be033236,-0x20559ffcf93d518250230094f01a61293ba14bf4ed3ba205b4,0xedf70bab45a9ba24bb96cac574ba1a6535cd78b967461aac,-0x4b66ceb314d7eac34cbf113bdce276c11a17402e4bdf8ec,0xf64bd33aee1df28c8941f6924177aa42f51446ffcaf74,-0x1d91cf0c03c9abcba3006ee0aba5e7d684acb305c792,0x1d50670f945ab1c894244d468aa25674f62413dc9e,-0xc45ed280aa58cefbc81f8728b17c0aa87beba5e,0x18834e7b6537c8dbe370b63bf6126844def52,-0x6af62ea418487b5200000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 23 82 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 82 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 54 indices rho q23 m23 23 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 54 indices rho q23 m23 23 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r24 : List ℤ := raw_ints% [0x4c91013964f452d38e07ec61faa846107ffe61145fca6c00000,0x69a80ef9fa2494a15fff552b01b4234874ecc64958e975c0000,0x45134bcf5eb251afb36cc2badbf7fecf1d6e47d8ec79c940000,0x1c77948657634a90b42570f3f9c4974263b9c658acc99911000,0x84cdfcbdb42ab41261649060fcc46348c2a9b91913b9647c00,0x1d258b6026bbe1bfc58034f113b3ae8d13aa65f4dbd7a20700,0x5003b60c54a21c9b225f31cfdca523af3ebcd9a2194c2e940,0xb00cb94d30e26f39550b230e9a96f55e845e740bc0ce9140,0x13bbb3a19714ab203e73b7db712673165bdf3c8bc9099cd0,0x1d2deb3309994aa012b2f4e34c3ff7a541b596f5af185d0,0x23d7b581157046aff59cf832c7b92c98150bdf4f48f17c,0x24bb2a060fd5041c3ea4fe872543ef1870257208d345c,0x1f737cbcc287310ec66d6d714f070dfa938f90f5e29b,0x1679bbae0f2d3ab4da39d653cd74903304950ad945c,0xd5a26fb812a690a669d19ab3ae6e7fcda42619dde,0x68c280ab76c7f0ff3862675b0831698697aace58,0x29ef8f227c16f8223bc8a37e980d3c94cc170ea,0xd7ad0471e77108d84b7d0c6e4b83ef3abb048,0x36526ecf8c86ee093258a440ad0067d9986c,0xa538c2a1d8aec3cab50f88934547b2dd8c,0x164a6f7a67647ef8ff51dac5a0aab7353,0x1e70a9e3c872904e952bbdf8aafcd0c,0x13c618948d3dcce6135e38e172f52]
def m24 : List ℤ := raw_ints% [0x0,0x4fa8b7beb98f23dafb0a2d65cc7db894dfd5480a32aaa4900000000,-0x8b5fae50eab25148f795a80270dacbe799c02f7ef564777789b61600,0x75f6d5b18df44bcb9261c0f7b2eed9c29cb68fd38116017ebacee7480,-0x4055c2615b41efb8911b8370f09d7d7cb38f5eff11d535aabd4bdc0980,0x19685e297d1b5b697eeec9026b2a73a8921faac6b12a08ffb445b416e20,-0x7bdea98c9e8e7c28241be00160345375111b2bb7575c3d0d1b1ae8658e0,0x1e4c6402caea5555afa5d860990f6a566275a92d8295daee425d3860ad60,-0x61c7d907ada45f49e56606a12d17bb393d17ba8c991455f3c6bf11fd05a0,0x109493eea4bd38df9abb4f52ccfbd498a904f3becf6053ce84876ed457568,-0x265ca14c1c3342c727bee7e8dfd4030a98ec24d9e6f01009f9cdddcc70e58,0x4c852003dee1c63c1361e11f2503ca712b80776642f1cb7cc4f5362534038,-0x84b3414a8f83ac1f9c283d3c3c58ac604c9151b3602f2115a714e4af81e88,0xc96271791adc4e9fe9e09ba23a6dd431bf54d9c9468f171059818f7b07cd0,-0x10cce861b47ea8376d32ec84fa12f84f14baf63d639e772b495546138b2eb0,0x13ccfea7dbdec40c823d9a5f8dd6d4501c957dd6a221f6c39cf540b404b270,-0x14aa70c551ab2ceddd6f191aa9bebc1a9115ecf0bcc5182ec0b9585daeb310,0x1323a211a4c5b0ffa39a4b0af19872719b2c96b4190ea7f2196f94efb06d82,-0xfbfdce9dfde4592f9c8ab24e429e5afcbc73a557763e07304e631fa4706ae,0xb85cab1c4fac7e0dffebdf09996d96f7e8eb1bccb1c8ed8362f2da5475e26,-0x77ebceb92184d3df57c1c6bf2f3caf09c3c6c37e565ef1807980d63d111ca,0x454ef2e140e0ce9bd6ea415b6d2f6a5a90f3ae57e72df063cf63cb2846294,-0x238c0576536ca3776abc1ffafc299154f66e30a5561846b6ba1a40467f34c,0x102608cd6c0d57ad41c35ff9fe084731bf4ccf1f100e9927ca676942cdb7c,-0x67b4c84e1afc5ff605589f762c106627887c56c5390e368d0e5333b512e4,0x24a88853d308714d04d00168c70918ba8257a695902f2ba538f40f379f7e,-0xb5dcc0ab7b0117c3e4d350c14d2db330bce9e144755b8b58ca9c7543e52,0x3139098bbc58869e3aba4406cae7a09dfdd9f4dbf954da51523a77c0ada,-0xb8fdc172682298973e103f70224767963a4cacf540e6ebabe1e93b7836,0x2572d48d324b84b67ca24559bdfc6d70106255845696fad2e61aea1be8,-0x67ac041ef1cb92e3ed08cb61f68b65ffb07dcd2933ca61e78ad5069d8,0xf2e680b92557f7d2eaaf14a5f137ab9c2b2e52b049d8511258821d38,-0x1dc05cd195534c1876ac77cf182eff05175294a3fb771b01c1634588,0x3015f69472faefda5cbcf42d7942648d4e53838ac10738b2c1aebfe,-0x3f0419179a990b7636c622a1c68978aac42883b5b2ddede42d91d2,0x4196b6cb1e186d41451fbe9efdd7ad848404b6d3d8f15e58a80da,-0x34dbdf7e944f41ef7523532a7bdd85370977dab7a187ad4b6336,0x1ff574ef5ca5233f2f2d7a51f828115214cd8481a71e28f2454,-0xdedbb65302311ca7f2e9063972036c1469af0da9ed08e478c,0x4282002291dcd441af641e801df3a46c0e462514292194bc,-0xcb33c9c7dcd5f0bf348f110fd2d1a1a72c1e775eb0b3a4,0x16a3a8d72280bd1474d74ee8c77398949e611a12543da,-0x14a3ef4a3440ee0679b184e7fc1641b47d81fc49896,0x7dd8a9d49e94db8a17453018aa18ab1359dd342e,-0xe2066cfa7cb329ef80652bdfc6dbb94fc6602,0x369bec3ff5ec84cb000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 23 84 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 84 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 54 indices rho q24 m24 24 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 54 indices rho q24 m24 24 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r25 : List ℤ := raw_ints% [-0xd22a3c1f5aedbb7894c9999125b50c15a652a8b7c1c643800000,-0x121e4aa035f4da472ad768b26fcc20dfed0f22d9f2451f0580000,-0xbd70a2e5762f535e3f5aaaaa2c64d651e241b8965f0f56e40000,-0x4e08b2e8c7d5e33bff328f7aae32ee76212a80ddecd7bcc6a000,-0x16bdb3b03d9df8aa1d3de6a0b5bbc4e650483f10f1e5bc30e800,-0x4fcfb8d9fa2cba1218530a0b1852e222a50c2615ff3be212200,-0xdaf885b22f2fd20ef910ceefe4175e808cbdaf5f3bb6904b80,-0x1e179c22822ae562b4c10461e9b76969b07c5ff44fb72657c0,-0x35ee4809882deb85c4ad3454a1ac99b946ad06073b86951e0,-0x4fb0106fbeeb7e0981ac09a06a53b9179b692b29676d2ef0,-0x61ce63a79ab31f8425f6bd9021f6268756a9171ac1b6bc8,-0x6424ce6839b5f15ae159f67dd90829da8eb4e8215dcd94,-0x55ab008e463fc4963c0848647b9f807ab08e5f23517c2,-0x3d285bc83e5882266081c8010c2431e19eb73faba473,-0x244ad08f58fae39002ededaa717a4b1b3bd5f890fb6,-0x11c67a0d52d5b77367d5c043fe22359a44df8e841c,-0x71b33c11cfe0cdfc1eceba38adbf18e98ae11674,-0x247ede772cb08c40282792489baa1e7b98b6fa2,-0x92d855291bbbb1deeeb32fe9b8a566fa76434,-0x1bddf48c13e346e70438aa9470e69b47bad8,-0x3c0ab87a218f3d956bc1bd749ef69052ca,-0x51d2c9881b6f65ea1e7cb993b12676b3,-0x3507e11cca7ee7629e419202e3f9ee]
def m25 : List ℤ := raw_ints% [0x0,-0x955c58859bec633a96b3151edf6bba1723afe7131efff48e00000000,0x103b1aa46dc60abc3f68e680d3878bdbb01908a3d04c6c2a8759a07e00,-0xda60ffbf003c6b95f7aecf831b3b2f3b5aa4023b456d8714f4d7033280,0x764c90c246a4a11f80ad81cc9f14581308f92dcf7c8831269a909ec4b80,-0x2e64d58c6917fe8e58d4c7b61c00100a10098a1c4c74af1337b0c3d7b3a0,0xe08b8ba3cfee6629a7f3a5a13c40ba179277e16c9a83deedaf6790326760,-0x368280b851066e1c19b692134ab5b4becd15f1fbaa3f1928eee71c4e00060,0xae89ba5a18402c04b1620fd376484870cd59fdd413d71a48e82edaa3b42a0,-0x1d5ab136fa1e81c6d344f6d1e2fca5c287a1f2292f70c810ba729f7d60e4c8,0x4356a9e2ad315044ad345593499315e66388cd91a54fd108bb6c10ac2b9ff8,-0x852062af19c9de8a17192035732a65686498e84b56f3ed3e02f254fe023a78,0xe4b97c01b039359a9510b221d31ad573e415f57699b145627d5038b4bec448,-0x157be129da220fdf91c65326f59db02a53ba571734ce3b8c5e85b3a6ca2b010,0x1c62a4b0a5b99fd4b9463076c815fb7caeabc37e4b47f9184c12d30aa77a770,-0x211936a7647fea14424787194f1f16f88e66f5488563b473c69f5cc64ff48f0,0x22289b84e1975388a5b39da71feff971313d11a1fe2932cceb3c3302f526a90,-0x1f439b47d8fae01d3a16c9b7e628f28d6efd91905292d7c50c8aee195bd5a3a,0x1968c98138b30088b63b555961c73c25535ec5049b69118da7d71764ce24d36,-0x12592283943ff73945ce66d24a7907dfd1b224e811a72521d085fefca465bf6,0xbc56506c38d3432d8640889dc8b9a2d714206b72fa387831c6610077aa6bfa,-0x6b45514eaf8bf72145dac1de5d557e52100ef692c4241f019d5b1b26253364,0x362c2711f38cb46c4fceb949c7ec5c6bccbebf649abc6fa5ce385d607a9f7c,-0x1835913a6a877b63c9bf3080e062c6abd46dcf5c90c14d4affed0589dd499c,0x98c850185e0dfc7b8e589e855c97bb29cfbd68e244051f29b20fede162e44,-0x3502eaad2622700828230afd096a457e88664f94770cb910c23a0d184c866,0x101d2b8dfb5831f6b428b96e625f7a995a3b07a0c2fc41bd576457b2755aa,-0x4450ffb660ed39ca67a740a306ac72aeea88ae5bc638d0923f006baca2ca,0xfaf7ff2101ad85a042559752f5884953504a143f95f6b439683d52086c6,-0x3193557fce5beeebeae09a4008e86c2fd01774e186827522ec9daa75f08,0x85aaa9efb5d6d9e80d01670d542fea176d91abc4e66cd3769b11910eb8,-0x1305b7b64034e31bb03c06c763692005ea4380fe15b75619c3f3937878,0x242427b929726633d55eca422482c3d2ecf1c69a78a62b57f638cff48,-0x3879bfb48682196125b4f55b3a4b185a7f7efa379211596e93b49586,0x475557bcecc7f4abbd8971fbebd7d9c4dcadef955cf45f6f174fc0a,-0x474e9bec1d49fcdf24bdcd98b4088aa890f2aeec9e4d69517ff98a,0x36f879cf45b939e0c44982cc481e01fc6e22151074efcd204d786,-0x1fa536b904eac61d9f66202f25c1176be97f517e1ae1ee8fd0a4,0xd10240dcff663b0bc9583fbc2c8a805dcc84169a090919d63c,-0x3ab8fc1ec97c7c8da7fd3aa78993be2be6056262f700a11dc,0xa7c043c90be114b78c24ab3dd5ba0a80d1e9780494c1204,-0x115670f54df06209f920ac4ddd4be7e7517b2f88e19c52,0xe885e1a4fe978669b5212a600ee6b557a964e15afde,-0x50a22c66c0fde27390458314f13dedccf8d1d7d7e,0x8238b87aa6797e0ffcc1a76d9c0eb01cd83932,-0x1bdfe1a64b6b65788000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 23 86 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 86 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 54 indices rho q25 m25 25 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 54 indices rho q25 m25 25 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r26 : List ℤ := raw_ints% [0x233a28e577ee6774fe9250589537a3c3c502b1b2a3a0866c800000,0x3092779d594bbd52807bf8cdf5b0f24edef0b8b38e058e5c680000,0x1fba50d8cb0bae47fe2f2be45643e240c18a8d74772ec3c9680000,0xd103df12da479b081d20d08939f8d0c8150c6c2b52dd86a456000,0x3ce205359f949707adf1f7f36e3cce1cc9a3b3867097c921a6800,0xd59023817b011d0b887d8a446dfbf5777fcba8ad8630fc063a00,0x2499b6c8b07c0af18dc73bc5ef32835b3f518dfe167a375f9b80,0x506df4bdaaeb7438c8e0f075fa842ab422b0b9d52ef2a621380,0x900d4ea2f49a1650cfc3a8c57d0b1ee318fa02ecf22d931920,0xd4b4067f74ce27647d4850fb1a275dd72e10d351cd2ae7a60,0x104def72bd19341411f52aa6ac0de12a3b0a37dc89cf92678,0x10ae4390f1a004afc96a062114b7befa17df169fa6176f28,0xe41d5439095b86d1ccf60dbf79502f9f40e517c6a7330e,0xa2b256c8449085aef5d0be440347670b84305d6e153f0,0x607326968ce498f6d117ff4e8fe70e709fb827dc18bb,0x2f30018af487b0d68c835b6ce3c9983dda0ff7e1890,0x12d79e22a4a48ecba7e7cc5a1e570cddfc0d06ba98,0x60a47baea5efdb68185ef0722718e84c656fc480,0x1844de7a26d4d570bc2774850e1770d16c67d62,0x49933c697264d40dd6d3c7a8b3c4f81365f08,0x9e415b2933ca76431a88f8dd10c8bb12c92,0xd743a0f3048d1026e486c722893d1f8f0,0x8b3a9be0a3b3b1139a934ab3e032c93]
def m26 : List ℤ := raw_ints% [0x0,0x1180d25fa845b3a0dda8fc799e2e9fceb62e9d143da1fea8a400000000,-0x1e3f7f97e4f0a7924a3c686b874b5aaac8141dc578ba97fccf3a72e4600,0x194689263e78bbe3403310f07043d96832588aa87c8b5f90897fdb5cb880,-0xd9a3f4ae700f25cb3fa6e9d67143ef12650ec3ebceb8c2e95b03b5af7580,0x54c5cb92c5deb715603605817267ed8c2f306eaa02c0ec6051952aa0f7720,-0x1976550e815de33d1e93ed76ff65f82468b6107ffc576d9a631344a96cb7e0,0x622b89e11e89b4d50b9c85d992a1f9390a497676de0bb8a1f5649f7ea86060,-0x137ed2e47f6396c3cc6592b38026f7c630c22677beddd0e545421020ff55aa0,0x340a920455274b8f765642fad85e6fd475dbe8ef8643573c109ce47a437c7a8,-0x7662f727e95f2857c6845cfb9017808ac318e91a9f6082345236e92f5db1218,0xe801fb6f5ce4d75149f1386b6811955db8f3cf3d8b8b4b8c05f91b952a98bf8,-0x18afaf6b5dfc2b20b9fb686d507cc3d72172c006677c9222f3b45324721d18c8,0x24bf0e82cf4c97177f2aa2e8e41b60aab89ebb1a37e920814e1eb61d194b4a90,-0x3010b86c672db70302053503b8809e57826970776dbacf6d6591d42b21d73af0,0x37755cec4942543f43ae084d6ac0868a12b123979ea6e58c6d4ec3d43d5f3230,-0x389ab1015cf79f4b7b4ca09e208195a74af0af390fd0fad08bc90e9882017150,0x333519fca099dae271a9b5dc7a5cbfe06abb5b261c5995827a124f1cc9b418d2,-0x291c287d05c591a7a25b1a54cd5b2d1f262d020a2c8f9382fa9c0a038beeb2de,0x1d4db5d00a1403454b69275599961927f9c9182283f7451c3be2f7ffeefcaf56,-0x128b30ff3fc72813556c9345c9370e4a0f78514b904d79be2c238c19edb8241a,0xa68f10419db5657b2dba7868132dcfa4a7d7127790497b0cd4cb8b7a12300c4,-0x52d4a0dc1a3a38317d371072847e35abf56999588e6b298e173d510ac461d9c,0x246abc9cc85e360eaa26af01376e2878277f24ec5d8f4404400bc2704b0a12c,-0xe1dd8a8a6fb098e3f0e199be8c4c4c4cb187beee234b788d41d78c992edab4,0x4cee28215b045e952ba6347ac77b55aaf92abd1fb47dbd8703f343ddfbf5de,-0x16ed0dc829793274d286f2f7c9ed2aaa9713eee041eed64b7019a386a9caf2,0x5f27eb4b2ba66c798b6c38479be409a6d5630deabe9eb74030c424396cb1a,-0x155b0fb5ab76ab50a2059975dc43d50a3cd1b4053f15ea28a178c034a71f6,0x41dc53e2068f682f804bf649286e5f3e7378b81dcd9603c639ebbe19e208,-0xaceed1ef773711f5f297eb8009b6eba843c75f6df66a26fc794fd6536b8,0x17ea1fce1a44b240f4b0a94b3a9ff004347d0554238fffff7c313e49158,-0x2c0aece92a9c98bba294ecaff23ce722c4b417b3834082ac6c62124a68,0x4286c2900740e878736974a35629cb77c4b835338d17a63bfda8db80e,-0x50f80c15cbac97d5a581f1b28dacfd219b5a915e8acd3152d8504b42,0x4db69068e750ca831d00d72f771bc77755375d3c262e6af1630648a,-0x39498644e43ddf006ef07733a304186df605873f37bf4c3b056f06,0x1f63b4225c2619f3fada926aa172dc12e5f080c8c9e208e6d5244,-0xc44889a5a65af2efd852d04844cfd01f0cee087b0ad6a60241c,0x33e5beccadef6cb6a0ce2cd34bd57c9ba87164fc7fe82a2d2c,-0x8a8fb49dd2ddf5457d1957e9a0171859e916a63c6c3646b4,0xd47c762e3ea45660c4860f72649dd886fcfe32532ffada,-0xa3b5850bb011d931300dc16c137dfc78cfed2853f396,0x33a74422ae1cdcd80702a9c887bb69afd3dfc46a4e,-0x4b018335c7c7be641f78fad44d50a336127b4e2,0xe39a71dfbb8c406c0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 23 88 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 88 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 54 indices rho q26 m26 26 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 54 indices rho q26 m26 26 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r27 : List ℤ := raw_ints% [-0x5c7c9b08d484571fca8317cdd64b3ae51316da72a7557461f400000,-0x7f7a0b330d293925210762f0340e3d1d9919305a03d0e2bc8440000,-0x533c90f6a6da08d07f09db503078c7b34de6cea60a8ffbaebf80000,-0x2241d010e88293db501464532203ffcf4e43c0879f3057f350b7000,-0x9f95d62a3d8b63c75b0a91b73cf05cf0357f6e85b4545441d63400,-0x22f84b734b9f6fe219dd1bf6a65f8fd2df7dbaecdb96e1c3e5ad00,-0x5fd737919da4f517c5790ab7e0921aff37b99b460550c2904cfc0,-0xd27e35c80cc81af666ade171ff513ebca9e28b9db11e12713200,-0x178c668f7c5cb3de42afb29706b7954c93434381a2e1c8fd82b0,-0x22bfa8aa4c2be6ba3642a3234ea09eea9b1369ae322551c2d80,-0x2a9697b3af3be83d87b37cc36bfcfd7e4ef0708bb0fd503024,-0x2b89ea4762c4e6abd4cbaec08fd9902834632a563cfc0cae0,-0x252ee0fbf6ef9b7ad44337dc8d92e6be24a4f83552f538ad,-0x1a7f371909cb8fee5fe2d8c79545dc718dce9f355f4f26f,-0xfb177bd61636cd9b70cb19b216a10e0095333372ce8c3,-0x7ab894e398fe4a7c4e31d2fcb15d5109fabbcf866ab4,-0x30f31567067b600678d156bdfbea1193787ad2ceeb2,-0xfac3e114ebb6ad19092ba2fa71686fc543db71b4a,-0x3ee41e7a3281bbd82e5d3bcdb4312fbf3258908a,-0xbe6517a97e6a1187600ae7e52cb810a81cae34,-0x198e568e40871dbb782a4e3b4d56566876ac1,-0x22b417dd09b5d4176bc2473be7e047671ff,-0x16676b2372e4ad1f9256a762847991dff]
def m27 : List ℤ := raw_ints% [0x0,-0x20d18a735b82b0cd9f9cd96408976ba395976685f38fbd7c33800000000,0x386149f54f28616fb24041b2b407390929551a6b774c58dbb42cf03dee00,-0x2ed2982640972031d995cf785ae73552e4a271fa5c899d53e7864d980e680,0x1909b1fe34fcc806e753d04223feb3c9f5c45c305f6c32a91aaf5344a6c780,-0x9b0120639ace9b154010f69365c91136c105df65fbd20e9f25b4d252a3a8a0,0x2e3c527d4c43f279e5bd6d4a157f88ba10d2cfba8fba9a16954d558106c7a60,-0xb0fafd21be6c1a541279dfd51b854f587af258c1b2d6f6fd759a1d4998c6360,0x22e1f7cd3eda0653e45feefd29affc987d1bd6e11f0a2aff0f2491835d91a7a0,-0x5c633f2a698b733ff4a8a9afcf26df3afdfb48461873050bb1253de497b0ba08,0xd073740836fe33a6fbdfd7479288d712bcd49cba5d44dbba5024be679eb468b8,-0x19504fc67fdfae364b411cf646acfd297e0a15e96de73eea37b557726de6a6e38,0x2ab5a9ff247d8e875d711241ecea0db512db6fd863eb4ef5e27597905dadf6688,-0x3efa864155505c3b8d9e37e18a3112ff51c124f2bef71cb883f3a83630b7283d0,0x519154eb1b4e2935eff7a71becc5fb9861115e3f89fe470f52fdf61764b304db0,-0x5d2444e91fa48ea4e399bc628baaaa23eeb3e0e9bd2a6f30ba9aa2961c1846cb0,0x5e087d76412820777383d6fa5072eeb056a21d3eb50b5e0f300d2a1016da854d0,-0x54182d2834f40d1954db201ffc4c4700663922774b706bd168ed5dd4469e0154a,0x42b2941aa875a591984797a0bccef52c91bd1d7296967955d2b6682c67296d3a6,-0x2eefd4e3b608f94e29e0bac08baa786b7f8c20cd22591ceea1a0a1b4a15161726,0x1d4d529f4859c6f463e443dad75cbacb4cf06639feb9512e5ec39552a3cef284a,-0x1036ea6efc67a02b005ad172094e71550760bd82a8096116011484b56522e6714,0x7f0ff96cdffae6df22349aa534037f1cd103978c78078bb54cb4834bb7636c4c,-0x36f6c7b6e845ff620725ef948114f1303dd9a165956777ab99f94d4b874ab44c,0x14f0cd37d40b57f2daa6a465a9c8ee9cbedbe59ad8f4c58d6fc549e6bac81514,-0x7007949b19f2e67e6e2945e768bc0bce92b6671ba02910bb250e5b04968f906,0x20bb7415ad2a7d3d8f88523a9f5e11a229124d3f2d2cc45c22e98e36fe28a0a,-0x8501975c4858d4c41b91018c496e32c7a0261a95165cdf672f185f3d585e0a,0x1d2d65993fac7c66de84845ae7ac2078a9a637b178877134d4948960a83586,-0x57cc191a570872f054c4c605d2bb2f665c263af567e08c4ee62138419c028,0xe07cdb078568aa45f46a9aa4575fdf2c036a20e0c8dabcfe22866f6e6098,-0x1e29a201b19903a8f24f541b4093574b3617463697bd2079472881265a98,0x35d65df5f0a6439b4425db282d199fc699518ce06c5e2598955ade96e28,-0x4e97940340b879331c686452724cc8ed38edb687257ed39fdddeaf6dd6,0x5c2607316487f6a9e76ff62ce33a7813be2ad06b8980e80bca1df973a,-0x54e4bdd5e938d946dbe3f045704939f9c4037cee5ab9314c1abcc53a,0x3bd25ce009f8b58a1238cf1e1f37cfe4e2f7b28419f1b915e7c2f56,-0x1f2fdde2eb9b70b15503dfc797dbe0f72384a7d07f731095d4d414,0xb890ad92c8f780948c8f3e0110ea8829d3543a9c54386417454c,-0x2de7cb17f14251d13fdc23f69b206e98b61fa4c8a4d40e9a34c,0x7282080803900fe55f177d169560e97a938daf39441e5c014,-0xa2ca3ebd09c88e53b1ebd37a2b34db548665dc255fee212,0x7340a2ac8b7fa03771e7a5987991e5f5fe5e0da139a1e,-0x2114f0b7d643965da8cf9feebcdd806913972a2ae9e,0x2b30f86dcb5cb465708a09f83b2a9d6b20b04512,-0x7420ef83fc22a89200000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 23 90 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 90 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 54 indices rho q27 m27 27 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 54 indices rho q27 m27 27 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x16676b2372e4ad1f9256a762847991dff,0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r28 : List ℤ := raw_ints% [0xee1e9bff30519c1c643bdb9995fa96cca29bc3f851fa4fe854400000,0x148181b3aeaa7fe1f0f14073a5b602ed3d692c31e748eeb3412140000,0xd627089b31cca85c81057301efba5b6b0bc4b524ec21855ec59c0000,0x581a4738f3525e1baf47eae4ba14e308f702e48f2849767806133000,0x19a40179160373d2f36d07d2c532f59685869c11e8b30f2dd4b5f400,0x59db8af16e55bdb6de1df8a5bccd5d8b8cd87e00a48bfdcfd6a1500,0xf6267972a907eb63e29f2f63c3b66985004db4b61a1872d04f2bc0,0x21c55ad68f08b243c405f9fe04a0fe04604e6659f075fcc80043c0,0x3c6a4456f7fa519725483e0acd6cec4a6ad4dc49f33cc18458ef0,0x5918c540ab1b99124cf9c7a70693550b364d7e3bce6837b05a70,0x6d20a9d23311a7ce1e5c45fcc6abcf2f0e8ff22b251dc827894,0x6f7c6cea74098ff0235b2084f0620e0362ba441f4dacb24794,0x5f2416f8f883ce886b74dea39d3131c5fa1d8615b5cb8a429,0x43be68ab3a744ba554a1725710772be6c39081d398a289a4,0x2816726363cca1c540faab67a48262cf63dbdc987cc8830,0x139316db196b812b71474d4673c6d240ef689ec01d1a08,0x7ccbfb93ee96c2f51d40c7898b4f8baa8cca8a362256,0x27ea073915447b2ddeb36715d4674a0e998c2422378,0x9ff9c027723ee719b4ce4580a6ec2501a89e1e1a8,0x1e3ae7d1cd73ab346f375afbb1e52847112f31a4,0x40d4e3acc3fb2f48a98712f6bfa84100530619,0x57e6f9ab97534ff783a8ff1a8f8d1b5dfc74,0x38a7206796a876f790ba47f44433e9c24c]
def m28 : List ℤ := raw_ints% [0x0,0x3d88e3984b950b818b46179b901be9d2b87be03b28ad8348e09000000000,-0x691af51a5fdb0dd0b903a7658a108c316475743f2f9f6725002513703f600,0x56c4563d12b2c96fbf00158fcfe3fdeca3200c35d43dba403276baa39a1c80,-0x2e1c068222796703a94c156c4ae2c36cb3f0f7d6a789924e15765e890d34180,0x11b9bdcb5bae595140d73ced020ca3fc888f356fe6a72af6315bb67fae7f8820,-0x5406d400be9acbe9b87a91f61f785b9aa162ec8942a95606f11404cc525d4ee0,0x13f609f04356287f289dca702d3556fca4e0ffc35f116922c114b9eb2abda4b60,-0x3e7ccde50b9ea09a7d631cf3fdfb1b038312a86748a288650c51e7b10b4d5b7a0,0xa43b743e57b20d3e8fea09978216bef5528f0f59c512236145e480c04558c0be8,-0x16f9567477a43d079677bc83c24ec44d21d2b27ebe2fe9a587903837f192f7d3d8,0x2c439e1458de3590f7d48319afcf5f5d6d20fe3b2afb21b65640347bc15ae2ddb8,-0x4a06e5b09de148ba7f31a5957cd5014abe2f3995287285db6e90a8adfa84dffd08,0x6c270741e1b18fc213f96e221d23d811085784589e848adbfb672a6aaa10557a50,-0x8ab8356441d6ce0c4dac0566deae9bd1114f24cd9f7d74fb040c8f4cfa72fb1530,0x9cca7a2392d599a1afa674f81f99880a9742cb51397b9f954e10200f88dfc543f0,-0x9c986ec64e8dc433aaa908ea3d6b2c4c041c43192c864cb224ad5dd94c99b9ad90,0x8a764f3cb772c00dd0de790e937b5678d44177f653fa916aab98af25e90577fea2,-0x6c821b4935cbdd2a70fb6a99b17b9888c51a3c443c5e6d6ff7b93d388dbed3e08e,0x4b65a92fa5accc3242b308958aee76ace1fbc9397db234b786ed51a153ec6e5406,-0x2e70d852a57e135c01a6f91ddc5ac9483a380928364505dc2148c95ae87c5aeeea,0x195597fbea2ba1699e0dee63f72cdc467b730f6dd5c8b12908e33443eb08b42974,-0xc38a5970116decfc6d1200b8abe9c02531dd195224bc0bc0b3ced99ef294a396c,0x533b0f68faa0bf29a04ba6f19e03664a9ce9ede2804b1048a6c26dfb647a3a55c,-0x1f2b0ad3707a367dc53df530df00f2607a6c4bc038c683a2bc81dad4bffb87804,0xa3b377c72cac8bd574f715468cf2549b006866f42eeed5efce3d8635d2d8a23e,-0x2ee4ed0e72e0ed3a57740d6dd70ab0497fa1307cca265a1bb6faad21bc336192,0xba8e0d0379aa8c33a9500e91c3af4b2ff4e7ea7dff6396e8c090f18825d5a5a,-0x28002642fe6593734df468e8e76ac77f4c672b7c3a9ba833c10e0721834b4b6,0x756faf9659fda23f1f64d4b57a3e7f90ae53475ba677a891610f1b9794e728,-0x1245f578877b27830eca598d677f1b1e4c42fb93f81680a03c60140c036c98,0x2629ed0165b88d2007a4fc8025af9e5da8290e1b93ed160f5b254b42b7478,-0x42021952ff7a741356a9c1c5796226220ce0e9e30cf1cba6fb42a3285848,0x5d1b27b06c47687db22dbf3af4dd0827549e99b4cb4d2a5625444d84a9e,-0x69239d55e0f71985b6239e52844f592f7467b9068e61ba5a6ad7ca7a32,0x5cf253fc36875c5e36781dcbb5010e894fab0110146ba9bf29ceea9ba,-0x3e96b0760bc8d5950db68dee4f73c78de8a760b7a83343edc1b49556,0x1f08c24ef849cf01142d93d0acda8411c32bd0bbaf1d3fbe8c6c4b4,-0xadc0715a6635b2481cf86722e0c70db5ce44114e2fb7f982ae82c,0x28a34b83332d4ff0d01e9f00d7afe4511ed278418d928302661c,-0x5eac23bdc75688792cc97046148a7746221508b97c2ddc9d44,0x7cbc16f6976c17aa70c8c666ac54cf6a3d492b78680bf0da,-0x5121c4eb51a8a1568aa2afecf15569727cf124e97bc796,0x152ed265b3f9d4ad167cd6cbc8a831eb40084ab1de6e,-0x18dd6aa5c1a28bb77946c697d08abbf095da175c2,0x3b3d552ac461977b000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 23 92 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 92 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 54 indices rho q28 m28 28 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 54 indices rho q28 m28 28 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [0x38a7206796a876f790ba47f44433e9c24c,-0x16676b2372e4ad1f9256a762847991dff,0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r29 : List ℤ := raw_ints% [-0x25a21c1c969ee3a80481aa6895ac2a867d9020635db517e4947d000000,-0x33d6279add35071fe2cc8a85b3e0fb66d023a14c2a0273a0c73ed00000,-0x21d2ad8665e9d954ac145743117eb18e874560c67bcdbe22b30f6c0000,-0xde8e23eac5a28dfc7baa2df3b87cea4034a751e900273dbba1131c000,-0x40bebd95759b55924264cb258235c75f59d29c02df4a3c7ebc01b2000,-0xe2cda12a9f78b4878328986fe571a3dbd1c4d8d96bbd299699ba6000,-0x26d027f5f8267106623593762aced8eb33ea20c4d874675203761200,-0x5528b2012aecfb33ac6910b925d420b32b472a600c9db1c203c0a40,-0x98447cb08010b6e7bf7f81bc66712fccfe8bad837760db583f1500,-0xe06e27ed75ce21d1b1d998bc2822109aba523ffed4f9974058b90,-0x112b8f451f52821058159695945cdf953001039f6e24b85250fa0,-0x1187ab754ba6ecce85f9f8ff6235f1752381d8c89e31a411cccc,-0xef315504a710700e3b8888a6b39540678eac32a7f51beac7c0,-0xaa2fecfebad99e67001bae259e6a6d83d8b93377540c5e1cb,-0x64a0e0ff42a938abd6c68897d053be73a5113a6d13897928,-0x311806279a0661ec59b1ae3c92c15c16a6d751ff4b1d58c,-0x138b4417c87aed1b230fe9bb51cc1e99701f818b5c6300,-0x63e997a6d1760866fea2957c02ffbf7f99cf689c9532,-0x19002efe4eb79bce57cdc38afcaeec50f35986610b0,-0x4b7fe1c950f382416d4f01b8915ce18d1ef91ecb0,-0xa1b55e06f3c231f6d9630939bbded975eaa2580,-0xdaf23a92c7e3cd002ea484015599d68b7242b,-0x8ce50a53cda431d1664fdb968df82aaaf48]
def m29 : List ℤ := raw_ints% [0x0,-0x7360aabd8db77592e5236c43ae34566b19e8446eec455628a50e000000000,0xc3f8c679967487d012771a011d4c7920fff9e4dfc82e565dca37ff3b72de00,-0xa0d6e4ad2fe45d8f8a524b943e8975de4601802b471ed0a9954364888753a80,0x54f4b36ccd3ea1fb6d8d167709679e7087731a020ab255944bd0b464341a2380,-0x2074023e9d84f3dc0da4dab75ac9bc657dac8247bc1b70866ff02dde3e95505a0,0x98d4a2b662acc0c46a096ee92212de2509c944140f4a0e6cb1351ee0d4a9e6560,-0x240e8cacf8b5b28bc18e0b3c05213449d4aff86296eeb33f72d593b5f2a0cfbe60,0x7010cfc908a6c36d73cd241449e2fa558ec0f8be74eeac2797d95e2af0ae4354a0,-0x12453f409e19ab5476ab3d1e70a16e2947df0a64188b627d78b4043d0943ff61948,0x2892737972827300e0b65278b3c2a55012538aec8ed5604e66108afc99f99e09778,-0x4d87215c198737e891e402aa8fccd15865dd779d2739276b3b08a2cc2fff8c237f8,0x8089e8f77510b8c501aaa815f66dd0179beb1f5383f785ba8755c1b7c337f7162c8,-0xba17b6414976958da3e81201b70aa66c8cab9e1aae2e47b30d810c0953337d19990,0xec6a39e34fc6338c0c871914c096e00941ac29636ca9f3123d6aa892a5a179161f0,-0x10888d37c074477a7c315f648fd261dd778e8fd4a87ae243ac60b2d652477e779270,0x10569a23432cb7f2d04436880c3d77526272e2a019d555f6dc456925c7d3627f4d10,-0xe49041e65bff21b496119d19ed749dc8da0c04517ad20e70fb210697ab1df4f88da,0xb101765e7dfa3c50a75a2df83fe1fcfdfd31eb9b58849c3073ef0144be5a3faad96,-0x79751b8b8ec467be6f5d6aa686086e33469556d138e90414cda2edd142ed859f9d6,0x49d24deac107cdbc43e022276c1645c8b815238d2075c2f52ed8cc04f981257c91a,-0x27b47a8521077365d07d97bee6e93a83aba16d75a06c3c437cfce751c755573cd44,0x12de03c05fbbcdf97590f32b2b58541e6c8bfcd7d720934758e0dbdd8b72a79a29c,-0x7e71a4f902aefb22d310459c3041e1b10314eee459b0e4afa28426d3e2f45e297c,0x2e8b722a6cbae54b512450415fbb237c39d858e571a57179ad0a9a252774648564,-0xf002a0475cb2d744f80e6c38692be39a887be95e2de71f7f9319fd6fa04a485a6,0x4369609c76ab5fe111b091500841dd48b953f9e98c21a56ca5eb797ece12c726a,-0x1068d1821f8072aaf495197cae7d174ebc0fb2b2219f14998632aab06f1ce904a,0x3706085336fe6d5150a0609ca76c8ca3211bfd732dbaa990f553675a369f0546,-0x9d9a0540136cde05d72f354246a761f05a8f42fc44bf058cdb5302ba41bc048,0x17e034eba087e2bddc0c28573d03b4213c09c88bee3bac7b59ea68278c4fb78,-0x306fd31efe1e9faf031617d1d9babf4f7665e5b41503a7abbe31c27c6bf3b8,0x512ad2f924ccc8ae2239764b23bfcefce4d24204c1fb825197173e5f79e08,-0x6e999582910ea289ab6a6a077e785fa94197d13bcd5fbe478ae1914556a6,0x7841a2a4eec1d53c17e3a61fcb553513b84401c02b7a7c8786ad2ae0dea,-0x65fbf412488d5f3f210a32ea8d7b31a59dc573edc753f1c8bb9746566a,0x419a93ec32cfbbc5180866d668c8e356eb369899ab38891cf2bcd3da6,-0x1eed899ff592a9d275912bc341a98e53e4f8e4deb736659e4e7bd404,0xa3c0c1b0dc48440aaa6d9ed3f6b9f919760968f746c954217603dc,-0x240058e424a57bdaed74bcc3e17cdcacecdfabeb5c087868a513c,0x4e4de0ec03f02700fd809aa87d5ce6e3e1a509c6d317e9e35a4,-0x5f9621367c3ee79dd992c61b22a5928eabbdd10ee37b300d2,0x391b718a7b46b51e3bda439e5fce5383919e9b8611e735e,-0xd8f93a745c729f8bc6d0dcd61a5f2fb75a28faa96dbe,0xe4f9c5e5a47799ce001908df8c353c59c82c7f2f2,-0x1e369a5920e9ecd88000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 23 94 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 94 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 54 indices rho q29 m29 29 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 54 indices rho q29 m29 29 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [-0x8ce50a53cda431d1664fdb968df82aaaf48,0x38a7206796a876f790ba47f44433e9c24c,-0x16676b2372e4ad1f9256a762847991dff,0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r30 : List ℤ := raw_ints% [0x5d97dfeb7292234b534449e8341694659594751fb6de28849348e000000,0x80e0ba190e6d1b3ffd28d10015b0402622e5a27e3c4f5cb799077600000,0x541092463e0c815c3349f0a2551e7979b32bc1ac03e45ee4eb2ba300000,0x228f49570e967a0c0304ffb2d74c1cf46803258ef89bfbcff79129e8000,0xa0cdfc11998553bb0ee7fd6fa2ddc0534231864709f5dfc993714e2000,0x233142a4c73725142b56bf4f4f54da32343bdf28933de9a7f127f95800,0x6051cc006bdc2d1ef3e5731cf5eb6469b08f5d58e8a2c509a13696a00,0xd33c9152c348a843825c87d8fc17e18616a09519b392f7f5803ff200,0x179840010ff55d672ae7b1caa49bb01b2c722fe56b647d1303d0a240,0x22c236bbbe47370e45ab612886d9f71eaed7f164130f2b55473da00,0x2a861da8cc171b3e6e50d8872fe24e1ac24ed9bebd515253fb52d0,0x2b639435c56417389783655c6359570ba464d50df23a70fd1fca0,0x24fa729507f010999ad6b2ba9e07f0ed13abeca24654090fe1ac,0x1a4ac97775dfc1b80b6a7b6c50ad13e4dbc41a2da29b371c278,0xf88d404772b7ae2104a7a97704d2d7d02062c1cf1bd33607d,0x792a21a9d76a37b0a04a2443ff331f7ccc6f9061f39028c0,0x303183d2091a9f12f2991968be1fe42c486bedce09049a4,0xf624ea619410639e8c4ff50ee2cb18130ddd974f16b30,0x3d87a1691dc846b0049e21b63f4f8745da963dd0f8be,0xb99c8122fd70d316c31587f3dd6ca9c46e7a31c060,0x18d14fce320e3f34adb3c2747db015f070c350aa8,0x218f13e01f0eec20372385bf94d4e5545106898,0x1590c00e46257c0a4501cdd6aabeca4a611bd]
def m30 : List ℤ := raw_ints% [0x0,0xd855402369b7fc736da26afee6a22208d093804ffb02018c357a4000000000,-0x16d73bee8b90b43dbef54c50108d5c239d48252ea765325f21b307d1bc032600,0x12a3db7b78957313e19021cec969f6bfcda5e8b7c7d27dfe92ae9046f7547a080,-0x9c9a96aadf247c26479b8781c58111d06bc9bb8256b6c5ae772ca97a16f926d80,0x3b74876f388f7adac54f2ecbd4b29bd626a65ac1afa77dcf22ba5950435287e120,-0x11631e48ec2cb7e576965bd59887c5ea0139a2e13bc9700b9abf6792c259933dde0,0x4131a2cab3f89a3fd8a77cc395798313d0cb8027fa66be39a32becdfffefd052e60,-0xc9346d80bea75f33526ce65d8da7b1e206cd4bcb6c014dcc8a5d37dd41e95395ca0,0x209006c821658b146b3264cb16b383c1a4c7cf5f6ab8ab6870bc460fba2b3f885228,-0x47c0fedd60d4b46aeca1420879dafc2a39bc69a94bdab3a6443689468b900e18c398,0x8801bf11d3ff4255333418bab8e0b1b44272968d0792ecc84f1c6f2b8e7c1cf2a578,-0xdf96032f42e05c4f419b5d31ea1fd03daa8526ab299b7af94b06bf697884141adb48,0x140d11611f65bb3f0f7664b2cc81f8da046306cafab3166ded8e5b0f4ede2e2589c10,-0x193c08399a814b9d135c1950c6768eabbb78e515f7cb3650c09895d95230a3e06ad70,0x1bf50514e0d57d43a4a51e1289afbf8fa86be554ab38c19b48b05fc81486f11da77b0,-0x1b56da488c7ebadd07f617629e0df5f9da77c0d0125f199734162c3aef8613ad057d0,0x17a3fb2481b74b544c1cb3b671395e071b0a01485c71f20fbd9e624527c44bb2112f2,-0x12182fbb13384e0919e10f20a6d85136ec0a3c2c637126bc903d81cc82dea9f067bbe,0xc433c168115393f2ed939990d630bf87801e723fcc34bc3b7798086759ed2291f836,-0x75afdd4a4a0814c196f8df1c6d2e20ea2f7fc2669ecf69fbe48c7d21712b2f8fa63a,0x3e6a4abe4c36196193ae7bd78b3cea8aabedd4135549309437cb243f2170359b50a4,-0x1d37d75df5d8a51789f4df75ceed38d8d638e2cec4a4e68299e07d911215c6ecb2bc,0xc0b54e34c1809d614ea12ff8fc9e11bedb07703b72fef7481bf3e94b87870531c0c,-0x45bbfa0838408fff57fdbc7f87a2b8c008443a6a6b92dc9eb2d76f5934b9cba56d4,0x1610e9810dfe0231d21bb2874edb01b6cbdfcdd699a3649daab3f40425b0763d49e,-0x613ab7c45c1d2462c66af2a4b457a72780dd0a9836dc04e15e9ae50fed32b8d232,0x172bd307704ee26d3dedfd75029b7ef65accd9af5cf887568dfc5322b23273009a,-0x4bf06bed0f037cdd0d960777d3fabc9354a6c77d3954bf625213e4c8b1b363876,0xd430fcd16ae3369b3f406815edbe26b40b068a3abda0226307bdd2fe297be348,-0x1f4b5f8e587588a2b69bff0b6c7ed6ebac23212b16814fe6e1fe5eda75b79378,0x3da92ec27dd9262c9446ce642db28cf8a88683e095e11932e2e3f107f9c3e98,-0x641787cbd3fd1a0bb65dc60b6f41d01522af8a4f6c4000d42d75458b3db728,0x83ba0693f73d2161e6d95c3777d0560d66a609b71bc692c3a6a12e362f7ae,-0x89dfcab65a7072f777a48f1d6c2c671cf68a7b511781e365ef64cc4aaaa2,0x70222b408f9932f760884ef3df7ce20204675c1f0dc801b5e54c7850c6a,-0x44e2801f6d4bd375ed73e81782d456ace979f5d914caf95d0e962d7a26,0x1edd72c02e7e8a0cce763093ec8f13de9c42a7f2c816bfa7a19313fa4,-0x9a7d469844615c39c7e8ce3cff6f947c6f53ad3654365a344ea2fbc,0x1fea602c0d8e891d85f95035e734e364aaa03f3b750e010662038c,-0x40c9fc0039df36f7f70425f2c6bb54df42cee1e9ee37e7141354,0x494181ba888e7632d799c4dc0463846dec373e202e1d25ddda,-0x283137dc478d5e13686113534e9d456bc12e48a7a0921c96,0x8adf160a958331455b024278c8f4402913dcf424bb08e,-0x83c127eafe0ad05d21daef3b6ddb29c7ae00c888a2,0xf6805961d9a06bac0000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 23 96 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 96 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 54 indices rho q30 m30 30 37468278360343934955371520000 30=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 54 indices rho q30 m30 30 37468278360343934955371520000 30 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_30
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<31) : intPolyRF (mz e)=rfPoly (C (37468278360343934955371520000:ℚ))*rfX^30*(1-rfX)^23*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V8C31
