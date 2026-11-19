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
namespace CatalanCore.Li2.NVMod.FamilySource.U7C30
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,7,30,size⟩
def bases : List ℕ := [1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
def num : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0xaa0e21ade5832af82bc00000,0xee7082e8c2bea939f6ac0000,0x9ea0f9555646fd7532200000,0x42a271b616be135b4e54d000,0x13d72ed2b5aa1429f8869c00,0x474bb133c49d8c5f331b700,0xc8c3b4dd2156316ca4a740,0x1c6548d6327f08c131ec80,0x348a94331d3eb7f7d1f10,0x5072525113d8b2c862e0,0x66c0212d623faa701ec,0x6e0894c822341df848,0x630a1259c6d7e82f7,0x4aef3a13f975bfaf,0x2f8d4f8d0dce361,0x192fd2f6633335,0xb0c45d9a46f6,0x3f767ae01d6,0x125558a70e,0x4280d9d2,0xb645b3,0x162cb,0x1b5,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x5,-0x37,0x21,-0x3e9,0x8f,-0x861,0x2f7b,-0x832a3,0xe28eb,-0x10d0971,0x37b7bb,-0x17e107,0x32584ca,-0x242f7713,0x602919,-0xfa6b067,0x904903,-0x48b841,0x217963,-0x1b94019]
def rhoDenominators : List ℤ := raw_ints% [0x507d24dd300,0xd021fd10,0xe18840,0xdd6e8,0x3e280,0x1a90,0x3840,0xd2,0x1c0,0x1e6,0x1518,0xbd1,0x5cd0,0xa0e,0x2d8,0x4ffb,0x3cf00,0xdd0,0x408c0,0x5ad8,0xa180,0x1a7f0,0x10b2b40]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 31
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x15,0xd2,-0x532,0x1761,-0x4f7d,0xd3f8,-0x1c638,0x31ae2,-0x47c2a,0x561cc,-0x561cc,0x47c2a,-0x31ae2,0x1c638,-0xd3f8,0x4f7d,-0x1761,0x532,-0xd2,0x15,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 23 li0=padCoefficients 23 (liCoefficients 22 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 22 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x14,0xbe,-0x474,0x12ed,-0x3c90,0x9768,-0x12ed0,0x1ec12,-0x29018,0x2d1b4,-0x29018,0x1ec12,-0x12ed0,0x9768,-0x3c90,0x12ed,-0x474,0xbe,-0x14,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 23 li1=padCoefficients 23 (liCoefficients 22 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 22 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x12,0x98,-0x31e,0xb5b,-0x1e48,0x3c90,-0x5ad8,0x626a,-0x419c,0x0,0x419c,-0x626a,0x5ad8,-0x3c90,0x1e48,-0xb5b,0x31e,-0x98,0x12,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 23 li2=padCoefficients 23 (liCoefficients 22 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 22 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x52,-0xde,-0x33,0xb28,-0x3168,0x8448,-0xfdce,0x1717c,-0x1a1d4,0x1717c,-0xfdce,0x8448,-0x3168,0xb28,-0x33,-0xde,0x52,-0xe,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 23 li3=padCoefficients 23 (liCoefficients 22 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 22 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x6,-0x28,0x276,-0xe25,0x3168,-0x75f0,0xc738,-0xe916,0xa24c,0x0,-0xa24c,0xe916,-0xc738,0x75f0,-0x3168,0xe25,-0x276,0x28,0x6,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 23 li4=padCoefficients 23 (liCoefficients 22 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 22 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xa,-0xe6,0x5fa,-0x1473,0x2388,0x78,-0xaed8,0x20472,-0x37ab4,0x420dc,-0x37ab4,0x20472,-0xaed8,0x78,0x2388,-0x1473,0x5fa,-0xe6,0xa,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 23 li5=padCoefficients 23 (liCoefficients 22 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 22 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2a,-0x1c0,0x516,0xa6b,-0x7c08,0x1bfc0,-0x3aff8,0x4e83a,-0x3a904,0x0,0x3a904,-0x4e83a,0x3aff8,-0x1bfc0,0x7c08,-0xa6b,-0x516,0x1c0,-0x2a,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 23 li6=padCoefficients 23 (liCoefficients 22 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 22 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6a,-0x18e,-0xe76,0x812d,-0x1b5e8,0x2c7d8,-0x7ba8,-0x7f12e,0x133f9c,-0x18ac94,0x133f9c,-0x7f12e,-0x7ba8,0x2c7d8,-0x1b5e8,0x812d,-0xe76,-0x18e,0x6a,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 23 li7=padCoefficients 23 (liCoefficients 22 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 22 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xea,0x488,-0x52da,0x12ebb,-0x80b8,-0x86850,0x1d7018,-0x30cdb6,0x286f0c,0x0,-0x286f0c,0x30cdb6,-0x1d7018,0x86850,0x80b8,-0x12ebb,0x52da,-0x488,-0xea,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 23 li8=padCoefficients 23 (liCoefficients 22 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 22 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ea,0x21ca,-0xd386,-0xbd33,0x1058e8,-0x328cc8,0x3ad748,0x1fbd32,-0xc65e94,0x11ed5fc,-0xc65e94,0x1fbd32,0x3ad748,-0x328cc8,0x1058e8,-0xbd33,-0xd386,0x21ca,0x1ea,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 23 li9=padCoefficients 23 (liCoefficients 22 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 22 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ea,0x8f90,-0x3c8a,-0x12cdf5,0x42b718,-0x1993e0,-0x1391958,0x31c535a,-0x306c2e4,0x0,0x306c2e4,-0x31c535a,0x1391958,0x1993e0,-0x42b718,0x12cdf5,0x3c8a,-0x8f90,-0x3ea,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 23 li10=padCoefficients 23 (liCoefficients 22 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 22 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ea,0x204e2,0xbba6a,-0x568d13,-0x5efc8,0x3727698,-0x7d5fe48,0x3098d12,0xd362bbc,-0x171af6f4,0xd362bbc,0x3098d12,-0x7d5fe48,0x3727698,-0x5efc8,-0x568d13,0xbba6a,0x204e2,0x7ea,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 23 li11=padCoefficients 23 (liCoefficients 22 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 22 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfea,0x6bcd8,0x5c0346,-0x81a2a5,-0x6649f98,0x115da210,0x662a2b8,-0x4bfb4f96,0x5f9e8fac,0x0,-0x5f9e8fac,0x4bfb4f96,-0x662a2b8,-0x115da210,0x6649f98,0x81a2a5,-0x5c0346,-0x6bcd8,-0xfea,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 23 li12=padCoefficients 23 (liCoefficients 22 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 22 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fea,0x1594ba,0x205a5da,0x5f5b38d,-0x2901d6f8,-0x15bc6208,0x121d532a8,-0x1309bb38e,-0x1502d2174,0x32b419a9c,-0x1502d2174,-0x1309bb38e,0x121d532a8,-0x15bc6208,-0x2901d6f8,0x5f5b38d,0x205a5da,0x1594ba,0x1fea,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 23 li13=padCoefficients 23 (liCoefficients 22 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 22 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fea,0x437c60,0x9f41d96,0x4c2648ab,-0x4493d4c8,-0x36cd7f280,0x45bc7e448,0x97ff7597a,-0x1319b41344,0x0,0x1319b41344,-0x97ff7597a,-0x45bc7e448,0x36cd7f280,0x4493d4c8,-0x4c2648ab,-0x9f41d96,-0x437c60,-0x3fea,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 23 li14=padCoefficients 23 (liCoefficients 22 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 22 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fea,0xcff352,0x2da2a4ca,0x25d8c24ad,0x5d09ffb58,-0x167284f2a8,-0x26f4ed05e8,0x6b8fb39b52,0x280e3a65dc,-0xbd26368154,0x280e3a65dc,0x6b8fb39b52,-0x26f4ed05e8,-0x167284f2a8,0x5d09ffb58,0x25d8c24ad,0x2da2a4ca,0xcff352,0x7fea,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 23 li15=padCoefficients 23 (liCoefficients 22 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 22 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffea,0x27ad828,0xc8747a66,0xfd1a0c7fb,0x5aebaf1b88,0x1ad40c2e70,-0x26d892638a8,-0xc6e0cc1576,0x63ff99ac84c,0x0,-0x63ff99ac84c,0xc6e0cc1576,0x26d892638a8,-0x1ad40c2e70,-0x5aebaf1b88,-0xfd1a0c7fb,-0xc8747a66,-0x27ad828,-0xffea,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 23 li16=padCoefficients 23 (liCoefficients 22 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 22 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffea,0x78686aa,0x358767b3a,0x6088cafe4d,0x38efa92eb28,0x9f981d9e8b8,-0x7e05aa123f8,-0x30dbc1e4fe4e,0x38a93c9bdac,0x4e8a470b213c,0x38a93c9bdac,-0x30dbc1e4fe4e,-0x7e05aa123f8,0x9f981d9e8b8,0x38efa92eb28,0x6088cafe4d,0x358767b3a,0x78686aa,0x1ffea,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 23 li17=padCoefficients 23 (liCoefficients 22 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 22 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffea,0x16bf9230,0xe07957db6,0x22cebe11f4b,0x1defe0cd8558,0x9cb216f194e0,0xf34dddad17e8,-0x132b0e82fd066,-0x38a6ffaef51a4,0x0,0x38a6ffaef51a4,0x132b0e82fd066,-0xf34dddad17e8,-0x9cb216f194e0,-0x1defe0cd8558,-0x22cebe11f4b,-0xe07957db6,-0x16bf9230,-0x3ffea,-0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 23 li18=padCoefficients 23 (liCoefficients 22 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 22 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffea,0x4496b4c2,0x3a1324852a,0xc17370cf86d,0xe4b225d12c78,0x70c8ed3449418,0x17d56d18d50c78,0x1a5b770e9e0792,-0x189fe48928be04,-0x431d244c6091b4,-0x189fe48928be04,0x1a5b770e9e0792,0x17d56d18d50c78,0x70c8ed3449418,0xe4b225d12c78,0xc17370cf86d,0x3a1324852a,0x4496b4c2,0x7ffea,0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 23 li19=padCoefficients 23 (liCoefficients 22 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 22 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffea,0xce741c78,0xee32359b86,0x41779e07d29b,0x66b2f28cb5ca8,0x460e394cbe30d0,0x16e7600746b41f8,0x3a9592753a034aa,0x409bf45b60f2aec,0x0,-0x409bf45b60f2aec,-0x3a9592753a034aa,-0x16e7600746b41f8,-0x460e394cbe30d0,-0x66b2f28cb5ca8,-0x41779e07d29b,-0xee32359b86,-0xce741c78,-0xfffea,-0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 23 li20=padCoefficients 23 (liCoefficients 22 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 22 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffea,0x26cbc539a,0x3ca8830de9a,0x15be0261ceb0d,0x2c37ec99661348,0x27d4e703f4f3378,0x120bd3cf61ce1f68,0x470a6a37b04d94f2,0x9f0569f00c07eecc,0xcf7a613494bdf1dc,0x9f0569f00c07eecc,0x470a6a37b04d94f2,0x120bd3cf61ce1f68,0x27d4e703f4f3378,0x2c37ec99661348,0x15be0261ceb0d,0x3ca8830de9a,0x26cbc539a,0x1fffea,0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 23 li21=padCoefficients 23 (liCoefficients 22 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 22 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x16,0xe7,-0x604,0x1c93,-0x66de,0x12375,-0x29a30,0x4e11a,-0x7970c,0x9ddf6,-0xac398,0x9ddf6,-0x7970c,0x4e11a,-0x29a30,0x12375,-0x66de,0x1c93,-0x604,0xe7,-0x16,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 22 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^22 := by
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
theorem cache_li (j : ℕ) (hj : j<22) : coefficientsPoly (cache.li j)=liNumerator 22 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x12a3f7cc059aedda266d9a1ef27f5e000,0x27992cd86c62a77d552ed7e39969bb4800,-0x28e49b8ed28410a5237dd2fb89ca6196000,0x1b59faa6c93ab05be6b7c6b23e6f9ce09600,-0xd51b296bdfbb9ddad342e48fa2ba2e341c00,0x50859d4c8b5be155bc18d73061484be35c100,-0x1891c54ed43e6ca186af57efb408fa45545200,0x63893274f71ebd6530d5b2a722ac8eb3360b80,-0x1553ed15bd5170dd7f594464d36fda97032cd00,0x3ecafc9a22b4b028f7c0981a8590264d1e900c0,-0xa090c97ae9df798d3335b349b30b5229079a780,0x167c207d866dbc6f09bc7a3562ab23b222274cc0,-0x2c741ac899c457f7335e0dcbbbc484a71acdcf00,0x4dfbdf17422734db3e2b1b93a3ebbd8bc07043e0,-0x79ee9b26f23b373659e01ee50b87a5709df67e40,0xaa84e554f994648a57dacf5d5a23e73f0955f5c0,-0xd5df9c90d23ce077a5a75f528e9c9067992532c0,0xf1146e37050b9b6fece1ecca4fc545f26dc6d330,-0xf49376029603112a913890d9bbc2586be60ed660,0xdf83b71081aa5eedce62d869376d3e8d3f65a330,-0xb813ed124a26f5de8e65e81fe6255f7d53f85f40,0x889987c8067b095efbd24b1761adfbdfbdd40b18,-0x5b482e24ff588a1687777f60b09359fc96d51ed0,0x36de53658f131b66e9d1b16c94cebf9114570848,-0x1d9e22181ee608267ba556ba07aea7ba48ba7be0,0xe535f2be0e442a2e6b9315ef56d4e67deb5a3d8,-0x63100701cefb947d9c07c2734f2f3913994ffb0,0x261f26ebe36bba31203f413db4a40813a2b3448,-0xd019e510b90ef4a7e3a5a6723f4acde7ab2e00,0x3e9e80a4a8f54e35b997261a4826f6c10de530,-0x1083781c23c2b51dcece50c5267dc08e87d020,0x3c99275736e39d913c05ed3e495ed44e36f30,-0xbf98618714a27f1d8dfd5780083fe495c580,0x203f965646c5f7823d47a90b93279176ce80,-0x48ece24e00a6f96858e1979ac35f661fa80,0x880274c860522bb8f2833a23ec64528220,-0xcc6dc16ea7e919eda7fd0f008c84ca6c0,0xf02faf219e79c7e5e4084c30cbde9e78,-0xd399546806a5182a85a9f813f76e190,0x83b8bb8b5e120b85c12682909b00a8,-0x34f4323fe4d460679a1a09fea4460,0xbd874a2b5e4fcc2f101bd50e398,-0x11c6f8ef005bc2e0f1a5a543b0,0x5947bc5e65c5526a58b8ac8,0x42f1728f8050c354e00,-0x1d49a21ec8235575220,0xa5639380a66d2de0c0,-0x2df0fe4e671e53dae0,0x9abffa4b764b35680,-0x1736658b51be7b360,0x235f14a388c0bbc0,-0x19b9835fa9465a0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 23 41 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 41 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 53 indices rho q0 m0 0 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 53 indices rho q0 m0 0 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x22f3709e8a827df9080d80fa06aed04000,-0x495b0f95d9ecb9487328b724a729f5af000,0x4ad3e1f7a28ff499a9c35b1e9f9e54cd0000,-0x316ccda0f0d4f67141f1112ea2d674dec5c00,0x17c31e52b9e0eaef4484c510dcb5f5d76fd000,-0x8dcb1989c50ad8ddb0dd3dc82fef314ff05800,0x2ab1399676c36d45c498e5aa6371aee15eb5000,-0xaa9e08cdf2b58732fc8c2f3a912ddc390482300,0x240db81854ca69e872bda5340491ae9f3bfe6400,-0x68a613b08240e8094cd9c30142b7d529efadf600,0x107b9ee2c7f0e3e49dabafc9afd0d8af7d29be400,-0x246273c53362d93df9fffa28ef270534f74954900,0x46d7e68d03ae672cd7e19a3f07b5bf764222bc800,-0x7a58e924ab2a729536508157ecffb11fefba39400,0xbc3ee88a5dd070267e797834a62bebb77ec7eb800,-0x102f1fe18c4b76a732d81b105fb89f98e0b733b6c0,0x13f505112cb58d2d8f34764acd0cbb9018e238ed00,-0x161b29b3a090fae123f9b36aae6243eb039c615f80,0x1606cbeaa94719184792f8c1349ac9638d10345d00,-0x13c2688c782a56670018c7d66e6734df505efa1d40,0xff6c9104fcd0e254bf69797adf7feea3b737bc200,-0xb9d2a21c6c47615d84109b9eea93a04dcd182b500,0x79a6c192f96644b20b669709177464b25a0f35e00,-0x47951fbf76e97f90cb91814a6f730046776c9a6c0,0x25cb617d93cde5e14ca7855701911d2799d323b00,-0x11dd52e030dfe2c6885136515cef311ef35a8e680,0x789a55ccd3081d082eab31cfb5a357ddf8f85f00,-0x2d42a94294c45bf3485fa4ddf7617a0237097b40,0xf0a7e2ddfa90423fb719d2ab98b0c88f6404400,-0x4670cca7e13e53510f1fe8f498a8607b596d200,0x120ae91e353268ab1b8cbc0474a7dbbe344cc00,-0x4032ef97dacc296257e1fe9512418f8f3c1640,0xc4703dd8aef16c2d4b5255c479d51dc560300,-0x1fed724e3dd3f89d355d1e1ecd743833bdc80,0x458a6ca10cf7b2491e122a64b1c8c5207b00,-0x7c8b9cb58c012736bb45eb919a58cee8dc0,0xb31e46de4bb8cf35d9487821218fe38200,-0xc87dfbff0024e99cb3d3cd9ced50f3d00,0xa75e862f894cffc54454145c24f22e00,-0x620ddb0ba45c4fa7f6eb156aefca940,0x24c4d76deb73265a1106cf731d1100,-0x794976beab17cf7a9f3993e44780,0xa4ff46d6a7d5467c9af1cd8500,-0x2de73e897f8fe2113e1df4c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 23 42 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 42 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 53 indices rho q1 m1 1 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 53 indices rho q1 m1 1 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x4188732943b4ac32ef1951d4cc87c678000,0x87ed3b111341a6073928f1a7ad0d677ea000,-0x88fe929b2bc8458ea37e2540c9e953f4fe000,0x5961f66fbad3c4810332d07e77a1d1179ae800,-0x2a7000d32b9ee7a81e6be79b5241f0d852f9800,0xfa035d73a33feecf5d5fa59c54e031613513800,-0x4a4c703349d167f79be20d7d000c0324fbea2800,0x124fd91d65b5fc5bf648f9cf1206b5514c108f200,-0x3d129be5baa04b36750989cc8f19600db0379ee00,0xaeceff72e3e1d972709ee5d5964aa5544d6248600,-0x1b24705660ed37085dbb88199dff336af71bb0b200,0x3b0ad3b1114c39a18598234d687d38c740406b9c00,-0x713e7b2d9181da8480ce9405410eb21e7b21731c00,0xc0945faa5f11b4df9d62ceb86b241d16732df3bc00,-0x123a5f685c12cbe3f030048a0022992a350d9b1a400,0x18ab388b420157094810cee3dba974c31edeb7ee680,-0x1dea14ef2db883038ddec4ab760664a55f2822ff980,0x20918d982b05d70a85ea239d1c02e2c504c7ce3ff80,-0x1fe103a9fa3a9799939f3cf47b430d433fa0b304680,0x1c13c33aadd78cfbaac02703d4293c9f11f0ae25700,-0x1641eb55068f42a8a8b8392d878ae3e0bd89397cf00,0xfe09ef66b519e0241048e7bf54523a833870f14700,-0xa2f512a0f7d2cc8a427182595b8120d83e41ecb100,0x5de1cda0e5ee68193292220302136fdf16b1da2180,-0x307d8e197a3e5e5beebdd45042b89d94fca498f680,0x1666ba54af54ec1819ad3c2fe1a71198a6fbda4480,-0x93a81bc9acf367ff5fee4ceb0daa6ce7059886980,0x360b358e49be59f1a273b815dacc622c1efc72000,-0x117e97a3c10837fb2172e70751293e7b80b16ee00,0x4fb2e002dc8120707fc143408d429d51b702ee00,-0x13d3cc39e9885ed36da661900fba394df60f1200,0x44673f468265b5e7a74b7c5131556974305b980,-0xca896adc8bbb97e1c1139ceb7ab4bf7a560680,0x1fc851c87fa5789c7c093322d18449045e4880,-0x42a8ff43a682cd6c4cdc9ac42fa676e7cd980,0x729bddc2ddec5fcf2ee5c2b7eca0420e6300,-0x9da695bb3777b621190013a4b1548f7df00,0xa807345dac47cf0c4f8d2ec5f86c6ba700,-0x84d4624de305053b51ecd23a903732100,0x492e0d27e7f7347d96f10b57dd4e1c80,-0x1992ad70cb3e655a018dd5d18264b80,0x4daaebf70cbb927a23a51865b7d80,-0x5fb227c6fd7a61e99f8f94f3480,0x17976e6c60133e758d5cbd200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 23 43 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 43 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 53 indices rho q2 m2 2 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 53 indices rho q2 m2 2 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x7adfd7ed5ef2c2df804f796eff7e94210000,-0xfbef52d7b467968e6b6a9cb3be08d4b234000,0xfaf0742f0d913783e6232a29906106772a2000,-0xa1c4ffde7c20c4c252c9ce24b16a64edf91f000,0x4bde587ac4e2a75c1d016c4a43f02e61fc596800,-0x1b9656eb685dda16a26daaa8400a41824e2d68000,0x8180cffc2a80cd240d14c303ee2b359847f20a800,-0x1f80943266dbd66b219fe49f3a598954321d729c00,0x67aa319830751fff27ec2e64cc0ec9fff29e008200,-0x124ac911fcbdaa4d064a09260e7d0d513bf74c2d000,0x2ccef428d9e60f098af82dba2e7d7b13bed7f7ba200,-0x60134803a2bc9574ab368548a7744fb2c170d284800,0xb5912f08dfa321c46da81fb05711954dc4aa6bcb400,-0x1301c78e1e37474e261b0d2384c2c225694a289d9000,0x1c56b11b7b82ab10f41af260506ac3b8c1fcac0df400,-0x25bda489b62b7d99fd86ed32eb70e89a672b6ffb7300,0x2d03deb233acc8c1650bd4c8daea2b0cbc0f2b27a280,-0x302e3ba7abcfdecc2895ebd224a7d75ab24c2248a400,0x2e5684dbdfb6c688d91b9e84dac6000c04e10250f280,-0x2813a8b9ef0375d5db46a19cbb9cd791847f5d8ff200,0x1f2d9b3ce1e1220e5118961f4e5143197f21780bd500,-0x15cfe1df287f3979154f7b27f0d683b45a830ac2d400,0xdb63bcfe31b51f91f5a73fc0b3f3d315a1c663f5500,-0x7bc491f5b794ea9b59e8ed36c69bb2b5260ccffb900,0x3e8b7c139ee72141be330d7526a2abdf72e877dc180,-0x1c3e35a730fce962f064394d8f1e173fecf47a9a000,0xb5c7c1be61a58ff09ef5e1d2257a8b5bead2f6b180,-0x40e4c95e7078eea47a5d177ab0405b76d09e366400,0x14769a84b9137e890b283c4f99d6aa040f08e1aa00,-0x5aaf4f8afed25c6f0ab741b53dc477171aa6f3800,0x15e9608a79a253a6e4bda815424645bc013142a00,-0x494a3a57abc87227b447c2f189e5fcc87c84e500,0xd1f795a0cafb83b940d2c4e859123c4a30c0580,-0x1fce5018f897e099271f5ccc310f58b066c6400,0x403901a392f3a7f8064ac29e184f4928cad580,-0x69f75f7c4b5eea4a1c8a9ff8a5c2a79d9a200,0x8b5bdf3faa397a13b09a90afd73d78fb5500,-0x8d5c1875fd106a60ff151ec689fb784a400,0x69c0f59e4e7d8eb0176624ad01e4b2d500,-0x36bf5381b0022c9dd15344172c5f4f300,0x11d021c918f2cdb652d583b5152e2480,-0x31c37d3e30b734c24c163dc4b08800,0x377dbd5367cd4fe6d6010812d480,-0xc1ebdf7d40340839e539e3000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 23 44 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 44 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 53 indices rho q3 m3 3 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 53 indices rho q3 m3 3 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0xe663b4dd12072d63109503b01f0d55bde0000,0x1d3124abf61cce0f09fd7fc96f6a50298cc0000,-0x1cbe4a6d66cbfc4d1dcd6cfab5c3611619742000,0x12500f8ee52bd1379a468febdf70bd22b36f36000,-0x87c6235c5a4dc7eee63fb0984352ac4a86e1ee800,0x30c45e9a0b6c02d954531712aa083997f8d7891000,-0xe211a7b9cf87332aacf4b4b341b55c69785875e800,0x364a2f1bcf0f6fae2b397a3d8b2049f499117a8c800,-0xb050c2dccf4624969b26613cbfa0a38fa5d919e2200,0x1eb1e33da4242877978ca2916f9627ae694ed5e00400,-0x4a285b80a42e6c4594a8d634f88e6c084edade6e7200,0x9cc3a7c1707dcdaac2d2779f558951d3875d7b1ea000,-0x123f9c17b2d5d91e896b7cfabb9b7b8e5e5cb8dd1b400,0x1e1c591ce4c215a92d426b09a43e9479e79a8daad9800,-0x2c3548dafb06547f12ff336e1ea825b91603278c3f400,0x39f32565ebd4ac6accc97ba5a18383f63f79e5e8f0a00,-0x43ffeef0dfa0b77717c2de6eb66b91ba346e925546a80,0x4790d6fee091f3592155231cb0b1d6305a2c69028b500,-0x43a44e98411c5a9c4a17965d4899a19e70ffc7983b680,0x3975913757aacbb71702db11a5f769680bf34a1d01800,-0x2be056253de0a68a4495fd51e5d33c0638bbc9bf09500,0x1e1bd1f0aaee60ad33402a3c935b5094eaa16ad0fe600,-0x128d40d4a866b08bb88c68690c08985f5a15de2a7d500,0xa3ffd9da06b4d82ad2c907f7644dd5c4decd7d5ee200,-0x5118310ecfcae59eaae7c417581bab9b61bf1733b980,0x23cc547cb3d990db0fc54af3ac046de3278cb9f9d700,-0xe1011c7f09ab0c14ca36025623c62c20aa74e8da580,0x4e598ebb4e2131fc90d8c4c79ef3cfac8d146f5a000,-0x18117b578d405b41cd9b62cc7147aec9ed42e41aa00,0x67c1bffada45ca570fbe79fed4109569a3efbf5c00,-0x18593661410ef1284dcc59c121aed3452463dd0a00,0x4ef3f79cb7af9c0d1fbfcdbf0771c1bc83e36ce00,-0xdad42a3c665925ffd0d52c31fc81c5ea7b587d80,0x1ffe4205b25a747ca4d39ff952323a93cfe2a300,-0x3e2d8a712efeec2e41d4987a9d55216020d4180,0x626cbb546428d61b13e679acd07fb8455cc800,-0x7bb4169fefc18d194d2704a28b1bb62a29500,0x775bcd0786d14139dd28f7a207270924b600,-0x54736fe9cf3156682b2944b72201c80b500,0x290cc218b35baf04ab97b04d8acbad7e00,-0xc6cc5028c352930790e43942214dcc80,0x1fe66d8ba154cc7f59c4116c7942d00,-0x202ba95538dbe81a8095d5a4f6080,0x63971f3a5e86e2f6b3b9e08000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 23 45 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 45 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 53 indices rho q4 m4 4 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 53 indices rho q4 m4 4 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x1affaf31e81cd7519bf1766ea3a3900c4040000,-0x362242018a98b73cf4c6022e1d5ae76bdd388000,0x34b44757e3b8cb2f886ef54641ddc4ea13a12a000,-0x2131a72b0e65797da513dcc5929b63743f85c98000,0xf339bbb970a1132d3a1520a917d18dc66815ae8800,-0x5650d7a7375e141d5d0c0b0d842a224512b411a3000,0x18b3bd7775056803daa283966499ee8aca2023d32800,-0x5db9774e9d6b8baed2971cbf946223a13038285cf000,0x12c7a6c270fb3b18a385acd81d5789bd9df6d56720a00,-0x339f3a624160c2543acbfff4044a86690caa289c62c00,0x7b087a3c133919e6c51bc91c94c3f1936f6955186e200,-0x1007ace43cfec438c540be256b194fae0bb55ed1517000,0x1d6e59827d37aaf8258620c49a5cb35fc01afcf3f4e400,-0x2fda0991055c94b6006199a76d63b6d05bb54d8527a800,0x453275f996f2e8e50f5c8a0f6651deb711729f076ed400,-0x594c9e5e5e6431f8ee09bbf49950fe317a29d20278bc00,0x671c3614b65adac6f08d317110946d7ddab0423bdfec80,-0x6ab9edd36fe1c31273ffd141c0ab7c975b0711dfeb0700,0x63276dd81364b05be63a709817d019629b2ffa19bc0280,-0x52bdd6f770cb8e6214d9c4093cab1f45e1cc11b551ac00,0x3e06fb7097396ef642636e5ed291ef788a81f42595e100,-0x29c1d4ac5ee05a54ac956f42bd309be27dd33459cc8a00,0x1938e7bab7d54e04e66361fc4242f975fa4e211f27ed00,-0xda659595ba21e4b1c566f8890f4ed56bb4b78eed73000,0x69af5f9ca711b974017b95ca25e8df1cbc2a1e9c82f80,-0x2d9ca4d877332c3451b34be2bf687dc70ee0aa758f500,0x117fccb1b2f5466050caddab4b0b5da02672e05b2c980,-0x5f1adf42b4e72c70c80616fd2442291d79bd3f1d0800,0x1c76288e56abe45268aa1f42917af484e9cfe97d6200,-0x775b149440f700fd556e674af4e1064771f0df32400,0x1b33aeb6a3b0b11981427a6548c6e1f1fa9cfe6fa00,-0x55812f9e4b2acbd5af5a94b96ba68bc74752d01c00,0xe53ecbe6b90fa37e0a0bffe01f656b95eef822b80,-0x2057a55343966edf62071cee2090a5739055ab100,0x3c7be92c10ad21055e3677e180d40e11fab51580,-0x5bd2fba75688d51d00e5bd73c8a0bf8ccd01c00,0x6e3f225fe58e15039a2c7ca87aeef32cd48100,-0x65220a9e32f3a377345ee73dd201543d0da00,0x43a1acced54f57c6d3e4c128a2390d348d00,-0x1ed80ce1caa4fdf32c9c1cfc6be324d4800,0x8ad6b555c7d36cfb016e2a61ba3147e80,-0x14750b84bf9597b5973605f3d5604700,0x12a56aee2fe9488de5e1d15a7d2c80,-0x3320a4125dc9cb31bc64e0c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 23 46 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 46 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 53 indices rho q5 m5 5 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 53 indices rho q5 m5 5 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x329f687d933613b90464be0f72d2ae16f8780000,0x646950c548ad3f69aaa6a7c37b9be8f08b6bd8000,-0x60b00b63bcea3f8d5d4494342691a4d44f3ac62000,0x3c36852241fa6a4520faac1ed8175390d6252024000,-0x1b425f52add6bb35d65644cb445ed8c234f109686800,0x98f717b29a9bb41c29d64698d5718bd9a611feabb000,-0x2b4022d090787e03339ddaed4a3241d23ed2a3bcfa800,0xa2152f7a9fcbc82eb0d317000adc6bf1508ea8ddf6000,-0x20115509446c3150c6f1e7ed6137ff9565b5cc47500200,0x5701fd77211cf21fea223279faeff035e106a9c0f9cc00,-0xcc9e2986f137666a02d8cea2ef8eb18ca8da2dce7fe200,0x1a4bd61f34a0f09ab5ecaf35bccdfa7555a5ff2b7b20000,-0x2f9a733f0d3baa8fa0b0f33b45bca93573ef78fff290400,0x4c4829c48eed67d15678e6462a061a8509c5242a90cd800,-0x6cabdda61177fd144aed6860bb159d49effbda8c621a400,0x8a1836d1cfddf054c011b4439b4c44071516662be146800,-0x9cef17563c6e5f73b944bf2ee20df97962cc105ef69a280,0x9fc9ae4b7df58eeac9bed0db2f2661416015b38e0deaf00,-0x91f24cc14864032028369921806717ef6dafe15fae42280,0x77a950251dbcc6ee9a3d7f5c7c3e4020fcf7dabea4aa000,-0x581465ae0e1991bec2049f449105962da7903aec7bf1900,0x3a2e4940f323a4fc75e81b8e7a838de1aa59d4e84cda600,-0x227492c951c0f385796bef43f78bba24418b6b985fb7100,0x12444991e26ff58446d1a19ad23881364f48ac7847ed800,-0x8a6d06e4069ad8247199571477d923dd6c574300c61d80,0x3a6a144b5dab3a7622be4c7e72a842d11bfd90efdfb100,-0x15e3908617ee86533fc1354f496a97a23ef54dfcb06580,0x740d20358d235de8ddaec61088d1bb43e7d6d3f9e8000,-0x21d5be51fd142d5f79a1cf05d9ef7aa2963224df96200,0x8a06b6ba5ac40dc8cead4e1c12b12aeb7f7b5c44ac00,-0x1e8c98a7b30a5a67f00e52a0a0e835dbc891b843b200,0x5d1411aec1d30076675a441cfcbe1362997b18c1800,-0xf15df50885a9cfcddc4cb9c9c9c39941bb7b9b7d80,0x20da955280ff85f016844f10125fb4b1a07fc45100,-0x3b1b4726188c03754308373a467b05c70d11fad80,0x56080528ad4e4c0cad977fd7e3ff6b7b6a4c2000,-0x62a190f855c62716abbb367ecf66bd2e58c4900,0x55f993594f0de0c995245bcabd1571c9adc600,-0x364ec190725d01a41191065700276f2254100,0x17387eda5448e17d6de0afb2629e9857c800,-0x6112d19e2cc03b1d67e50f99fef2569080,0xd1f9120e6087cfb14c35172e47ed6300,-0xacdfcc32828f258f338a9099f01880,0x1a3d1a9f6dd00798d07325200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 23 47 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 47 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 53 indices rho q6 m6 6 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 53 indices rho q6 m6 6 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x5eeae3eb740564fae83ce45cf74b066b11e100000,-0xba4bed863efbdb1c7d6d9f38200bfc7e704fa98000,0xb176ecba1dab5fdf06ce022676d3a33e57cefdda000,-0x6d4e391062f35333762ebf5af7a7314d5134d921c000,0x30edd1765ba07e4f26afbc94bbe0609b462a67b304800,-0x10f6923f4d7f1dfc707a97035c442a222e802e057b7000,0x4bd66fe389095ea5ee85ba3c2d048e4f6373e36ce96800,-0x118c69a81df9b5c60fc74a2b25f9bac7a4a3c6228914000,0x36dd1040d8ef98d463646a03e21d4c08c25071f82e8fa00,-0x92f7d69ff51f0d36cb353d2848981ca5fe54d8951ffbc00,0x1551e76941ce7f70dbf6ce347c5e1a34c3230bc29dc43200,-0x2b402c3e377ac4d54c44e149530e727092959f01a91b5000,0x4d371e9b00ff05ea290e06e4a3d4031c1609e90168d0d400,-0x79f9d6fafc6765f39f95c035e5e3baf123fc277244f46800,0xab392749d288deed9246d36c52d7d88610a4a445f8e36400,-0xd64bee415c8feb5da1e1b5e8acf23e0a57f9cdfb2ac86000,0xefbbcb146accbc19f259e9518af2fc3463d0daf657537880,-0xf028540348615b46117d061f17624431387ac62619ad3b00,0xd7b19527476e942cfc3160eaa13b29135b9cba2eab28c680,-0xadc9dd8d3a900de9b8174b9df420940e68a9bf9a34406400,0x7da01cc56264b03b2afd28fdeff0845da9a1f554e1558d00,-0x516f0cb64e659712e8825d19aa44780fa8b42ee1598b1a00,0x2f4a2cef50492975d45a162341b30a28278f3686cfe6e100,-0x18903e55b5d8e6092cae913193ab5a7b14469013ef368c00,0xb634bf9effa9ca085f9d83d7378bcc9c5a95b61a94d0f80,-0x4b2fe8df494634a3d8b4ba7bac6beeb99a5aa1f8d652900,0x1b850be9f92ea635d817536d422cb6f26ae7f3d8bc65980,-0x8e57690f91ec89a979dba46fccdeb2f1f52df069407800,0x286e5f69d77499a03e744347363ccd966f64d4634faa00,-0xa0714408d85c3ade3a99882958c61708775ffbe596400,0x227bf45a4b18525b723ed3922cec86d9a793296d7f200,-0x65d546eb361aae36dbbf0fd00f162a5ac16edf6fb800,0xff5fc2cbfef6e54559b2ea39dd0e7921943c7d73780,-0x2187c3b7ff1430f11e17b19c5c19ebe70fd17638d00,0x3a045b1a28a5aacd899e5f1dea578999bae89e3980,-0x50ef5326aa19553b78b68d215776758dc1b83d400,0x5890759c031d0aa7cc1b82fe5b0858aa62bd9d00,-0x4951db9938926f54bbcb4d040fa115578428a00,0x2bb81ca1b81c622bef91624a19edffe5751100,-0x1183618328745d0c94d9f2510d8df72be5c00,0x43f0fcb24d052fddcc18df29406fe2b5680,-0x86bbb50b16eec278a2f2e47740249f300,0x64257ba99a816bbfcf711306dd02480,-0xd7610c8aa318f5ec1d84b3000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 23 48 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 48 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 53 indices rho q7 m7 7 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 53 indices rho q7 m7 7 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0xaa0e21ade5832af82bc00000,-0xee7082e8c2bea939f6ac0000,-0x9ea0f9555646fd7532200000,-0x42a271b616be135b4e54d000,-0x13d72ed2b5aa1429f8869c00,-0x474bb133c49d8c5f331b700,-0xc8c3b4dd2156316ca4a740,-0x1c6548d6327f08c131ec80,-0x348a94331d3eb7f7d1f10,-0x5072525113d8b144c9e0,-0x66c0212d623f2cd096c,-0x6e0894c822220c5f38,-0x630a1259c54f84a77,-0x4aef3a13e3756987,-0x2f8d4f8c304fbc9,-0x192fd2f011d8e4,-0xb0c45b790776,-0x3f76725409a,-0x12553f351e,-0x427d632c,-0xb5eff3,-0x15d37,-0x17d]
def m8 : List ℤ := raw_ints% [0x0,-0xb1f86b59798a1d5673722c2e4facac08c185e00000,0x159ba13609343f277f491dcfca0185970c45540f8000,-0x145e2814ba20aa79c3d12755db8e1616986aa7cc32000,0xc691ab6a05aed2cbfb2bcd09d316528e7b0f4f603c000,-0x57e905fe65249ea536b287207b4037e219e3312d82a800,0x1e2278e4b61c8a5831dbd5904020c6894b93434842db000,-0x852b795bf78545b821760971656c1120dba75377ac6e800,0x1e7347a669bd48a7bc9cae9c8e4248506bedcd52958bc000,-0x5e0b2a60058d0e03f227a8345ce74655ab1ed5f53bae1200,0xf8c7ec6ce61b3e1cddfcef872a01f0bd324ec303feca4c00,-0x23a06c9ee9efe1a5944eccf9a0a9d2170e15ae614c52ff200,0x47521412e6c9a55bf7ad8175239ccfc400a070323e9b80000,-0x7d996663fc8afcb6088d6714899b3e8b718ade6e484ac7400,0xc3a16c1ca5e010e597fc7e0e75220b8f65974ecedb5477800,-0x10ea6ca25f2346ef056be25b6968f55506297649701a837400,0x14db05a6ffa127eb65dda04bc03e987406615b44779abaa000,-0x16f8c308ba2c35923a13dae2706961a218374014c78c1d1680,0x16a544f758ad41a55fe199b15a99e18a02838c5548d2b64f00,-0x1400c2738e229fddf9f1db8a4e48c177b7dd57c6922a7fd680,0xfd73c12a52bca09ab58fb8e01c4cc3b5b68624dd26d502000,-0xb3f3cac7c6ae505bca5bb2f44e693fbb1684abe43acf9e500,0x727dcb1310bd6cdf8dcc7fc2449b8d1052b66ed014be2ee00,-0x413473712790adede7eb3d0419a3a8bf9ecd20e858225f500,0x212ffd692fbd1ab030a89e89c1598faf6fe5f83451f93a000,-0xf0ff2970a9ff051377772c1beb602f5058337f6830178580,0x6141186ed555107e8067a3987983e2eb5d4041774885f900,-0x22c5b7664cce5ee5aaf149c3bf44c960dd035a997abb5580,0xaf7839c187405bb8fdd8d14b286b1acc76228780c130000,-0x308ee6075fb3f3155645089d9806d8d635b1d8dcef7aa00,0xbb7106d633212503764f8ab3413f4e3642cae6732cdc00,-0x271ee48930704ee4670f111c525995dcf2a7602f820a00,0x6ff52cb451413b92069a2ba0eed434c52698fd3042000,-0x10f7af11538848bbbd45f3c04c4a48bbc4eb64cf08180,0x226075377e6ad182177c9f3d766ddd9988b6e7fcc100,-0x39312b8ba19c8e1654172a4986a746fec24ab178180,0x4c70f49647ff7115fc6dacb59fd6352f065da02000,-0x4fce28805f14f51491eda31fc73e97ba5bb664500,0x3eb71a6a0278305f65f7050a8ec5f2ba2836ae00,-0x234774126b28e9d6eb7ccfc8e4a5198c6cf9500,0xd3b10846c7317637fc9cac5fabbbffd12e000,-0x2f986f7fecaf2fda78e233151da146c5e080,0x5678cc5c68218da475e162de4b6a818b00,-0x39ffc10ab4323f482db2664924f85080,0x6e759b7b8a78ac1bdfab108000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 23 50 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 50 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 53 indices rho q8 m8 8 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 53 indices rho q8 m8 8 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x17d,0x1]
def r9 : List ℤ := raw_ints% [0xfd17081fce9436f3591cc00000,0x1623364b2bbf03eb04bf23c0000,0xeb27229118a4e88e31a2f40000,0x628d2242aa829bd16e62199000,0x1d449e3de24761ef1b92015c00,0x68de33cce043d8a70f876bf00,0x126568919de536ec8bddb3340,0x2979f9b1ec05b9d61aa85340,0x4c6bea02af5e673fc054e50,0x74717b3f78b59694be0850,0x93e4cc3b79fb35949125c,0x9d56c35b04c39dcd79bc,0x8c8574031acd33c8a63,0x6955684a1def45fcfc,0x42165bc3af548fdd6,0x228357ffee9e3a18,0xede46c5e89c33a,0x53670f27fb408,0x17519dcb5f3c,0x50a484f86c,0xccc8583b,0x15a182c,0x12d2a]
def m9 : List ℤ := raw_ints% [0x0,0x14db1c947c3e2f702187612d6d563c2906adb0400000,-0x281c01e3de4fea377839753cad1710dba224ba5898000,0x256b902a663d6c3dc9e3b3866d609ba424864e0dcaa000,-0x168fd19721ad503e8db1a49e7df2eeaf40d674b1b80c000,0x9e194c5e08e0248b4a930716557f70c5f8c0438b8d68800,-0x3598ecb1691df434f5e0424065ed8c2cbaf978697185f000,0xea2d8a881affe44bb2ed7d032e2cc3e3d4f2a6bbd9baa800,-0x34ecdeb419faf544197422d858ce752db503ebc1706b68000,0xa181f89bf30efd2dc48bfb5e812bdb9ae18ec51bb82280a00,-0x1a603ac2b5883209a628539bee49ad0e538c4499d37876dc00,0x3bac3ecf9d499bbdd7ba867d41e63065d15ce0619bd9ccc200,-0x75e887ecf6604162f3c321d4fd9aedd443b6a5581f2d14d000,0xccddc6450d47cda4b243458fb1103e1dd0334b65ba06e04400,-0x13ab1fe50caf88e3ae37fc435c2aff79e215951bdbdfe028800,0x1ad2dafcc313a7bacda0485d2777ddc0cc28bf59a850fd6b400,-0x2095b0dd1d465ef5fc663c97ba6003e4ec01dca753e6c953000,0x235850915a15cc4099a0e5a7687721198ea3633fa3aeba12c80,-0x224b4f745c177471c798729ae05eb782b61897e149c0d662300,0x1dcc1feaab07d2c4137155edba7a6366a33e8070bc2a05b1a80,-0x173268d791a7b17e25f13677f2933287aba9efec4b4bc278400,0x102df37e261c018687626f769fa9af67c27854e5f870f965900,-0xa1adaec22de7aba40082db7a5ebdc6e5c541016344da3a8200,0x5a50c54b4cfa271096046b71e2076487ebdeac91a563124500,-0x2d0c632082cd3112ba787ed887885ad77fc763fc23252a8c00,0x14046aad9546d75d5086d23d4d06e96fa966abf86b35567780,-0x7e687b8c744b94933cf9bd24dd6b6e18b50e562aca3a85900,0x2c26f33692edf5186ff495bc8fc803c514544f35f65b54980,-0xd960f715e1f11c40c97adcf7a9e7fc0c30d47bd600057800,0x3a9baf8ab76275954e03ee169344083ee5f72efac794f200,-0xdc10ba321d8f9b7edf4a7b2138dee60498b042bdc349400,0x2c98da63d0df96767d1e16752779471476469ab44728a00,-0x7bad52626bcf0945cc29ed22951be33fcccf141a2bc800,0x121f00d4c9e59e436b65fe4f1e66cb756c3d2bd4dd7b80,-0x236681853fad5bedccd37f3ba44008e824170310e1500,0x389cdcf9c3404608c39985988d4d6ed796248bc3ad80,-0x4878bc05e995c928d947ebaeb9822dd1967e528b400,0x4827b6c96d141743361ec016dd72e7970e292c9900,-0x35cc2b2831f8cea23dc9fb610a2164fbc50ca5200,0x1c883d289c1b7e59982f306466308cf54feac500,-0xa02ca08aed8437414943dcaa4eb55b1bc2bc00,0x215ea2c565faf5898fa893d7721d5b3b42680,-0x37818d7f34bbf28a30cb177d7df50d13300,0x2194865c5b45c704ffc60c86249939c80,-0x38a1d510310258ea5a435cc0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 23 52 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 52 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 53 indices rho q9 m9 9 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 53 indices rho q9 m9 9 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x12d2a,-0x17d,0x1]
def r10 : List ℤ := raw_ints% [-0xc80e83eafd62e10ad827ed800000,-0x117845159075b8c09f73197780000,-0xb93b182d8bb5af69b0dde7040000,-0x4d78c7372f849308f9e2ef862000,-0x16f4b6392b804500d6aaa9680800,-0x520b67e1128709c604fc851aa00,-0xe5a12886de7592b6687332f180,-0x204168b8b2a552b3cea76819c0,-0x3b37ef614b052efb2ed649560,-0x59dcdeeaaaad254ef51c4a70,-0x7199aad3d66ba06e7eac468,-0x7833d794016d30708e5174,-0x6aadab04e13a418f06dca,-0x4f5f3b48d1e98c75ab53,-0x315b9d334480c505dee,-0x197ff728141a32b9dc,-0xad708a45d220a844,-0x3bca7123c2b27e2,-0x105aea4a772a44,-0x36eacb744738,-0x85c955edf2,-0xd49a8c13,-0xa80086]
def m10 : List ℤ := raw_ints% [0x0,-0x271ad59668f498f23eddd6352d01b0ccec85aa7800000,0x4a78611aa07f210c50c164ff95c3e22a9233d37a038000,-0x44c82578685f6877250b25a3b9e2a357916317e4e942000,0x290b9d81604f0f2db9ea190a1e537a7f8ab2f80b8bffc000,-0x11c98698248213bc9b2986e740e685dc8c7da41273ff1e800,0x5f70b0ce121ee318ad889ba4681ca1671df09c357458d3000,-0x19c610621e466fa6cd2f5ab6545d78d4d4cb4810a717462800,0x5c2399c63b14fd558e7475395a5d1f74da8c1c6b27be6b4000,-0x115e2655dd0b07e143e2f4d207976cb66b7b4ac023e8de96200,0x2cd5d9d75697f40ca18dec2692743650a53519bc0f680a9ac00,-0x642dceffd7efdd20f8c494e2e12b04f250f193a2567ba590200,0xc36b17e5b4b4ca240bc9bfe3ddc1a7a50abc251405943448000,-0x14f1239fdedb5f6575784f62a5e3d38882393a46e8a5364ce400,0x1fbb5e8ea6e8fde143597a9c7059be1bf8f1ea6f0f998e5c9800,-0x2aab13be6dcfdf2ed78b476583e729e6b275afa4bba098cb4400,0x33147a993776f4e4b0b757729ec6d75a91f5db0860b8e4a94000,-0x3693047b8ef91d2e64f132c3619a89bb3cbc8c39accb76ee1a80,0x34207fd286d78e072546dbb78fc927c02a1ed921e33329a18700,-0x2c8f427a65af979737a7f1f1413a3297ba14f8704055ed61ca80,0x221b3c1909c79e2734fbfda259bbaa401337ea40e938067e8000,-0x175f6f98eba474ec7430b0c5dc07617ab4871a09a686e4777100,0xe54dc8089a3e7c9f91584ef23938bc3e5374dbc21d949129600,-0x7da7bab1194faab99d7fa825089054a21ad28468fe111f6f900,0x3d6db35595bef99098f39e5d1003a919d23683d8dbfd9873000,-0x1aba0aa7cf049391d1d112e97b0474c32b300422ec8e73dfd80,0xa5155b3b38ebecc1d4c0da200d25489ec6c4b048fcf7bb3900,-0x38550c3c41b71e3d805c7feb8c063c2319a426cc4732334580,0x10e9a7e4102c850455c142706a1f37cbec918d049d9b140000,-0x4714dc0fbbf4efa7ecdc223451c7bbd5e9e56a869c28ff200,0x1039d406628e0506ff931ae08f6dd6db56666d49f6d5a0c00,-0x33150a7dd941e29f18007658c33f05ac13f30c9953946200,0x894248b4797060843ac514f99c293dbbaca5e2cc0792000,-0x1370ae810536b2453c39fdc76c62309ea289f8eeefe3580,0x249c567fff087e61925abe040fee71cc16c00415cdb900,-0x384389966e2a2f8b02f9fe6e8aec228a9ca5d64149580,0x44f597bc7c939ddb0f365de2461ee3761885bcb5c000,-0x4172daae9d39b7d130269d8710717c810aef0eb8100,0x2e45d05248eab4c44b38b448fa579b32c3daec3600,-0x171fc0b92e9ff1ddb188b13302b95a0085b376900,0x795dfae49f26d10bf26f80e0f78292fdcdeb000,-0x1769af9802a2e1b2ef15e463d4511fd33aa080,0x23a202d5eca2f63f2fbcae3ae1636165bb00,-0x136fc218066a5403e88920dcaade950880,0x1d06ac8cf60c2308235555200000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 23 54 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 54 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 53 indices rho q10 m10 10 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 53 indices rho q10 m10 10 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0xa80086,0x12d2a,-0x17d,0x1]
def r11 : List ℤ := raw_ints% [0x6f999f1d843f1a558533e6e6800000,0x9bb24433b955921ccb9d0f30880000,0x67027256ea19e5f2079926a5480000,0x2b01826858e656ebffd8959960e000,0xcb7c855b28a63bf88ac6b86ef8800,0x2d5a8638051078b8e3992ba9dc200,0x7ea021497d63df46099cd7dde180,0x11bce5810e65069a90efe0eed980,0x2076f636899994de392769628a0,0x3117b12af76c52c73b8a7f2be0,0x3dd07d9faf2cb6f1f812eb718,0x411c408e96ec3b8b4f053148,0x397b9268f001db6d1c23bd6,0x2a824aa60608164589e7d0,0x1a3ee163fb948fed15973,0xd71b5cd853e86646fd0,0x5a8142cbf375fe6ae8,0x1eced936ba7644dc0,0x84b64b4116c4972,0x1b49c776cad9a8,0x40b3516c347a,0x630c9bc850,0x4a2e58ab]
def m11 : List ℤ := raw_ints% [0x0,0x4952507a04ca9ec635dff1a3b4632b803b7a9fa1000000,-0x8a4cb7a5ca5133e4e735e0024405eeb292164a88d858000,0x7e7c9adc4940f18c4d92ca800f77213a782e03e8bd87a000,-0x4ab94b630161e251e8091c3f98070d5a136c2a7d0a84ac000,0x200c7bd03b9205eb7b5f94c2584053e14578570c82e378c800,-0xaa257bc7ba0a5ee63ef71f92f59b6b0b89a0fc506277317000,0x2d7312bf48cd18b2f9ae0c1568c866c17043e145b6fc5c1e800,-0xa0aa7b11241b17b6d93d510556b8f2abe6f0833b4c0e16f8000,0x1defe978a52f85a95069731c618c4c0758feae4eef399fca1a00,-0x4c5ecbee9b116d36d5be80ab203538641698581dce7b95573c00,0xa88fec860afdf7ebaf667320228a1d90416c76271d5d8546d200,-0x144af526db909fcf00030c478337cb5225c59453372bf75fed000,0x225809f80a6273dc66af8dcb3a7bde84748367565b1ca864c3400,-0x3357a80fc0ab00897d25f0664d34f2472fa9990c45f25a4e32800,0x4414fa3bcd673953aa413e5c5338fb5b53bbfb541b142d0248400,-0x50560972c8069bf30495d0aa83de1fed0d12efbc476b8729cb000,0x548eb53f5e45ba8f9fa7649d1ed42b9d328cb2529d8ffa8e3a080,-0x4f858533910b597be459c78673db63475bf9769c6ec59d7259b00,0x42e3c3ae08cc365ddb24faa2281430474bf8d597c55127a304e80,-0x32589571ab820412da0f48c554213ad4b746d375caaf2fa84c400,0x21e750b1bc4401bedbd60b22b441b0c4568a4a7af2f6effdfc500,-0x1469a4698429d0ea586feca762077d6349bfd8ca7686e4a9b8a00,0xaf97463d5ad8671ab02f31b97ffa89eca61fb8f88b899edec900,-0x542451989dc0cbe61076457437b24ed3bd6e9973de5d17881c00,0x23d961de06b85f1a44b4ff8e49b8a8f6982d1d5f522c4355ff80,-0xd89946df8f329e22ced3d0a4ef4692e4f9c9e81a30e20537900,0x48363d0558031f3f8d0b9ad750580fc43ab5724ddef2b7ef980,-0x15275f375f0521d9b4ef14bf2719861c57be225e906cc29b800,0x569e779b4c79677270a6a7e3a40abd3f8d93e5f4a8adbcfa00,-0x133b72487d66287544e66e054bb9349d4f5ceeec4686a70400,0x3ac83d705fb57d790382eae40349bbc99310e874b784be200,-0x9905d4d6d848fbe150d8727aa293aa1be97d4ddedc8ba800,0x14f244fc70a8f9219f88d4116a6f0232ab2cc51c76f6bf80,-0x2604fe61e70f75dd859da08c378d8f9a0eb50ef0cf10d00,0x382220aea0e12e7de2012bb02aff485a62f76c67af8180,-0x41d909b1531267aa51c32e0e90755b681596ccc5eb400,0x3b8c5dc211319cdb55a4d9d3470f7f9f48269211b500,-0x27e703b523cf6de1d4b46523f167810bb39ef0fba00,0x12c71fd005ee52b3080e9bcb487b3f13e6710a1900,-0x5c1526092e113e03eae9b3356d5e044327a94c00,0x106ffdd6e12448a6592c64eeb13b507ca921680,-0x16e0583bc56641375182efb9404949b324300,0xb3f2c836574304550ee4b85ece39b79480,-0xedf5676bd9f875fed42dc3000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 23 56 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 56 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 53 indices rho q11 m11 11 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 53 indices rho q11 m11 11 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r12 : List ℤ := raw_ints% [-0x3146df2cc49b6e0adaa05f4f39400000,-0x44a81705a2c1507e73b9cd83fe640000,-0x2d5b8dac8fc8921c574c3b344ad80000,-0x12e802b113f97a4c74a34f2134def000,-0x594c99022db9d3ea4eb9e29b6295400,-0x13dd4cff177361d142d3d3be42db500,-0x375742984bf3b365a074b7fe5bf5c0,-0x7bbcaf58049afeb8af8fadcc71800,-0xe1dc398123fa23b204a77f326630,-0x15482ccfda5d764ae8385b80e300,-0x1ab4a8a112d50c9f186dc203cc4,-0x1c055ecf0dc69808cb091ee100,-0x18a11361f4367e82c3fe331b5,-0x121efe93f07567f2513af60f,-0xb1f503107b2354119951fb,-0x5a8743624aff4349212f4,-0x25c70dc37854e4418682,-0xcbba89d3becc525f0a,-0x3630fbc61e4c4189a,-0xaf9e4727d4165d4,-0x19875def153ce9,-0x261b97f0911f,-0x1b94819397]
def m12 : List ℤ := raw_ints% [0x0,-0x897a56e4c8fbe9b3a503e512f239f1906f85eb4de000000,0x100e5cb32dc9b650c3a256ccbc3de2d95cdd61227f5df8000,-0xe8b5fdcdc32182829c0f0f7858541524f268bb116a2dd2000,0x8821419be1fbf6e088d1a711bf3916a46b6e8e67c35355c000,-0x39cc4cea5efcad29154e264d743056c0e85402e250b6e172800,0x12fad14bb24ec175a8afad4511536dcb285a3689793c4dbeb000,-0x50416b714e2543b9f25487c94c82546381d7432bfb0b1baf6800,0x1189a809d39d71a0ae3fb5b812b04d4d0b77fde1954fc6f374000,-0x33b24d8532ac1cf5a95b56fcddfa6d094041f5097cf3c237a3200,0x8259381df2593e8a800f4d8b68d96691ebc0da9a86a68687f8c00,-0x11c423c498dd48349e4e11662d28b4ffa7d66ef3b6c08300729200,0x21cc7341fedd886f203f1e517583f8212bf3eb7f2fef62e2b70000,-0x3878c4b871b215720762cd4ce512b4377c48beec1c84420f87d400,0x534f1bef7359c1eff9a5c2fe7b6ecdad0b77d6562e8fb0c76eb800,-0x6cf6875108cc45cf4a3d3f9df241e98e3cdf0171fc0b6d260a9400,0x7ec1d586aa0e13993bb9acd3b76d4b84bb2a1f65c5d23d636f8000,-0x83760172169a6f3fcff111e04ab65a40fdaec7448ffcbd512efe80,0x79bfabbbc9011e1c6dbcfa742ee807d688a285511c67e46c9cdf00,-0x64c9935517aba90a2d2534c9610a8f4dfb6c1a668c05924c0b5e80,0x4a9befe0664b33b99919325ca6fe058f44d8933bd3314b65e16000,-0x3160fd321581bbfe60d3d9b6d085198af7e5d659dd7c9a1b3e1d00,0x1d323e689dee75f930d87086b58044165084a0c902926cf9b57e00,-0xf66e5b98ad39ab8321c6df894294b81eaf440b43a0cc68e595d00,0x73c37e64d5b0e4cf05f4babadecd5f0f8b98f49474643273c6000,-0x304d68d080f2c678a4416d08eb439a2344dbd02b9fa61a0ee3580,0x11d7e28845c73229899b213d13a0e13d2244a698910cd645ed900,-0x5cff2ad7beafdf10074f0df36250b6c4e02e0e85004802bc7580,0x1a94e0fc9dec53dfdb2192620ff229e5f26d4f26d6c0063f0000,-0x6a0b299d9d805cd6bc631105d149956333fbb81d5e30846fa00,0x16e69006f19998d2a97740b50635f29b346dfb4a823736fbc00,-0x43f313c4b9e678a9b174e823a4d51a44fac0ebe3efd5d6fa00,0xab599d062fe5b5fe93fb0fd2427aadd8bfa70e6dbd87b0000,-0x16aa4204000b3303873dab21542c4877f8c9dbe8bcb454980,0x27a428eea78db520dc53634f7b2913efc30c0ddd5bfd9100,-0x38364c5569461fdfb764fe288a7eca87b498e3eb095c980,0x3f16b8de8687b5af9ed1d8471c24e470b2fe963980e000,-0x3656ce473aef2493616782bb42dddd8de629919c25d00,0x227e14f4340dbceb007ed92b6b9fc288efaf80befe00,-0xf46ca5041a21a5b6091100d88d2e2bde72db2a1d00,0x45f2afaafe24bec6db48459e77bdc1a5585c3e000,-0xb8bf8ff0729ec34509e56cb148257614e3ce080,0xeafdc54cdbe5de6524c12d15f9283fdc60b00,-0x68182d1aa7da3c57ced38988111d43e4080,0x79e3aea6a067be714acb608000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 23 58 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 58 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 53 indices rho q12 m12 12 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 53 indices rho q12 m12 12 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r13 : List ℤ := raw_ints% [0x125223cbf921d2bc796fa3e5410e400000,0x197ee8ab378ce9a6194bf677320a340000,0x10d2578fb170bc010bf618c084f27c0000,0x7006e148afd4772f4052c0e9e6c9eb000,0x2104c5f78c1fa2116ff49315a4a1b1400,0x7550af0244c0b621a4b380177f3e9d00,0x146346064dd3df62f60f8eb7043ab1c0,0x2d7d059837924116478a8c3cd6409c0,0x52d5ba7d8dc832b51b1bd415ec6a70,0x7c8dd449f66e81b367c9658a68bf0,0x9bd5bc80799eb86f1f16cb07c334,0xa2f71ced0ef4c6a84ced3668db4,0x8eb2df64f7608619dcfc2b33b1,0x688a2254f6dc0d07644d15b84,0x3fd8d3e3e40804bd5f80db28,0x204b2a2810c1dc4ab065148,0xd62cca81a2d5492230a26,0x479deb7bf872d34570b8,0x12de86e9ecdb8f33438,0x3c71b63f67d21f844,0x8a931fc337a7fc1,0xcb1dc01c199d4,0x8f8e9405fa4]
def m13 : List ℤ := raw_ints% [0x0,0x101c562ecf8d85630d5674d83862ca4eed11b193204000000,-0x1dd4ea52e1fed0e412ca8e9e7af171ee58a8da1a64b6d18000,0x1ac5659494417d4ce9228908700eff60f2c4bfc46bb6e0ca000,-0xf82aa99f810eafc9ce8122f9b075aa064635b7cec7e58b0c000,0x6854618d39aad745edf9497d10d390923819c2eda986dd850800,-0x21e9c09245f9e521c656f00de0cd2bd62dbcd42187f55e04cf000,0x8de8562f13bf18fc6d0cf5f779e9edda10fd81b362d58851b2800,-0x1ead7877d9fdb20d2dcf658035c6d5a21a98d19aec6bc9eba78000,0x596e23e0dbf3c28427cfc1d5b4bef93e6198335028a4f3eb0eaa00,-0xdeebfd84725cd1df83a5c3af3ad514a0331f273b0803ab6d5b9c00,0x1e06c1e30a517e46eb7e1c55bfe0f152938772b59f5866ab7176200,-0x386dc9354a8767db602ca957ba4c011e7854688efe1f21f9a7ed000,0x5d195b5b7307e12624e5000a5f73ae9adf2e87094e3105cfe20a400,-0x878ee16c8b86fc8ae030edae7cb991b486a34460b5fa1d042a8c800,0xaeea3c7207778e705dd407a66ebb7727aeab0fcb6df8699c327d400,-0xc8a3a1ac9bc5bf880140ac19dc0ab88b8e062f6f7db423d67a8f000,0xcd11c020c23ba2d0a6b1435c0a683a506ba5d7f3a00178dfcf63480,-0xbb0ef5c36a4e02c5360087aee22e814280f65afb2f0366b02161300,0x986cea07bc27736ef0834b62e299aa946f81566e3f7520eb65ca280,-0x6efdd1632d4d4481b623270f704b301cdee52f596eb75be1ad58400,0x483495290a60fda3abfa91432e758b4808752313029adaef501d100,-0x29ee92626e7f43576bb52705539fcbb9da9896ce8240920fe0ed200,0x15b51ed4d629ef600784bcdc25734aed7de7c2806e18692f80e2d00,-0x9ff6560b50cfd9b862792d104de22d5c96dc89c5a8ff90be886c00,0x415eca82b2cc59c0a9faed9ee0aade563b54bec23e62ed32970780,-0x179fe7402d6f69b9c1ee286a9972173375f75f39dd0b0eaf5fd900,0x784ef46ea63603d7d065f94f7fe28457a9a7b372b4f993d02e980,-0x218debe30dc7752d38d314676efa5d4d250a7f986e12ee47ef800,0x826a3ba10d5d0c12f2871b052a855f59b3eea80fa036c3f2c200,-0x1b6443537f3be295bc1f353d420289afc252694e4a6f90def400,0x4ee4db154761f96385fed96e16e5a6377374873d87a50da7a00,-0xc0b269f49ab5e7edab2313d12a7f117c51237393555033c800,0x18a03b61b467d99e5f76e1a8ad76a58bd1c2c3df12d49d2380,-0x297e37aa3288fa3dafe19dd5e131086f8f38bbf55aef58500,0x387e5c2ea36ff47ac5b57df7382f1eb36af3c67fe304f580,-0x3ca416d835339a2d9101ad5dd48e1860dbdd784297a3400,0x31b975d2458b573899f1a3e0d0d98718febd5a50c7f100,-0x1de266dd873d39a577aa488078d0c4b0bef0b23886200,0xc730a8f8c1df2a87acc4a40ca5482be1d79eb97cd00,-0x35313cb5a6c4e5b1c738c0e9906b313a759b651c00,0x81d7da075f7f7b996dd7108b57f304a27f64c680,-0x96ddaad34afbd7c222ad481ea6b616cc8b9300,0x3c32854f5ac984a14a3fc7a005e86fb40c80,-0x3e6ad182f9398b3b17b968c0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 23 60 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 60 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 53 indices rho q13 m13 13 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 53 indices rho q13 m13 13 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r14 : List ℤ := raw_ints% [-0x5f5c9afaf5a51544041b4d64f3847000000,-0x8490832a7f49043787479ed3d6acbf00000,-0x575c55bf0969c4a211ee87e0d7bf24c0000,-0x2450b4ae46aa87db4149ea2ce8eb5094000,-0xab0391b4155c5cccbeae3c3521bd814000,-0x25eab0d229673852ba892d76b1b4a72800,-0x694017bb889f472da509d1a46444d4800,-0xea62fe8dffffe3867135eb51e6845040,-0x1a9edbae95f606c2e12ed676a14acc80,-0x27ef4e4112a8c6ec34ee26d67240d10,-0x31d5af3f9b075a884bf39a7b0d4340,-0x33f6b7b5d242a93ecdc61514e02ec,-0x2d5a574ba58e7530bc24d0ff0188,-0x211a2f811d7726236efb825896b,-0x1421c92b69c2148495a2514da0,-0xa2230b0a458b0d97524c9dcc,-0x42d4f942af33e3b2fa46e50,-0x1633ba6538ef1fa7848cf2,-0x5ce03be82cbd4103c640,-0x126c7caf3f148ed4450,-0x29c4bccb6f3401b68,-0x3c61defc6d21f4b,-0x29f0a2921a920]
def m14 : List ℤ := raw_ints% [0x0,-0x1e352197c5295a19b9021b1569b93b53fc812cf3dc78000000,0x37705108b3c020b28c713aec9da0033035564c261688cbb8000,-0x314c4ae20679231f570a9b4c91ae670c2c07f1316b64e16e2000,0x1c4b6d40e8534c847e930b9d2446cf10d957c7340fe972043c000,-0xbc7d790be9e8fa74e9a51dd06b0f6aab48ea6d66ac95586866800,0x3ca9cc7d60959f5a13eeaccc9eef4ac062e76a2c8d74ac56b43000,-0xfb40dd60b677d2fa0b1a71806e1e3be38a5be6aa2edafc069aa800,0x35bec247168e198c95864307279758b3e8d0c2af83738a4f3554000,-0x9afa43f1cafab17896ee3bfb032abb5eca1a830c1fa3d1714e58200,0x17dfd4bee02c67e8fcc0ac4f476a3445fce9cb6252990fc3fff26c00,-0x32db7fbdf4bdda22e7e96ad62059ba7a5e595fb4e31850e8910ea200,0x5e6f5b4d7476624f07b5f6edf603cff0b21531c4f3cb941034b98000,-0x99e0a162dcfcbd347ed175e90ce2ae2fbdc75bb859353d71ce4f4400,0xdd2fca4d5f232b9f4ce4686ab29426b0698f8d2d9321dcde1b53d800,-0x1199d964c75b3a849cd294fc3875972e6654571fa3b3843320e936400,0x13e94c008b80a7a805662766dfee4b49caf6836579aa47a363bc24000,-0x140f4116e32daf3523201999af5424cce79b935bffadf8442f2de0280,0x120675068c4bdbfbb15acfd758a63f6f87ed7b9bfdfa726b943ac7700,-0xe75c320c1ea8f4fe93cf52ed8bd74110fb0d38270f75f863ea2b1280,0xa5bdf0454df8a507734712f8e9cc9d5150db8407c4f5de9a1e364000,-0x69ffe35f29c394a31a2d22fb33bd7d6341b9677155c9dc3d8df26900,0x3c77bad2f6bda8367fc7998acd26fc89fea2076f6980664b91162600,-0x1eb8edaae4b254f50b71f97825067787cd611dc21db33ddd8357a100,0xddfb2eb376ea8983f4b3b54e08f57f83c5fedbdaedc0585f5fb9000,-0x58dacff852e2c92570cd2d602362afaf2307d12853eeab35ad8ed80,0x1f6ad72e86666a75ec359b77959ce2580cbb32d3a3dcc48ab757900,-0x9c55ba1a1ecfac50f152790c536f820895e8de57ca5dcbd2cde580,0x2a8baf6e12c3b3d42b15a1ae829ff3fd67e84cfbe0b068e9ac0000,-0xa11a0e1147fdf142998a7c31557e53c4a3639df296e4c1dc1c200,0x20e85d3c2287d7cc6147c5b85cb6dd5ada6a27828ecd347ddec00,-0x5bff1a65db464ea4dd5fb42213d77c343c41efebeaef3524d200,0xd99c1e72183b7c49d8f2bd58abb8f64518138e03f38273b6000,-0x1add0d7b98258148355a7b9969379679efd1909ae6ce8f97d80,0x2b984d37629aaccfb0a33ecbb7fb4bf6d8a05ceeae8925a900,-0x38f93472d6476728962c973e7900579924c418400fa2b9d80,0x3a7815a8e224b69c34413dd9d20cc4b7369877e0a9040000,-0x2d9f836f3fc56d98182b0c379f2067f923414d26f6b5900,0x19f2a7773c28bb832144ed15bbefd5a0d22f874a4c8600,-0xa29612e927bdee7fac3b66565979264d8f2bd4083100,0x287da7123ad3fa4c95973e3aadc798f78480d6e1000,-0x5b4b3e544a043b69902e87411cb2454429474e080,0x60da43624246fcb9ce4b85161147ba14621db00,-0x22cd2a52117a4213ded742b7256b9acabf880,0x1ff42434f8c790c386034d200000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 23 62 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 62 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 53 indices rho q14 m14 14 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 53 indices rho q14 m14 14 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r15 : List ℤ := raw_ints% [0x1bdc1ca26bced8becc268864297a738000000,0x26b0c9424e32d435af2e51068740a1a800000,0x19785311a65ffc8629adf72a7657298100000,0xa934a7bd8d4edf5bbe22e4dc72e2a59e0000,0x31bcc2074c518c11b463384c1c1754c64000,0xb03200c4da45dee31dd0f2b06e01184a000,0x1e8563e243f71064ba7f47898b761970000,0x43da98f282aa17e73bf97831abd390c800,0x7b132063fdf5e1db6d1ffa90233b121c0,0xb83ffb78074adb92699bd3109fe76f80,0xe5665cb8759828cd4c15898396cfc70,0xee972cbc9e113ca01d94845ae14dc0,0xcfa49cb1d819ca8f6026353ce6af4,0x9711ab5124b9e599e7bfd5d27b58,0x5b8b172a9799f7317ba0e12ebb5,0x2de390b29a78634b7fbdb81600,0x12d36aa5f7390029bc58aa6f4,0x638517a1dc6cc3927e81270,0x19dab3402f993d50a692ce,0x517222bd24e4d4f51600,0xb700213b2dc8f19d10,0x105b45d38364f40f8,0xb35e686fa39455]
def m15 : List ℤ := raw_ints% [0x0,0x38a39efc91ad88f03ae3f2c8263b4f3d797234493d610000000,-0x670c967a6acc7eab4e052899ef6d8291c3606396c0d3233d8000,0x5ad212124a356f3d94dd6b8b4bc5916d1b7fa4105bec7f579a000,-0x33a66bea96aefb33a76111872150f8f4f0cff765cdc04a2c76c000,0x154d6f90e2494ebe8a684cf9df1b7d95d268eda1c7da17f2f034800,-0x6ca1d799ae521c05974fd299e91f69d056fcf130c7be1a531747000,0x1bd6fa192b6edb185f14c396228aff1496f6b7d44d2015860c466800,-0x5e4d096b58defba90448dd5f5becd09c0a760db7ae747bd7bbcb8000,0x10d0819706fa07758d6b49f579bf74f4c19e5a6a2b7159f7126c7ba00,-0x28fd3d5258d6332f940000fd6ed599363a7bb8e07085c5a239fa6fc00,0x56530688321b4f0212df4265bec2d2ef1c147b06484141f5b69a67200,-0x9e68a15f847a00f6a1f81956d69f4efe7dd0f59750272157a6942d000,0xfefa9398004633ec65da50b5ce0ff996d55fb739c19d60481a1d19400,-0x169e36932d441881c96b7502062ef58184b15b0ac4e579a531e13d6800,0x1c6b9ac5cc755c1812bd388be7294a87f41c0ff893f76912dd5fe8a400,-0x1fb6abad3cf469a3e7b9918e2936e4f77d63531706fcc8ee9972523000,0x1f7f6ab4359049cc4ac87db36bb33e78b27efd728ebbed44c5a0576880,-0x1be2e81e06442ab3fb78424d99e0d1cea3e155010c2df3737fe9374b00,0x1606ea0864e9e803156bc8c056673294825bc153eea9c9615c8a121680,-0xf86cc66db72ee9b83afa75449508c5fe15cd65ae047f30ec00d0d4400,0x9c3691975cee44da050118b6865103d9af39efe9d5b5bea097e217d00,-0x578bb76ecdd5af8c7cb2ab8b4de50fd800c510f77532440a342deda00,0x2ba8e272ab8c8295bf83df0bc5331030f3d2087cdeb6cde86f06a7100,-0x135573386332b23e7b02db5434eafdfc377431d90ad8f59edf9fe3c00,0x794b0e1fe6a5ae5601d2f5e06e2400487f544f0ee7896436826b0f80,-0x29f639fe52ec7fc953f77472c461ef822c8afb59898515f77584b900,0xcc09ae353f3243c6e99f943b4a8867b1e317553a03c3439ea451980,-0x362ebb4ff98d6a9137093ae77fb4a7c3303f7a2026d9e4a7f003800,0xc7e0706a32518c1f4739ae40dde36149ddbad5ee4ebd84c8704a00,-0x27b4624ea937aa68beb30dc68b7e3969cc4ae5503b18627fa56400,0x6bba060c50515d88b519cc543ac4c97d6f735285b01f5366a5200,-0xf6be8eb9cc596139328109bb59feafdbfb53a77a21cfc7d1e800,0x1d6b1290479372d4be93679587aee57e4a050be7ca779a022780,-0x2df86010c0e82474010e453e7ba3ef5c9eb25e8cfda5649bd00,0x39a64074a30dcf82c780698d25fbcf07b7a4d3835e7bce0980,-0x388aeaca83b49a7174c03cff89ff98a362d1fa70e9f82b400,0x29f75ea0dcd16c16128d0d73eb8402e488355f6babc44d00,-0x1693674c3e0745d0436c9b1bdb9bc01058d2c599412ca00,0x84e7e2537373c4682a90c0225a45ffda9d0c14235e100,-0x1ed9a8e511150c3827c59877848139fba867ac086c00,0x40367d05a0b6dc5fa9ddf97086fc382d135148b680,-0x3e2c3e52f115c621a44fabaca7397347818ce300,0x141d0b6eda8d83c30c279742735ab893810480,-0x105a8f020e4d28872093513000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 23 64 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 64 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 53 indices rho q15 m15 15 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 53 indices rho q15 m15 15 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r16 : List ℤ := raw_ints% [-0x7726981cdbcdc4ecfde5b54660d8f186c00000,-0xa552d8545b390264e1729f9c9dbeb71f1c0000,-0x6cba0194a6395390d5efceef0c3f3a0a200000,-0x2d18a3260592932d427a4f4e93f757e2591000,-0xd3d9230dad7baa4ef695041b77e140543cc00,-0x2ed86ba7a614a0d3cbb575a6c0d3bad878300,-0x81a7c12dc87b55a9baba7c5c2db36f97e840,-0x11fcf475e75c777da0ff38b36136b6368680,-0x20929c6235eaaa22c65a43d3cdc8e1fc850,-0x30ac6854313078e4db533a58c316a132a0,-0x3c7a3bf246589abc29b9a85d5b3eca3dc,-0x3ec22e468286867112685be0b5e81378,-0x367b1e23013a20ef766d067a01bfa43,-0x27869e3a0a755ac582d7a480886627,-0x17e03d33e91ff612e68410cbc17dd,-0xbed08e57de437e0e7a8b036b8e4,-0x4df6ecf77fea6391c06029b1ae,-0x19a3d4a9aa7372001358dad1a,-0x6a01e53e9169cc5df057d36,-0x14bdeb7efa5d1800c527ec,-0x2e43d15f6283c5d48a6f,-0x4196a70c02f0e28c57,-0x2c7bcb0e5becf421]
def m16 : List ℤ := raw_ints% [0x0,-0x6a32ca19912560c26e6b673747af349343b622095315e0000000,0xbf96b77fd6f323f8e66a3777833606a3ab3028727675ad9f78000,-0xa763a12ce374a48e02795ecdc74355616f8eec75c2713f76c72000,0x5e585c75cd3277fb9c7a9f2e40ca62966363c05db8ee7518e41c000,-0x268dc16a0226fff5dee7204b249e2d9110d77b3e91357d041c9fa800,0xc2bdc66bfe3ae49261a96004738422042c83af0a169479bbff15b000,-0x316b5b8a34f4753eeb0cc7ca3b183738d9c1ea6705c4079ef6ff7e800,0xa5b50e7dac9e44dded5687cbf0c1490bb635df9aab9fa43be8ddb4000,-0x1d3d13867583215a827cbe8425dba63826b4648e65df420e2c90035200,0x4681e50085b13dddf07c0902bfad3ee5dfb17ab6342b88be113af44c00,-0x92d56fd36519e083b20b45272b3f31c7dc76bd701e8ad56bfc9fa93200,0x10a552c62563322a624194f9904e70beb997e1f93d10e0e2866e9840000,-0x1a78fab08a577ff6ee0af5c370826ce9cc982fc1b18d8a541c8d1bf3400,0x251aeee6c06fa4aa4af10c5bb5c3774d48c858b948787aa4a4e4bcbf800,-0x2e05a2ea8709bc58d7cc6ba06c5ea4a99f798707f26bbde493ab0c9b400,0x32aa53167255351390807e059bf986222b39290652c108d525a53650000,-0x319df89e3e6e26ec2d49917799668b6f4835a3cc7e38380ac97a9b12680,0x2b49bf9282d0b581685658db4d5423dcd1e6725342014744db51eeecf00,-0x21ac2686392bd2423d98ae501c58ab061525dfcda639ab865c603b3e680,0x175b9c4baa5d253cac670c73e444c1f3f78935344240b207d499c172000,-0xe717745216ffeb20d37b007ee98b862800bdbc92f8976544bbafff5500,0x7f3f9a7c25ffe95a6f34c9dbf9948d69f58aab7cea32d7b34f1fd08e00,-0x3e4bba834cbb7ce4808d79e862997a67a2453980b82ed88127d59ec500,0x1b0dca9c6800d0a1bfb12ff4568ac4e425c0621da98a9d228b6e1e4000,-0xa6454a364052852e157845896beaf4852df946498d1f1b172ce052580,0x3848b8da6631dc7411a4f05ea6596222e6e9025c99123f57630a19900,-0x10b705d04cb837e4620123764b5a2c168a04c928c4cf8c0aa8f799580,0x454c6ebc2aaad1ebd72e98a15e388436ef0cd6e6de49ff2396830000,-0xf90ad18054e3cdc2a1c77246f80bd266d7544d7c2163d312dba4a00,0x301b601d18fad7a484f001d1e9b1485fa41ef5f3a13722129809c00,-0x7eaa18c00203308d3ab740b4674236d66bf96b8d617f48ef3bea00,0x118e36a8c27213bdea91855fc4072d0d08afc2675e8a092f50c000,-0x2056643a05a383480977ebe87e3c6c98ce50c93e39c7141fed180,0x30a550e06f71e8415c0d95c4bdca6b972aa75c1d21d52fc98100,-0x3a85681579af5558af7b0b1c48b6b9e24fd91e33789bb2d1180,0x36d5dcbb35e9c229cb6dd3d3abb7f7bdc61e885a0cad2d2000,-0x26b21adf9606791a01c4331a6d8eb5fc804a97b1a5d957500,0x13adfaf31557c8dabdac5988c4d0ea317a6db7eb9534ce00,-0x6ccb0f542c6f6ea868a2457adad0fdf927fae73e82a500,0x178639b34372d7072605f5aca4baa0470ae4d10b3c000,-0x2d2dc63f674e8da8e962a7fea64fe9870f22499a080,0x27e82f8bfea7a6e70c7c46e7a903e095c1b62ab00,-0xb9eff65c668953e319e88a30e08a1ebf163080,0x85e158bba05419f6f51ad08000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 23 66 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 66 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 53 indices rho q16 m16 16 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 53 indices rho q16 m16 16 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r17 : List ℤ := raw_ints% [0x1d8ca976d08afb151dd274e113b2a8b0a3c00000,0x28f77d176206f5b793f36e3f0b04c133356c0000,0x1aeb0d2cadf3c90b9aa52dae9ab836aad7040000,0xb276a70e6ba67095e827b0df07f0253a50ed000,0x3457b894f76721f3f1a3fd102aa207d43b10c00,0xb8fa33d013eb3a846c14c5c02dff1d6a90cb00,0x1ff531a1e0cf2d8c1afdd1d196bf6e321b0c40,0x46d7bf38a4dbc4dba74d642bdd2a893419440,0x8016a73751694cf1d08fdf49c9eb4d45ba90,0xbf1631c836901c0207d416ff09a42727690,0xecfeefe9854529dcd3b89e3b54104afccc,0xf570b39b79996512c3e7f3f120ef4fd6c,0xd497ca861d1af14ec0c9855684ee3a5f,0x99da87a0d70e0028966ca31ad18874c,0x5cade658f603040f2a2e440d155d5a,0x2e26263ccceb191350f544eb805f8,0x12ca31bf9fde07e41fc54916e4d2,0x6279e92997041dfaba9a4c82e8,0x1954b7e689122c994450133b4,0x4ee2fc4be762e57f6cabedc,0xaee335584d72eb32c7027,0xf62a3947cfcc8a6adbc,0xa58aa937ffa9a2ffe]
def m17 : List ℤ := raw_ints% [0x0,0xc71f3aeff026156c8f096187a66882941ef57fd17bc9040000000,-0x16446fd4361ad9e2ba682248d90290ec0294802b3c1846679098000,0x134a471b521374441640f329f836d7d6ed18eeb6790e3614248ea000,-0xac7160fe44db539b9dccdba8c5435f7b7f735674d5d28242882cc000,0x45d5ad8e32daed6dce2400b139bef94a77b60e4a59962d6e365e38800,-0x15d79c7e4d02b48da016087e7aec18ad073f86782b4920c301f477f000,0x57d6525e209ddeb5bd48d2ff25ed5ddfa58b6538b1e9614e38d6d3a800,-0x1239cc12a64c34d91a4f1e2ffd42edbba6081b3ba470cd2d3429c8f8000,0x32ed8e69e2ed09717e44c08d07b76d83fe722ebe6ec0549a4cfa6314a00,-0x7982b37d10963d72e1b685455b79e1eec975af5f805dad909e08cbd5c00,0xfa468f67d24c134e5f416518f14cba8ab3a93ceb2bcab1dfb82f1080200,-0x1c0cd2a49730f32d9d2030af26bf044bc3ebb466aa22c174a1808162d000,0x2c1559aa24a8c2832b24e0e26c5674a2aafd0f835def66db07c0e0430400,-0x3d085e3e02b795f1fe6884a5abfb0c62bd669743f872abe212d62a210800,0x4abc53610f8e637f789c9fd9252ec538de5172cb91b759805b3ca322f400,-0x512f78b0be7bdbbad0a290fcc6c5914c6e6a9a9eec3dafe0dcf0e5297000,0x4e684dfe38ce34398d57e655baa78710f22d301f07c46ca24a1b4e3a3c80,-0x436b824ed675818682cab9759d51931ce180d01a868bb5461285153e4300,0x33a769558953ecd1b22665da3742d2a247d058c6eaacbf7b862c6e21aa80,-0x234434c63f84f1c9c7fc124fd4b9658e6237f3b1339dcdafb3fc04020400,0x157253b7528d41aa4679ed5a0d125042acb11132eb5c93125a36e03bc900,-0xb9ac43b4a3ebe2990bdd73ef40666e271cb63b9881a28a234adc6d3a200,0x593d7fd6fb678b64f90b62e9020a9f83bb008b8460593a5c025393e9500,-0x2602b0fdb09887675944333db0486e43f871290fdcb9c262cff33688c00,0xe4de725473c777789b97101136208f02065cf08515275ba13792b81780,-0x4bcf82014213de460a495390424da7f06caae7f50a0cafa23ea90b1900,0x1600426df58bf7ff534a60b29440144cdc8b3568de39f409c4756b8980,-0x59012f5a314e62e26969c99513d48f35aaf936e02e7f384c94dd97800,0x13798e8d40e35fe8a945032d0d64b7855fcc13e1cd3212bf0cc439200,-0x3a86e2a7f588c2a07d57f7fb9cd10b0f7d3e12f2c2736db62fe25400,0x95872062fd7bda4429225bd5d88caf262ebb95587aa66a35ffd6a00,-0x140fd7963317099870a07f59beae9ab1b97c76d61aae9f33ee50800,0x23ad29225150c8a19506076edb2ff0ea1e8b283500b39152f4cb80,-0x33a704cf7ae3e86300ceb53795e9cc828abbc8de0642fbc64b500,0x3b9707b4d131ed0a6d04b92abcd9253bdc707e2d5895e597bd80,-0x3553192f42704156a3d7036a3886cc786f4402740fd510e3400,0x23c3051015cd105ba227d44cf3a3923c132aad4ea695f7c900,-0x112f96a8da81eb1b904ed278cc6b83561beb328321d4ef200,0x592b386d6b8fb37d8f06cb162e21bea7f94db20fc7b5500,-0x11f38cc3648f3da7aefd3055e2910ab44bac7fa8103c00,0x1fcb80b3432b83d4d3ed81ef617cdcf985bcd549e680,-0x199cb8c4b19d0ea11f647f2216a20550e3445d3300,0x6b65fa45365c241af1f36386cdbaac6d9967c80,-0x447b996ab66f6223f4c704c0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 23 68 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 68 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 53 indices rho q17 m17 17 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 53 indices rho q17 m17 17 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r18 : List ℤ := raw_ints% [-0x6df737bbc3c50f6e622086047f54c03c3a8800000,-0x9856e00b98ad0937c33ceac63b1a13e93aee80000,-0x64043483ea1631311d0322ba8c146a48866540000,-0x29681a14ae752270c496fb4805a5be37393526000,-0xc21f9a363358cc3712438ae8d4430d437f23f800,-0x2ad4eb9b249cf912bc9c3838cbb8ed2e3e3b8600,-0x76433e8a2163a35ca154cbd65c577ffb801e680,-0x105d56364729e8201d3c7ef8156b336ecd91ac0,-0x1d8c4b00452de3ecd109cb3d4e27f233372da0,-0x2c03d7683da72d7196f1aa9af9a231a737fb0,-0x368019c2ef2c8b568b11dca97a88b893c598,-0x38573242558d404c1d29776c062d15692a4,-0x30b4177f5a24a143b8d15001c5cd324ca6,-0x232b4a441e4e4b670c68e681ed15d1643,-0x15222d676edbf437fccb0e129e29e1f2,-0xa7e99010c1398addefee422fa02c3c,-0x442828ca647f65f1bced4cf5d8c1c,-0x163f8b4428d4196b535e9ea13782,-0x5b351b136cec79498b84c0cefc,-0x11ac59e8d806abe4b7b2878a8,-0x26faaa2178c9c4df08845be,-0x3689cd9b517d63b74da43,-0x246b7994c7a008d3eda]
def m18 : List ℤ := raw_ints% [0x0,-0x1755a8e81e247682b8c3196de5803f4d5ba0c4fa8c818e780000000,0x296ab924c03b1eb0116f2ee49dbadcbd46073e081db044dd26138000,-0x2395500ee722830184989cb640bb8804c127db7be50f6b8f6c4282000,0x13b62fe0b2a9290fbf9f0c4956fecbc6ccd458960a6b4b80b5fcafc000,-0x7e99f17e05dc353b10c13bed4820e0bfdfb152f7d4925b4d786172e800,0x273cf3497f500400483ed90e66c5a589991a03382784ca4e9aa99633000,-0x9c509eee68c9fdd35fc232e5c25150c919569e4f64a74313a8645972800,0x201ec8c103580dc0376b1d5ebad41a5db0b29029623a0c4fe50507a14000,-0x58da5bb31cbf8511a2a23ae7b42ca3d22abb78e787c14d49cd19c517a200,0xd1cb7dc84417b3447406a144f569224507a38b8371b0ab6dbe302c652c00,-0x1ab7644ac0eda407583d643ea18c9560f4af563004204d6ba027bbb864200,0x2f5f8e64b3e87ca03322a8cf2752dd477a249da94fdb042002e8626d68000,-0x49966deeede1ddf70e06723c3363c483e8a39a647e952ea566a756a9ba400,0x64a6c9c20b41d15683748c1ccd3b1aeed9de9af9ac499f46e8aeeb22f1800,-0x79b3af0b80c8d6e019520961e3d9e8c9ead2b189c00d1ed521c398bf98400,0x82799a76c64c36170ab82a488e0e5a6da5b8d6ff9f259ebb8f72b68f5c000,-0x7c4a4dc2c1d8ff810476023eb756a7625987fd826de5965b66fb0a4656a80,0x69595bd580b079ed6d670b4563c0a15aecb606e1648f4f30711c77afbe700,-0x4f826c4770dde5388a6de37347b5d301a51125481099735f960a48152da80,0x356fb65b568ff45a0558dbecdb80f6e856ed940b011ba51021a3c62140000,-0x1ff6a98ee7699aeafccf896695b95d9cbbf9d7f6cd784c9e8f180c629e100,0x10ff474f28834e961706c27d440e502520b126c768c858ed88c3be5d2b600,-0x8056c693a99c449a3a3d418f016f16610e5d1c344fffbecb5b3e046dc900,0x359e35bea3b7e892f16dd1e198089fc700c575632bad02afa0e3209e7000,-0x13c508c4cf1c1a3b836a38291ae0c2130a0def292f6893cf7fe6572add80,0x6687e9ea5a288e75bf107fde60121c50181095cc1128cfb2368cc013900,-0x1d14127c7569c82cf7a597d1e27f63c4688f704cdfa05d396e6d7ad8580,0x72c92b5d1fccccabd241db95108f33f579fc27d076ba6d40a8ade40000,-0x18775633e161d3c51e10fad0e4ab2e53901d940884a5560e75de3e9200,0x477d618baac2244ada2adf3b600ea45fda919dfc39bc277cf8c8bcc00,-0xb13522e7be5f564ce0c71ce4b752e081dec8809619c1f03064d64200,0x170317728baf9bed10acdee5bffe7c790890487bef10b70ba47d2000,-0x277ff1309ff4faac567450f73dda85f539b24abafea74422d924580,0x370684390d683e1625693e6e24e1d479fc5dfd4f368b7aa2ed1900,-0x3cdbea3cb55aea14e141b8c43de28ecbb29a9735d09ba49532580,0x33fd9248b15a7e452c597c84d637d345c99921765c6d9d4c4000,-0x211f45ccaa73e910c47364570c81fda12537eb727226669b100,0xf08978b727b84aca530e9996896d279299e5a28c03d3dd600,-0x492ba44fd37e4757dd5dc272adfc1a6ef5417a7bdff47900,0xdb5314fee0193ed8da85ba776471dbaaf36fd83f42f000,-0x16616c1bc34ad44985e3f807a7ed05cc965bf22e52080,0x106f860f81aa6d953f0c8f01d33b69637c4c2ae7b00,-0x3e03f9feb25844f7719b6d722cc33f659b34e880,0x23058197760250caf87d0d200000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 23 70 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 70 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 53 indices rho q18 m18 18 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 53 indices rho q18 m18 18 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r19 : List ℤ := raw_ints% [0x183161680aa754c1fdaa654c1ebba4acaadc1800000,0x217df57577c2a757d0c0ac9f7c1e0f0fe120df80000,0x15f8e4ce71d0254a273995c4021f50194fcc0580000,0x916cd542002e23694e16acefbe20bb38e768452000,0x2a92ed85bf0ba0a82ba401bd5a46efac9e95167800,0x96273d058324f2a5ba1c39fced12ba4956e83de00,0x19e27fdb2d01f5d70765fa5fb6c21fc6844bc6680,0x393e6d1669f6a4a66f5b8665f051f1be26487e80,0x673b653c629d49378ca425b688991be0d0938e0,0x99914e09415f7efa4f2a30559f510108bf4520,0xbddea4e42cfc8d3e0a0067e3d7fa8d9374b48,0xc3f65282698e7f85c0824c5da208aabb17b8,0xa918baf77dd6dbc86ce23d235bb3227c5b2,0x79dd846befb5bcbb436b14fce7b8e25060,0x491213141611bf300aab4683bc63b0857,0x24329c79a0141abee5959b246ce78f30,0xea73a2f50fdd67553a8ed5f86dd540,0x4c4cb641b958df57fffc8a21fd820,0x137ba2447c79c7e7f3698a086e6a,0x3c2b860e94523f8dd44a6389d8,0x841f8f5d901f0193a8873bc6,0xb7ed537ac3bd33d0620520,0x7a1a8efa746cb5a76fdf]
def m19 : List ℤ := raw_ints% [0x0,0x2bc09cb338845e351a6dcfae0e5076b10bcd7155c772eb2100000000,-0x4d0cf6ac54fac0b0bacc186774225577e176092aff3f7eab870358000,0x41aa432eb9a3d43be6dd65b8b5c88872fe2091d4ae7c40586af88ba000,-0x2412d602a3f423306ff7725bd3cdd25c32dfeeac85266f0c065e992c000,0xe5b34fd8561e0bb6dcbba2d4f0a0384cb375d24f81b8d88b01b6635c800,-0x468f8c2e132a6a0fabb941267c0471ee14925997685a07830aa90af77000,0x11684c820ec2e7f1f4af0aafd04e7225df8c62e2e35743aa21f0aab12e800,-0x38b01bc0d2311cab4e7c8b745ba86fe6026324c98d9bcfdaf809fbec38000,0x9b4585ef65983925711f5d16d1613e46c3944345a3d30f069182ccacf5a00,-0x16ae1ae02d201f5ed526b5be6fb25af6b92081607aea352864ab865966bc00,0x2db8ef22ee480d4aa911b93fe9d98198eabce72488a8ca46c0991e47201200,-0x502f1187a707e97edfd870d5e83171cef2f6959d64fd449901276ef3bed000,0x7b21ab297a4858ad8df006667c62b083b5a5702fb0166a3ce79bb736f8f400,-0xa66a218b6602d16c0f53dfbc516777b3bf8ab0ec735cbc7057a16df8cba800,0xc6ba07be934e5b75a49a008af863dae4b18cb60f7555b889e552a22d42c400,-0xd24cd30e90ab182964adb55623cbb3664a52dced376d1caeba54792822b000,0xc5a0fd232b7b8b01f76163d05d21e228e44c8b924f7f3c84ae32fd0cabb080,-0xa525ec04bb66bade495fe3416bf37dd2d1fc1aa1f73e00db0a989348e4fb00,0x7accce47fc28590c4f707ceac471ae5087802bdf718827da82ba5d6f005e80,-0x51409b154a03207ab2ee6a093744c11a635b9980f58e38d7fb3a66017bc400,0x2fcfa5537bc5a60fb2016a728aedd0dfcfc542c36bc3ee258159f1dd45b500,-0x18fd3a1df1ba16e34f6391d0ef69f8d7e8bcbaeaa2baba46f594b32ef32a00,0xb947532a77aa37c0337b9c036879ceddd7b7bbe4e3797a7c0e1e8b7719900,-0x4bee73c2652d019f693ae82fdf4754e5ba2803e43b09e9a6b8826d9af5c00,0x1b6eae22cd78c02952e8d1946d2aceb4daa4a3aeb73bed6eeb73506061f80,-0x8b3a8d6ae6740e8f2f795cef7950a4c930840f359bef12852bf7114af900,0x2696964c3e5d581a5bbf2a607df5d0bc590bd74a0a6eb393ffd6bc543980,-0x94a21653d004bbd309630f9000d99d785065f5b3deca5ab2a831e2ab800,0x1edc15a087ace13aa9d5ae072c699a98399be943bd1d39851be21da9a00,-0x57aa988d26d7fc57a63841e75279a337e8527b0a8556efabea05e9c400,0xd2cf9bc2c065be16f273630313712bf83c580f716d3c545f47d7dc200,-0x1a7e0f2a30220fde8de10107f792ca7a856047f3294b8fef1ce212800,0x2be222f2846d5a13ad3d6d6f78f9d63eaefd0e573ad2464393620f80,-0x3ace1e43ab653cef4bcd98b4356b28d90d587a499ee247838a06d00,0x3e5545015fbbe19c9f6ca99720ef666b2d7ab4a559ed3eb1831180,-0x32d0e18d46291a9fcdcf9abd0b694780cbf3a705f0fb858b4b400,0x1ebd94722af9528b0673ac9e1d60a70c5937195d72214bbb6500,-0xd2bf0cd660b0b9cab260d2f8d90c45cb07c7e99113898ada00,0x3c1b951cbfbb70914e985e63c7e611db181aa12f3334b2900,-0xa793d857ff59077324a09405538b2dd8239b6d6b2fc8c00,0xfc19e89b6e4d5c30c0480a35098de89fa649a0f125680,-0xa8b9ca459153336f49667b9ce9cb5e0c1780a088300,0x23cca8e0cb4ad38b9e0f7341845cde684faec7480,-0x11e7ba6a9c3a72d45bc9aa3000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 23 72 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 72 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 53 indices rho q19 m19 19 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 53 indices rho q19 m19 19 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r20 : List ℤ := raw_ints% [-0x511c607680dbc8d1beb0018e00f6c0b753665c400000,-0x703744e566b55e04d23cc9fbff7ef5f246f8b2540000,-0x49914c6d21f18e2f285f5a836ee7e82feea07be80000,-0x1e68c59ab83bd5f9671e72a02f3d0defaee6f1b93000,-0x8e52e6aaf1bdb5bbc0816b6b515e0bca68636a0c400,-0x1f58491c0ba6a949dfc45cfe7bf765afc143290f100,-0x565fa46260e55e8efc2162c574b50bb73cf42e92c0,-0xbed0eddbd3b70c74416978845337791c472cc1d00,-0x157b973a47efa0c9c283005aea338c102bb9d8070,-0x1feb1d71576ac76eac99828ea48d32ab72840840,-0x276923d5841a9d91f72a75ef91f28e2d584bb74,-0x289d96eca2c37247493a7232c239336a833370,-0x22fdadecfa56856b179917db40108a3631671,-0x192c3c23f4f609dcf89cba9630ffefb014bf,-0xf106e8b75ac77b8c3bf8f2b82de765d01f,-0x7724644c2186bc996fe9b35a4bdf58dd4,-0x301d4ecd437b5cf2b36a101739baeb1a,-0xf9dd1d9c67dd72446d93b94b8b8e2a,-0x3f9c7c3c8e990219a300b06aabf12,-0xc3cabc43fc00b6bb24dd4a55d84,-0x1ac49a2095ed8a4c2e6360ca15,-0x2519fd682579a3d1ebf0d80f,-0x18820296c5005e466ff28b]
def m20 : List ℤ := raw_ints% [0x0,-0x520925d009f830a3918de5665ad6de8bf6213480d5f778dde00000000,0x8f5f1c689413bc415590c0a08c3590fed366a4fef8551910f2760f8000,-0x793a167f3c01865fb165a769fd6d169a280338621d1cb8dca08a7d12000,0x420e90be77730a51ee11ce0cc864dae8ce6916d401bacdf2c825728dc000,-0x1a11877b07abb9cc9c983fb68d8d2b40381861d119da6dd0e1a94dd502800,0x7f03dc34f03a0b01eb609944904c61fa575c2c70028b0018dc478467cb000,-0x1f0db5a8ed5f0623a2c5c6a72d402794dc231ff612955cfc6b284c57486800,0x642fd4a0b8f5f206648a4e28a82b2958085778c3125ef3e5d4dcd85c874000,-0x10fc5b0c11d96dfd1f9d18e8db5743f757369999d7ab8f13f41049490367200,0x274cc6bd0dff933a07e92079bd1b2a1337b24ce82af518c225057b2219d0c00,-0x4e677af775097b69a88076eb523aefeadf34948a033f5697dfe72293e29d200,0x8803546c85e3f70ffeb9abd1a8c65a13b98723e2066e49ac218b495b1d10000,-0xce83fd3651fd19216eb94211db755c2fcf947e042f2632585cd90f13ae89400,0x113d74b307d187ba6da13304aeaef38450172f2eb2edbf7fec7f1996a3b53800,-0x1456074240506bdeb83583fa3876e6b74d66fa05e3c82617bec684c8046ed400,0x153ef5067d6f2f0856c6193ac30cb6da96ab963fddfc837250b6a0f6367c8000,-0x13b318efc11dde6737b8728635fbb69b6ad8603561d3e0625da2976a5fbbce80,0x103b6fb5162155df5c309dd4e72942323ba5b0cb5fead710db4e03ed9841bf00,-0xbe4abfa7ad54058ecb82498b7f9aea5b038852309b7913babcda3849444ee80,0x7bf9b51412cd515f449c1a95fc23dd168ce584ba0a755ccb81d6ba48e24e000,-0x47c5b4dfd7b8fc3ad5dd3554465a2c856babd78e353eafe28a86b12c2670d00,0x24dfe904d5aa7882ba15f35c85a90958c0408eb1aee1ad5452caf7c3a329e00,-0x10c7e6e505cd9f37e4b801f1fc32c4088532974b7ff8cbb5f5e7a1fe703ad00,0x6bf253bd8c5056f8cda10036c815312d44028ff0bfbb0f8c687a99a8c82000,-0x2636ea1206a102110eb78a0223bbf83dd96a68b5f1ba52c6bab8f7cb261580,0xbdcf8c9446c77766618844f26ecf41bbcbf5270d61eadc40d178b50505900,-0x33696a7556d499527f8682184dd9445a3da9d4a916f0caf919f994777b580,0xc1393fd417ff1d2cb0e1e148f7c624b15f10df30d7c9c3190c768f2f0000,-0x271390a514988280414fc8f47f5e1c9068bed9080a6c29a97f0bb2dc9a00,0x6bea63e68bbed03f2e47651b59e0c0ef9a4f144e20e6f71200319d37c00,-0xfbb7b67421258c510668cf0397f6f9c116113d141bfe566f3719edda00,0x1e9b7a63897f62ebe5127398e5f7075d4d3eeb9a3d2e6cd32319508000,-0x30ea7d85ff9c829bd34b51f9dd58da274abe0813250e025d0067cd980,0x3f0991fa4afc6e5193c66c7e0e248fd654a0cd00276e7f892b667100,-0x4004b538cd6607ee63622f016c4f8a495e58f419350f29c9766d980,0x31c92f938f057c28551a54f835a42690ad916333fcb70bad096000,-0x1c95f7b816b6d5dabe75b2b13da032cdf632657c998f589610d00,0xb8eb56319ff7e63373ee27076cfa39d11612e1d025556259e00,-0x316d2949ef9481af6f59eba83bb786360248679f4b70f8ad00,0x801b891566e6c97bc2608e4ec3b9e1af6ea8feb81437a000,-0xb1818b1d691571c06b5c543472d6ea82017de8ff8d6080,0x6c3d44d51999a769972d6cd130a79aa1a5f127ed4b00,-0x14a8ea15c593fbb566d4ec0c308c6b72d5c1402080,0x926e99ba8a3dbeacde99608000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 23 74 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 74 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 53 indices rho q20 m20 20 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 53 indices rho q20 m20 20 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r21 : List ℤ := raw_ints% [0x1047b00dab3b0edd63879370f0ffe12ae8665b41400000,0x1682877124635b5a2ed0fb30f36c19058456d52b240000,0xebf6f74665c9f68354bdefd95432457779cebc50c0000,0x6178086e6d093b21ee3336897fad64e776ba568c4f000,0x1c7d7174b07a9a49787006526718fe20dc9d7e2d58400,0x644fadec06074f1280914a98afcfe7dc69722d5b9900,0x1142c9cc97452fc423e1e03cdcde1a12141575b05ec0,0x2618ae832e4fd5e6a052ce52c69bce9cb75aefdd6c0,0x448dbde37a8f79e803ff1d49c9c225033ce570e0b0,0x65bd92208125f62ca2d2a643e8b5c7cd3e3c7ef30,0x7d77fe008b2fa92f3ec25b77c62d2367e34f1ae4,0x8121d2dd77217f94191a761d857cc4622ad23a4,0x6f164675a5159042126f8055963a99f41466ad,0x4fca0d08e2cb25df85ba9a0de285b15a06b94,0x2faa1f07ba07da75c1a8fd981b1b644012ec,0x1783f68b81dc53ffc133dfd6ec158da17a8,0x979e802e0b817365f1d8f3915f48d85be,0x3118166e190386a38e8a2cc7df466018,0xc772b8888c3284df40612b1c946270,0x26412c2b01af5069c1b80c14209f4,0x5366e408ac0bc730c3006d2b0ad,0x7329c8bf40b2f5bfa44c8c024,0x4bbf10338cffd1c51282f38]
def m21 : List ℤ := raw_ints% [0x0,0x99d126e612b15b32b0ea0e1fea52e1466d7e4271913002a00400000000,-0x10ad4aa73f93c9b5850b42b607058d83643535d44144803f3913dfc18000,0xdfe4011a270f11f2bb4d42348b22e719a4c430c095205079147602b0a000,-0x7908923dfca09f8e07e3c54bb6b908fd24f76e604c4d829bbe2ce3728c000,0x2f5f8f948b572d6c902228098bfffd9b37a6fd972a85085ffc88f9ab0a0800,-0xe4dd1c6279c58c0513b81f2462bc03e5ebc434e1ae4070812e9d6f30d2f000,0x3776803e0dfe26ae29c81fed196e96e9d6cc3c6666e9dd11d43bcafa8d42800,-0xb14ef13078f75f7bfba85b54d0d0e6650f0dd9fea9fd8c2ebd92e98bba78000,0x1dc6e54a4343cdd2fc106ff05e6b50d6a30bcb69de914dac7f09b9ce36e5ea00,-0x4437f1406ae5a2434d192b9032d3137f9b6c9debbb3c7f4b2b189bfadb3b1c00,0x86b565db678eda104fd0740e8fecc8beafb1bc9e37f9f179cc78fcc4c532a200,-0xe734be8b763ab3fc431caa75f6beab6ade4677c9de6620934f07125e1fd6d000,0x15b2b0be418c18b2b3a3e4f61b19bb21de8f48a7d98bc10e76d465d6f82176400,-0x1ca5bf989eae86e638be94bab3210aefcb4dc15cbb92fc09eefc54a3f3dd54800,0x21628c935c49b9897919d44d157da9cb6547d861fc4d750f8ecf53de41ad41400,-0x227085a54b00ce5bee77a01adb243b213ec3866035f9856ae496423c5a13df000,0x1f831ea3d967ac083b239586cba8129cf9884da91bd480a6a235f6c20b7e8c480,-0x199b65e88b1043456a06979e656bb24eed7d06aebc11356f424604d3d07a97300,0x127d82ff62c595c5807bebb757199baf13be74183af3f572978807aefe69b3280,-0xbdceb22451c79e22d900fb32d3b8a6e5d5fa378869c88b8a4b90cc0731ea8400,0x6c1f477ba3bb7313db89cbc2c89036cdcff23e9e4653244ea4687b1eedbc4100,-0x369c6d1ffc3afe67fd3e8d366a35049017e5cf96531ef456d12155c7d14b7200,0x18688eb97e406f7ef16c923bc1f8a6c6ac522fe960deaf7ff576ff9a28127d00,-0x9a0b47d0213d87e407302093d38ca6eed514743fb63bcb0a7b60540fcdeac00,0x3570a4f3c9f2c6aeb2b65a8af6fa294a2d13b3fb209de22a5af3719df852780,-0x103c6d93238432895265feee2bf97df9df6cd31d0cb5b468b96570b37985900,0x44c39ca823d83ed4bf2cc3afef1683a256c01015292240eae2ca45e9ed2980,-0xfc2ab157289390f95321a80c80b9b34de11779e2cca2cf7750b03e1a3f800,0x31aba8d8491d1c5d2cbef75aa5b36cd927ce681f6e4910ba4b72379936200,-0x8556e982bf1d86c6d9b51716db0e88a2ecd7b1c92af68dd150be979fb400,0x12da6594338e6051f5faabcd4765babdbd79359123e501d8b73f1ec55a00,-0x237bbe0e0fff0df6490f8d7a1893a54722ede8c5dd0073dfb18100e4800,0x36b3b2f4a05e990052ec676ec1dd7c592ea87fa231f77cc2162936f380,-0x43c63d9939a15a8fdf180281307d5f8c9ac2ba92b1676aa9adb92e500,0x41ec3edb9c1b244b0893fae660d2674783011aecaaa32b61d5c90580,-0x30e31f923e63822f47f2ccbae9faddc7e934d32343fc21f08f63400,0x1aa1914407e37307d18fec869ce40fddb29201155a69c477d02100,-0xa27b84eaa81f7ed90bda95e60b8e0edcf325b9cb187bdd9c8200,0x28ae353da8596a4a0d3f26fd63b52da818b135beaa4c2505d00,-0x61fae831a908715926423b90659ff8686c46fc3f988595c00,0x7cfe8659159af9fc24e44cc3d20423018f03a54d4340680,-0x456cabaf3898063d3826eeed1d457ffd1feca4f4ed300,0xbeb5a5f584a8039b129865040138e2d4a82cfaec80,-0x4ad42cc768a3dda4f16c30c0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 23 76 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 76 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 53 indices rho q21 m21 21 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 53 indices rho q21 m21 21 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r22 : List ℤ := raw_ints% [-0x32510f2c3390e847c8312e11b5dfee60f338c51d2000000,-0x458870620defe47c36e730c87a200532ec9397c48600000,-0x2d8764b8f5b18395fd454b3e906cdedad379401abdc0000,-0x12cb5bc37b4a52d0da4a61d732a6b2b048e357f6fb18000,-0x57d617cadba551bd9d29a273bf0fbc71872e8e0b513000,-0x13508bcf2b9e5d5a8bcb81d03dcd111211b7c708a38400,-0x352231d6a23e2b57fdcbea22ac714896721f5335dbd00,-0x752b1175b853b2d1cd0937dc10f7587baaee6ba6dd40,-0xd2a453a969e367859b70776dcb1f35984971794e4c0,-0x1384aca24bdfb3a3b02d97f92f4576ba415538be050,-0x180b206fb783c6f2981f528256daff699392fad070,-0x18b723144c409b2c93c066f6256d0dbc297146cdc,-0x153bc0fab97e42abd2390e23aee3b744a8a2db64,-0xf3a9ed6df3acc04fa192fd4d474ac18e36a89b,-0x91542ee876c7a840b3843edef5e7c609820a4,-0x4792d2428d9460275f08dcedf3c67d21dbac,-0x1cc97e92655d0157c1988d49ad9605c9828,-0x94d2b66a455a61d056485043eab492b12,-0x25b2e683ad1524205874b3239af9bcf8,-0x736369ff2d4487e3ff311e9268d180,-0xfad48cf9ac79b42c33bd64611234,-0x159360e075cec7bd17de55630bb,-0xe235de8befdbb55c44cfda74]
def m22 : List ℤ := raw_ints% [0x0,-0x1206828ef630c8aff0bb6da7bd75b66640d4cbc94f03a04ec07800000000,0x1f0b2fa003fd46b0fa0ce715201c9928615d493308ad85b628f9758eb8000,-0x19da89cea2247c18361545a2a8f063770a617c2ebf7c8b512b1dc84e022000,0xdde500e91499a32f7b4608f707cc4f313dcaf290794d428f12983f915bc000,-0x562822250f9e586e48b61520c9cae3e29a4d65553f2f2d27f771e36c2076800,0x19cc82681a2668f77fd2fd4ef65be3c1af424db17d88e861f3e6a8211fc23000,-0x632ca0710b7079d2e4be4aaffb185b614521a04f1eb70fc43542a207035ba800,0x13a38c268b24092199ddc090f9e5445238f5a3d71edca76ed7180c9692c8d4000,-0x3447fc60c064df3bfae5c7ad3ff8180e27b78de420c974bffab9d3dd827d3c200,0x769f361cba02cba9c682e875f474ad178ac9986f90bf3f4634eedb3e37e93ec00,-0xe7e3fbcc759803b623b9c135d15b08ce127048f545e5717151f6c2b7f7a37e200,0x189d915e413ae3fbb75bb60b4b95fd811211d959ac9b6e4b209f8f5687b0138000,-0x248f1deae621fabb62737b8933136b3076ffacf70e3fc9dd7df4fd8c9557ca0400,0x2fb8361f855a7381b7157c0523f62274aa1079afbd2bdf34d02a4522e794d65800,-0x36f35364512e57f8e57ad102809d2f195d58c86fd737ec5ffe753d79b311d5a400,0x37fb512206db9be825925d83803be402e735391428241e2b8a45e1a38573294000,-0x328e641f3ecf3e9fc5f46c7c4713f362b6a8c1013059475a6f58d63dddd5ad5280,0x288564244acfaf4d7336214e9c4e37201287f687101a7728e3a7bcfb7cc8765700,-0x1cd6e2f6b27da7c8ee53daad4d7a491b6609203265b1d2c71131139fd3eaef2280,0x12392906433d9f655ab4bd1eba7ad30e8aeac3ac7f22e301ebe8e45a5e6a21c000,-0xa372b2ad79b200f075145fa6c9595b14a2509414ee98123530cfa4529bd93d900,0x512b05f723820716d639fc0048a8b477ae3dbafff954a3246d8e48ded08d64600,-0x23a2201dacadf061761f3997f620f68a40e3c090db1700adf6d5d52ca82d77100,0xdca6499de6d5a1b514f8715f912b96eaa82ab7eac3b41ae9f02d80525b4f5000,-0x4b03e85d5986b51eab003cb34024b00cfe5760b577959689ac5e014a8ee2cd80,0x164e483e35c194c2b103e06e81d9adba84d296f5cec32465f16f8dae88a2f900,-0x5c5349b1c2554b96295cd4e8700101ae65252d5652fda12b4fd315e67962580,0x14a57d3d310a5b78281f01c6434c4e0e8abfb89f6aa4579801cda97aac40000,-0x3f5fa74e27b77f3de2c0c63ff30be237fd7a82a63016f649a377f4df926200,0xa55b19379fd329fac93082bd5cee730a5a69506a2c69f35786cf1ec4bac00,-0x16ac30f5b9de2c54e60cf4ff919e6f3a815331bbcc87d1cdec9a070ccb200,0x29462b98a08d7acfdd0de902b084d398fc19cb1c80a5a5193de522d2e000,-0x3d5d1fb50af87a35f00cb867973721df02de25203607dc5345e065f8d80,0x491354dfe8b2cb98a3959dbb54bbfa0458e3d1ed1dea538a269a838900,-0x440e4cca8e211b0e4de5b2b0c40feb7749021565e6801f1ae85392d80,0x301bbe25495f2e7a08588c5699dfbbdb1bbe36779f34dffb652c8000,-0x18da722c996d5ec9005a2ffa1c632da6630842b0616b08c5e7c8900,0x8ef3ef440018c00fb75a861de2a1a5fbcf836fd1320e58afa2600,-0x2182a3ff8540aadc08cc00be6b9e3b59666cacf6e4faf5424100,0x4af8059813fb2c3e2c68c1f0648da2439f5a49fd7d8085d000,-0x5805a6ea782bf9a21fa6439bbf276a5560c2c74a1fc86080,0x2c853e59ad81ba18317dc196dbc704c93aee6eee4f1b00,-0x6dfee532b191b8464554ab5fed85d43dd84d9efd880,0x263ac4b46dbc631e7ac295200000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 23 78 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 78 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 53 indices rho q22 m22 22 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 53 indices rho q22 m22 22 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r23 : List ℤ := raw_ints% [0x9644427db3d48a8bcb1ec70470935a15d5512df553000000,0xcf8c6f31bae82eff948aaec330770ae70880a3146bf00000,0x87d2f6512236593088c001751bb1f87913cb742dae200000,0x3808f7a606a9e8238fe837986f594cb872928fe63bb24000,0x105b6e65f1532ea25de83fa18d85337b864e716ff2253000,0x3982719952216bbcc4c688f84e62212b8713a0b760bbc00,0x9e1678e7f2cd9b9a582e9a9cb0725ea06e5db2a524c500,0x15c540d71d8bf12c93b00a8641e3a51cb4dab716266d00,0x271ab41b57de74767027e1ba0d8073c75b284436ed600,0x39eb950b2484fa19328de9de57aca38bb4a4028aa8c0,0x47468fc16a9ec4f9c3390086dd17a689e07b597f6a0,0x492f9a575ae418d2691faac2f52d40a25c723f0030,0x3ecc984da10d6297e62dd2c5d512a3c36437e4110,0x2cfb34f65955d80f65537eed83ee373b207405e8,0x1aca22fba86d5bcd736dd528ca0f2b6ceeff959,0xd2c421ae6abbd63960c5a3d6d66c839d13560,0x549fbab1ef6b21ae2406e79d75ea061dc7cc,0x1b4a749a5450f8b96f30d0be4a41c1678d0,0x6e608783901aa7f54ddfc1ed44b767346,0x1510d844e68e9b981e61472029b3ca30,0x2dac78e8f59529fa1b68b6df46319c,0x3ead517b4e2b4fd6339498858fc8,0x28efe6dd838590c5039179b749]
def m23 : List ℤ := raw_ints% [0x0,0x21cc34cc0d9b7849e35f6d9a833cb5ffb98efe197426cc93a8e1000000000,-0x39cc53e9aca5b52db7eb4f674a8c95d8607b28fcda311138db1e5712ad8000,0x2fc90992927fac711348a9c35a0ad3badb4e3926d58565138f4541cd63da000,-0x1970a2a851c80e6531e089b69b901abdd893f04a3390ebbb0f2d036f566ec000,0x9ccfaea93c8a7a1fd969aa3d965184ee43ba45cc004f041b32f44463cdf04800,-0x2e935c840fd821ba1bc5b177c7f97af65519fc9139c1867209b72b57a1dea7000,0xb189deaaabbacefe9801ec0fc66912941769e77624ddaa94c5589d023f8676800,-0x22d99345a831a1d0c551d822cfd69b22da398a8bd612c7ecab4b9d3fd63a3b8000,0x5beecaaeeb76a469be58c33edfb0b4942eca9b6ac31bf205e418c2111ac458fa00,-0xce9e145fc307a12db0794ff03379d91d7c02a70542d41cb6e991ce8e95a4d27c00,0x18fef5f327317a2a98b29866f5876585b7ef019f38dda96a6a32b95c9c3ff23b200,-0x2a049613144e4a0968846cac1394b0e31bd5e5966e331f3c93aeccfa33d00aad000,0x3dbc90201da39ea51b6df7f69853da3d6e936c7841d233179644dddf3f2c2625400,-0x4fae4e313cf17044b77d21d73016649641ce20d3dc791e3a2cbdc63fca22c15e800,0x5aae15d7f30c40795457af4e8f07b2ccf8578c368af4cac6000de4587a05342e400,-0x5b3f857d564699965fed6060d8089809eb45d0d116208485d944d1ec71bc32b3000,0x51581be1b44ea93c1ea549d4d779702fc69d93e77e2e6c4491402a454a0d5f67880,-0x405100c1e0d17a175e702b0774a8c82bb17cadd8d8598bf4303014e8b7e9a49ab00,0x2d1fc0e89d95fe50113d39e1c27ae0e76a35cae5da8f5a7e000689a3b6165e72680,-0x1c16162f76eb4130210dbd3eb2e0d28849712915c7dbc2af366e95cc0bf901e4400,0xf7ee097a62e8a38e4291d765f108e44e1d025519b40f7646eb2113717016646d00,-0x79109d5cc0bd43fd6753250c9910b2d586d19aad65be5dacf39c48f397dbba7a00,0x343548e0ffdb54aed615fff2b1d40fad5f0582f1af03654b34ca59bc7a00c84100,-0x13d37a7f5375dc293ae4b6b195f8b7cc0f14e390c2ebd85560b7f9147a10327c00,0x69b1a25297a63e3d87908af9333ca045def659f58556ea6bcdfe3d4e0ca652f80,-0x1ec2829bbb6b6dfc72efa5674f84b947ee763accbdd44d43255885e4ba6d73900,0x7c6ce91355379eb41ebf75534bec6ecc504738231437b7e306cbb9f29d145980,-0x1b25eac17395cbef7177ce9f7afa21a2c6a6a57209d2903cb606328da5353800,0x51276718a4f261dad8fa1590c11cf97a83a684424aab7d375fb244c74fbea00,-0xcdcae46fb124c4f751f481337f34c16cf6d2177d6038a7d54e4400afc82400,0x1b5c12f1e8ae4712151a355b779d5d30128ad99807acad9537f639533e3200,-0x302a8f4bed41acdafda1b9adb497e249f7bff7c4747aca9b2abd5fbc46800,0x450ba4f72f2f5455c39b7726f0ebeb9eb7db6bc0d6571a2c60670aa87780,-0x4f021f5975260a702569d28856cb01d6bbf677b26d864e9d46d2fb21d00,0x466db21c5cfdc8939101f6e7df65d465585198473c001b09c4030a9980,-0x2f7072bc6ee9be76baed1df5a7f32f698774a10c6abf2f7254332b400,0x173b76c7d7542131a62930e9b7120a87a8a70df51c8c6a3290defd00,-0x7dec1db9db747527a04ee9b084a1d5dd47523ad2c2aedc4369ea00,0x1ba007f54a4319d823eeb8120dd119ec34975dad16331e32df100,-0x3961f68ab5b599d076f887b65df8343e362de263cb65682ac00,0x3dfcd8a5fc344fd1be8f5fffdd5e4e8b0531d2765ac10f680,-0x1c8b6602f97d5d4486622e4f1a56a67facffea84f402300,0x3f6cb25543870c5000788af2b12db4d2841399b9e480,-0x1386d8b0676766479ee5e73000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 23 80 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 80 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 53 indices rho q23 m23 23 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 53 indices rho q23 m23 23 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r24 : List ℤ := raw_ints% [-0x1b3191d07509083d2d58cd1a87e0798690597315cab9c00000,-0x258ac2437f45e215d29e6f65eab5a41ab80f268632f80c0000,-0x188e41dccce4c8ce087c67b31dac17062ab5153b4bbf300000,-0xa20008de60c5f0576902777c6ef0014a154d2d5c098bf5000,-0x2f42e227c19b51e56080738da37c2f78a7c91bab598343c00,-0xa60ecbfd92564c30e8ad933991875b4a146d20016fd8ff00,-0x1c8290ec5f1c34113fc017b75216e5983535810485b6b540,-0x3ec591321612796c1c89c4328eab38fc3ebfaf46aa72b80,-0x70a8fdcde378b2bd19eaf9d343f0cfc8e1b97e744bde90,-0xa6b94e22147dccc1ce4656dc647ce9af8676b92437be0,-0xccf95e6e4e5b3c9b0350799304d02810c6966e00978c,-0xd240b8101223358bb10ba926f9207add39db5774de8,-0xb4368f072447214060e73d4fbae4bdee630431e93f,-0x80ed07942c20d7793b202a9d319a11f15c3d280d7,-0x4caf0ee042744a5c9b1c2919864c855abeec27c1,-0x25a71237bc2e0384032705724638615960183c4,-0xf181341f7e11217c201f590c0231ea02ce0c6,-0x4dc005ff923e5b4bb44071b6ca8b01f6b83a,-0x139dcc6c39fde5227cdd47a84487d3a2c2e,-0x3bc6bd54125adcdf3d70fa285ad3ec79c,-0x814db258d13af4a5b7bdd1caab40adb,-0xb0fba916bf0d3201fc047cbb11747,-0x734339cd357b04a1b82bc404fd5]
def m24 : List ℤ := raw_ints% [0x0,-0x3f5ee2fe9983818a8a52ed81b611d53f7bec1c6fb9c8bf94dca5e000000000,0x6ba17193df144ddb246bdb7b17c5380ea8e32060f5173b1898c01b91da78000,-0x585aca7833cf7d24357c7ab59d225c9bec5b821db402ac0639c82bec44fb2000,0x2eb1654dc64e392c8d6c4ce8a758455234c1d2ca05d09f936345989b0d099c000,-0x11d9f19e43d96d150b28ac22d702a44464b5c7a502217b93934ac7752297e8a800,0x5429dd0bbe5bcd692c7d7c7e4706bd0872c03526f233cfb605d72364f4b793b000,-0x13e2e4e6ede35e78d3b66dffea9b2ac83f0783284b342f17bb8496c4e096ca0e800,0x3dec6965f6afb36e57567b9cb1aeb57e5288bdcc8a35226a22c87e52df5f0334000,-0xa1e615eabd0f0ba89d461bb1a97e2e33e78e27e334bf6634d2fbafd2ec948039200,0x1687e25cb83771709df19213a214ee4651e488d87f8da5a75ed6a65592e74481cc00,-0x2b3096c03bbd1b25623ba7df351178c689ee85b9d4202967afa5a6eb228733f47200,0x47de7ffe65f0c1316118c9f84f51758d28ccb4ad5f51c41610c93ccb4219d33e0000,-0x687bc3f5866b76d9c60cc6fde9e5b8f6c7a1ed12833db7a3ab8e64cd08d64003f400,0x855d7eb01d48622efe76dc61a0fe2f84c6009bc59b4bd5619764f4cf82fe25ca7800,-0x96058a68ea3482ced93ceb51433e71369c64b8d881123b73365fd0f7f49a13b9f400,0x9521fb1a52b04179ef0ceeb1b4c0d78c28a060a46e1a0be32da85b3b6646544c0000,-0x8341416ce99b42796aa56e8c753bd91e7172f846bbca77cc2d421692c24ab17af680,0x666426d991ceecf81d121d8d2a0d797be33ee0c2b3dea1b5a57cc9ea1e35d9dfaf00,-0x46d3448ac0b125068f9c8453308819477edc422c25620c97c7c97fc2d3da517e7680,0x2b6db0057fc4d047e76c4eb9edc7e9ac8b57eec1f17a1bae1819ba6955632c62a000,-0x179589219c934a2bcc9059db0da3268629f7cbbf7ea82988e41af4d5ba812d154500,0xb53301a52b0066001bc885c6ab5dfd6a1548a7ff7228bf468051bd39b68c9d3ae00,-0x4cc3c7204d8c69cca8c9697675127d5a3fe3c05b26ce45aa015d932d25efa381500,0x1c9b341d36d09b91127cb51beae00052d8b21eae38d0903cc8b100cb9fd4ae80000,-0x9577198881a03c4cecae5fc48378a078e12b02de70bf5637e515d951d3288d0580,0x2a9313539e32d80e6d764dc8320abae4569d72167ebafe86f333c1c741eb0d1900,-0xa84e0210f2bc499d3190bf7e85e46e3015f329c53c0739b51de52d45dff36d580,0x23d3e5394ee298c9a2d3b2003a44f2bb91f3acfd37e42689bcf65aebe0f830000,-0x684bc0f35158c3340cc3acce9dd117e941b9db1935b8010314128d03a90dea00,0x1010300e0efeac1488971630fa0aa0e72de8e2d5a4ae7eebd923e3f399885c00,-0x21204fdeb8b9db73dc4fcf6eb6ea1067e51b700aabe7c7cb4498345dcccca00,0x38631bd42019b9424b16b142683d06dd5d866f0b5602d6e0ec272fc1ac4000,-0x4deaac7df20b84e30f2a36b6f538029d0ec9d185f3d8593f9c8ce45236180,0x55a63fb2aefe276b1b90a34f854befe4197db69a878638dd84bd59a26100,-0x490dac7e6136f47cdecce07dfcc983cff4cc8b7dac7153918d054c32180,0x2edef34094e9fd09c589c862a45e83911614bec8f82424aeb6127da000,-0x15c0287379ab934944bc43b1682e1da308a7abacc7b64c8dd30e52500,0x6f0b9065abe97e85e0ae318536d54baa9735e5d4211a39e65396e00,-0x16ca18c7dc6af0aba527b434e6ff15b395308ee508ae42a3bc3500,0x2bef85f0bfcf6becde78c50e130d90944acce2074146a3e18000,-0x2ba75195f3dd3a42de4fc7700a70d6a481ffc5d23ff1dc2080,0x124c3bac0cc106c124be363b992e286e6eea6500b223eb00,-0x248faa5fee63cb0701fe26e64b26488b83bde6e7c1080,0x9f8b71a35e24ac930747108000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 23 82 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 82 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 53 indices rho q24 m24 24 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 53 indices rho q24 m24 24 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r25 : List ℤ := raw_ints% [0x4c91013964f452d38e07ec61faa846107ffe61145fca6c00000,0x69a80ef9fa2494a15fff552b01b4234874ecc64958e975c0000,0x45134bcf5eb251afb36cc2badbf7fecf1d6e47d8ec79c940000,0x1c77948657634a90b42570f3f9c4974263b9c658acc99911000,0x84cdfcbdb42ab41261649060fcc46348c2a9b91913b9647c00,0x1d258b6026bbe1bfc58034f113b3ae8d13aa65f4dbd7a20700,0x5003b60c54a21c9b225f31cfdca523af3ebcd9a2194c2e940,0xb00cb94d30e26f39550b230e9a96f55e845e740bc0ce9140,0x13bbb3a19714ab203e73b7db712673165bdf3c8bc9099cd0,0x1d2deb3309994aa012b2f4e34c3ff7a541b596f5af185d0,0x23d7b581157046aff59cf832c7b92c98150bdf4f48f17c,0x24bb2a060fd5041c3ea4fe872543ef1870257208d345c,0x1f737cbcc287310ec66d6d714f070dfa938f90f5e29b,0x1679bbae0f2d3ab4da39d653cd74903304950ad945c,0xd5a26fb812a690a669d19ab3ae6e7fcda42619dde,0x68c280ab76c7f0ff3862675b0831698697aace58,0x29ef8f227c16f8223bc8a37e980d3c94cc170ea,0xd7ad0471e77108d84b7d0c6e4b83ef3abb048,0x36526ecf8c86ee093258a440ad0067d9986c,0xa538c2a1d8aec3cab50f88934547b2dd8c,0x164a6f7a67647ef8ff51dac5a0aab7353,0x1e70a9e3c872904e952bbdf8aafcd0c,0x13c618948d3dcce6135e38e172f52]
def m25 : List ℤ := raw_ints% [0x0,0x76d1e99d5fd692e3c35b7d5335616fd7085ab5517c5867371db704000000000,-0xc876eda525dfb95eb744097ce04d7978b6e2fa1a3a42e9637a9b49c05bf98000,0xa36d593309c86ba8e8808570e315d53c77edb984f51c942d63acc4573d072a000,-0x55bf914948e2111d723a6fa64db8d7dcc07b076d029787af706bb62e0d44e4c000,0x2089fc2c5d70bed95d0540f85241f7dc6178ef88a09dadec97e4ca3eb3c58f88800,-0x9839d92f9c06d545b9cb32a58c4fbc7c49e3b3bad43f072d415fade9396e51df000,0x23adde388cafeda7165a0229ed8899fe87db3c6b765b62304fa540515a1bea9ca800,-0x6e2bcd2f15fb49d8e360ceedc4de70fab193e2704002fd6f87c6b521c93ab47f8000,0x11d880b6e5c4663d8acafaa66e8775141c75791b6f384a09d2ce6e43e64b37d2c8a00,-0x2760038fced4e0d72b12ae0f265148784cf236b9df7b8a7f895afd1237b18e484dc00,0x4ac34124fc34aabee56fd4fddeeef83b81e1ad9ad6f3fc1c2c29c6ab41e4ddd774200,-0x7b2c7e792719971957b3d75521ed76a374201f6d9e87e057f5655922fd0b9d63ad000,0xb136744623a303e8d5190318846340242a87a3f042c7763097e34f8690a25863dc400,-0xdfbdbe8b57d3db3673c5f5b813ec35c11d1f1c012ca7341a0bee69ab0230145258800,0xf8d164881066447772859d264c49f7a4fb853da27ce882dc791b36852ea140adb3400,-0xf462b42603b3af12f97110b369331a06f4a02e4a0f5db8fbaa505137ffcb063da7000,0xd4627f62c8894a74b912870079a6a43c7761cdb663f4e21d53aab56911ee8db41cc80,-0xa37cc1c773ca4e608044255f3846d6e8ad7fc3c68ec94ef4e321f7a83bf695e33a300,0x6f821b02f8080b9777cc5bef6486ffb57e0acc6874f0ae4e3a8bddf90cc45a9613a80,-0x435dee23feebd8c5644f0788b40cc8f2a381ce7a0322297a8c71b02996d915fa70400,0x240391c1d91cdbe8e4ed51114745abe4adb883f461717a2144c9848b2e880288b3900,-0x11021524f26de99a40480713f28745d0a58fb030f89c8110b6e2dc1126dceed0e4200,0x7144539a333b701574d7bd38b85c9d3f192d4750f607df0ea1ce55e3ca456a51e500,-0x296c0343d48dbb4668f666b30ccadf329788c1fdd4d0b1870459692c763431c6cc00,0xd42049a5473baa7dcee2d71aa8e248d29cfc1090a556bd9c6d59c9b5b7a0a363780,-0x3b241279f27fd107a616aeea24bd0cad988041c2da3ff19848e431ffd70fa4b9900,0xe47b7e37164e26556b9125f7acefe0ac17456e92e6b690b0599b490579db97c980,-0x2f73a5f351f05581368365ba9b2b8eec3ffda99692bc5f7323240a2f2700ce7800,0x86821931bea1914a7ec9686c2b1effc793c1e49636623695d05d7b35f4f523200,-0x14212a3ba44b2a69f1a53a1276205ee2a753266417ce7c1fe023fb29cf7471400,0x283d314b6a1e3bc7fd1fe9e5879ad42b7de83c42d4e257c0957a4c093ce24a00,-0x4236c9775285d4cb1cd210d406f1976fdf4ece9d233b02e84b5c1d2bedb8800,0x582d5e2112ac0e43904bb8d7b515397b41f631817d63dbdc6ef8045f939b80,-0x5d16055e3c5fb2705585b205041b8a79d474dea4768e705d9ea3d2e641500,0x4bf1e798535b3a0a65c232afb9b16547296a151300a564beeacea2d0cd80,-0x2e653992269ffcca2aac5cc1fd09288948eca987bb6da40b1c73d0a3400,0x1464a44653b149e6f26dd7ec3dc9c67d8bb7abed0c2913dfb949b8f900,-0x6207199d5fa15a24cef84d746cf4b43f2725d42e2b64f6f522091200,0x12cfeadad621e30a3478149079b06dc09763abf0beae4253dfee500,-0x21a61a40e80a9487719234c8dc5cf31f5d4d33e8bf2de0f347c00,0x1ebdd3348d7bdc96a18fe6d8fb4b917d23e099803ecd4fb2680,-0xbba1849a1dfd4328ffa2f65772385e38e77f6460772c7300,0x1511ee2b4ed457a65e000b2bd97b995ddcc12b57a15c80,-0x51748b990fd6fdbe0da8ecc0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 23 84 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 84 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 53 indices rho q25 m25 25 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 53 indices rho q25 m25 25 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r26 : List ℤ := raw_ints% [-0xd22a3c1f5aedbb7894c9999125b50c15a652a8b7c1c643800000,-0x121e4aa035f4da472ad768b26fcc20dfed0f22d9f2451f0580000,-0xbd70a2e5762f535e3f5aaaaa2c64d651e241b8965f0f56e40000,-0x4e08b2e8c7d5e33bff328f7aae32ee76212a80ddecd7bcc6a000,-0x16bdb3b03d9df8aa1d3de6a0b5bbc4e650483f10f1e5bc30e800,-0x4fcfb8d9fa2cba1218530a0b1852e222a50c2615ff3be212200,-0xdaf885b22f2fd20ef910ceefe4175e808cbdaf5f3bb6904b80,-0x1e179c22822ae562b4c10461e9b76969b07c5ff44fb72657c0,-0x35ee4809882deb85c4ad3454a1ac99b946ad06073b86951e0,-0x4fb0106fbeeb7e0981ac09a06a53b9179b692b29676d2ef0,-0x61ce63a79ab31f8425f6bd9021f6268756a9171ac1b6bc8,-0x6424ce6839b5f15ae159f67dd90829da8eb4e8215dcd94,-0x55ab008e463fc4963c0848647b9f807ab08e5f23517c2,-0x3d285bc83e5882266081c8010c2431e19eb73faba473,-0x244ad08f58fae39002ededaa717a4b1b3bd5f890fb6,-0x11c67a0d52d5b77367d5c043fe22359a44df8e841c,-0x71b33c11cfe0cdfc1eceba38adbf18e98ae11674,-0x247ede772cb08c40282792489baa1e7b98b6fa2,-0x92d855291bbbb1deeeb32fe9b8a566fa76434,-0x1bddf48c13e346e70438aa9470e69b47bad8,-0x3c0ab87a218f3d956bc1bd749ef69052ca,-0x51d2c9881b6f65ea1e7cb993b12676b3,-0x3507e11cca7ee7629e419202e3f9ee]
def m26 : List ℤ := raw_ints% [0x0,-0xdec9960713b2536b0e4b8afc0416b1b32faa13f8c925c18757b7278000000000,0x1756fe4547389faf6860457182855736b50711a3735e9c9c93cffc243a6b438000,-0x12e6545cf8b0c019e367e2a54f3c397577ee3d7cfca46e8a24c4ecebcbe9cfc2000,0x9d8e5413a0d8f37d49c1fc1cba0494ea3386ee028b752bb3b8bb814ea670bc7c000,-0x3b5aab371a1e28c760e9d4018c46c62cfe1ab92ee7d7fae45d9032cd6008d5c3e800,0x113942adeeee81a9cd5ef6b9550f6eff9120d48fde0b89478922f5215007d93513000,-0x40155e3e7230481196b1335d5cedc74e374b3e8b791c25d7ef47da3c5a36b16682800,0xc442314847f420e86e3f786547959c9bd75cbc9e51aa6d12ca490af638aa629f94000,-0x1f84d3dc2cc79339475a0b6430f6e690e98f7c9e23083df00537a35c93df68d879e200,0x44ec7a1b97bad5b91d9793868206b1edabff266bf1c578ebb269707b1d82e1725eac00,-0x81a60d1c0beaec58293269b479e7c45cdc16188864b0619a3514adaafeb76c48438200,0xd384b68a34712b2e94d2e7c9a5bb17c746c2076b9f465a766abad8d9fb2e9dcaf08000,-0x12d35cb30d24b90e7a6f5dcbb0193272df449086cddba4adeae8d11ed2026ebaafa6400,0x17839c7041026a65999ede41bef9ab2e52adea9438ec929d1f7a8bb9722f758ce899800,-0x19db1713ea916eb003cb1f1f81b6f93ec112d845f1d8a09b2ff4be092700d97ca87c400,0x19186c96f78c6cdb3f2393f944f408e23c0d5fcf2d6423b5b15e75d643d4fe74d34c000,-0x1589ceea418b7d07b429c6de1eb466c377c137507d8ef6bca1a31335996de7df92dba80,0x105cc673a3e87d83ce2e3b0bf8c36ee1bcb03c13517fae159ad165622f5734c73f3c700,-0xb01808be5a2545d86172d277f85083d2eb2b1c36456054a007e8101aa0a33498a7ea80,0x68d4c16436820818ee3723c0384fc0f0f9e5ddaa197b917efc63c8b0a41e525b3f8000,-0x372cba35135f8f3814b25c78e502cbe40c5fe36f43d08a4f510671a32e98f227985100,0x19a119c859acc07bc0cdc0cb1d035b5273bbe06638607296f5574e48839564b370d600,-0xa7b3b4b8bcbcca3f09f6bf6fd11cae99c7808be82c1d704144e6f8db3054a0f8c9900,0x3c307a77d8706de861d8cad502443cfd4f0d1a5481c66b44f7b339a53708e80a63000,-0x12e1fd9abcfdcac24590f9948235e5881161cb461fd059bd6fcda7cf9323cff50bd80,0x52723f0a3376887132e3214db5691ea71bec357097fb96458f039587e675fb42b900,-0x137475c55e5e2b5bccfb45a21d9de92a6b214daf7e16e78744d38d35715c0e77c580,0x3f116026c9c76e08b579a85e0af458028a463d6edbfffd34c0ce38fd0e462cc0000,-0xae11a1f43ff8246fc2bc4ed8a23364ea1a38ed0b0e213246d76c00fb28572d3200,0x194f2705a28117f8829e03d11c8c6eb1c9510dcc68d21622b4b3b79cce3abd8c00,-0x3108cf166c3681d6d8039eb3eb95a57bf667dab67aca51f7fa65ef2ed79d82200,0x4dfc4507864f50fa6180efd6e8df947a4c5dfd2c6ca842d5272f15eb0ac4a000,-0x641010af49015414b15010d808ebf6c6b8249024d3497a9dedb09a6f1f95580,0x656ac9f6f708bea64cdfc72adf3e6887e94d33d6de2c451bafcfd4b410f900,-0x4f1e816844fb0ab418b84a64fba469f725a391b6b4ad6946d00218de5b580,0x2e017a935d8e1151d0cee4254d3fe8b2697b005dc692b1b505309244c000,-0x132585ce3c6335db36948eaf15b58b8ff8c96e5b8ebf45f0080b4abe100,0x569eb127619f28612d0cfda1ac409e6c24357776a18b012f57bd17600,-0xf89b86cefb8e8754f51de7cf5a4da12412e15990c4e882d72c98900,0x19c6c2b5fa06198ff92484df490b758f0ff7050504f454d25eb000,-0x15a5cf8d8804e4f053105d4faa8f1fabf469b9e2d5b2b0dea080,0x7839dcecb4d06795fef1055657e8921e12f120398773bbb00,-0xc23aac955aac13abbc6b0a11f53ce70ae1a740209cc880,0x2993ed8bdff5c7be0cd3e5200000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 23 86 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 86 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 53 indices rho q26 m26 26 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 53 indices rho q26 m26 26 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r27 : List ℤ := raw_ints% [0x233a28e577ee6774fe9250589537a3c3c502b1b2a3a0866c800000,0x3092779d594bbd52807bf8cdf5b0f24edef0b8b38e058e5c680000,0x1fba50d8cb0bae47fe2f2be45643e240c18a8d74772ec3c9680000,0xd103df12da479b081d20d08939f8d0c8150c6c2b52dd86a456000,0x3ce205359f949707adf1f7f36e3cce1cc9a3b3867097c921a6800,0xd59023817b011d0b887d8a446dfbf5777fcba8ad8630fc063a00,0x2499b6c8b07c0af18dc73bc5ef32835b3f518dfe167a375f9b80,0x506df4bdaaeb7438c8e0f075fa842ab422b0b9d52ef2a621380,0x900d4ea2f49a1650cfc3a8c57d0b1ee318fa02ecf22d931920,0xd4b4067f74ce27647d4850fb1a275dd72e10d351cd2ae7a60,0x104def72bd19341411f52aa6ac0de12a3b0a37dc89cf92678,0x10ae4390f1a004afc96a062114b7befa17df169fa6176f28,0xe41d5439095b86d1ccf60dbf79502f9f40e517c6a7330e,0xa2b256c8449085aef5d0be440347670b84305d6e153f0,0x607326968ce498f6d117ff4e8fe70e709fb827dc18bb,0x2f30018af487b0d68c835b6ce3c9983dda0ff7e1890,0x12d79e22a4a48ecba7e7cc5a1e570cddfc0d06ba98,0x60a47baea5efdb68185ef0722718e84c656fc480,0x1844de7a26d4d570bc2774850e1770d16c67d62,0x49933c697264d40dd6d3c7a8b3c4f81365f08,0x9e415b2933ca76431a88f8dd10c8bb12c92,0xd743a0f3048d1026e486c722893d1f8f0,0x8b3a9be0a3b3b1139a934ab3e032c93]
def m27 : List ℤ := raw_ints% [0x0,0x1a1b9f94d44ee5c68bacda49887aa8d2ff95ee5727926caddc4776a10000000000,-0x2b7c86e582b567d752b5ec8eab273cecb7b19b2b674ceb2edfe435fb5be26a58000,0x22fbb5ffb95d251ee1de4b35ceb574bfb5da92927ac37e93e5d9d7717857c88fa000,-0x121a693af21bdbac1be127b47a5c27b8dca62ef14889deb4211ce810ddf18dc0ac000,0x6c58214d227fad3e6b5171121e4237a25a3c9cba5ea94fafa1efe3bee7b12a2b2c800,-0x1f3547823e5528d94f579e726dd51b74073fd18a41fb8bd810f398fe1a966b084d7000,0x733916f6b1026eadb412727e4264fc795c9a91dcefbe3e06e320e54d7dcd5dbcc3e800,-0x15e0c71431fc336fc6f9ff402382de06abded195b3e1f76ccbe25860aba0cd64c738000,0x37bf41a0dccffe939ad1f56fbef90a533634da2f2381fb30b6b0e31cfa1572be2849a00,-0x78d6d046a4dc57110953ffa6274032c12327bced0232c6391731b7fdc805ec34d6a3c00,0xe139a488120a5f916f0315db446f250d52cf5e8d2945d967ba7226c6afbc172ba515200,-0x16bee1af7cc3fd2f1bbbd43ebb1bb310763923068613b64f17add879df1ef24c8386d000,0x2010bf0f4de3f507f70f097365e7a54d09f87a4dd1fcca369db16b8be32d214852adb400,-0x27a10e51eb316d1df011f97e6c6de1d71ea8ee92e27965b821bf459c1e75051e615c2800,0x2b17d3127bdb4aab9c30481e8c4c303017688b724b8a54c944198c554d89f46271c90400,-0x2956962a8ce49013354c466100996322577520d8a770f39bf423c1e8e90dd37882bbb000,0x230b092da0b3e99187c4e46b7ae6cfee1e30c9f431a29fb95687a57588aab9d8ed5fc080,-0x1a46de35378b5f4c8ac393d755dd60a097c5cb831074cc7d4181a971f3eaf0abfcc55b00,0x116ebb861741d1e97c40154404219d3b2ac6ad1529ea3148389f6bc62602a4a24b4e6e80,-0xa3a35a45d6031a75b51e933fa8c9537a812edcaee8f01a01bd2227247e60baba054c400,0x54cd5b333e339d5bb50b98521688f83bf1ad7c4f991656720c35d903d7b88da8d45a500,-0x26bf9b87121c1b08430e8d9dc8c7c06eeec6fc91b5e689c7e13e98b3b159cf9f904ca00,0xf923f8c7b06dcc1106a657bdf1e100277048aea71cff6f5aeba26403138cba83466900,-0x57c3056735540a9dea5abc3becc7102562f334cabad4ee617c09ae79efa10a9e579c00,0x1afce9cb1840a7cf1513f3a0b885da0c3848fa4bcb2cf50021ec9e291d6fcbee683f80,-0x73567fe9a37689d987a914c1aa96429ce1f0337c01b98be50cb4505c6d93ec7d97900,0x1a98eaaa95f2db08f25247be147fe8e1920a9d4897a7f74607546d324894029b57980,-0x541c9c71a99ec5877192f2f1f4ab0ec612bd07ef97801c21299787da1a85965fb800,0xe205d7421cd52b187581023627a10695331625fee15283aeaa6a64e347c81043a00,-0x1fecce907e74f503ce7cdf13e9485b3c783c601bf72f6ee66cecb9aa1922b208400,0x3befe7bd8711c7465a26a59f74aa1db969218a52045944192785b1b4c078bba200,-0x5c1d91979fa66ae9b026eee21459b167033552cd836d0f7038d1a83c2e72ba800,0x71da01d91cddfd6ca10f181c6238ec81ab2cb59bdc4f6123b01ff671573d5f80,-0x6ec15c06afacea66aab2d086a2c0c36291a4b581b31e5e0e2303f7067becd00,0x52980f9016807c111138b2f7103779fb6b8bb3da0364efc770079cbccca180,-0x2db21e7eecaaeaf300b5f851f1a9b4f808c67555c479b75cdc8281bdcb400,0x11ffd5271fee03b91184712c7c4d3adc8c5f9b14e09ae5ed727f11971500,-0x4c9ba92b9398d27ee924279692f312742076cdecd23c9032fd2fbffa00,0xcd71d65795ef201de9f70bc53c954998639b011a646067ced7163900,-0x13bfe3ba484d58e7aa2a239d1c6f6768eebf5adc619d5227ecacc00,0xf3e37f5094a92d0b436fb4549ff4a26bc0b78bef6ccafd349680,-0x4d04eb465bc2f0a828872afaed39430f5c189f2aacdc63c300,0x6fdfc6dece106e98dc97caa46976a1361e3c407e1a95480,-0x1537e9d36fd402e0e9e8083000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 23 88 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 88 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 53 indices rho q27 m27 27 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 53 indices rho q27 m27 27 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r28 : List ℤ := raw_ints% [-0x5c7c9b08d484571fca8317cdd64b3ae51316da72a7557461f400000,-0x7f7a0b330d293925210762f0340e3d1d9919305a03d0e2bc8440000,-0x533c90f6a6da08d07f09db503078c7b34de6cea60a8ffbaebf80000,-0x2241d010e88293db501464532203ffcf4e43c0879f3057f350b7000,-0x9f95d62a3d8b63c75b0a91b73cf05cf0357f6e85b4545441d63400,-0x22f84b734b9f6fe219dd1bf6a65f8fd2df7dbaecdb96e1c3e5ad00,-0x5fd737919da4f517c5790ab7e0921aff37b99b460550c2904cfc0,-0xd27e35c80cc81af666ade171ff513ebca9e28b9db11e12713200,-0x178c668f7c5cb3de42afb29706b7954c93434381a2e1c8fd82b0,-0x22bfa8aa4c2be6ba3642a3234ea09eea9b1369ae322551c2d80,-0x2a9697b3af3be83d87b37cc36bfcfd7e4ef0708bb0fd503024,-0x2b89ea4762c4e6abd4cbaec08fd9902834632a563cfc0cae0,-0x252ee0fbf6ef9b7ad44337dc8d92e6be24a4f83552f538ad,-0x1a7f371909cb8fee5fe2d8c79545dc718dce9f355f4f26f,-0xfb177bd61636cd9b70cb19b216a10e0095333372ce8c3,-0x7ab894e398fe4a7c4e31d2fcb15d5109fabbcf866ab4,-0x30f31567067b600678d156bdfbea1193787ad2ceeb2,-0xfac3e114ebb6ad19092ba2fa71686fc543db71b4a,-0x3ee41e7a3281bbd82e5d3bcdb4312fbf3258908a,-0xbe6517a97e6a1187600ae7e52cb810a81cae34,-0x198e568e40871dbb782a4e3b4d56566876ac1,-0x22b417dd09b5d4176bc2473be7e047671ff,-0x16676b2372e4ad1f9256a762847991dff]
def m28 : List ℤ := raw_ints% [0x0,-0x30f3cb370e13eed445e41949dfe5fc8b9f391ee36a328bc5fd05fe6de0000000000,0x51098d4ee1f2803be447ac4e558f8a44fa28e63e92d81b00bb44b42bc44a60bf8000,-0x40c6afb276881c9d62874fbdc34bf24def4768387e56febb42a92d4914c71b8452000,0x214c537153d572fe3f21cacbdbff6354e4d4cf1c99eb7eff5c09dbcbdb5a7b1a65c000,-0xc5e84df92a62f5c49e0f496e4ee8d033901fc17c42773f6e2216d456f3019dc4e92800,0x38989e0e77d5b255e6c7a6b18bd2ad1688bf2feb2ab878ccc11ebdfc4b191bfcb5ab000,-0xcf639622e84041f3a57c22ef465722dd3953ce0663bc51b2631db1efbe6a20d38816800,0x2711c66c21df81d9660b2d1baf68eafa44b428f4f284afa41c0f4748a721f6b7cc5f4000,-0x62bc94b1e5b1b89b824c7fd8c5d665bdad8cc27abf4c749e9cf07002ee3ea120058ab200,0xd430b2db21d9dcebdead4c334d04d4775e86eb3c5658871142c25398e0fd5519fce28c00,-0x187f082f57b32994a7fce512385543686174480218ee47be4b9370fb6421d85a555a91200,0x2735b18e0c5755ae78b812a8da62c0208d5b0e417b0ac239531edd45e0f79304364cb0000,-0x36bac539a474e25a615dde2badf8139ab5abd04a1d91cd361c255669dec4bdf6239b15400,0x42eff642bfc0646551589109c35c04c4985be109c0a03d42d3fdfd196635517a844cbb800,-0x47fe4eb99f154c15e4e91e77699c1498af331c12ac1acb7db0036d9e3ca8d41b34a8b1400,0x444460b51fe3f562ff7a2e7dcd1f9f6f0bd9357ed136321f79a9879c9d633cc8412b38000,-0x392b31417e06d042ef79b148f7208772b8b4985d9d829697f4595223c13895da5e6d69e80,0x2a515c9c6b9ee22795e9b00969fcde960aa620662364e62f2a6be2dee466d6d566d589f00,-0x1bb18834a332b2a6ebb043ded8e3ec1d6bde95a72022c0a0f19444dfc04a604f68ee87e80,0x10037d92aaa3fba1ff8c13928e480e6b88cf1e9e92437196d9908bd75645a1fee4d106000,-0x82c0af856c3fbfc353e683438a7f4e755387e8b4df1ccbcec4ca2907783daecb8651fd00,0x3ac6417ca84418f7b682ef10dedf3c5790042d683d62a83880d1fe068210f414a9a3be00,-0x1735d01504d4f11dcd2590ce48564e7f6b644ad58b88c3e1deeb0261af7e733c8d13fd00,0x80664f2210fe37bbdb98d1bf60645355f9822e7b00cca06e22c3c1bb518a310ca7de000,-0x26b457b8ca26a119fe89264c30f1eedb7aeea5a0c470b615c9d7302245a21da2b59f580,0xa1e816753ba90b79451f177607536f11a8f929304bc40e4b1f6bffcfbd877e4e17d900,-0x247c81f1245a1ecf9e269869c590a0414a58957795215efabf0bf92bb89f35c7e6f580,0x708e4e68e1e6f0d34fdfb7c8a768715c1a3e533b20449bbe438b408d1813c907f0000,-0x126730aa4b512be568f9289dff72b0391f87b22ea9b88656d269b001a7543d07e3a00,0x2865e21758b1dcb48af3e75bea982e27ae5b6b2753089a30d895db52e242c1bf3c00,-0x497c161bf147bfaa789899143a334815fe3d1299a2acd2bf0979cb21e4632e8ba00,0x6d1c88b7c4ad319a6dbc259913039661c3bd660ee3303dd89a24d2b2a433c40000,-0x81df6321ae73e210eaa1d62d2594e9d91106a53334b9242fe06326306289a6980,0x793a791513a6719922498bf4780fde543fba502da8b5826955ec2538b00d5100,-0x5663a5914722f42a83f46fe6d45eac6c3eaba62395fd6de91828a33fea9e980,0x2d75ba5688c271d92274df5ef61a2d8515e26bc5c7cc1979bd69b23249e000,-0x10f0f7d917e0b66b903fe54a21b4ac0cd951e3bfacbf95b2586c8a909bd00,0x43cf329be0328f866883fe1593e20a45b132e92af6df2ff6e39d8a03e00,-0xa9dadae1ebadbd568ac2b98d7efab0443a2f65479fdceb5831f053d00,0xf225dc546424c01ffc0e45c1a56ee28d9bdf6cbe620cf6e87f16000,-0xabb7fada8b750e1f24e93728fdda630beb8251258889c5935e080,0x31544d0bcf3755b577b168232ff40325d876d800154ae668b00,-0x406bf9386f786c8a05b3ceb17abfd8784875ff62628a0080,0xad37e0761c08e3a96f23e08000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 23 90 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 90 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 53 indices rho q28 m28 28 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 53 indices rho q28 m28 28 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [-0x16676b2372e4ad1f9256a762847991dff,0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r29 : List ℤ := raw_ints% [0xee1e9bff30519c1c643bdb9995fa96cca29bc3f851fa4fe854400000,0x148181b3aeaa7fe1f0f14073a5b602ed3d692c31e748eeb3412140000,0xd627089b31cca85c81057301efba5b6b0bc4b524ec21855ec59c0000,0x581a4738f3525e1baf47eae4ba14e308f702e48f2849767806133000,0x19a40179160373d2f36d07d2c532f59685869c11e8b30f2dd4b5f400,0x59db8af16e55bdb6de1df8a5bccd5d8b8cd87e00a48bfdcfd6a1500,0xf6267972a907eb63e29f2f63c3b66985004db4b61a1872d04f2bc0,0x21c55ad68f08b243c405f9fe04a0fe04604e6659f075fcc80043c0,0x3c6a4456f7fa519725483e0acd6cec4a6ad4dc49f33cc18458ef0,0x5918c540ab1b99124cf9c7a70693550b364d7e3bce6837b05a70,0x6d20a9d23311a7ce1e5c45fcc6abcf2f0e8ff22b251dc827894,0x6f7c6cea74098ff0235b2084f0620e0362ba441f4dacb24794,0x5f2416f8f883ce886b74dea39d3131c5fa1d8615b5cb8a429,0x43be68ab3a744ba554a1725710772be6c39081d398a289a4,0x2816726363cca1c540faab67a48262cf63dbdc987cc8830,0x139316db196b812b71474d4673c6d240ef689ec01d1a08,0x7ccbfb93ee96c2f51d40c7898b4f8baa8cca8a362256,0x27ea073915447b2ddeb36715d4674a0e998c2422378,0x9ff9c027723ee719b4ce4580a6ec2501a89e1e1a8,0x1e3ae7d1cd73ab346f375afbb1e52847112f31a4,0x40d4e3acc3fb2f48a98712f6bfa84100530619,0x57e6f9ab97534ff783a8ff1a8f8d1b5dfc74,0x38a7206796a876f790ba47f44433e9c24c]
def m29 : List ℤ := raw_ints% [0x0,0x5bc91d073a655fce030baf6a83cf3985ca8b19ea671ec6133a6b3d0e040000000000,-0x970a06a2e6f9b9f716b2097401d9f4d1e2313bb13c6d7c5165abc8ed298ecf5b18000,0x77fb711c096baa5f81892613e34101183d4b5f6bf6170785c7c0fcd1dda3e1dfd4a000,-0x3d473f490615c9284917534e24faefb0757d5c9ccf91d74ea60e77b46673874c160c000,0x169c127415545738216eb582cf1770f31492d43950a39597fb800d4e0d1fd363722f0800,-0x66b99f0e15c74cdd1f83598e49b6ab3176f0db5bc88eaf445d7d0daafc1e03bf2058f000,0x175a90fbda43b42ab07465fd816a300c8a50321b3a97278086124a9b7138b52e88cad2800,-0x45da5f6435cca461c0142c4ea818e42087a0b21359496e9cbe5b175bab8c854d520178000,0xaf1debda707eb45f0af69ac9855d7c2c1d69031ee823e813258b823f87764a536d5a52a00,-0x1752c5a98476d21eaf7ba52b3abab6be3d1277c85698bb574ceb2230e9ce2c582b595a9c00,0x2ab38b1db0e9a7aa4697dfbaa7b598d66309d65d2d210574dd217a1d02b52a08f31275e200,-0x43b7bd77c8081478d8ba65aa23249a112ed177dd12d7c5bac28001330797dc5aa8c68ed000,0x5d9a6a11be368e495a8d20c3dfe3b180ecdeb44d731d54cf315bde196f265f7a8884562400,-0x714fd4a3a9727fb9c6bcad6025bfeb254e9f13eaad8cf1510e8fde564a346fc0570dd1c800,0x788efcb0406878625ff6ac86f1f648df6855679176921cb9b97200f2838213a63d0f185400,-0x71052f1fa5b1296544aba49a0a8c478f4431e3132e7aaef26705e550c9481f89876dbef000,0x5d82c3f37d0a606ea2225dc850771c7065596b7f0a336a868f9d51f9f2a891cc7d704d5480,-0x44573dedaef983d8fb9254a1c4ead0c4baa2fcdf4412cb92b953ce744276783527edccd300,0x2c1f3e3600b0af76f9566f7a305a0689982eb15971c0ba2c339c90856668efc233e6fbc280,-0x19263c9ce2fd25bbf3a0d85a1040ea4f028385f5d09fac901e3917d3910c0fda2e80378400,0xca3b7b6c5c17b292a1968984075e7561af5f4ec8fc2326e26aa061244b6542513f2b0b100,-0x596fe1f0bf9439877c83a2536e3204b7d670a1f8bffa8cb15942fa6afd65c2679c9cc1200,0x22b5de844480e87b9b3e52b114e658b5944977e4b397f61170695b45d4178848359d4cd00,-0xbc7b91665f299a38121a18e66dbd35c1743c493e05740f41717e56b25e10c435c340ec00,0x37b1e3575c612d7aba0d2f4f8e61d43f79ffb19bd331ee45935379e34282f65c264b4780,-0xe40bd28a375a6a8055635f00e43d58f09d0ca37c2d0a37a3ed9ff4f7fceaeceaa04d900,0x323866dbb04705b45e5e5fdd271c91ea61d07ec3f2d63e4dd3751a93449511e3f9b6980,-0x971df7096bba41a41dd83bf1d5c43e04df70942d0e9768424059558f55d388d9d8f800,0x180d3a405fd02e12a7a1b01025f549d43fdd87dad601d4b8dcf6b8e3f5b387f3300200,-0x3347262b0b05f3640feb94107c775d7df4dbfd0f947696b95ec9293543c2b81787400,0x5a5bc9e745f7cff3cf281b1903d36235cef517ca172d17e94a964fd47dae41643a00,-0x81986ff2bad7bdd13bdff969ecd9cf4c90fbf6f66384befe1aeffd19f4007ccc800,0x9483cca008a41feddd9200afdc55394962168bc93d9efa18e32ed59036a992c380,-0x84fb5928a247f20bc5916e4cc9f5157b021e896e2c98319182789a19b85084500,0x5a86dbf725334e93712300dedd4c040e79ec97f8e2a90541484f21d949171580,-0x2d4b0a3dc2071001864481e438bae8561168a9f341bc695db7bd8009aca3400,0xff6a4061453e363d942ec30f39c850ae8783bb87fc3a04e057c9f025a5100,-0x3c11226b3feb93b573b19f5494cad24ec15dd22e52c40529daa73584a200,0x8c7d33fe7c180da0d23af4f3675151f4810a228ceb0b035ec5ffbeed00,-0xb99538f5b512997ca693d38965638bd7a3147b9b5e20a8f814419c00,0x78e4bccdae9ec86bc6f56470c3ce9f3937fca6067e1d70a36f4680,-0x1f966622e56861f7e109cfe77053b64b64f318b59ed13b361300,0x25165a2f72512425421c59af2da109237b5d421820f49cc80,-0x585cb5dfac08c26f497d38c0000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 23 92 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 92 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 53 indices rho q29 m29 29 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 53 indices rho q29 m29 29 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [0x38a7206796a876f790ba47f44433e9c24c,-0x16676b2372e4ad1f9256a762847991dff,0x8b3a9be0a3b3b1139a934ab3e032c93,-0x3507e11cca7ee7629e419202e3f9ee,0x13c618948d3dcce6135e38e172f52,-0x734339cd357b04a1b82bc404fd5,0x28efe6dd838590c5039179b749,-0xe235de8befdbb55c44cfda74,0x4bbf10338cffd1c51282f38,-0x18820296c5005e466ff28b,0x7a1a8efa746cb5a76fdf,-0x246b7994c7a008d3eda,0xa58aa937ffa9a2ffe,-0x2c7bcb0e5becf421,0xb35e686fa39455,-0x29f0a2921a920,0x8f8e9405fa4,-0x1b94819397,0x4a2e58ab,-0xa80086,0x12d2a,-0x17d,0x1]
def r30 : List ℤ := raw_ints% [-0x25a21c1c969ee3a80481aa6895ac2a867d9020635db517e4947d000000,-0x33d6279add35071fe2cc8a85b3e0fb66d023a14c2a0273a0c73ed00000,-0x21d2ad8665e9d954ac145743117eb18e874560c67bcdbe22b30f6c0000,-0xde8e23eac5a28dfc7baa2df3b87cea4034a751e900273dbba1131c000,-0x40bebd95759b55924264cb258235c75f59d29c02df4a3c7ebc01b2000,-0xe2cda12a9f78b4878328986fe571a3dbd1c4d8d96bbd299699ba6000,-0x26d027f5f8267106623593762aced8eb33ea20c4d874675203761200,-0x5528b2012aecfb33ac6910b925d420b32b472a600c9db1c203c0a40,-0x98447cb08010b6e7bf7f81bc66712fccfe8bad837760db583f1500,-0xe06e27ed75ce21d1b1d998bc2822109aba523ffed4f9974058b90,-0x112b8f451f52821058159695945cdf953001039f6e24b85250fa0,-0x1187ab754ba6ecce85f9f8ff6235f1752381d8c89e31a411cccc,-0xef315504a710700e3b8888a6b39540678eac32a7f51beac7c0,-0xaa2fecfebad99e67001bae259e6a6d83d8b93377540c5e1cb,-0x64a0e0ff42a938abd6c68897d053be73a5113a6d13897928,-0x311806279a0661ec59b1ae3c92c15c16a6d751ff4b1d58c,-0x138b4417c87aed1b230fe9bb51cc1e99701f818b5c6300,-0x63e997a6d1760866fea2957c02ffbf7f99cf689c9532,-0x19002efe4eb79bce57cdc38afcaeec50f35986610b0,-0x4b7fe1c950f382416d4f01b8915ce18d1ef91ecb0,-0xa1b55e06f3c231f6d9630939bbded975eaa2580,-0xdaf23a92c7e3cd002ea484015599d68b7242b,-0x8ce50a53cda431d1664fdb968df82aaaf48]
def m30 : List ℤ := raw_ints% [0x0,-0xac19166d8d7e13a245b5e8e7b7248bdadbc4d0978159b3640d89127a4780000000000,0x1198e823e9fdabdf399e4ef49900de6df87ee8da4e7c94ea7aa7df89dcc29d7d51b8000,-0xde4fd609ab68f9c4fdfd41c42f916fb62d0cc6d2a493d7b135eec65f84afa965b162000,0x70d3842525f5a391ba8b419f7f156128135c8be7ca51a381a450378b0e1257e48ff3c000,-0x295b0f9ebc39d0811620c1d8fc26008f7c70f096815d7252e5c1710f3a5635673b5286800,0xba9b810485a92c27e893f5e646a66e01ffc2ddb19e006625c4097bd83ebba856203103000,-0x2a1ea130eed6a472f268c9a3e70cf8dd3b0cb629f13cebb0a8c168c1c0205a0734933ca800,0x7d09ca9909d2ba0fce174af78af058ddca689db773baa9295184a8b7065c7a62fe71e54000,-0x1370002d2a92ef41560757de8160488e31143fcea3903d005c5035f0871313f10c3ed2a0200,0x29147f94c2c30d4c5bae0c8cb8b99cc4016b63d26f930e2108ebe36c1f8d87268ff54856c00,-0x4a8f9cc39918cb49415e2777d55957be5ff214ba349542bce8c48ce08c7903b3a30f5492200,0x752b0f7b82f39f936110972667f46aa1da07fc0e368475ab29f7a492b55f06e7a4ab46d8000,-0xa068a60db6176523cd9ecd2823acafae6eb931a33b3864dfaa22400bb8cfce9b29e97ccc400,0xc03ab42a85b101938835f858bca2abdfa9dd50434c4c6dd2b03345e7ef62631feceaa08d800,-0xca5a20c1ac143b4e0ab1f61ed87311720a00b67a29895d7b4f94eef0f99f5b332efeeefe400,0xbb929f7a10f8c3bca4ea9ec41c2c6fcd506cf6228f950f95a5bb3e3e4ed6f4b3b142d184000,-0x995aa598e38a8fcee19f1da389a9c81e232fed680c4b8084bbba6d477dc754478170acea280,0x6eab368ab07515d06a7203f7921ffd6b63a25e7292a53779303ea51913b8912139a63643700,-0x467f78c19933deb03b4565165b03a5f9ae6ff0c9e2730855177b8253d518aa9d2579dc53280,0x279d5d2ccd161843dd8d2ce69c0d4f1aed1d9c5bf5d2d619a9c289edc653a9da76fbe2d4000,-0x139c0a1ae6f163c8aa30f9af04e6f31431a329dcdec1f3e2978c9bc961f02c152fe7a3f4900,0x888713ab4980d0dbaadd1c080822d1357fc809ef76ec1e180458880fa039a92c663b926600,-0x3413b2dd6a599ff963002d4a51dcbf709124b7771d7431ac1a3b5cbe1f4a1a13151ca54100,0x11597590c66ead65017ffe330cb7c1584f05aa0f4fe7e677654c95f2f3e1a528b856431000,-0x5068e1161c3351af777bc7f45112e24d13560bea4e97618c95587aaea7303d0771ed4ad80,0x142456c27733f0b7c39b35b18b4adf8c0751f5af854414d5a6e3fb2773d0a690d3c807900,-0x455a12b55f647a328079dbf620d7d90d33fd717abd2747598e40ef8787643253b2026580,0xcb8bf00e53d3e1877af190e2b086a1590731903d129bb8be30b4d4d364e7aa672fc0000,-0x1f8873fd13c87e437ae407e8c71f4d8cfb385a2bfba21f6aed05f6b72018b8585bf0200,0x4148e0adf1d1b86bf4ec879912d1e34ddb207b75f6ddb54e5a0ea6c6caea9a8e016c00,-0x6f6c86535e2db30de219833bec5a7999efc3bb7171563e40761359c0c76eb58889200,0x9a54e805d9fa3b2f83513e127e2b910278a02fe47566e6cc0fbbfa491af137126000,-0xaa3d29ba2fa459f06430eb6529542d90b7ea17d716b956f0f70891fa83d11879d80,0x922e4e33b1e81ebb000500b969814a3abafeaa6b081e7af09ad70b629478456900,-0x5f07d872377cbe1428eaf3291c3c641bd275192213b74d0f7452c1c2fbf80bd80,0x2d30ec9cf8410c02a6b1aa0fb2a738a33dc2da989e2fd8638153880d52d50000,-0xf0ed585226825944392a0a598f40c54fd63cd97c45aff79cbdddfe169fb900,0x353eebc6482c64394d87f100daeea6dc91827cffa34cce23daeedaff3c600,-0x743e51ee7b487c84f69360925f9d024dfb1ee988ec9aa4d582db2025100,0x8e3eb46936eac2d2d8938a6bb7d3be98bf8fa91d722b7c1d9976d9000,-0x551a3c7f972256f417fb91709bcbdd689eb24153d1c9070fc17e080,0x1438e48b2384c3fbc864694b778f70c0c66dda67bec744b745b00,-0x15587d74937fe96b15a0c63f4b3ab202e526f758c5aefbb880,0x2d10fc1dccae7ea9aeb0fd200000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 23 94 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 94 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 53 indices rho q30 m30 30 240036838436952761448388034322432000000 30=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 53 indices rho q30 m30 30 240036838436952761448388034322432000000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_30
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<31) : intPolyRF (mz e)=rfPoly (C (240036838436952761448388034322432000000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U7C30
