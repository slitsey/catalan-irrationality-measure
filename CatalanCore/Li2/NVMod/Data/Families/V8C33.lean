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
namespace CatalanCore.Li2.NVMod.FamilySource.V8C33
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,8,33,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
def num : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x292f6c281d95c4681a988000000,0x3c5cd758fbe1e1753ae9ec00000,0x2a2078483a42584f65e1c140000,0x12a2d8680811ec20ae0d5320000,0x5de67065a4e21be390829bb000,0x1668ebe21a69c108bdd81a5400,0x4368795676d046c65cfcabd00,0xa3e55ed3ab2a50dc512b4fc0,0x147f4085f4a3c9e6fcc638c0,0x22301ef59a28db1e97bb570,0x2ff7538e2381aac5f4e6b0,0x38f68157b4b3d5603f2f4,0x397c8f21d4b7184298c4,0x3165f3e1707ce86f931,0x2425b9b4b02969c6e8,0x167c4f4ca203821ee,0xbd892ce291976ac,0x540ed7c1a1c6ff,0x1f1b198f410e0,0x97c1bcb2c08,0x25755c575c,0x74bad37f,0x1143308,0x1d236,0x1f4,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0xb,0xb,-0x8f,0x1b5f,-0x8f,0x8f,-0xa16f,0xa16f,-0x14b1f5,0x10d0971,-0x4e0139,0x1182e3,-0x242f7713,0x242f7713,-0x321567b,0x28b1643f,-0x569235,0xa9aded,-0x3cac037,0x19dac177,-0x2ef7dd47,0xfa7f46d]
def rhoDenominators : List ℤ := raw_ints% [0x15b1baef9df00,0x2db5afcca0,0x28b396c0,0x48a8420,0x189a80,0xbd420,0x219e40,0xee0,0x1c0,0x4fbc,0x1068,0x8dcc,0x26490,0x49bc,0x888,0xb3f4c,0x8e300,0xc160,0xc1a40,0x2860,0xa180,0x9efa0,0x10b2b40,0xc007160,0x3601fe30]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 33
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤32))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤32 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 33 omega8=padCoefficients 33 (omegaCoefficients 32 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 32 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 33 omega9=padCoefficients 33 (omegaCoefficients 32 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 32 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 33 omega10=padCoefficients 33 (omegaCoefficients 32 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 32 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 33 omega11=padCoefficients 33 (omegaCoefficients 32 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 32 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 33 omega12=padCoefficients 33 (omegaCoefficients 32 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 32 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 33 omega13=padCoefficients 33 (omegaCoefficients 32 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 32 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 33 omega14=padCoefficients 33 (omegaCoefficients 32 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 32 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 33 omega15=padCoefficients 33 (omegaCoefficients 32 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 32 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 33 omega16=padCoefficients 33 (omegaCoefficients 32 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 32 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 33 omega17=padCoefficients 33 (omegaCoefficients 32 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 32 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 33 omega18=padCoefficients 33 (omegaCoefficients 32 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 32 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 33 omega19=padCoefficients 33 (omegaCoefficients 32 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 32 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 33 omega20=padCoefficients 33 (omegaCoefficients 32 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 32 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 33 omega21=padCoefficients 33 (omegaCoefficients 32 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 32 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 33 omega22=padCoefficients 33 (omegaCoefficients 32 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 32 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 33 omega23=padCoefficients 33 (omegaCoefficients 32 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 32 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 33 omega24=padCoefficients 33 (omegaCoefficients 32 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 32 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 33 omega25=padCoefficients 33 (omegaCoefficients 32 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 32 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 33 omega26=padCoefficients 33 (omegaCoefficients 32 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 32 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 33 omega27=padCoefficients 33 (omegaCoefficients 32 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 32 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 33 omega28=padCoefficients 33 (omegaCoefficients 32 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 32 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums29 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens29 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349]
def omega29 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums29 omegaDens29
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_29 : padCoefficients 33 omega29=padCoefficients 33 (omegaCoefficients 32 29) := by decide +kernel
theorem omega_spec_29 : coefficientsPoly omega29=omegaNumerator 32 29 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_29
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums30 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens30 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384]
def omega30 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums30 omegaDens30
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_30 : padCoefficients 33 omega30=padCoefficients 33 (omegaCoefficients 32 30) := by decide +kernel
theorem omega_spec_30 : coefficientsPoly omega30=omegaNumerator 32 30 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_30
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums31 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens31 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384,0x3c1]
def omega31 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums31 omegaDens31
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_31 : padCoefficients 33 omega31=padCoefficients 33 (omegaCoefficients 32 31) := by decide +kernel
theorem omega_spec_31 : coefficientsPoly omega31=omegaNumerator 32 31 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_31
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums32 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens32 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384,0x3c1,0x400]
def omega32 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums32 omegaDens32
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_32 : padCoefficients 33 omega32=padCoefficients 33 (omegaCoefficients 32 32) := by decide +kernel
theorem omega_spec_32 : coefficientsPoly omega32=omegaNumerator 32 32 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_32
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
  | 31=>omega31
  | 32=>omega32
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 32 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 8 33 at hb
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
  · exact omega_spec_31
  · exact omega_spec_32
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
def m0 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea820981000,-0x162491a67fccaf8d87c34e9d884400,0x186e72a8a688d24df9af4cf094f2a00,-0x117df759bba1be3076849f6247573800,0x922d2092489bfc09c1e781af4831ce80,-0x3b5d4546f9b3212a92262d6265bc5c1c0,0x138308e0ec069477d7315bcb85729afdc0,-0x5559259f39d11bb0f5d0181f2d0b4658e0,0x13cb7de364b298a259509a53b318bb89c40,-0x3f3fdc5d4f6b579e0d7505dbe4dc1fba970,0xb004f791ff8c1b9bdf79f52948afff16f70,-0x1ae82a42d49cb40095eae0afa186a89f5098,0x3a4166723168456d58e131a67ebb6ee2ac48,-0x704cff877fff807af6eabcf2092b0f31b8e8,0xc1a93852084e8e2aa3ccccf9f1097e86e038,-0x12be403fcf97f56035a111c8188bc0a08738c,0x1a2474f46ac797133a64b070e6a10501d92dc,-0x20ebbd6f41419e719edc1e14178d552321fd0,0x257fad0557a1f34de4d41c1a365e58e9c4dc8,-0x26afc5917e2d367e8d44d416a610cb4f80fd6,0x242e5f709e3b1905ec182d45a80926bd73c02,-0x1eb0366649262830e79aff475ff6a6f784e2a,0x179b75508bdb58adfa465d592ab4bfd7c0dfe,-0x1076c67ff48c3cd6168b3ff8e8eb62d1b3f3b,0xa66caba911b2e60f09a30a1efe647c82c3b5,-0x5f21db49b08ed47df753172c88ccad793573,0x311ef5668925f46a8d9410625fc8c09a7e9d,-0x16dc901c69c9abae45d8b0eefc73688241cf,0x990ab423b418b7dd13463e933c800962221,-0x39601dbf28d616f34806de8d859cdcc4737,0x1332d74ff3e642fd88d9abacc09e562d7d9,-0x5b4f3aeae6028942819dccf2a29654bdea,0x17f9e59262b7b132b93cb8d47c51944dde,-0x586230600305631e946723fe5e8148afe,0x11b902fcb83319f32ccbdc15ca76eab3a,-0x310111655d9792bfe99ea00ab696fdf4,0x7362db5e2cec8436c339152103d0e04,-0xe3f4974a9e099984bf79c06808f3d8,0x172def2f81d1d58637105baf660a30,-0x1e52764b58aac239fa65f31c1297f,0x1ee761e21c05fabb4434be7dcac1,-0x178213c07c3cb9981900a4f3cdf,0xc8e33231b8586f690d558e5e1,-0x44ae726369a46c0208e880bf,0xce80d2952d32cb38d7b1a1,-0xffe81d589df1df77a58f,0x40cefa3e7aca808711]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 25 44 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 44 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 56 indices rho q0 m0 0 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 56 indices rho q0 m0 0 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d50413020000,0x2bc53272d55779ea86683f5f903a800,-0x2fb8e34bc44ca237c790ad2dbce72600,0x21c164a621305bebbb1c77f7520c93400,-0x1169ed9a89e1e4dd3a8d6e6c50a8a30f80,0x6fbc645abb12ec6d2e941f5549e8e59d00,-0x2441bfdb4d641bb7559ca4d134770b92c80,0x9c87c548ad0d699d1936edaffc5ab2b4600,-0x23d28120ee4340108b541fb827d23ed83ce0,0x70e8de894e83af8700662011f371c2de5640,-0x135defa4da9378cec480671958d9f87336aa0,0x2eb29f4e596e985196a2d1689531964c0a580,-0x63a43399c23d7052db410c6488e02c4655760,0xbd3cedba539451e666ae8f88005abe82a49c0,-0x141641f6c82e38d6c163114114182350931120,0x1e9f44ff2930c34f1fd1a6b5adf5a1448b0480,-0x2a07d02d322a0ef351ddd2195f20f4952de938,0x341037761bfa95b658119213b166cf81d5f890,-0x3a4eae5f2060f1e1a784bcfac63929d6811328,0x3b1dafeab009ccb771a2ba7da9973fd2dfb2e0,-0x364e2611478b19d52ef4fc451480affc1e6af8,0x2d37d071abd16246c80f04e15f0d9e40e590b0,-0x2220bb662361eb423936c89302a9e68b7c3928,0x17565b395fc15693b7dcf9d612005a7102a820,-0xe7267cee9c06fb76650a98dae876c427e45f8,0x815ff82fdeaa9214d7c6977d5997941e123f0,-0x415b61f9d020172b25c5e9b213e418d9b2728,0x1dbc136d7e5605ef98d441026fafe55a3b840,-0xc26620477c04cb9b19b4fc4d0a2562a9d4f8,0x471a95bf87db68b516b133733a58d1e85fd0,-0x172fb1e20a3474b93f40f352a2eccf84a668,0x6b55406ea5464a179b9b4980df8906534c0,-0x1b64ce5cfaa35c4d02d4fe7965007c635e8,0x62000494f46ce8e8363b404ef696208af0,-0x1309990c1248925bcbbcdd454685d571b8,0x32e528330d0c432fa68c601e07a740f60,-0x739a99cac79dd18d473af618bebcc728,0xdbbc20d3ac382ecf8adf13a505ab7d0,-0x156e48c7c42c531154c639ddb7116b8,0x1aca65d6175ca849301febafb47ea0,-0x19fa1c8ad423eb835c86cd01d6208,0x12b252cf67d79a37ac66c64abc50,-0x96202d9da6961b8910bf5fbb58,0x2fcc1327ef5c69fc78b278600,-0x843db1e3e7927fea5d70e08,0x946110c0e93ccb3478ef0,-0x214c8a3c17c01075418]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 25 45 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 45 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 56 indices rho q1 m1 1 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 56 indices rho q1 m1 1 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa08260400000,-0x568ac23ef8cf47c70325a8e5d7ded800,0x5d428925c4e684d5accfcbb3cbcaf8200,-0x412f783f2373fa3a263cbf2b0546591a00,0x2138fd2caa42ea595480d9604f875aa2680,-0xd28dfb31755f31846538ef8817cfda87880,0x4377569f3e8213030486d47d63afe7e4bb00,-0x11f8bb2149694702df3b00d7b5c784eec8700,0x40f2551b4774fe91719e168f8dd1c712de420,-0xc9faa7b5b343d79af8c38435b61506ecf44a0,0x222c3908e0dbc359449f44267d71097cd240c0,-0x513ffce77692640bf6be53142607e12bfdfbc0,0xaae584ad70804273a5a1afe841aa6178db67e0,-0x13fd453f786acd9e7900c3d1f6f8bab54d84a60,0x2170f712c4d981e6f96fdfd7932a706c52def80,-0x3232fecf3cb43d280b91edc975a9f80c913ba80,0x43d14a2251838dce3f838ee6a01385ec7b213c8,-0x52a632b0d47dbf747fa20efcba44f5b2d4165e8,0x5b066c5f32d4e6e8bf49d32b9100e1ffc1fd470,-0x5ab62e0f7f822506b20e0f1d9378b1aff26a730,0x51dd5397a4384992f2d3f7c3806045be3c90098,-0x42ee188cb27b0702b554656ee395422acee18b8,0x3191dfd9f4b0c211bedfa7d0a94f27072a8cae0,-0x213ddacae3e0cc6b39e6f6e7abb818ecd20b6a0,0x142aa1c2dcd62f7f9c85e6814f71ac278877b88,-0xb0da4224826f9435391b4285870c53e9db92a8,0x576b80eedb78961e63d35275af092e7228dfd0,-0x26e213d2a738b88a37ebbc698f75fe37ffdd10,0xf84a258ec3fc95181031144fa5a5ddb5a4318,-0x589ba08326275f4b4d400691a527713bfbb38,0x1c28e185cad77e205d996de102df5ca6f0900,-0x7ee172c34825f2b5b004350c1daa3dc5b840,0x1f799c8da2d5b4112dc6ed6f65f82ee53c98,-0x6d457429a904173cbb50c21afa8e677d1f8,0x14900afcbd76a0e2c06969cfa926e910810,-0x3524dea13dce6e125db7c477cd7d3cc750,0x746cdc4b6af0cc6c953c848455ff01688,-0xd4dc85c35f417d94deed42055d804de8,0x13e7ecc98520cee8b6016bd675f33960,-0x17c5397de8c416d1e96307be94edda0,0x15eaa572334b8a1e92b11495e113f8,-0xeea61810433f0f827b318afc4cd8,0x70734a2134ac345bd5b92607af0,-0x214fa9f552616b77a98cbd10b0,0x54bac32f06ab97c7a2ce5368,-0x5603f0f667c9e05064e748,0x111a5984d728c0514e40]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 25 46 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 46 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 56 indices rho q2 m2 2 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 56 indices rho q2 m2 2 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c08000000,0xab26395af8fd3232d3905376b31ac2800,-0xb655c761ea8f41e091eabd6c221c5aee00,0x7df7a7cd2801c1a8695856f320ebfec9a00,-0x3f7115d0dc30e4c1b23a82cd76064041f980,0x18d399c38fe6ad25fe58600a511f833fafc80,-0x7db69252af60564c58570eff644e8b0dda500,0x211118a928d38c588dd2e1d8f156457fd72b00,-0x75f7196aa308aeb5d1c76bc6c0f71c443dfbe0,0x16a0dbe13371b255042f35565c4631ad790b1a0,-0x3c6f42ab49f39edc21bb67ff9a66d6040e8af40,0x8db868d0536470406d74e7e154f9a55f63298c0,-0x125e6e49d641835dc7ba1c207ee29e9432be4720,0x21e1f1e71bf3cb9fb5ac5e0252ad381d95227860,-0x37d93378625db157db900d04faf599ce634e4f80,0x52912c5b2f6aa6a42dc6876b8939429d68082480,-0x6dd04649a7b6b407511c4e78f439e9ec3b522138,0x83b1cf92f818fd692a4927a4ef777c915dac9e28,-0x8ea932018cc635ac91a603b580eaf8bb0d427890,0x8bc4a799858776ebbc2ba0b79941ed76581d3b70,-0x7bf0e7195b3b4965950bef97759406fe93cdda28,0x6382d06bcdb9b55c928672e4a07925c98a214438,-0x485547a034decbf0724ca43fb70cfe0e637c73e0,0x2f939280badb7ddf536013a42c7a0352342c5d20,-0x1c4a2e8350706657a5f029a37b7f8d9488b14878,0xf2fb17a0a9fd7c254b1312b7fb77cb0381ef268,-0x7589d9a28b881a40163e59981cd88428b4f7030,0x331da408572e8ceaf0dea3868b35b3ddcb3e0d0,-0x13ed41016b05a857f95c3e3e6eeebdb3c25d0a8,0x6f05fe99d76a560b79a47ae0b591f233656d38,-0x22634ee33dc5aef85359e1739c168747ddaec0,0x96d0deddccef6932a9c27b7fb592465695d40,-0x245d0c6f17d9712e08bcf7d28b9e35de24668,0x7a81046e514d612e510d184f1335522ce1b8,-0x16544fb64a766f44180f37af8c98ac17eaf0,0x37c86e2b5f8bbaa9ff3422b3735d150e310,-0x75d82b6afd37d542a4806be399798b93b8,0xcf3121ae30c1be0123fd04680adf80b68,-0x12927d02d29f9e83bfbc5b184a403ace0,0x152d17817d8a11899598c0fc6edb5c20,-0x128e6443a15931fe5863209c2d24008,0xbef09177346aa7e9a8edf8fb09018,-0x546963311f5502b48eba495d6510,0x173ef55231ae0225f31739f67f0,-0x364feaa8003640194308794d8,0x31da1d69f0d967dda4cf248,-0x8c7fde200466432e6600]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 25 47 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 47 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 56 indices rho q3 m3 3 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 56 indices rho q3 m3 3 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea82098100000000,-0x1528cd1223041bf84f4d65a28bcb9d8d800,0x164a6de606ef2561912a04406ba814347200,-0xf397aafb475ce817d48359f72acd40b98e00,0x79423b02ad8d78dbca9f7a1c4c1b12e0f3280,-0x2ee3ebf2d36a1142a3f08b94c8b49cce322d80,0xea914626e2328286977c801d810e300d7ffa00,-0x3cf00e87c4dbe80afe1a3863d216024233b3e00,0xd6a72bf2331512cec26e96b533b663aa01b1120,-0x28a4f50921a959098df7c9ccf65848c6d06a70e0,0x6b1e7e00bb663c55b09ea9db87ad7cdce35f1d80,-0xf7ce179efcfb9c976a9b38785bb29be551fd4080,0x1facba28528dd0761b03b9a2d23278cb9aac30220,-0x39991446a9af9e273b3a188c0c0dbe65e0297a3e0,0x5d8edb05f84a9a6405597e736a6b023da43fdc200,-0x8840d187a2a1e214d216891faa5b10503d4c45200,0xb26ff4cc3e9c25ea25137f4bc88bc52aed6f71448,-0xd29e5d73c025c18d371140a3b2c476fcdd0faca38,0xe0749df5323a8ab5deaf18ee007ed9a7c37a06560,-0xd83aa650b5d805afa605b3793e36224397d41b820,0xbc70689149834392dfc67e77bbe327e19b06c5668,-0x949aa2401e8970d23f5f3446055bf18470d73c718,0x6a0823f22be69f339de23456c9d9fe5a65d3f3d80,-0x446a08a2ec6cda71688d69fdca3a64df9f192f780,0x27e0bfa0accf869cf5be9bef912055bb8a1de8f28,-0x14f800fa7b3f5f45482463c047d5858e637a84758,0x9ed6fbf5afbe4a636e9182111445e4084994b3e0,-0x438bd8d23966c1b80bee96df67fa68a58de1a4a0,0x19b91b923e5b2339b4a71808e0f46bf69a6371c8,-0x8bda477f53c18959267043b1bc164d9770893b8,0x2a383b31967d87877d98e886f8e58ebb874ac00,-0xb43bb26bd7f8b83efb4d7f5b22889288439600,0x2a3ca80b03b8f93f8fd638f893f57130bd31d8,-0x8a11ef6caa43b40bfe3327334e570be398da8,0x185fe5417e8940cf009c7ef4deb4c9ea42720,-0x3ad9d08e61f2679ad7b264895c9fbae6d760,0x77dd5907eaf3e72e544797c3e4a4def49b8,-0xca9bb6cf1e0bdb27fe479bcac61c2242c8,0x116703a67457e5653f30000dde91d32280,-0x12f03282a5f6c0d342ded0f67f6e79a80,0xfc3938970b1083d16dc69416ab64b98,-0x992fe6fdd0894e93066e504f4085e8,0x3f7dcda5ec9a2bcd403b9add05820,-0x103dc2cc1df2780f870e24844560,0x22d3cccfd6ab15b7b7bdc18778,-0x1ce2c69244a38fafc8342308,0x481caf6e203081e071000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 25 48 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 48 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 56 indices rho q4 m4 4 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 56 indices rho q4 m4 4 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d5041302000000000,0x29dd65936192dbf96903cbf9471141422800,-0x2b9efaa6a9cdaadf00d24a6f218bad22a8e00,0x1d75f6acd5a161097b51d5b773a7a990c57200,-0xe7f9e38922aa4a83e45ff68afbe1d0028d9180,0x58a98f0bdf35a485ab249370c6b30b70f23f280,-0x1b644d5e196ff34870c581c784e0d843e91a0b00,0x7079ffecb9c249db0b1b91a83c367fa68e1ae500,-0x18749b635eed1b17104405da59add3a7e81add5e0,0x4926920165911a3b2d7660669f0af757280b87920,-0xbe49c97264fbf5df4261ad279e2fc487083a842c0,0x1b25aa441d74d949d899b28669d2d244e46d117940,-0x36c368158b9bec784dd30cfe8a89a2bbcb806fcda0,0x623104479f5cfc5f709dfe632095b8c145e6fe6960,-0x9d354dc5c7a4b238b559630b1a19ca13ec8893ee80,0xe193fe8dcaf293d660300047bc10855bce7e36a180,-0x122f1d187f817a046c7df1d5e3feb76aec009f45038,0x152112964a8ef2825149305386a2dcf58616ee6d988,-0x1627f4733e694615605b551393e7a6952e9361c14f0,0x14fdb666a1010866037df6fea87a51e4f2d9c38d610,-0x11fb281f5f9db74ab3c60927dc5f4b170aaeae0a448,0xdee124f8c460fd73bfe713096ae6b1fcaec3300478,-0x9c20e7ac6ebecaa02a6aee6e4f1abc26ad7539f5a0,0x62d5c2ffff413722621ada421deb30fc0b9de98660,-0x387b356cbd383561fabce2247a4e33166611552bb8,0x1d1846bb363998b020c4e4ff34aba947f995c77f08,-0xd7ba8ab8218132b33e5a4a0a7db06ab9cdb5a73d0,0x59b6a627e59c98d85041b1044fae087073f900330,-0x21609861a9b5b36261bbb06ca54d1ea752e9d0288,0xb116fe3ebf2a29487567ccf115e42de4c2c37b38,-0x341ba4b5264b8e89f05ee7579de34a780e8b2040,0xd8862318b85d77099b2155f2e4288c739ceffc0,-0x315109a0fe488c62b6d6406e717306199af9ae8,0x9c6be8d4e925454c6be654b26cc0eb0d350258,-0x1abe1a6617fc198458550dbd8df5b3f8bfe690,0x3e64f5932c21bfccb87eed2012790b3a53270,-0x7a7f6773be03349e4508642e54c5dd2ce198,0xc703646dc4f5fdb594029df80bfad0deca8,-0x105fb0658cc22654313c81571de020d6ea0,0x10fff8bc98603205b1705848ee1be87560,-0xd6f4d53a2c6cc56ce791bed026be9b48,0x7b3766f12aa4d3500d219de5e472bf8,-0x2fd84ecec6d0b559cec6d257b3c1f0,0xb5c060c7af8d7d3805e347b18710,-0x1656ed091215f321181b93b9078,0x10bbae5be5fea48911fce0fc8,-0x24ffd396db4d9110798000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 25 49 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 49 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 56 indices rho q5 m5 5 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 56 indices rho q5 m5 5 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa0826040000000000,-0x52d9a54e088255c3da33094faa1eee702d800,0x55669b7b57aebc060ace254d117f0b2d9db200,-0x390c2bd685d3315c2d09adc438abf2a86761e00,0x1bc2ed65ac1d75dd027ffae6f715d057f7adf280,-0xa7d56fe62c83a13e33c34841d445ef03d7e4d180,0x333f5d0ddc8b9a284e544e1aa3291c18a3bc6b200,-0xcfed676c387125234321278a361a17f817fc91600,0x2ca88ec119a33631cdd3848440272d69b2f7bd8520,-0x83ea6c2737bd93e56fa0008296414c6424f3d9a1e0,0x152c5ee41120d3be1a0c26294afa8111d253311af80,-0x2fb2b22dcaf2e6781ae6986f1fecf96c877e4532280,0x5eedd21d8384c4659794bed6e3fb5ce68acd6490920,-0xa7dd7e0493994acb62d8d3dcd512623a7cc968a3be0,0x108f51e67c28dae1b6cecd4fe3d50dabeb9f5f5cf200,-0x176a944e1b0275af710bdcd24f9de73ddf654022ea00,0x1dc00a7280a3b3b587cb41babf0298656f3c4c5ad848,-0x2209536045d839b651bea443981c19470fbd3b749978,0x231fd6fd180efa9dd2b1087714fd42b796b06ba30fe0,-0x20bb9b5b1d2efa7d3020af3adc35d768255d920c3aa0,0x1b90b4bb9f145c37e5d967935f76a1afa282d7066b28,-0x14fb4f5d1a31885e0945047343c55fe7e2c73b434718,0xe6e936e6ad05b2d80fdefb81f8ec148b4a51d2a6580,-0x8f6f29058d321c9d2347de785ae1b7f907f86844180,0x505f8057f835b749ab2e159b28e92b49c71d06d22a8,-0x289074c22d6243b072528e11fad12631e79847bbb18,0x1266ede198a93a2a6e6d9d16838d00efba376bd7c60,-0x77c07a764f4b79b7af755e9566546a47d1ca1c8b20,0x2b876ee42a3d1ec37e8ad9210e1343f075a2d89d08,-0xe1642a63468bf505c1d620c88ba4132cb292a2f38,0x40a4c905982a2bc3f7505cc5ca634d84ee76e3800,-0x105767229c11a658da10c01e7f01a67d8133c4e00,0x39e0bbe9d681b7dd7ba5855ff866ad4c274e3ed8,-0xb21bcd1da329dfd92a37e7cdf25c5d4aab05068,0x1d7c682b1fca289a328b9d3ee0a349af01fcaa0,-0x427805708bc4e996560c10506c6ec77ef65ee0,0x7dc37ea48057e37b5ed286cef37de856dfcf8,-0xc453d10099414c8c1aafb1fa41e437b6b7c8,0xf77a3018740e62e5462377271b177d66680,-0xf5070568b3d4a4743f8abf8eefaa90d880,0xb7c0cab0d2576a7fade92fce381af8b18,-0x6359a9fdf32f4d459a94451c93da1728,0x241dd5fbd136e13ffe01a5ec6f89fa0,-0x7f3e50266ab13e765349e7feb32e0,0xe5535a874601b19cbfc0099b538,-0x9b0d02f8d93283cd652048e88,0x12fa3593b15cc0962e40000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 25 50 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 50 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 56 indices rho q6 m6 6 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 56 indices rho q6 m6 6 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m7 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c0800000000000,0xa3ff114827681d4cb43a3e43ba76edf9582800,-0xa7456c6ff46bd2d97a4415bcec3d30a5ffb8e00,0x6e8a271af57d1ac6aa5007c6c42efbdef0579200,-0x35343ac1fdfa7e01c460c7956080a7ef5ce9c8180,0x13e0d49516cf781ea6756690fe075295b052e5ba80,-0x60017e1463c9064decd81072c289ccd31a0b41ef00,0x180f8642785da45f7c3362cb3fe456b05d1a198c100,-0x51b1994d35ffbd79f0e2394745f10d927654359fde0,0xee5af1d7f52fab1fd7dfcadf5a9c2c30bf944739720,-0x25c6e442454e9fe4b0c3644dd7dbc3c2c6ae1b6fb3c0,0x54015cc936d5fa3bdf03b1beec36f5690bef60488840,-0xa4fa5aeb7e3eb08bbad5b9769e168995a148a8c461a0,0x11fc63ce956e57a927dd2f5fd1662998362c1980fa360,-0x1bfe29dc5fbd47f1d917428800d216a6027e336e31c80,0x2703e15eb2cb836f1111dc393d583e89b30b20da8b380,-0x30d61530fe618838fdfce722164a21464f067a0951238,0x3705b24357bfbe032050bc76cbd396d2d4282db603108,-0x37e3d879dbab0f70724539760ebda80f78cf3dc3e6e30,0x333dab48ce480cdda4042228612eab4f74692523f04d0,-0x2a6dd43cd99e2c35d7c36983ee3c8a6be83dd27afed48,0x1fbc6c446cd7990ab8f7fcfb51c2e4632e7f39c8fd0f8,-0x156ffb6caa452d5a3ca9d2aac5ea168da753bf6dc4120,0xd117dadc1c3dd0d14af9a1a67ac2dd9beb54675e2ae0,-0x72e620ebb30a876947678ca28ab7448ac5bafeef7db8,0x38d291329bd4613b6435d5f28d910298fbe128a52888,-0x193ca9c5a2511b2cbfe43d8bdc323e1fbc2a64910d90,0xa0a20e60496d36d9f95e726825ba482f3ce46058170,-0x390d0a4d426e8e08688832a898c22958288a01a5988,0x1204ec57737350a1e38a4beb3953a2ecca791b923b8,-0x509980b06366839893aa46a0b41eeaa3a00fefcb40,0x13d51ab0939a3e57209a2d96dd25247601e58374c0,-0x4443e55224aa6016b8de5f1f30167415ef1ae20e8,0xcbcd7636ea7713c06a47df84fb836245999778d8,-0x20aadea2b2a92b48654f878e178170c5082bab50,0x4723b17b8633a0494ba5770dc4adf073cb3c5b0,-0x81b0ee1f81011d16a428ed32fb8e64f621e098,0xc27c7da101725072091d33c90510334c91628,-0xeaac06eb706db0a34ae8d28f797394509e20,0xdd7b679923c53e3b1bf8589b010fbf5b5e0,-0x9d8871a22388a7b12f9ed8ac0ad35ba948,0x504a25ec97703e6140ffc4c2eaee8a678,-0x1b4e80f7ebf81362183f64fdbb4ce130,0x5928d69f1274c92a442ef1c0f9cfd0,-0x9328fa57acf59c6f75025d759d78,0x59c527390e8322b951d8fc5f48,-0x9bb079a29970450f8600000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 25 51 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 51 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 56 indices rho q7 m7 7 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 56 indices rho q7 m7 7 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% []
def r8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m8 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea8209810000000000000,-0x144b0f37dba30e707181f9115fafc6d131acd800,0x147c5790b154fe65052fee33bede644dd28103200,-0xd654b3a546ed906e48f96880a58cb130ac0a71e00,0x660d9dd32efba966460e31cef5b8b60dcd0d3c8280,-0x25b60e4bab621d5412e8b00e993b362a407f5f25180,0xb416e8e348410af57a20f167c9060e0eb53166d0e00,-0x2c9d702a6441d2fb58ec7f67540b688f4ab7b6d01a00,0x95b358c5111bc564131aeefe55f4e1b8b58c41910d20,-0x1af82f95cda54acae00a1bbfcc9b5a63c0fe8891fade0,0x438b81bbeba87041bb7033a3b69dad239ed9a89368680,-0x944bd2e6e45cafd85c295cafc9c59cbe49b826e0de380,0x11f723817a7ead946cee708a41424c33b4548af08ac120,-0x1eeb06af7e94b4f17a216976db922375f6a858cb764fe0,0x2f7541cbac4280713d963ee4d2c1a424e0e1eb0f1a9600,-0x41354d8dd346581e4678797fbf644bad9cf3e9a0db9600,0x506ea13b1ad67d6dd09bd3629a3cbbcd7b3e106c981848,-0x5941e83e510f867396f6f84b1b0cb06d3baf6895a4d678,0x594207ad4ea52abb0d33b2a974a6e6fccad681fdb7a4a0,-0x50855d1752d38f4f523a016068600dc5cee674f795e3e0,0x41916c4f9578c4b68f1fff87445c8b5a901c03887b9d28,-0x30338a43baa5f5736146a90959e9145da663a2515e6c18,0x1ffad9822004eb1cb737be57dccaf5d75fbbff8c857480,-0x1322788a93e723eed228c6fefe6fe4ee5e49b5a26ec680,0xa5006092b118d0fee29482561cdd0e886687cbcba8f28,-0x4ff78c8f78125b0a3499b93d1c355898b539f98920b98,0x22c64be8308a76b5c8c0ac0fb17ef5518cc3a1682ec20,-0xd8824b6dd78ea1bde59f1bcf7770518001fc317c6560,0x4b2365057bf82339455f8cc91cbd8420046e0aa96488,-0x17299faa82dc42788a21684313e4a5cd4e8e931776b8,0x64fd73545bb81ccf59bafc1f915d72dc70b9717e800,-0x18301442e8f7f96e1759e3655143ac28e84d8d6a600,0x50e8f8d45dbf2a947c63ef24a4a4440354713063d8,-0xea5300f764ee63f1c67fa5f756ba360fdc8effa68,0x245ca9364ac0675e79cfa938403f0a89b0feea6e0,-0x4c7b954d353254ee8201847e99ff5e41449114a0,0x86513ac0543cfe6e918127aca5d16ab2c3765f8,-0xc1703aae138178c52b5835a3535bb516e4dbc8,0xdf5904a239fa14bdb84411aad79036dc82780,-0xc8d9950ee58423655471595db653b0a90b80,0x876c8f5cbb1e6243e5078639b25c74d7998,-0x410655ea65c6e882e386935f6afa710ba8,0x14ad160ebafaff3ec0936c9d59e2de7e0,-0x3e85b032fe7c9838e9f1820d84278a0,0x5e723dab314d5fe223ecd43efc2b8,-0x33f5b45b054de4c97737ea33208,0x4fcddab54c6a82ae11000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 25 52 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 52 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 56 indices rho q8 m8 8 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 56 indices rho q8 m8 8 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1]
def r9 : List ℤ := raw_ints% [-0x292f6c281d95c4681a988000000,-0x3c5cd758fbe1e1753ae9ec00000,-0x2a2078483a42584f65e1c140000,-0x12a2d8680811ec20ae0d5320000,-0x5de67065a4e21be390829bb000,-0x1668ebe21a69c108bdd81a5400,-0x4368795676d046c65cfcabd00,-0xa3e55ed3ab2a50dc512b4fc0,-0x147f4085f4a3c9e6fcc638c0,-0x22301ef59a28db1e97bb570,-0x2ff7538e2381aac5f4e6b0,-0x38f68157b4b3d548059f4,-0x397c8f21d4b71068a044,-0x3165f3e1707bc756021,-0x2425b9b4b010e38e68,-0x167c4f4ca0a37cbc6,-0xbd892ce1b418f14,-0x540ed7bb506cae,-0x1f1b196d2d160,-0x97c1b426acc,-0x257542e56c,-0x74b75cd9,-0x113dd48,-0x1cca2,-0x1bc]
def m9 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d504130200000000000000,0x282fc5bc7746d1c22b49a9a0019b5135503ee2800,-0x2828dc278374c1d1a7678d3176e609fd01dc020e00,0x19fd8cb63fb5a805179492680c1b80aa0f18754d200,-0xc3ec1a16a6e90deeba1891a35d44e3090a1321a5180,0x479e8091f8e0a9e9f2ea64fd598a133366ed335dca80,-0x15240196be49ed66f394fac37d9004d52e2fb9716ab00,0x52da2f84a050f185689d3252e3d0429ad3cf800c1a500,-0x112c9cd1f85c45f2dd29b51b1e3dc5cb0fbdc19ef5fde0,0x30eb0779ad42239a4a6c5f0dea98e1e16e82c67211ef20,-0x79067ce4007429c42b0e098c49a64ae7060e50e86b52c0,0x106655a7f93195956aeda971b894a0d9f9ea83d6485f140,-0x1f615882af44fa59a36023a4eb49af1f27fbb68756673a0,0x354adfec777c459a788c09cbc19ed2a93363cd68e1b0960,-0x50b10cb786509c564c05e30c6ad27e355ce2beed5b52e80,0x6d5269c88d04ed7a85a1bfc0dc0cdf7ab92f950d8258180,-0x84e6e6595bf605aeac49d5954e498f93a966ed0f231e838,0x914ab4cae9e1be9f8751a7d9ff3e03a148d556be8bce108,-0x8f0fce8870789a6aadaa25c5375dd519d4d0a9e937430f0,0x7f026bccdc86ae682f0e48ca6405d82b7e8025a4dafbc10,-0x65b964e3b130c3cba15c9fc1751e3e0e1bff0043f187bc8,0x4981f18b186824a690adfc9795aba6e5f8c5eb64aa16878,-0x2fe871be95486b2d8919400896970c319a6ecd11763e5a0,0x1c238196e7fd39d0a6717088920d277825bd02653cace60,-0xee02480363c3c8f3f122b7172a3c10b3a3157c5ea724b8,0x710d6ae7767d2d63e3eb7af0665ccb2b2af368b91e0b88,-0x3023cf33b970dbf262c130a12a918c0214dd20a473f3d0,0x12533b387258cfafb4e1e1b01f22d11094082d15509d30,-0x636f04c37b4f874cfd119bd14ad4276b502de8d8a1d08,0x1deae901092b98870a71bccc9772c04f9ad29c55d8238,-0x7f268007dafd145e773e8e3b1dd1d7d9e9d5092e3040,0x1da448176870afd8c91085550f8b04b86a98eefb8fc0,-0x605ab8c4a62a5c10f85d0e46fa5e45089f3ac1f48e8,0x10eade285221414bb39a27b9a32021e7f3be9afbad8,-0x28a8afa442f25465bdda6263439979af2006023290,0x5296ab055814260bc4d52d36102cfee491c8d3c70,-0x8bb037e69e1fc9eba73e4e882b796573d8cc5e18,0xc124b73ba187f714b6c83e58a5de676bcba12a8,-0xd5520e620446369f2f5314d72317db886beea0,0xb6b46fa2fa2831fa2aef0fb1407995c2e1d60,-0x74b84789d0b07f7dd414f76e226845cc0448,0x34c48130116b76227ba78c89506f890b978,-0xfad4066d7d5ccc2969b4aae26e69169f0,0x2bdf7c088d8ec8e9088f6ff6ae090510,-0x3c9ec17191230ac977eed48aa2ebf8,0x1e10f0b84b92886d31dcb665b6c8,-0x28e4d7fd62451165d18000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 25 54 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 54 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 56 indices rho q9 m9 9 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 56 indices rho q9 m9 9 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x1bc,0x1]
def r10 : List ℤ := raw_ints% [0x476e3f95934fc0a48e207e0000000,0x6887d6122cbe2d42ea131cd000000,0x48d3f3c5ec0f2f483f78a13f00000,0x20284edc25c4d3305e793a6a40000,0xa1b17d69c977099ca3c1b0d34000,0x268012abc02a88af45b24b0e0000,0x7382a3b3d46a9eaf7d68b857800,0x1180b48e1b5705fd1b6f7539400,0x22e8ce8980a0e7dbc2169f1d40,0x3a0381a998149f6a9f5c87580,0x510df2fb2bf2567d6b4463d0,0x5fcc131b3b2fcb668e47880,0x6024a02931a250bf0099fc,0x52150a08e1cd321af90b8,0x3b9b0ed74a8016ff9a3f,0x24bd3ded9dfd0774a60,0x1323d9a8c53df2068a,0x85f12b65b9539330,0x30b212d8bfcd7d2,0xe818e9d8d8c80,0x377b70e518c4,0xa4fec3ead8,0x16a512507,0x214b860,0x1968e]
def m10 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa082604000000000000000,-0x4f993f9da28f01f8d29a66c2b38a6d574b79d6d800,0x4ec2f4589675c5249a69b7ec029c3e31e05e1a7b200,-0x327591dda09073a1c16bf70c53836685df80db93de00,0x1787427fe78c4925521b5f9f3ca1aa852f9c59f6fd280,-0x882904b6d2246512d5c74f0a2eb17db9ab8a416b1c180,0x27c1f47d10876ea8d747dde8cdddb2554b74a90216da00,-0x9a16a78c85b64084da9600c760fe6b8a72765279686e00,0x1f93f423069903c1460831f7fcace327cca046fc475a520,-0x58e5865af9158a373b921f9d4f0b87646a633199c1865e0,0xd94d817ab253464336372eb688975631b1dca9b3b816980,-0x1d158580dde8d9ae325f4007c0e0b9d0b02ca6b312a10880,0x36f2add0061a41a2a97e7001bbb722467020fb47c18ecd20,-0x5c1a8f0ac9e6700949d5d2d578d6dcd0e0f94756c30da3e0,0x8996f236fe38bdde25d6ddf0ef3b31b4b859ab3236beaa00,-0xb7d5f958abe09d86829d7d8cee77198045b9f55676c83200,0xdc4e8ecb143a5834180033d5291ee46b9dc5b2eba5e4b848,-0xed4e2d1cd10656cac99247fc216038d1630820f37e8eba78,0xe61d0f093aae434a070d219403537f19cc6ea2b0b57e1860,-0xc9152339b71c4c7d0218f51674983f7ed1844aae1911ca20,0x9e6db75c754931bdc727e6de99e6cb1807e8e5c05058d828,-0x708cc8dfb8f18e8215eae3a09fca3ad9ab803946fe102918,0x481131af7e58055bb7da9452c691ee4b608b168c8eac7780,-0x298e7d0147a40577a2e9ad544779b6ae3db1041c716def80,0x158d384837938a208417777c86f5831cbfc548d125fdcba8,-0xa08b4475a32502fc610a2f2cda259eda09cdf77010d1318,0x42f2661064d50f0f44be8e71aa4b0d06164b246566246e0,-0x18ee7db1db3e828ab3f7e7caccf13dfa163d2991e8508a0,0x8433dfa1863907717fdc340a6c0d53aa81aebe02d1a508,-0x26d341f208984e3f87e90bfba1557384836dd4f28aae38,0xa0d83567ff6a17bce82b5afaf1a3e3154d6e10966a800,-0x247f16df3196c190b8001bda6786ee33b8511d26c5e00,0x7347ef0ce079228fc61ea0708c711d35ba2deb7370d8,-0x13a1a46a5c06789527b05e6c657bd798e3de3443b968,0x2daa5a164f6877148f3da9013b603603454f19af820,-0x598fd5e4f85ab5e1ded9959c6f77b2a920f3ea5960,0x91dc2bef122bf9775d9610b8dc67b43d6c63d89f8,-0xc1922646b87b513b51dae3938bebca0801baffc8,0xcc6f093c7ba8b8f6f606ace8fb043e25594c480,-0xa6b0cd1671e334b11a45d11dd9e59ae87c3a80,0x64d87bd52cb6319687e2744c477eea582c018,-0x2ae6b00983c08c36d92364ddcf9bbc8de128,0xbe6a5be7ff5dbbd87d1e1a0f6f182d2520,-0x1ece12f5724f641cb00c4d0ec9373c560,0x26e9221483e06e6fed6f0670afbff38,-0x11647c72b42b3150cd35523dd1d88,0x14f2ef286d45c0b81e40000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 25 56 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 56 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 56 indices rho q10 m10 10 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 56 indices rho q10 m10 10 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x1968e,-0x1bc,0x1]
def r11 : List ℤ := raw_ints% [-0x41680dd59d2bee900bec9b970000000,-0x5f954ac6fd40a31a55e7898ae800000,-0x427e54ef3248caada4b47897e180000,-0x1d4fc5954094d73d85ea34979cc0000,-0x931d0725c983c0735981b7b4d7a000,-0x22f522ce0384e7c3534a45eeff5800,-0x68a51337b2618f3ae52527f24d600,-0xfd1083630d9763cb4b192afb4480,-0x1f7523a15a9404ae814b9ca06680,-0x341cbae216ae3fae5379dbf26e0,-0x488ca1992ba60ccc023deaa020,-0x5565aaad247c4abf28e3b5788,-0x554eace5586b6152aa531c38,-0x4870cd523c5858ddf115532,-0x344690d1037e919870b3f8,-0x1ffbedca10cb6cdf2abc5,-0x1084371589a95ddd5108,-0x725a50bffebb62c4e8,-0x290728db030d10910,-0xc04f5be168a449e,-0x2cfb58ee36d088,-0x81e59a27a1ae,-0x111a35f1398,-0x17a1318ed,-0x10554f8]
def m11 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c080000000000000000,0x9db24c4261e0aaf3558283529cb733d9223c1042800,-0x9a889a055d11a4407c9af834e96a3dd506a5857e8e00,0x6206c93070181515f8aea61a038b47437dbabacc89200,-0x2d3f1d644ee455482704fa4d7f65ea5c1fb2cbbea32180,0x10322c3d6fd1c8c7f985c4c42d8eee198fd318d34677a80,-0x4adcf871fe462822142ede43e7f653db0890e01e1252700,0x11efdf6769b0f9fc9948fd6f058c0415b2fc374272c74900,-0x3a2880b825988433ff175634c2a9ff0319129c00e96ddde0,0xa1d93de3df9c4715923028a350fd63d2b4dbe1970598af20,-0x186f95ce85f40ce50dff6de132835b2b20a36977ffc5881c0,0x33b20183497c44cbf1fee9cb9b6f20536f9646885ce9daa40,-0x6073843d4d66bfb9b755ad90bcf73ab384762705b9510fda0,0x9f996fa633d9d9b8460fae6101457fedfeb2d084b5f64df60,-0xeb44f29039860c07b211dbb3afa8e7a1b498e1c5ef3500080,0x13610b5100aa6b9bc5324d852a6b7500d7df23aa55b2790f80,-0x16e5a86710b1ed710fe6a94ae1796c389c0d25c923d07dae38,0x184e302a7c03271ad976cdecfbbe61405777e1ddaf51f21308,-0x1736ee42337133d4f8100028c14ea70ce6b978f3223b6d07b0,0x13f859c3334f088831d5930a61801c5d030b203e340c54d750,-0xf7aeb8031ad993f94f36c165bde4b4c5c1ebac2159f998048,0xad02a1f3b9a38e979c4b69bb388b8ba60824b1016fa9d1bf8,-0x6cda2f623c5462962c6faaa65807962005ec586bf1eee5a20,0x3da18782b9e0b72b0b62ea6c8fe7e38380333f0b9ed13c1e0,-0x1f5bd335a6d3a5a5f25cb3a81d71726031652fe76bcb447b8,0xe4fdff6fdd938ea617d260e203e4178e769dce17ad38ec88,-0x5d850b548b0cca59abd04d5de6d3ee5496d6712403490e10,0x2213115eb859290a61d4316db174f63f2135347e19311cf0,-0xb0949159d90af853011427df1b1dd679b6e6863fce9fa88,0x329e46993a4a4d72dc644887f06f25860c36c4dbd6d20b8,-0xcc68e4947f0f77603cfb9d677717180b4aced334785540,0x2d24a90031592e234a2fae8b940573eeb9152e03816ac0,-0x8a8d5ccb704dea80d5685e50709b84d7b7b9c21e468e8,0x16e1d50afb1ee7020d888fe57647dd6e69ace579a7ad8,-0x33828039a35703878cc7274ffd82d94d41d9469975d0,0x61868729fc3d1f02b008d79b7bd3bf1374c61fe1f30,-0x98e6002c87f2d4a3019d2f8106e2320c91a6294598,0xc2b2f5b6d83639adafaf47d9faabc5bdec85fdb28,-0xc48db1aed5e74b75840580ee3fe05c5e8b63af20,0x98823944400b14ee81dd9cd4785061a4ab374e0,-0x5755097100f6355e7646974f41841d6637db48,0x22f0c0e6ba7e0d9ae509a9a165cae1f692678,-0x90b7a3a84ef4ae205fc213593368e1adeb0,0x15a409d4c9c925088739f46619ce0bb650,-0x18f9e0d5c549cf30a8d2747c32620878,0xa0ee51deb2cfaa62f53f88d7f1648,-0xaba801543c2245d92600000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 25 58 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 58 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 56 indices rho q11 m11 11 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 56 indices rho q11 m11 11 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x10554f8,0x1968e,-0x1bc,0x1]
def r12 : List ℤ := raw_ints% [0x2a0b04ba541a430bab8b0e4dbc0000000,0x3d5d48707d00f90ec1e576d475a000000,0x2aa180cdc8a1799b18239b42d14e00000,0x12c3b7c9e4cf6aa57b47a643372580000,0x5e061ed26b4dcae75ba6644a92c68000,0x164d4b9969d80257401293f1ec39c000,0x42a0911d4cd4c91d053fa3c946bc000,0xa0c4ee83a3ad4330770ee6a7bb6c00,0x13ef79e1a1d370319fcdb49b6ab580,0x20ef163f1716e9dac2ecb25f01e00,0x2db54820cc5da81293dbb4a213a0,0x359d6fd6169539ce9a91464cc40,0x3558b7d24d597935488c3cf658,0x2d186c254c63f0d9dc1275f40,0x205f68e58f058b88bf337b8e,0x13afca5e82ed10aa0b84298,0xa17fd5988b7735b04badb,0x454ad1300cd32e222200,0x189b4f09b12baf71418,0x71e3bb1cd4a9c3eb0,0x1a382032f8608c82,0x4a2ddf14a6be80,0x980e19506e12,0xca486c48b8,0x8456db73]
def m12 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea820981000000000000000000,-0x1387c35c28b7a7979f09b96e2d158f474b2545f80d800,0x12f541c00f63905880636f7fffb35f3caf84130bf33200,-0xbe8dcffaeec5ba9b472a562600c815e6377c3b1c819e00,0x57159c936706d3373e838747c5c7f15b68fbb3e2e17a280,-0x1edb0c4ca1084b0a8fa220c1ac8ed9b51337febc00d77180,0x8d242e7d19264984f9acd2063efa3f0f7ec2982e1a264600,-0x2174c2f331d5874b11a5c4afda8b529ac847cc331365b2200,0x6b49b0e6db7984f385f1bde6c7eb9db179c2d74ea8ecfbd20,-0x12735aef4c9dd55118c2229bd9f9c35ad60f04ef15a88e8de0,0x2c0e04f034ba06d37829c7e5b7118a5587dc2977cb2cddb480,-0x5c170fb37d6ede41733244423f314a6005be147ccc33dbc580,0xa9b61f1b04148d05c9231c14efc1d57957b44758baf47ad920,-0x11546a7835e0ea6a99bfdf6bbcc7e3d4936840a401b85b5c7e0,0x19369e9fd87ace05c7cbe254c4a93ee83553ca35bd1ec931e00,-0x20c83fe8ab320010f33b07cd506622349fd850d17f18fa26e00,0x2631fe479dea9a9f29f3c8669b299c6e4243156f04709118848,-0x27f648726237f9e8a8cd6c0d1ed45c821a5e7995980eb100a78,0x2599d150d1d1f31d121799ee0845531dbec4282d2109bb10e20,-0x1fd8e4d8ed37c2369dea7aca2af5c140ea28accc06001152e60,0x184ac7fedbe2ba93dd564c72c3896ba9753d444373e89e53328,-0x10afc14feff4ceded67fd9d7b3db6ac87d3565ad5096f606a18,0xa5132b1d6087df633183b558f9a6a7e4d1454b644ab5eda280,-0x5bc7e99dc8a3967bc5a7fb1429b20d33e963ed7976cdd17080,0x2dd27943b23d6524137dce52e5213df7e07b8dc71776ef8428,-0x1480a53d50117e2f2d56ce404d6c31875accf8b2d2da1efa98,0x833782fffdfe47a1ca06ecdcbef5e07920738c43641c46ba0,-0x2ec758f8382b8e5e5a3e7bc5d6d17f4f5733670781fdaa1e0,0xeceb9dba5f31148620f60b557db46529293979de3d64e988,-0x424afabe969d97a1abdedefc65fd1ec5653af387ac1ae5b8,0x104f3cd77b58ea0918a8dcccf74ba5edeb3da9c50332e800,-0x381703bd979652f71a207179d2e7960b065711b5e129600,0xa7428b5e320c403856ebc76711709ef6dffb7df11d45d8,-0x1ac9702d54cdbb3b3c976bd86bdd75784c6f982f31a468,0x3a588d1eba0a993ec80b238b37f115a92fe71859d1f60,-0x6a9f81e117ea326a56dea92535ec854fecfeae1d4820,0xa0e17ce0aa1e63cb13b46c2194de6f4ea2fa44915f8,-0xc48394063332c566f6dc645911c5c73cb9ceb287c8,0xbd90a8c29b21b1d4f79cc3082faecbc46996fb980,-0x8be85a3f9b0c702bf38956af16e4f8db475c9180,0x4bcb775c21465e265f57c6f25c8efe03465d298,-0x1c80d5f50264e508b7c77aabe1ff05dcde0ea8,0x6e19a904d28da3b405d06f811d164205d860,-0xf35b3ed80aa65838148c6243b85c245c20,0x1008057854196e9fcc87d8f7ca6536fb8,-0x5d0a2a23849e373b9947d7a129d108,0x57e27c13ff7882eff1000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 25 60 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 60 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 56 indices rho q12 m12 12 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 56 indices rho q12 m12 12 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r13 : List ℤ := raw_ints% [-0x154a6d01168f10ea11fbdabf68018000000,-0x1f0a4ef4095ed852866e6e468e3d0400000,-0x1589abc1e94c992279cc53d7fbc5efc0000,-0x977a8c3379b87ef86ae3b4ec0076960000,-0x2f5e725fdd887562dcaf9d9c7f89281000,-0xb37adf6d4147c6ec91bbf1d043ee93c00,-0x2173e8b8696d47cc26afd8e1c59882700,-0x508fd76002b8b1da0ab86bd7b9c25340,-0x9f7cca84cdd8a52c0c45df4885c5240,-0x106d71d175fba6e77c54510cefe9bd0,-0x16bcdbe58b327c39a4ef7c878c1310,-0x1a9719d3173fb5ea29fe0bdf2cbfc,-0x1a5de3ef8708c792c37c2c0d7fcc,-0x1633c8db6f5503bcabbac07e5ab,-0xfde30a7bb9248450ac87572f8,-0x999c35e40061192ddcfe5c5c,-0x4e4b3f54e246e792c0530ac,-0x215c2ef13efd125b8dceb2,-0xbbfd9df9ae7e7d3112a0,-0x35d8136ec697aa88b80,-0xc3efd747d3582b3a4,-0x221fcfadd3241a8b,-0x449a26f3c40618,-0x58f3ec793230,-0x38313853e4]
def m13 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d50413020000000000000000000,0x26b562c2cc9eba7e1380ae53cf90859a219837909a2800,-0x253a38428da9a81669b3eff8afb62c0d5f0533ae3330e00,0x172a5a859df4aec09d50479d09ba0f68a2551f2e37005200,-0xa7bef8639f9152d5b44e0cb540841f74cc46a58b7d137180,0x3ad8367236b46c7c0f5eda6cee293084a054f693fec502a80,-0x10a6c45bf44cc019a6814527b518924a73bd8a20ebfb080300,0x3e7dba8102ad4e27acc518b7a65e179f8a0eb29c3bc46f8d00,-0xc63da4a3f232dc2f90d672dfa2a9f6a4fa240ccaf1f465bde0,0x21b6f83f7965111fbfebbea60dd4f69fefee391024cee068f20,-0x4f959f7e5d990646f291c671a2f72c1819883a2b5cf1c3788c0,0xa468d4ca4af72c9e2c9817823d05a1e7f2ad1b439ef2c214b40,-0x12b53fb11ca66b2f122ad37e94932c819407c434187fe9b3e7a0,0x1e2f42a49847a928eab17e54e93f9725617f749098ec74db7560,-0x2b5a05184a4a17f7076bcfdfb51300b8f5dc4930c0fe75164280,0x379dfc756bbb3196805a86f092268be0db7ca3ee6f88cc4a2d80,-0x3fe9464347196feea9ce912e7a2fecc696347ac4df321d139438,0x41eae5ba36e023b229a5899178106b04f556e37be0d63d5c6d08,-0x3d1c24998d0ed01983dd0889b22a6084a03c70e56f1d3b158c70,0x32f80ae2261920a0115ba77e0307cab67a02ef7782484cfe7490,-0x2642e3f7ed73745ac807585d31e9fa8cc51d62d6c4f1431b3cc8,0x19d9569333fb6119615656316799eb2c5335fbddd8f8e51f3f78,-0xfb53fcdb6cf3ff204341d03ba7468ed77c0f5ee675ace168aa0,0x893cb5f7f0b352479777aa6f60e94a5a4da1230976fdd5eb960,-0x433c7ad621c84f12f3b28c0dea613f2a0c55395ee2a07dab2b8,0x1d7ef71228acd19b7b478cf551f55e6f152163554d1b7858d88,-0xb8e88800596bfbe01425d34bdefc99cb453ae52b72797d1a50,0x4080762748d888fc77914c066eb83350cbce693994deb09ab0,-0x13f49dd63178cde7bb6000c877e1035431171efdaaf9de3808,0x573521df7e73447580a9da91cf9a1ce9b185e35a4cb578738,-0x14e9d337d7993f3d98e16830309fa624b5f6a6768c25bb240,0x45ff6c88d6502ee712250a404dffb4567419a9d62d720dc0,-0xcaca5dc1019f7ee0cdea6ce00ecbc78453c6f95cbe478e8,0x1f7d8c557de8c0d1b3a5cc8d2294f250ccd64a6156de2d8,-0x425be3f711f3ba1199b1ecc8d9e6ad561884ea151b8b10,0x7505c35615ad9569890b63ea27056262afc4cf3223ff0,-0xa9e591fb8c68e6153e2b2aa6c4531e047d466d72e518,0xc7024210e3a37e5e4ca151b0374fd4fde202e7423a8,-0xb75eac59069f34ae0e01e85f0769612ce7fbe56ba0,0x80acd49cf54eb220d71cce02dcae1502acda31060,-0x41eac2721d0827038fb8974ab5beb8c1cf785a48,0x17498761ff00be9faa5bfcb25563252ed47e378,-0x53d7b298ca81043b29e8103cb8ed367304970,0xab1aee8d5e34b0a031de041ce309e208190,-0xa4a19212e8f7e4e5361f1fc4b5d5c74f8,0x35c6078b8c394d3bcdec68f106ffdc8,-0x2cfb976faca69175498000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 25 62 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 62 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 56 indices rho q13 m13 13 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 56 indices rho q13 m13 13 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r14 : List ℤ := raw_ints% [0x90a4acc58dd806f729d49af3321520000000,0xd2a9fbbc503093b3624613d1a87d8b000000,0x920297cc6e40275adac8abbd7e67ad900000,0x401aaf026801eb76681196084a90b78c0000,0x1404fbceb9fa360298028a9479cad622c000,0x4bbe42a87c40a2d8b609bca697bd786c000,0xe18557fa7bc52a91a912bb0a8de4ee1800,0x21e27129cf7284d32e5c1e622a2de62000,0x42f3723d4c57d3bc59de2f00ed52e77c0,0x6e19cb6dcc038081e79df47ca6249580,0x9807c0ed0c8e402fdb639700c69e8f0,0xb1512442f906f7e54dadc5351d6a40,0xaf4db2fb07286f5b9a8bd63c4ce94,0x931ee7c83b77e2f4cd5e6aab52d8,0x68bf73e7435cc58108c6c6a78f5,0x3f1a10c050fd287e421698ef00,0x2000af69054a350aae0c918d4,0xd8eb493242e97b9125cb770,0x4be25b045cb74f9049d8ce,0x158fb4e0b9aac4cc8bc80,0x4db5eb0cf0bb4081670,0xd605240e4e63bd678,0x1a80749c6124f095,0x21bb4bf6d2b400,0x14cc358aa720]
def m14 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa08260400000000000000000000,-0x4cbc1fd9e7e954e4e484ffdf129582daa116eba82aad800,0x4921e0bf99ae84d4399bd4cc87b0087884a607d6b9aeb200,-0x2d162dfc2c80645c92f350f24ed2b7e83abaed742cdf55e00,0x14361bd63b6b04cd14e6882fb2e3d78f00f8094c26f3bef280,-0x7055db4fb18affbe7548f8efe20bc06050c45b6b1768e0a180,0x1f7841a2383fb7a8a3a880b19fe7cb7338c6ab4fba4b95b1200,-0x74e3633e76b7c7977536fe3f6861640a96b90fec245a53d7600,0x16ee25fbe936c353c140345da3d82e9ce0cd7bdcadc05bc11520,-0x3db7933a869d88ac23ae7d19fd01cbdd0f62395f66bfcebd35e0,0x900d99555f772236b0328836f4edbb45adb9483bfcccdf129780,-0x1262875d109d054bddabab952aa7108b760d965ca845319f92a80,0x2112df6fa23fbadea63cd51f8dc7e78c98d71a293be928f649520,-0x34b53b985337b51baa2bc80865a81231fef30d1e3abe28d5e7be0,0x4abd77da0c4c5f53f94bf4cc63a684e300b4b52a384386e70b200,-0x5ea12455eccb002c12e82d91447b0f8529e4e5a293804c92e0a00,0x6b443b403bc39cea109285d5971248a1b6f6b44cfd27ec5944848,-0x6d14684ebaca1d01e714f27b82b39f88cc84397c071d2c10bda78,0x63a6b10889e4b3069febe42492da2ff0cf1596832bf51ac0141e0,-0x51db8eaabe689aedc9914fd7e4f87844ce6cd7af081cce9f2e4a0,0x3c7bb395d183a6eb222873a8e82428e10446f9f871197a9beca28,-0x283197151e4bc0be67c5c8cad8111392f87afddabf9e83525bf18,0x18024477aef34b1c1ab1169aa08ac111ae5e94ed259718a078580,-0xce078e69fad248302d8c18852d104415bb9a1fc586ac36bfd980,0x63102fae41c1491fa376082ebc4130a5724bda203967a2f488a8,-0x2a9cc3b0553e8dd8c4292af87b763fab13f7f8b8d8a05cec0618,0x105ae34129d9750179a298229daec2fbd319870615bba7fdc660,-0x5952d66db47d63ebdcf8f42ab430fb0265ca37b1d4f51847520,0x1b02a15a2619245b57f4e8c096380803de847588e171d65fe08,-0x733880926573aedb8749a505186febb5aab876bc1823f01d38,0x1aeeefd605143b6e1ff3346f07851c9d32a6d1459e5cb66800,-0x57bae23ee8541bce65329b73a49cc5df8a836f47224a6ce00,0xf6e886fc3796b03bc1149cae0e8a8cc666209712e65d22d8,-0x252c1cc4b48b5273d8b2069368535f07a025e59d348b5768,0x4bc594a72ff7ce97e51acbb1989698350c227746ac0b0a0,-0x80eb96eaf9b00505f0821369e498e173bf976be9733ce0,0xb40cadb0de4d8af9258f270d497dc33b91c471105bdf8,-0xca2eef0d9e1293095aec42fa8936c6997d6747d163c8,0xb1e1f257b5d925a102a551bf39db4b64525ee213680,-0x76a19597b4e603bd46c173b4c6d98a958caeb40080,0x397007e5452c8f2285fe413fb676b1284d84e2118,-0x130d6c36f66499193dc0b37ead83b88fe4409028,0x3fe6cc0650ffa02d5f893351c62fcaab2b15a0,-0x785859e8a48a1d00c884b6fe22deab49b8e0,0x69a851da8e5e670b1e7d41fea72265c838,-0x1f11e9ccf999a5ced0b6d929b004cc88,0x170486430ae3c0b71e40000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 25 64 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 64 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 56 indices rho q14 m14 14 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 56 indices rho q14 m14 14 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r15 : List ℤ := raw_ints% [-0x3588eda721ef7ec49beeefe5f11ce900000000,-0x4de5d23ac471e4fe573404238d80cdf8000000,-0x35ef9754c3ed640a31949693ffce5f03800000,-0x17a7668e581b1ff3bc6d17f6cacfba96b00000,-0x760cd5e1043be7e97268cb3a850100bba0000,-0x1be0dbdaf898b7c9cab4fe1df577ea1f3c000,-0x52e3091ed249648c9ddbd6b32636451be000,-0xc6f231f60d5fcf10aea319f0fcb3f022000,-0x188684a2a6262a1590fa44e0f3511663800,-0x28414781920e55ee9890dda3fe0c044640,-0x3777bda712e37903228a0a605a5d51080,-0x408aab2e1ce4c9a63bc80b34c319a190,-0x3fa45525ce9630c2c6a43a832858a40,-0x35410edd61b0fe9a0cfd5bf3134e8c,-0x25ca939b4e5ca1c7e8dbe045ee228,-0x16ae6813091884f902acc90806cb,-0xb74476980d54e2c6ae3db81a80,-0x4d42b4d182768a839ecb6200c,-0x1ae02cfd22f066d0bbe78490,-0x7960b2d5d43058d724e032,-0x1b21143f308bebf573300,-0x4a0571f8cdc10c03270,-0x90ffccda393e4c288,-0xb5fa7ed4e52902b,-0x6e38c9bfbb680]
def m15 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c08000000000000000000000,0x9825deb7283fab9cb8390bf994dcad87981c6895d2b02800,-0x8fb96eb3de45d28841b0877528619542e6881823cdf278e00,0x57cdea36148fee8110696efe59d0354962957ddcb7b7421200,-0x26fea73e7c19fd5754b65bec5e77f85a342c6ef4cc9eb194180,0xd6a9f61fa7dd5b849f934c68dbb24ffad043ae54e4276215a80,-0x3b8bc2b8befe7604b729ab675fde97fac33f81ddf7f58c24bf00,0xdaf08b2066c8998271e45868bb5949d27f1649600bbdac4ef100,-0x2a8103ad68c281860fc1af20d97bbeca5e83403650cece0ac1de0,0x712d4628dee88d9422b5261d71261b934849681f12bf348f06f20,-0x105413f74291a08ebaf16cbc77962f8c860d863e3e573d506a47c0,0x20f6d1aeb3db5f439907bfbb95e9283e46de0f5bf069f2a2007440,-0x3a9b3595d3f62a8f0a5dedec48a4d5d6a5ef8deebc2e840f4951a0,0x5c447beb6ddf04ff9df85f8a36d7ccd3d37ebbc5cab571f2d28b60,-0x8132f4cfcdf085642f7fc1df0ee324c50a3f6d328a4215761ab480,0xa176ae8cad592b8e3485ace2100288df339e18d8ded73af2d41b80,-0xb492ae3c264f530c4dbe6433ded27140bebc177d8ffc8994a4da38,0xb51304cf433d152fa73efbb24a8264bdcf002e32075520ec710708,-0xa309b1d0de41f6731ed6de9dbd338a7821f672fe8ac86f628b1730,0x83eb98ed7da801d5386ce6c064a14c229f2ae1c8045732cc769bd0,-0x5ff47fa57d0944f64a9b6550db645e67c8b5bfdc961d08d21ed948,0x3ebb49f1aa3cdcaf09ff61b639b2dede9b157e652fce43f86742f8,-0x24d65394b17d984050a507e3e5f2d1fd1d833c1607f058109aa720,0x13686c3e1af1bed43911bcf4bd979c5c78afc74a0b16ac211e04e0,-0x928bc8a55ed4b79875464457c0769940bec6d55b8eaa7694b35b8,0x3dd0bc5c28f275af97e2ca1ad0dec75c400e54017eab5c8fad688,-0x173e133ec86ad7ade172fc1091b2fa57654b3c84e7bff2f600090,0x7c38c34763acdbd1c019a1bb683c3c00c6270d99115f97250e70,-0x24b70d655e6688dc60e147d9efbf0d3309fe7f09e6bf9a6c6d88,0x98e20a8895d430aa9576141b3fca6de308d11e45fc53cd815b8,-0x22d570d2bac9362e654b235095de9a170e3556176d6adcea740,0x6e6aba0bc7014937bf8713c13b4e2add2bd5bdcc2176a118c0,-0x12ddd66c48d4c3c4c180229ce3f065b44478da676ec36b18e8,0x2c0e2f364342fb6a23d03e9d5f491b0270ff62f78dee2dad8,-0x56da72b6c085db7f5563102edaa76e106ba504d8c88b9a50,0x8e8bdd76b3d371e8f71ac11c93f950050566781eb7396b0,-0xbf75223aaef95b7a8bcd09fbedf9c2321898cf0e4d9498,0xce0b1d19e69f8d48e0245666d725958cbf7c032445c28,-0xad07a0204be5156bdc5ae792676fee3e4b44bcad5420,0x6d9f6e7fb177865b9802191cbbce6ed071f6eae3fe0,-0x3223dd858df9faa571883443e96fb07547fd585148,0xf9ba786566e4e3850658583d8abc5717bdbe2878,-0x30bda74d6e262de4ac9e44337eb6bd6cf0e6230,0x54aacef00e8466dc9c366112c08e41db0ced0,-0x43cd68c3918296ab7069e0d5a58a4f7f978,0x11f25cadfc4afaaf2cfa5ad32e647ed48,-0xbc667534ec7c458b4600000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 25 66 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 66 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 56 indices rho q15 m15 15 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 56 indices rho q15 m15 15 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r16 : List ℤ := raw_ints% [0x11bb834df9f063959a0f0a3969ffb37400000000,0x19c7bf7bcb1a18f8b00a0cd0928ac582e0000000,0x11d5662a2992173f9f8a7218c64a39d24a000000,0x7d02bb48683342da7ab6bd9799fc7a321800000,0x26f3624b9f7eab761b6d8b722e84796f6480000,0x930012209af3f88cca6d756befc92b15280000,0x1b47ca5f85fe0e5bbb8e8e88801559b4c8c000,0x4162b9839c461c7ba34962b0195678c7e8000,0x80c4784f9fa1da08a4edb78f3f1df4b2c000,0xd2fda7b86d1dde7cebd05aca22354422000,0x1222d5565e77adcf93819fa312bc90031c0,0x150f1289bed2276677610987351c19e180,0x14b79b5ad1649948db40aee912afa1870,0x114a7eb3e673653c5da0be16042ae440,0xc3c299b1e87eeb35b6bd2e72b11574,0x751bdc302f36e600fb5f65e2b48d8,0x3aec9496cb5cf8e316815cb59735,0x18bcbec9810c960c66a17a9af00,0x890601fa031d10b543cf18ff4,0x2676bc11b8ad033c9ed42f70,0x88ab1b192dd88fd85635ce,0x1721177dc2227b2f3d680,0x2ce5c04bdfcb6790190,0x37bad25f58568bc78,0x214c6b3594de1d5]
def m16 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea82098100000000000000000000000,-0x12dbc2184cbd28ac21fdd3fa652219036b6b70aa248354d800,0x11a91700c091bcd9da5451d3d47d30c493d03b38e729fca3200,-0xab18be6b277cf1488a071465bff1b664fd37d9f06137b131e00,0x4b4b2f3b645919d73df740ef01d9e7aa0b26fd626857cb1dc280,-0x19a9bc5b470cd68c379e53eb1274d71248a5d902ea52acb765180,0x70cd975a32ba640eca5e2b4ab14f17cd8c958b6e5dbaad75b3e00,-0x19aa62670842906425e78bccea0e7884410e489c521d4222656a00,0x4ee89cdd38dd5bf06adc1c92d5ca08922a375eb9fecf316b08ad20,-0xcfe7c4bd8a473054d5a8f58d53f2921aa3d395e9d26e9cbe689de0,0x1dab98e1a942e5d07a5ca9edfa25b13a85b803ef75a4a93286c9280,-0x3b3ab8883fea5909e3db6473be7ab42547de0a1cb60b029af2fb780,0x68164ff1a7261a59ce33c7a87d7f1ca0a1df939f78db1fa8e63c120,-0xa1ea70667d7339ef4d141c4808f61c2bffb978b34e5fc085c83bfe0,0xdfed4fcd320ec53032a315a109c6de3b5c157b4fa539e14f12fe600,-0x1144592fe89d35690136132434d8b7112ace5cce708d3e6a27848600,0x130e08663f8ac2829361a5fa974e605a033fda35e7b882cd77d8f848,-0x12d85e4cdbc190d776f48007e417f8c94f939c19570004e856e77a78,0x10b9d6984cc1f6b3f614e6e32a50f1e533d030f657597cdd135053a0,-0xd55321164a9d97d7513d1e04a4fbf80d36bf9ce2124db9a12cc0ce0,0x98c4f7e79f87fcac9352bedea56f82d76eb8042cee81eeff5c14d28,-0x624427074fd280c33345a965ecdd9a1b6d9afa0df0b5bbb4434a818,0x38bbd93542793acd1422515b4640f7f1ea4d709f94a8d83652cc080,-0x1d5d7c32c62df2f195ec4665248f61b191507e09107cfce6b270a80,0xd9a69d36f79ee631db36a4e3b45c1388a47fbff33e4e950efe5928,-0x5a09320dd8bd840b209a528f38f3ed1f0d78b913b00610860f0598,0x212a9bf8065ef54ba8cf89a6d22d83f122ec62175cf8e0ad665720,-0xad793edf1832c5869940ed1ab12a1b0c276722fa0bffa1999c260,0x321da0ff08d94e8af8686d0ce933130dcade402a06c431fde9288,-0xcbb4ad5c6c095ee0dee51bf0cf4990419caa710eb239f36f54b8,0x2d3d40884abc322e13f0284449793f9c6e4a50ff2f52080ee800,-0x8b8acce30cee11207d286b055d5217a293b4006559285344600,0x1728a47dfdb88697a54800445e520bef05b8af848c068a787d8,-0x346ac199905dbab9c1873d7c3c4dcc1a5c75a3eb4a0b09c268,0x63eda59c79837487a24402ed7ea085f3bc4dabcb647814be0,-0x9e2b91e75ae0c7bec7cc8f610081f9a7c941dac6c6c9d7a0,0xcc419c6ece750d7d3bd4bf7e6037257767ac49b3a7491f8,-0xd299cd1637a02a3d743a3825e46ab071d04979c8f193c8,0xa8bf5911305716b37ef6d28baba094424dd3a500c5b80,-0x6584f142e4ed7b3711ff65fbf9d4de7a9bc19827e780,0x2bd832622325fd0f115d6c93c851e55b8b5875eab98,-0xccd3c2bc11ded78e0ce920e86af1411c45d7c15a8,0x2533ebd8ed132487f5d1108a8ecdebbced791ce0,-0x3b948b04cfab31a032835f704b3c9ebc655ba0,0x2b813b19cdd9f87b6b7225d474f190c8d8b8,-0xa5d083562176bfeaf48ccecb203f19008,0x605a938a395a82a611000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 25 68 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 68 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 56 indices rho q16 m16 16 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 56 indices rho q16 m16 16 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r17 : List ℤ := raw_ints% [-0x55b6844b8b265d1ad654fc0f6c6e5ca9628000000,-0x7c84116893dc75a96fca7496580ebe61cd5c00000,-0x560fb09eca728ce2dc06ca9766dac537c10a40000,-0x25ab8a574c3bc0a4e342a37858a6cf0aa0a9a0000,-0xbb9b97e285057fc15634142b57720b684fb97000,-0x2c3438e6c406b61cd63c71e82bfebc6c3f73e400,-0x83196d0d0ec5002cad977a508d105dbd7a44100,-0x139d014ea3f54cf299a31abf93a914da2185ac0,-0x26922f462ed2a868e7dd495b928b8cce0f77c0,-0x3f1a41fcef1f258ecb138307dbdb88c62a630,-0x56a35a0d25e732eea2eb0c6e74dc32328070,-0x6469a6042a5b7c7f3202cd228b928356744,-0x629465856944747b48049b3da4b2877d94,-0x52169aebd1bba372367f245f049144e55,-0x39eff5b836590db1f4012c11e47182c8,-0x228f9f163aee0b296639767a46b5392,-0x1155851f86750db47cdadfb30da044,-0x740382262c2fb542be56707e19f6,-0x27ffb714c3b277751afa19d3b60,-0xb2ce6452cea48e55f7b351ab4,-0x277e3ad75ed7ac8d72745c1c,-0x6a43beb1acb9ef3f3161dd,-0xccbef5bc1635151ca728,-0xfbe60fa467e50a5b5e,-0x94e6f054e6b4578c]
def m17 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d5041302000000000000000000000000,0x2568204f52696495d139a1c37c28d076a0202a49a6be7462800,-0x22bc1eff1213b8c184fac9b1d4abb229a2f23b4dd02d657c0e00,0x14d988461437fafd073d2bb46c440881a59b125b431e63af5d200,-0x917ebe8b2f3623ac88413ae2fe0d82f500ffd1a5b34f6c7c89180,0x3122bd45e5bf9458e049597c35bbf2c2f7ca2cb65bcd6dc3e50a80,-0xd5f0b9497b45beef3c4cd5eb8c0341c4823a15989412f4d0b45b00,0x3034300d16341c3b627c7a75e32c5f02f2b49ccd7ba104df51c7500,-0x92b7f6d3f4233739581cd9702669b5b725718ec5f48ba01f0d8fde0,0x17e93c5ae2c319e2cea789d9388997bbf48cb3077e546a768b6bcf20,-0x360423c54d0081b2e6ed96b418f6b948251881ec19cba84f2bb6fec0,0x6aa4bf7a22575c7b7a333f6ed4ed62109a4945de5ad09a43811ce540,-0xb947a78019c8a22260f0fe13d7a6054f9a648e1fab7465a4df343ba0,0x11cd3ed9abadfc0d2cae08c6f7f8a5e1edeb5142e96cd57df4042a160,-0x1851dcadc706411b62eb92f5a41a13edd8fed03267a5881bbc09d5680,0x1da04be218e6df2e2dfc8815108e5a75fd66a4cae759cbee37592d980,-0x20440ba3ab48801614626746cd0ab61cae61aece19f11c8faf3c00038,0x1f7a2a8e771e4e4b98e59f3ef3e3d93b2eb898da87bda79c12056c108,-0x1b8af3845aa9e9541e197055a4afb8ffa14f59ca8a37e9052d84577f0,0x15a1ec36bd0fc13ed235ed5f0fa7b6f82aa24263eb1315ee1c6717d10,-0xf412717e3c7e29db615a2ceb0424f918445fe4f6990d28ecdfe715c8,0x9a7c5b90e0f145ddbbf754e611a627357a8e06075d2bcffd83d1c678,-0x57b3d528910b08db53d8c56613cbb2b830477b404bd1c1abd84c2fa0,0x2c99e22ba333793068d888a1852868fcf59761737cf595bbf1ab2460,-0x144859bb3c05eb1ecf879273c92bc70ece266e7231da5059738af0b8,0x83a9ce24209d57406cbac97c206b386c6610f5e486fb53c46188788,-0x2f84f22f7c1e9667729917d1be6f3f17eefd4974df2f51ed6ae90d0,0xf33e6772279441c79bcc92b83eefc66b8b1f989712bfc138daa830,-0x44b04ebd22c55133895c4766a023633a4827417aca73f5f1a23b08,0x11089cd6413036ca635bd212e5b87aaf8f14bb5ba1ab08d3900c38,-0x3afe23c8c52e076e0a183e68917fcfb3e7d6fa6265b1628eab440,0xb10f244b7f1ed19c695512a0ef7cd3f02c3aedfd5dd1217f0bc0,-0x1c8a09e697413c06eab448797be0ae2b5537ea56778fc88e08e8,0x3e9a599a7d4fccd8c1808096f8e35f9a97459998595c375c2d8,-0x7363ceefb589a07e758065532315ea9fcc9cd8946760d91390,0xb01b96d00d86129382e3ce3c8e27b2a402461ba0e8fb8b370,-0xda99ad1eb28a43b7a0a0dc5d14ebb2e92b9f384928c15418,0xd7df70d081a1647ace448733a9a67d311c3d2ddaa22a4a8,-0xa4fadfd9350b9719723af933fb388bfcfed2ae2f6368a0,0x5e35815217c79fb58dfb8d0c5f2ddd9952f6f15fc0360,-0x26669acf92f29362a2158cc6a3fec421f11bd0286048,0xa82f8972123e026caffdfcb60a29ac448a2f697578,-0x1c69ecb850867b4ffc079a8a8ade6e69cbe9ed8f0,0x29ef320e778b82c2225e1464bf4cfc10d87ee10,-0x1be91fd3afd4ecd8f85a2b7d0ea4a1c5335f8,0x5fb8f0782e13153c0271c8bb2c11de64c8,-0x314411edba72113ee18000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 25 70 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 70 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 56 indices rho q17 m17 17 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 56 indices rho q17 m17 17 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r18 : List ℤ := raw_ints% [0x17f491cc7b37e19a7ca83ddc66c880325ee60000000,0x22c66a0faec5c1a790dac4f5f716bb46fdbe9000000,0x18044230d360ddd26f1e90f2f20f17a86f551300000,0xa80e538cc732310c35fa584160d02cdb1484b40000,0x34433585777c7a4767f4c1f10a5e3314580b5a4000,0xc4d44148da7456d7231408ee6dd1e6ad5e1388000,0x2471f1bce0e6f5f113306f2d3b13f693a2da67800,0x5722ddf2241105327cfbbd16a31e3950d7259c00,0xab23eca9840acd3c59647f3ba37ca485e97ee40,0x11798645de7aaf505b92df9b9a840d61f00d180,0x17f49d6b35ff962de5e241c4ac1e2643b15210,0x1bb7b018146020f0fca5ce04108083b174900,0x1b29443fbb96551999819eab290a3ff0bfec,0x16923a9f119ac47052de42530ad5a6c7038,0xfe50181ec202c51043cb553ad9a7d508b,0x9752748088368e53b804bb767d20ed60,0x4baeaa0a8ab233059f6b84475c6067e,0x1f8ee3dc0dee36baf070213157dc30,0xad782311e7081e6326094437408a,0x3045308a116cf2512abc3159100,0xa9cbdb8bd98664f9929aaef9c,0x1c6714ddee08de6ab0e37658,0x3662eb12f46d1c46d23e83,0x426cd47527a7dc4aa860,0x26ecfdc16ab330a212]
def m18 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa0826040000000000000000000000000,-0x4a366f1a2b21fe72e41b578770fc93e5d63e51eeb311017ed800,0x4457d3b94ed926b2a8dcdca9d992ec949c410af3f1e68b205b200,-0x28acd7e61fccb1a8782af3697f7cacff7d2983038b6e4eae7ade00,0x1195d7effbe3e953ef5431ec3f5038bc096169657785491cc801280,-0x5e2adb384985ec4aaf67fc69415d23d12d35b9cde283ccd33b08180,0x19637fcaec1d1cbb675274fd225e4ff795d2252102e2e90a13fdca00,-0x5aa788bdb4410e25a54686645e2a1fd90a1e025e4ad3d10efcb3fe00,0x111369db54062758e7c65b283e25654dc5e283e61df05ac549eea8520,-0x2c1313b5208acd9cdc82f2b99b2cb1cdea04bd6f83d0b87527ce9c5e0,0x6285ef6db55dc70a5e3456638a7658893099d6eab9560a9e8ac8b6580,-0xc0684174e8039322ba492b6a77bfeed65b1cacb29cfe138850675ac80,0x14a8a44ca4e038bf109e6166acf24c9031f24c6d5e1e08089048545d20,-0x1f63e47cd9fa6a9168e3f853d17a1b1d4a69f99da02bbc3d55e33c93e0,0x2a5e55449ae168f4544bd04751e6b06ca6e0cc92446a91988e74823a00,-0x32f8513373675d319edfbe7bbc346a0e47c9f8ab8660566b4225146200,0x36cb1d93046f330b7df873d5ec9f38f4898bf7f9c09b6f42edaa3a9848,-0x34bc5d959152df712ff9cd018eaf539111ac8988ac7a2b05bb5cf92a78,0x2d7fba9ae1ab8f7698f4b68c7be3137e5a51e8631dfea4aabf1584f360,-0x23370cb3a97dd2330dbc9456f2f5bc231caf4e8fe5737de9c5f7e57720,0x187487ad8fc9419c5c9cf3e231bf7012b72f9d3eda698cb8440a4dbc28,-0xf3bbe88ff23b763379a327eb88e84112ed38d2fa93982cddf08d1e518,0x8812c3c968e090f1a77efcbf6802885b89d3b9e99eb2b794f61b8b380,-0x43ff556a7b39807ed4e32c10afcf560a0e842bb85528ae2a8d197a380,0x1e5bbdde4117539b0f23a9ce1e835043e27f3cfc93fd49925cd40b5a8,-0xc14ae5b88af26266cdf07d7aa6eb5b6cafc0be3bb90da0b3e1b67918,0x445abd607bb75fd8b27d823cc4d8bde16e58744c9ee1a7e9e8476de0,-0x15671fb132fb7aac8a659eca58e28f973d125dfdab2bcc669e78b9a0,0x5e864871a5b32e19ac0437e0955545ec9af298151d1750cac7d6708,-0x16e18f7f52e4615046a0d25fb009cf6d1706cbad63030a7f8b88c38,0x4d3c137190f53a56f895328c203f3acf50a81216980cd5c4352800,-0xe18bc68acd73157ca517a543fd7736aa066de84265844dbe63e00,0x234dfbc22fa724cd289ecc421dbc12e2e614d6d5ddcb2cc1ef4d8,-0x4b0b93a9987b44787c5c08279c79804a41ffe08b57dc992e2568,0x85b6e9f529e181bb1115b2f37db8c0b539a7860a01a1e924120,-0xc4badad80b222f12f362880da87a43313c4e5a61a793084860,0xeaaa67944826f854c63af931821d7a1844414771d576e11f8,-0xdde1e2b0885bfd407729ef938f2fa639b3e57af351a3d7c8,0xa1adc73b1ff054aae4054621735e0c62d83e77c3ca28880,-0x57988ec6fc1103bae071e5683a72ea4dede1c06c9ee680,0x21aef15584cb3d6f4ac9755aba874a6777c4448023218,-0x8a3d770300d6ea6bc34e7fcc054b24fb954a0819f28,0x15b6914a567b77cf229ba96611b464e584c1dede20,-0x1d84d8de501fbbea402ddadafca3baf55de4d460,0x11e746fae66eb8d1354dff5bd1ec194a8c6138,-0x373e4a949f7e392ec974962a69de6fb9b88,0x192efae38a36c0932e40000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 25 72 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 72 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 56 indices rho q18 m18 18 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 56 indices rho q18 m18 18 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r19 : List ℤ := raw_ints% [-0x6432a98a52e2778086b1befd2f4944e3e5fb90000000,-0x915b4d14aea8062d05358037c79b9dd340ce49800000,-0x6450b217675c70dccbbc59f9e8f00f1bb046b8680000,-0x2bd6875c4af281f3a6b97923cda43afa732350540000,-0xd9f13ded658b37a89e5da56070fd65cd0fc2f9e6000,-0x3340ebe1e73fa85d0909a128707f2d5616d8fa7a800,-0x97b14e296445ce02ac1344e163c89a9bfb76a2ca00,-0x16a4a6e08b6f0328c218f3e91668c4f80323dca380,-0x2c6ba56aae8d74af104bbacf3c4d4633b42b3e180,-0x487a6ebb8e80edce9f374efde9309969a9ebb3a0,-0x633858f6d6dc2d2ba49a5f14a967e891732c6e0,-0x72a091235b66f841e968b865316d3e72142b18,-0x7023a0cffcf6c5757b9e46b79eca74f037cc8,-0x5d048e363464c1dbfe67dc529f09ab6dc786,-0x415ec82aba85f0f60e6ad46fbe402625c18,-0x26cf490336598b1ce785818fb7f58dae31,-0x135cabb6bebd80bdfe67f5f03080242b8,-0x80d1a67294d8ba86434ec7f24575570,-0x2c1e35e5b81003828c2375cc7f1390,-0xc3bbcd87eb85088c97791b6ee806,-0x2adc5fec073c50cbeb8a1f0cb78,-0x7230d9bea009fd0ccba1e4d52,-0xd982f248e769f0c54533038,-0x1080b0d4a699940c74b549,-0x99a0b289cbe1eb1e2c8]
def m19 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c0800000000000000000000000000,0x9342d843aa7d741fd76c55cfcbc45e8d4f18bebe7af0f2e5c2800,-0x868534d307ef0b1ab0c1127e584ea9bb51c3fe515bfa07beb08e00,0x4f65a341c8fcb2615253e3bd4778da27ee6c8471fa0d1add58b9200,-0x220870850a8fbffa86f18b26f2eab639290591ebd6327aa232ad6180,0xb4a3a8471c84155b3a1a1a2f8485771453dcb27820545044cc873a80,-0x3042cb4ede961298d35d5e846e423be8d46495ced9bf0fc292015d700,0xaab6491e32357f666922a34f4ab901c8078d7ea0dd79332fb9d411900,-0x1fd86572409400059958247b6b98908365f435df0d79e8e2adf40a5de0,0x516075a5dd2b5d24f49f5edb2aa2cf5b4cb9fc7f94f46d3159bd50af20,-0xb408b25af982ea9083a338b2f479025bf28de7f549f891263cb1eb6dc0,0x15bd838b6a0cab4acdb53a821088afc120169d7bd26eab2e9bbf0fade40,-0x24efa5eabdbf1f9ef596530dc6127ecbd2ecf2d314e94af6793060b25a0,0x377b51b30ac8df5c0ab070f23be13a842e4c2901a7a2583c2310de33760,-0x49ff8d66445b14c5b0899a628f557294c29bdfb4b47948abe4a32bb2880,0x57ed153a4199cd73a1263e260083091ef5ee5d7fffb10b8c362ea8d6780,-0x5d504caca0de42ec1159c1eff41e0c913b15572d68068722277a23c8638,0x589d976e5f151a3df9e5515f5de1ce741fe280759b2039870875a1b9b08,-0x4b658656f071d727292402db1f9eb1deb9f8e63eb42a22ef0847969deb0,0x398347a9607e242ab86a2110c93c3095f1dc5cea9406cedaaf5573c6850,-0x2756931d99d0c1ad28c26eadec717f392417b470bccd53424522a091248,0x181e41f0a6c0916c99bc11d1fc04d8d1092f4568830d51f18c8e3bf29f8,-0xd3e2b465614d3d3f6696bdb0533a0c67bbd65617d2b9d9d398ccefe420,0x680d24e979f024cff47f1a061a08d87575a019d3ee3109d7a751f257e0,-0x2d9c9f3f3a333bd716a44ed5e459bb1705c8730909e872fef874e143b8,0x11cdd81e00e458018b7cecce48f9827faba79c681368e48c840deac088,-0x62b5ab7b0ccbef4a8f0367907ea3b0c67f38174ea3160276fd61abb10,0x1e4019dbe611143eff457badf399dfdd4cc1a36f4967532647a44f7f0,-0x8297c9534c4c85db9bdb222a2f39cf16058b58791c64e275e7b06088,0x1edb73b70cd02b23cb5c3341dbb01a8f3b23fe7d7b98c79043122ab8,-0x6583468b6f230cc8005b95070b0b8e9f51bfe477387dd5f9ef5d940,0x1206a34e2f9bd9ea17eef210de8b7125379f56f1168a77501d7e6c0,-0x2bd6590b0104ea48f5c27bcf8fc6db43f62897c9815e1c273988e8,0x5a48ee8ccac89299d7b9880a5bc17f2bb6012bf552c5ce572dad8,-0x9b7b109f26d4c299041adde7a0a687395e581cce9641a1bb06d0,0xdc78e4c32bdc9e5ac6af790bd227fcb070183741b69a4080630,-0xfca717e233311370d80b30704703397ab32ed787ea9866c398,0xe4a86244a248f3c820fc9dd1cfa66ba0bbce086beb1c6dd28,-0x9ecd2f855f788b58ada95ac4cd42a400544b8dcaa118e920,0x5198f3c4959d56e1634a0c50454390eb5aef86257fc1ae0,-0x1d963afc3cd777d3f9f9d4648df5eb8f8631b778cd6748,0x71bba58539de8d6e21358c4e3825f3099c4c8e9d6a78,-0x1099d33a89c2a04db204070351fe62f3ce0846dbdb0,0x14c81492e8af1a3e086f8df504621ca6684424f50,-0xb7b7b22c6da6164c88dccd5644f1713bdf2a78,0x1fdf79992c3253d79e49b3b4eebfa152e448,-0xcdebd544aa7e4425e600000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 25 74 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 74 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 56 indices rho q19 m19 19 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 56 indices rho q19 m19 19 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r20 : List ℤ := raw_ints% [0x18b73200b722b94c3264438d5d2feac9b3fe8240000000,0x23d52e2a47528c037f98a797a41014fa0be555f6000000,0x18b67e4283d6ebfd8a9fb69d2af1a378c00f554e200000,0xacab56a98e61e03683c916071051fd7a28f27faa80000,0x359c4239ffa473cea7283004eb2779eba1554daad8000,0xc98d4f0a5b6977572835598b46bc0b797427f71b4000,0x253fb215518f24c86e3628cfc2c24cb3e2e06e960000,0x58dfe272e38959812181a7fe87d5e6c7296d35b0400,0xae2a0f5dd818475a8c717f9ad27d75cdcd11d93280,0x11bd7e15543b98115e1cef9efd6a8136cdee8ebe00,0x1841460c3ccea0af21604d4f0e9217ebf50bfe5e0,0x1bfb8f88e39a99372021222d3cc05f9d2b126fc0,0x1b557e6a04869032bb947d1b39acaa1e4543608,0x16a2b6e0a3cb3cde301c3736a560a93b4d7380,0xfe0f3e35b0a62c8b27545ee416c7c7366dba,0x9687c423aa31f59c4b7d9bfc3e410fa41d8,0x4aeeacbba6d68b09228abd6bcbd606e02f,0x1f14f72264df967a074519deb885d5280,0xa9d9e810428b4a4c2d31041bc1b9990,0x2ef3d6cd71739f48cb6a9ba8a262b0,0xa3eead131b576f6074c348708fda,0x1b308ea7cb245549ee69b898dc0,0x338f068e86cd80d0a2b3ea0ee,0x3e43fa9b96c84edf402b5f8,0x2402cf6ab89bfe6fa3957]
def m20 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea8209810000000000000000000000000000,-0x124444505082a3f402c509eb55c827731c93ff1910e32d69d28d800,0x108e056b3b3cc1541dc89f0be4b10a9a64816efcbf9e1b81b7613200,-0x9b115387d8fe2b001e22c49594ea3599e89af178e956b8b3173c9e00,0x41e9bee6ac1205cd50aca0b6b9a712f2cfa35918a3b76069246e1e280,-0x15ad659a099f2f1925a95905a3f2aaa445b63ac5c2a39ffc8282833180,0x5bd70ff0ce179070a7cefa354ccedcb51112e0d73855e7a9672355b600,-0x141e237790e5fc559a164e3af2c62be0b3573f79a88cc3bf352e87e3200,0x3b7a016cc9b63d182c0586aa99ffa087d0399372b28097f41e1c1ce9d20,-0x967f38ce12278fa20fb0a59fdfc1361d59df9111d03099a3d04b9dcade0,0x14994676c77746a58216f649c8b07b960a01009e97c5381f03913889d080,-0x2761b31f0a4b99a10c2d2d73b7e87f3eceb4f4cd2c55836559ecb8624980,0x422e75289aad99265935b0d40dcac85e0b28f956db54c413efd64edf6920,-0x624a96e6cf1da0a107c0564f1ea17fe1c0ced27b4d1b3091d9273567f7e0,0x819008fb28bc037c1e40dcc418f54c34301cbcbd92cba4f50c39e3352e00,-0x9814359de1d1d7d6b179089b5cce2f450856d147431b5b3a99d9ce281e00,0x9f5bd8dd0477d3c102ae70fd3eea7e2ca3dbb128f14c4c0d166a768c2848,-0x95586f29e94eed5464cb978935d77c0306aebdb0925948dcca3bf156ea78,0x7d535be405a572f70dde02a7162b3febb6f95e79cf75a4e97c4452139120,-0x5e3b4684a173c60a96294c0e88a5261341afa44c2934c59df0b25d9d3360,0x3f7d7c3bd22469e05e6b9c5455244485b9e604fbd104e28f59359d8d5728,-0x26512b8d8af4c3ced60a6463cfd93091ed8c126ff93a3bed47c49d8e3618,0x14b1c7f52dc8c613d779c388ca2703a12cd9af51cd8c009e83f94033be80,-0x9fcdcfaa464e4b1cad05adcaf386da04242116a28d312a318f8bed34480,0x44c902ffebc37225eea2765f464d152c542477285121dcfe5346e235e28,-0x1a56a6fc3c7b29aea0a86169f5d8bb4fe2bbb5e61ba96223e977f48a098,0x8f17f57a1a1e75e48a2c8d3c2ab682f528ce66bb4f8371e3dc284b1aa0,-0x2aebd1009db506ecab5f5721e311dd72a986d8e2d09b8b8e7eb2e3cae0,0xb52009074186d3c8ff4fb35e42637515b745de5fd0c1a963d71757b88,-0x29c65abe5556089e13b5736c7c39a69e8a879e9fbd357873d9bd9c3b8,0x85eeecf4bf11e512db6b47874634d58b8bf5108d8ce690c21e35e800,-0x172317b369591c85e0ccf037f1fa570191cdf673e29897275abff600,0x36a188b3d5ae098cea2684bc9b5ee71bc063428d34c8d37fbafe9d8,-0x6d002c57a437a091a7e9771f9694dc29f4e2542307e351a5b90068,0xb5645ce3c74ed35a189cb884dc33b51d3d1c4b73a1248b7e62060,-0xf7d8db1b6086a3e83e5fe7d6744d36a4034570bd235c66e77f20,0x110ca142db742f848a57c1fe73118ed1c9a198c097aa9c0b7df8,-0xec3b95306f99230e21b6e44e70bd6e71fd27252102db92efc8,0x9c4f8e87310bffed9aee4d78cfb4620bc6f9011805e2c1d80,-0x4c246daa5bee38dafec7009618ebb63eb44220fdf7b69d80,0x1a05c14250f4798434c9b396a2d437bfc78326258a97498,-0x5da6a6c075a67ec59da88ddca5638923522dea5c86ca8,0xcb2a2aa22e5197325e3633b91060facc4364ff28960,-0xea1a841a924834a413e7ad83516d2420b8bc57320,0x75ce6b1fabbf66c9ed7caea8648f4b3af15e1b8,-0x12625471a9d731513a1acdf6606d2a5366f08,0x69362117fa1081d071000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 25 76 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 76 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 56 indices rho q20 m20 20 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 56 indices rho q20 m20 20 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r21 : List ℤ := raw_ints% [-0x5cb1ef30043b1b4db1fa5e1bb1b4b0776939fe538000000,-0x86500b86d803a3fac3efacc8baac2d86e42daae73400000,-0x5c9321ebf8fad62f045c138790a78d92d0c2c6e08cc0000,-0x286644f8148deafc89030c18e1ebd98a106d15f47de0000,-0xc88c458fc7046dbce3fbc499ef51c69952b032f270d000,-0x2f163e397d1ffd695b937690b3ef03d4f7857b7af90c00,-0x8b1e12fa50220736172a803d56c9917af22805cdffb00,-0x14ba12c9f7777d60c79addca18ba3b50114442d63da40,-0x2893eca55346465d587701ec3c670461a10122250540,-0x420fa5e935daf91740ef5e8df729b0d6d07a1f76690,-0x5a376aa4a664f90b340c0d1716d2ca860a46e8d7d0,-0x67f35e3a60725a1432544cc0c77a61f6e45f7ff0c,-0x6566cb500b7ecb3de8d774bb4b1213882efb1edc,-0x53d89370355af114e96a3b3da96de41b8e0629f,-0x3ab884464cba2e5d79406bfc454986137ecd58,-0x22bab19137ff57ef90c92d7e5aef4a1d71828,-0x1140e2b0ea612f1390bed330a122fe115e9c,-0x72417c43b0ea251812a15309aa6c48877a,-0x26ed79013485a5185d2c32d1f851649a0,-0xabb4a80838b30c893f69b0c228e2528,-0x255acd3adcd8b4405bf58ec10ac994,-0x62ca2f60bd535c594099a02a974f,-0xba9a6a6aca1f5defe2478091f8,-0xe05af997dc1653e409e9d56c,-0x8118280d9c85e12cb547f4]
def m21 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d504130200000000000000000000000000000,0x24429c9bd9b8037114bb9a464e6a8c6f075ebe4090b827fd07f22800,-0x209be799326a2ddb66ae8e861c6fac62f73cd7056188a3dc5f4c50e00,0x12f0619bf535d27d09922109aec6265d90035eb32b033d587581135200,-0x7fbff9f2d78846291be937968b3bb367952af28cad441c2b830e13b180,0x29a8dc9a578033ec8c79f6de661844debc5f76de8b704f8a41b799bea80,-0xaef62f1d927ac66a237d062105dba57ffa48b56d459021b9da332983300,0x25fb1a89e11262fec57d1062165d3da1a8244031e1e127a792695dd5dd00,-0x6f3e5654984a9047bdc31070d98bdc68ee6f11cdaa1fcf553d845dd63de0,0x116c7317b7e28af6a7147c6cd15dfacb43bce5b958b1755af82fa9f210f20,-0x25c6dbf5b0361f6b263d2a1161d0dd3d7f8096575817044cdef7730b954c0,0x477a7623980187f1bc394866193c6fe0e9adee835d286dc6c345451729f40,-0x76d5e4ad6d61dac7575ed12e9ad6f06c511e29fe6b15d37fdb86aa5c28fa0,0xae8855fd9f7ff2e45b0cc7e8f4f4b672bf7073371bd18224300f011e7cd60,-0xe36810b8176eefea5c1e26631d07a9790051712eb6b4c022d1b791ed92a80,0x107b9c2e92bf3651fbfab8d6aa4eb3ccf3cc8695029a12ffbaed6bdc62c580,-0x110e66df4d47385dd1df3b8d549c64bc1830852dba2a0ffc2547d07045ec38,0xfc6cf1b17a508b650906cc9822d0f76f7155f4041730dec8e42ba1eea1508,-0xd0f3ccc93f07456e08067775bab6570243f983a992fea0f580fd3a7327b70,0x9ae209e914d367cc4d49de8ffcfc0a0ea3b5bc98fd763d10124d3037dad90,-0x66cedeb5ec86d9e5974ee1df690e65277ecbf5ed322c599cae30fee576ec8,0x3d152174e29dfd0494a649f07679722daa6ea0bc04ddc006f4831217ecd78,-0x2073d728107a702b68ce15e7442122a08d5670a2f8f648b1ffbc5e8cc84a0,0xf6503473eeb3f2554a414f73b252b3a0c1a95d347437e8c8e0a259e5df60,-0x681d06e7875864bcc46229169e463bb184c9e1da8282654a73a6daba8eb8,0x271c0a4c7bc4263822f1b4f170fe3dfc969f07bc28138affccb30fd32188,-0xd0381b0ce6d353ff27b51be0f4c468d43b4feafaa967835f7b50fad6f50,0x3d21966ee149a87d6081ae1be09ab064ecfe33e15b067c61dd3f9d68db0,-0xfc2b25091924d6bb27d17d02e1b1f469e3dcc2f0520915e39227601e08,0x38c50d3db47f9f349e42380bb8c2c22300dafbdfc8757ad873d76f3138,-0xb15ececa24e057eebc3f93ab028016e1feca331aada45d575cd4a1640,0x1dce7793cad4815ab7bdee65cd17aea74b8d71812669e459d0143a9c0,-0x44532b3664f06c31d3e7efd6697767e98eca63e4b58d6e8d37ebd8e8,0x840bbb592e139039b050da8fc0cb9f20380ee2702fdacac52fde2d8,-0xd44e2ac8271b8ec11efe4bf27930b39f47c1080cddc2be9d3b8410,0x117751f7bed61d8c22b9ba32a8d629deaa1e01614741f3521efef0,-0x12755ac960ad205e2d0faf121a64c4abb8ec73adf41b5d2350318,0xf4a58c1be72334dea0dfcc872e97a3b108ae7a77241f23fe5a8,-0x9a2c8036a1a73c7e0faac09ba9a7d7af86027baa0c651115a0,0x472b2cf94e18d845441e6cb5bc800860efebcd7a020044660,-0x16ea56f48ccccd5a53cee902194a9d7d4301990375394648,0x4d2ceeee14a4b04bc81399f6c2d99e975e781b8d0a2778,-0x9b75160920b00021a0b3e80d146f6ab67a27c9e42070,0xa4d48d0385d8034f4d94708e40c71467313e896290,-0x4b87129c7693fe9cba5271da78d00a7eae2a56f8,0xa99d30f1ce273638880d711308ff80d8cebc8,-0x35be47778ba790c2998000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 25 78 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 78 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 56 indices rho q21 m21 21 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 56 indices rho q21 m21 21 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r22 : List ℤ := raw_ints% [0x14c4c863f428707148b32a81ee87d518ed966c24da0000000,0x1e13c8ba8e85301c3c5f859913dd97b59245cce5157000000,0x14b80633757c17120856e9ebfe2682adaa3bd5af1dbd00000,0x9093e193953083dd5e8e305d2937bda6a577e15808dc0000,0x2cd3969f4001a54b789990ce60e59bc6468ff2e9d255c000,0xa846fef129db65416e8cabffd4cec26583c70bbb7f34000,0x1f0c9d9842a2add0e805b8179049b229263e8036dae1800,0x49f42abe75c29dddfdfd980dbb9bb0034bb71466464800,0x90a6d79e67178bedd2fb628cba667d290d6a6d9077cc0,0xeb43aabaaafcc585956e5d25aea3fe02c3693f45f980,0x140f2d6d13cb3c022691f22dee647adcc52151df4930,0x17162088936f867e5325ef149a4ad1efe4783c064c0,0x167dfae8562b943679481a0b572b8d186b0473f7c4,0x12929c7904962230b03233c954f76bb83b46bfad8,0xcfce28e43684160501de0b8fae0050398238a81,0x7ab3add467ad4e3c539e8799c8fbc318b08b80,0x3cd95090ab78ffa34b41424e9838311f3b7c8,0x19228692ac27794f7616d2d571e9f49c0570,0x88b7f853d8afb72cfc3731e15d7b65ae06,0x259978fce658d62f271bfb61fd36de600,0x82861e47e4be137fe57595de9bba288,0x15825b1f5bf6c5d07fad50ae7a0478,0x287d97a6ab6395fafdc975e54451,0x307ec9966fab5a30ff23b6c380,0x1bc834a2b99f27e74826b324]
def m22 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa082604000000000000000000000000000000,-0x47fdbfee714a523bb6e72904e85bf0171e47909d1864cd7a3f652d800,0x4041566618817ee12c4dba8d8051b9346d79be9253bc90caef23dcb200,-0x250787e4b447c1b435c12f0feb8ccf8b9271b02bc5522cdd4dcb6a85e00,0xf7c70e4e4032b1a522fe3ff7008385de612ddf945cbe9b6a7b0915f3280,-0x5022307c97ddab31589ac7e77c077a21850a7990cbe88f4f06edd6f26180,0x14dac17a6a310eb0c209109d3f750418424b6fd5a34d418e21f3a4e1e0200,-0x47cb81bfa18b37a1b5be6e0305f4e940d6a8901185daac228a87715710600,0xd05d164a023b37f50148466f44790c516c69e3053c279d6a66e6a7abcf520,-0x2053aaac0b262d90f4918e27af5fa8f0c88aa11c77c8b53d3571d392d955e0,0x45671e5fd45f55fe0c95223be8aef75ee9f8542d4387331259a94d7b0c9380,-0x81fc55d3f5f6175b9ccd49f58b39a303c12f7ae57a9d5155d949938b42ce80,0xd5d45c25789827ab929bc39752673a34deb94d498d5604f82e081c2bdde520,-0x1369cd6ce8495f555bb3c4dbfacc3c88e51f6635ad48619e00d37048828ebe0,0x1901b5355f4360d3aed5616cf2383e3f1c1d9ab2e76aec6a804584cce564200,-0x1ca835fd89e78dc924f8f6aa2c2c9343d20b4c51b810b69498a0296a28a3a00,0x1d49c3bffa33d363f75e3f76587994f76c9e5a1390a2c2b478b949e11d4a848,-0x1abdff124e509e17948b177e742d50dc21d79f518f1e3ae34d7684b5ce1ba78,0x15d6d18475d486b1cb65cf849184250e506b61b6f6d4b321871ddb0c8dd1ce0,-0xff5e55d7ca7896ba40a1676aea3e7ba027c6ee0ca71786b8d902a60624d1a0,0xa703ea85c09c201bbef8edf0e39288c868c9d33864ce7deb752346eb9d5e28,-0x61b365003119b78b03cf5f073f6ac8e4f6137e739441f4cc0084c2673f5b18,0x331130076fe6dbaa26efba4c154ebfe6bde482e76ccb8f953ec22efad24180,-0x17d001674c123e02dead4d1abcf2b12f1e50d3f4530cdc5f722f419adf8d80,0x9e28177902d2bb77a0313cf1e39a560ae570bba47d52e796ce7ea7db712a8,-0x3a4961fc1a04c68bf1d1df11671989e3e77dba1f1c8a59177e7500151bc18,0x1301cbb7161d5730a4177150bfad3398e0cb55f9467006e7815130f8fed60,-0x57649d7791313dd47157ce174171fea626afc83067f105c38b5194c8e620,0x1606448f29607f5b4e0b4ea1d41fac7d54d6317c33f72b6d2247a004d008,-0x4d6f196f71366951443ce0d9d3356418b246f23bbff478328238a06fb38,0xebc1b7d35d91aa9ef99049a70465b5b4186fef8f187e9b5f1aa399e800,-0x2689481e5465ceb6a163832c631641e57b15bf97d977d1b3ab7a28ae00,0x55bf8bc598b01922dabcffa312a7a755da0e421a42139910ad8e4e6d8,-0xa07ebad6745630375f76913479d9c2576930c5eebe6c40d10391d368,0xf944105efd183b3ebc591156330e20488a413b79a050a5999b4f9a0,-0x13c039a4415cf81b44f1b246bf3fdfdee89f508a4271ddc935aebe0,0x140953dea8edd9196cbebde90b56edb6066378df04f3c233c015f8,-0xfdf1cb58ed4d6fba91bca97ce91e159f757b42cca005c1329bc8,0x985c9e8fcd0bbc256b5fa89289d8a7d1b560604e49c9b417a80,-0x429f77cc2409e4d04e7a224fb231233a57f52b14e9d3acac80,0x1433bf6a0430145222c789df2af9ef79319156cc9f53a3318,-0x3fa4e2c212fb7067b78c8f96d648026bdb708d1c8a3be28,0x76fe04ad595c7cc45e5f2c4ac98787ccc6fe99e39cea0,-0x740eb6b0379bb5b335771bb8a62e5072675a9b507e0,0x3069a45e040ca8148a5d08014a99265852591da38,-0x61c737c057096c31daca37368294e9003d8a88,0x1b724d09eb3ec04c4e40000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 25 80 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 80 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 56 indices rho q22 m22 22 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 56 indices rho q22 m22 22 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r23 : List ℤ := raw_ints% [-0x47835ec8a4d602629fa2bdbd30395010b6ebfdf5ef20000000,-0x6783adf76646afa1223451a81452b55137b935abc0f3000000,-0x4744aee3b8a6f2781eb365f28125a84e9d86836f8497d00000,-0x1f107dac3300db8d4c4cf3f6579246f115349b172a15380000,-0x9a0294f72f526df6536b594691df89bf4f50d26e95118c000,-0x241c3de10bcbbe6c2f574f5ed7b59db4771354d6b721a1000,-0x6a875480a8dafb71cd75db1705d552ca9377662050b65400,-0xfd8940ba980abf9232788d89cb4bf892d1cf4d51bac5f00,-0x1ef7f44ab7d61f51834e7ece49e09de220ceac82bc7f300,-0x325290bfa4329ce452984ee259f1d7ab46b813eadb5700,-0x449553b4462ba2c35011fd42949ad801d1d1092978740,-0x4ed9918c2e8a7e853d701a87b29b9c80f9ba39c77d20,-0x4cbb631b23ab99223defd832a80bc78fb24438622d0,-0x3f482d8e579d79c0ebc81c0f855ab78a6c2c0a5620,-0x2c315b6374290c3c897f6ecc7e3a19333daf835c8,-0x1a0e3f1afd1fccd03a77f86733b02d9228cea4f7,-0xce67702073c45ca823ebe73d5d5c537a6668b0,-0x551b89962c9aa03f225a3cd72164c88ca9114,-0x1ce06da2fea075fac944eabe6c1bb6c2fa10,-0x7ec9df0d95ffb1dffb48b0734846261b1a,-0x1b7149132bd9a0b79d2b1bc7f164bb6f0,-0x4829c5f47bf5638103d08213f45e854,-0x8770760d238e1b6c66f026b3bc0a8,-0xa1ab464a4d3483a6e56345c0d47,-0x5c43d3762df7fbeb9c7df1ed0]
def m23 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c080000000000000000000000000000000,0x8ef504def26b9674efd73bb2e30d212ccaaaa8305f434e1cdad4082800,-0x7ea88045df46c5e3fff04f67175022d85b35216c52ec84bf1d857b98e00,0x48702e6a920115bb5a74a9bb124c9737c2ef4b0ebba9aed79a3e689d1200,-0x1e0eae63ae172b1c01a694dbc825403702ec6789619cf5c5c83dd43278180,0x9a468926fe99fcbcb26614c985075361d29a3196a6fc1ee87768c34771a80,-0x27d0671768069d85bd8340374331f8abee75e49e0302272d8b74f81a626f00,0x87e16eb5ff91c831497d9e26914c2bb8c12e88262603134e77719653dbc100,-0x186d24a4c166a04e7195fd4e779c9e31fae052e756f46ffce7214e1d1929de0,0x3c12603629b3ca9f6d4249fb479da4dde838fb1d83ee247fcd03f0897a6ef20,-0x7fba49b568af9c5f3ab1d2d0071375b2d1078440c6716874e6565cd2fd873c0,0xecd58c99001063c4a7a5a79819045f12fe67a8a408e805953a94091ca466840,-0x1818e5f64cbac93bb9ccf92b97f95915554f0336b73b550384e99efc43f6f9a0,0x22a067135a6b410b68a169a0db3eed75428c7b57ebbd4390bcb1393db323e360,-0x2c1a42a640c32f1a5536d0bc8376a2cb39ea3030d0f28266bec91486edc05c80,0x31f318a4505ec9e92f92453531a372dfece8a0b98758051475276e163b4df380,-0x326d55a2516311efacbca9f7f4919e5abfa4f43150d1d9bfef9fbd607257b238,0x2d75197ef8b728491276a8e9bf774ebe80277cdf28ef6d72fb630ee006feaf08,-0x24a10cb08fe74d2e37bf5fd6dba96dddb11324f0051e6929d5cda19bdb48fe30,0x1a65890618ceab69dbc973b30de661d7065af5e293bc6aa836d7388284981cd0,-0x11030dde363cfca79a86be2fd6509827666d70c266eb5d7df072b4f86276cb48,0x9cc9d5d7826c41241b618db57011cf484749a1a01fc458a6800b3aafb9810f8,-0x50a20520fc4040024e53f91a3a1f1e7466f14d449bdb2d9f6ec20269e71d120,0x24f64ecce7b55931f0dd389d81f8acad38d89f46dba5d38664d7305cfcefae0,-0xf11be09d697bc7866f04e6daacfa644baba90dcba56eb6c05fefee245731b8,0x572e7e4ad974f5c38c86cd0f718d0a199c1b3c1a2a242ee7ad7e9682614a88,-0x1bdcaf5c4803fb65d7d6736d246e205cd98f064bb441b43a1b8e1c43ae1d90,0x7d65756be1eba979a3cf906171c9665c77416a9f8f3fb4e6213d4e72f7970,-0x1ee41f676d1e3d2023ff541fa7e9e68fe9808c4170af5268920b9821cb388,0x6a015722d244d01f063d0e92eccf442fdcfda83266fa7146bc12c42fdfb8,-0x13a7cfd908ec37d99e845069a81ec2271fb079133e871f47b450c63b6b40,0x31ff5cfa3b849cfb1d65dcea231db792195c5e9adfe926d23bfec0054c0,-0x6bfab6ade8e1359abcd1b4e465917e86e37b48be70b8c21495249b38e8,0xc3b45a98eeac35d80baf367efb0450b9e7fd9c0469dc6f1f3ee389ad8,-0x1258cf61808d2d47331187288b0b3f6df2164c1755a034e2b9fe11b50,0x1665ad9315ae1b3b73d67a6b5e4a622139b3a921e78d096ad9c28db0,-0x15cde6c01f3b61a275fe52d64b28d30ba029ce12210f52b24093298,0x1082d57099359acce2dceff0957e3b528ff01e1cbd5f88aee49e28,-0x96d95f7a09f2e8c3abfbaf757981b242752fbb2f6be5e2202e20,0x3e755b902060df5568f1235a4d364fe7449ba67516342d945e0,-0x11d4316c95b48625026fc2691826f2311899acbc550ca1dd48,0x3484f5518da544023f1c9a5fe02597c1852cf91c1239cc78,-0x5b1b559622e76386025829f7bce57b35fa62277a2a9130,0x51b73af1e2b2bbe324ec464ecabc8dffd7759c3b17d0,-0x1f06a4ffa19ebabeca6f0b3b82241b1af057413b78,0x3859f6210b3c29e313cf538283679f6a1bbfb48,-0xe0382183762841a90600000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 25 82 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 82 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 56 indices rho q23 m23 23 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 56 indices rho q23 m23 23 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r24 : List ℤ := raw_ints% [0xed7f44cd287b6f3b360bfa9484d701528143fe0afae80000000,0x1579d82df14aa896079253b578a4316e6dea1e0807cc5c000000,0xec750d7ae1c4da6e90c5ab4f513a04727a73df3896c35400000,0x6703119f52e12b477b768b0afd1c2c2e9e5a12154b27cd00000,0x1fe6a969766368ba491fa7aa823cd46197c9643b8fc97e70000,0x779a228d949d55bdf1f5dbe9f90feee2a8288a9ce486238000,0x1609a3c2fddc114a391908e707eb88fea79d15e32cc7c58000,0x346965358eab92526f2ce097dad243fe0c5249fdd6e12f800,0x665a02ba4e6385979dc65b4ae3ec2f6568f1f2002f483d00,0xa62dab12406ec43ab41a2be5288930196b9d9df248e9800,0xe246e54f72e55ce0cd8c838e2f539440e9cab76278b800,0x103e58d192f79c9211f5ffb20c6a75c963de7a15a27700,0xfca656d0f19418efebba7275d5a7c0011448b8f79a20,0xd0203effc129a20f3862e019588c8cfeb1884071300,0x9129f9f6c105156a3139008116992623fa7b4e7660,0x5578be4eab771c77ee0c3a7ddf503dd1076ef3f98,0x2a41447cbdc0dd5eb08cc2223dd2457a4b9deec9,0x116523d91058a97cf0782be5f3d798e5f7e2880,0x5e4425f7b3a248c9ee953321581852a9d64ec,0x19d1673c5e6a4a028da98395bafa4071bc70,0x5937be6bc7b944e66ec9657bbc8441a7a6,0xea0c83fb1c873206196d537a9aea0240,0x1b61be6c2cc0d1eff0b6d0bab167e2c,0x2096772e970cff759fa01e3eb5f38,0x128932b88493d4614842b6c20f9]
def m24 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea820981000000000000000000000000000000000,-0x11bed7b71e387a1c50b9fbc1d599f7046c8aaa5ddb8926757e7facfcd800,0xf9c099a1d434fd0860ee02e09f8524086606491d67f2b41767cc9f783200,-0x8dc7b79653dcd1c30366df49188f20b336ed9a41e0584d4925237538e1e00,0x3a6131bc1fc799c3843d18dfd4a30ee86b3872dfee9065f23c7615fbf40280,-0x129462a6a24321d5d1f095e511d15a957d2627a620bbe0ff6b9f85cb9e21180,0x4c16eeda6dca980bc33b30a964e63359bf6c69d1d129c819d83ce21d729ae00,-0x1017b75106223f93281ddacdb3842ba6d19f2caf9d4155901b3198d336617a00,0x2de10c5ffdde7aeb01bfd0d8855059d01e856abc9dc1dd17f12e0499ff4d8d20,-0x6fcd6531856d3dc9cd95f8d7bfc35e1caff52dad84312849fe4fca232657bde0,0xeb78a557c3bb736e36c7e17868512f2f8a6c4ded3f6666c5c66aebaf9e6e6e80,-0x1b052df5b692f32d604325f9efd722eb50026094e0efcb2387d4c7eba25fe7b80,0x2b89d934faf3f2033fece8201a4b7f26a896b85a5bf95c84f3e10fead8ba4d120,-0x3de5c870c5e9028e59ec40e134ba2fe18388fd393ae5941373ea4ef956f366fe0,0x4df6b70608ae8902062b231bc8ee1e22e12ec7dbcd9f96f8197d46ca39882f600,-0x5747d014f1b721c5306a4ed6b0c2b9fae8a3f3905d4900597fae736e165d53600,0x570d9073f27e5ecc0905065fab2a701ce47b4bb350975043298aa0887b95f1848,-0x4d7c4b749dcea8d64ea405563591577a4252880f95d0594d9d31845b4c1f29a78,0x3d9d464707454cf85fab0a9d5d7ecf87a7b09fc604f7fc6ee0f7f2af28c9606a0,-0x2bca0fce7efa42bb8278b56a7c2ed5f56f2e94ae1a8f12c6708b0c3e00c9e61e0,0x1bcffebbc5675227c3c3044e2edd3d01abd4c2e87cbc1e85de32096588eee1128,-0xfc6ea4d428089fe6516987f7a1816329c991691d60ac9fb16e9d1e43aedc1418,0x7fbe56c3f423e2856a493b80cf5112aef279009cbefc8642755f1d6018009c80,-0x39921137142e4f5cba94f8d5222e8c6e6acc27d0793041d7b7cd8234e3621e80,0x170dbf5aef3ef8c48f74b45ee683103dd0f56dcc3627700b30225081a6f19328,-0x82dd91e0dfd92557aca3a8c52ef7b4aca4fba70cea03c99d92275b226c50b98,0x28fd4c5866a0fa0ae2a4f69faeb3c1323654e0cf9c94ad8c643bc888873f620,-0xb49362737f9347aaa6fbb859ff272a156bf4c8ebf4419d8d433bd3efa27b60,0x2b7bc8af87beaffafc72a80c1f13b130f97a4328d6b17361f4345aa8976488,-0x91a3314b03d65526104d8ac48318f7da2abdbe5848ef2bf896783dc8a32b8,0x1a4fcd67d9c0a577c1f8ea8f6c260467f24ab2ba64160b6d6b65afac5e800,-0x4116ff7db9631941e4d7528203a75887298f1bcddf31016df499bf1ba600,0x886c6758bef4409e380794700c60ac7e7dae053f7c9428ffd56be666bd8,-0xef638c6f7f2fc7d9acdda7a955f9d2ccb8adb48b7e08881195f6761e68,0x15ab8d4331221c76c7697a07dc370c540888b47a22d51098cc84f95ce0,-0x197782a4326b76c3f9d6cfe4e40089e33cf556c805f3da47bc86f7ea0,0x17c92893aaae0965b3a7dba8336dbffd97d7aedcdc9c8a08abfe19f8,-0x11366c2a1eea3628bfce049670166eb956cca015f4ed1ef58139bc8,0x959cf7b6c0d4411c7755d55358881a5096aafc7989992f0deff80,-0x3aa26b4e7939ab96874510786389838afd2c021f121b2af2b380,0xfbff078c035833096461ec2827253d7714b7f59bd786932d98,-0x2b5d63e669e0a22fdddf04504aac6d9af1b904796f001d3a8,0x45c5f3a72adf70b3bcde82066fcdc3c33cb95315e8edde0,-0x3988b9eea3b0eeb32c2fb900aebc6c1960ecc1e50e2a0,0x13e11ca2b63aef7c7cce6c9499bfc5525482680cab8,-0x2077bce3ec9133c2ede507a0f3157d366ab46e08,0x727524bd419a806f11000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 25 84 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 84 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 56 indices rho q24 m24 24 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 56 indices rho q24 m24 24 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r25 : List ℤ := raw_ints% [-0x2fb6824a6162bbca809f0a6327eb655dd8783de26aee548000000,-0x45008d4d78f09997716c6a761d697c561fb706c9ac201e8c00000,-0x2f76255f9742df64bdff78f89dda7f2661f18c7d291af73740000,-0x14aa8bd85860ecb27e3d067054e5e4aafedba1e967d0168620000,-0x66583c25cdff03bc8b4db6aac425f17f42f4b15f136e429e3000,-0x17f7c835d7bece54453c866e909b8414d1506f1c69e55434b400,-0x469dea973be81ee8c47539a3c1f7ce1f6d7ec77b762a9ae5500,-0xa7d5ca75fb43b643cc09d2fc23b2272d9812d2f0ee7a5311c0,-0x147854d5e02c1af159bb5ad5c93dd7a854b873d38f66d23ac0,-0x2135ab1264ec257dca03753f0ba0c40f71bbcb2a5bbf93cf0,-0x2d2eb11843cbaa03d61430d0ce6a546eb5bcf6cae5bbc930,-0x33d956747218bb55c350d8c539ee4e4547957fb40ad1754,-0x325ab8fa42123c8d0a86ba3fec4f64574a6b7634ec9fa4,-0x296fe28111ad15f074b9952a2c87d86b66a306322e689,-0x1cde629826f1da604d62ed4e9b943a31c615de9864a8,-0x10fa0945920f9970fad60a7d87f296054bf29f04a1e,-0x861ad397049cf31925ebf0c7bd04bf0f5a63aadb4,-0x372037cc47a99dda86d2b79bbe0786be0c307f3e,-0x12a4138e5cb8b1d7d0d1bd498e4889aa6824160,-0x518b1a44aa9f1785e7fc6ce8d69e72ee16edc,-0x1193d44b51b2b3675425608b5931c01abc0c,-0x2e036140085fa2599e2afc2d1fee79eee1,-0x55ed458a17f1b706e55875e0d77ca088,-0x65fe8d867803dd7f157de051bdb85a,-0x39d7fe1cbe3bb5861822eb45071c]
def m25 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d50413020000000000000000000000000000000000,0x23401a330848525f2bc62ed5e6110e98924caa15d959ba83a5175f29e2800,-0x1eca540a7cfe61ccbf1fcd23f23137eca09a0f354970e145af27d34f8e0e00,0x115a4847e6d9b1be9fd43f3e5a4c5737b12e97afc6e8bf1090513fdb5b8d200,-0x71779079a2542b53951aff146e70bf02fccc87b2e0b1114c61da5aab974d180,0x23d4eed4e835101fbbbf122a6924953f37da0de97a98d3dea915cd12978cca80,-0x9190c7e6f980504cefa111aec9d1f18de5279d7b0e86d0735817b28f9bd38b00,0x1e87d4c65261cd7f29b32f40a56d4ceeab6c6e18d7cf278d3ea40d566f65bc500,-0x564a50b2686cf91a1ed76fb2b3e23e5d2972f399c771441497d8f849b5cf57de0,0xd065eaed950000e2a81fbc5cad91331dbd19d0ef9ff019f8cf1bcb6e42aec4f20,-0x1b2d5c5ff73e3cc9caadb9c2076e3c1420a05a13ddb3f74e160a9918366d3e8ac0,0x316a3481a426345d20cb9f69ba7cda194b05a59f158ee472e03e0a301a2a4a7940,-0x4ed29dc71dff1f95de94fc6209eb009d940034d068e053f693129314508b34e3a0,0x6ee2e94aca484d240a33c71f05d419b378f2659bfd4464cd6608d26dbc96baf960,-0x8a247a2399f683b8682990d6031d48ae7c440aa903861c740b88667a2d9e0dbe80,0x98e342a679081c78a4ee3407d8024bb28ee2e79996d21dd8cd4c1bb9113835f180,-0x96ac4391d6fcfcfa50113b9e0026cec39b4c0ffb6795e348788c4380fb6b4d5838,0x8471469d0fc4cb21929ea9e364d3321671dac11092e11e8f5cf4032f1e431de908,-0x67f0c49d1a0d78065814b1a0a1c3145a9b2a4bca299014a4c70e165429584c96f0,0x48dc1c53933f3df4ed7adcd4fee042e110a45ca70b4c0e54c3f3eb1d3e38bd0610,-0x2d9c92c8c70fc9a795aba5dee3e08588d5db662b97483f596deee2a92c5417c7c8,0x197ba47e0b16d462ba91a73d2a40ac703b191b3bf10f92d878d0abee8019965478,-0xcb0c7bf44b9be62e7fc946b7b1bae5850e6494ef3116ea292b4bc558637b489a0,0x59f92b34a80089f0a1938d837df21f121514206a49aa358a023fc17ea2a31ea60,-0x2363f666ca34cddd372da769450a30d36fe5699f33312fa237dcaec97422f8cb8,0xc520746c3725d3512299180f4e1f301d0b59b9229e22c7424b468edf7a6cdb88,-0x3c83ea8ea99d10cb7baeaa664ba9e9b42622e5bcff6b0b08a229f8c7ba1cb5d0,0x104f5ac306a71550eb2fb027fe6c7350bf2da9c4c7ba00d95d9fad18289b4b30,-0x3d6d04df099e7eeb7069d46fcb92189b07dce46ae81692713525e7bb6d96108,0xc8c9d7a5c3bed9c6cd4a11f0527cb9f2e63a09bce502b994471dfac2ecf638,-0x2357e0f1c1aeba22bfae919ddea17143cdafda23e0c5715a8506228e4fd840,0x55058fcb1532f245182dbfe63351ccf7c9cee69bb6134372d9e323cb9e7c0,-0xacea67b38ceff0bc01b784c50fe2bd552c24b2fd8456e0668291babde8e8,0x125b847adeff23e250112e0577ad06dd8e68d3c7342d1ea7a03cc96cc2d8,-0x19ab1bb53623f5616af0cb01023f60724cd1345aff93974d808c2a8dc90,0x1d086e48ed2d2e7d67a28846d26d833e7595a2fde5f70bf92721cd2270,-0x1a020317c7760dbbea90c88ab05346345835057853cac80ca5aac7218,0x11fae43aed61b582d89bd9ed266e5648c220157c98decb4be49fe6a8,-0x94a2420a349f199fa5d325a094b45ed72bc1b4df54d999ade772a0,0x371d8857e5858aba99b0f17ae29115cddb62481baed9c7c92d960,-0xdecf815829c9fb1e261db28c239d6792c3452a894fd40250c48,0x23d337658cb4b10fd50687dd732d810fd22f2e68f92b9e7978,-0x3572396dd24fb77bfe1763629c1066a700757cb818b71ff0,0x28819f6758f14f072e3b37f2361126ee1f96ae3063df10,-0xcbc135c0cf12f96ebc4fbaba3a83d799dd5c80057f8,0x12b3adaa67a9708e9d1197ea9b1687b236ad792c8,-0x3a6a380d20471000718000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 25 86 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 86 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 56 indices rho q25 m25 25 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 56 indices rho q25 m25 25 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r26 : List ℤ := raw_ints% [0x94e4eca7161a0a8c3fc13d762fb78dc7880a97a7cb7942e0000000,0xd73e354461c46d842782f4a50c87b126a03ec7fefb484b55000000,0x93fc550be5b811ccdb2541dd189cb718df7422b678b071b5700000,0x406854d33f39a7fd7ab3213ccdec3a0d99592c36a521363c040000,0x13ece006b00dd622c48c65411ee34992eb04456eb4d8e592754000,0x4a9eca5eb22f7dc3daed744c83b50a5b6f185eae5a472bc8f0000,0xdbba628047e8e0e4be9b901d995503bd676dd22b710fe222f800,0x209e7bc64c19840c190feeb831e9720e8ecc53fe615024fca400,0x3f9cacb1d28daedff51ced20a3f4f5157bd3b0e164422a86340,0x67209f0e6f7918b8010a23b7d9e255988ccd8ca00e3bdbad80,0x8c32f3d7391d961eaf24c237b0816c7c18fb775975a8ece50,0xa0c074c9d477aff9d13ddcbe12eed1201350e4c3161b7580,0x9bfa72380fff1eb0c52e404b0884fa9aa6c43ec519cfa1c,0x803b5661415afaaf4f8c08cf8c6e104fc191ad37dbf8b8,0x593e7c19e1c5ea9f6bbed7136de29a72b981f9d6732d7,0x346c03703fbf1d9289e2972aac4b9b4f8ec9cf9ed360,0x19d96c10f5051d0d599277c81137228b391e77364b2,0xa9c8cb80a82b48eaf56d141c2ead29d13aba30f30,0x39543d6f9c173610397a9504e35046e387577942,0xfa619ce2d72a782dd61a4c54a27df92812c780,0x35e0aaa5c7af082692aa3a2e440b42d67a334,0x8cc41920dfb5348e8748ed99f6ab657ded8,0x1065048d54638931fb3da92f41d648ddff,0x136a1a95d46719ff7ce031c07003d760,0xafb4ec9ab88c10ad1a65331142a56]
def m26 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa08260400000000000000000000000000000000000,-0x4608e3435b81eb29038ba8db1e2e8c479b74898a551dd95f0fdd486126d800,0x3cc168a3b3bab3495aae40a933d6aae7bc212ca15ac45fb5db567fea233b200,-0x21ff8b263fb46b4d717f155ab9fb0da845f31290e47f95adef300cbd2b3dde00,0xdcaf01ef8d7481541831e333123ecc280b4332699ccd833d68976092ad7c5280,-0x452958a27b9e70b8922f878b4f07e6594991542825c4e73167346124ca2564180,0x116c26afedb8486ee60cb53b3a65d6f81d71936f0c39040d5ad87f7970d8e3ba00,-0x39fd6e403ef3c8735f018c6eb0d04ac7b673745cd87495af03ac992bacb2cc8e00,0xa2838dda01806935fc3b685503dc76a00366c62533ae245993ffe279ba17686520,-0x1850913053246fdfaacf1da495e6d3fdb3c8133717208dd291001470370873fe5e0,0x32454432dfe7e0234dd76a78fcc58b15b84600c7714281ebfb6187cd383fae02180,-0x5a890a5163a486a5decd40bdce1f82746e8cf5d08fc8d4ef9b8eb61b1dc7cb69080,0x8efc169ca7ea523c72525adc5b960ae2a648c2367a4a3cc48737faa7fe863f52d20,-0xc7125335e075ca5f3170864c930dee229c7bc437a169b81ba2b90939f943fdb83e0,0xf554ea3eb6596a6cf5f2efef763740d4e17f4eef444ff2882694f0e16ab6188ca00,-0x10c7648330d6874c241386249aba482c5fee582d107dee4d589072b9e6d6da539200,0x1057558159caeb9767e135ec95679b7993f5b80feb581723baa244e0c40c253a7848,-0xe2fdaa8715a8cf5c4c37e90c80c2ae6bbb45d68d1638a7583def6919f2e684e8a78,0xafd709a8e93dc5f570df997d92555291e94325927ec2ba732d0904cbf66e8ee3e60,-0x79967de38ee58cd8d00c5ee713e18f243bdfbb57438d017d874a632cd6f99247420,0x4b07fc85bd3b2c144fd102beacc84a18834356d8d6198a96eccd92744b51d6eb028,-0x294a608c3a0a8f09a0835013130d2231143bdd5fe6a70b012184f91d4893b9c2118,0x143cca8b0bf36874b7441c32c88d92c218ea5ec530aea364ab73a4f1a7560eb2f80,-0x8d15452d4f61140fda0e7599c5eee392b0ba6be9af717d58c26921ccf111b89780,0x36839436e5db8bd06e885b388650fa7882e8bfb76bb7121cfca70d8c7b606d9fa8,-0x129f686cca9f2586ae3d4c3445bb750700ebdd5e637124f1671130ff852c30cf18,0x59a74c961a16ea985e001a347d25ed94300dbf292478e5c7007e5dc03ba74c4e0,-0x17a715eacb5c8229d58a5a25f7ca1404b33fc1464df407dc4534c1ebf5d677aa0,0x5712be45104406eb87ba295be7633c38b79dd1fd7613d9404573065efe933908,-0x115c698998a8dd5eea3613e3b586e23415448800a057b5ee4d22109d43236a38,0x2fa288a382df90817ec716e6ebd729381cab00b0983b148ce7cf8d174aaa800,-0x6f6ba8dc3d296b8c2e83af59f74c88df026fe0c9fde8a796db7d943ab81e00,0xdbdb85a2e63b0d544b9d164346c75060f7ba965a2b2070a3f57e8a75af8d8,-0x16973fd9f0a719bcd16e5505d1e05c626c75e0e851624e669d42f82d56168,0x1e7d0f7c94e0766fad1fcb2b2f616fb1e13e77964ac5b0c4a56175d85a20,-0x212e91a9bbc06a8dff077743db3185ee5cdfd3d25b67ebdf1314cb3a760,0x1c8051fff3737a12b91a0e1160aa4cdb2e9aba05e8e17038bd407ac9f8,-0x12d15c7d745d4d2f6753bb2751330299d429e74f99138b8f566a3afc8,0x93e4a9f2a9a025eace1044129d5416e3d6f4fec8ba2f30e878d0c80,-0x33deb38b96c21b94dc3be88b98bd09189808c1f035012eafa65280,0xc52b5df69fd0a1221d3e6d72be0019b987113ae6e38dd72c2418,-0x1d9c468ba6aa1ebc7241ff9eaeba014ccb4f9f5fc70b8d7ed28,0x28f2593d78cbfc3aea59582bb634e4eef950d0f2b5e106720,-0x1c842455ad4bf8c704fa9fbf5699f19a2225134bfa5d360,0x827f3eb552cba950cdbb02d56f9ad0ffd0e70a8b3338,-0xac50ef3f2f37d63516cb538697bc071678bc69988,0x1dce7cb62dfbbfe27e40000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 25 88 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 88 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 56 indices rho q26 m26 26 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 56 indices rho q26 m26 26 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0xafb4ec9ab88c10ad1a65331142a56,-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r27 : List ℤ := raw_ints% [-0x1c448658145ad853ebca96cf248546e633f1fca33d3bff43b0000000,-0x28d93b5aa98dbf1f374dc16404c18fffda7eb85b360c7071f4800000,-0x1c12b9c81303e0b344d110345e690678ce5ce51bc150f17d61b80000,-0xc3681539da988c7d7c07651488863d6c4e9c47ce21513f81d5c0000,-0x3c6c5e587f29379e6161c70d97d1e9bdc8dbc92bef3179cef292000,-0xe22c1bb44c202ad21cd1fbc08d89b41ee234297fc66477e82af800,-0x299a220e8e2d9f3f36b60a81adbb44ad80cad98562cadc188e7e00,-0x62c1fa6bdbe46e5e4c181f24c626e60a1cfd51e90db2a787f5280,-0xc0791ca3e795d57a58826943a154e8e2b1600865ee5a79e9ec80,-0x137d43cd920bcc3df7964e0cb6901708bbcc17961283356af060,-0x1a79ee6901a2580a8a8786b1ed3a09578ccc88f36242802b1a0,-0x1e5595261f3724c117310902323a1b1518d453580bdfb0d7a8,-0x1d68bf41b93d8482f81fa9c7a0e50fbc1a58fdeb770a40458,-0x1827f3eaed2d6060a77235856a55080ea5b449b60d70c65a,-0x10cba07ba355aa50c42962b99b7005d21a470d9fe6ee938,-0x9daf6a3b69df1a6bfcd5391f11d952c9e641b9f9d3f1d,-0x4daab5df339ded0111356d9062454621acae5dd74268,-0x1fd8218c99249f78a59112d38fe041aa5150a774af8,-0xabcf58ea3f98aa7064d18c434a8951a99f29f5c10,-0x2ed4730995163863f9000caea139cb421cc2a16e,-0xa0f99754c98f6d86e76422b17986a0da77a968,-0x1a3d8b2d861f6c08fa4bc11e29fda84fa3f76,-0x30cdfc7eb9796717cc2dd870fb37b7095d8,-0x39ac1e06465950c6eab5355a139089c25,-0x208bb4c0e9fff09a498a8bb6b5ed898]
def m27 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c08000000000000000000000000000000000000,0x8b2a995378374ec0b455f361eb552fcabd31ca7c04e9d5282ebcbc3c3b42800,-0x77ec1fdd2e2278fe6d74e9375131df69ddcecee795409a862deb1a05a4428e00,0x42a4e0ed9326219d5fe34d8f9333dbf580f9d3020f62ea4cebd844f5efa769200,-0x1ad7e983c105abbaaa962a839d8a29488eb74f2080bd192cea7456dcb163e7a180,0x859aa13030f45e9360b71a61adc7839a72284cad920784d6fb2c5defef74f0fa80,-0x2165b36259af0bff1cd8172e30b0691b0de4fcb187264a1529a6426aa669dc28700,0x6e4611a8cf36c01abac875ccae97be51f8d3eaecb84149a80007b8b1a9c7226e900,-0x13278e6c1ea851ecde70c0bdc93ecbb9d2d0db88e922610065d2183936224014dde0,0x2d7527c681016a24adf464eb0974904de07552c6f883c0913c2631c56a92909b2f20,-0x5d23c1b520adbafaffae4d2ce71f34df7a31ec30f92eca9f86303643ad912d2f59c0,0xa62c1747812bc8860cb383e915048fce7ce794a1f618cd1d8ba1ddc9898211551240,-0x103e1a139f56fc948bc9c6ed3ad5814d938aa2afdb30fb136e65a421844fdca38cda0,0x16623ffb844dd7c536aafad617ff73c18f7a3ca5613617c963575106434cbc1c08f60,-0x1b4ac9d0c9b9241f314c96cc8965d4be197e7a960f7392d3eadca7e1a2d844e325080,0x1d888b865db2a9342647d5bc1bade30bcf632e9d851b14fe86ab0ac550b329dadbf80,-0x1c6da24fecc71df1dd7709e7d59b807a08e858cfa37e259a23a96edd7f0a076025e38,0x1861311c664eabc0e092e5ccecf4a8635b44c14d4dd78a094098d48aa4181a80c4308,-0x12a4e9565ef0543882abdf5a3b235dc6f3d259e6b55772fba6f4f9ad44cf6a3e5f5b0,0xcb7f16cda2e76fbe2d481ae4a344569fe6401658eb25dc47b2a9b704815d07d83950,-0x7bccc9079f243254ead4e7245428dbb625f1e8a0fb3b1aa869981b1122ea71c70448,0x431ceab680452e491fe05ab8cf9280d1534d33b5189b19f9ec5b0cccda93f590f7f8,-0x20604e91e4800808a90257e65a13bc3ca8f3d642592dd8383224c8a4ca79af8e6e20,0xddf43ba5b6d18ef68424b9bc55bda396515807e3df0c98e42eb90c992d939adede0,-0x5440a3a7d08f6c7192e63b0e01140edfaac74010d657fb6e55a8d70fdcc27bbffb8,0x1c3e8f42498a4e962b9740462f8e679593e58498a1ac78a699b8e61dc07fec57488,-0x8546cd158670c0bb505cf92127d2a490ba95f84df7966a859ecd8ca5867f05a810,0x226b2e2a547be8f11fbab1a219af8bc352a138759b5cd04daa8bbfd97e9dfd12f0,-0x7bd9b2cdaa3aaf7f86f978c2308be2c477789ed9ef45a157a58a7a9bf8a196688,0x18193a628219d0b881d58ea66f84b9ac371bffb980543c6cdc66bc298e4ff34b8,-0x4069bc71d8b844bbb2379b0e2808a90af27875aa605b5d1fd3930bcd119f5d40,0x927b96fc2e5eae21ff186753669aaa8c0acb91080eeeabd662f44cc9faa62c0,-0x11865fe31cdec65afba0a5ac1a2ab8e6b1f76d124c871c1b39a2ed21cba28e8,0x1be17597ed56946da0a2be9fef04d5867fd2f35ff9ae704b80af0de2641ad8,-0x244f9535b3bfb5648f82c68bd6115cad2ced9dd862bd4f942ab5aca4257d0,0x26041fdd2a5cec7580235ca549e3a27eff0bf085128b35ee78ca4c72ad30,-0x1f4d04828603469b8606638cb03aa1854bf5446888096c6b27ee133e198,0x13bb10e1917cea044dd7471f13409b2c59aa2c494c162b6b75b9989f28,-0x9360195fc34ec64fd6113c921e50cda33f7240c7fec65bae76552320,0x30dee5c6335c80a78363cdc538137f3b838a4aebd77de8f87dbc0e0,-0xae9cf8e400c961ba0c7ca27550b6a7c21846c0c24f89dc270b348,0x187c035cdb4f0ca817b30430ad715c8edac7866d0ccb51324e78,-0x1f5ff096fcbbe47c421626c9d13ff6281a8cfbf70ae0995cb0,0x1412d1ebced42eb3bf74c51e4c9202e34207df5b7832a850,-0x538f6ec58a719f284aa7a0ee0cb8cb13df510851c2c78,0x6334a97eecb4de00eb8a0aba60df50a3432f1f3248,-0xf34b59f14f7a3e14a600000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 25 90 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 90 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 56 indices rho q27 m27 27 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 56 indices rho q27 m27 27 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x208bb4c0e9fff09a498a8bb6b5ed898,0xafb4ec9ab88c10ad1a65331142a56,-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r28 : List ℤ := raw_ints% [0x53c67591ebd7224acea454627461cc7d834ce9116175bf768c0000000,0x790476c78f1920963ff8d89817fdafdbfe59c8ce8fbf190dc92000000,0x532332d8f4509dc79d9d67c4a52cc223a81957f9aafabea7797600000,0x24273e744bfe7c164de03077c76d7d91676e6db22be43663f63f80000,0xb2ca4634ba292f6d79e271d723770cc5459aec01ef5c8fc36b948000,0x29cebe8a79a30bf13181cc0efb2eea2141ad69cf7c6dfe386f58c000,0x7afac613dc9b303166b0bd39c1bc503808b8b595eabf7beedad4000,0x123c7afcd1f3f20d8a8943d1397c7fc6ff54957a7c345ed2cf2dc00,0x23855a746ff4df69e8b4e99650bcb7f7c6320f6f8b0a03f3945f80,0x398330677d41c93c2affca3e54aec27765815f285c95af7c04e00,0x4e1435d55936b0bc5be12c0f19348f2b49034a2110d13b428820,0x5964754e0ff6e734b254634e9fa506051a940cd0b1570eb6f40,0x56997ca769cea767d1e61c91b245e60dec06e2669cbcb73cb8,0x47127c466fc72b79fab3fab489720420ccc24d2af0cbf48c0,0x315f1f98036caa315769d59c5b200e30cf8e9845ca611366,0x1cf15414232080c4500134b01ef6be2041bb5fd6eea0c18,0xe3d9e47424a58d4a04fac633c8a140c520491baca5703,0x5d50f032ecd5b3e5def38026e94098a09aa5c0c00d00,0x1f6dac67e12714f1741b6ce9474057a35b786efba08,0x88e135fbdd73d9e18009ecccaa1afc8637e1988b0,0x1d5d58634cd82d5d81ed30c9371cc6a1038edd32,0x4c774d6bce2b2b4543d7af4e27a4e6d48b1200,0x8df908bd63d28aa4b3f1668fbea63f02cd4a,0xa773000912bd8ddce3bdd1b147d0d5ca38,0x5e4bf0282ae91266ced6386c7c366cbb]
def m28 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea82098100000000000000000000000000000000000000,-0x114954b13a6c256d7d855400079ab0c98ce90785049850cfdda8dacb4b2d0d800,0xecc927cee2f4c77aa9fce619da08cce5c433f0b0bd48e96ce8401684ee40f3200,-0x82b366dd1a4d376e141938014d252df03009f7b4c39589ef5621e9afb7d9879e00,0x3446cee9d4491186e087a2b86d01e89909e24a8fa003603e0c3b1f1b0082eb42280,-0x1024d3f0734d21768fa3717f5b7894b63b7986950ff0d1015e084e0762794b72f180,0x4014f7f08d6a3de8dd57047b9cece377351fe9d6fe25114e47785faa1584d90f2600,-0xd1ef4df8286086a7b89b96778c0dc54ccdbd3995438100ecc5501884b6d291174200,0x242b3b13d56924add2fbcbf0ddc359892f1c704c4f645e027d397759cea03fc457d20,-0x551bf790b5b59b8271ea6cf39ff8fc5c7c51dc0caf6529b3b904f469abe708f29cde0,0xacd843ad38279691c58cb116db8d87c3be95939d99c59a5e5afd4cffa7d9a23d86c80,-0x1318a1213ba6c48b32c011c3b314a9bf1b5b57babef5ea0df0174ca1ae9fe3e4d64d80,0x1d941544a24a6e9e92ef3730122f75281ba2537cab53fea2e7428f62ee3baab07bf920,-0x285a6a53c1d2f7330351a8be7632a087bd91763820366db6c94b2dbd337bc1b13727e0,0x30afa4d4ea284f8f865670face6033956573599245d5e43b30917eb8fa73312dc53e00,-0x341b29e4ef72c93f446e2a4a54c6e42812751cfba1d5ab24c659d5e5128fe7719fce00,0x31945ecc498f0070567eed734454fecedce08d8aa25559b83531441cea2d00f9f9c848,-0x2a017814d9d1c5c2f677788b6764b72c973350247436d7fb1ca1207e8e0217e8368a78,0x1fb76c7fbf5e4c34c1355a9c18942c935ad48f3fc8dc6d1f8fa1a195295f06171d3420,-0x1559007e45cb1bf990d6bfdf5847516f577c079b5e2747745a45b3583e22ea4a1e1860,0xcce07991e12fb71ad2f0ff7eddda9526a12c8a28b83abb8ebb7db365fce1205ad7b28,-0x6d6ba627c51fc78d25d807defe1b4a363c6fe0d5109e66f35cd8f14899e3e73484218,0x33f5c6e5ec464624c671c538c802d1157233644c830cc81f5af4bcef23f2c43165a80,-0x15e50524ac794bcb44f79c9b7beaf91e4c31371aa662eff0086ed03730f69d0609880,0x82a4d96f69b46da0528f65d75fff5ec5cf1667195750fde0974160a751a5c01af828,-0x2afb0235c3cc1bba23d8487e7e782237aa5ea54a8d021f26ea0b534a9055a21e4698,0xc6caef2f0a365cd405b1fbd37ae8b1827dd59a576654af331942cca0ab66e2369a0,-0x3240fba7dee21b96e6d9afc393113319194f3febdc38432c8c650fc679b6b7753e0,0xb0c0521e01bad439bc8f01d2bb996013e322f5f39c43bf7330682136805d284d88,-0x218fb54a25a39b92eb8e08cdd093585f9ced8bdc53fdbcc3228bff74c5dde8a1b8,0x5761ca68c34bed4e40df613262413a6ab556c2546633be3f620ef89134474e800,-0xc12e03e50bd4c468988d0ae2512cfc3e805408fdc7bde1e7f139c224c3915600,0x166ad3a538ae9239b83cb54e7d8addb16486ffea99bb6ccb58c82cc776870dd8,-0x2281807c4ea9b9a279a7631add4085981b3207c15ae680df828a8298b211c68,0x2b5b7bae43ca2c284547900901b8f6b085ff647a6aad7ad9eb20d5a4958160,-0x2ba8248eaf18e9fedce202fd3d519de460b982695d53bfbf664631be35620,0x227243b03efc26291ea75de368abd0132b5ad3fd01d3843521959f6e65f8,-0x14b95c34b84be333c6802cdc03e5cc6226274f2a8ec7557bbe5e03d97c8,0x9310e8f3f89fbe7ffd96ca2a22a5c0647d36671c507d3773e26780180,-0x2e17ee4881e4328af7bc40f9450deaedb66ddf1d6aeb5febba792980,0x9abf2c52c4b0d5a4fbc87e7ba5eb43dc447352dd16b2fd3b85d698,-0x1440e9ca4f1d7759c8fc113aa6c115e26f6cb4ec61ac56d224aa8,0x180b048386e2310cf1c7625d7e90f11cd5e5165ef1906bd9a60,-0xe2109fdf498c44ee7b4e9c7a14600590a829d65441b42a20,0x357e725a5664fcf875bbd47ea9a75b5f4cb34968d193b8,-0x3919b19886006300b4f70af2551485c3aa78aa78d08,0x7c179e7a0ff87e81f1000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 25 92 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 92 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 56 indices rho q28 m28 28 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 56 indices rho q28 m28 28 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [0x5e4bf0282ae91266ced6386c7c366cbb,-0x208bb4c0e9fff09a498a8bb6b5ed898,0xafb4ec9ab88c10ad1a65331142a56,-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r29 : List ℤ := raw_ints% [-0xf2ba13e565371ddb0f01c3a4d6a2dab5a654aba3a6fdd6ec3658000000,-0x15e83870b426270a4b0c3b59733201177dbe5bffdd4efb6509e36400000,-0xf0b66bc07e484f4444e4c22fd6f0e07a05f5bd43c44a01b5f2609c0000,-0x68a2f7457efa8376d3442bee852daff6a509ad8b2cb87212413c260000,-0x205403f7c0b0931cf67d15ac095a903c73c43c5b1c780a0180d2019000,-0x78e6219cd80da92c4e7e534a2bae7b864b138b5d1b288b0524316dc00,-0x16376f7d29bb9fff5bde24568dc31a907f3f9a4233287e81fbf7b4f00,-0x34af2a64034916b7e58feefcaec4c5165534e9272b5bca32751b0140,-0x6690683cdc2c526c78f915347932dc23472ecab8ec1eebe10499840,-0xa5f79e273d5f8b2c8bdccc3b53b329edae6caf0a19bcac4ff46950,-0xe12d81c98de75e016f5c4d1070ea555c4a6097aee2d8cdc967490,-0x101a25c8cccb4ac63a9a0ee56014c9bfcd43e960eb2b9b396e01c,-0xf9682a5454df8c9d2a40fded22eb8b11c1f5a6147a08984d7ec,-0xcc87ef818960f843750c51ed87231c3732c54881105d577613,-0x8df6b6263afe10a961427462e529311421e071e00285ee2b8,-0x5325ea7f0430fcc7ef8269f32d55ac1a5ee1d9a5dd241d74,-0x28df43658bfe3c85f307a0b65bd413758e7315bad08338c,-0x10b8c426278552f8db9eeca457f753e996c8d0741f9942,-0x5a01e7e3176e7531609617639377823678c3ffe6c6a0,-0x18787b017a835427433d6b96b0b8639ad39a6bccfd0,-0x53e210e4ab865f0f41ed524e6501897172e9d1784,-0xda1e182c265db9bd64905e81cc58a6132ed3493,-0x19455d92b799ea578635b0aabda5e91e6d94d8,-0x1dc1167062c2c60452402d55a25706648828,-0x10b951056111aa13e83c94829ac9769304]
def m29 : List ℤ := raw_ints% [0x0,-0x138bfa65133e660159d5041302000000000000000000000000000000000000000,0x225c6c579eec6e4c729029ce66f2768681037e91b8e71c92bd7727e9e1a74a2800,-0x1d3ae34efeba72ff9a6a9ddc2dfe3638d643cb9fc85714893c2a441524d9dd70e00,0x1007330d1d06b1fbbe1e7f12ab107dfef5502ced15e7bdf98ae0a65509856d665200,-0x65df2fe2a3ccc745a7c20656ce01e07580e6bb8e75cb8f7ef2341b033d611bcbf180,0x1f3c8872c9f1b1622e4761127687b2cb9ede2ed41ba4ef905b109161158502957aa80,-0x7b13a391e0d8f1227ac7bbad0fdc483f55084d5bc7c99a1ce76a7cefe40151f3e6300,0x1901cc189e821c26d310ee64c908a91695430ea35d2e96f81ea7d2335a0a8536162d00,-0x446239d86087e4dc53c51f52891c019765b8007815c2f27251b0888b64c18cb2e6bde0,0x9f9391d060302d26c0340f03b574798ab88ce3c21721bfa70376524b1460a4e7fd8f20,-0x14144a27298cc8292178605de532632bc5a1d3ba987779ee751ab130072e7e2432ca0c0,0x232c597e5123afd4ee18bf61770a39a4f240e65b6d9a622734287c89506e3cdafce7340,-0x35f738f229dfb4cf58fac5cdb753e0fa33fe71f1a31b879a0f1600ac1449f85bb0f37a0,0x48e597bb663ef84dc18fed47d5f7bd4711c9e40a3727a941626b7a64d045d9e49982560,-0x570a67ef8f5c1723b7a54e03a53797f46a1bb369c0540b71f1aa880efad4064b6b31280,0x5c2549024a6f8ab9d8576a9a7092079654b90e87823c9369d20a91dbea0c24666b45d80,-0x56ae62f1577963404e483e8b4bcab91b4ada62d8e21f04ab053861a90cf1f5cee324438,0x489026085228e2972d79fb12a8ab0958e79521489a6418f737c62a81068b2b8860e3d08,-0x3619e5e1464e373f3bce92c3d722e55f81355130220b4a3f05dfd29d8320323eef34a70,0x23eed96c1d435b891c57c7ba3f58892f4a131655776146e7d7fbfe67f76d7acb1040690,-0x1540c808779c094b1cb78720883334468233e75f0f81b712a83571f9754387ab81520c8,0xb2f0c9a41f8c82ae9750a031551e255529aded39079cb727c5fc36c8eeef17c9635b78,-0x53a681b3fe31c6a34813ae778ac3149bf343f6e28d912ec98f091fb5facaf8cc0e3ea0,0x22aac453795bb6196cb4d45bc85150fd3c0c2438f81b3418f4ec10fb5b17a1dd4d4560,-0xcb3d0e314130ada22ddb16262e542b04bb55794b2db9a625b2c79eb24b0b9c20ceab8,0x419ece910a8a1758770a5d79235dd87e7b47d0b25c780d295d88daab4dd45397ab588,-0x1297f678192968dca235d0b963f881f40b6c23637ae7c14aab1d7c8a2fc50869de450,0x499e0fc0418fd395573ec7b81fcdf3620e8c5828f97ff14f266f561bd819791360b0,-0xfd13d46a5797ec717a23a05e223eca3c23e8ed58cdb3b49e8eb85eabf0d8f400408,0x2ee42c79cdd209fa440a3c2b2fd705160e8550162703d0ea9ace340e8cebc0f5b38,-0x76ea7a9ef57e97e2e74b540ec5e304986d4b40b25543b600f50a54462aebd3fa40,0xff8a3b597e973cc71051fc618718d0a316b77ee8f1bdedb501e917e921319c5c0,-0x1cc240d69d0fbe2e223f0c53b1c464834d987b43e7bf0c02c4444a89a667638e8,0x2ad2612e4bdd70e9ad22485a74ae8de2cf94cbc32bc54e1ec1aeb71998f862d8,-0x33e6bdf78c4aae4556efbdf9a8f6934a4557d6c89f281575d4e020317f39d10,0x323f7188980b7c0e9cd2cc203a349fd88c08e4beb20c96645b211d88bc9df0,-0x25fb9e43c32347f523757566ef9acdca98ebbc491e931802ed92bbd48a118,0x15cdba1fabdda5054fb28c0385ab0bdd15d61bb3a1fe8f84458a0409a7a8,-0x92f3d26dac3e8d7a3bf3fc5f5e2e56cb438585531a0c70725b01b47fa0,0x2b84561bb160352a3089245b1d9bb8059a6118765bd10918dc021bc60,-0x893ace96497d966630b4b51e092ccaebceb059e736d70c335bab248,0x10c26e965503b2bb692a83a17b0158f6f80f1bd08f1179929f6b78,-0x126d14be7f7c8418199eebca048c173c68b3146b7b7dcc5e5770,0x9f1a153638a4e11ab2dc1839ce4adea9f266662f8ce34e390,-0x223d0ab6da7ef149ef7d618c606d360a6cd9f3caac138f8,0x20db84e8b00af1b9538e6083ea000f3226c2ed9a59c8,-0x3f47e3ae78508ef8698000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 25 94 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 94 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 56 indices rho q29 m29 29 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 56 indices rho q29 m29 29 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [-0x10b951056111aa13e83c94829ac9769304,0x5e4bf0282ae91266ced6386c7c366cbb,-0x208bb4c0e9fff09a498a8bb6b5ed898,0xafb4ec9ab88c10ad1a65331142a56,-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r30 : List ℤ := raw_ints% [0x2b0c710899a5b247b8aa0aa8abc78f54a718516272bb9d7b0fbe20000000,0x3e25406958c852e24758fd926cb37115c8bf48a6c0b68c35942c63000000,0x2aa9e1827cc82e0100fd3bef705b7501c07d613ced6f7f4a3831b6100000,0x1289fb4125f30f7eef4b812c3b7f2510ec798a551b50cc601708aa2c0000,0x5b9bd4e30ee750efb0c6512c6abbc8345f4d19f9e478fd9c7f35458c000,0x15673a44b7974eba9249cd049e5a4971ac90c8c8bb80babf4a464a3c000,0x3ee6d48f30eca41078e80d2353379b9a324efb92d0aacb1f6e849b1800,0x9518395f3aea7f9898b6b986f512c206e8a99a0eef565c301e67d3000,0x1221b504dc1046e5d62bf5113a904b01166d968a6a822c9fc391421c0,0x1d5311f6df5b11c811d27d9b70ddbd02882ecada9ac736f630748d80,0x27c3684602704cbb4a11339ac3a81b2337880d27c46078ced764170,0x2d776be5b758809953fbb0d35d2036b91d69c1e2d2062850737340,0x2bfc3ca9e761ed1e68da3b86d4a556093b1e48d02a99d39840ef4,0x240b9634c805b3c35908da59f583287dc108dca2856e87442fd8,0x18ffe5faf4019b8cfb8834d1845edf51a850cda14f5dc76dd8d,0xea1531c051c19a2ceec3e10e0d12e4e606aaaf75815b14f00,0x72f68440b513bd30fa7ade8d84bde717491d7e8e25ae813c,0x2efd29a22b85c831e2b965d337483c09d3567692f4d5570,0xfca9c44487cb7689e9a388346b0e742120149bca14a3e,0x449d855d4c654c2e3a11896b5dcc8d77d32aad3e8180,0xeaebc004efc6396c785bc62e6f835eb43fb54661a0,0x2620c1e0ce2c2a25a852274532cf9e2841f4a2378,0x4693f47f8dbb14f0f602d882cc4946e38612f8d,0x52f7f002a3ab6fa96bb927253a9773832b600,0x2e8dbce1ed3ba2a8f5624b973fa75329ba8]
def m30 : List ℤ := raw_ints% [0x0,0x2717f4ca267ccc02b3aa0826040000000000000000000000000000000000000000,-0x444fc26a3f5fe144bcb2ff1c97e345a499f6c53a563fc75c4f16dd5525341fad800,0x39c03990e75e69040be4fb10396b0fb305b62d4b0ad1d04b5b259673ade61d0ab200,-0x1f76ba6b1b15f58cf50081a6e0b7f47005713aacb59fee27b3e4cd4379db4bcbb5e00,0xc6a494765c64223e841b6086a5e900b8eb463cf09a3ff77608c9bf717063681377280,-0x3c7c7b313259377b101e3b49c587d86ecc18f913ebbcb44c36ecbb24d1ab41997c2180,0xec9b0e0d537c3e21923352a2fdc614adfd22ddd03b3abb8b7ec6360a5ebb440386f200,-0x2fb685179f4002a2da86aa6a0a639e8a406f7817fc75a314c461476fb652bb3a5ce9600,0x81742f94d9912eded91cc660a8ec3a82e81a54d7bbe63e44182b0a2a6149cb7586cd520,-0x12b9f1b9a81b4053264bc5494881ced8cea4b89353de01c7b3c2bddbfa68fca8b75d75e0,0x25613fdeca9f3491a32687587219cb4586a1422270f5dc99aa55f23de66b8b2f6a440f80,-0x40e58d6937b7809e92b034ab7d3bef7ac82ad3897d2111b04179709b260af5879362f280,0x62a4d7f7e259832251b335faffce22b2844423ae20a925be495c758a0e464c1b10923520,-0x83f380b8b0c16aa0338314f6c2d549af61273eea265b41d464843d6de2053f820c7c5be0,0x9bf23f4c2742ada12d243d3c9b06452d2a526a8c602a26eca2179112c7f7ca8ef685d200,-0xa353a4788ab9622920af44e1045f6d751b5520b25183b8996d004410a277fadc8a446a00,0x97ea52cb71f50ca635e4eaabef5469e86f4649720070aef35c08b3a2f1c20a6342740848,-0x7daba2014b3c10ba86d73a37e86e6890dd888d0df5b868a6084c258954bb9598e4e79a78,0x5c88266e7da7559f1a5dd28b54358c730f9ac36b875dec69d9011fb25bc11b842d5dd7e0,-0x3ca710c748b1c727787c74a795b777771dd204a410a06e6b530ec2399d7c1a6d1a62dea0,0x2360a86021a1e075f7ce4737161f7ecb3d635f19c081ff7c98c748aeca76f84bc387b228,-0x12581c5f200513ddba7e42270edcac1abc595caafbed431f3d5935044a7e9732630a3718,0x871558895e156dcb2ee6fee644fa16989a144db7055b80ca12a7aa5b6c25cb63fb67d80,-0x37103583a3424043e863e10deb68674cc0eb8e66e69538dfe18b4728af91f9fa01fc180,0x13d2f374850a407ad81b51de4da914780156549235db04dca89391e6b65a212186e5ca8,-0x6482a6d20d82f128c720ccab39c228d99c43aec3c4e00f638682d9bcc350d63761b218,0x1bea9b2aa827881953a3bbe9a60018531c439925841945050dedb6233a572568487460,-0x6c31b238810af67380b74c4e827353d186fedc4a996f3901f01f0be448c3cad95f720,0x16b888621327371a337401a38ba95f85d6b9ec5045bec82a7ee86b13cdf8a8830a208,-0x41b93f47ff9e40e47ecee385a419a37bb5d0c6771010051a694801a42acef9a5d938,0xa254792f3e12c6cd6c6a9c2d2a28884bef9bf1bdd3093d010918982e305533d6800,-0x15309819ea7045b000cff13277f11543cafa93521d7bb1023e6c9762a2401fe8e00,0x24ffa71baae7cf8ef0ddfd846b39dd3d2be2188a8dd747541a849632fbaaed2ad8,-0x35485766fd688c96a6f82a00bab754a33273249545460410148ed109c406ccf68,0x3e47ad246c95f3d7bed9b83da32fb79e31b6552474cd29263d7b0cc57bd6e2a0,-0x39f5bae10b0f2dbaf47f9a700d4874634e2c4fd6bd5293454974547da83fae0,0x29f63ab0404f4078675c1cac44d33bda422e5c7ac6275ba690080791842df8,-0x16f9c95b8231ca8ac74c7876b51a424420755ad6f9ae949b858d1573913c8,0x9305e4e5a046e921fbf8967a7f42afc0b9721fae41a4eeef97640c83e80,-0x291f47a5223e308e0127d64588fcd4f7d691f75bc3b3e95dcaa0d8d880,0x79c4991cd530a20be4ef8f2f3a3988320714fa88856e82503a9a0518,-0xddf5482052fe3ce55f60a4b2a407adf2a5300fbb44459cb5742c28,0xe1f474b7e0fd591e45ea4b55e22a162f2d38a90d9954a0e227a0,-0x6ff5e715641a305c44997339238170cba654ea74b092e3b6e0,0x15e8c6b8e5bf24d6b080871e598e2f641eea6588f0ac6c38,-0x12e71b5d4cf880ffb43a146abffb5d75f53d7a212c888,0x204389e8526dbf55be40000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 25 96 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 96 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 56 indices rho q30 m30 30 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 56 indices rho q30 m30 30 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_30
def q31 : List ℤ := raw_ints% [0x2e8dbce1ed3ba2a8f5624b973fa75329ba8,-0x10b951056111aa13e83c94829ac9769304,0x5e4bf0282ae91266ced6386c7c366cbb,-0x208bb4c0e9fff09a498a8bb6b5ed898,0xafb4ec9ab88c10ad1a65331142a56,-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r31 : List ℤ := raw_ints% [-0x77d52f0f3af38fe20a9283db8ca605b1e61026ba12031dd0b4c9940000000,-0xacf0ded045a4d86d349e48914afe9bd51726922116aa4afa756784e000000,-0x76b0353d6cfdbf4e34efef95879415fa6a7a5dc6b17431cf5b47e26200000,-0x338ea7269949532b68d1ba4cb6de964b7793e46befe42b6d08a3378c00000,-0xfeac5b23254e4d415fcf974388456638f9bec662e34ba2ba48b9af8f8000,-0x3b7a6e07d6e5d88b41c963e7ad74932fb08d2d598a17c1692c02d5ca6000,-0xaeba47048e4f8fff4bb4b545aeceab84c077067316c749aa2f5a2d74800,-0x19df88036665671bbdd31865f9b571935cc02664f941eef1db44c9a7e00,-0x3251e94c6baec78599dfe32d2a7a8eb6a41adb4036a9cb39c6d5744e00,-0x51577fa63ee51fdd6d0cef6d163869dfa9e17835e060a8e9886d5bfc0,-0x6e3ce8117e520d39216c634ac2401fa5a080bd7a55d6361a7e4f6600,-0x7df9e85ec0d64219736bc27ccfd25742588d47ba5cef4dee0e2eab0,-0x79cbefec341e0db3bc401ba52f3eedd4c3d3a05252d5eb58077960,-0x63be7a1ae671427cc7c45457884645c712a8ce6c190a818822434,-0x452116e0eb45e57d76866ea0acd03240455d76469c6092e4d068,-0x286caeee5660f461a239f8a4b65848167ba27ddf015ab6680a3,-0x13d6435a6c024797a46833a9059c8337e1e6de05031776b5e0,-0x819ccb2aac9c72991c08e75ef7a6f78cc35384d748c67b1c,-0x2b844de0948fc8d8826ac0f8d09d53ca4cc42e0a2d55d90,-0xbce3950f90a23554d5246acc741d3b19c3d9ac5ec7302,-0x285fb88f88c07eb1e08b0522237dc17ab7475c3786e0,-0x68b770737a7ea0ece140b5a4dd504d58e65d304eb8,-0xc195573d4817383c4f9fc79ff4f2fd38706d31c8,-0xe33df398bc383bae84dd7d2777cbbc9fa375e3,-0x7f4e4e69fad0a08938ad47e2dbb5aea54e20]
def m31 : List ℤ := raw_ints% [0x0,-0x4e2fe9944cf998056754104c0800000000000000000000000000000000000000000,0x87d3e9aed1b55b966b122a80c72356eeea4e1e21071b9242d93c4cd4f814fd602800,-0x7222b3eea3b5675b706fc5a2cd38ebe00b6442f3a3739184beedc244371dd844b8e00,0x3dcb0163594436f52d3f84df3bea7170e46d9a7e217673df1130b9be3c3ead0d981200,-0x18393f96bc6a5716e26259615b81a29637c5912f552b464132ed238c31b4e61abcdc180,0x75373cebe11ad131c3017ecdb8864f58d4d6af9fbaba752f596c9c7b0a7884b2914da80,-0x1c747076551bf19abc3d9493551cef76702cf5c4d9ffacae85af283a92144c83894e1f00,0x5b2244a09ec34eeb872334b47f55fcaef53e8e505cdabd1d5bcc820e66d466068b4a9100,-0xf55d83a7a1321e0e05cb174c047bdb736ad63f71b18ffbb3feca695ca7d06b4028c11de0,0x23359fc113d9099cbf783545dc2d4e7a108af52b3dd5d5d1150cc69ddade3a4785a7d6f20,-0x45b1b4809a13c96ddd451fecf4cbd8e0a4670459328818ef184ad412a2089c204bbe61fc0,0x77f0c8cf2591e12502572928777414542e7b4c588c93453afc033d7496336b94d2340dc40,-0xb4a48656e503b6995d403128aa1eeb480659f40746e1236951c80d6769b1e6c3059b4a1a0,0xef51d95cfa9d44f343532021c2239f69e34e056c2dc41c30e0cd4a4cf057eb0f473553b60,-0x117feb232b967ae480700fbd0fda57f1ad412d4db9ff1754fde2d9f8630d6b5118b6690480,0x1222640e1400623e967db13f3e5e11fd73f909e3252350fc004058e1200732e78aeb74cb80,-0x10ae195816cd842df0a743f7c5f5207975b3257094ba09b4b23a844a001f336469ce588a38,0xda3200787cc2875c82a34f4d6f98937cf9af4db6fc03eabcc3fa497558319baf064885708,-0x9eae24ee3f64a38ef65bbd38e07a0f5622b99377fec27b2eb849908af4e523571f4f44530,0x66a8f639cf4dfe78eb5410ca0bb2b714af732c30c542e0a2c05db3567c4533097783d3dd0,-0x3b0ebd0d387c181c5091f1df12dfbe2f4dd61d3da693f3916512f5078abe2194a741ebd48,0x1e2d8bd5caf59c000f0d6c5105decabc0527345d9fe76da4d361afa7077ee26b4f3a4def8,-0xdacd7203fd5aac43a355493e10fdab369bf3cd28babeea04e07ed7a7cd977a4ab8c7bb20,0x57bb2a994e9a6db07e807962e3c59971d9e5de355bfc49e478eb60cc9ff91668645530e0,-0x1f093a381731f0cf97b341f6bbc6c339a4431cdd0ca0af7e2aabad30e0dfc7c7bfa2adb8,0x9a7148a789dcf51560b52b0046f41cbc01460d8d322b7eb5dc17b6559d38cace9843e88,-0x2a0c511a0b92d2c8c12a0e1cfc76c4abec8c533ec46baa1a808c82d8e002aeab51eda90,0x9f8508ab807fe6faeba614bb227cb6771c3be706f5aac610b2ad68dfffae673f7c4470,-0x20bda42c794e68627799ad12a8cd2c028b5bbe2178f795eb000819c5f1d7e6f6007988,0x5c67ec6401694a36492d682e6cc99419cf495d0f2bc3de647366032d9f646b02629b8,-0xde4396c959a83afbd601183af891e2bc0182836d5a08fb118c9aaa0feb6ced29af40,0x1c31fdf31e89591af186d35108dc89bc930ce2ce95566a9ae72acde4303eeade10c0,-0x2fbb02d5d953328311ff4cfe374f798bc6919a56b7377b615d1c14fef54666858e8,0x42781f0b9e87954864b7328c1ed5912d9253b1f6ff56561e30133c2364ae835ad8,-0x4ae8e1c964a752ab4a332b2b331218cedefc40ac1d095100b0867f78cc53d3c50,0x42feeb1a619680e3bba2afeefc66ace44f84004165fffccac3e4728643c5e4b0,-0x2e7110530280a992e79c7b8e4d07355935793fa544bbc5d1077891fd50fd098,0x183f4e2024fd9495aa6f0ebd2795cc76cf38020c6a99fefebea3b786d9e028,-0x93447a9dce2f1638cd78fcb700ad28c6333e96a2178fb14be8d6433dc820,0x26e479bf529037126ad86ec43ac4feaf344bf5084f62538d3cc91458be0,-0x6c1b666d7391cf6709cab329ba60f6961b46ba76812bef95e74f8e948,0xb7c5344d4c4fc9adb0c7b47f685eaa41a52385468517acc1c87f078,-0xad2ecbdd92c739c3eb45d037e8b02403e91a2325220b95734a030,0x4ec6db514e7ffb155766942a9efd389c066f6bda4d06ed280d0,-0xe0448b142756baa0945830f3097bc2110cb798bc8993fd78,0xadf414c7cd99bb71656f3243e1e96591613d065988948,-0x107257e8e36743968c600000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 31
theorem quotient_ok_31 : quotientCheck 25 98 31 num den q31 r31=true := by decide +kernel
theorem quotient_source_31 (size : ℕ) : (coefficientsPoly q31).map (Int.castRingHom ℚ)=polyPart (key size) (X^31) :=
  quotient_from_check (key size) 98 31 num den q31 r31 (num_source size) (den_source size) quotient_ok_31
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_31 : cachedMomentCheck cache 56 indices rho q31 m31 31 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_31 (size : ℕ) : intPolyRF (coefficientsPoly m31)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^31) :=
  moment_from_cached_check cache (key size) 56 indices rho q31 m31 31 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_31 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_31
def q32 : List ℤ := raw_ints% [-0x7f4e4e69fad0a08938ad47e2dbb5aea54e20,0x2e8dbce1ed3ba2a8f5624b973fa75329ba8,-0x10b951056111aa13e83c94829ac9769304,0x5e4bf0282ae91266ced6386c7c366cbb,-0x208bb4c0e9fff09a498a8bb6b5ed898,0xafb4ec9ab88c10ad1a65331142a56,-0x39d7fe1cbe3bb5861822eb45071c,0x128932b88493d4614842b6c20f9,-0x5c43d3762df7fbeb9c7df1ed0,0x1bc834a2b99f27e74826b324,-0x8118280d9c85e12cb547f4,0x2402cf6ab89bfe6fa3957,-0x99a0b289cbe1eb1e2c8,0x26ecfdc16ab330a212,-0x94e6f054e6b4578c,0x214c6b3594de1d5,-0x6e38c9bfbb680,0x14cc358aa720,-0x38313853e4,0x8456db73,-0x10554f8,0x1968e,-0x1bc,0x1]
def r32 : List ℤ := raw_ints% [0x147b1fb85aa7c58405c3887c91cc5e2f50c9b517cd89f10f90684a100000000,0x1d8cb06cf9ac25f05a29e26a5b9a0f7d42db33bc3ddf66b1e912f5918000000,0x14460d98ffe066d11e1b1645fd1eab9f48f4352d10ea3ac3be9d2bd4c800000,0x8cdcc79a3430850d053a34a088d4b22d1543c91c94223230c78dcbbc200000,0x2b79204957f2755623ace9d4c79bc28e32f6859021940cd88f5fa0ba560000,0xa263b7f25b5921fffb37b7b924fc490daf5dfeb8d383889c838e97d530000,0x1dcdcbcc1cb83b59e965f29cc758e0a2979c240990cb87d0cc128ba234000,0x469547b15a0f1eb90a17c3e5d20864760acea27e71bbcad6fd2e9b9f3000,0x8936d8f28b6b55c6152087b82b87ad5dedae673678a22f08644c5371a00,0xddb35e9503eb328ab4442ad3ba4a168881917e19d7779e5bd81c7a8000,0x12c4e685cbe305fb749235b7507c341306ba91739c246565252580b640,0x156fe83783cc112b7073b6e8096b557473d41cd64728883f6e5795080,0x14b6c20b38cdc168de69d28f353be28b8f2594e7728900be204fe5d0,0x10f3f12fe5c1e63aa42e99431ffdbea650ccd70b7b960fe83599ac0,0xbbdde0fff83a965458703028c671ec790eb464cf5626232d968cc,0x6dc7aac4e32549da7c16edb5b7fbbdf2e6066fed153830dbf158,0x35d4582fff8463250c98665df894ae6c5ce5e1d11e39eccbcdd,0x15f6cff3b26d38b9c49eca9ce195564302a9912cc5fbbedc00,0x75e28c45282ef2aa7472ae051c324bea46bbd51d533fe0e4,0x1ff33a3f720a18f9c18574d109675bd625bb8a38f229370,0x6d274b9c430858d3350849ab64513789610c6de88807e,0x11acab0a286085ee52a76b20d31ad84ad24dca6e9b00,0x20a25caad97a938d9034b02674006f00ca410a8248,0x26420e042cd373ff567d99c828d813034ea788f8,0x1566fd8e41a73ddd7dd4f33f9d531c7b39209d]
def m32 : List ℤ := raw_ints% [0x0,0x9c5fd32899f3300acea8209810000000000000000000000000000000000000000000,-0x10e1d56c4a4268fb5ea61eacc438a786ee5f75a5ffdc56b6184e4d4dca0a8aaea4d800,0xe1a38953bd9c3a0d0d907d49609e963dd0ae6eb641da641856cbe813d463d305263200,-0x79699f6f68a121a2c65c12e2e20c2f801f89c93b32b92e2c662447ed59f6b1c69a91e00,0x2f4abf4b6a2056a95fe576ac8e508c03781fc3446d30cdb9d5aa23b45b2b763c7e824280,-0xe352bef4e97c7dc59e1fbd85810f7c866fa99aa8f3fa6db01f30a6074cf15315a2d5d180,0x36cd7c09ae287e05f7b76e622b5244cf6921206141279395883d169a1c7f1a4845efe1e00,-0xae412348d0a48ea897d3768f6c8ff54f9be56476a1377cf645b1052ea7e582a6148e78a00,0x1d1a079d4c12135e1b70adb0a43ea488ea3885c47f12c0ba76316aa2844b969c647fb66d20,-0x424aa470f34fd47e19f400f7aef7e6b42359040a22775a4c5f2e1477c2935dd06d18d2dde0,0x8223f5f7c52d0b86393da40034451093a66d9ec4563d07be792c28bd0d24862abb3535ca80,-0xde0a493d851bceda43584f5ab225033250e459d20fe09fbcc8e30d40f43bc941f014cbbf80,0x14b670d1d996b82a9c9863dfbce54c9e2a3d0587b8759506c2d212bd9efc72be96164fce120,-0x1b2e6efd30e6a954f5eff8831b0e11d7989cef26633282b97167d99cdf5cfbab46cca321fe0,0x1f7c59e00205eb77487cb481df2c3e84201b486f496bd076c0a986f2658414a7ff0be680600,-0x204998064312723a0bbdc20fb2d41484be658266aea707b653d5f359d4dbe837f86995be600,0x1d5f5531007ec9a28df2be203dc80b3455eea4a1b90b44f3f409e6802fc492399ccda843848,-0x17bc8d9660cc93cde266918426ac5cdd31d7e69bdb9ca8f89c5753e821a81554a681bdaba78,0x110d3785da8cd6df63101c565f38ff86b21d4242c3fc452391be8ea28c7e1742545928a99a0,-0xae3be1c62cd7ebca678c31431f2f4e6dbd3a33af1ac8facd0578ca6b455f697ca1933ed6e0,0x62ddb32ac66eccb40be0b5999a57cf2b99b17647b50209e2824e02a9937fe9154d9ad99528,-0x31ca490a0b1dd5d6c44ef17c8a86fc6d92e54b339df6677c05da05ca77e2f8376b147cc018,0x16377de84f0862b9f703b9347e975a4de680b4932bed4c4a9ea4550ae0517576876707f880,-0x8c3525d8c8e678356033659c24d1feb40cec7198b6651c7b5fd2240fd44aed144cd2bb280,0x30bd8bb0960d3a0e9c81f7e17eafc710b32656cc7b6b1b063a2bf1156844f87454cd18d28,-0xee0f35324578e53fe260bad8514becf10daae433de7510b7a12b1dc94b4bc00381ea5198,0x3f8882c000e8f39bc94072fbba127858981ffd0db1160949466a377919a1c773e227f520,-0xebeed416461e060ee8de115be93ef4872dcc964e21446b5c29e57c7878b39d04bc7d460,0x2f538bbb0d3cd53f60831a2d71bded9a2a8905e9ba5d1285086c938b7b236a007d03688,-0x825124f8eeb02ee579da28cc58a0186afd02413b26ecd823254b0d653b69d545bd10b8,0x1313a228168144528093ff7558eb2c93037e9a27c856f28d48f59162e182b2b8b8e800,-0x259f8d78a53f17e977dc818d66086c74b8cb189b540cdfa405b210e97a786cf6b0600,0x3dbd9152ddf62be22a99d2a0b31c86d850eb8a5536354d686a190bd531a661edcfd8,-0x53204f1136dd1e66998c487c3411a507f770a66be8176433a3fd13afdff80cdfa68,0x5a4e2791cb2f2c2acea1c6dff91d80284fbd20bc0a37577c81fb76275e99490de0,-0x4d98ba68e68c4be85695135f9d6bd147347a3321c49e560fd93fdb07e7f2085a0,0x337d28cc5ec4c917d0369cf5618e06a7d6e8b6dfeaa6d2ef915311a0f94a61f8,-0x19a034cef99ade6a4979b6d65e388b2100388d3d1caab46ac9c254d443ae3c8,0x93ad3026abf0a1e79876e9d88007c9e1f51b95fe58bf489ebbacf5bfa2380,-0x24d01dcab6adc39b9d7c144a242c39b8b78c11311be4958670308e16ff80,0x6006b81286394cd91367fb69f9361a7eb1d6c61fdbd7f428745c8b6f98,-0x983001317cbcf96761346c3773a39d382226bd99fdd4beb0ee87d1a8,0x84bcc71fb49ebdf618ed3d7c4bc082e0fea46035965dbcca623ee0,-0x376bad2ad862ecf2a7de12ae112f6a2a9bc68e11881e1a97c9a0,0x8f7253654f58e85ab7c450e0c30b5fe4acb74a6fdcf2c3cb8,-0x64070dbebadcf31851360d126eda6b3ba7e2627bcbcc08,0x861d8e4e652a7c0911000000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 32
theorem quotient_ok_32 : quotientCheck 25 100 32 num den q32 r32=true := by decide +kernel
theorem quotient_source_32 (size : ℕ) : (coefficientsPoly q32).map (Int.castRingHom ℚ)=polyPart (key size) (X^32) :=
  quotient_from_check (key size) 100 32 num den q32 r32 (num_source size) (den_source size) quotient_ok_32
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_32 : cachedMomentCheck cache 56 indices rho q32 m32 32 10941037027447311758448126812160000 32=true := by decide +kernel
theorem moment_source_32 (size : ℕ) : intPolyRF (coefficientsPoly m32)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^32) :=
  moment_from_cached_check cache (key size) 56 indices rho q32 m32 32 10941037027447311758448126812160000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_32 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_32
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<33) : intPolyRF (mz e)=rfPoly (C (10941037027447311758448126812160000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^e) := by
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
  · exact moment_source_31 size
  · exact moment_source_32 size
#print axioms moment_source_32
end
end CatalanCore.Li2.NVMod.FamilySource.V8C33
