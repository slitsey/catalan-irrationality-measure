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
namespace CatalanCore.Li2.NVMod.FamilySource.U7C28
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,7,28,size⟩
def bases : List ℕ := [1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
def num : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x320a0b16553099e2a00000,0x42c49e6985eaf2fb820000,0x2a176db11ea043ee270000,0x10ad1a22174b1986e57800,0x4a8aa3002b33e17869e00,0xf9dfda58bd46ba432b80,0x28c256e8a805c8360920,0x54ddd8f1322d8d49770,0x8f49d102df4c6e2230,0xc64c3d9d8efe2be10,0xe26d33f86ddf53e2,0xd601e00025670ab,0xa771e277e56dd2,0x6c22aa1efe375,0x3945d0a20a04,0x189e09664ee,0x8734910c4,0x242e45aa,0x7458ba,0x10847,0x17a,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x5,-0x37,0x21,-0x3e9,0x8f,-0x6ced,0x4d27e,-0x5a2d01,0x1c51d6,-0x10d0971,0xdedeec,-0x17e107,0x64b0994,-0x242f7713,0x1e0cd7d,-0xfa6b067,0x904903,-0x48b841]
def rhoDenominators : List ℤ := raw_ints% [0x2c9991a80,0x7edca4,0x97f0,0xa5c,0x340,0x19,0x3c,0x1,0x20,0x51,0x1c2,0x37,0x108,0x8f,0xd,0x3cf,0x2080,0x374,0x5610,0xf24,0x50c0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 29
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤28))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤28 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 29 omega8=padCoefficients 29 (omegaCoefficients 28 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 28 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 29 omega9=padCoefficients 29 (omegaCoefficients 28 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 28 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 29 omega10=padCoefficients 29 (omegaCoefficients 28 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 28 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 29 omega11=padCoefficients 29 (omegaCoefficients 28 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 28 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 29 omega12=padCoefficients 29 (omegaCoefficients 28 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 28 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 29 omega13=padCoefficients 29 (omegaCoefficients 28 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 28 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 29 omega14=padCoefficients 29 (omegaCoefficients 28 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 28 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 29 omega15=padCoefficients 29 (omegaCoefficients 28 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 28 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 29 omega16=padCoefficients 29 (omegaCoefficients 28 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 28 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 29 omega17=padCoefficients 29 (omegaCoefficients 28 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 28 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 29 omega18=padCoefficients 29 (omegaCoefficients 28 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 28 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 29 omega19=padCoefficients 29 (omegaCoefficients 28 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 28 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 29 omega20=padCoefficients 29 (omegaCoefficients 28 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 28 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 29 omega21=padCoefficients 29 (omegaCoefficients 28 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 28 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 29 omega22=padCoefficients 29 (omegaCoefficients 28 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 28 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 29 omega23=padCoefficients 29 (omegaCoefficients 28 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 28 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 29 omega24=padCoefficients 29 (omegaCoefficients 28 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 28 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 29 omega25=padCoefficients 29 (omegaCoefficients 28 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 28 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 29 omega26=padCoefficients 29 (omegaCoefficients 28 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 28 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 29 omega27=padCoefficients 29 (omegaCoefficients 28 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 28 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 29 omega28=padCoefficients 29 (omegaCoefficients 28 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 28 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x13,0xab,-0x3c9,0xf24,-0x2d6c,0x69fc,-0xc4d4,0x1273e,-0x168da,0x168da,-0x1273e,0xc4d4,-0x69fc,0x2d6c,-0xf24,0x3c9,-0xab,0x13,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 21 li0=padCoefficients 21 (liCoefficients 20 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 20 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x12,0x99,-0x330,0xbf4,-0x2178,0x4884,-0x7c50,0xaaee,-0xbdec,0xaaee,-0x7c50,0x4884,-0x2178,0xbf4,-0x330,0x99,-0x12,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 21 li1=padCoefficients 21 (liCoefficients 20 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 20 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x77,-0x220,0x6a4,-0xee0,0x182c,-0x1ba0,0x12fe,0x0,-0x12fe,0x1ba0,-0x182c,0xee0,-0x6a4,0x220,-0x77,0x10,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 21 li2=padCoefficients 21 (liCoefficients 20 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 20 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x39,-0x60,-0x12c,0x930,-0x1ddc,0x3f60,-0x6132,0x6fb8,-0x6132,0x3f60,-0x1ddc,0x930,-0x12c,-0x60,0x39,-0xc,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 21 li3=padCoefficients 21 (liCoefficients 20 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 20 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x4,-0x31,0x218,-0x9c4,0x1bc8,-0x349c,0x4238,-0x300a,0x0,0x300a,-0x4238,0x349c,-0x1bc8,0x9c4,-0x218,0x31,0x4,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 21 li4=padCoefficients 21 (liCoefficients 20 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 20 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xc,-0xcf,0x450,-0xb04,0x930,0x1ddc,-0x7c50,0xedf6,-0x12278,0xedf6,-0x7c50,0x1ddc,0x930,-0xb04,0x450,-0xcf,0xc,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 21 li5=padCoefficients 21 (liCoefficients 20 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 20 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2c,-0x169,0x218,0x1004,-0x5e18,0xf38c,-0x16ac8,0x11f1e,0x0,-0x11f1e,0x16ac8,-0xf38c,0x5e18,-0x1004,-0x218,0x169,-0x2c,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 21 li6=padCoefficients 21 (liCoefficients 20 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 20 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6c,-0xb7,-0x1050,0x6144,-0xe310,0xa074,0x1a850,-0x54102,0x71548,-0x54102,0x1a850,0xa074,-0xe310,0x6144,-0x1050,-0xb7,0x6c,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 21 li7=padCoefficients 21 (liCoefficients 20 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 20 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xec,0x65f,-0x4708,0x9a4c,0xfae8,-0x70ccc,0xe5b98,-0xd09ba,0x0,0xd09ba,-0xe5b98,0x70ccc,-0xfae8,-0x9a4c,0x4708,-0x65f,-0xec,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 21 li8=padCoefficients 21 (liCoefficients 20 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 20 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ec,0x25a1,-0x8a30,-0x1f734,0xcf4b0,-0x16ac34,0x8a30,0x377dc6,-0x57ed38,0x377dc6,0x8a30,-0x16ac34,0xcf4b0,-0x1f734,-0x8a30,0x25a1,0x1ec,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 21 li9=padCoefficients 21 (liCoefficients 20 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 20 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ec,0x9767,0xee58,-0x1188ac,0x1eb768,0x35639c,-0xed0988,0x10cdcae,0x0,-0x10cdcae,0xed0988,-0x35639c,-0x1eb768,0x1188ac,-0xee58,-0x9767,-0x3ec,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 21 li10=padCoefficients 21 (liCoefficients 20 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 20 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ec,0x214b9,0xfdbf0,-0x38e9ec,-0x879f90,0x29c2164,-0x2161bf0,-0x3becc32,0x7ceaf48,-0x3becc32,-0x2161bf0,0x29c2164,-0x879f90,-0x38e9ec,0xfdbf0,0x214b9,0x7ec,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 21 li11=padCoefficients 21 (liCoefficients 20 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 20 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfec,0x6dcaf,0x69acb8,0x4ada1c,-0x6389818,0x4a197c4,0x15de6a58,-0x24e012aa,0x0,0x24e012aa,-0x15de6a58,-0x4a197c4,0x6389818,-0x4ada1c,-0x69acb8,-0x6dcaf,-0xfec,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 21 li12=padCoefficients 21 (liCoefficients 20 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 20 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fec,0x15d491,0x2312f10,0xa423d1c,-0x16ae8bd0,-0x4d5bb6c4,0x9dcc50f0,0x5858a516,-0x13d482838,0x5858a516,0x9dcc50f0,-0x4d5bb6c4,-0x16ae8bd0,0xa423d1c,0x2312f10,0x15d491,0x1fec,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 21 li13=padCoefficients 21 (liCoefficients 20 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 20 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fec,0x43fc37,0xa7bd618,0x60d9f8a4,0x72a44668,-0x2e8695e54,-0x1e7af1ec8,0x899027a3e,0x0,-0x899027a3e,0x1e7af1ec8,0x2e8695e54,-0x72a44668,-0x60d9f8a4,-0xa7bd618,-0x43fc37,-0x3fec,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 21 li14=padCoefficients 21 (liCoefficients 20 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 20 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fec,0xd0f329,0x2f440b30,0x2bb4347e4,0xb17e27ff0,-0x2fe033aac,-0x3808d5fb30,-0x183f52062,0x5d0f262048,-0x183f52062,-0x3808d5fb30,-0x2fe033aac,0xb17e27ff0,0x2bb4347e4,0x2f440b30,0xd0f329,0x7fec,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 21 li15=padCoefficients 21 (liCoefficients 20 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 20 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffec,0x27cd7ff,0xcd6d2a78,0x1169fe44ec,0x7cf23e7ae8,0x1034e8adf54,-0xe3de4ef4e8,-0x391ebf4de9a,0x0,0x391ebf4de9a,0xe3de4ef4e8,-0x1034e8adf54,-0x7cf23e7ae8,-0x1169fe44ec,-0xcd6d2a78,-0x27cd7ff,-0xffec,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 21 li16=padCoefficients 21 (liCoefficients 20 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 20 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffec,0x78a8681,0x367898850,0x675053886c,0x45a33b073b0,0x124698e747ac,0x1852a37cf7b0,-0x127d13d2569a,-0x39c23757e738,-0x127d13d2569a,0x1852a37cf7b0,0x124698e747ac,0x45a33b073b0,0x675053886c,0x367898850,0x78a8681,0x1ffec,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 21 li17=padCoefficients 21 (liCoefficients 20 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 20 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffec,0x16c79207,0xe3520a1d8,0x2493f5ad0f4,0x22742a628568,0xdf512c5bcebc,0x28f7c0c022ff8,0x30cf60378c0ce,0x0,-0x30cf60378c0ce,-0x28f7c0c022ff8,-0xdf512c5bcebc,-0x22742a628568,-0x2493f5ad0f4,-0xe3520a1d8,-0x16c79207,-0x3ffec,-0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 21 li18=padCoefficients 21 (liCoefficients 20 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 20 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffec,0x44a6b499,0x3a9c69ee70,0xc8c2b3a20b4,0xfd8fdfdb7f70,0x8fb2267c17244,0x28ce22087c7190,0x62fc98b7d5786e,0x848b2ade05c148,0x62fc98b7d5786e,0x28ce22087c7190,0x8fb2267c17244,0xfd8fdfdb7f70,0xc8c2b3a20b4,0x3a9c69ee70,0x44a6b499,0x7ffec,0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 21 li19=padCoefficients 21 (liCoefficients 20 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 20 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x14,0xbe,-0x474,0x12ed,-0x3c90,0x9768,-0x12ed0,0x1ec12,-0x29018,0x2d1b4,-0x29018,0x1ec12,-0x12ed0,0x9768,-0x3c90,0x12ed,-0x474,0xbe,-0x14,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 20 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^20 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 28 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 8 29 at hb
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
theorem cache_li (j : ℕ) (hj : j<20) : coefficientsPoly (cache.li j)=liNumerator 20 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x57c6e1c89812cb98da21fea18b000,0xa66730794aca67584f2243f7329400,-0x98db254f46604f1fe9a9453e5496000,0x5aa13a451ece57de01be273c67f8dd00,-0x26fae6848737042830f454001b79b9c00,0xcf57092a2c9d5b773d7cd085eebc8cc00,-0x376f7b65af298dcf8f716696875eb9a400,0xc3eea579d1ccc8587fe72f12b124be70c0,-0x247534e574b6af9901a1ce23d676790c700,0x5cc06e71fe6a19e8c1ccc67604abc8ba980,-0xcbdbd8233f9277fa389e262cc94e6145300,0x18660e4d16408d2b370cd78e0f6ea5965360,-0x28f9d6f3c4c3d0928cd90c1d4d8dfb301080,0x3ca9840176ebe5518d5b0cfe0952700575c0,-0x4f79d9534b326ebe282545670d714627f880,0x5c6acf7b7f90b3a74d13c7b95929ac2fd170,-0x5f946af1fb95e289263929fa4e4564a48d40,0x58080f7aad0d851f8223a55293fe74d0a0a0,-0x483f7355366df9a8b65948571a36447f3840,0x34d4be4c944eb4a28903ee7da48760326eb8,-0x22654a45218fc65d6eacb9b3b4057fe65a20,0x13e8af2981194c496473dbbc73ce228e7270,-0xa39298d78b833a4c51dbfd841cebbbb3420,0x4a4cb5ee1d687709d7b272667c73fb38b68,-0x1dbdb82c1aad3f08774b689f73f14b65500,0xa70f918448e378e5d88ddace2fab41fb80,-0x3322f8af50142c8fce65f23da96c620500,0xd8c4ec974c20e64da8772b4ab140e1d30,-0x314339b68d69ae1d15f72cbe4843e86c0,0x97f11a5125cee3724aba505733279920,-0x187ffef8f7d8b268942e1e8495d3f4c0,0x33f1550adb05fe9379c3abc7ffb0a60,-0x5872d53b1f4f3b7237e1d1356db9c0,0x755aeffb1ccfa039cf16b76055ee0,-0x7466af9c2e4f3cb3ec38eb8f0ac0,0x51584e08b7d0b0680a3980e95d8,-0x249ba66c961582a0b7338df220,0x924362c656300fa704904df0,-0xf45489e28ab187d0726e20,0x5523e36882ef8ad916a8,0x37d0c3bcc1d2e200,-0x1be861de60e97100,0xb29c0bf59f6fa00,-0x37d0c3bcc1d2e20,0xd220ff02d9b080,-0x23057fd5cef2c0,0x3afbc9d3e3480,-0x2f2fd4a982a0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 21 39 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 39 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 49 indices rho q0 m0 0 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 49 indices rho q0 m0 0 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x999c0b1f0a20e44b7dbb7d9ab34000,-0x11f93b9b7e7f1019a105df2161bd3000,0x104cdba5589797cf758993f551549c000,-0x989f4c76af251e1bc4efa36f0a83e0c00,0x40c53da8bde7c7f9e6db40a5dde1a3a000,-0x153d61d2d76707eca74e82e3d5e3c56a000,0x5998624792f388e057f6e4eae1865f8e000,-0x138267435df048e60da2f9882bf75bb5db00,0x393bcddbd79c9e9f4270740ccf9ad305b800,-0x8f6c2719fb3463babae2a69c1012810ce400,0x1365f459c52e4260c11314575ce431e886800,-0x248efe2808d51ed114e243e36066893e0ba00,0x3c65de4ca16c4bca53787f4f5368a02e69800,-0x57ea7d1e6cc43917efc8362ad825313b5cc00,0x7131159c349825679f747fe5ca8b069962800,-0x814697ac554f4d51b17205f97de988d0efdc0,0x833c7741bc3387968ec75460ad2313157e600,-0x76916a9c0cbd4c0ca5c6cf2b1be6715717d00,0x5f633e42cfd1ed93c31b606d6ca933745a200,-0x445297a0513845df4467bf500c3f700a02680,0x2b88b80896c671ecdd643e4b3038a82b23e00,-0x18a3b761aac8c2e624c18428ee77458bbcf00,0xc5c10d62e6e75a19f43ccf672fd0f4c97200,-0x57a6d22a43654e2fcc0854b27c6e1e6c4d40,0x2231fde157b39cf9bb8624a64b1af0834400,-0xbaf4969560a29a52b232324da1364750600,0x379da0563a678e2fbedb426c6adcb6ccc00,-0xe4bbc1413a55f018d669856673346e8100,0x3255fdb59a5a39d7f374d0191aae1f8400,-0x96011ec964df143baaa3c320d9b986a00,0x174f56cea2116fb4ed6d1f655e9607c00,-0x2f7b82e50fe1511d6986ea54d381c840,0x4d677aa5c175d42cfa2e480a395de00,-0x61e3c1b3068ced24e31fc412a3b900,0x5c0b17a4222c9925772c21c2f2a00,-0x3c8ecc8e00453f326bd95413aa80,0x196d7a76cb0654c3286d71a0600,-0x5da5080deb5e61b31bc830b00,0x8dcc54c1ea5bca937f34a00,-0x2bc99f3a722e647d3f9c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 21 40 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 40 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 49 indices rho q1 m1 1 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 49 indices rho q1 m1 1 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x10cd1137651b98f841c081bceb9b0000,0x1f1231341fc6ebc50ce91bf75fe484000,-0x1bd3f79dfcfd4090bd12007f60c2fc4000,0x1013f1aa6de9f22d428a3a18996ab3f1000,-0x6bc055fbeb5f0a76d21cdc8189482275000,0x22dd1a1699f367e289c9d1a64fae51ac3000,-0x910ef13fee8f372feea701a166492a66d000,0x1f250db2d3a62ffb3db2952d1e4819d112400,-0x5a0e7f4db750fc32a4267bf0cabbfff99b400,0xde5978e3e2571903b86a6ea3e28a5fee63c00,-0x1d9e3a5fb8bee9e6c3f802faa71cc73800e400,0x36f335cbaac7f21714d720fef15be331f5f400,-0x5953b9add869742e5f49b2d0e942453b61cc00,0x7fe0b0dd60305b4f9c308762ca086c4bcfc400,-0xa1d62cba049c1608411762615f67f8addb7c00,0xb59456a368c9ce38a0e794a5b0e2d519380500,-0xb4fa4589e7ee8ac96836148f3eaa6ea1e9a900,0xa06cfcdc0d89768d318c4350cc30b1d9f38300,-0x7e89f9278289c3f11977b6855c077a71a80500,0x58cb6abef7d2c099a8164458891d9a27311100,-0x376207b1e60daefa0eeeabc82e7df351689f00,0x1ea7be52cf724dd8a7b1430aa27d919e871500,-0xf05f97393372778a79670a9bac8fc5cb9bb00,0x67f97901a954bdffa352ec8a32c22ca2b6800,-0x27897d099ce7f4eeebec1e7021c2f8ae8ce00,0xd26734addf90bb08e45388b2dd513eb41a00,-0x3cd48c91c8f31993b67d0137ba6ae4f9f600,0xf2b8403215a8ebd95be7779a17cb7b4a600,-0x33b7f961a07171aa94130070117371dca00,0x94e505ff3639dd9836ff79179c93b4ee00,-0x164b130ccaf6d9e97caba6ff7f8c4cd200,0x2b9e68060fb2f302d7a49fc1f4bd2f500,-0x440bb6e6a9b24c84170f66b013900500,0x51fb3992109c831cdb0e7eb0098f700,-0x49075f747db2c24b82ff871aba9100,0x2d331c2bceb68954f46bb2815b500,-0x11b0f4be6575988633b5a72d4b00,0x3bfec583b65562b2d3c324f900,-0x524730320e5e408f99897700,0x1682bf2bc6443b863c0a00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 21 41 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 41 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 49 indices rho q2 m2 2 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 49 indices rho q2 m2 2 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x1d66de20f0f04bb27310e30a9c4f40000,-0x35ba851bfbac8ee9acdbf933c4fed40000,0x2f8944469917334685cf25e4ab2d3e1c000,-0x1b1f8aa0b915456664b9654e539085a44000,0xb3764e9577c740abc5aee1a892cfb3813000,-0x394f2cc89a1609c52bb8904b675d3b350e000,0xeb4300e9364756ed804f156e48e10e5841000,-0x31d1bb53fee2995fe2f535e96f6df5a5723000,0x8e06ea67dcb3dc6c00a17ae9ff3924d27c8c00,-0x15997710be893b1fa579c86a7b0071400e19800,0x2d598487a43888b7c461c6f305ae86e715f7400,-0x52d92208f4ab012f96a8f1aadeba61a82930000,0x848d9f79e682f0d401bf3387fbafa7405204400,-0xbaab9b54c3d98f0115fbe51cf1e94ffe605d800,0xe8458a77a7415513d56a52f84f5863e5a997c00,-0x100142e5f3bc6363718954cd92dcdc7827d96c00,0xfaa3ae27f957489dd4cc1687b4ebf7d430d9700,-0xda08c0703d174a9026f51e8700a16ce8720be00,0xa8a65c161e4e0f811b9da2493269b7b7c2d4900,-0x73f666157b86b016862d7c79d222464e97b3000,0x46cfc1377289deb8b5305110aea635e91668500,-0x265662d00666a3c7300064b015b5da44437fe00,0x125badd296528fd3a4c020c2196da7db61acb00,-0x7c0149ec9963aef81b134057c701a1810de800,0x2df6df78d41b94c33a7a509de08d7ffdc9e200,-0xee1a347f4ccad10ea7955e46d729aac0bd400,0x42e7068574ae5193e126f1b6e8216c74c5e00,-0x102faa81f16216fbf3657ed9c852ffeb75000,0x356d6162a3c0e8e16043df055a49322dde00,-0x949273635fb6cc2a03782e22524f3314400,0x156dbf72baed056da4c1792193f73350200,-0x28429024f76ede537053ab5a0c285dec00,0x3c145baa58dad727755134c807718ab00,-0x44ec300198e1c5fa97f803e091731600,0x3a20d8d4736e99e094dfb42468ef500,-0x21d18714c93beefba414b047d96000,0xc53ce9e8336d3bf4116a9e997900,-0x26756dbf500e14b034645bec600,0x2fbb4f45fff5940d73d18d700,-0xb916f194be3d6a56317000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 21 42 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 42 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 49 indices rho q3 m3 3 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 49 indices rho q3 m3 3 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x337404b9a5a48478495d8d52918ab00000,0x5cef70424349bb015813c20b6dfd22f0000,-0x513fbd454c5e62442677ae1caf1e93114000,0x2dcbc84b53c492b09834ad1e0819c646d0000,-0x12b3dbc56c64bb3f7e238004ec59850f3b9000,0x5e5716d81fb95d62ef2451386c8297ca538000,-0x17e3566f9e093e0a545634e95ebf51704165000,0x4fd959aa6e91f4a1ced901abf1ee844391ac000,-0xe07e44e09683550252042fa974b5d3147c0c400,0x21a7f02ed23099f92bde37f7bd0d99a0c3dea000,-0x45a15160699d85b0f1b44a17e0fa121e2130c400,0x7d4a1a4890242c27f2380d66d384f900bb40e000,-0xc557e280960ef0bb5e21e8dd578723fe64067c00,0x111747a01b8be2e3cefa00dffeaf8e95328f44000,-0x14e9dd47f6aa02829704e43bd01f4cfa711879c00,0x16a95e1dd5d9a89ca146924461edea52e1950d000,-0x15c935f6ec12cc68754a0801d868e253bd53add00,0x129a3221239ae5c28d9578ccaf7cdf86199a6a800,-0xe1cf561cfc9b45f16c96183eabac01b591131d00,0x982acb4a3174040dc5fe66dc8f8499d993fdb800,-0x5afc699e39b3d227ebe95291e7c01407b8717b00,0x30305267584cbf218120b9a71533a90ff06fb000,-0x168cce2a4ac8d904404359b4bf0a73a837c6a300,0x94adee6a80101f9cbd02f0d322d2eb0c0e98000,-0x35b94c7a232ea3ccf35b7129f855ec17d516600,0x10ee838a8c16e3cb377d3dba21c01c0143b1000,-0x49faaa0b3cd7782e0c35f54c24e4e39f350600,0x115cfd535a50dc315dea6a019745ef40973000,-0x377bca4bd490696824e54737825c6b19f3200,0x9502791af1125f130fecdc8b06ea5ee9c000,-0x14b2d65dfb681fa8137f0ae9409335470200,0x2554a0a00096960963561841ac5a51a3000,-0x3544ad4f8d462f98d81af9bb7e79e36900,0x3a283b6f01fd3ccfc821b1f83209a6800,-0x2e68a3081ceb67486b57cd6c54ab0900,0x195c49b08c8b2450cd3b790b6077800,-0x89a09e531d0d7e3e546daaa90d700,0x18aa3834909d0db85aa7a68d1000,-0x1baf1b1cf832f14fcddd5b3f00,0x5f14b2c6b6861e30f8e8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 21 43 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 43 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 49 indices rho q4 m4 4 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 49 indices rho q4 m4 4 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x5a0b0844e1dfe7d28063b7507eb2b400000,-0xa0cc40cd2413dcca8c4a4f1a68559e090000,0x8af33ef1a3eb05f76373eb41dcb227ad5c000,-0x4d63d4ea4913cd3353c325164c124e61d10000,0x1f3879e3921867018400d257371e36e74acb000,-0x9b84934cb958e1dc571faceb2c822ea39b04000,0x26dfc3f024a784af523396cd1576302985609000,-0x803ae269152a13e074a38677bb432e1e687b8000,0x163a162d69b3054d92b98d48d3278b5ea8d5b6c00,-0x3492923e4c84b4711cd9e3cf446c3d8f4ace31000,0x6b3415b841fde7f22ec3470fa4d0ebeec6f6e1400,-0xbe0a125fabe55c2ff0be415f8fa238d10a080a000,0x126c0c115ecc4b4a5fe83ec3fcc91d339ae101c400,-0x191fa9848f0d48d28533fffc29bf4dc9faeef15000,0x1e3d8059311ff2d5e9f61427822bd218734e7ebc00,-0x20367ffb99bc7abcf1a84f0ff5b2626919c98fc000,0x1e6c9773ceb33033df39950029b0e9dc0711680f00,-0x19810f563d498edd29684a5d7852a1f6b73a3d1400,0x12fb641466c59891fbabd391a3c8d58cd816237100,-0xc89d262c75af68231df1fc542e6af869fcbe86800,0x7579dc3068046e7ad472d0e28c6f16d1c0e8e4500,-0x3cdfc0623da4cef54c69f24bd5a85fdcb2b658400,0x1bd73618b152536ce159cf66be25f959e2a5ebb00,-0xb330e0c1021e350d1a1e097a47d75b477bbd6000,0x3f1fb771f8b2f3d1a5fa3cef4d6e727f08325200,-0x135dd4202bd8bca64b8787b48843b8e4ec557800,0x523cb8c92da02f3e92ece2bf4e1ceb370d16e00,-0x12b935c08c2c3837c3bc1e1a87973ee29389000,0x39ea4162c32c078e568d876c098af267edfe00,-0x963142fe5287415d81bcd9732060bf7eb3800,0x14169785ed00ba738d04a8a8710919e124200,-0x22c48efd383d4ef0d39b4b9f87502f562000,0x2f6b61607a08fa32f1a69857dd87cb0a300,-0x313edf7090ed584edef18a0e502e296400,0x2528993dbf81894949316c9245382dd00,-0x130ee17c423d221cba7648dfda22a800,0x60275ec7dde55b1e569787102ed900,-0xfd323704793d886a40048d55b400,0x100d71a1ca8557f52cae3b42700,-0x30d355520fa39495485c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 21 44 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 44 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 49 indices rho q5 m5 5 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 49 indices rho q5 m5 5 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x320a0b16553099e2a00000,-0x42c49e6985eaf2fb820000,-0x2a176db11ea043ee270000,-0x10ad1a22174b1986e57800,-0x4a8aa3002b33e17869e00,-0xf9dfda58bd46ba432b80,-0x28c256e8a805c8360920,-0x54ddd8f1322d750fe70,-0x8f49d102df449429b0,-0xc64c3d9d8ddd12500,-0xe26d33f855591b62,-0xd601dffec561a83,-0xa771e26a0d863a,-0x6c22a9b9e8924,-0x3945ce80ca84,-0x189e00da3b2,-0x8732f9ed4,-0x242acf04,-0x7402fa,-0x102b3,-0x142]
def m6 : List ℤ := raw_ints% [0x0,-0x9d934e788b47d5b060ae80ccddb8bb000000,0x1164b073d7d4e8ab84a2516e105d6c41230000,-0xedc3609a595fb0aa64217394555d7199b34000,0x82e3da79125ea5796d6ca00f03551da65fb0000,-0x342cea3b784215e86f68b59bfc8f8e6a16eb1000,0x100b96f6052d7b5838755d7bae6c056de81044000,-0x3f5dd6e3f42791067b0bb017e7e560b498f535000,0xce526fe5d2751f59aef576b0d4d449cdb793f0000,-0x2349aabfde4dd23a51b290b2f598a0db4919172400,0x52527930554dec359ad008f111c96475b4d33a1000,-0xa57f584e8fcf62f5694e21c09a115527c7af3f0400,0x1211a0b4b71e65f4ba93c933f9cee3a4c77aeb8c000,-0x1b9a5f6db4c96d706319b1a9aea051c44daeed39c00,0x250ee7f05b25c5dab447177952330c162d9237a7000,-0x2be2c9a68f6dfd352995d57f4e4e3df5c282e97dc00,0x2df783b6785e93079f6facb19598e79dd9f7fb40000,-0x2aa9184db130a982da761af130cce12a59096c51500,0x231dad0d8233ffb643ec89321022fa58f08b8b93400,-0x19a4ec74032f14bbad4950ba3b4899bd0bcc735ed00,0x109b4ec600d439c631a3628cc76bd63fae3dfe63000,-0x9866f05ede103a7be062b5caadedf538caafd5e300,0x4d4690db031c408725c6824581c3f644edea2d0c00,-0x228b81b559f956754b26b7052ba7ca45fcf86af300,0xd910ba436837fa705b894f9fd77b2ac9485158000,-0x4a8d1d089fa6ed9c6e63e38ccd0272e254868f600,0x16442a45d4c854a419756b5dae8ecc70efff5d800,-0x5be3bbce37ad92f32186f3326df580b5c8346600,0x144b21a39dc7798ba54b79944d2dc2c529262000,-0x3cc16ec849ce37c35a1f4f6efa9c1fb125d2200,0x981dd985edb49cb7cf574f5d0b725536ce4800,-0x1395e6de054b2672f6ed5bb2e069dd4565e200,0x208501365f8bcdf1cd216e14e9c45acd30000,-0x2a604829d3122ca9a612af0d0cb47fd0c100,0x29d6d9f5bc048676283385e09ae454ba400,-0x1dd53f53399942e5a4ba13a62843ac9900,0xe59a56715f825058d0ed374e9b647000,-0x43413530337d9b82777f7b9c72c5f00,0xa2803102a47276424144c238e3c00,-0x94e395b58a9f79b73db8606cf00,0x19105818a6587585f80a00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 21 46 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 46 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 49 indices rho q6 m6 6 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 49 indices rho q6 m6 6 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x142,0x1]
def r7 : List ℤ := raw_ints% [0x3ef0a1f21727218f0d400000,0x53c94535a41c550676e40000,0x34aeb35a5effaa7e918c0000,0x14cfa371302dd5d7be79f000,0x5cb78f6414e2900106d4400,0x135a2e6739b5fb830f61900,0x324a91764a99ff19b44ec0,0x6832e570d69cef33071c0,0xaeecfb5689bb4b3601f0,0xf077486fffe769ee670,0x110689784a155165d44,0xff078880a9b609bb4,0xc53d20dae23e07a1,0x7d8c7bd45ae92f0,0x4147a5d0320fe4,0x1b626aeaa28d8,0x91721d972d6,0x250f040100,0x6e2ccaf0,0xd86654,0xd8c1]
def m7 : List ℤ := raw_ints% [0x0,0x113c1c952f3bdb5f4a93161668403474000000,-0x1e1c6b985903354d358940d0b87f56b4bf10000,0x1971261590fba7bfc2e46d5472ffe010c0f7c000,-0xdd8efe1b5dddf6f79ddc037c29729a9f5c230000,0x574a775b1e2ece092e1c086f2045175d43d4b3000,-0x1a85fa9d5a7501b4f7c3dc199a3e242cc9b725c000,0x67759cc3895155f828dbc79898d02d1f7f69069000,-0x14c9a2e097a06dc5d38a8e7d800689979b6626f8000,0x3824ebf7c4b5d223dced472feab54f1e3e484078c00,-0x81379c0e6720ddffa96fb67a9a3ad10d34d242ef000,0x1002b68de1478afbb585e40b10e0d7d4409b9b259400,-0x1b9146626473e3bfe1b00637881e83deab49e51b6000,0x297d47307a04610aca65017d2901971b0cdce5396400,-0x36d8a771e8dc9b256af9bfd6bb1061da1bb4ec613000,0x3feaf69aab9dba285230c3eed31bf6662370e91cfc00,-0x41d7cc8231afe95d2c3495ddfc96933e4e7e1a4f0000,0x3c0ed7247daa1d18059f2657df76e5d11d02f217b700,-0x308d9a744b6ced0a2d41a642330a3754b85fa94bec00,0x22cbe150886546cf820b80b462a68672bba594101100,-0x161849f89a040d3836c09b2cd823493064558c6b9800,0xc6a375b0c931514e46abfb90e29c09003c9e6df0d00,-0x6291961797c783e97d2140981084c2c013846de1c00,0x2b13159220ec08353cb0aef927a073b8cf86777cb00,-0x108427e44c7ce14250c64934769a7e88a0ba5812000,0x587df595aaa1ca724b354fc32656834ef40af14200,-0x19bae14124c628fbb3d409bc46b0fc68d06e080800,0x673186888b5a261e3dd9425e78a47b619a2ad6e00,-0x161ad53fa321f9f596f2bf37e38453278c9e77000,0x400bc1b5d730936b09c24922729b2342f8a3ee00,-0x9ac9f91104d3e1be9601d9b9ac538fa6e550800,0x132e31eca71d50d2c8a7d7fc02d9dabc09d6200,-0x1e8ace8eb5ab98fdfef4114277470a1e33a000,0x2602792642dd5db4134998fba27dc97bfeb00,-0x23a905f7562b52879c0b915293994f6b1c00,0x1803518dcd97dc6480066998cf5f2d13d00,-0xad3331c5790922b52b3400558f53b5800,0x2f16f033888dd58e4da8e25ebdf80100,-0x6851d071bb86e2722aeff60c26ec00,0x56495140c5eaea8c39a1a34b3700,-0xcdc9a80449ac49f1ce7000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 21 48 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 48 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 49 indices rho q7 m7 7 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 49 indices rho q7 m7 7 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0xd8c1,-0x142,0x1]
def r8 : List ℤ := raw_ints% [-0x2a5e32ed33b73b7b3adaa00000,-0x38494b4284750c03d63fc20000,-0x234fb6f1eebb33cf20fc830000,-0xde9f1da1cfbed7d91beb37800,-0x3dd031d5f4917afd193532e00,-0xcdc5c9083b4c367b08ea8780,-0x214d10f15f902d915779c820,-0x44b68134ab83a39be585cb0,-0x72cf20a9f2290698afd470,-0x9cf703c1fbd38df18c820,-0xb0af63a6cb00cd8606f2,-0xa42c62f1b595d24dba7,-0x7dd5db68db5d405f9e,-0x4f3af39eb9b872b94,-0x28a54dedbcee5a14,-0x10c36cb6658d78a,-0x5717de190daec,-0x158b2fd08254,-0x3d738fd33a,-0x71965a97,-0x67a6a6]
def m8 : List ℤ := raw_ints% [0x0,-0x1e29320512a8bfe6c28166a736705bcb0000000,0x342458c5989a481ee458765471e1d65cf56b0000,-0x2b953017b77924f3f5c02b93d519ae8aa05c14000,0x1775718f566b4f925220695bca6de3eda233b70000,-0x9232c73d5f3121e59c2b4539853a2391d0285a9000,0x2be7353ffac235ab23aa93727f125031c40554d4000,-0xa9311f1ce7871c8f91154636363ee35c2be39255000,0x2192d02e31ca3d8ba47e5e32d8353ad87d88adff0000,-0x59847c82faad79e0b3f4b2df53ae5cd4f53bc3388400,0xcb4ed7f9eb51ca5636eaf190e3ce915d0e63cedf5000,-0x18d8ed0e53576f7aa2d8d7058993ab707d1c4fead8400,0x2a2e02470fdeb2469fd43119060e1de8d73dc7259c000,-0x3e8df10c380dedd46973688ba30515b9d20d84b10fc00,0x51712fc6f3c5bf383a14866d6855f1621226fbe923000,-0x5d6c35e83d7b0c4a27ed8bbb35f237d030f7405201c00,0x5eaab260034c019ae03acd8e186c3a55afa379efb0000,-0x54e23ddcb0300e5dc709c160191a76174b6c4b4accd00,0x4368d250f0fd3e4d9c8fa5b9c6248c6a0f6ffd5834400,-0x2f6b0afad2be8518cce84df4e6358bae08ac933fe4d00,0x1d872ddfbde3c4728e3533bb4877877543c864fca7000,-0x1041832d63c06c6fc8a2caaa07d80f74fe4c19ee3db00,0x7e52c4b3fc3d76543c649ead8e0a28d1860d6bc1bc00,-0x35f830f7c6b2d626c3831e7cbdd31a4a1bb272f18300,0x1434ad4229686422ce9ca8b29ed99f01ebdd64218000,-0x698f39726904415051a9b78f74f7b6a9169f3afc600,0x1de14a47441c620b63157656b1640c1614f0e2bb800,-0x7475b2b4f9a7f12a3447a048955e557c36baeee600,0x1831e7af7c991a5b85800412dc390c29ff5c2fa000,-0x43d5a7d4931d5ffd7af58a0e79b7e4ec82b9f3200,0x9e39fae1780ea31e49a07054120ac07e8f016800,-0x12dd5a456e620cd63649e4a3bcbc902551320200,0x1ccc99dc86ddb30ee259fa1ef389b290c3a0000,-0x2236e3ed6ac3d3b574e5932d2afbefd73bd900,0x1e7c6f00ac5aaf854c8a69890df0754137400,-0x135ffd8e41474f136514855af02224cbb900,0x82dfb8f6df74ef5deae84682c9bb1fb000,-0x21004287857a9599c7e96cbb3d2647700,0x42fb925612ec013d10e63df62d0ac00,-0x31fde098aae1576fdfbd5024b5f00,0x69910582c1a415cda5e8000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 21 50 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 50 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 49 indices rho q8 m8 8 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 49 indices rho q8 m8 8 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x67a6a6,0xd8c1,-0x142,0x1]
def r9 : List ℤ := raw_ints% [0x14429d6baff246ab7b1cb3c00000,0x1ade3453bed313b79eb887ac0000,0x10d28a5352c8bc10c65477880000,0x69d30dbf67db1deb7389018d000,0x1d4faeb30760408771c5f0afc00,0x614eb6eb11fea3d9d942f00700,0xfb2f3a0f296d80ad57fea2340,0x2047b01c7c4a4112a0aa30a80,0x35b891cc42842e70fc8cee70,0x491cd0c5298496c7405c9f0,0x51dde54f5741f7f00a286c,0x4b9b1ae219b4c1862e9f0,0x39890c5bd48e56548685,0x23eaf954b4fb5ddfc40,0x123cb01fd4c7a5eb04,0x76d4759e05cb6c40,0x25fabd67ac31f8e,0x934ad9d028d50,0x19903fffa248,0x2d8d0a94d0,0x2775b685]
def m9 : List ℤ := raw_ints% [0x0,0x34c81788e0a74fd3d46273a49f44a0a340000000,-0x5a51036955b4de822ed6c359e6a044d1c76490000,0x4ab2d59533ee9fdc30c2777b9e0f83091d59a1c000,-0x27c5f3523e981c91597cd7524f5f71032c3d0bb0000,0xf51ee2855d3db32f2b0daadbfd06c90ea039365b000,-0x48c49872f6be89bce251810909d7fe5db71a9fbdc000,0x115206242e2101e8a5b4068faf21a7c0e437d237e9000,-0x3652cca10403c6f010edc9ff7b3da038e09ff56218000,0x8f070302aa83873958695fa4f0f9f545c9c2e30e4ac00,-0x140a121c1b1ed595a791d3ef0503fbd8dc151079c8f000,0x26a934d9999d7d6e2a4fa4781e57f24391255bb65f9400,-0x40b811550290b65361b8c4acd17c5d26f896af3d49e000,0x5e9a201d5e4440912e2bab22ad60ac353a276f54948400,-0x7954757b43313859ab852e0d8000c7d02fc21ab345b000,0x8905cd3c51abfe860553e1a7d9f3e826576a3048af3c00,-0x889c49d82a9b7bc53f51d98ba918a29c49ee4363db0000,0x786ff027d76fa607f03acc85e730ac65717806219c1f00,-0x5df8206a81c8705f3cca4aea648658430a2d0faaafec00,0x40e446a650c9df84fd1d8715cbc99a66ee5f8e42385100,-0x27a2907e2778ce7714d5a6f382603e7959c2d317a63800,0x1561ae8a8fed25fc82d9ca666a42f45b9f20b28758b500,-0xa2a4fed45fc3ec46abad7c428f7561773740d332c3c00,0x43f0c2e328f66139d9e384a971a4c9461a421ed585b00,-0x18d69cbcfbc28561715df44a0ce48e6398146930da000,0x7e8770d9562e32728425204f0c6d11c9413c8bdd3200,-0x22de2cccd4c4363bc5cb831a4b850d8bb13b9c508800,0x8410b2f7011e8d8de4e5d320c62037011c1f820ae00,-0x1a9bbc1eeaeda27f62d0d134bb8956e84104e58b000,0x482dd10beb6eb3c966510042689c009c075e369e00,-0xa274cde63cb97cac2ee4e38902bf5ff12b21b4800,0x12a1a41feb4ecbe3e286eb18ac38d3363c35b0200,-0x1b427fd2cd614f806c15daea597e7abae3f82000,0x1ee72eb9b6387e2e6317c49de2f71efb7cf7300,-0x1a234b017267e2451def3be97e9b4449679c00,0xfab1021c184f57b8fe64e375695ad7733d00,-0x630bca4141a4cdec0acd435d6e96bf9f800,0x1725859ed0fd1dc6c020ccd321db290900,-0x2b03e6e89a524fbd267d8f49263b0c00,0x1cf486a7f6290f54c54c16f2714700,-0x3622fa7237e5d44b0e1c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 21 52 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 52 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 49 indices rho q9 m9 9 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 49 indices rho q9 m9 9 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r10 : List ℤ := raw_ints% [-0x7b689f49b48f9d2aa9a307d200000,-0xa3664fb86b65f264e145862ca0000,-0x6620e3950067f4f75b8b4ec970000,-0x28137718a511dbfa4fffd98ff5800,-0xb139249102998beccf5b932b4600,-0x24af04ce1575ca55836188479d80,-0x5e70a67959c3bd44994373f76a0,-0xc19a2b8a534a0d28a7906229f0,-0x1411a6bb1a81afe2b9e6d2d870,-0x1b35427f9f0cd676424af2fe0,-0x1e54f3368c5d919a2aed767a,-0x1bded23af48925e461ef26b,-0x1515a64098502f7cdc702a,-0xd1270158e9021e7ad344,-0x69548f121de11440fd4,-0x2a79a340943503b8a2,-0xd69e62ae56a9a194,-0x33403b7f37fedc4,-0x8ba563985c752,-0xf2c15df249b,-0xcb6c4eb92]
def m10 : List ℤ := raw_ints% [0x0,-0x5c5e292f8924cbb2b3ac4a6016b8191db00000000,0x9c7b25928ff61fe446ad0213a877ff8698a9b30000,-0x8018e7db50773a3f411eb76d385e21b2cd4868f4000,0x437cb304bd7be0922e5da5c39ee1e643e6f676e70000,-0x19b68bf6adbf24c68200d7699666d63f2d5a2fe5e1000,0x78c4ace0927b20136ccb5ed4855db6b39960e2e974000,-0x1c6a07cd638c20f7cf32edc62cfc5fa92050b05ee35000,0x580eaa06ec3bc4ed555236b13a4d371a003bd977190000,-0xe4fe8c588f8d5a0e93fda656557947918c51064c66e400,0x1fad1576751141f0fd99eb7558992619e8ee6d4af73d000,-0x3c4e948c5325e23efc478af75e788c16d2b147f0ccb0400,0x6393f1d6c3b1204f5bc039654b687caa5f1ab4644ee4000,-0x8f7f496def146fc2d8a038f4e035eb804ba127f28d85c00,0xb555c80a0d174cdbc8bb140d76ec4cb3f8485f196fa3000,-0xc9a8d22bf8a7b788a7db8ff90bb1f578cb963f517d45c00,0xc5da7edfc4bf0f79500810b505a92d4b9a1aeca4b7b0000,-0xab88f67b2e653c710123db3b18f40a1c594f17ff55bc500,0x83847be87197bd881daf9dc88f2c1429304a9b94c936400,-0x592c8c6463289b155e762c3c2317ec377eba151b8786d00,0x356e51dbec88d9c39e6b76a3bfd9b0b6dd0d3d6ce969000,-0x1c3f9a9a4a0099f65a95935ab92651299ecd092d6c95300,0xd25d1d6dbc872f755af09036ecb0e27a31edbb78923c00,-0x55ecfe09a03d866dbb42e80d17957ecee071fadd4e1300,0x1ead4acb245413d4cd28e59c8fa5e9c2fafc3b1a160000,-0x98626f66277670bc42ee38fa2f7ae9f7e92bd5b771600,0x28e1ad997dc55baee02b14fc19ff16c1b521229a3f800,-0x9677a174a7ee90cb59583fee7f00b1a121cd342ce600,0x1d65da8390075bda21ddc48747ece5fcd0e1dd7de000,-0x4d258185ddb8e34a914e989207235bdec53146f4200,0xa783fe0a494feb485dec7d739ff618b71fe56fe800,-0x1279a83cc59e4615ae61f395a391a2bc8d965b2200,0x19e5d51420eca71c20d0580c6e19ecd8d36768000,-0x1c00d119d5de434f18dbe347c8911d1a8f403100,0x1678a2e723c3ca24be3f36cc18ce062180b9400,-0xcb295059a85f5c742ec0987f75613c6749900,0x4b110d94fac5bb0e50376a9182f122f5d000,-0x103f228e4be08d3b48d4db1998456ab0f00,0x1ba05a4bcf09a38622cff218bb702ac00,-0x10c40c80b37d79ad1852c649996ef00,0x1bc0e889cbd33754928a00000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 21 54 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 54 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 49 indices rho q10 m10 10 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 49 indices rho q10 m10 10 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r11 : List ℤ := raw_ints% [0x27c3226aa1dd8d02ca23d4c1f400000,0x3492c07968b4730b5516ccb49040000,0x20cefc7f9533c59236dbddf3c740000,0xcda30fd46fde1f7bf795ae876f7000,0x38ba4138812e6c970258695cd0c400,0xbb7aa72251e525e2776509e120900,0x1e186922f61017be3c00ffd69f6c0,0x3d88c85029f60d21dd042ac2b740,0x65c28538eb0353fe0bb6c8f6570,0x8980b34575024044acf1363cb0,0x98b721694fef81c5d6bb71d04,0x8bb9140365b612d858b7c40c,0x692f53e3723526d17517559,0x40d7968682bfa36753af90,0x2070276ba3eb220308f04,0xcfa72c0e9fc8d5ff9e8,0x40f63f851dcb1bc326,0xf5619b88f7d52760,0x293359346b56a50,0x465ab8a061e2c,0x399c8e4b0f9]
def m11 : List ℤ := raw_ints% [0x0,0xa1a4c81330006478ba6d822827c22bf3f400000000,-0x10f301314bdc3ec8840a07e3e160b33232bf25e10000,0xdbc86f4409dccfa6ba1fa17245cdd3c59929121bc000,-0x7299e5db971f42fe868c19f34359ec6ace11e1b3b0000,0x2b338cf54508b591a8ee16f89b32f5fa995e6d92fc3000,-0xc8b088e0168cc1f24ffd24f44bab2932090ab187ffc000,0x2eaf70161ed4106d7a28aad5acb6704f701dd2978369000,-0x8efe84157fbd2c85efb01e36dcb1ce4b0570a62b0cf8000,0x16f6042fe837119fff9aed2aa9c3761d9ed04e97cc4ccc00,-0x322f13e3f00ee581b698cf415213502ea006d27b94037000,0x5e4ecc6b2746f61726f6c2041cc8eff926c4a23f42499400,-0x99a1829e31fc102d1adf7ba54028cac79e98e29324ef6000,0xda4e8235046f608cafa1d3eb30c274511b0b1e78dab8a400,-0x10fe00665b8365be7ed570a724a259cb7f5fd581ffed0b000,0x129c9da9ef4e5b4df3c4959eae9777fe637d4f293c4bd7c00,-0x11f9356b8b7ed6921f6314f2d8c7a7c028a34e56f03cb0000,0xf53af4e2067f7d66ce7ee288bafe0896daa8d30188284700,-0xb8cb2009baa667f781e3bb2288ea31ecb4a72e6fc1ce8c00,0x7b0b68c55a85842e7aa985a39fead6dbbfdb864acd089100,-0x48559849918d948903379fc18163ad3323fd0e242d8c9800,0x257bd8fdebc744c572b602d4ca82e053b470d9d9d3959d00,-0x1114d4fb97955b328b085b85d42f0fddf1595ec033757c00,0x6d2b05ad75197163c3539b8dee7ce5397b8d650a6a3eb00,-0x26102841afcb355e34eaf1ad79db3085fe0aec62bc72000,0xb8608e51e09867c2f92c3c0a5ae8ae6ca1e323e369a200,-0x3027b977a0fe026f6bfe76b048e9c98b96a198d2e0c800,0xac38f9896e4677227141dd404249564cc1992c23bee00,-0x20a05b2b3c6436d345a47da717f5d271078e85dab7000,0x52d0f41451d59f3d7355c71088e6f55433778378ce00,-0xad73c93ff7ef8c666060a4ff3dfed676599f3e54800,0x12644877430038e76c7c479a0b68db200a0552aa200,-0x18b0f0c96116102f9febda806a32ad7fe4eda1a000,0x19745d81d55b6449c3921b0a8a00395a24ca7bb00,-0x135e8079e052aab7fcea85b2dda5ec3d8e393c00,0xa4f892758321e04edbfb6cd47a8481ec1d3d00,-0x38f7d2dd60f7ddc52e1eb46885a79729a5800,0xb692fbd069d5440b557b45035c6a4265100,-0x11be6eb7c4d8943cea27d3d7c6d907cc00,0x9b474e3e7d5ae65c7bf8ecf7a065700,-0xe3941a96004f68045f7000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 21 56 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 56 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 49 indices rho q11 m11 11 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 49 indices rho q11 m11 11 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r12 : List ℤ := raw_ints% [-0xb42d666f8b61af9b1e00e7fb6da00000,-0xeded910400512cce73bde5bbe2320000,-0x9446258249c12d253884bbbe2aeb0000,-0x39fee95ec99cd7c32c87fcd19b3db800,-0xff8d1254ad8e93ddadfff379f203e00,-0x34b002d6b7080c7bb983ebeba6c8b80,-0x870b7c7607c9bb919f4c556542d720,-0x1137c517a842cbbab1d77d713a5530,-0x1c6683a4f41e76bf28e34d69d8970,-0x2644161280bafa60ba2f8fe67820,-0x2a5cbdc49b1f53f3000bbf5ba22,-0x269dd8e1bd3af60775381e094f,-0x1cf330a4c0f39837fdff86d36,-0x11c2e3dd4971cba653973774,-0x8d6186c537653bf8bace54,-0x3833b9da8abda8b733c7a,-0x1172f0ba00cddec814bc,-0x41509d94221132df34,-0xad8ce6e1cbfd058a,-0x124613f473872bf,-0xeb6717a7317e]
def m12 : List ℤ := raw_ints% [0x0,-0x11ae05e219400afd3463fa3c64593cceaeb000000000,0x1d61996a27b2ea6e63d70c7d35e44212f6c3bfebb0000,-0x179493964348a6200142d0d68960fa4a8c7cc3c2ed4000,0xc2c1743065255395dcdd08e7d6addfacead76cd0a70000,-0x48a8703c88a8a37f399ed5fbf3efd18e89aac519b359000,0x14dec77b2839205be5c68c2a30c12972e8d9bbf82f154000,-0x4cd24b73e78ae0e9122c42e616f6af23c243385b9a195000,0xe89cfea20c050398b8600e63365ec6245a546621905b0000,-0x24e8f3becad1d240198408f32c93ff599cdbea552f5164400,0x4faed9f072fc14808d2fbee844afa11b6d2eb6a1da3a15000,-0x93d7718bce83619da9e91d6b097513b31440674eeac6e8400,0xeda98c56ad1cc39206d31768a82a2bdf9e828bd0d0934c000,-0x14d1509d6f5ea1e867dc1344e2abddad4d42beb8ea8ee0bc00,0x198e48c14035859d46c84e6ea2820546de0863d1541dbb3000,-0x1b933c038e35b28bde46709b6ee12540d3085ffa44ed249c00,0x1a37443aaf1a3df5fcdc02086588423214c80bb3c2533b0000,-0x15fe23bccb127d92f40c6215f1ee147c5133e907c4ff0bfd00,0x104a7e3c0ee8aabce6b720c8c74c65ab65a19ebda4b062c400,-0xaa76c6cc7d2949ab22d007f71762ceda99fc839c72f640d00,0x625584825efc7e90fa9044bfd09a3c5ea76b9131ccf233000,-0x31f3b9d9160a3c2225978d6b394e6361ce6d3683c56ae0b00,0x164a1f04d4e6101daacbb76cdc674fd05819242700233fc00,-0x8b518e674c49ad2b6463c9636cb755b62dd5cee56083a300,0x2f711ccd17ba21e79432840c4601a4102e62e48563688000,-0xe01a7c6dda75c555d6e5456a78cf28acf0f202e9579e600,0x38fb18cba9eb0652bb9c9680a544da7adb9d927290bb800,-0xc60277f9da29c8217e587aec2610dcff46ae2be19de600,0x245e69397e786f1b393d73167d898d992ab9a342412000,-0x5947cf9fe5bbf045fdc8659017704d64fc5164c18d200,0xb45341f08955c379797482c55ad7db97e44e8e23e800,-0x1260a68350cc132fe601723de63cda541742522c4200,0x179f012ee93487d3315923b4bd91affe11e7b690000,-0x1734ef894ae40df627add87082c57eff2b7faec900,0x10bc824a73028f7dc600cac91589367262503f400,-0x8635972e4cd46b712f49fc2beef3d92ff36f900,0x2b491adf957e6e536627d1ae9a6ce85e587000,-0x804de18237f610780622a19e3418975be700,0xb658e4fe5d8cd34b5c655042b31608ec00,-0x59db0b05019f1cd1bcf2d56978f97f00,0x7499364fe25c2ca5cce8000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 21 58 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 58 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 49 indices rho q12 m12 12 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 49 indices rho q12 m12 12 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r13 : List ℤ := raw_ints% [0x2e035ed78b68ae1a9ee25a967e2ac00000,0x3cb1334b703f7ddbab1449fd8e3e5c0000,0x25c687714da6cb7c68db68d8b9cc000000,0xec15807be4e0201493893031d6dfe1000,0x40eb59b5f39ec6ca284ed2141cf420c00,0xd5cc4c71528f691006dc3e78c9c2ab00,0x222fcf8f32df437cdbf4115dfbcb1240,0x45991b77ad3cd1ddf3914abde6c2200,0x728ab1b649827764f4e245ded5ae70,0x99f153e9d424eebea34e90dcd1270,0xa9f1577e25c3ce1b5a454981131c,0x9a6d296296fe2392cc2d2b37508,0x735b204d07a0e127fb36d1360d,0x467c2d75e1af1527aa2f5eb60,0x22e74309144e1ddc44b07a84,0xdcce410a5cdb8c93de6cd0,0x441ff9f016666ba9487fe,0xfd21b2ede088339bef0,0x29abaf9ca904626658,0x4576b31a2e6ba468,0x3734f9a5a6a14d]
def m13 : List ℤ := raw_ints% [0x0,0x1ef08a4bac30133b1baef5e9af9c2a69b1b4000000000,-0x32f1dfd754709c7351459ba173af11f0f26467ddb90000,0x287fcb114416931ff40d1e283509f57f7afbf37b305c000,-0x14b38b4bf1e4b752340600e847356f4827821d6026db0000,0x7a525f833025d538b84234547792ab2e32e403c00beeb000,-0x22c4d70e0b142f6fc3d415e15bcebd37687dc2dfb3ed9c000,0x7e99729e625a8408267a78252e2e9899d847452a557269000,-0x17b0dd746bb66f015b81b326b5093e1afbca33d159c21d8000,0x3b731e87e07c522daaf80b836bd771d98fe780ac304cffec00,-0x7ecce779c83c15afd1b391d602f13c2943f86b8325f50bf000,0xe8536931cfb782584c0fea5187302483f3d4beb867a9e99400,-0x170a1218d441b3444ac93f3da25767f33e0385571a2c8dce000,0x1fda7e8020bfb95abd2be24cbdde88eb03e35f18dd45eb3c400,-0x268da0de2c83597133c71a1cdf5a8929a2c53816d80a3f5b000,0x28fd22ce0e55fc90cb47c533340f6069637c30e0ffa70a7bc00,-0x265ed9d46f4bb384eb696522c2ddd36ecb75281a232d95b0000,0x1fac2a80b7c2fd6e9cf954928016bd53b69df386cedd0962f00,-0x1710fdee3473e5302370bd9d6f9716361645d164e465f72ac00,0xed180da72df671b2aa5397e178ea1ed20ffa9f6238fc265100,-0x863a2ff4e3b477c6b4cb3207728cfafecf0dce92b7ab24f800,0x42d944524f4a75285a19058c98ba8510e44c69ac01fe054500,-0x1d361cc294d46213bdbf3aac6331d218964e0b772b9e073c00,0xb294016a231f74769144bac826b690676605df2660ba87b00,-0x3b64fc5088366c5cefefab28d1d87c106a404a3ad2940a000,0x1119b156b992b2ab876c9d175199f3dc6413454cbc4f89200,-0x43b95c623d21d49f58d02daae1b6cccd2a7c0a96a7460800,0xe4a86cc015a9c0145f57e2360ab9626babdb1c60c8a2e00,-0x28b6e120ddfec7b2097e45b01c9ceea22803ea90b5a3000,0x60a5b2d9e77b4cfec9772cd1f1a2d4670945cd4ac97e00,-0xbc347eda222e7eca2c14a79c2cc1adfbefcaaa75a4800,0x126e1c72cd44cd6784d0ac51edaa31243e9e2d99a4200,-0x16abe818b3d1ecac4034db24ecf1602ceba6ef9b2000,0x1537b6fbb5fd0c30aed05b9abb467ee0cf8e9f0c300,-0xe7ebe24d9e5cc0f62a5b6dd2174527d3d847a5c00,0x6d5fab94500ac684c4719e12a263304f9bb4bd00,-0x20ed021985e0b9374a2b1f40ef53a596d74b800,0x5a35d5e96529f0c65da640cba68c2b48f5900,-0x751e070a88e9cb37f92e4f49ee7e1d70c00,0x33fb2b08dee0e76f0142668604d1a6700,-0x3bb88e9aeaf5239e90dc0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 21 60 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 60 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 49 indices rho q13 m13 13 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 49 indices rho q13 m13 13 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r14 : List ℤ := raw_ints% [-0xaca833832aaa7be9a07ebaa798fca200000,-0xe380bb673ed92f9510412cbc5103d5a0000,-0x8d70d2c104f18209cb2b9317ff0ea5f0000,-0x372dd825977f86658edcbe4e2ede77d1800,-0xf27205ebdd7224a378566ba67bc2dd7600,-0x31d4177276c35bc79c7162aa402a4d8980,-0x7f46398985ad1ff1bc8ddf539f4fb33a0,-0x102a3c75a1d4c75fe401145e05203ea70,-0x1a8cf0ea1bdea22a9ee2c3b27d545670,-0x239abefe7145d7c62d3e1ef70458c60,-0x27353be90c1f99ef56589c80ac4a8a,-0x23879abbf316129e23a320d3c5b53,-0x1a754b7db7e03f789992178ba522,-0x101c210616a1df3aea44340c924,-0x7f21703ca2a63172618ab9bd4,-0x32097eff77bd22ebb6598f12,-0xf5b61a01066f523fbee224,-0x38b6e071643a6ff625624,-0x94508427fcc362deb02,-0xf52418767c32bbe03,-0xc0d8584699e874a]
def m14 : List ℤ := raw_ints% [0x0,-0x3624f2046d5421a770722e58f3514a38f6fb0000000000,0x585b3866b506bd7e688836193a83ba8c407f12462830000,-0x459775656e3d306c3240aa07a96bf540e6d1fa77899b4000,0x233ba080ab2eca721f3d23f9ea819e87cbc1c834303270000,-0xce2290368db4b56b54c8dff35c880e2f09f21449036411000,0x39fe9a3f18a459d3cb2476a012a85fe85c159f863a74734000,-0xd0f00c5b122301884db8e7890839b766b486f08e205eb75000,0x26abcbdc613d23132bc72ff190467267102e090564f970d0000,-0x5ff05b496757df9e787e95454101027ca2701207e73fbcea400,0xca371a0db98c1169d41805fb18a27df118743e57b2d4e66d000,-0x16df5c8641fc0c2edfe1840f7fd2e45aaf51c84442913da40400,0x23d41e3a42b1bc50f021cd3de0b41df07d60114c68ebf6274000,-0x30e0834c1e80fcae736d93e223ca450ac170f44a2af2573e1c00,0x3a563b12a7c27679a5e7632c0bbd588d0190eec97deb27f03000,-0x3d1fa43942b308dabe088ad46f958bbc82eb54fe2e5a4210dc00,0x385a0ed9379faf3f49b54c23250ef6ce90c509ffb50ff83b0000,-0x2dc6b4e46aa0246c00313f59d672e0ebffd6732732046c8b7500,0x20c834206ddd598f0f2023cdbd1892f82d774141f26ab4642400,-0x14b0dbb0ef9d437a173eb85770d0ecf9c386795607983d0c2d00,0xb7f60acd79409332065dead791b132afffee56f7704c1e2d000,-0x59d50041dfcebcf3e7c5cce57874e7098850ab76596f2470300,0x2671fe49ca54d9dcad98048d71fda53049d8d47f742efa2bc00,-0xe5e3aa1a3f14fba49fedb7a4dadc07989012ff764555be3300,0x4aaed1401de138a42c0ad4b69db877f56eb699c931c2170000,-0x14f812af8578dc4e5d00300c73845f7f04ac4a81a655e83600,0x50d7e227785ca566c7ea6e9efd85ab326910cedf1d4eb7800,-0x1092edd81ed1156d196b52c0b18e901e2979851bafcb7e600,0x2dc5114fb6db3fca2cb810181eaf725deb39207f55ea6000,-0x690ada15c7848f8b175b5b48e89a6d2a1cf9e5d335de200,0xc52cd8c0d100ab3253ebd8c9aad40a28fa7bc9ae59e800,-0x128c36b1a1f60a4af324aa164559912a7b65078d816200,0x15d41ddb0956f131acde87190618f98ba1007f3178000,-0x137399a73a2e53b8fafb79286883521603790fa9a100,0xc94e02c20585ce0385314face4c975a236de025400,-0x59474a7cbe66fa0648fa8e937b8f7677c12fdd900,0x191222c1e3bdabe86276122dcc8da93c3e6e1000,-0x3f741690119e4809ca24b11ba39d2ffde3ff00,0x4b37c22db42d542e4c22bb98ea5af9642c00,-0x1e0fc5c59d10143a7845972b1cc9030f00,0x1e94707f36b480f20b8a00000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 21 62 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 62 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 49 indices rho q14 m14 14 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 49 indices rho q14 m14 14 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r15 : List ℤ := raw_ints% [0x25b1d20b5b607a5607db478aeb1bde2400000,0x319f3b874aaa4428912fb18191f8a77740000,0x1ed1a3d1a6964ae9007771c495c3b2aec0000,0xc027a94f78e7f6bc648919e3eb6b263db000,0x34b41b6b85d49064143fb0e0df5066be9400,0xad13ee6de77b809be788cd3cc7bd97d9d00,0x1b96f1beb66acb4e412b6630397f5e0f9c0,0x37f9b78f030b8ff8e701013e433b74a2c0,0x5bc637fdc43e51592480438b8a3794770,0x7ad3d200f18f47b11c5bf9a94a510a30,0x86f68233b698d5727bf39968f00e0f4,0x7a010777ba39fbfd05295b6e4473e4,0x5a9b50f261ce1f08af26b819b2161,0x370016a2cde7cf6969d397f4cdb0,0x1b08a21b44d70ef28bd51563804,0xa993dddfc8eb50d140aeb12f8,0x33d030c3761dec59e194a596,0xbe5e62419630965549e700,0x1eedfe0a21eb189d565a0,0x32c412e14d8904dea84,0x279b59e1c30e80541]
def m15 : List ℤ := raw_ints% [0x0,0x5ec0a787bf533ae504c7d11ba9ce41e3b03740000000000,-0x994748d928ea9d5dfb52aa5def83d04691e44c1663d10000,0x77a4048ea48f22097a7c7c70fb0d6060bf8850502935fc000,-0x3c023e4446476c09596ee76e8e4b6749ad27c1ad6d667b0000,0x15bb64dd134628945db7e9daa7a49f408479fa187885edd3000,-0x60d9fd35e5a6404dec17ffaf4f54e7088ad25104c508743c000,0x159530ba1ea8845382b4c12e4b6d11c1aad244edaa84baee9000,-0x3f3aac358398b9ef20d56db8d68c37762b7447332e47465b8000,0x9b1e80d161707847349434a78584ce300d957bf62aa39f260c00,-0x1432b629739378df7d7ec7850c31e6bc54f770d0398bf38287000,0x241d0a14d0bb6c9eee2d98610084b6ead054a559c12167a479400,-0x37dc2d325a6feaa481061c97c90b209595ba74bfc942611566000,0x4b34d64abd406d363a1a20b350f6f4a54d25743666326af45e400,-0x5888f789cd8d81045289a642e4913b599cee369e0cff69eb2b000,0x5b701f7082e649b485fc44a13bb613783db6914e1a713522dfc00,-0x53097ac82f6f0c85facd0c67a77c20edc30cfcc4c87b2516b0000,0x4264c02f38457fae1bd67375badda133de62d657e41b76d5fd700,-0x2ec3095df81159c261579e02346359839771caf63ad06195bcc00,0x1d005c2ac8a1cb4a05c09b41afd5cebab98f435a9224a9a839100,-0xfd1f5cbaece608fbbda4da0399cd64bfbf72de038cead2085800,0x7935b90371cafca29fc4a9e476301977598eedd0fa74fd9fad00,-0x32cf2729597a74b928f6fb1209ea034082e9f2b0dc26bed2fc00,0x12932d129df98938f8e1e73d716bccfe26734d559e3b84be0b00,-0x5e4ef8ac7dcf0d8839e05ab61beeebadb5dedf1e18589662000,0x19d2bcc275c30312cd36130098718d1d11b69ff1bed18fe0200,-0x60ea434c00b882c752facb60337ca819711db70004970d4800,0x134d4f13659e2f6d972d898ec067a0c22d1491e749724f6e00,-0x33a9a4bb3e471cec81b9e983b65c7706408f50698cf4ef000,0x729ce3f7b7e1acd595eb1d89ae914a77a36e0862d2d0ae00,-0xcf5536ac9004bafa87b4905e2747bec3b9c8ab4aa3f4800,0x12baaf38a2f35bcf6ef9dc5e74b81456dda37aba591e200,-0x15149959eda594bf3358a96966c7a76a0dcc4b96c0a000,0x11e0e730d5445f3318e078e99ed32b274ce3b54a48b00,-0xaf1790656c9fa03dbe6522874f5c298c0ef29587c00,0x48fc39518958d0f47be5dce6485b21d6db4c4bbd00,-0x131b7a72bb57f9047eb7f06d4231bc206d6ea1800,0x2ca624b24b7a7c2ea0795c0eb3f6a0b77542100,-0x304dea7f81451d7cccab872e3603c433c4c00,0x11613bc2098eb3168a88566eff981bd7700,-0xfa764949e226c48de47000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 21 64 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 64 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 49 indices rho q15 m15 15 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 49 indices rho q15 m15 15 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r16 : List ℤ := raw_ints% [-0x7bde556bc4efa3189e2064c507b97faaa00000,-0xa2ec6cd2eb0f6fbc1b32b6297d02ad83c20000,-0x6517d712269825f5638b1f924a08b3c3730000,-0x275ac01157893dc1a0700911ae9b5750af7800,-0xac8334857864d12f831d69737a56da4066e00,-0x235d7ad12f3e83ca363825c10b84fa028f780,-0x5a1434924a2bda80e5e33d794c134f685420,-0xb67dd0f2558f6c129ac257493cb7c8ea9b0,-0x12ab975f13492a48bdf7be620654eacfb70,-0x18f18fabd46fa430ef59f5e6eaf14f4aa0,-0x1b5acd68e6a0a51f62c1c2d665cd6ac32,-0x18acbf42cbf544d06595949fe41d1177,-0x1247e5c72950fa8bcc978f76471886e,-0xb1131cffd624a0b4f02695dc6e854,-0x56c62bf9c4c4fce283235f01d154,-0x21e79a139950b2c95e7bc820e6a,-0xa51d08736417c1a1d999602cc,-0x25bfe48db00c15fb37975c94,-0x61a38c3f7e89d7568c423a,-0x9f532bc9cd8f4bef1767,-0x7b74fd60c7a649d776]
def m16 : List ℤ := raw_ints% [0x0,-0xa5d1252d8ed1a710c85dadf06928f34e7460b00000000000,0x109f7a7db2e0e9559c339e9e06688190c67098395c870b0000,-0xcdc8489a5cfc71daeda2fd4e7cc62647d85323c1bd2b194000,0x6647b2f3235f413a8e03cbf76138f03a33b806604eafd270000,-0x24b159aa30971614cf0fe7590e7c743cc8cdf9f08d8157609000,0xa1ef483d6d672ab2706bd3126980b14c0ccffe54283262614000,-0x23b8c2fbe4d32865eba96417c4d3c283744275a37cfc34dbd5000,0x678d9586293d1c1d68b19cfe802fb360cfa323977fa0d9bcf0000,-0xfb4638240f1d097ef10b476d43710fd031b66501177f635e80400,0x2058d988002a589d0fbd9bdcf4975a1cc594b5d558c6194e005000,-0x3926bcf3b8f9c67af7f2ac1366dd67ccb5229d253db762b6ab8400,0x574f8b83f8765d1e9ec205d0e00fcd89e1cc24a18df766f1cdc000,-0x7408efdc0f7879aeedaef16a5d903511d5407699d863e23fd87c00,0x86c2440dbdc3648cec58bb651e25348e3eb5d2ae1bfb5a89e53000,-0x8936aa618870979bcef91fca4b86d0420589398300d33427d91c00,0x7ac34dd456f00d7b933e8f9c08df7c1033df4de851c8fb42bb0000,-0x60a1961bf7eb0e89958d7168ae319450739dfd2fc098daf2b82d00,0x42f20b5d0daf9b1913e29b8f7bc445298ffc8ae8d963c08c128400,-0x28cda8dcd810a06da509ba96f8e5eaad36f76adc6cb250b580cd00,0x15da51047d00c0a26a3a8447b0473138530b605277a3743ce77000,-0xa434317b217780a3c24ee7bbfca414a379aab0d158a93ea563b00,0x436cb1ad0d275d069ceab6b6d37d1a8eb5efff558ce71b7c57c00,-0x181d08d7ae8d9d4fe6ff80746eac556062c824c42af2c9b2dc300,0x779767fd87a4a1bee2b8350b059940ae2b1901fafae4bb398000,-0x1fef470e598bef72d71d33a7995456440ed2a4c474f31d260600,0x74aa9607e8454fe6af1daeb93ea8a716b77e056d81cc3a53800,-0x169233e0349e69ac8204f6b3d8540827df09ba0fa4aabbae600,0x3a8bc0be50f5c4d8fa2bb04950eac98936d4bcf742b7cda000,-0x7d87ba9520f0962d55b273a2285ce436a992d4c57108a7200,0xdaca69c1e25be8927edf18d3b91a95c2bda9bf7ebcb3e800,-0x12f969c4185fcb895dc5fbd442c9d7d32a200cecacda8200,0x146abc434d8f09cf2527387fac2c9c52eb52e068d7a0000,-0x10791b3ed7c670560ba1e00fb2cda4eaf49a7e0d36b900,0x98970b234e1de0569453ca433690165aa09773adb400,-0x3bbfc194f88f37a50be073bffa758b38c5090393900,0xe930fc51925a0fe3685ac9595ee853b393918b000,-0x1f6d437a45e727342eef367411b5383538cd5700,0x1f047ee702175d37cc5ce6e245037de2cf6c00,-0xa0b7dbd57300c7c4ad9f2d86d3971439f00,0x802d452e18ae62b96de8000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 21 66 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 66 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 49 indices rho q16 m16 16 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 49 indices rho q16 m16 16 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r17 : List ℤ := raw_ints% [0x1821b16798cc7e171f3c8167a64b03e2d5c00000,0x1fb71cf49dbf886245a6b1752772a7cc714c0000,0x13a9918e0c128d1c42cb2de9b3571cc403380000,0x7a5b2a8873bed52381beb7a2da5909a5a1a5000,0x217d00e90c9367d87da75739ef3fae0a40f5c00,0x6db88b5fed3b58c348dc2e629f7b7707f81f00,0x1172287b8fc11235b2c5d72bcfceb364891d40,0x234c1c78608b2ee0f3837c8d130f8fcb48980,0x39b215a2103b9d38d978476711351c9b6870,0x4cf5a90bdbf1a3e720fd316a86744060ff0,0x544061e39ad26b93191a84cb9fba862d8c,0x4bd9e5e16d636ccae575915335263dfa0,0x38137de247b62abcc8a230558bc0eb55,0x21de2cb1f45466b9bf63f8872859280,0x108d85c00ce30566c1dfcc56771184,0x672cbbe4bb586e53435f90f29660,0x1f4c7141137d7ce4fe0a42447ee,0x720f3b871311e3dda09b9df90,0x125be82c43c835b29d97bf28,0x1dcf567e953103ee202f80,0x16f79257193c3d190cd5]
def m17 : List ℤ := raw_ints% [0x0,0x1222e010fb9eee45d5ea3f064b807a9c94ba93400000000000,-0x1cd9ccde0217d48ab04e6f4d5f922930a3b5a83a0c23e290000,0x1621cb380ad146a9e9a4573b25c717b3f874d8daaf19cba9c000,-0xae734dcfa12674ab180e42afcd9c31faea21a81ead40cd9b0000,0x3e02bb4e072d3bea0d732a435b067693cf4f217f2a288de67b000,-0x10f116f64f83d90a1789777285676c0056e4d351bb7b50109dc000,0x3b34974799dc466cfe21301367333f0e610bec49486d1e67ce9000,-0xa9de0f7d5369d1448338d7105653c9a79ad12b7f45183ddd498000,0x197c86b7f272425e5b0c6098ba7348cb01a815f80c03358fc472c00,-0x33e902ce2abe0a506fb5df79e588d6dfde3b2c6619b7647cbd0f000,0x5aa68273cae0574a5f45dd07e7cc598cfb39cf7380f346579339400,-0x88cec5c201553153095f9b6a78ef6d8b8912098f177ce550b8be000,0xb3826fd795251ad5254101937b4aeb736d9724aec4a520851f70400,-0xcdb50911c07f7987fadfc6ab3688f57d7dccdb8f8411cfdeabfb000,0xce8994df81e7b87f358fb1e1574764599e5f61122fd2ef2c8903c00,-0xb61576d3581bcaeef13120dcf39b25bb9e87b2b922e4714927b0000,0x8d1edf6ed66974b541d67fe6cf7c7976f4c277b4df51b23f5ef3f00,-0x602eede5e874202e631c835910e5b2284bbe74e8728298f565fec00,0x399f0b608ede4bb885e623094fba9710ab23bea6b6b672528f45100,-0x1e4d3df4233a3d2adaf1c0f85ea0497deb3de4bbcb823f41762b800,0xdf5361865acc5da34767a241c57760816ca0e3e1a95a954e3ed500,-0x59d57e25c749c2a5542cf9976d0a718a8c31452367b4a72feebc00,0x1f6e6b9e71fc36ec64de3487b9eeebf85ae1ab3e60482965249b00,-0x9846f1a97fab35c7f95b7e95daee0abea4db55e550eb4ea07a000,0x27a7b932f056aaca5fb5a39c5262cc104dd3ecaf4e9c38415f200,-0x8d040d8e8b044d1b60a9b4b1443192f0cd8307bdd652ceda8800,0x1a7fdbbedf153b0c059645c08fb20d95f4f6b78997532f13ae00,-0x429a61fb01faac25fbf6f23751cbe99159743e28cb23041b000,0x89fea7bffada29960f3a571d725a3f52aa8f7be699af1a5e00,-0xe7ad9a174f19b05802efc117f946195734e7b7ceed3684800,0x134870e51db7b6a843380273599562b162f66351ecf218200,-0x13d442ab51da19e2154487a0f2d757e1a7fa2f5c8ba22000,0xf36ab16ab1f0fd846ed7e2642b7ca2a69725d1ca751300,-0x8539609a114003f72415c3be4ce34869701781e219c00,0x30fa0b21acaeed7f84119e3182873f5d16419d563d00,-0xb2011764b250904a77f47f70265a7cc33a11c67800,0x162032af22c77b11e1c2c446fc18995056da6a900,-0x13ea2f1e8a1e68d3daab104e11f0b794bf58c00,0x5cdc5f2e119b7db05de105c3003134ff8700,-0x419411cc28d1828fd09c0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 21 68 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 68 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 49 indices rho q17 m17 17 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 49 indices rho q17 m17 17 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r18 : List ℤ := raw_ints% [-0x47d413f5e89a1abb05f240abebaafe8490f200000,-0x5e555cb5b7887cd493dec2318e94565c4856a0000,-0x3a700fac8940ed8241abfe8b91d116cb189270000,-0x16b5739fc39021330ecfc8a2cfab28bccb354d800,-0x635a5372dd8f77f925da030e8ca6e2f4f64f2600,-0x145312876954f5493fa740b48b88b5a03b5dd580,-0x33a65bb2c9e2c17d67371b22b8847ae998af8a0,-0x68600acb7872df9e0093e1f8e0028d756222f0,-0xaa628503c56e9837e599894b4128d8b382870,-0xe2f30dbcee3fc7d11dc2ca3febb77b857ae0,-0xf8100b31176633d3c14eafce736a9cb531a,-0xdef1946cb298a629f543cb18dc046094bb,-0xa4819b1a3ed7391d8badbe9a3f428581a,-0x632560338baf7a21150a12c686edd104,-0x305803c674a57a009c1667bab28f2d4,-0x12c8b005d2dee5f64988f724a41082,-0x5ae79baaf8673857e6211ec58cb4,-0x14a303c74d3d1402ee5f139a684,-0x34f30613482227c44c766ab32,-0x559c5672465e904299677eb,-0x41a37960611ee48dcc302]
def m18 : List ℤ := raw_ints% [0x0,-0x1fbd081db85620fa3659ee4b0420d692044681b000000000000,0x3215ba7ff2f1b98becc52e2f4d99cef7a8bbf0be247c8e530000,-0x261a3a8a3d2e49661f81835e2eb4c2e1066e45345bb9afae74000,0x129c000eea8a8a355681528bb776aa27a3837e89dc6b83b5a70000,-0x68e4d344c824e12b9cc799459e7d92f827698ba41b9f6c49741000,0x1c644cd2042b29faa43e654d75d4c33b78a008720efed80eb1f4000,-0x6242fb1a93221c49dd3de86987995e9d6b36422302523592c6b5000,0x1171779c2d5db3c3f1ac076aa00473e6032c695967f29f00caa10000,-0x296f8a22f30071d595d38388a4737518e01dff44bd75f6b7a13a6400,0x53793870a921961d2055ddacf51c36fc50d9c3587d4d5baf1cbdd000,-0x901b3f93279b523a266b119bcfffdd8601ddcd462a1b484b5a950400,0xd6e36d9561387dd1f3e497790bd362ff2c787098a43b333dc7284000,-0x11670cdbd6333fbd8e217a41e95e6d47e1957e4b66b8998c412a7dc00,0x13ae63c1f505e13f3028ef4c6239da4c5335e2b42fc52dfd6d54a3000,-0x137d33dbc6f4adce5e87b37bb58de1f6e3b5ead7b66ddeaa0b4bd5c00,0x10eeef37657787047633c9fe468030c371b55383d5fcc107be3bb0000,-0xcec94fb56d1bb4542b77dcb1a59437e7921442f05fd0beca45c02500,0x8aad2db5018122d9a300921d0686b6bd640a19cc068a752d0771e400,-0x51ab1dba6a069dbf8bdde6cf633a195e7c857f2233ffdd9db6e5ed00,0x2a2d0a80ca62b14f90a6b145ce0e5044b20d8cd56f54912ea1711000,-0x130e9a4e33799c0b345f84cc369931f8b4fd00a08edfbf4dd8c1b300,0x782a50cd2f75b9be1c01b3b0b82eedaa1fc345b9fb3924daf383c00,-0x292273768ebcc497c8678159e0cbaffc0076e2b18125f579b125300,0xc2ae0a9c424a24c1c855fcda9fad70845c8625c6076621cf100000,-0x3170dc8f4e5bae9699402d4d84553c314d4c9f67eee80849475600,0xab20ad5de15a057bfbc32676bbc8bcf3921dc6162a0786070f800,-0x1f3ba5431837d3d6a2e9deaf2a462b112950e255bf1e6bb0ee600,0x4c0e06b0bd48d89966a294dfc0d21976a26647a2bb712aaae000,-0x983d9c8961781796ff091bbaa71e70171475c06e72617b28200,0xf624c64202fe72b2c54a4e14e7d557eebd484e85e3bed9e800,-0x13a7f3cd33e792e24689268cc0cf24b5da43ca5832a847a200,0x134f356a8aa66b1d66a9963b59ed4c65147cdbe02ee508000,-0xe14dc68a9a3fe4256dd65a6b28783778a0c09bb6bbc1100,0x74844c84f5c3503a0724b63484ad1a1cc809e8e23a1400,-0x2831d9d130cc22b8bcd004345d28e87363c546d6d1900,0x87f82657c521fef5224fbdc9823431b82735f585000,-0xf94a51a049ea45b80a07e48b33247c44d95c5ef00,0xcc8d1c6a2b1b43ec7d1cde000360dee2856ac00,-0x35a33496899d117b2ed870af6b52c884b2f00,0x218aeff8e6fc525e630a00000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 21 70 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 70 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 49 indices rho q18 m18 18 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 49 indices rho q18 m18 18 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r19 : List ℤ := raw_ints% [0xcd480ef50d723b5dd1880c23d76d6b5a53a5400000,0x10d6bafdc43828bac0d200f23aecebbb6e8ede40000,0xa6c7e5d066f779645b30f65df3a1a93aaf0be40000,0x40c29b2b7ad293d9cdd40d1bf8137fa2356f0bf000,0x11b175c66f2a673f9806e7917a777a1ebace126400,0x39dbc13a41a84d9e792fcc930f2b85e6f0a59b100,0x92e2df925a240f15c6c9605e0f23dead55819cc0,0x12881fd8019fffea86c63696aa6ac52aabb88640,0x1e373d54edd4670b7bad57d611fbb4be8c4b170,0x2831d3e4b13b1073fda49085758f0de11383b0,0x2bdf2039389a49bd613610f13f18a235652e4,0x275e21d60ce531f98016ef21c2841da7cf3c,0x1cffbe20b6b460e92d12c1de7861e893ce9,0x1171c0d7a4c915ce03a324f1f16a858dd0,0x87cf69152819dc753eaaff7a43674f04,0x34a587285ec7cb4ab2b9390516d2108,0xfe1ff6163be44b60f20a3f2235d06,0x398609353b8ec5955ed616bf7ca0,0x931cf1ade1654bc54f3f1cb8f0,0xecfc36ec5c0a37f516ed7a5c,0xb4f0ac609090d36c617909]
def m19 : List ℤ := raw_ints% [0x0,0x378ace340296b9b5df1d61034739777f877b62f4000000000000,-0x56f7801834f08e276d3e2e121c8515cfb09196c23192302c10000,0x41a07115d58ee5340c0062b6ee395857a5522a2f28ae597663c000,-0x1fc8a1e84f28b57625a0a5fb4933863f50c868d5e9ce59c263b0000,0xb19799d565d54de6221c83bd04caccf6cb24c49ead23239802e3000,-0x2fa2390d832d7faea4ddbe3615ad055f3281337a919590cfd8e7c000,0xa34d16234cc020e526eeb1ac010bcb6d0d1c8adefcd75c909e869000,-0x1cb4349283006e9198885cef4f1f59033e016bd2ffa4719c5da678000,0x437c5562a351936b21d2688563d102a9d7eff07523b5a144bcb2b4c00,-0x867ee1d26beb820f80113b4bb596a8b10bbaae65bb7d57e1a25857000,0xe596bec1ad7c6ab718df46a6f240e07728f7774b3ca70d9a4c71d9400,-0x15257df5eca8f2190645c9752c3dcdafac42e31f04b25a025d9edd6000,0x1b1048ad03150f9434eca2c7eb43f8a28440043b3b480449693b2f2400,-0x1e365e179a06a24145d85f7d77534e817fe1676dd0efe7c400cafcb000,0x1d82fbcd136cecd86bd8f04c406a5c9b67a2414a454789a5044d0e7c00,-0x194683f7caffa66a20a6bbf3cfaf6137afef3f158fc5907569768b0000,0x13002c8a84aa0818a34a547b7175cff90c48286b0f197a216d071e6700,-0xc8a28afd3b843521f5658bcbd5ebac8329d396e48b057fc04967f0c00,0x742ae58f219eedd3fbfee7a877967a9060638af0baad5a52238b49100,-0x3aebdfafd7aeefb417692cc1febfde33b90e4588459871617014c1800,0x1a1e4cfaed8c1b647d36c3d963e1646ce33dc5c6ab1be418b7074bd00,-0xa15cfd12c7cba79927047f8192726cf6f2f809f377d3877ba7d27c00,0x360bade17cc742d0e5ee73bf45bd6b5bbef20a37e3979b40093c2b00,-0xf9e07fb11168315e908ac3c98bec68981b84b36f8fedc2136052000,0x3de29842ec9009cccd5beb979e1d3730c0120bf42986818d69c6200,-0xd07afd2e49d319eec5acb375f2188e1ac32755e4c26a7ded8dc800,0x24f3d494dac8935853a3b5d1bae46373553193eaf5f43ab22eee00,-0x572ab867440a9efdd1ad7fa1a74dfd4a9cfce44cdfce6e8627000,0xa88ab59d23e6c293446a9732068141133a967d5048ac40628e00,-0x1065b57b191f51313e452c19f36bcec4469f29d2ca9018454800,0x141844b9f47adf7dc8bd7f1f5fd719e22eefc53a8364f792200,-0x12d9debd5fe6ae2a7c7daccd056f48af85405e2e35301fa000,0xd0fa37f1339961d001a46c7bd789f224b991127375645b00,-0x6611d51aa5fac257782a6876f0ad08a7a665223b5b5bc00,0x21061fb4879dd20ddee32d6e92b5dd537dd73753b03d00,-0x67ec62e7dc8df59952585a0eae35a5e6bab5e221d800,0xaf9327db8dc827919fa69c757ea56a59908a30f100,-0x834ae9e0e14934ec4c6df6950f86fceb61facc00,0x1ef8ee8761b219b2631599621af5909af09700,-0x11270341fef325f8e5d7000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 21 72 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 72 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 49 indices rho q19 m19 19 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 49 indices rho q19 m19 19 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r20 : List ℤ := raw_ints% [-0x235e1ae7b84f2896797cc6ba170a2cc1d02697a00000,-0x2e63bc9d09e7f946225bcda5ad5588a8e559a4520000,-0x1cb29fbf2193041b168e55e473fe8172b7d1e07b0000,-0xb229bfd3fd32f2830f675c9a0958fde4d8b9fe53800,-0x30a365137a75364119061f11fbafc98f2c1e35d9e00,-0x9eead9dd50dd8d92c820522b3b7b50bb18f959a380,-0x19313aab5e705957deb48c5675b93373197efcc120,-0x32cd97b0e4a5062ca7bdabbafca04efc966fba630,-0x52be7ccd9b19f9b589dfe9ce30257986467f5d70,-0x6df0cafda464669053912fdf7ecaaff76198d20,-0x77d7d37d7ca8e489a60046aacecce4ab0e4142,-0x6b636322dde3735be0a1b434784caa1bf761f,-0x4efb5cea3e3f617bc82452f92576bee34f26,-0x2f6e4acca576221dcbdced7ebcd80bd0f34,-0x17092dde64dde55db8dcd7fc0afd6cb054,-0x8e94cc6e458ea1843ca7d5405dc4bb5a,-0x2aea8b268b38e31f595fe874f5519dc,-0x9b08d58303892223536814fd46ff4,-0x18b5bb18a462b509a43301c18bea,-0x27ad6ed58278266d1854bd208f,-0x1e2f279a396ba038f0ff3cee]
def m20 : List ℤ := raw_ints% [0x0,-0x6132e8db0487c4fe467369c5bca4911f2d17ed2b0000000000000,0x970a9d915c8910b6504f71fa90df43c690a9734a06a6b14a5b0000,-0x711570548a9f712fd56f2c9731f8b06559d3154313fa5897c854000,0x365216c4ba08d18e3758c789668b03ec51e47a1a9b5682438ca70000,-0x12cf0be6384ea15fe5de72c1d1978250e1a5c098114cea21a5c5b9000,0x500118116f814fe30a3ce799493c5df70985b01c7625743ab192d4000,-0x10fbf7c60bb5decad6fe7314bcfbbd0cb54df582d247a721fb3f015000,0x2f4e795f6eb1311203e13ffbe4aeb5d366af685d7b4b13e29fcd030000,-0x6e1ad5853e0d68d771a9b274e2006395a2e128961ab86a5410eaddc400,0xd920d67abb3e662d6cc5fe624e6a46fcf3d88adedc21c78c609ebf5000,-0x16e91bfab8073ac9f7547cc4920f093c19efaf022b361593c9875308400,0x215fb8fd80575bcedbe16143f17d188b9fec376047c51ce728b5d16c000,-0x2a321b64eac9c912fa9a6a3ff1ab54ba506f17742d305de4bc59a243c00,0x2e818bb0346ef590fdbd03e04f3f49ea3d262097ef8f9fc7fa1a7df3000,-0x2cd1c1818f3a9b16306c03555037843198d24e583ff17ef2d3fdefd9c00,0x25d81c63b76bfbccd6bc970652d540bc5544b634d5bb29e98ca633b0000,-0x1c06776afb21a4fea5b758e46b49048203ff91ba210a2ef8bba68a15d00,0x12343b4dbecb14a0010715867d70081eb76a2e14957ce8b1b55638a4400,-0xa5d33c035b61a71aff7b9114855600666de2b69f84158c45f3e00f8d00,0x529dc86e341dca9471f7eb220e2db3deb6c2f8f6876cdf9d460377b000,-0x23ee334239bfda6ea9c027ecd704c98667150930c4b0a656355ccf6b00,0xd983bea5d326b0791803796ce89e5e61d84d1445b5c79d70a8f8afc00,-0x4748bde31628ee0900aa3c9fb87446b61f89b6f58fbfa2e0d456be300,0x141f8d301d3960fc5e30cd3f61d63c9b04767c95008643056447a8000,-0x4dc306bc0536837d63ff546946ba01dc760a1ebde964c9ca0a802600,0xfef4f4cddf2cdfe6acf5c4cb7352d4b40fa54e890ddba80861eb800,-0x2be1d0b795e3a81b7b19ed8be9470d4944144df0d3190934b7be600,0x64428b1385d59ad628a4d6cf37672f54fe8705857a79142cf22000,-0xbb3807fd232a91f672daaa0530ee9e8929a9bbde75122016a1200,0x11882ce5862eb6a91ed18f1c41b96350baed5da1537550f4be800,-0x1499d7ec1ee6dc2676e43c96186b09563970dfc588a0a098c200,0x1272c0bd45e863d5003475afa4de4004d5106a57a94b27b0000,-0xc2387645571e87cef48a2eaac97823f2e07477f1245efa900,0x598ca81294571f624c9bba46fe2eaac749acc971456f7400,-0x1b28f7b593d5dac30f0721bc7d8579359008a54e6cd7900,0x4f790a32790a6a7d71e0c59cfc15583335a5ca2a4f000,-0x7bac106b3316520cae71aa3a5bdb79a44ebbb9bc700,0x5441b72cdca87a52b1011f7fbf7f894ec43e9ec00,-0x11e11dbd8c0572d7c4ee022e5f5791ae3a9bf00,0x8c4d321d649ab80888e8000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 21 74 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 74 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 49 indices rho q20 m20 20 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 49 indices rho q20 m20 20 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r21 : List ℤ := raw_ints% [0x5e664e25409ae5a799296b7e53423fb55fd8e30c00000,0x7bbf8e2b8bc07924b15a7aa0cd14e6911f72fb33c0000,0x4c81bee3550612f3c130e9708b0eb1ad6ce77e7f00000,0x1daa8cc76b5f86d40f7eec93b716c77e5d499d8fa9000,0x817d056250e19934813ece774a59c7c116e92e49ac00,0x1a6c0c05e7ca793524aff67c6b0b0eb79e5759c6d300,0x42f5d518460ca9d210abd1c675823b7ea94e9e65840,0x86e8d9d4eccda38176fa9bc2680e40ec59c2b64900,0xdb831bb38ca7c5e69c35961d98e91edfa853b6270,0x12358e1800b7d37568d52c7bff60cfeec34c91570,0x13d3747ad89baf88a2383b62cbfc493f754d66fc,0x11be267b82df8c459cd1051e394facc4e0b91b8,0xd07fa27ac990776554cc19fab3a47df77db1d,0x7d04538a69d6edb0737522a370e948fc93a0,0x3c9d673a435bd156d34bc4d1bac2a3d3084,0x1767b0eb8bea3e7ac23bde4b44b71eecf0,0x707c3c9a27280e98403badff6352cade,0x1956d8f2612c390fa30f2abf0598230,0x40746bd9195fd2eddf95d2267a4f8,0x67344d2629a350a841f0bddca18,0x4e431a43650c426fb8422d6dd]
def m21 : List ℤ := raw_ints% [0x0,0xaa19177f47ed98bcfb49f91a0a1ffdf68ee9df0b40000000000000,-0x10661975c31c0c5a6457577bfd5c674913bd88b18fc794b2d7990000,0xc2f160f3eec99b0e4c3889b8d5e7c1d588692a86a5ef2c24220dc000,-0x5ce5ec0d0f0181d8d563f26b3b9f54ec5104fd944fa972481445b0000,0x1fe66f1f9555a0094660ccbdd58194f674a4d8df6e0e706851c8d0b000,-0x8684a5736031b276e9e0c87a237bc93ec0dd5b315d26b265fa48a1c000,0x1c4cc6a8200b4a1d3c0972b708a1f08ef462ee3b224041cdd48e3d69000,-0x4e1527ff5b706551bf82c1403de524fdc149e2e9e222d713af564358000,0xb3f286440085ce2e3e624adecf2baae203c7054bc6c4b39a699e55a6c00,-0x15f340f5ade4d8b8a1301a1395490c15f320a58952312cb9e343f2e5f000,0x24a85613fe28d63a58ffc3220d192ae1ad0b3a73778efae07fe569759400,-0x34cb4691a9a58c087d7bee5a0e591aaa2e2523806b9534b7f459586ae000,0x41f44c2dcfc436dea984173fdb158deecca96430e88529a5e1cfdf964400,-0x47c7cc61bcd61eb1984797a8bc8987ff40a5c769d8538399461917e9b000,0x444368b3770a064515699565121f88d23f7926a5e37c44816c8844e8bc00,-0x38d5f9000ea29a5b0d32f4a35bcf0ad218722e9647d709d5f1f0a59b0000,0x2978032683788426eb74728e5801f54c7d333c5ff3613ce671911db74f00,-0x1a840349c6938d683279dbb4f6d61d976089d60eba726e2da2c848612c00,0xed88cbd26857d42e0d663e04ca8221c749e98c43947fe0e7d1350405100,-0x7441c0bd585b9e2dac6c2149f2b08bad66900a60e6f0455a12d36cc7800,0x319c77a35573fcf9c5aeda5bd92dc799bc80c7a1e9d40ca075f25236500,-0x1264ef10f91934f508f45dd1901354d325a26e2f2ba09819c2f4abe3c00,0x5e60fbafa96f2efd7ce2bdd3450d60585d8aa950bc2fee6257ea64bb00,-0x1a073bf6bd4766de8a72530d8408ba3e6dd08d7b4766ebd7f9ad7ea000,0x621530b2eacf39ce9df1dadbe900d3a7a6fc2acc3e624b9b0f10d5200,-0x138f5b905ba2d0e657e70e70f366e56bcaec1fed7a32411797ff70800,0x344cf7dc35c42ebe382a24ac6379b736fe553a260d1962924e792e00,-0x73b8ad2be115e5fa8633b5b4b7df7f2235454f07145019bfa413000,0xd0a5c3e841f29632501fad2878c3a091ffa8f205441cb2f4453e00,-0x12cd3868e0035af56d5e03973c64295b7902229ee0b1e48d364800,0x152d431982cb16c023ada58c908ebf9f625077bac481865c8c200,-0x12188d6017b329a054a507315fd970792766ea14272ca4592000,0xb4d8adf3b63bed4c16b7a11f828c26e6456f8dda953fa46300,-0x4ead2a0bf373ce58fec1e124f7805fda9465178ff943cdc00,0x165bb66adad53e034d8b3c51396538cbad10e2c8a875bd00,-0x3ccdc0953c7f9190cc1d649a6a7512fa7bbe62ce843800,0x571ec128c19fdcf25e2d94e08f6b03a88bade02cf900,-0x360fc81364392d691737d479a03b785cfcd86c0c00,0xa51728018c290c4bd1cd7fd11d699630ea0a700,-0x47b58405f17af11ecd5c0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 21 76 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 76 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 49 indices rho q21 m21 21 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 49 indices rho q21 m21 21 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r22 : List ℤ := raw_ints% [-0xf4c2d23e64ea1ef504c0da31b5d5a23e56318a64200000,-0x140b02450311f9e35def7129ac8a2db721763b79a7a0000,-0xc626c50f7070ceeeb7b6e2b13e28f7b265e9b77e6f0000,-0x4cc9b3b4f3a5966224c60da813da3221cb41af4e789800,-0x14ef1ecbf3c2166f001f64d4e6903913164303fa4fd600,-0x444be3698e3b6d9ea838d8a9127d166d374b38b0fe180,-0xacf24c5bb6014dedbae114c2ed460f6c6a455ebfcda0,-0x15c2798c9fa115978d05cec78a0555e440e3d9180370,-0x235f7f167d17dae0d895479efa65e74cda093515a70,-0x2ee70356db7f15a01b925d0b1950e3faa19a841160,-0x3303118cfe02bc1c41ff98f5984c313e3012540aa,-0x2d9936375a8a20877a41ade3e8ac59f2f436cea3,-0x21727080f04f5b46e6ad44ddd19b7eddab5c892,-0x1406edd84800e22015c58ae92e9cbffe4d4ee4,-0x9b2037e7de9c110b3a8f2fb4095eabcd69d4,-0x3bcc44c85a188d541ffbdc323768f92e4f2,-0x11edc3e714a5ed012e17ea50eb2d006444,-0x407d1429e82fb9f8a04ea41d6f6f74e4,-0xa3aaee1f0dd08acbb1b54766f69262,-0x10567bd8af85d7fbc36a870d5da53,-0xc5ac7a15990c970b420f93783a]
def m22 : List ℤ := raw_ints% [0x0,-0x129abe91ebddfcb4ab7c173ed91b7fc6f7a194653b00000000000000,0x1c7e41efba5c1e21129992f0b7b06dc8cda83f5af483caedcbd230000,-0x15033584e487b5f5e30eec02b8461e3782a68bf2a2e2bc347797734000,0x9ef93a2f24423280dede646b5616ba512747e2e1e22c19094d06270000,-0x362634b5624723f7690a12da9e0f44e7d378ea1410f1ff3642344f71000,0xe26aa4a54da5f0c79f7b21d0d74e7686a3bfed942b2d1128c75840b4000,-0x2f36e3554b843a88a1352c58c65ba3098af86eb9d0b11efc78577bbf5000,0x81123935408e95fe8b3b0db2919b86155423b4b627b9420dd5d616750000,-0x12696a6d4e3e8ac88a89ed665987d919d91c7f9250fcefd9bc943b02a2400,0x239244e578205e0817fda6b1f311ac4502554a3aea116e7cc6cb33e64d000,-0x3ac6912e9bee91017ea5e8bcdee68ce5c1c7427433bbcc6e31b75f4ce0400,0x53b49c6222011963f86b23aa73ce67ac7bb7b0903d7c7fd5e9ef2faf94000,-0x675870f0c7832320f3bb04b2ad8be96b41c22f4b722b86ad0846b1f059c00,0x6f15d9471597ce644aaa9c2a475b620c4e0f227c9cfb8925ff4e3e9a43000,-0x6843deb0de23bc10dc54f55a42547fd750eff4cb763229faa21a108d9dc00,0x559d5172b177866bd2f28d763de6802689d04c290fc114e5ee69a253b0000,-0x3d8e1064b96b91666bcde1b813825f4242e51b27e25b54c3b1f198ca9d500,0x26bff26e64588e36828c85b7d51d89be0cc55ca58c1021731e6b48133a400,-0x1556b9eca0cda94f7e5f3145d6c06897680437e415ba473f31eb15171ad00,0xa42cb09515ed4b0b3c58821e73cdf16bfb3f387250038b643d748c135000,-0x44bfe80e892671196b73ce1a2fae2c80677f8abf69de8c24929a5d156300,0x18fafc17131d5e9fd0334704dbb6303e1c6cbadbe673aa39c467a39dbc00,-0x7d6c3c4882839da4bfd0eff3239eb6efcd618fb8a2004a52b8308ba7300,0x21cacd75637464ab068082e397d6e5c7691ba90e5a99c3898ce75d90000,-0x7c2cabd0d5b1b5d41f1b6f2561b06f173676ec42c0e3db90fd1be47600,0x181904423cc2a4a93922afb7891348f755e6adb7bf2aef21091f5e7800,-0x3e8e3411a4dda8df1bc44b3686216069362ea1f7a6adaf6628809e600,0x86052ac0c0a8423bfea8faab2df4aaa394f9930ad5821ed8b4536000,-0xe944be70eca178594619f14320f69557a3be428a3d4aa2c31a52200,0x1438d9c94a7e0991813c11a0699d1c01f2b83ec519b55963be9e800,-0x15d33d4cc937f48f2217b101b9a8e2cf2db71af908621d861de200,0x11ca1fb9cdadf8a6f09d51d453027a7b9bb91a797c7d6f4598000,-0xa8b195ded29fe333c88fe874e914fcc3d62302e2d247b178100,0x45371419e295f14668c72f27d02267bd24df3a0f782925d400,-0x126bd265b52ea9aaedadb002e8f3f63b14220326e0b2e5900,0x2e8a271f405ae95286de513831d7c64fc86b58d4c969000,-0x3d5fe23c3123bed946060c7fa8d28fa290029ed2cdf00,0x22ae500ef94d3c77409aa7625580140676e99892c00,-0x5f3ef42fd7d70a01953cd250386581b5a7ef4f00,0x24a466f6dcaaab99990a00000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 21 78 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 78 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 49 indices rho q22 m22 22 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 49 indices rho q22 m22 22 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r23 : List ℤ := raw_ints% [0x26a37124a495a71fed8e7291c8c99a8837f9a6f858400000,0x32998706ba18f07b322be1504227dd8403e9f90d87540000,0x1f3fb31566bd42f340d84fbc456c20bf1efcccb3a25c0000,0xc1a4a98a203aac3298008a0fc47c00ffbf5e91889ce3000,0x34c24ce5b1bf937713f36cbe21e5bbf9e5d96f7da173400,0xac027dcacc52c9525d3867d9f4e84962f461702fcc0500,0x1b3444ace273c85c4428420b8cfbe8fce52e4542d52fc0,0x36b8c0b2849d3049560302cb45e3bd80e1315edb701c0,0x58e1de3848767014d9a956e45655f2af492589723b70,0x75bec61e37f9452061fc75abc1183b7f66e22553530,0x7fef9301610fa67ce3a78acf7d90c9c293622cdfd4,0x723c8f2491b7c769a396b4e7395358688c2716e14,0x53b23d6d77f18b839540efc2c8733be11ed482f1,0x320d1744dab4c53dc31c600020bf7e0bf7197f0,0x183261ecb0f7cd61f6fa58049823873766d604,0x9502fa8f1aecdf767569d4d7f6c69c3f0418,0x2c9a46a1fca7401a328b6070df5eb62c776,0xa02380ca6323d17924a7b808dacc11440,0x19599611294a47ff8b3d4e0f0d51d540,0x2865c29d1401e375ce8a1afeeb95b4,0x1e78eeb8eb9f174a68e28ee9ab51]
def m23 : List ℤ := raw_ints% [0x0,0x208ecd7f5cc47a3c2c1928adfbf01f9c315ac3b127400000000000000,-0x31847f784c6dd316bf9dfac14f39985e74a6a21c4beba67147f2b10000,0x2440e2ab70d252f6ecc99e6538af07ce5556db62c2a301bd1acf927c000,-0x110372ea6acf3c865116081efd6bf3645f674e73097fe986fcc403fb0000,0x5bfe19380c02017877f58c0059797f8b17221d3df0c2c2836e5583ef3000,-0x17d7e1e123aabf7faef52ace10bc3735ac316b82c3a1cc7ac4eb9ee4bc000,0x4ede6077a67efe37d9a25e3674f54ff7e1f86552106176475b5e8fe7e9000,-0xd5aa46a4f080b9cb0c56b8e9c5047daeb62cf023418ba5da758f8d9338000,0x1e3102e39de5ad41b9f0621115fc18d879d216caa0537ec3a1761bf71c8c00,-0x39c086e84fd81af2124b354821e73e9777cebd642d1459bc681245a5127000,0x5e6ec20f9ccfd85dde57dbfa8e8f307475867cffe948d925b4562e4c2b9400,-0x85039fec2d0d83d0f735ee6f0b0cc57c72b5fc4ec1ee1089e6b48ddb546000,0xa2543a77c07d24bd1097d4005e4cc5bba1c39c69efe5ae03caf926b7946400,-0xac5cc10a670f7d96cea9e208868b4cbcaa0781720e6d8b84ac51873486b000,0x9fb2d74dd26daccda83185a8e8d1bb7df6296249e417231e4b4256895efc00,-0x8158afc6edd85d4603562ec6bdb1948788d47f2db73a43db639fe1bfab0000,0x5ba77e26ce9e8b47bc9bff006f6b1c066cd4c1f97b1db3ae8decc058f3f700,-0x38d00cd7ed56bc35a694e008739ced9a930073050d120505a231a6ac0e4c00,0x1ec65db81895a323a3c0783d416adcaf8dfe6af67009030954782494b39100,-0xe8a67b99b8ede6ecdb27692b3f6d9d40466186daa07b352d73046846bd800,0x5f9c7fa7dd573849c5f0f6e710d4ea19879b92f8f188c9e0391f8495ccd00,-0x220c4d77ba859ccb02e0becd7a8ebe5bbb5436e6e665ff88804fc4011fc00,0xa74a3daaf310185b6a0869040b77bf399ebc0b3d4ad5e5df2478ae7e4b00,-0x2c088a0761e3157cb2d9f711779396482562d04cdec7064672e044942000,0x9dc7cb387af65b90ededca9efcdfdcc97f8a2e608facdc4ce5d7484c200,-0x1dcb5c06d05c02577b95a5653dc86dae6096cde4047e954d93264264800,0x4b148553c391d726ebd1c95a63aa7a9ee31290d6c212c617855d0a6e00,-0x9bb98df1106e262bbdaf700b11350272a961d393c6b851611d16df000,0x10599758a4782a3a075f8e0c3578b2870b23e1e8f215cf359ecfe6e00,-0x15cf9f1b684a2815f0943b1c11671f575e4bff9bc363c8507b5b4800,0x168c9f28fe1110a5acb138994049a2e8ba381f38afe58dca2c06200,-0x118676496c9cc3cca358ab186329dade3a01aa4f0cb3b4506ea000,0x9d9f71691fbc3ec93a98636640cda26574f60b149b1f49972b00,-0x3cf782f993b26fc2ee9b842f32b60d1d778889b96e135befc00,0xf3073f67622aa0f1672942c4011c6403808924b18a262bd00,-0x23a284af17fa852a741532c87b363ffcd529215ec4f59800,0x2b3cff8e6e6871ca3a5329cc178c5a8e94344f9b44c100,-0x163e5a584e78a6a57dbb2a15188260378d100c094c00,0x36ef492900688f63e7725905cdc06f2b4221fb700,-0x12b81db1827723905ca7000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 21 80 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 80 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 49 indices rho q23 m23 23 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 49 indices rho q23 m23 23 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r24 : List ℤ := raw_ints% [-0x5f4d0ab4c08ad08f073657fb59b307816a16f2eb194a00000,-0x7cbf18c808faae941dcefe63392a2418c16c3033b11e20000,-0x4d0078f557235ff5658df23fc074b70441e2f8003e0030000,-0x1dcea0e235eb91c4f5aa4ff152c6cdb99bbef02e58b66f800,-0x81dd0ef9ecf00df672fc2c9eaa4bfb37b836d86da153ce00,-0x1a7220b9008a3fb759e7264eda04679e0acdbb178ab80f80,-0x42e04cc53f19b01dbbfa844bda767f6dddee59e4f853e20,-0x866d242b40a2d0d3c78b4e29f46b070db89cf54e868ab0,-0xda2caab487a8220552f938d6a2d23029e53328fa7df70,-0x120c7dfbf2ad656b1948b2dc63382a150f1a6aed097a0,-0x1397d60aab095e085479f665b416732a2adf830e4b52,-0x117a578142f47b49240a93297db4a7abf1e7e11ff47,-0xccaa91ec07ec4f474e383f6cf68546e54dda3975e,-0x7a4012edf6ca8bc1305d9afac9037692467e9c14,-0x3b06b20c251256a4de8089642d30623d6283f54,-0x16b00044f1ffa0ced1fdd5ca1211172e38134a,-0x6c7d80f04a21d6ff3a42ccc992bca67635ec,-0x184df2d9b38a0295be2847633162383d154,-0x3d723d511953357bdbc4b57101c9d3c9a,-0x61b93a7befb2124a68f6c278e283637,-0x498cddff7e704ee10546c061b5fe6]
def m24 : List ℤ := raw_ints% [0x0,-0x38f9e79ee257d5e94d2c073078e43751565ed67604b000000000000000,0x56129b7594617ca487c18809a1e0f78fb1a7f228aae4d8df29698ab0000,-0x3e9309df4d3053c5cbab9b9fad57441961b75a6748e9c1aa88de47314000,0x1d268538c6730730916cf0e39efee350193807aa02ab323f4f4b596270000,-0x9c691f0999b40cc76282cc203c617efaaa0d894e9c8090a11517ff5269000,0x2836fc6b87e6cce074344c8f277fd5c8128963099c0deb1ece87cbfb394000,-0x83e7eaefb9e951d4a9fd22ac087525cc0177440452a0987cfdb21446e55000,0x16234b4d15d013da44c2c7be3afc60bb564acd658c0c091c137474146770000,-0x319689cf20e99f35224027ed345d9f021be7dc7cca0bb5e2e6cf0e020b78400,0x5def3c70a69ff4f5f4a6ee3d9e58a15ff158ba755a421a758194e9c7c0e5000,-0x98070d124d9f913f2258179cd735c27409e7aabaab8b142016cfe695d3d8400,0xd3d60916396ecff2473a18a3ae8aee2c7ebc6ae3bee036c85e661ac372fc000,-0xff96698063b010b4056b4c67fb1512733ddb640f34d944c5c2872008d43fc00,0x10c2125d031d54bd0818838adaa1a608e0fb605843051d0dc109514103993000,-0xf5468e52126fda150f75a7209da75c375dcc7cbfe59b89965a10d7170921c00,0xc3fc3252ebaaccdd47ba9601e4a352b623adc3ea1b501acae4a7cf95dbb0000,-0x88e3b17c519541d2af1fab03610bad13d1f692e7c23f69cd44abd4224f78d00,0x538fe00578fba5e86c65a99fbb52658304f8c5f6d4d8a35f16313c375c60400,-0x2c87f8d5de38559f1183b67a3a39d2a3855c57a3da1189376e1c165ebe04d00,0x14ad130f885e235e17167745b58b574f7396058b4dbc4b010596186b21bf000,-0x856f7f62f76b41cc5c9b1b12074ee986803795fbb00787a2def1975cb99b00,0x2e92b2fd2ec8384de683969136fdf73e0a3db1fb43adaf57ac97180a907c00,-0xdff00f702b56d1a001b0c6091ca26957d3988a1beb8db1337cd1018fe0300,0x3995d5368dd66488ae3a991ce650697f2640db72b3093029119e5988b8000,-0xc932a8a085e8220eb0bdb2cca0ca054fd923707292c08bd6f831ff684600,0x24f773ea773d11d36c7c611324f1e6c73ad89b81604db90c788410e03800,-0x5a6ac508699207d33700613d52e91be3506785b7e597e58a7efcb80e600,0xb586916158b4de500ea7317e6dc453139ac9ae0d104e42652fa1fea000,-0x1263fa63d05b864ccb0d5ce20e35a67ec99f347a47f96012ee0837b200,0x1796b578ba26e4e5389d81c14bee9768ba6c2817de06c05533d13e800,-0x175a63891acb86073892fcf01d60012fa502db29f22db7a1f7a70200,0x114cae242c8b35e2b1f045b21763c90fe42a0a2aeaef5ec014c0000,-0x93833c8af8d076258efea9fec96c73e2627ae15016af827899900,0x35c3617b0de98d75f949bda8cd8a2461331ef40248b33eb53400,-0xc8887828d7e22a07ebe28a14047c779463c8db9f30d2c3b900,0x1b4b350c4ee0d1e881b5e1fd01c60bb705fc153a3a4853000,-0x1e761264d042a10e45bbcb5c2a3b4aa3b390626fca73700,0xe4378edbda86be1984f5d1a5662b8dec27b6fb746c00,-0x1facf5d41137a1a02e99c8391d787c44a5d8abdf00,0x98f8fd1dc6212c931de8000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 21 82 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 82 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 49 indices rho q24 m24 24 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 49 indices rho q24 m24 24 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x498cddff7e704ee10546c061b5fe6,0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r25 : List ℤ := raw_ints% [0xe60660c0acbaa847ac1310505f751266a7849d6c3afbc00000,0x12cf818e63b9a53e19e8f05f3772192a92f1b6fa5a7a02c0000,0xb9b187ef261a268a4f885a13bd175df0f52b6d374a5e280000,0x47d891b222afdc61d7a88ffd657cd29f0460a5acfe21aed000,0x138da2e220ab24de4f65baf071b3ce0ad2bbbe5c85362cfc00,0x3fac836eb894931b409b0b3511bf70551573006573aa9c700,0xa0eb65cc1d9d86d5ebe6f06082848034bfab1ad019970340,0x1433f0fb4e728fbf7ac1e60f8e2c1b6cf0e8b75ffc7d6080,0x20c412f725f09a1971cbb0c201c6fe98226a5b0f62bfc70,0x2b56108e1089148db7197b7b6ff8819db4f2d88646d2f0,0x2f013de890fcb010c46d071a8be609cb94e2f0ccba36c,0x29e4757113a687cfaa6bcd7e355ac480b3e68e736350,0x1ea1458f34aee70703901bec151b6dddf34def59965,0x1246ba1ef7bebda78f7b245ede9f3ce30e60a22ec0,0x8d06b27dbfc2661ffe46ebcc81973d967339df84,0x36231538dd1216fe5120c42cdff68b5f984c080,0x10286316304e9db1470cc64a1c5b11df51b8ce,0x39d427c9c6fae94195fc0d148d0c5be476d0,0x91f5f9abadff9a0eee515f09e7298eebc8,0xe7b6daff2ecad021214b7931cfdf8c30,0xae0c54f50ffc22dd8d3b5976436365]
def m25 : List ℤ := raw_ints% [0x0,0x63b555560c19b658470d0c94d38f60ce5725f74e8834000000000000000,-0x95a4adf4ec5ac91664cabb1e3e7f3d07023539b03b3ec1f895e21a090000,0x6c0c38c2c00df05b4d403cdf14cfac19fc70c6e76dc487c055db18231c000,-0x31f9b992da5ec10107291e310c256d9ec8207bac555e4a2c0ac9a4011b0000,0x10a2641191fcdfa8d6b042de4133cf6271afa7fb792177c3db71fc2ec29b000,-0x43e5222ecc03d78a5a48d28b3150c9c9826942e0c91a10ba42904f3bc65c000,0xdcdfa0957a69da59297a543d4bdaaeab35b00ceace4f0cdceadfecc5f3e9000,-0x24c023fffcf54e3ce14efd9503cf9374d468f6a5fb28c42185a4e9dda3e18000,0x51936b45f6ba9a8ad6e1b135b7210742c748cfce83b87b2c85402564c979ac00,-0x990f28ca022bfefc806e0fcb283e48d4c14799d7dbd1805882ca2939222af000,0xf53c294f33878493773d4662c228f87c9879b2b8e8dbfc0c247ae04273af9400,-0x1521957c92ed4c96954c40d399c1059912313792d3168bd76b46f7baeb1b9e000,0x1935f014cc678601f2ee9457fb2404e2e62a76582e645e2eafef4d855cf518400,-0x1a229aac13e567be32f0b880c74d40b806caa982bf6ba99a4c8f5f47eadd3b000,0x179ba840b4b08f6d2bac6849f6fa3ccb4b43966f70c6d831b6a55351587b13c00,-0x129ce63b86f8ca7a7b701c0d638192098b72dae1c8370a96a8cd6a88144bb0000,0xcd10ed52a18c499482f732a2cf631190a6d778e477a12fecf1dd7e1548fe5f00,-0x7b4b01aa9a69ac85cca1d14a22200c619a0d4649cb13851b7616737bface6c00,0x40a5b180531287b71d89dd66b9b69b4461256a04047dc462d20a4db9724a5100,-0x1d7fe372e6b9ceee1488edcde1e3905260f4647e2372c19bfc9b557b32723800,0xbaddee381644394347392d0c10d233b59fef720fcbdec90ce8d54724c62f500,-0x3fedeca0517ea9304415a5faf28f6dddbd6348254103df31863df9946adbc00,0x12cd474afdf39a1d346ed43f74796c4ae653ad8e5ed5d3264b9c85c79e8db00,-0x4b9320e34bb48ed5a22cda19f36a76fc9ad0ad78d4a3f48191c9e35e65a000,0x101761cb1f95ed45ac0699d0621de30ddb5a134756e29ed6d748f56fbeb200,-0x2e05ba2009cdcb50362e061d5e7c5e51fc49ff84db27f6adaa1ab1cab8800,0x6d3efa6e4cd0f00d45f6f1fa4ad65d44235335e1232fad4c79f0b63aae00,-0xd443263d4c359060429761561ddec1f7223012e57bbc24236243cf8b000,0x14bee9167b5f4b610ba2c041694cbc863c2c21e95e3dcc54b0e2b6a1e00,-0x1993fe6aaefca0ad39715d7f369275d3dead30acf49ddc4dd141d44800,0x183da875cf615ccc47ba8fa896446668a883b6875dfe7096b6a900200,-0x111bfed9ff004df1c123dd43cda7535ffff04ae3289c9a82eb802000,0x8a41fa725cdf59da71d77a517d5c897bbf6a61765450d0e84eb300,-0x2f761c540023b564ae714c43a28a742619094fad46e8631841c00,0xa5935fc547459a231cf6a034b908ce642969882af6896533d00,-0x14e928f67daae45d1aaf403c87a58b3a147510ff73833df800,0x1575920c763cb61f01f7cbcac16e1d40a82286e3e3924900,-0x924fc7c8d609d8b2d4b0b4eae31c028ff206a60128c00,0x12425f3acf9668a14b1441fafe773913accae7dc700,-0x4e1ce54844f16f4b871c0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 21 84 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 84 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 49 indices rho q25 m25 25 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 49 indices rho q25 m25 25 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0xae0c54f50ffc22dd8d3b5976436365,-0x498cddff7e704ee10546c061b5fe6,0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r26 : List ℤ := raw_ints% [-0x22053c9ce552d68c961a82bf5893c749ab9011c3bf3a49200000,-0x2c7ed4aad39cc05c54643896aa4708543609cacbfbeb848a0000,-0x1b70fb869bedb022f6e1d7ee58547936af75a7bc28736a370000,-0xa9cc3e1398fcc306c421abab4832f3a713196191450ffc85800,-0x2e3048eb7805e36b0de9ea6c788721453925e0b30a98f878600,-0x96548cf1129f1a428aaa9312b8d4e89d778fb4ff8ba2a5ad80,-0x17bb457e129f90e56096f9fe8c8272945844e45ad6cb8f32a0,-0x2fa429a7625bd0afc00db59bc8771a33f89be1f2aeb290bf0,-0x4d372217d4a247226d32f37053f59c78e8f07c8cd4beac70,-0x660d4c4bac334c036a45dd28a9c9d692528412d7bf92fe0,-0x6e9b1107cf7d861d6ed3b18943361107969257506bab3a,-0x627e57738319698eeeb6d9147b6ed1a1491ba9ba1f10b,-0x47f30364b0aa8946c6d26d6355a4c5df847d027f268a,-0x2ae37f94b94e1fd5a5341435c203ef3378a3f4462c4,-0x14a97bf6ae81c8a50b044fcc5e7b486796103750d4,-0x7ec2ecf8a49de618712c9c2e3e3eba496f6dfc62,-0x25c928b2f058fd636cea6027495b9327f16a8d4,-0x870ce7071102e8fb773d12560e54ce35e8144,-0x1545c1676e3ae2d3fb805c78e923c5007892,-0x21b7035c9a73d8d336c600adde21a1cd3b,-0x19475a72aacf7b5a013e28e6cfa136f2]
def m26 : List ℤ := raw_ints% [0x0,-0xae7d5556952cff1a7c56d604723ae969188270c96e5b0000000000000000,0x1043722e2b2482f2719915d7b84c906b3bef2ff2db2fbea537ced8bef30000,-0xbaa3acccda1134992d3b5de499b41cb87a1a94c9161e1d5b791438bb3f4000,0x55ba5221f0a4e78321598019920198390933798e15f9acbcb401bf550a70000,-0x1c53c1ebd144d988a7af97b998976660c692409b2bc30ec586e147b493ca1000,0x72bd67851271ed4630ed7e5e942092d516d8cc6bede7ae385e06578972374000,-0x172481eba269e53f5d86cbc0a63f9cf8409f91118ed6855dbc103a90772b35000,0x3d179dbf62f174693c44a3b6954acc1ee57dabae26a273f0c6eb0bbf750890000,-0x8668721cfb33489adef43bc35815148a6f76b45324701daa0fb9a1a6d145de400,0xf9d6307bb23538e41a6e3b7c2b44036d99ef7759c32628111186592d33d1bd000,-0x18c5ba06fa3e3350a2ff16f17e6beafd9ecf8409dc71aa449c7b8f3eec47cf0400,0x21cc56f15317762934569d43bacff8e0ff4d338edb276fbe35521b06f2b91a4000,-0x27e1433d88c0ddd8d2516b27d126d8139440ce3d7bb3dc888f95462a8ece175c00,0x28dc5ce10528b759cc43f44519b1c74465cec5f2ef2c9709022041ac4272be3000,-0x2474166af0ad9dc33cce8d3787bbf3fa8b23ea65f769a7380aea5fe5f6b0665c00,0x1c5cd679c7c7a660e55a0c0ae76b285e6ab4c1441571271bedfbda1d8460bb0000,-0x1341beabb7dfbaee8c5fc78342e52a56f0ae2da291a19fa6132978118cedf88500,0xb67a9e81139cff87a0b3e943fdb3af3ab93b59ddc9d00b974cdbdaba919d96400,-0x5e2716b8cf791a490232bd491253ba9e7180b960a1b8dddc2750b76f0c08f6d00,0x2a3a70e234ca594e4cdfafeddcaf97faac8a3702b7a357bf821ad24e84ea99000,-0x10695777e3cf2f90f380eddd82229f6960ec420c52b295dc30ad4f0fee3f21300,0x580ea4b412eb42f0ffd9e1869c3a2b6b6fe5282b426e98c6b26faeb731833c00,-0x19588024cdd768dfc7c19f31af8013dde67f0ec092afb5199627e7c917b69300,0x6387597df500e3dba1e8d5cfd38368d03f4be720f0f1fe5cd862e3882f20000,-0x14a96d99f9659ac6982a6d50a096c00b1c5cbfc1b16aefd80f1b69bc6df9600,0x397d02e33cbe14ec36087e2888bd2fd3de4fcbd76ef8b09764874db1d3f800,-0x846bb0aa2176e366c24dc94b8ae55257c0ca5302e0690d217cca7d868e600,0xf8f51f652caac00f51f90186360fc021255747ef2b5f187e6cee37a3e000,-0x1777e1112c3c4800efe6f88daa3a7360f39b94d02a2477baf75e53d5c200,0x1bce286d1bb72fa2bb2e3c6898b6ce2f8144ccc261663ee53b81e29e800,-0x1937b06d722f2b54282e0cb5a2845140593378b6593625b7a62a842200,0x10f3b6f530c1614dfe87cec4d108e019cd57211061dbc641817b28000,-0x81c420989baee8eb350f4b515f1e457544b5feec2a3b90ba62bf100,0x29f0913cbadc4eb1c9c3a95601d3024fcee6ce58b59828b6b59400,-0x88cad7d7b179b8224ada28a0d338995b4e134d2a7dec37219900,0x1006326d7bbecdc312c5868222e55a009b79d7392677808d000,-0xf1dea6e49744f8c9d81094a8425b95e5779462583608cf00,0x5dc7f0ab8fba819017325523f5d2f3ff6ae7a758ebac00,-0xa85c90af155edcc2cbaabbea2de62252d1ee86f6f00,0x27e0d57917bf8ca3ad8a00000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 21 86 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 86 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 49 indices rho q26 m26 26 123557730405954960569713459200000 28=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 49 indices rho q26 m26 26 123557730405954960569713459200000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_26
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<27) : intPolyRF (mz e)=rfPoly (C (123557730405954960569713459200000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^e) := by
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
#print axioms moment_source_26
end
end CatalanCore.Li2.NVMod.FamilySource.U7C28
