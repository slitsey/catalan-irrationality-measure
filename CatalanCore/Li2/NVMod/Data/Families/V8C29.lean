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
namespace CatalanCore.Li2.NVMod.FamilySource.V8C29
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,8,29,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
def num : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x320a0b16553099e2a00000,0x42c49e6985eaf2fb820000,0x2a176db11ea043ee270000,0x10ad1a22174b1986e57800,0x4a8aa3002b33e17869e00,0xf9dfda58bd46ba432b80,0x28c256e8a805c8360920,0x54ddd8f1322d8d49770,0x8f49d102df4c6e2230,0xc64c3d9d8efe2be10,0xe26d33f86ddf53e2,0xd601e00025670ab,0xa771e277e56dd2,0x6c22aa1efe375,0x3945d0a20a04,0x189e09664ee,0x8734910c4,0x242e45aa,0x7458ba,0x10847,0x17a,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x5,-0x37,0xa5,-0x1ad,0x1b5f,-0x861,0x6ced,-0x51fa5e,0x5a2d01,-0x21a12e2,0x5412f35,-0x1248495c,0x20d569a,-0x90bddc4c,0x6c8e6539,-0x2ef41135,0xcb76f53b,-0x512911b,0x1fd09c7]
def rhoDenominators : List ℤ := raw_ints% [0x59332350,0xe1884,0x4bf8,0xa5c,0xd0,0x19,0x1e,0x1,0x2,0x51,0x19,0x37,0x42,0x8f,0xd,0x3cf,0x410,0x374,0x2b08,0x50c,0x1430]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 29
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
  | 20=>li20
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x69b91e2418a691f6984961100,-0xcc88fdd26786d2b6218e9d54c0,0xbfdeefc0dfaa00b65f15bad36c0,-0x74432b884e89e77d4d5068065af0,0x3324e1d5d8b0598c4603cb09db870,-0x1167966365cd463981ac3ea0705d00,0x4c487e47cce1d649a9c9e298519600,-0x114813cefb10044501a15d2e423905c,0x34d1acb2722d9889f3fc77571b49f3c,-0x8a1a725fc878057d6ace871dbbeb730,0x13854007275feabd8ac344c0ec0048f0,-0x268345458a82aa32cbeebac89940a128,0x42bb2ce3a04af672e5abb7e98345b8e8,-0x66140e028df9ed24bbda812ef371b4d0,0x8a6a054c4db87045620ea9cedc7ae010,-0xa6e1603d481ab869f3857674301ab623,0xb34cb4a9a8ebdef157c4734f88cb067b,-0xabee1138d67016a29784fbb824eef77c,0x9341c3689de908a2f81a06111434b52c,-0x70accfd1cdad4f88c78474f445106e4a,0x4cfc810789dfc7c4786f3bbf5652ad7a,-0x2eebcaa4fe232dbeba8e1c4b515aa944,0x1977097ed3611f06584e13ceaa137a54,-0xc46ed9fa11e8417f3054ecc97a48201,0x53dcba137ea19ec99d98adc413c4ce9,-0x1f93ca793c29b3521a805c15a6ac248,0xa6f3a4050501a590a7cc9bbedceae8,-0x301e0401b724d336808f0ec5dbc244,0xc012687baf2149faabc7d5edd1ea4,-0x2918c3fcd18dc1e50096c30034818,0x7748fb3169775ea5dedbc1419178,-0x1215f5004c703df6237b553622a5,0x240285f8e9baeee4132b27208cd,-0x397c26eea3229a93a1eca1fc8c,0x475530fa349624fde8edb957c,-0x41f460431c726a4b6c5a023a,0x2ac5f342a2773b3d84fee6a,-0x11c0a846b31a374f731a94,0x40d53e32a4ed0e2da8e4,-0x61b6288bbabd0f05fb,0x1e231ee1a5aee7b3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 21 40 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 40 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 50 indices rho q0 m0 0 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 50 indices rho q0 m0 0 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xb903f4bf2b237f6f8a8069dc00,0x161b8ed847bb303e815789c1d100,-0x147d4ab631370c4e329c2d1eefa00,0xc4347c5f70eb22b1e8a2c756ec640,-0x5539fee08c41c340290e75debbf780,0x1ca15a2b0f9b948785014738414e600,-0x7bd53ab950a6d07106b3b5794493c00,0x1baced56ac789563f32151c848fd5010,-0x536afbe1f60fa04887bd8b030bcee6e0,0xd704298ed432f1f6295ccdb74619eac0,-0x1df3142e0bbbcea2e11f1dd58923af680,0x3a346a68dc84f3c451365450e4a77d6e0,-0x634ccb0fd96b12c7ccba19247ed988b00,0x957e3a1f9e562e793a9ad2355ed35d340,-0xc765fee144601a0bc1f2ed8665ab77100,0xec5bef4281bb29ff35a62dfb556246754,-0xf98878230f63d51e4c115c3aac403bb18,0xeaf94e8281176fc8d6240c1670cbfbe70,-0xc58186f0c881ced97471d8e4b231e90a0,0x94348881facea3f129e1ae6a06f5f5138,-0x633b402673645dc905cf48d6ccda41dc0,0x3b376e882eb72d0351bdc6001131c5b10,-0x1f704dca582fe42c0befa9efb607a1440,0xed001e710f317e86e95333a55cf3d27c,-0x62c5e982e77b8fa34c51a195f4add7b8,0x24433130b67a3069cdde45c7f8686420,-0xbaadc46671c43dce1bdabb4ca4b2d40,0x344ecea432ecc309eff6dc65a2de730,-0xcaa659082dc10a05c91e354d877cc0,0x2a002d41db78ab79351f48954bdc60,-0x75d251d3d8db72181ed4597e25300,0x113847b34a90317399da4185fb44c,-0x20f2b4dfa032a6a729ec6c387408,0x325c0fb349badd39fce1d4c6eb0,-0x3b90d84f794040df6446fef0a0,0x3434ffcb29632bb7a72539cf8,-0x1fdebc7eff511a9beec4fc00,0xc5662cc126664f61cf4250,-0x29837014116e8016facc0,0x38b06acffd2c4f0cf54,-0xf7e42d073a38bd48]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 21 41 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 41 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 50 indices rho q1 m1 1 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 50 indices rho q1 m1 1 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x143c6ec4e8b7e1f033260b941000,-0x263e722e60f7d372beeb57005a000,0x2307457617a489945a8a6b53396300,-0x14b66db9ff90ff968f3d49529e5f800,0x8e2f2623c53002f95405a7623bdb8c0,-0x2f29d3b856db39de0476293f3976fd40,0xc95d540134974a2d859e37d6eb92cec0,-0x2c689a595446e32fbec5923ebff2f0d00,0x840a35d2d7b8d2e5b1cb071e1e52f11b0,-0x14f9b9688d3bef48ae0dc9755de78307d0,0x2e140e21c0ebe938ab0536c8feb22c63f0,-0x583bb95e7a065f1b6612edc427a4500210,0x94407c3d06e8c9955d2f2621791b541650,-0xdbb55a5cd5d2f0aaec8de3fcfb7f249d30,0x120572a964e8e286d4aae9a55ab8ad59b90,-0x1501c8b22006dcec11da05a618810e49c20,0x15cc0d509145443fa92aad90a5d0c764ffc,-0x14291959f1f94aee5f97c7ddca2560608e4,0x10a238021483a50610d28db570a6859214c,-0xc3e30e52c49e41623332982d85f94e40b4,0x808c82acc4edf6573ef0008b5fdfa44464,-0x4b1f6c637a389830e15d177a674af205fc,0x27056eb84b429103df9c379530434872f4,-0x11f827f7397602f47fef057e83fd358dbc,0x74fba079c5a5868802b416fc5fec79848,-0x29e0ab8cf4a7b997fa8bf87a762fed5b8,0xd1ec1774e3c08ee81300d3fa46e62268,-0x392fbd6e4c8c6281af3a41947b77e318,0xd70435794745fa6e552ea719f2b6118,-0x2b29ac6bff2c3f1d906cd6068ef5928,0x75012886e2620441f745ac6896d4f8,-0x107af6848a0cad5ce4901d503a2418,0x1e4b2fc1f66b6be943d9692e7008c,-0x2c50a6d84531aeb2730c74b81c54,0x31efe245d646b22cb7ff0d2369c,-0x29764982330081f3e37ba310e4,0x17ce5ebd56ec5799f1ccb0834,-0x8967b40b6c04f0803e6b3ac,0x1a990dec3513a1d95adc84,-0x20e20245a584f934264c,0x7f63b9fb80051a8c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 21 42 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 42 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 50 indices rho q2 m2 2 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 50 indices rho q2 m2 2 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x2369c1d89741cb64598294431c000,0x422d46a8b97f1c61da527840d82c00,-0x3beb0506a8861e7200e7e27be195500,0x2303b8a29fc4ca5c72e2c800d353ad00,-0xed7990be8bb21d98ae81f768e0c3df40,0x4dcd7c0a92507c26b50df90bb6a5a0140,-0x147fd27b2d46d8e912092af43d3b6c8840,0x4765df9241b1bd400180e2267ad3ad2940,-0xd1775aeefd71a9f50e0145c6a7e1dd8b50,0x20d22564e4b299ea58124fb197dc459b0d0,-0x47166d26c74f75f1fde0a00fe922d2270d0,0x8627b6b97d8ed9d6175e94988c24e50edd0,-0xde0e094066b01f110bcd6e092baee80c630,0x14407f2d7df99e0784f69c3517d77b2301b0,-0x1a282b35be700cd605864caa413b1fe28030,0x1dfdafaed1b133e85d082304044b4c456f70,-0x1e97680961f876d30892956ef4ac3a4e01c4,0x1bcc2ff11290e7e303cb7abb60d007fc04a4,-0x168445fec87d3f503f671af0c479b11739a4,0x104256283fd6ac8427788539c518f6fadae4,-0xa75a2f93b71bd0de9d2328a82b757b72fbc,0x5fc9c9f7145be2d13e84cd6224da78a8d1c,-0x30afc3ff30e4650f7a9325566b8e8eba63c,0x15ea766791a5a18d807cf1486e877156e7c,-0x8b4e4955629438ada843a0740b6c4d3978,0x30a1187a6109b034984cf3f4abbc9d8cb8,-0xed5ef9e9c70a5906aae87bc0b9c2fdd38,0x3ede0138e0390218705bf77a098ea37b8,-0xe564bb56e2e246f3289061c7421d3a28,0x2c98cc67fad79de7bbb387db3a8ae168,-0x74cd9daae20e83b9556889e0dadc1a8,0xfda0f9261ee31af7a725950e3e1668,-0x1bfc07c19bddc889de7d644bc34f34,0x2729ff4ec431012a9670f3b759994,-0x2a0604105036daba31405696ba14,0x210839d27b9331dc14fad739354,-0x11d318ea01cea4d05bc0d3c8ec,0x5fc8c5ad3050e93797e136cc,-0x110cdee8b0826d43fba08ec,0x1311da5176aa9b507f1ac,-0x4170b2f71fbae94200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 21 43 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 43 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 50 indices rho q3 m3 3 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 50 indices rho q3 m3 3 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x3df9133b08b323ef9ca48375710000,-0x728b39b30749152182ac8071dd4f400,0x668cf3569e70a5e1995268a572e7d700,-0x3b3dce46ebccc2deea45c2cb62aed7700,0x18d11ef782ef54ade56df37be2e056edc0,-0x80863ef4785cda4d22eb7270b0cc2b6ec0,0x2171f9740c2a6be5f3e7ea4efa7508a5440,-0x7302c7e6427c5c7bf2af220cab92dd04540,0x14d056c63a05c2a02795c3edc211181f7170,-0x337b3b518b09cd37438e2ea13935ffa0fcb0,0x6df79c9b74d985e84ecc4aa15060fbe5c3d0,-0xcc9478777342865de1a7fd75bc899f1b0710,0x14da99c7f43dfd37e84f284cf8af6c06b2cd0,-0x1df88239d457c398d16483c24a1331790d690,0x261acdd90ca0e96dada12e95ec0181586cff0,-0x2afbe1d0c6a39b0176267c92cad6832393cb0,0x2b1c4ad8b7768cbac7520db373799b81a9eec,-0x267e3fcc69ae96e1cb28dfd98c88599c2d27c,0x1e9e337f597b6c31b2847676d25bc08f8b0a4,-0x15b1b4d93a050247c4109cfc0cbb435723c34,0xdaed9b2ee46799c9bdd5207c0b7827221dc4,-0x7ac04066fef5cf1cca77ea87d445ca4a46f4,0x3d0f04f1a97dfd7246f71c688a1ed88a23ac,-0x1adea42f1b4b59a678487b73bb39f374d3dc,0xa6c67a2705f339fe4212d6398c5ddaf5868,-0x38c655ee399bcb8aa7eb1b4b16dbb155848,0x10dde06557b4e487837c36d8d0bab5ea978,-0x457cb06f7b330c499358062d8143984558,0xf60bcd0e8b6f89d1ea14e8a4c28f23498,-0x2e523d8ab21eda35f5cf0a20d4b7b7bb8,0x753279b9c65bb8828cfd53f1e4fda608,-0xf524d4b44d950e8dfc40746b63ba228,0x19f813c0cf12fa20d9a2589af547afc,-0x22c1559c9391047bedb0beccdf114c,0x237dfc818e6e30357a83020d74654,-0x1a65000c0de89bbf9326575854a4,0xd601c769f6d13ab321dbf2bf54,-0x42dc0246e021ca7c0a1608b44,0xaef47a34846064c505896dc,-0xb0e7608b5b7a1934af3cc,0x219ac696f6dba1a3000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 21 44 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 44 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 50 indices rho q4 m4 4 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 50 indices rho q4 m4 4 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x320a0b16553099e2a00000,-0x42c49e6985eaf2fb820000,-0x2a176db11ea043ee270000,-0x10ad1a22174b1986e57800,-0x4a8aa3002b33e17869e00,-0xf9dfda58bd46ba432b80,-0x28c256e8a805c8360920,-0x54ddd8f1322d750fe70,-0x8f49d102df449429b0,-0xc64c3d9d8ddd12500,-0xe26d33f855591b62,-0xd601dffec561a83,-0xa771e26a0d863a,-0x6c22a9b9e8924,-0x3945ce80ca84,-0x189e00da3b2,-0x8732f9ed4,-0x242acf04,-0x7402fa,-0x102b3,-0x142]
def m5 : List ℤ := raw_ints% [0x0,-0x6c73e1a74f397ee3521fe60d85c0000,0xc650e1ad253fd8d238756e67ea5e7c00,-0xaf9d1bd0db861e0508f25dd8a25448d00,0x64505b078f5a639d6ab57bb9dd2a336d00,-0x298a64bb043f73143ec25e16f0c0cc98d40,0xd49a5e2c2f9a2b1ce48a8142b75b2d1d640,-0x36a7e869331b24ea468720f8857ba25c4b40,0xb99d93639165822818b1c2d53e6e83ea5240,-0x21298c2c987690572f4a685493dcc8d2467d0,0x50f2310f7c19d93880cc233db73e5b00dd910,-0xaa9063474260a23359d2d71b5b9efb3aace90,0x138e1c230ef7c8c73604f4ad1034ce11271050,-0x1f6f1f3438ac5ffb9b29cf0510fa7f6ab46a30,0x2c80f07487d7c9ea5c7722e7aa732b873da7f0,-0x37b5e32d1ec1843879782b15170ca4398e4cf0,0x3dd7894472ee12da9c666d69fdd8ce45b2c030,-0x3cffa268728ccddc4d3ac51607ddb25b394fe4,0x3587c33f8e05094322162f9b2c301f7f2638f4,-0x29d196efe4e878aa63ebb91971482e6e3817d4,0x1d145db755c0397981cd9d8887a4551ec5d684,-0x11fc45eef0cc0fd30c14ba6a1b057d21c9493c,0x9e13e5f57153d079aa92ba74401969125656c,-0x4cf6253b41f8361ad2b50efcd2145e9f35eac,0x211cf99b055614bed274699a3a0c87f0218bc,-0xc8b529252224223b741a97b00082813af4b8,0x42a2af6ff364eec8c18e069690f243e8e998,-0x134716f218819a15005ee10a95f88c7b1a58,0x4d3602bc8875fbe37fa57139d53aac339f8,-0x1094a4d69d36deb1c02db8e7291182753a8,0x305bea735f0419fa88d364ae76060ea8c8,-0x762cee730305707665b96b2f724b647c8,0xee0f8c42f1cf8357aab7dac182608c28,-0x183468b9bc2d4147338212a9b4a7fc54,0x1ef72a3bfb9e73f3ef7f66ce6323624,-0x1e145cd0b6a43e2ba588e2c48e3104,0x15266dbd1e2acb28f49e9a5b51ff4,-0xa0eb53213a009b97944d2b1d2ec,0x2eb9bc9e50e5be71ff60d755dc,-0x703e2bb49394a5a4faa9729c,0x668aa2c9d1b56ff39f0aec,-0x11401ae88a7de6d48000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 21 46 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 46 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 50 indices rho q5 m5 5 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 50 indices rho q5 m5 5 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x142,0x1]
def r6 : List ℤ := raw_ints% [0x3ef0a1f21727218f0d400000,0x53c94535a41c550676e40000,0x34aeb35a5effaa7e918c0000,0x14cfa371302dd5d7be79f000,0x5cb78f6414e2900106d4400,0x135a2e6739b5fb830f61900,0x324a91764a99ff19b44ec0,0x6832e570d69cef33071c0,0xaeecfb5689bb4b3601f0,0xf077486fffe769ee670,0x110689784a155165d44,0xff078880a9b609bb4,0xc53d20dae23e07a1,0x7d8c7bd45ae92f0,0x4147a5d0320fe4,0x1b626aeaa28d8,0x91721d972d6,0x250f040100,0x6e2ccaf0,0xd86654,0xd8c1]
def m6 : List ℤ := raw_ints% [0x0,0xbdcacae4caa49e0dcfb7d297aa100000,-0x15772e15e7e87a6ebac2e4034f416c1400,0x12ce5188e2620ac9b2b6a0fdf6aa4051f00,-0xaa0013671e0fd91717489fce8597e878700,0x459bfc3fc2c7700c52f623ea5edcb27e57c0,-0x160285a34fd3bb887c97054d9f95faf3dfec0,0x597637afd3f7ef003a3e3097b9ec10c42da40,-0x12c1f8f552614a1ed664b5760d26a6b120cd40,0x34f2f3c60c20380879b6bcb9fcdec2db841bf0,-0x7f939eedd8c4066b3c23a7753e3be685ae5cb0,0x1093eef65a569807712d8ab9470566a3b563f50,-0x1dfe34e39d2df85a4f71fcf96e9504998e84410,0x2f876b4d016e56af4d4804df99e1405e1929450,-0x424dca840bbefe08568b91cd93111cbce834c90,0x51bd8e6816f4952c8bdfb47a81517beb6499270,-0x594f1ab72254d0dbb8e89d633a0be07b2916ab0,0x56a70525cc78d98bf802500c1eb4edcab65eb0c,-0x4ac0a6f829c9a21f845fa8a9467ee95b5ebd47c,0x395db5c9dfd9f0e7e5f7b1f17f51b147682ac04,-0x2727eac64a1ed4f8ea4c733e5ec4fdd8ca6bc74,0x17c06cf84398fb81fe1dc6654c6bc81f827a324,-0xcc8e333bb845d44b80ec3c08186f718801ba74,0x617cb978071b71d3ffd548a597558b57af96cc,-0x29038d821b304ce3e4930d1fd10343b8da181c,0xf2c8d4d43f93da82778c095ce7773d8c4ea28,-0x4e9d439601ad708ea3981934b8161c0bc1648,0x1625dbd3f1d61c7de2d16022e1a0ec80000b8,-0x563cd5c4f4cb6c76fee1b04960116ae8b6d8,0x11f8062e4ef83bbd4d5f52c20298df5418d8,-0x32bd14bdd9bb3321f57d2f373c89151a6b8,0x77bc687ae2e45bb6d36dd5ec8870baf4c8,-0xe83d1e6d2175238c86e7266e6a06a96a8,0x16a7ee1bb517580bf57bfdaeda956f49c,-0x1bb1c7787a6c9a1e1ff79e0de77aa54c,0x19939080ab63ae176ee546a7872a634,-0x10fe26fe365a74d46d86056c5135e4,0x793b658d633ba19e07e3bbfab234,-0x20b0b7427493d646bd5890d92c4,0x4807e5f0b2a337c039ecf167c,-0x3b6c04c31850484ffd9650c,0x8da29ca7a8f7e2cc0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 21 48 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 48 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 50 indices rho q6 m6 6 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 50 indices rho q6 m6 6 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0xd8c1,-0x142,0x1]
def r7 : List ℤ := raw_ints% [-0x2a5e32ed33b73b7b3adaa00000,-0x38494b4284750c03d63fc20000,-0x234fb6f1eebb33cf20fc830000,-0xde9f1da1cfbed7d91beb37800,-0x3dd031d5f4917afd193532e00,-0xcdc5c9083b4c367b08ea8780,-0x214d10f15f902d915779c820,-0x44b68134ab83a39be585cb0,-0x72cf20a9f2290698afd470,-0x9cf703c1fbd38df18c820,-0xb0af63a6cb00cd8606f2,-0xa42c62f1b595d24dba7,-0x7dd5db68db5d405f9e,-0x4f3af39eb9b872b94,-0x28a54dedbcee5a14,-0x10c36cb6658d78a,-0x5717de190daec,-0x158b2fd08254,-0x3d738fd33a,-0x71965a97,-0x67a6a6]
def m7 : List ℤ := raw_ints% [0x0,-0x14c22e31062a014982b81b089699c00000,0x252f40c4180f1c17d512432ab26ef321c00,-0x203d3a28759d1c183a9a7522d27a4336c500,0x12053d1e1008018d84361a9375718c7f3b500,-0x74c49b89a273a7266068bd9628646b7ef5340,0x248170b3ae328b1e498761cd8a58621b2ae040,-0x92aa1e82f808e90c21f079c259c1a859582740,0x1e629ecb510f79281de53ab91bb75eba4843a40,-0x54b7eda29fb7e1bff33b8147baaae702f17bb50,0xc98a2b5498bf9af93e5197942db7cae1649a590,-0x19d8d1b2c51cc1b3af47641b0900b08e29c10990,0x2e21c993d82efa770df0a4bf81cb9c243b37a650,-0x48158f5ef8002c1f0a23d63e6b5affee8f77c1b0,0x631b5f0ac0ea7925613a24f425b63990ec0ab670,-0x785a2d5bbf013400908a377e16275cee8876ccf0,0x817448c335a0bc2a909f0e462d2f2f0b114a0130,-0x7b93c59e414f3996f3d97462daf2e457de675c44,0x68d130293670c208976631793ff39e3a566e5694,-0x4f07f6234e07dc0e438906f44cf0a77bd5469494,0x34f5795dc4262e566285975d181d0b5ab8eb1b04,-0x1f82de684c105938c9fb8020906778f4f08efb9c,0x109f49977569d1bfeaf24d08982becc702c16c8c,-0x7c168e43bca331a352474aabe72c1c55fe78fac,0x330d414580f05be884d556261ff9457e220bffc,-0x1272936b821269589cd040a43594614b0b8f0f8,0x5d37a9853ee16f6ebf44eac17b7a2f1f3a8358,-0x199329873df8f848b6e372efe8953a192a59d8,0x60ce8c7033f7627d7ba365dc5d89792eb89f8,-0x13920374418b04bae5cfeba9d951b4823aee8,0x357e7a1bcba50c554cc59e838d1574f64c88,-0x79e270b30cf5e15cf26c858b0ea7ea548c8,0xe38fc4167244b8338d5752e388401072a8,-0x154b07ffd241ec4df8a525e429ec530434,0x18dc199679865340799a1975a0991d244,-0x15d0d46584f32eb368192b63a0c4e7c4,0xdafd500d416821c1e7f36c63472774,-0x5b7ea4837a77f95a4cd2e6ab903cc,0x16e4b0bca82fc094ad6207f6127c,-0x2e3c5faf97462d54639938be9c,0x226ccad871af53e5471d9a2c,-0x48a83542ed44458200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 21 50 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 50 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 50 indices rho q7 m7 7 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 50 indices rho q7 m7 7 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x67a6a6,0xd8c1,-0x142,0x1]
def r8 : List ℤ := raw_ints% [0x14429d6baff246ab7b1cb3c00000,0x1ade3453bed313b79eb887ac0000,0x10d28a5352c8bc10c65477880000,0x69d30dbf67db1deb7389018d000,0x1d4faeb30760408771c5f0afc00,0x614eb6eb11fea3d9d942f00700,0xfb2f3a0f296d80ad57fea2340,0x2047b01c7c4a4112a0aa30a80,0x35b891cc42842e70fc8cee70,0x491cd0c5298496c7405c9f0,0x51dde54f5741f7f00a286c,0x4b9b1ae219b4c1862e9f0,0x39890c5bd48e56548685,0x23eaf954b4fb5ddfc40,0x123cb01fd4c7a5eb04,0x76d4759e05cb6c40,0x25fabd67ac31f8e,0x934ad9d028d50,0x19903fffa248,0x2d8d0a94d0,0x2775b685]
def m8 : List ℤ := raw_ints% [0x0,0x2453d0d5cac98240a4c22f4f078d1000000,-0x406e7a8961d96702ece73d88ff503098f400,0x374c0931b2a97fcd4b39677d4eb102803c700,-0x1e966868ebe0669757d4b8f4194068c1232f00,0xc414a9d92aad4a3c8eb680819919bd6ff369c0,-0x3ca098dde945bb53009e8bcc9f23b3576c310c0,0xf0d1637556ebdbc1bfc2af94caf4fbce4d41a40,-0x314f3b841e82e6868d088d0c3bd5647551709540,0x87d4145b46bfbd59a8f9dd25b44a58c2a2123270,-0x13f1da9660e9b39b4a94953f88fbe3c61fa449330,0x2866a7c1c4b13c17d60529bbef9992cb38f2fcf50,-0x4726f4feb04101eddba7062ce30d0b079b96f0e10,0x6da77481440ddea7399f1002ec0b148ff08255cd0,-0x949df86e4c21bfa7ccc51ff363a3dec35771fcd10,0xb1d03ce365857ca6377e643876c7bed919b3f4970,-0xbc5496bda075ad49e74d78509ed97444df5cd97b0,0xb0ea5602c7b082cdfb52e04fe1bddc2692b93b52c,-0x9391311eba42a0b4c9f980c7cc71462be2e447e9c,0x6d56627cdc81d290951d75f0aa630d495ad48f104,-0x47f101adcbfaa91b865bdb12f9d7c84075c8e0df4,0x29fec57d3aade7a418587ce712e748b8b13c712c4,-0x15b65faae30b0921f72c31b64ceb48965934f1014,0x9eb3bf68f35ec4c76519f936d67c05e2d14d988c,-0x3fdb17536e8b114a64fc034753dfd8316e8ef15c,0x1689b9fa009862dfd1490130e4724ae9c2d4dee8,-0x6f15361ec3b563e9456b47df75474eea6c5bb08,0x1dadd6cd4ec4b060f82fd5b48ca38cd59555bb8,-0x6d355eaf0b2f492185035b2d44ab32e18c30d8,0x156b14c962772b9347a60371943b357c395398,-0x38aa82b078c629e32eb975cc09df42cd3c578,0x7ca29b488ebffb91cbdfe800626668921a48,-0xdfeef871a7a93af5ea026bbf6cbe7876928,0x14175277ee605ac5e6eb77e87da50888f3c,-0x1664c649b37e35d78e7f9641bc88069fec,0x12a9e1b46521acdcdd18c4ca71e5d2834,-0xb0cd19066e9957ef64ac57e98bd8a64,0x452a3cf664a615b973454f6cf8fd54,-0x100be5e792331ffd3d5993ab96be4,0x1daef77dd6d5b4dce0143485e3c,-0x13f01094ea2bb84127413f24c,0x25429037ba284bd3000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 21 52 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 52 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 50 indices rho q8 m8 8 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 50 indices rho q8 m8 8 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r9 : List ℤ := raw_ints% [-0x7b689f49b48f9d2aa9a307d200000,-0xa3664fb86b65f264e145862ca0000,-0x6620e3950067f4f75b8b4ec970000,-0x28137718a511dbfa4fffd98ff5800,-0xb139249102998beccf5b932b4600,-0x24af04ce1575ca55836188479d80,-0x5e70a67959c3bd44994373f76a0,-0xc19a2b8a534a0d28a7906229f0,-0x1411a6bb1a81afe2b9e6d2d870,-0x1b35427f9f0cd676424af2fe0,-0x1e54f3368c5d919a2aed767a,-0x1bded23af48925e461ef26b,-0x1515a64098502f7cdc702a,-0xd1270158e9021e7ad344,-0x69548f121de11440fd4,-0x2a79a340943503b8a2,-0xd69e62ae56a9a194,-0x33403b7f37fedc4,-0x8ba563985c752,-0xf2c15df249b,-0xcb6c4eb92]
def m9 : List ℤ := raw_ints% [0x0,-0x3f92ad7622e0a3f12053d2ca4d36dc000000,0x6fac39f5294eb323ad20f52cd6b4010e1bc00,-0x5ee532337e8a01dd52851741bf4c1c60b7fd00,0x33f577108924fe961187263cb94aa5127410d00,-0x1499ac49ab625a70c7b2f67a0f2d30b15827b940,0x64d12b1c66ec1b7894f46f471ae879030fbdce40,-0x18c05512dd4e96792bd25eaa984e04a2ccc0ec740,0x502999ffad4213f3aaa070d9f084b91b645bb1a40,-0xda36ab4f7e49a9974d5a7cbee7b95d267abcfdad0,0x1fa6dda14b6c79919e0e93a38d7e2f21de7a707710,-0x3f4ee2e572e796bd46b636579413b5115b23c57190,0x6e0acaefe5e8749cc5c4279be289654ba8d6a40e50,-0xa74c7011dbf22623c79b643907152755af4fe1c730,0xdf9194d8bf8a2068b47bb4db66d34bc61156f1a1f0,-0x107996f12bcfd29780185fed5a598c9ddbf7e5851f0,0x112f7e22da79935ceca090382e9a1179df03cdb6630,-0xfe3c2126e26258728e22cf88273927f8ff5ef5bda4,0xd0941c718507b748bf796d3796865037f263d42274,-0x97e493f794e40245e995273b8d1d53c95de7fa3194,0x62262c1226e97bba5932cc9027b550cfedc7e46804,-0x38377036b0edeeb67a30b31d80437453e9d4ced97c,0x1c7dc50ca6cc4c0bdf8901eb862e902c0dc10f19ec,-0xcbec80614b3cb8ef50cdf0cdf911ee31b629768ec,0x5040b8564d7f7947b847dfad83b142ab57b74693c,-0x1bab2d449346751cf157773dc9fc9a4e4027e6138,0x85045e6b67690bef466904bce8d4967f1632ee98,-0x229c0fd5018c9f30e480e68da2cd99cdc14c66d8,0x7bcb3554738eafb6dc10becad180f8e2d4dcef8,-0x178d486ae3b6c53f56a70c508179edb9b9bf128,0x3c4d79d41bb25c75f83a80cb3621e94b1d63c8,-0x8002830654cd30d9b1e662fbcdfe33ddaa948,0xdd46b04d9655636b23c18b5626040b936b28,-0x13076a51b462688dbea1bc721081378d2314,0x143d7519fe2832ce4bfcd5b76ff9f8921a4,-0x100321484ae17eacd2f222eb83a63ebbc4,0x8f0e82ab6b691f047e9b85d06563d374,-0x345d372158d3e879bfa39498d3b282c,0xb419341b794c776797a0e4a923c5c,-0x130f25e3282e1db3c0eae1a381dc,0xb8b3bee23477aa6beea95f56c,-0x131a03f65a6839f48000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 21 54 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 54 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 50 indices rho q9 m9 9 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 50 indices rho q9 m9 9 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r10 : List ℤ := raw_ints% [0x27c3226aa1dd8d02ca23d4c1f400000,0x3492c07968b4730b5516ccb49040000,0x20cefc7f9533c59236dbddf3c740000,0xcda30fd46fde1f7bf795ae876f7000,0x38ba4138812e6c970258695cd0c400,0xbb7aa72251e525e2776509e120900,0x1e186922f61017be3c00ffd69f6c0,0x3d88c85029f60d21dd042ac2b740,0x65c28538eb0353fe0bb6c8f6570,0x8980b34575024044acf1363cb0,0x98b721694fef81c5d6bb71d04,0x8bb9140365b612d858b7c40c,0x692f53e3723526d17517559,0x40d7968682bfa36753af90,0x2070276ba3eb220308f04,0xcfa72c0e9fc8d5ff9e8,0x40f63f851dcb1bc326,0xf5619b88f7d52760,0x293359346b56a50,0x465ab8a061e2c,0x399c8e4b0f9]
def m10 : List ℤ := raw_ints% [0x0,0x6f40af8ebd091ee5f892b0e20720010000000,-0xc199c55d09088395ff8669119011f41cced400,0xa2eed9397967bd73b2a3cf26718987daf3baf00,-0x5854589ce69a0ff627b86391410c4659c6173700,0x22a9d637c43173a9f8a4213abf6c6c9e880994bc0,-0xa7dc2ee6eba2c2da39385f5bc8600287665ee9ac0,0x28c3b42c6fb45e4849528794298e827414bad02240,-0x828c7000992f157125f40055b6a87816150d640d40,0x15f444be42d559be54fe91322a9a8b2f5e897b794f0,-0x3257b5ceb4467acb5526599d07b5152fa5e67908fb0,0x63729b4eb5019cad904eae145d76cce2aba4d184950,-0xaaa55f82a1fc4bc34f225fd7fc9b3b33fd1c7a9a410,0xfffd428b3d35e3f5513511ed9cf146792350f852550,-0x1515f3509198364e565a909d54af1f27eec07eec6390,0x188137230311d28037798c5ddeb5db0ddea21e76d270,-0x192e1c624729a7cba8658beccaa5970ee249c99b44b0,0x16eb552a6f689f2ecd690b08322253e2c4155df49a4c,-0x127f7b60b3573e3a5d6d1ad12d740e84c01fa8ff503c,0xd3df49d2f457a8174e34eef8adc17fe628cee0a3284,-0x8678a4469f3b918dfadcd68913159da3fa2c4109a74,0x4b9552c5c27a78767080a01481f82f98237b931ee64,-0x258e10f3d32003c38e63d089e80610d8630cfb53d34,0x1073d05af9ebcf5f4fa08faba751b1906b3ec8f3ccc,-0x655548e63c57ba67b6703e466b1c49af6f5be5aa9c,0x2220e392e7b826df1d8e843485815e9dbda109c1a8,-0xa00adc6b3e5bc268437a662ba6726c45b587bd4c8,0x288d34151960122834f5b87443ca03089f0f921b8,-0x8cfd34b254a9bc8060f9bcfaa3c8253efd5248d8,0x1a0490f4820ac713931c0a9a947b550712a72258,-0x4075d2b46f5694b21cb3b9ab7c6e9a17f67f538,0x8409cff2e8d30d35f752efd1915c90772a22c8,-0xdb86b76f99008b79c466e7e1b7f86d85447a8,0x1216c07ad9960105b335412960de70860ecdc,-0x125a3dc66e93174bf1816f1d8a7c9e40480c,0xdc6466ddb8430b773deec700513bc558b4,-0x73fe4743ea3ccc66601cccb35796c51e4,0x27b31a517f736367255c2c0abc3a6074,-0x7e6be9d5ecd8051dda81609015be84,0xc3d0c6974c77e1f1f3d4661a467c,-0x6ae8f9687e5e2bdcee858deb8c,0x9ca207019a6a6c0c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 21 56 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 56 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 50 indices rho q10 m10 10 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 50 indices rho q10 m10 10 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r11 : List ℤ := raw_ints% [-0xb42d666f8b61af9b1e00e7fb6da00000,-0xeded910400512cce73bde5bbe2320000,-0x9446258249c12d253884bbbe2aeb0000,-0x39fee95ec99cd7c32c87fcd19b3db800,-0xff8d1254ad8e93ddadfff379f203e00,-0x34b002d6b7080c7bb983ebeba6c8b80,-0x870b7c7607c9bb919f4c556542d720,-0x1137c517a842cbbab1d77d713a5530,-0x1c6683a4f41e76bf28e34d69d8970,-0x2644161280bafa60ba2f8fe67820,-0x2a5cbdc49b1f53f3000bbf5ba22,-0x269dd8e1bd3af60775381e094f,-0x1cf330a4c0f39837fdff86d36,-0x11c2e3dd4971cba653973774,-0x8d6186c537653bf8bace54,-0x3833b9da8abda8b733c7a,-0x1172f0ba00cddec814bc,-0x41509d94221132df34,-0xad8ce6e1cbfd058a,-0x124613f473872bf,-0xeb6717a7317e]
def m11 : List ℤ := raw_ints% [0x0,-0xc2b13339cacff6127300b58b8c7801c0000000,0x14fb7fb47d110db4e4318b523f53224055d05c00,-0x117e46f263df520fa8135c93c0768c5f2f0d37500,0x96458e7a09bcdb39e7cd91772fed7ca08e5a0e500,-0x3a62977af2bf8d8e9b9a1cbdca7ebef3d10c68ef40,0x117d5596ad4cee3be1d8d0ffd132e51d49840735c40,-0x433cb6e6f986ad21c73f6a00dc0c7f6e8c97159d740,0xd4f89e19b6349971898b8983f4a88d336d6bdea7a40,-0x2368e4deb9d068c5331e9426c1ec0cefd267f3546e50,0x503f0331211b268e1434cd4dcf142fc2f1ac0375d090,-0x9c9885f13a5c59c51bc22d067acd64c5a9c58e970590,0x109539061346d255e9573120b61d3d7be7e693456d650,-0x188d1e47c1c1baa3fa79d021d89d5ab299d5699c288b0,0x1feabb707f35c217ef524e25f9c74a86a6441475d1570,-0x24915d4de32511d291279ac459de8a4bd1a1706bf3af0,0x2505ab044e1e015125ce9a5fb38ae31195159d614fb30,-0x212e14bb7de909f3348356e622949e09804bad9cac804,0x1a595f142b4de4729fbfffe918e1799de08169ddd9854,-0x128b8d36ae4f6d76dde8f7e19c722c022618371fa8d94,0xb900aa364129ddba27fbfd9c12ca454d6c114e301d04,-0x660f28a6195546ac583f4859c224f8c38633a961625c,0x31b88d6e7bf3aff24764e58e58595a6a3ef8a401b14c,-0x15557bd1f4a6a18c5a98e969fd5ca8f4bf9c8cad5f2c,0x808a1cae9d0a708f4f597a3d8abd93b95073f011e7c,-0x2a4ad6c4d5c05a53642798f0ed5101a745b3cf3af78,0xc1756ffc65fe550b6530962805794da7872a9c75d8,-0x2fbc3511bb728704ec8d379b88e77305a55dbc45d8,0xa15021b0cf15f7ecf6d7be0531715d877371b33f8,-0x1cdf243d602441f1559e4567bdd7b8ce8c8247568,0x45347aa2e04fb314a1444af7b36cdf1eecc1a708,-0x88c248a4a66f3c7942da368820a974e57ab77c8,0xdaa22cb9d88c4e091a0ecbe23188053f273ba8,-0x114175d4a7d04682ac02cca3590c873cce16f4,0x10b1344a987b6e9999a329d08aefe2da1e304,-0xbe138bb61c8eda567df9f2446ffa6bac2c4,0x5e3b9468129db99f0908e021f68024f774,-0x1e22f963a2ac0e13a1ca0139ff8d1038c,0x58cbf7b79eec16451105628900d683c,-0x7dbe61015461ff4fee067b74eb61c,0x3ddd0fcc7c021d5ee70f76cdcac,-0x503ffb659f0d824200000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 21 58 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 58 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 50 indices rho q11 m11 11 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 50 indices rho q11 m11 11 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r12 : List ℤ := raw_ints% [0x2e035ed78b68ae1a9ee25a967e2ac00000,0x3cb1334b703f7ddbab1449fd8e3e5c0000,0x25c687714da6cb7c68db68d8b9cc000000,0xec15807be4e0201493893031d6dfe1000,0x40eb59b5f39ec6ca284ed2141cf420c00,0xd5cc4c71528f691006dc3e78c9c2ab00,0x222fcf8f32df437cdbf4115dfbcb1240,0x45991b77ad3cd1ddf3914abde6c2200,0x728ab1b649827764f4e245ded5ae70,0x99f153e9d424eebea34e90dcd1270,0xa9f1577e25c3ce1b5a454981131c,0x9a6d296296fe2392cc2d2b37508,0x735b204d07a0e127fb36d1360d,0x467c2d75e1af1527aa2f5eb60,0x22e74309144e1ddc44b07a84,0xdcce410a5cdb8c93de6cd0,0x441ff9f016666ba9487fe,0xfd21b2ede088339bef0,0x29abaf9ca904626658,0x4576b31a2e6ba468,0x3734f9a5a6a14d]
def m12 : List ℤ := raw_ints% [0x0,0x154b619a522ebeea049413db435d203100000000,-0x2464e54f01ffccd46100c0063bd6756ed5cf9b400,0x1e10bc734efb66528d13531fca282c63860e1d5700,-0xffd70c507d5ac68cbd4379019a7678d0f01c3e7f00,0x626fd97f89a5d9ae31db36b7f494590f80c64ebddc0,-0x1d311b102e007c69634aed30010dbb9143c5a2aa34c0,0x6f102af6ab59f7868ccf3f22103b3fb8986076c06a40,-0x15c053b477f62b36fad4b8dd61ed3e760a36757766540,0x3938e38bac8e57fca9828a2c75a6ad428610823f11370,-0x803031bb2d123fcec7d1e12948108e4e1b35201edc030,0xf72bf99f2ba3896d1d81f949ca0a37d959748c2d81350,-0x19d9cdae825a57d80967b20fe1668638477ebd62c19210,0x25c7cd0cc74c39f0afa619afe208a0881bb88fe39619d0,-0x307542a8e548d2b9ae8e91451bd8583d19d271955b0e10,0x36bed9e366e334c102d345a775dbd3dfa029ebff3f1370,-0x369ea7f69db92c91c1bcba9ec51232073ed167c631a1b0,0x30352dfcc570d2bee824e415fd3cdbf2ccb368a0edd26c,-0x25acadc84e2dcc3a07a9961d92a02320a6d3ac9f8342dc,0x1a13130c1331af3979a7af7632058ca928bd844b2bb004,-0xff90aaef8a404526f5a3fe58aa67f997ca6cacc427cf4,0x8a646ec9375921cc241a1692a6a4b00578d9620509904,-0x421d3b7e6741d84e9c945d066e431a5cb4f44277f1b54,0x1bc9676cc647530fdbeb3d81399498d57af7dcecadf0c,-0xa3c96807f20919a2e50d2b0d11527c19e57f419d17dc,0x34a5f338e208101c5e10fdf7c58c2dc2b80de498f668,-0xeaec5b725258ad13376642021de416e4d01cfdc2488,0x38729a87e7d0ba16f221bc23268f45f72c9a07f87b8,-0xb965d889042f4bb184ecff5149bc67259e072e4cd8,0x202dee6c7fb07f293c92471eab75c72d5f76e26318,-0x4a9d3b492a02dfb17c3e228d4c6d164a341ee82f8,0x8e37ee0dd4065b2d652d77c8c09282bf8675c748,-0xda8f17622708aa5b35598cb48f2b76b1d27e628,0x10843dc039f28cf0ca9c794241e51279019497c,-0xf3a0c1a8cf92175d2ed2543a587ee62f7c52c,0xa453a8910f40c939bc1b13ef9d59f7190d34,-0x4cb19a2cd2ee984721511e295d194fb8f64,0x16e76d453347c52cf14d21cdfaee13e694,-0x3e6724514cbcde91e78b356c59287e24,0x50bf2b78d9153a935fb877f92c2cbc,-0x23c958175678df41db03efcc90cc,0x291a7bc3ef94e643000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 21 60 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 60 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 50 indices rho q12 m12 12 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 50 indices rho q12 m12 12 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r13 : List ℤ := raw_ints% [-0xaca833832aaa7be9a07ebaa798fca200000,-0xe380bb673ed92f9510412cbc5103d5a0000,-0x8d70d2c104f18209cb2b9317ff0ea5f0000,-0x372dd825977f86658edcbe4e2ede77d1800,-0xf27205ebdd7224a378566ba67bc2dd7600,-0x31d4177276c35bc79c7162aa402a4d8980,-0x7f46398985ad1ff1bc8ddf539f4fb33a0,-0x102a3c75a1d4c75fe401145e05203ea70,-0x1a8cf0ea1bdea22a9ee2c3b27d545670,-0x239abefe7145d7c62d3e1ef70458c60,-0x27353be90c1f99ef56589c80ac4a8a,-0x23879abbf316129e23a320d3c5b53,-0x1a754b7db7e03f789992178ba522,-0x101c210616a1df3aea44340c924,-0x7f21703ca2a63172618ab9bd4,-0x32097eff77bd22ebb6598f12,-0xf5b61a01066f523fbee224,-0x38b6e071643a6ff625624,-0x94508427fcc362deb02,-0xf52418767c32bbe03,-0xc0d8584699e874a]
def m13 : List ℤ := raw_ints% [0x0,-0x2543eace0fd1ce19880322bfb5e2f855c00000000,0x3f241f1e9588f39fdb9044a68aafb287018e55fc00,-0x33b2a34cbbf968929468b1c485b49dda324a8382d00,0x1b3e30b10f6564a0c20190fb506e33a138405f91fd00,-0xa61fa3ebfa75d7aa5d990d25168e44648048dc263540,0x30c84ac4d3145409f01bb6ffe786b24f97b2d4c3f7a40,-0xb7b7ec3266a2862daf7cf7c12ec0e1f621227d09c8740,0x239a79081529822504625fac76f77ce14374bc3bf0ba40,-0x5ca5809f86ec4608e4f2950c40965acbaac7a57195b5d0,0xcd350ae43985f1c32ffdd61fec22cd1dd428179260fe10,-0x1870d3929a766509ca0b58c03e3185e1bd8af6d4dc06190,0x2866cb67431c2a8ae0b432c08532690dd4e19a3f3e3f650,-0x3a4ca32d7065d7edc54d81e5ec3acfa5d5bd4682ac09e30,0x49ca7645094a3e5fabeaaed598758382b3b483cfb777cf0,-0x52383de3a8b123884bec6116bb7364439728d7e033763f0,0x50da7cc66b189842de31b952c3ccdc50cb56a4827a2c030,-0x464a5d0f231187382c69088a96061b8988fbcf1bf281364,0x361182a473bff188854f93e0b199ff6332e48907f58b734,-0x24cd9de7c0ec7eb50cfa20f15baea8014008c2c172fab94,0x16276a202c8675a9cb6cd14971cc9e18e4f24e8a719e804,-0xbc70c66e8dee158ba862d4365b51776d825359b18b0c3c,0x5849b9ceb58f355a3566120d99855448ca078c9a6bf1ac,-0x2459695dd88c9a46549117f8579c8fd458a3e753be3d6c,0xd19fde2c93fe0863ea6dc9fb240702ac203eb30daa7bc,-0x41d55128e8196f947bdf891c8e28f32eb14183b0df3b8,0x11e8e18a052305b3a67aeffb9f13653bcfdb95d5c2318,-0x430c5b3c77c03c72ba4c08e74ba502193c5e635ff8d8,0xd6041ad8b45b8e620585282cccdda1792c62c5684f8,-0x24051db7604a5b02281b49b04316305484d07f0f7a8,0x50c72f766750d29a39b0b9330eea3d1874d6191848,-0x947921ce798f6b8037cb190bc6b22e93060903e48,0xdb4610aec15045f257115e7d19d8f3de1f780c28,-0xfdc460b8aada6ed7626636b7fc59f9d3cf6ffd4,0xdedcda22666fc1d7649175364008c178b8e164,-0x8e63e1c93904c1f86f1203bcc19f502d0bbc4,0x3e8670253e32c01a05bf7415dfe92945d174,-0x116d02b8d4486c71e5912ff307f8e067bec,0x2bdfe7c9b6365d888093db5ea312b591c,-0x33d9a283815866208f3afd370589a5c,0x14b1ff95134517e9bccddff618fec,-0x150bfdf9e36285348000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 21 62 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 62 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 50 indices rho q13 m13 13 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 50 indices rho q13 m13 13 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r14 : List ℤ := raw_ints% [0x25b1d20b5b607a5607db478aeb1bde2400000,0x319f3b874aaa4428912fb18191f8a77740000,0x1ed1a3d1a6964ae9007771c495c3b2aec0000,0xc027a94f78e7f6bc648919e3eb6b263db000,0x34b41b6b85d49064143fb0e0df5066be9400,0xad13ee6de77b809be788cd3cc7bd97d9d00,0x1b96f1beb66acb4e412b6630397f5e0f9c0,0x37f9b78f030b8ff8e701013e433b74a2c0,0x5bc637fdc43e51592480438b8a3794770,0x7ad3d200f18f47b11c5bf9a94a510a30,0x86f68233b698d5727bf39968f00e0f4,0x7a010777ba39fbfd05295b6e4473e4,0x5a9b50f261ce1f08af26b819b2161,0x370016a2cde7cf6969d397f4cdb0,0x1b08a21b44d70ef28bd51563804,0xa993dddfc8eb50d140aeb12f8,0x33d030c3761dec59e194a596,0xbe5e62419630965549e700,0x1eedfe0a21eb189d565a0,0x32c412e14d8904dea84,0x279b59e1c30e80541]
def m14 : List ℤ := raw_ints% [0x0,0x4136dae89baf28acae057ccf7e4d32961000000000,-0x6d9235cbd01f5c925449b4ea1406a2e4c5f03119400,0x58efecfa077516f548bbe9e879c038b58d2f9f2cbf00,-0x2e72b2e00d1ef4b96712ef8cf8267300c43d92fb68700,0x1189e12eb9b536ef284552488c5806c46e74bdb5d11fc0,-0x519dbc31681427cbce03d523c122ce64fa8427703bbec0,0x13054da06e792d6fd5d1652528002c2efbaa1fa2072d240,-0x3a5f614ff65e22df27ea040a8b553522a256d15729e5d40,0x9647b8b29ddf60d06d8b8a4404fe1c99d9a26240a7e0df0,-0x1492fb40e7b69d8ead0dde98bdba8f64831d8af9343a3cb0,0x26c1c45a797f07e0e33ea45c0bb7db067a384da0c4f6c550,-0x3f4d338ab994ac33f61dc25121f8ba9af064ba5f287fc810,0x5a3527e68317bbd924aec4769458cca83e7590d761698a50,-0x70b24bd40604467d25826ed90d8fb4ce08134ce482b02490,0x7bde35429f5d15645e6fb884a9a1e6217943c2d216e86470,-0x78157e17d0d35aeea263bc5c052af96703d947bf7bcd2eb0,0x66d8cf3a939446fcd86c7c86588831e7347d718b0222e58c,-0x4de155696c3c8190e734ecb241cbbe1e89206249727cb47c,0x34250d4302a4a87110c9a4474a05efd7c85704668ad92784,-0x1ed94d2d7a32db0003db96d4a2018a63eb7fa49ea14c5174,0x101a33542a929f1f3692af91055da81b0fb642f286c3a6a4,-0x7664c40f2104cf8aace44cd82813432e1d56e21e94ac874,0x2fc114272a2d65e67990eabce49a83c6c54949f39321d4c,-0x10d75471cb2107fe872d997ea32aedecd7579f3bd87891c,0x52ae827c9b1f32f8b7913a2a4670b45a4fb3c5d779fd28,-0x15f123f85bd5eadb05f66296de189aaebbda5932dffe48,0x4ffcc7b8f44e8dafddde1852a5000357ee539535e21b8,-0xf81d0d49187e172e22ea143d080cffd770d2639954d8,0x287ccc4506329616a28448a4f86eed55ebe815e4fdd8,-0x57cd4dc4eb6ecce0ed61653f86e1c99dd02142832b8,0x9b96d75fdbd85b7aaaf6aadf64cc13bad99642cbc8,-0xdcc1fe9cefa1697b3d1168b1469a4fe17ae5a94a8,0xf4723309b0386193dfe58b30903a139da5e1dd1c,-0xcc69a31dcec48e0dd0398ec42e59e5584c98d4c,0x7ba5ef5106328ee9c9b39529c4b50b1ce89bb4,-0x330dfe5e06832de0f95e50111c6b0f903fee4,0xd45553968d4354c82047a7df9aba19523b4,-0x1edc246d1355c9da8c0e2c3706062450c4,0x214ae9752194d0a0cd973096a7f736fc,-0xbf6e5b50d4de7d6d4c0d3e51d220c,0xac61f909545cb64c0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 21 64 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 64 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 50 indices rho q14 m14 14 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 50 indices rho q14 m14 14 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r15 : List ℤ := raw_ints% [-0x7bde556bc4efa3189e2064c507b97faaa00000,-0xa2ec6cd2eb0f6fbc1b32b6297d02ad83c20000,-0x6517d712269825f5638b1f924a08b3c3730000,-0x275ac01157893dc1a0700911ae9b5750af7800,-0xac8334857864d12f831d69737a56da4066e00,-0x235d7ad12f3e83ca363825c10b84fa028f780,-0x5a1434924a2bda80e5e33d794c134f685420,-0xb67dd0f2558f6c129ac257493cb7c8ea9b0,-0x12ab975f13492a48bdf7be620654eacfb70,-0x18f18fabd46fa430ef59f5e6eaf14f4aa0,-0x1b5acd68e6a0a51f62c1c2d665cd6ac32,-0x18acbf42cbf544d06595949fe41d1177,-0x1247e5c72950fa8bcc978f76471886e,-0xb1131cffd624a0b4f02695dc6e854,-0x56c62bf9c4c4fce283235f01d154,-0x21e79a139950b2c95e7bc820e6a,-0xa51d08736417c1a1d999602cc,-0x25bfe48db00c15fb37975c94,-0x61a38c3f7e89d7568c423a,-0x9f532bc9cd8f4bef1767,-0x7b74fd60c7a649d776]
def m15 : List ℤ := raw_ints% [0x0,-0x721fff171072872e30899a6b1d0718869c000000000,0xbe2fed0649d35ec2ed575328d347f4bbb7d152da9c00,-0x9912899be12679cd3ef08e96d8429c31821f8aa382500,0x4f3f43c0a97027a3d9d6d7fee7e49b11dda4e4b5155500,-0x1da760d28757a97966f8686c53b5a23f54a628004ec0b40,0x88b50465ba54a2ebf6bd7321a0bba6c3e3a59a2bffd6840,-0x1f8d35c23d16582a1ebc43842fe8a2c09354355210109740,0x5fdb6a863a0d114a6b3f555f278d4aad4213bf6b53b65a40,-0xf43689c969d61887ea0dab65b5f3200f7d4caacc1c011150,0x21126f6afeb5bf1f9fdab4b31999e35021567c0238ab28f90,-0x3d9919ea9fc06b6ed7517632daba807344e63b06700763590,0x636d61710a2435319adc2ef13054f8a6b4d0ad1d879db0e50,-0x8bf45486e085113b6d9356cdf9ffd03d933977b0de096c7b0,0xac9c6ad5e3f6bf2c9a3bce2f95facca64fa94de9b536de870,-0xbb2ff8364d972343b4a401fa277fe928bcaa978707a9ebcf0,0xb2ee5a6a0e00e540c70e766b45ccc783d66d216675f62b530,-0x96fffa73a55a0dedfa76308e720f6c1cb640935a22d3977c4,0x70954523f740dcae1ca09d3efde02c084fd2c4ccf4b5bb314,-0x4a28b9e64531300e6f355e0a3a980a4c90e39d34be51e2794,0x2b1fa779eea58cf412611b20fc5e3cc675e4b17b54096f104,-0x161a92d350842040ccab6244d8fa3b58ff302d2a7049d671c,0x9f6b9a49eb69e909264cac127f4f3e8fe8d7d00332ba4f0c,-0x3f00781d2746c1d3aeaf12d6ce9c4c90fce9f9da724c8fac,0x15bd9a4ef99f6255a338e365b2c7c55b32c0bf42a0dca4fc,-0x684a073cb5b3abc76aca9ba93bc676897c1f4a78615ddf8,0x1aff73e4a9d41d2b18d41be20da7950893beee257b0ee58,-0x5fd4d6a126d7c5fad1d1891df28169810e2992e1bea7d8,0x120d9d49f5c7158bc0d47625232f0a4af659dae56851f8,-0x2db1cef5e8fa4e6dc126774588bd3fc5ee98277f9f7e8,0x5fcf0d0146fba2c225a9669fcb4d21d9c06fcd0fcf88,-0xa3a4d0b0020da02b9c0045470a79c0338de789224c8,0xdeffdc91517352717592377acd736d5f6f58b53ca8,-0xec2c010ad4cc67d20db7167346e0d9e72435d35b4,0xbbf7b5d6dbc5a2dd6f52e582d85bd6f9d38be0c4,-0x6b977277baad20fc2ca7da66d8cccc265cb32c4,0x29bfef2f2404fe953e20d6c3062c8d83834974,-0xa1d90ce037e6a0725e09bc03be10e73b014c,0x15b6924216071282f015374b62c2a87b2fc,-0x1560077f614f37ba6c50664360c18ca9c,0x6ea3229f3d7cb3470e22e59dff4f2c,-0x5838055f35169f8200000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 21 66 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 66 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 50 indices rho q15 m15 15 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 50 indices rho q15 m15 15 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r16 : List ℤ := raw_ints% [0x1821b16798cc7e171f3c8167a64b03e2d5c00000,0x1fb71cf49dbf886245a6b1752772a7cc714c0000,0x13a9918e0c128d1c42cb2de9b3571cc403380000,0x7a5b2a8873bed52381beb7a2da5909a5a1a5000,0x217d00e90c9367d87da75739ef3fae0a40f5c00,0x6db88b5fed3b58c348dc2e629f7b7707f81f00,0x1172287b8fc11235b2c5d72bcfceb364891d40,0x234c1c78608b2ee0f3837c8d130f8fcb48980,0x39b215a2103b9d38d978476711351c9b6870,0x4cf5a90bdbf1a3e720fd316a86744060ff0,0x544061e39ad26b93191a84cb9fba862d8c,0x4bd9e5e16d636ccae575915335263dfa0,0x38137de247b62abcc8a230558bc0eb55,0x21de2cb1f45466b9bf63f8872859280,0x108d85c00ce30566c1dfcc56771184,0x672cbbe4bb586e53435f90f29660,0x1f4c7141137d7ce4fe0a42447ee,0x720f3b871311e3dda09b9df90,0x125be82c43c835b29d97bf28,0x1dcf567e953103ee202f80,0x16f79257193c3d190cd5]
def m16 : List ℤ := raw_ints% [0x0,0xc7b7fe685cc86c90d4f0ce3b72cc6aeb910000000000,-0x14a30f7e7bb29f85deef283991323c039af563bd0e7400,0x10793dbbbdc3350e7f8bd9f941acf11fdf17d9cc0ebe700,-0x874cb09a1db9344f7497718f5407b9d66e8c2bbac6f4f00,0x322efee0ffdbf608732a4a9b6ac70a5811f0e97ea46b91c0,-0xe53e90434696187c553e5dd4051c86d6685e7031a54b38c0,0x3468b256e57858d8f21fa89b68869595d5ff28fde4577da40,-0x9da951b0b13e3618cd6ddf2ace2182f2520ba824157abf540,0x18d92a931d491d8164006cc5669b10f94f2722c49033f22470,-0x3544d739f22bcd94f0ae794a894693f0ba9ce86951a9960530,0x621e5caf0140fdb207cbc4db8c20dd915dc72499aeb4e3ff50,-0x9c8cd062cc46f4f2d97ba3f3a805445d665045595b45204610,0xd9b54642abc50eb907c6ddceb17db4e998819a5e5877dbd6d0,-0x10920f6ae097f542f8880d005cfe597318d90f453c6a294a710,0x11bbb2025b049f343d932af6ea47928f5b2b61993e3aa442570,-0x10b78d4e50b86eb2f9ad40338bc3edfad3a82a0f9b75810ebb0,0xde72c33116963ba7390716c6c3b8fa6770f49e35480ece9bac,-0xa353958134ef86f6586d87254e8ae8b1a87c6fcab53798a51c,0x69db7b9212023f511ed6c6812861d7f45c729aca9c05c06104,-0x3c838688f29755522703ef9d88142210a495938a9d65e617f4,0x1e7648aaa0468dfd0d42a6b3209846a611c3fa9b4883a70f44,-0xd788ee2b8f3a626c31ff47713c6e8e9bfa95f505e2a3b0494,0x53763ed6234f92c95c8c0e3c6f59dd66bb1b53b99a9fb2f8c,-0x1c2eea9ceda3d28e49b800bbf54876645962cc8df7bce3e5c,0x84195da0397982efd16aa1daad1eefa96a68c5d803e445e8,-0x215be617d56ec13d5884669d0c64cd0e6da8c6efd3706208,0x734b3a6072a9ea0f652447ab7bd2306ed0fa2e1c9ef5fb8,-0x151a7e0312d26de16888acef91eb1afab4830ed749060d8,0x33c6b16562009ed06230fe982696f5673d371bdc914298,-0x68f127023f3e708a359a09e9927fa72681268d35c8478,0xacb9e704fdf8a43c8a515fe719eff73f701013300048,-0xe1fe8fc622d61ff4d6e0dd29eb73fd86b155d18d328,0xe4d5081ba3d1737871731f6258a0a505f32c8a4fbc,-0xad43b77c81f71c74729eb458712963dd7efe1a06c,0x5dcca9e751d05dfcea1ccaff4001e2098835ac34,-0x222fee6e46924572f7b0fc8ced9d6972c82a064,0x7b76fa96fa32121e944cd0ba0fb63388b6fd4,-0xf4823f4f2c99eeb76d084e584c3f733f664,0xdb8dd4989f0d7f900f027a81ce8a8fd3c,-0x3fec5d41c1af913698612c16c18df4c,0x2d22893b972170f3000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 21 68 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 68 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 50 indices rho q16 m16 16 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 50 indices rho q16 m16 16 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r17 : List ℤ := raw_ints% [-0x47d413f5e89a1abb05f240abebaafe8490f200000,-0x5e555cb5b7887cd493dec2318e94565c4856a0000,-0x3a700fac8940ed8241abfe8b91d116cb189270000,-0x16b5739fc39021330ecfc8a2cfab28bccb354d800,-0x635a5372dd8f77f925da030e8ca6e2f4f64f2600,-0x145312876954f5493fa740b48b88b5a03b5dd580,-0x33a65bb2c9e2c17d67371b22b8847ae998af8a0,-0x68600acb7872df9e0093e1f8e0028d756222f0,-0xaa628503c56e9837e599894b4128d8b382870,-0xe2f30dbcee3fc7d11dc2ca3febb77b857ae0,-0xf8100b31176633d3c14eafce736a9cb531a,-0xdef1946cb298a629f543cb18dc046094bb,-0xa4819b1a3ed7391d8badbe9a3f428581a,-0x632560338baf7a21150a12c686edd104,-0x305803c674a57a009c1667bab28f2d4,-0x12c8b005d2dee5f64988f724a41082,-0x5ae79baaf8673857e6211ec58cb4,-0x14a303c74d3d1402ee5f139a684,-0x34f30613482227c44c766ab32,-0x559c5672465e904299677eb,-0x41a37960611ee48dcc302]
def m17 : List ℤ := raw_ints% [0x0,-0x15d81fd36a25ebdfd74a568e808e5bb1c3dc0000000000,0x23d62cc36015c11eb407bc2c9a1da660befe244f0863c00,-0x1c60f9a0fd2faa22fd3579a45d152717a11719b12ae15d00,0xe72745b88b5916a59171e2b5de097fdd11365b17ad1ced00,-0x55008eb1d087b41f3d131ec55a4aa597176751e878637f140,0x180d93b94881f937c6a549613480bcdeda84bac42d5cdba640,-0x572b9b814b429ddc26674c15072afd270ee9489d3a476c0740,0x103b77ce136bddff49f48d5abbb21fc45cf5197166d19a45a40,-0x2886210e3a84bdd01f2479928eaf3521fb1a461701b622960d0,0x55f849181c656915c5a179a76f13dfaa7184df8c2fb6bffa510,-0x9ca2474f3f9f9485ab5e41dc1de2bd5788d290da74bf63c0190,0xf714d2ac53341a7ccbcf497ed52ce6478d8cfd93bece0e95e50,-0x15389bc68537c236e7309605db1a167f3b6877e63c68011e6530,0x1985f179e25d698acc3f4d6f6eabad2983431e610a59a4fb77f0,-0x1af5940b79794ad4b0a049263561e24e545d6cae1a660c0005f0,0x19116b47b5875fc5b9ce96d1ee091af1f583452b35fb49f5da30,-0x148cb799b293039070a58c133b02e77f2716505723d399600d24,0xedc490f314a667e650b312b81ec9345a6fbae84192e0678f3f4,-0x97a780e2b9ea4cc97c163867f40b2f3b3edb3681ea698132194,0x553caa07b0b40528d8623a478490f288a3151ef03b96dd80804,-0x2a24e63847e9c0e718acfbfe81c74a08dbd74cc4893bb26eafc,0x124904aa2572bbe4666ba5e68fc56a0878af63ed53c02b1716c,-0x6f041bd76e4f98d1ee47d43cef5edae77dfd4a862ddfd485ec,0x24af845f54e2abb5a366386499cce4e68a5c0bf3eab279163c,-0xa804aa3effb9ad73f711b7bbb37b3e4537c9e64ad7f52fe38,0x2963ad774376b0832e334bc687d40f199f6731fa42ef3c798,-0x8b46c7887bd9397745002cd6b5c30bcf5620225be2b8d2d8,0x18c4996403426e71d30994f253bd66e83069aa815071baf8,-0x3ae4e96e4ab2d2e4f8a456ec61f565d48ac38a346110628,0x735e7f8ec92fc6e15eeb7e61a3e99a84fc3b3f64537cc8,-0xb6f06141e89808bef0049d7c965a84bd1e90314a98b48,0xe5bec5a1c12c7e2bda599f203f93a9c2882675cf0d28,-0xde54626cb0f44a02e853bc114bd1187d399d3bf3094,0xa014558623b6e5aa8b33bb578cfba04626e9536924,-0x51ec37e22ba3dda522e145863a59bbc3fce0687c4,0x1c07a983c5545049f3357d8f2a3d4f7f32d8af74,-0x5e40972f20c7308feabbb7622aab96312dabac,0xac204d3f88fd1c1c687fef138c6fca957ddc,-0x8ceda9d0522c8bc10befabd1b8dcce76dc,0x24ec10bf885c24dda1cff9d8dd3d5a6c,-0x171608f3256cc8948000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 21 70 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 70 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 50 indices rho q17 m17 17 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 50 indices rho q17 m17 17 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r18 : List ℤ := raw_ints% [0xcd480ef50d723b5dd1880c23d76d6b5a53a5400000,0x10d6bafdc43828bac0d200f23aecebbb6e8ede40000,0xa6c7e5d066f779645b30f65df3a1a93aaf0be40000,0x40c29b2b7ad293d9cdd40d1bf8137fa2356f0bf000,0x11b175c66f2a673f9806e7917a777a1ebace126400,0x39dbc13a41a84d9e792fcc930f2b85e6f0a59b100,0x92e2df925a240f15c6c9605e0f23dead55819cc0,0x12881fd8019fffea86c63696aa6ac52aabb88640,0x1e373d54edd4670b7bad57d611fbb4be8c4b170,0x2831d3e4b13b1073fda49085758f0de11383b0,0x2bdf2039389a49bd613610f13f18a235652e4,0x275e21d60ce531f98016ef21c2841da7cf3c,0x1cffbe20b6b460e92d12c1de7861e893ce9,0x1171c0d7a4c915ce03a324f1f16a858dd0,0x87cf69152819dc753eaaff7a43674f04,0x34a587285ec7cb4ab2b9390516d2108,0xfe1ff6163be44b60f20a3f2235d06,0x398609353b8ec5955ed616bf7ca0,0x931cf1ade1654bc54f3f1cb8f0,0xecfc36ec5c0a37f516ed7a5c,0xb4f0ac609090d36c617909]
def m18 : List ℤ := raw_ints% [0x0,0x263a37b1f9c25cc7b8c2177960f9207716c100000000000,-0x3e3eb01e14ff48c23480540f50fd92b1eaecf2455e285400,0x30e8bdefa7fbbc7b6bc71ac9da790d5631d24e154d9c4cf00,-0x18b2cca1e74aa76c36ace4a626743d659f929902c685e2d700,0x901ad4a4effb5d0070b1dae0bb8bc7683a5d8825d4733bb3c0,-0x286c73710a3694083c22a5356e7015a22877538467a596922c0,0x912d7f88cd4f5007f25ab30475a1424f62a409a94bf29268240,-0x1ac7c2f9052440e9435f452a2f98fddd8ff916252499e3842d40,0x42340e098086e77091a38225b629e85ad2b7e7d8c73c27b4f6f0,-0x8b03f1d179d8a228131be53f348ddad77fd721adbabafe90b9b0,0xfa95971db79a842454662b2c82b4119d9cf60658f53439c28150,-0x186e25e1961319eb22fe32c78fa5918837e263ea41b2d63034c10,0x212e55e3c25a3b1e47fe7bfc7e2bd43725ea7278da97d22d29f50,-0x276bb2cc6231c0cd6e61d8ad1aa2c558f5322d6d8a90cda743590,0x291b07ae22249534c64ede9d02223fce61296ff066df2672cd670,-0x25b52c3914068c16ca064ab29ffb59310c4bc0a30079e458dd8b0,0x1e79330e3f8a16b2ceac8f7ffca8a068c6f83eb820b0911ca7ccc,-0x15b53afe02f3e92ff597871a816d2672f52f65e5ee7f4fe289cbc,0xda0ac6eb23e5096cfef804df55514f0fff49b3cf9f43a8c50c84,-0x7881aa3394742e178f7dcd4a6199689294dcc2a11e28bf0b6074,0x3a8783744127fb2988a6c67c5866d0d2daf693dd80bf90d49ae4,-0x18eadc14eece78ce42f93ef80b771c172633a87a5850b06917b4,0x9441cd1a11c083be174d1abf61240f2620d3b19caf5222cf5cc,-0x2ff2352320b2726b791ed4f0c1e81c0f87d73137dbab312379c,0xd692af5dbccf3227b84459dd2991993193356f6940f48380a8,-0x338f9ed79426a8c330c42108a0ca8534c29302e6426348ffc8,0xa8ebdcc73864b18bfd297b56560baeddcad59f8915315a1b8,-0x1d2eb48137ce5a1e90a3539479549c62a22737122193c10d8,0x433e4eea8502418dd45f0c117139606092b3bb90fca8a158,-0x7f49360a2a529f68971d7c5693420a478f8724cc3fde838,0xc26658ec852d8cdf28f67c138c0a0a0fe016a20a29e4c8,-0xea42da7ddd3be24b738637c74ffaf14347268ee53e1a8,0xd894726fc82d51d1a0e2254b949fbf07f7bcf2dac95c,-0x94389f99038a796d88749ffc67827c6c1139f1c268c,0x47abc0180ab93467c57a6690f82ed1ac85be85eeb4,-0x170226ab868cdb434460d84efb3f35a25835b83e4,0x47ff8b09cc16ebecb247d13a754b8e5aab072f4,-0x7931a32a08b1719cd0b8ff60607fa1f0e9704,0x5a7252b26ed14563f4a584167575fd41f7c,-0x1551e5071a418f1dea0204c24a5e5088c,0xbce272bed6cec18c0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 21 72 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 72 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 50 indices rho q18 m18 18 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 50 indices rho q18 m18 18 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r19 : List ℤ := raw_ints% [-0x235e1ae7b84f2896797cc6ba170a2cc1d02697a00000,-0x2e63bc9d09e7f946225bcda5ad5588a8e559a4520000,-0x1cb29fbf2193041b168e55e473fe8172b7d1e07b0000,-0xb229bfd3fd32f2830f675c9a0958fde4d8b9fe53800,-0x30a365137a75364119061f11fbafc98f2c1e35d9e00,-0x9eead9dd50dd8d92c820522b3b7b50bb18f959a380,-0x19313aab5e705957deb48c5675b93373197efcc120,-0x32cd97b0e4a5062ca7bdabbafca04efc966fba630,-0x52be7ccd9b19f9b589dfe9ce30257986467f5d70,-0x6df0cafda464669053912fdf7ecaaff76198d20,-0x77d7d37d7ca8e489a60046aacecce4ab0e4142,-0x6b636322dde3735be0a1b434784caa1bf761f,-0x4efb5cea3e3f617bc82452f92576bee34f26,-0x2f6e4acca576221dcbdced7ebcd80bd0f34,-0x17092dde64dde55db8dcd7fc0afd6cb054,-0x8e94cc6e458ea1843ca7d5405dc4bb5a,-0x2aea8b268b38e31f595fe874f5519dc,-0x9b08d58303892223536814fd46ff4,-0x18b5bb18a462b509a43301c18bea,-0x27ad6ed58278266d1854bd208f,-0x1e2f279a396ba038f0ff3cee]
def m19 : List ℤ := raw_ints% [0x0,-0x42e5e1777514225d8353a91469b3f8d067d1c00000000000,0x6c230136706d4bcce8d24940ef4818ede387fd950ee40dc00,-0x5453feb40094ab7e1e87f66d02d89ed208bf5e94bd7fc1d500,0x2a40481f3cabc96a6c81efc4e0f5bfa228ad20b8a8c4dcec500,-0xf482f4812cbbdf3665b62c2c6f8ca79e78e5f962ab3259f6740,0x44024a5fc0e5268a258fe7fbdb464cc89d4c4241d031a2e1b440,-0xf218b988da591948b6be64595360681b0284ebb620749745d740,0x2c3faac1b55247607b74a2c65fa1ac5af7eaa88444a94157dba40,-0x6c56f9c935cc78c5969345bdf775785f6f829c4411584bf108450,0xe138967872e28ac302763b723845b6f1a953b540511ce6b269e90,-0x191bc2894bd04c5859a5e4c72effeb204c2c95de5d2c6e32bc8590,0x26bd014241b4129b518acc11f2810823dbe5fe0ca21d738460a650,-0x3402efd7da52270ac8402003b537b01787e2dff9c6a71513e056b0,0x3d0cbdb71061628ccaf864507c586503a39d83bcc1c9af928a8b70,-0x3edb0261a292b55a9e8f74f19ed2c0ae04377cee22de1c4feb3ef0,0x38e4d723584c333d8b0a67cecc35e99ac19cf7ade5baca0f092f30,-0x2d55d1165d5134b7063736066201f8a94b26670ade78f6bf352b84,0x1fd155b36fb70704cdbdfcc81777d8414945a1c50557a240b871d4,-0x13a988f27e89068841a3b47c07f8f79d66fe0ebaa9a12cbe0ec994,0xaafdf53a886c9ed0705318d948bd535e50902565b5de3e2541d04,-0x519743fa3ae781485fbb91ca22df0da91f7fa5416809e8e35efdc,0x22160b274d9e37a87e09d3f092776ecfa143095bea39e0f4d90cc,-0xc6c4aea0692c6bc2dab5a6ed0b23363085955f20d8d22d89602c,0x3ee9750078b5a7983dee1139be9f46bb7f2ac741ff906e917b7c,-0x1131ecb2359c6bb94b18f787f56c4b8f5f5a8e4740ffbaebe478,0x407cce5f5a95b8c68434e96bff4f3e88b3e7d5b0831ebc5fed8,-0xcdadb411d28306fc343887905224fa4dce05007d2dfc7459d8,0x2283d92e190f43c8f9d96c27de02b06d5097c1a6b4b0e91ff8,-0x4d0ee76a1c3825916d2bc8980c1a9bdcd0d91021209477268,0x8cebe9f09a95027ba78c70a9cabef9abc3e1ea0a273ab008,-0xcf3e2f9c090a1db9a863d60b2c682347448db8c5c9cb1c8,0xef8ec7b35056a6be1b19d16526be61f2ef24e4c2b33da8,-0xd38266c47caeca51804371963adb06110da9ae0f02874,0x8986accabc7c6dd580eb5380c88732357611116ed284,-0x3ecd2f9a429f6375c84e26924aee776b83ef25d6ac4,0x12e82387df6f0ca6a29a95da3d10cdff999dee7374,-0x3707c53f680f66e771d4562e47fda4dc9d1b730c,0x55584ea3d3b38ba8fb38bc90fee67bdbd111bc,-0x3a09d9fb0f1f1c5f90008d713ebf300f9f1c,0xc4e9e1780da11aa32322a47d050bef1ac,-0x6090532faf5f9d4200000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 21 74 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 74 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 50 indices rho q19 m19 19 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 50 indices rho q19 m19 19 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r20 : List ℤ := raw_ints% [0x5e664e25409ae5a799296b7e53423fb55fd8e30c00000,0x7bbf8e2b8bc07924b15a7aa0cd14e6911f72fb33c0000,0x4c81bee3550612f3c130e9708b0eb1ad6ce77e7f00000,0x1daa8cc76b5f86d40f7eec93b716c77e5d499d8fa9000,0x817d056250e19934813ece774a59c7c116e92e49ac00,0x1a6c0c05e7ca793524aff67c6b0b0eb79e5759c6d300,0x42f5d518460ca9d210abd1c675823b7ea94e9e65840,0x86e8d9d4eccda38176fa9bc2680e40ec59c2b64900,0xdb831bb38ca7c5e69c35961d98e91edfa853b6270,0x12358e1800b7d37568d52c7bff60cfeec34c91570,0x13d3747ad89baf88a2383b62cbfc493f754d66fc,0x11be267b82df8c459cd1051e394facc4e0b91b8,0xd07fa27ac990776554cc19fab3a47df77db1d,0x7d04538a69d6edb0737522a370e948fc93a0,0x3c9d673a435bd156d34bc4d1bac2a3d3084,0x1767b0eb8bea3e7ac23bde4b44b71eecf0,0x707c3c9a27280e98403badff6352cade,0x1956d8f2612c390fa30f2abf0598230,0x40746bd9195fd2eddf95d2267a4f8,0x67344d2629a350a841f0bddca18,0x4e431a43650c426fb8422d6dd]
def m20 : List ℤ := raw_ints% [0x0,0x75124a910ce33c23a5d267e3b8faf36cb5af1000000000000,-0xbbe734124c75d1b2dd47e391fb5b007c545fbc3b8920d73400,0x9175317be18448ad7c5943057b8afa3e2b665ad9c8e49717700,-0x4852dad5b864fd6f369e4ec2648b600c801719aebf774ee31f00,0x19f3a08c55eb2e3a7d8fc80150b7f6fb0c06b0e266fbc5bf605c0,-0x7289f19376ab468ecaf9df9bd6e99831c8d672514f271eb83fcc0,0x19439d049bb6d7f9a989407787318ec48544232eb47b46b297ca40,-0x4937fe209d99832f931da8d8e7b44370c57a8b9f5abd7d15980540,0xb19766c9117871a611abf51d467eb42c30f470a1adc078e9d12570,-0x16d91b33c0ee481ac50d682db06e23bc633b006f8986d2c46ab7a30,0x28565a359beaa94150afedbbb7de2a3daa056603d5490d181638b50,-0x3d90dbd3ededc9ea2fcd07a2ba8bb5be319ec1a5d335bca34d01a10,0x51bac5d9fa3d95e07769b76fd5cc2ac83f71e52ed84aabf38ab83d0,-0x5ecc11fac3afd53318e7cfac449bbc077a42af4c5de276454c7f010,0x6062e868ab346af4c6fef86f1b6fb9d83b5c04630e1392987a57770,-0x5619bfefd75734cabe03bf74943adb1d53789962a7e127275dcf5b0,0x43a8b5b7cd92698ba49c4c0ea2c11f160cdada4d650e75f64f2d0ec,-0x2eca7911de334209c7d67c16cba385e331d0cbd99facd6253e0035c,0x1c77abcaff0bb262b5a2eef28e5b791c90dbae30f0e025abf7afa04,-0xf37ff980ff23605b016fc952b3aa0bfe1bcaef97334953bf2f7af4,0x7228fed462efa6cdf2121e9f2091ca6647793c5937b4f12d4f1184,-0x2ece2c4bf6715fd3797f40c94129677a4fbd3626470dbee12629d4,0x10b8472e4e5ab887eee2ea32bfd78207687bddfc4c89117f1ff00c,-0x52df09b4e3eada0f4fdcc5a95348f39e6d450c69031ad65b174dc,0x1622217342ffa6dbb77a85d503272cf18ed8c7c9ea816a6a6dd68,-0x50f7fa6aad09bd5c1a4389f486ca59d939de485b9ac08d92c788,0xfb64ccce2222fc6849f978b94c1b44498cc1f0eaa763fdc07b8,-0x28f96a3c8336d93f5a827d5928b4053ac0f988cc528b30a84d8,0x589f19600ef0b1fea1d214e761e770df65a8597e59cd258a18,-0x9c8b3bc3653e68a85bca515d431d8be9ffc00c24468af0df8,0xdd9f16c95863ba55221868b3c86d3b7fd181affdfa2bb948,-0xf5a817fb73bc90d7a38377d6ba61d34865ba9bdeca20028,0xcf0dd24114655eb1e1c52af0d76ca74acd44487b8831fc,-0x7fda7dd012b8759150d3a32d0dda07a55c8867088a7ac,0x371c8b8d315ff6dcbf47423d5970193a251e33b7b334,-0xf8d3e7abf30a7d1b5cb9c63e4d01b44c5596147964,0x2a153a0906a8f32a1394fb4c6fe5ab3049539d514,-0x3c1b46582cd5767487628249bb86e839aa3baa4,0x253c73dbbfbd32212d155f303981610d05dbc,-0x71a31293bacf11ad39b3a3c6bd0f72ddcc,0x315ab89eb0cdebe3000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 21 76 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 76 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 50 indices rho q20 m20 20 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 50 indices rho q20 m20 20 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r21 : List ℤ := raw_ints% [-0xf4c2d23e64ea1ef504c0da31b5d5a23e56318a64200000,-0x140b02450311f9e35def7129ac8a2db721763b79a7a0000,-0xc626c50f7070ceeeb7b6e2b13e28f7b265e9b77e6f0000,-0x4cc9b3b4f3a5966224c60da813da3221cb41af4e789800,-0x14ef1ecbf3c2166f001f64d4e6903913164303fa4fd600,-0x444be3698e3b6d9ea838d8a9127d166d374b38b0fe180,-0xacf24c5bb6014dedbae114c2ed460f6c6a455ebfcda0,-0x15c2798c9fa115978d05cec78a0555e440e3d9180370,-0x235f7f167d17dae0d895479efa65e74cda093515a70,-0x2ee70356db7f15a01b925d0b1950e3faa19a841160,-0x3303118cfe02bc1c41ff98f5984c313e3012540aa,-0x2d9936375a8a20877a41ade3e8ac59f2f436cea3,-0x21727080f04f5b46e6ad44ddd19b7eddab5c892,-0x1406edd84800e22015c58ae92e9cbffe4d4ee4,-0x9b2037e7de9c110b3a8f2fb4095eabcd69d4,-0x3bcc44c85a188d541ffbdc323768f92e4f2,-0x11edc3e714a5ed012e17ea50eb2d006444,-0x407d1429e82fb9f8a04ea41d6f6f74e4,-0xa3aaee1f0dd08acbb1b54766f69262,-0x10567bd8af85d7fbc36a870d5da53,-0xc5ac7a15990c970b420f93783a]
def m21 : List ℤ := raw_ints% [0x0,-0xcce0027dd68da93e623035ce83b729fe3df25c000000000000,0x14693636a22d23cfdb91a1df20d67e80cde1b7e3077676b27c00,-0xfb00f10eaa57b9899b83dd1a900bbf2d5f19c601a9d0def78d00,0x7be082e8b838cdd9be0708c7e44a02c13bdd11564011c79f0dd00,-0x2c1b6c7a1794e8ac4c6b0c7d2fb22f6abff3e442ac2f5ce6abed40,0xc11a150ac93e4a17bf0f4043c3d07470cecd71bf037e17977f1240,-0x2a3c3cddebe2dc5d33fcc5079d056ff73217ee963338a9c83e10740,0x795481b8dcb93aa3bb42c17ee88b0d83c9d50ebe6404dd167b57a40,-0x1239665390a6b2e7cd2602c7529021320e41a67fa8ea46dac9155bd0,0x252784f02d29ff29b3420d34eed9f4b486d1474d78370e654a67dc10,-0x40ef66be8d11948cc44ad8bbdb5f50f3ffb08a4b6c46676037c18190,0x62105c7199a461ca5b37f71283d61d5250c291fcc16c4b3f0f8ea650,-0x80bd4e966e7f991e592ae61b782ec2f2d74d0d6610d1c3ad803c7c30,0x939579f613b5960b338f2bc0014f6289c240fb1065cb95960ccf82f0,-0x943783253ad2c92dd1fe380a6f9aeac53f7a8a5718440458a8fd67f0,0x82afb32ec4adbfbf162f2cbfb944999ae059fe0e0f8f1f5efde9b430,-0x654a69846118878ccca10ce3bb3db1c17796b750e3079b8a44046ae4,0x45091dc3caf8de78ad6d192749445dbbaafc340aebfefbfc4d34a4b4,-0x295b428018311a07b9501aa9ec9d9e169e2cba3e2f48000c9aca0f94,0x15bfaec228ca99ce0adfd122187d8ab621357d324dd2aeae8db92004,-0xa04fe77d928e2df9ad138fec4ed694a1f698fee01e8c0f3559d8dbc,0x4082b1bc84e31fe91a8c9cb491cb255844dbdee87052389553f652c,-0x169693e63879490ed1cff212db677efc9827e2e5e6c7ea2519e9e6c,0x6d94c3eeda439b2b6356c831a0e283ab9ea59d4670cb3ee3ef54bc,-0x1c996aef1b8a2dc51cafe066286b3b027f0e7c374b2e78bb5ea0b8,0x660cb62384360e77c1f7333c171c1436b4f0eada8034da44fe418,-0x1346bfe1f360476212e71dc3ac7a1ec5bfb1f25c9e3aa2fc99cd8,0x30d1c3d5eec040b439e58d8407b3a20fd99ff4105b61ca42e0f8,-0x66465eefa9c246c98f7a07e44c314ea5acb6c0873995aab0ca8,0xae7795e814a57d05f1f8ac6b187f33d3f80438176068f2f948,-0xedb5ac50df93fae68493f657ffba3c5363e18569378035848,0xfc95e16940c3a4505c1ec3037d0f7ebb7655908ced938e28,-0xcb28548e46ae008b37ab292af57ef340420a47bed809554,0x771510983c817119cbeb4bff48fc416d3ae187a121f4e4,-0x306e2af3c9ddd004b593a5e71190d8078b5801a3c4bc4,0xccdbcb1531806adceb1b781e131cbeec2d3a8340574,-0x203243006e7f7875b15046e73ccb517b589c910f6c,0x2a55b6110e64481c4c1d0e1e13a897222ed9469c,-0x17e2ac77f64ea3810fa867f7fbf756af3b835c,0x418f5ba6eedc3bde5bb4c5c9f90651354ec,-0x193824e2208704148000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 21 78 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 78 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 50 indices rho q21 m21 21 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 50 indices rho q21 m21 21 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r22 : List ℤ := raw_ints% [0x26a37124a495a71fed8e7291c8c99a8837f9a6f858400000,0x32998706ba18f07b322be1504227dd8403e9f90d87540000,0x1f3fb31566bd42f340d84fbc456c20bf1efcccb3a25c0000,0xc1a4a98a203aac3298008a0fc47c00ffbf5e91889ce3000,0x34c24ce5b1bf937713f36cbe21e5bbf9e5d96f7da173400,0xac027dcacc52c9525d3867d9f4e84962f461702fcc0500,0x1b3444ace273c85c4428420b8cfbe8fce52e4542d52fc0,0x36b8c0b2849d3049560302cb45e3bd80e1315edb701c0,0x58e1de3848767014d9a956e45655f2af492589723b70,0x75bec61e37f9452061fc75abc1183b7f66e22553530,0x7fef9301610fa67ce3a78acf7d90c9c293622cdfd4,0x723c8f2491b7c769a396b4e7395358688c2716e14,0x53b23d6d77f18b839540efc2c8733be11ed482f1,0x320d1744dab4c53dc31c600020bf7e0bf7197f0,0x183261ecb0f7cd61f6fa58049823873766d604,0x9502fa8f1aecdf767569d4d7f6c69c3f0418,0x2c9a46a1fca7401a328b6070df5eb62c776,0xa02380ca6323d17924a7b808dacc11440,0x19599611294a47ff8b3d4e0f0d51d540,0x2865c29d1401e375ce8a1afeeb95b4,0x1e78eeb8eb9f174a68e28ee9ab51]
def m22 : List ℤ := raw_ints% [0x0,0x16688045c3777e82d2bd45e296680897cec68210000000000000,-0x237b3dff6cde6c263f6d17ae4f3cc703d1253c9e6c97e84d31400,0x1b14f1f953771f7a5f4fccf17c8734125bdd4d00185a10c41bdf00,-0xd44e770d8e0b8990d1dc309f338a1666c69da3c2c6077d9c122700,0x4b063cda5e50f8f96e9d6dc3c63e722458406235639f33f593b07c0,-0x145e15ede16c588bf2ef6a837ef6336be3936b86a898b007bb4e46c0,0x46b14123ad4e5bcb961d4bf7cc998b44dfecf231ac471cf76304b240,-0xc956c5a0ee7b1cc0db89355f780d5f28a3d1e6be07749e00d7607d40,0x1df878658d8ca209a495b09ce2db88f0bb854a5b0e3d2c0a900984ff0,-0x3c8723e0136ff5fcc900b27fb6f7af843f316791a813143a7c0f466b0,0x68be11cef95d57df0220758704ac7e06c49392cafd2a0617abb605d50,-0x9c8ad18abe305c864fb97b41a2e17135d31a6799d2df843dcd087f010,0xcb45c4956e7bc24f3c3a351a1509ffc8fe8d7069f428bb80551f72450,-0xe65ab001a7a840d5f5dfd191028181bf926cb7b617fd7cd84e0f5f690,0xe48b39077fe3e536825920f188bacc607c5cb5bb80e65912adbb30870,-0xc6f0121f618b6e8777a8d171dedd6d01cb101a4da73266c52960742b0,0x981b0d35ec099d982e2986b132863bc3f6f2ced1d153ce15bfb40a00c,-0x662f0654aa9dc82df32979cabb8cf526e01b54257d35654db844280fc,0x3c486cb3b1c96ea6ddb2be6227a90c88c0477cc9ddfb7bc3f7a35f984,-0x1f30552232bfebbef6a4200100fbb48426f117dfced59d28f8d403774,0xe1edd01b12f39eb719edd36b824541195d0682d7e1d03a5ddf56fb24,-0x593d3c8e0f7fb2485afbda808a9ba23d27c754cb92e8608d3f59a2f4,0x1ea14aee0e5d1a9e42b332c3846e683f76852d506a8f6386456d1e4c,-0x9171f5b4328270d4ebf33973c10303e30faa62c55ccf53dd433f61c,0x2517eca10907811322d5a65d0ad56487e18845e8ba43d36c2820c28,-0x81199a755b67ac923cd006b8cdfbd5856cfeb050688f6091342948,0x17bc63ea7b93e65893988d2a53f45060655e1593945471fd83b1b8,-0x3a5f8e3ad643f83d729e5d707d41d53c97bdcafb88741672adcd8,0x766e96589ae00d01a3309d285b3b2bdecdbd7d806a8bc85aecd8,-0xc30f4b42e67e59361404295642bee7ba71bd8e7cf40860625b8,0xffb4ae57de27e72639a2252116377dea56ad87a1e5a87dbdc8,-0x10460c464d2dc0052331d513cb4b8c79f1ef2f89890a776ea8,0xc7c5507724b99de078ee077f454088fd83a54b45ecdf319c,-0x6f1b9c23d0459d9d7439803ec5726bc0edbf1eb98e3ebcc,0x2a9d45ea27f3f0bd5b72e66be1905585276a9ccf7749b4,-0xa8cc9b095ae8fa9f856eaf926b2195bcc80e83c1d0e4,0x18a4698edcfa00ea2cedda376728599f5fccf47fe34,-0x1dd1a4fad86954e7d04c26e739734eaf210202944,0xf518d28f184209a233c108bff9c5d4c4c9f7fc,-0x25cffc28614df3f34fbdd9b5aefaeebf9f0c,0xce23742221c08dcc0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 21 80 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 80 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 50 indices rho q22 m22 22 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 50 indices rho q22 m22 22 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r23 : List ℤ := raw_ints% [-0x5f4d0ab4c08ad08f073657fb59b307816a16f2eb194a00000,-0x7cbf18c808faae941dcefe63392a2418c16c3033b11e20000,-0x4d0078f557235ff5658df23fc074b70441e2f8003e0030000,-0x1dcea0e235eb91c4f5aa4ff152c6cdb99bbef02e58b66f800,-0x81dd0ef9ecf00df672fc2c9eaa4bfb37b836d86da153ce00,-0x1a7220b9008a3fb759e7264eda04679e0acdbb178ab80f80,-0x42e04cc53f19b01dbbfa844bda767f6dddee59e4f853e20,-0x866d242b40a2d0d3c78b4e29f46b070db89cf54e868ab0,-0xda2caab487a8220552f938d6a2d23029e53328fa7df70,-0x120c7dfbf2ad656b1948b2dc63382a150f1a6aed097a0,-0x1397d60aab095e085479f665b416732a2adf830e4b52,-0x117a578142f47b49240a93297db4a7abf1e7e11ff47,-0xccaa91ec07ec4f474e383f6cf68546e54dda3975e,-0x7a4012edf6ca8bc1305d9afac9037692467e9c14,-0x3b06b20c251256a4de8089642d30623d6283f54,-0x16b00044f1ffa0ced1fdd5ca1211172e38134a,-0x6c7d80f04a21d6ff3a42ccc992bca67635ec,-0x184df2d9b38a0295be2847633162383d154,-0x3d723d511953357bdbc4b57101c9d3c9a,-0x61b93a7befb2124a68f6c278e283637,-0x498cddff7e704ee10546c061b5fe6]
def m23 : List ℤ := raw_ints% [0x0,-0x2736e07a16111d64f0cb3a4c87360f09a9db639c0000000000000,0x3db0f104af4f4601a59cef6043677e88bef16d5623405802431c00,-0x2ec51697329d72e2ba5863483641f9934fa37f7379cfab52ef08500,0x16c1390bfa6192948225003dab298aad8c042a54444000ee1d993500,-0x7fb6cc44c884751c85015b94bf8d533622470034bc503b9f18ab0340,0x226807bb85b5e5fd09c9968c8aea480d27c381ea666a7f6a8fb874040,-0x7676ae0d5c84717d8c70df53b8593422c4906c9c3b2faeb0299f89740,0x14e921a90bf1b32100a43829067ea05d51b9ddd6dbb8afb041c5469a40,-0x315db134a8bc4a3e8af8bd79560c68d2d4032ab06779875bbfb343c750,0x62c7d932e5cbf0ac4c5f6d2c008872c5cd6fa28817de3bb521a378bd90,-0xa949196b747f4d32092e6b5ffea983f93bd367fb1c9be305ab1edab590,0xfa6eacf82de4d6a78d5e26fedd627477bcbbd2df2ca61d619b613b1e50,-0x141b55a3641d54ee5d910384be80a3d519ff1c2421ab78f3fe46b4fb5b0,0x16873ed3f1bdb4c3f61aabbee6b9a7d6acab7aeec73c94c6f137ca3be70,-0x1615b05c7f09d326b4e776f12ea6bdab835c6e6f17cbaa1dad7555780f0,0x12fb39ae1e4f330690594fd54389851403763ae56d4a38428e7aa546930,-0xe51a955f223571ae4f27e3b5a3ebd329314122523806fb20fc78c1a344,0x97ba465b969ce11729b52f92d0b01278ea64b404d63e000e026c2a4494,-0x582946bd02cbc6f00bcfc775e3d5f3bc8910332cc9a4e771ccd3376394,0x2ce122b7c2e43415bf0d2aeb51c15faa4af648124284c7e03892778104,-0x13f86a6ff87c35327b596c2678fbd5224de803fcb61429956fd8631c9c,0x7be479dd7f067d86fb7d945156c998ec87f1ff862528927f9870be68c,-0x29afef9f42b8f66afa3e30134b7ba225f0570cdd531d34277527ac0ac,0xc1c2bc684bbe75bcb37376c065d3adf1a337c64fc50b1750f68621fc,-0x3049d0a98b1de1c390d20f3b75c7f47095674719985dd79a9226c2f8,0xa3eb36c1c238a427c85236ddd40c4ac7f8ad371a8455a8892e34758,-0x1d54fd651249abe23088b98126a97c3109c05e326ecebbee103fbd8,0x4609f404158b3f7b50ff0df64879a713863075962d2e0ae8245df8,-0x899815438c8baf98245c64f5d39cd497a4d460ad559ca929524e8,0xdac11c0d1e9d6696847a2a65f7c95e1f7a63e783973f34a16888,-0x113d5c9b46f4428faf67db22ce09ce698d8bada6f86c37a93ec8,0x10d12ef350815ff90a939d0cce107298c7de2d910ac701fbea8,-0xc4d9ad972093375da2a5170cb54776149b5a8fd5a14d62f34,0x67d6ed3847ca9d3cc46baf69ace28a2b4fa0084d8097e844,-0x258ac94282aa5d52d7762d3d3f9b42267484442ccd11ac4,0x8b3156904a080aaf73c2fb6b17225c29648a8c00f5574,-0x12ddf8ca92b5a5e2a433d41a5d05f1be9eb50c7478cc,0x1500e88a13983a3a6a063ea28c844f87167910347c,-0x9d2853c1cb7a2629eedeb435b9abdb2864a639c,0x15cd796a7e28d25a4cab0179eeec83af5c42c,-0x6948e4d70de87b8200000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 21 82 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 82 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 50 indices rho q23 m23 23 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 50 indices rho q23 m23 23 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x498cddff7e704ee10546c061b5fe6,0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r24 : List ℤ := raw_ints% [0xe60660c0acbaa847ac1310505f751266a7849d6c3afbc00000,0x12cf818e63b9a53e19e8f05f3772192a92f1b6fa5a7a02c0000,0xb9b187ef261a268a4f885a13bd175df0f52b6d374a5e280000,0x47d891b222afdc61d7a88ffd657cd29f0460a5acfe21aed000,0x138da2e220ab24de4f65baf071b3ce0ad2bbbe5c85362cfc00,0x3fac836eb894931b409b0b3511bf70551573006573aa9c700,0xa0eb65cc1d9d86d5ebe6f06082848034bfab1ad019970340,0x1433f0fb4e728fbf7ac1e60f8e2c1b6cf0e8b75ffc7d6080,0x20c412f725f09a1971cbb0c201c6fe98226a5b0f62bfc70,0x2b56108e1089148db7197b7b6ff8819db4f2d88646d2f0,0x2f013de890fcb010c46d071a8be609cb94e2f0ccba36c,0x29e4757113a687cfaa6bcd7e355ac480b3e68e736350,0x1ea1458f34aee70703901bec151b6dddf34def59965,0x1246ba1ef7bebda78f7b245ede9f3ce30e60a22ec0,0x8d06b27dbfc2661ffe46ebcc81973d967339df84,0x36231538dd1216fe5120c42cdff68b5f984c080,0x10286316304e9db1470cc64a1c5b11df51b8ce,0x39d427c9c6fae94195fc0d148d0c5be476d0,0x91f5f9abadff9a0eee515f09e7298eebc8,0xe7b6daff2ecad021214b7931cfdf8c30,0xae0c54f50ffc22dd8d3b5976436365]
def m24 : List ℤ := raw_ints% [0x0,0x44a008d5a69df370a563a605ec9e9a50e93fee5100000000000000,-0x6b484969cd1fa944b5fd4cec25b4473ecabbf0d4407c9483d13f400,0x50cd486f1b8d026eab2caf4020d782c3d269f4a0f870ed88f35e0700,-0x270b3af0b6d1569952036cd6c5dbff19063f30e7f9e08a729df41ef00,0xd993642f4255397f68b4713b7a9cff6720fd9c681380796af9c1739c0,-0x3a2d97aa4e712160dd41b0828f942ee072a97dcd2eb15b64bfd0b680c0,0xc6bf5d690d516c874bc54d18d850efa7e1b2d995e0a4eae339de3e3a40,-0x22cb86972653c34f8ee2a36bb406a9c316a5de703ab5fe418bf8c0e9540,0x51706e7b45d364f28c15813d1a0401ffcb7b6603a1c142509ebe47b1670,-0xa17d596b77b311d6d4e86b48e0e2ff20aedca2673750394fa240a0c9f30,0x11221264c63faa1ef2e0688979df15042d49162aba0273896eb977403750,-0x1917c18068b785253082ff905889735162c7319aa30576433fccd3820e10,0x1fe52c41af13fa2c38a36eadf2f548ef10375b310d9c98563108a64d20d0,-0x2356d8a73f6888b4af07ead10b2d4761e84a54e0f7fd028222d16a676910,0x223c7793894a993b901b724a644ff5db6b96e94dd95b5141f11083b28970,-0x1d0f157737e9f596d2b4927262fd8e41b9aa1428077aa847bfdec925bfb0,0x15a1b35e591cb8b8b89fcd8ff733da8a348b8d0f9a711ac28fdad72bb22c,-0xe1fefc84ddb8ac90ca965fa363e7168eaa60d9451f9e68eae3c27db7d9c,0x8159fcd31dda90d9424efee50746e1031dd4044bb511bcc85921ac95b04,-0x40cc200340a77ad5fd51aa006596a9bd0d0caccd4062c800201aefce5f4,0x1c57754a41c9bde96b4e2139f09fa47f9d8b859ddbeec9e346107af9fc4,-0xac9cddba5b2e377a981fa001bad018502cc983e3f1f0dbe4fbbd48ab14,0x38f0c5a58e980caed73350438de6e26555a7355c4d327419a482e5808c,-0x103105430f053950af0985babb7c77710ea8e1efd646460127128fbb5c,0x3f170817f285677939b9ea698314fc9379dc8901c8ad683d7394d3ce8,-0xd0e016eedb18034c77dd144d6315794042b4872f397c462571261508,0x245fe8ca371c83e3f055d4d342cc51042863d92a0d4cc6f4d4c8bfb8,-0x5451faf38a51bbce83ff0844dc2b159d506736fbe91a66657f338d8,0xa05ead41ff16953481d99cc2aadea04aee05113c53224bc06e3998,-0xf60f34ab42bb810dc39ea89e126d7e2d1b3774e4b25fa697ddf78,0x12a5a8672f55f977868eae385f628cf87172bef11cc2d44863248,-0x116b825be6f7e29b8902382629ea8b6eede885948688a01a6d28,0xc25ba37dc33f4cdd20d748edaba740fc67c91472d9c412303c,-0x6132de0163bf7d5ca3280e6d006ef0d22dfe045e87b157aec,0x211c610dfbebe5e2d1556255a4aa1eeb4ffc3241ed648234,-0x72dbc11f79883e7bc67ddaebe21cbb7c452c1b0b255a64,0xe7320fbee10b6f4da4470566d0b11cbd0499c32b1654,-0xecb4ab5fcc786f176af3ea89a28f860a90ed976ae4,0x64bfd61fba09bda2a6448725fd2ae715ebdb2e3c,-0xc9163348bed95223709e2ca10791d6c148c4c,0x35c309ed3c9a5713000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 21 84 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 84 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 50 indices rho q24 m24 24 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 50 indices rho q24 m24 24 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0xae0c54f50ffc22dd8d3b5976436365,-0x498cddff7e704ee10546c061b5fe6,0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r25 : List ℤ := raw_ints% [-0x22053c9ce552d68c961a82bf5893c749ab9011c3bf3a49200000,-0x2c7ed4aad39cc05c54643896aa4708543609cacbfbeb848a0000,-0x1b70fb869bedb022f6e1d7ee58547936af75a7bc28736a370000,-0xa9cc3e1398fcc306c421abab4832f3a713196191450ffc85800,-0x2e3048eb7805e36b0de9ea6c788721453925e0b30a98f878600,-0x96548cf1129f1a428aaa9312b8d4e89d778fb4ff8ba2a5ad80,-0x17bb457e129f90e56096f9fe8c8272945844e45ad6cb8f32a0,-0x2fa429a7625bd0afc00db59bc8771a33f89be1f2aeb290bf0,-0x4d372217d4a247226d32f37053f59c78e8f07c8cd4beac70,-0x660d4c4bac334c036a45dd28a9c9d692528412d7bf92fe0,-0x6e9b1107cf7d861d6ed3b18943361107969257506bab3a,-0x627e57738319698eeeb6d9147b6ed1a1491ba9ba1f10b,-0x47f30364b0aa8946c6d26d6355a4c5df847d027f268a,-0x2ae37f94b94e1fd5a5341435c203ef3378a3f4462c4,-0x14a97bf6ae81c8a50b044fcc5e7b486796103750d4,-0x7ec2ecf8a49de618712c9c2e3e3eba496f6dfc62,-0x25c928b2f058fd636cea6027495b9327f16a8d4,-0x870ce7071102e8fb773d12560e54ce35e8144,-0x1545c1676e3ae2d3fb805c78e923c5007892,-0x21b7035c9a73d8d336c600adde21a1cd3b,-0x19475a72aacf7b5a013e28e6cfa136f2]
def m25 : List ℤ := raw_ints% [0x0,-0x78180f75e3946a05216e628a5e158e0d982fe10dc00000000000000,0xba99f499db66bb1f548345837a8e133c050514f73d923a9e711abc00,-0x8ba64efc5e4e8bdaf5bdea6ae10a7a3d8d05c421d0709b083aaeabd00,0x43080be97f765592626f5d08689b5bbbc75188b92950db167f0e6dcd00,-0x172f21e6e6a102718641b4dbfd446279c6c81c9ddc9555b95a069ce2940,0x627796bde7a6495c6940b3b3561b889a55c84ebd1a841db7f088e01be40,-0x14dd202d0c2a61c3abe02284407c5550e87ea242008d17fee305002f8740,0x39f9b27e33ccec3994fc28cc7ca555e9695413be5f3d8c84e28db0d41a40,-0x868e047c44cbac6e3cd3c468018c5a50e7bd6935d50e25587dcab7aca6d0,0x10875b300bc2cf4b75c33778224c821f61c2bb15bad56fbbd3301a1a7a310,-0x1bcbfc4c112ae514643363d549b82bee78d9904e9d20a13d68ea94849e190,0x284fcc3015bd071d05fbdc397e9325b06fbf47f50d2236c9e6b8c2b4fce50,-0x32b5a9c56119612b10fb10a562e6d94ef9fbae847c9aef2aa728c0123e330,0x37920d0d30898963d3731ed8560333f3e5803b520760e48c94d9cfdc99df0,-0x353653d9631d939cdf42bb9b2183a622e9011bcd37321eb1e2ab87fda89f0,0x2c9c39f49a191c6f1dd81599c510c177c311c3c86a26632f39322c4b64e30,-0x20c6467f2d27915161677ee74ddef308c60de9abc5976ca1c972c323eeca4,0x151a6c9ac0ee82cf3f673912053a3f53aaca3fd0ce7953ffa25f886854974,-0xbe64e8926f7325fee92fe24496e0adae51d3e5485f9b1c0608928fd9b594,0x5ddd8b010dfa916f9219a6d3196633e16905690b32d87e74b4e9fdbc3004,-0x285bfdb44b0bbc2956ed34ee015c686940f608aa492a3985c6eafac2347c,0xf154ef9b3676e84f36cb3a6c5ffaedf2aed238f9dfdde7df62ead894cec,-0x4e0cf07bf9830158aa8107690b75876de4288a33237396e9895138a46ec,0x15b9caa1270665726ad4c52ebd2f97d81bed7ed9dc2f96dde8a898b633c,-0x52b8e18e1c41f0abb462e7100617b447702d5b88e50285ba9d11a95b38,0x10b19096ad988399d3195c7b862460da13993995ec4e258923a8f97898,-0x2d4358d55b69d6c6ad1186945857da36c414647696676fa9c924bd6d8,0x65d950633fefde09b85974b3e39550c1cbd7a0c4609190296427f6f8,-0xbb7fdb26f6de01b3281a0d47e9bebb7ddb6c2508fe944c820ca8b28,0x11592be3217481ae3c66535aea0094d8b431c627a3d874db5e88dc8,-0x1438d569f21c8c2b0d90581091a67879ed1dae95fea0bbb9782548,0x1215dcd35a3ef53cec0119eee662dee4c135a8cdf5aa40bfd8f28,-0xc0428cb7dde411fa1df47ef24e5a8b25a2113b05427e181ee14,0x5b1de3d6143aed24c5c6bd659764db10e0a47088ef7c1404a4,-0x1d3baf66656798458beab765522ab90f078239a2ce41e47c4,0x5ed67c97a822150d664c97d4024c6a5dd155d5c6406d374,-0xb11c700dae3741e53230bd3f1c984efa060eab1c0e72c,0xa6b899cc05c6dca39cc858592580cdaf8e9b824335c,-0x4092eae6f60513152f0be1f952ae9669063247fdc,0x73e20eae2f8e28e00045e9da3f669c4e8d7f6c,-0x1b7251c6d4b137b48000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 21 86 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 86 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 50 indices rho q25 m25 25 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 50 indices rho q25 m25 25 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x19475a72aacf7b5a013e28e6cfa136f2,0xae0c54f50ffc22dd8d3b5976436365,-0x498cddff7e704ee10546c061b5fe6,0x1e78eeb8eb9f174a68e28ee9ab51,-0xc5ac7a15990c970b420f93783a,0x4e431a43650c426fb8422d6dd,-0x1e2f279a396ba038f0ff3cee,0xb4f0ac609090d36c617909,-0x41a37960611ee48dcc302,0x16f79257193c3d190cd5,-0x7b74fd60c7a649d776,0x279b59e1c30e80541,-0xc0d8584699e874a,0x3734f9a5a6a14d,-0xeb6717a7317e,0x399c8e4b0f9,-0xcb6c4eb92,0x2775b685,-0x67a6a6,0xd8c1,-0x142,0x1]
def r26 : List ℤ := raw_ints% [0x4f0ed8c334562ff0bf38ce8ee9a4450fcfb7baf8f4de5fb400000,0x675ca5aa83f1579beba40df4c53ffc2d0bbbb715de646e3c40000,0x3fb8640245e520a167a910d7e2048e441a98de14a280ed6540000,0x18a1c786084f45cb1cd44b97ab1e75dc3f3dd782b6a7afa047000,0x6b2847646722f2b799541e9f76776b68c920bcf80ec300cd0400,0x15c97d2220c3a20d9140770fd327000f7209dc0130e78aa49900,0x370023c76272038e046d6a3eec01b0dd59babeadc43a37bb2c0,0x6e59d5ad950e5c365e7c39f4d32cb1ec17b46ce89dd2c99540,0xb2be2e7eb69e437f698c591f9890c09ca09980812e0596570,0xec145179c4b82e0d2eaad1f80cc4e47d1ed7acc83bc05eb0,0xffaf197c1d8968ca247a00f0f6b581f4d9aa22afbf7c7c4,0xe3823f12b1a15d68ecedd3d16e8f60532d19424199e86c,0xa60e56556851a9369c6db4a073ca190c04167ff7c2b79,0x62e563889c68fda3aa7da63a9756c7a079e053d58c10,0x2f98fff96fcf0647f31e19fca567a108210b089ed04,0x123b3b2c446b0c3af5c503f2559fe3da25e2ec4c28,0x56da2b3ecf9448c2f28e031e6e075b9efc7134e6,0x13607e0365d46f9f5917d03ee63a0bbbd430de0,0x30c49707377dcc237ac2ba86e3ed2484e9a90,0x4d2d6a8e7b873ec0bbe15f274fe115f548c,0x39c5830b5c2834faf0fc7b6f072695419]
def m26 : List ℤ := raw_ints% [0x0,0xd22a1b0e4e43b988fa812c7224a5b897ca53c9d81000000000000000,-0x1449fc004706fa35cc91337ca95efffb8e28e74df1536c2eb5edd1d400,0xf171ce416e901f1081a30ab383346266e2dc87224bd2d62db706c1ef00,-0x73250be7eb1c1788cce9dd2e6597bf847750b593ce72095061cc3747700,0x278e4fcc92927239a38d2ff049a8acd2876c688f1a99ee20cb346ca31bc0,-0xa6cfb39039a7c718b1802b1673221317d9dc64ab90089a5c24ee15e72ac0,0x231510fdbaeb9932e175a15a50a874194d3c3296ea622dd77d4aa95cd6240,-0x60b96dc769a63451561d150011d4d5b0e596cf9f1b0ce2d814e9d6f8b4d40,0xdea4f6f0230aa5bad3ffa1181d9dbedff02042f45dd97832431b579f118f0,-0x1b1d020c4afc5e7cbbf16d773a517fd9c0ab432a1b9b6529247eeb232843b0,0x2d2e844e112178b5e555cddac815b8b86d389c9a9f80e7df63be307f205950,-0x40e4b71dd53749ee47cac778aaca1490077b0c99bf3f42f0d7fd6ec52bb410,0x50cd38179458a51bbe9c2056ff6c3628f023cd49c443fe36da50f075e41950,-0x5797f07513734ffc6eae4d82789432d141799a21c6f42b8080bbc113486790,0x52eb184e0c0e17fd413a99eca26879464c5b7ddd25c539ae64482e9f70fa70,-0x44abc66f810703804e996c7305d10b8cc668b01b58b86a582197af2ee16cb0,0x31cce3ac87583dd61bddb1fd97c04e90ee90ccc9892adb33e106df141c8f4c,-0x1f9ff0f6da960735e42fd6f000f4bc4d86d310b9692617741c903d7cbe213c,0x119207bf2467e0acb3525aa0b30eee5204237a0a3f871d1735ca9a5a69ee84,-0x886ad58bc8da1c1004ac5b34054ab4215144e48314c816134cab91ba65674,0x39aa8340fe22999c0fc32381e83efd7395fc36938d51358d2e10cde3d0764,-0x152914d56fce36a02c5c54d33b3c6a0d0819448767e5c8122e7a325662a34,0x6b5c13aa7b71d3b74ce3ca01a6d3eaa40d956415dfebcbff2649c71016cc,-0x1d40fa91b4be678c360d1ea787e179fc39f0d5d9ad43c160049f6f28c49c,0x6cd7b18cc3210ea068fd41b5cdee7a686a3dfbaad0c3409b3b59a611fa8,-0x156b9f2bc3e88c56b309aa9e7e321365bc9e82f65af7e2264ac8df3fac8,0x3883345a8a673a6b8bd977af1a322969a644a0b62d717fb234c29e51b8,-0x7b6af1ab02e2704037fbb6c03353190027d52dc82db5252ffc5c0b8d8,0xdbe26905815d4a44bb36a4acd1eeb438a2a3e4a7217f1022aa6b6058,-0x13a001cfd58328892497034dfd2e3cac60fc991a9877a42b4bd56b38,0x15fc2cc1531fd68356a00f9e9097cbd0e814c50183b1b13989d56c8,-0x12d12fb968cf52e8ecbb8b19682515d4a2677c3e4cba598e633ba8,0xbe86c0754433718a1f511a18c431dfcacdd52fddf31cb72355dc,-0x5588af3f5d7634fab1a55b53137b804d44722737c40f4af9d0c,0x19d5a6fdc3dd1cf462afa652957d8f9c851e405129da2cacb4,-0x4e59f92c74ab9900c3debc5310a16379eef7ed9c03de65e4,0x87b54aa5481443bf7b5c6b5ff865aa4d9733e9ba190574,-0x756c0328e10ade032c837dfb715fd538b8b60593c784,0x2960f65c17c524d7b8593923444b2e79617aa2407c,-0x42c380405c6ac50190f80377aa2d3be9746e58c,0xe024fd3335321b0c0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 21 88 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 88 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 50 indices rho q26 m26 26 81100169611134058344960000 28=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 50 indices rho q26 m26 26 81100169611134058344960000 28 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_26
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<27) : intPolyRF (mz e)=rfPoly (C (81100169611134058344960000:ℚ))*rfX^28*(1-rfX)^21*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V8C29
