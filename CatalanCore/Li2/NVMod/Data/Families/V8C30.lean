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
namespace CatalanCore.Li2.NVMod.FamilySource.V8C30
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,8,30,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def num : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x5ab234187a6816eac200000,0x7c24ffd0a80ce20605a0000,0x5076c0b79fe12a4f5ed0000,0x20db3638dc2222836259800,0x97c8619265992231255e00,0x20f705ec10244131228b80,0x597e3b2b3c5ee68623420,0xc294701dd2f8584b30d0,0x15893a3c666e814e76e0,0x1f6b400b072791daa00,0x260b22bcfd622f3eaa,0x2665099f8b1aa1741,0x205804a79753e175,0x16b70b6d0123213,0xd3f13444b05e9,0x65e441ab78fa,0x27eefdd4b22,0xc8c86f506,0x315c52bc,0x9248c5,0x13319,0x197,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x5,-0x37,0xa5,-0x1ad,0x1b5f,-0x861,0x861,-0x28fd2f,0x832a3,-0x10d0971,0x5412f35,-0x4921257,0x20d569a,-0x485eee26,0x6c8e6539,-0x2ef41135,0xcb76f53b,-0x512911b,0x1fd09c7,-0x3cac037]
def rhoDenominators : List ℤ := raw_ints% [0x75131e590,0x119ea50,0x5a368,0xba78,0xdd0,0x190,0x1c2,0xe,0x2,0x1e6,0x19,0x113,0x252,0x11e,0x5b,0xb6d,0x1450,0xdd0,0x8118,0xa18,0x1430,0x1a7f0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 30
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 29 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 8 30 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xc99dfa34952d66770fd6d2100,0x19cd5b7aedb2456dd816854f2c0,-0x19a8f915a3d3e4e15fb465360140,0x10830c37b48ad37cf7bca67347830,-0x7ba511fb9ed409b3db6ceb8ecd110,0x2cda4ddd56be26c6fd1811fa19bfd0,-0xd1fc45f0245b0f04b805470e40a470,0x32ecbea679b730a0122b3d3985cdb1c,-0xa701d2b2485080767d4486f700427f4,0x1d5b4ffc8e75f472dfcc81bab1396ac4,-0x479b1999abd97d8cbedb3560fa714b8c,0x98cdf3b54a3f86aa25dd02d8880afab8,-0x11f40fb83d55aff94f83f36f06faa81e8,0x1de5000a04892df353822143af511c6c8,-0x2c4842232141c1681b98494c5de14bcd8,0x3a8cbc8e3df5bc10f0d6cca14648a3443,-0x454722af1a7297720ba6c1aee3f1530d1,0x497e733d02d332c34e326fc5a51b01185,-0x45fd7ed2168981b3c6e82d8cfff20bc5f,0x3bdfe12c364cdbd8463cbc438950e453e,-0x2e0457e4095dec6f51367d22dce7a302a,0x1fc2a1f8998c70dcdc9d260d6f1014e42,-0x13aa9f4d2d19210b121fba9639f7ab266,0xae8bc00c7efe3f21b09ab973b058f23d,-0x568d788ed42fc2cbc157a2378450abcf,0x26430fae31591bca0aa831e6bef0250b,-0xf06dfa87d4de2e7e4b3d3d69d6e1f91,0x5387ce140ae7a8fc59f7c99242b6a9c,-0x1989bbc5e43b2b53a2306db6980a634,0x6d3cbf88fb5be4fa51242e859012a4,-0x1956d8d0ccbce14cb186fc0a40502c,0x50d5434ce94d7db05ee04ed21967d,-0xdb12317696d640abd5d8d1f683af,0x1f12984556873369d1c10a9cdc9b,-0x39fac42fd4ebfbbf4592d282a81,0x56e25de2e348cb7943e52a28de,-0x655d54ba25352ec26b5e7908a,0x583ed213ea2a361930a46ae2,-0x35f5fd65317eeb8a03f1b46,0x152545c055fb1727059c47,-0x49032b464d7fd8dedcdd,0x682eaff32242c8bcf1,-0x1e7660740b2beda3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 22 41 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 41 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 52 indices rho q0 m0 0 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 52 indices rho q0 m0 0 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x16d6e557f4e6249b7ccb55cbd00,-0x2e3972d73f72c3378400f1501ac0,0x2d6d237a9bd22839f5306e3e6cb80,-0x1ce0ea4d77d3922248b86078d42bf0,0xd595d96b34497277c70105e518bb60,-0x4c810e717f8b19f05487d764f7523b0,0x1618f42da418127b491992eef72ade80,-0x549da7dbb173aacb5e5dae3e9a9be32c,0x111c2c18795be5ca825fadabc7adc6118,-0x2f75642f243fbd333b7cb8b3708c530bc,0x721fbfda08aa9d987f26a9e03045f7800,-0xf0023a4d5773678854bd59d5d06936438,0x1bc7a98ea493b8bc29028f42f4b7fd8350,-0x2d8cf0b4c7b5c51b6fca30e2116bfe2158,0x4269f80aca7b87e141c4022b686b4d6460,-0x5664be2c5847c3350011325d7d553fb537,0x6485bf8916a56028531918677d1d21357e,-0x68cf6927a3594197808e5a692d1619831b,0x620ba3a13466aff0b5e3cc73eea6738180,-0x5256dbaee3dffee74a860a14e732b0ae3e,0x3e154d398626e74e2c7ac2b7c0112b8c14,-0x2a01e1f0c21ff9a6f99dd7799d8e049666,0x197b3286ba954dc04daab9f7694fae17f8,-0xdd5b95a7a32f2daa675770ff95a0a8571,0x6b57162ae7af0af98b916498d990bc37a,-0x2e5b59469c9632f83a6c5cc49d6c3390d,0x11c43a81d7ca7d88086be226210c55468,-0x60422f50cb640458c284dbb60609debc,0x1ca5318e203c169f3fa841de106c9f48,-0x77153353e1d87ebc9a3e6c61e27a98c,0x1accde549087fc61a8a0e6470e0a790,-0x52c90c24862b9a8f7fe8a812283359,0xd8c45e65b2a457aab086af11b2472,-0x1da0ad6fdd5566440809792f96d35,0x351c048e6bc4881138a910e86050,-0x4c2d5a0d7f8634e1326d479a67e,0x54b04d637d15f17af0ffd5edb4,-0x45dee1778bc28eae9e0af5e26,0x28353e3227c8669fe4265a18,-0xeb199ae2e4c3a3bd72ab33,0x2ebd9db7bc9b7e544acbe,-0x3c6dfb98c0d7728e807,0xfa8764a2aca0e9c8]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 22 42 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 42 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 52 indices rho q1 m1 1 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 52 indices rho q1 m1 1 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x29657faf6be12259d2308b816900,0x52d54af4e817633d5cdbecd63fbc0,-0x5076604368dc040a77a53cfb8fdc80,0x328c5d5ffb47cf2c679d9c42a885330,-0x1715904bd8878519e1675b0a191c74a0,0x82aaa3620e668561cc56b11618c37a30,-0x2544220eaa6bc800125f5c7ece4b90900,0x8cdc060775bc33483793f316e83eff1fc,-0x1c1b58972c96d14c4502e333bcc42d8268,0x4ce7cf73cc5e5a85b5bdc6a88e0996039c,-0xb65e6da8ef1dc7a541eeea9f0ec6b765e0,0x17a11a7c707b27e9820b9becb3cffbbe018,-0x2b1ea5f0293e6ee29333a14c348bd0d0730,0x45a3dae4c30cc4b83c29bf9f1e6a271bf98,-0x63f76a26aa2d0bedf1994ca04e134d6a3a0,0x7ff7e0034d691ddd27678a8f0c0c1c0edfb,-0x9273829f89cb81b4304decf9ee6caba5062,0x961c321c832a3bf52d5df5883395b990733,-0x89f673489a20023d53de8103792bb0cb358,0x71c35aaa87fc6bdfe6f4a67d492d0c740b6,-0x542aacb3d920e9d311a1a6d396eed9b578c,0x37d73e0e8ecfc55a5e8492441c3153cef36,-0x212fe33fdee25a89c996ded8cea96eece08,0x11a39d81386b63c36b05ad9e489b7d9fc3d,-0x85d96f94e9ef59096c29240ddacc513766,0x387a5328f8940a38737de2a67fa1da8035,-0x151feada9b29dac57c1d9bea677387a710,0x6f8f841619cfcf441a1421462b6634e6c,-0x2050b1c1baea63eeea68c5f0dde5f5df8,0x828f5882dac0cfe6531da8cca89d022c,-0x1c81a9f53334bd8d96c8960d2e1cabb0,0x5541e9e56256a6b9079536059c3ee35,-0xd7a60196f54c983dfd8ef1daa887ae,0x1c657369172960c7de3250c5c6101d,-0x30e2ad92ec0567be0ded9a26c4ff8,0x43167cdea16bb829bc43d7990ab6,-0x47091760592e4df3907c7764fec,0x378123779c0cd20ca87cd91df6,-0x1e0913397b7e60ccf3c2f1828,0xa3a085cc16ce40151d3c877,-0x1df0c3367dfc82b2dd63e2,0x230b761c2fa49139bfff,-0x80b9eb4d5c792f4c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 22 43 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 43 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 52 indices rho q2 m2 2 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 52 indices rho q2 m2 2 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x4b07f76df3880e42ccf7fcda8e500,-0x9479a2c5bd934e56841c7e512e34c0,0x8e98dfcafda901a203ef0e75bb08a80,-0x588c9e956aa262f1c9c5bb88cd462d70,0x27f624fe0b7fb452fc147851a94a6bf20,-0xdf78730088f5fc8b74b8a33936fb757b0,0x3ef2717a66d08fbd03b0ded7f543a31700,-0xeaebb4ab4cf4b81df2687ca2b3e860ad8c,0x2e44b16a6b528425f6afa725564f740bf08,-0x7ceabcee42cf0a22972c1b7ce335a45e43c,0x1242e8cfeac55267f4b794940c70b82a72e0,-0x2553dea33375f3949f667b97e8505ce48bf8,0x43230165c5eb490bc566995a8b1852457270,-0x6ad2cc58dff386376d073fae90f0ae6cb458,0x970145cb75563f57ffd9590e0df25069cfa0,-0xbe443f1e0a528f11dae3b4c67e2221544daf,0xd637ded90b462fcfc8fec371f8e930d489aa,-0xd7e4f1f02508a122fcc421cf03b3f7e0727b,0xc2fcee33cb17e822bc840fb558ac1c3d0698,-0x9de7398c4df58894ff0fdd71d77608c3deae,0x72a6cf56747de3d98bad7de5a1b8e7dde0dc,-0x4a98f9956c90152194f37294483e9c022e26,0x2b71b1476ecc1a6892bb20f07d3c9ab93d08,-0x169b8780ef0f8a70de25d7329c2b28e5a739,0xa7cd447789cf8f2b16a3d12f3ffdadd381e,-0x452f5e1bc9eada9c4131adb5063a9fc67ad,0x1941c76fabf38643512f69541bf1116e6d0,-0x8204e05276fdb85aecddb4caebb977879c,0x24a8f9b87fd285535bef0dffdc3f173198,-0x8ff1cf69752c79fc33ac782aeea64a70c,0x1e7d40849e0838d82775ceb438f0e2bb0,-0x5847ad4ef2c0f0ff26e6e1dcfb303361,0xd7a9fa229e498acfdb0a7d99bf2f066,-0x1b5a52b59b938c06342d364c5b7d1d5,0x2d358e3bfaafbb11acc147c637b0b8,-0x3b5639c7ef2e3be3c322b17fd68ee,0x3bceed5b4a3818c5c2b9b2c8303c,-0x2c3ae2085fc52ef735fa39055e6,0x167d3e635ec115fdc422c15328,-0x720c480e8b34bc371e9ce18b,0x133056e9c346a9efd59158a,-0x1451afe96b7a3fb90c3e7,0x421e16621f94f2e200]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 22 44 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 44 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 52 indices rho q3 m3 3 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 52 indices rho q3 m3 3 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x87fe7077496699d913817a4c21f100,0x10a34ca1fa332984d941beec9a2739c0,-0xfcd8e405a8445f46ac830af5792f5480,0x9b3dbc9887ffdc01a334d215f572390b0,-0x4540307084ff2234ddd74f52aee8f27ca0,0x17eb0096bffad18b5a7d1642407e1d66db0,-0x6a7de2f302421090917163e4bce80063080,0x188819807f20df6d532d734185fbb9aa615c,-0x4c52a9f5c86b2b3370840be07b56c53a1468,0xcb5f50a33ee95ae757ba448be7f8558a0afc,-0x1d551c403916598d20b0db17305ae3a4714c0,0x3b21ef8258299e304ddcd258757cbb6b518f8,-0x68d95997111437d9ec0bc6a24a7d331673390,0xa465a9a1963038d97fba8735229fdc51ca9f8,-0xe4e680d2c6e840d93b3e6a5d09670718d1fc0,0x11bf252c4336af30d96f8c6029fb570f192573,-0x13a93949d674391aebaf2cfa9d7e63a8ccf022,0x137cb47617f50f3f974c86b304ff150a54aeab,-0x114c7b845272708700573e7412084dc2d738b0,0xdc297d837dca741ac61a5cec65952cf9c1dce,-0x9ce9aad9783607738624f1f8608ea7aa6c9c4,0x6423cd62e2f61bbd27472e7b24b0137a45b2e,-0x39281dd916211e201cee64850a67496976c30,0x1d1fecf47d9de50723759f2297359c851bb3d,-0xd3799f71ca730ad00f83cd7525beeaf8a84e,0x5534b3266dba1f8b3eb881ff85489a7ff795,-0x1e5c96745c9d6f3f73da12bbdb9e9455e3a0,0x985c9bf4aafb4d923967c557da9b9b0abfc,-0x29d144048ff50b2d8964abebed2ca7ce688,0x9f91a2f65d793a8717dc0cf84b95ca94fc,-0x20c938cdb63ea741d2cbf47c52fad0b020,0x5be47fe79a3784c01c2543c1587d071ad,-0xd8c801fe55a99d7f2c33b975602c823e,0x1a79d4d627a99b219e9b93f603b56f55,-0x29ffd5ad23b366c296c27a75ca3ec70,0x34b2ab4da96efb13a6305abcb2062e,-0x32897c21c91a9abb02938ebd51d44,0x23599cbfb93e402a1ec57b7f29ce,-0x10e038dd860f5558621a90d7170,0x4f98b0ddf66ab0145c80952a7,-0xc4db187bf5924ad9f2de22a,0xbc7420d78c80d509cf40f,-0x21f29dad7f98a613000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 22 45 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 45 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 52 indices rho q4 m4 4 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 52 indices rho q4 m4 4 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,0xf67d2bd83509f6d9735aada9fd84d00,-0x1dd6a3fc580150219f4992204d42c8ac0,0x1c0925aa553e782d52e77c5670a59f8e80,-0x1105fff22a086f13bba4077c9a4ff8abcf0,0x7821ace0be06ae29d0c54aa1d4c70f8b820,-0x2903086831237d1a8b9d37cf4056a8ae2930,0xb47000a4187a7e2b6fee2fb22e475a01e800,-0x290fa48fc08e203dc48285a814649ad64086c,0x7e28403112ce8fdd3404f1835aee9fa25b848,-0x14bdc15ddd26b31baf024ad4a7ba89f3f9421c,0x2f3c1038744e3b831f769a344d07e7a7445120,-0x5def1665cecdc8e5f61ed14ddfa8b110760998,0xa43c74a741ea583939dbce1c42f3ade1a032f0,-0xfdd12bbca33195ab231768609fe4377e3cffb8,0x15c2cb4bbb1406877c7a54ef4996b4e255051e0,-0x1a94ddcead5eb75701aeb6cd0fa7db202e89587,0x1cfbdb6ce65e08a3ad3e207be6755c43c762aba,-0x1c420b6c24140660d12fd0ccb5f1c39f2b6c593,0x18a8f28049b76008d89a0bb5cfaee3d5b371e68,-0x13455dc2ae3d7ce66f21c4722fb92ff2b4d9eb6,0xd7bea4b5e8495c81f77f4d0b6a345ac61f6d7c,-0x8712292b467affab1948ba8a34d87fb572f2de,0x4b9173162c755cff4b41c449d180a04142fe58,-0x25b5dccadddcaf5533d714dcfa52ea55d576c9,0x10be483033ca84148a11b6d1339657e240c2ae,-0x697d05329f917fc00863be048353d58876a4d,0x24b143a129a69e2ec6c96d249cabb45984ab0,-0xb380535dc72d95812f1479e01c44a17f56cc,0x2ff4da4a1cb3884ea35d371d505155e48658,-0xb1d557fa064893a611a79850cb61096dfdc,0x237100164844e0f2a8b3f83720fdca47d10,-0x6025131180769c12aad305a08168ad1bd9,0xdafc3e665c8dd119815ff86a72957d516,-0x19bf72b28c89a07697ee615c616bb38ad,0x27303d56e8d15c97691bea034e5746c8,-0x2efcc068a0bbc73c9232eade0358316,0x2ad98c92346b84660ccd5adb3c9a5c,-0x1c54f9b5f26b9543db872c83f18fe,0xcb080f2d4b67485bd3bdeb0bb38,-0x379e5cb4e38746ddd7d4de904b,0x7e440c4d087293275bc83efa,-0x6d36b1ab207540c87bb5f7,0x116c9924534468dc8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 22 46 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 46 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 52 indices rho q5 m5 5 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 52 indices rho q5 m5 5 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x5ab234187a6816eac200000,-0x7c24ffd0a80ce20605a0000,-0x5076c0b79fe12a4f5ed0000,-0x20db3638dc2222836259800,-0x97c8619265992231255e00,-0x20f705ec10244131228b80,-0x597e3b2b3c5ee68623420,-0xc294701dd2f8584b30d0,-0x15893a3c666e7fcadde0,-0x1f6b400b0727143b180,-0x260b22bcfd501da59a,-0x2665099f89923dec1,-0x205804a781538b4d,-0x16b70b6c23a4a7b,-0xd3f133df9ab98,-0x65e43f8a397a,-0x27eef5489e6,-0xc8c6d8316,-0x3158dc16,-0x91f305,-0x12d85,-0x15f]
def m6 : List ℤ := raw_ints% [0x0,-0x1bec2df77e0220f6a21145ac41b80b900,0x3586b12133ea65c666598efc9a497fb7c0,-0x31c3649b0486d64e29b3ba9de4ac9c6f880,0x1de41d0fe6db1b0f943eedd49cd5aa57aa30,-0xd09bf3ab378991787a08f603e62f475559a0,0x46697b8207caf7acb54af53d5eeaf98fa2330,-0x13231fd2c751d2ab4b2fa6820991707a781e80,0x44d9899851d1e610267786c29a728ca78c34bc,-0xd0f3413125f7d70c6c794b0e33be4c327af4a8,0x21ebe72905a5959031b2a3c2c7ff0c83d0739dc,-0x4c4096e0651df334df951e0bcb7519eed9dde40,0x959fa26d6934f000f528d0d3d6d598daf395618,-0x10205365c4b619b140b9998cad59052169ee7cd0,0x1891ec16359c269c67d0d0c55563f8ee23e7eb58,-0x21365f306b497465b44d86194a0128d4613dc9c0,0x27f552aa579118e4d78009edf080c11f839dd9eb,-0x2ae3e3d0109708441935585e24fde4d6690cc372,0x29240e1ed291372079fc714e894e3a034b571003,-0x234d1c31bd90676a74759126ff27dabc6b683810,0x1b1b658af761f6b92d6f0bf82594c8836f0e5a36,-0x129fbb96e38078ddc731379f019c877de0bad9d4,0xb70b13d43326cf31a39abeac0a498384247e866,-0x6464e2f1723d03afbd8df5cefeffd89b7027c30,0x3111cd44b36ac1403faef24a3f38875a0265ecd,-0x1551514fca05a3415fb3b476c981cc60533422e,0x8345b5703e69c582ba75cf5c51cccc0254f035,-0x2c9315cfe0b9c04f6fe640d69208a2b64f3960,0xd495c2b949640b5716ce2ce2b02833338826c,-0x37490f4f1ca99f294e23da3d7e3f632c64d68,0xc738b38409f0acb91c3a9cc722dbe3d9bdcc,-0x26822d933dd97d4cf850d7f23636843475a0,0x6518df48dce2268f4bb0d0430b459746bc5,-0xde46f1a115f3e19ca3f980a0c9fa13c0ce,0x19276ccae473b6b5eb254ffda50f82396d,-0x24b85f42d35c12a1f8426c3852bfce0d0,0x2a0e09b1ca18e7d40a10d82964476336,-0x24736df68bd1cbb551df8861e57d814,0x16c45fb4742eb31905e230ceb3e866,-0x98f481ed7fe78e50232fffc4dcf0,0x26e7eedeb535f3630f79ba5e6a7,-0x510326f8f4b9532bdd9bcd62a,0x3f468839f6609d3ca89379f,-0x8f0b240a126bf18c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 22 48 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 48 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 52 indices rho q6 m6 6 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 52 indices rho q6 m6 6 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x15f,0x1]
def r7 : List ℤ := raw_ints% [0x7c5a556d8fd4b76bdffe00000,0xa9dc088afdef41cf56f460000,0x6dd6ad3bf38dac20ccf990000,0x2cbc18973e32ec27d479e6800,0xce0e0a642b8ad3b92c164a00,0x2c9ae8bd17bc1c402d37e680,0x78a4a2c186c3d9fed82ec60,0x10531a206307c92a6b5b910,0x1cc49268b29e8af249cc50,0x29bb792b586858fe13820,0x323290a06ef72d833996,0x3243d605efe48183c85,0x29f25dc7cfe2de40aa,0x1d1f785ffc79f1cc0,0x10be0ab3e0a2cffc,0x7e74e2cc21332e,0x30626a0dfca24,0xeb5bdb56954,0x372127ecae,0x9738ea05,0x1131c42,0x10084]
def m7 : List ℤ := raw_ints% [0x0,0x329c13509463dbbf05bf4e48371d94f500,-0x600b06e1e1cee0682761b1e57096027d0c0,0x585fcdee8769b2e19f21bb75a2878a5c8280,-0x34865b901b1ab508ffb3f41142af479a51870,0x16a9dbb5ea49ffff8ec9e4d964b0443f218920,-0x790a4410fbce0feb177b1c3b4332724edab6b0,0x208617fc900849b135e1174d2fa3cc9db285c00,-0x73a561dc425cbc000eb926d4e797f3f99502c4c,0x15ac39cd5ac4e2de306708fe25a45d1f2ec0f988,-0x3799bb8efb7b7f682081887319abd506604a6cfc,0x7b66076df57f8fb057535c3d80eb0f1bf1be4820,-0xeef810b9755636f12bdf47b02a11246d041df4b8,0x19689a37933c2eb94083502d514bae80896e35cb0,-0x262c85c44428337fb24f383edd137f8750531e918,0x32dc0f1d9c606b05465c27b1a172385db92346860,-0x3c47b7895fde420b7005453b5a3d478350413649f,0x3fb503098e5eb99cc00c417372ad863034c7b604a,-0x3c2228fabe1054f05b9647e43695f83a3d392c7eb,0x32be41fbb262474be1e10dafcd2afbcf62f19a3a8,-0x264b2a6ff597242006a01b4311e38ebedef8fad9e,0x19d68dd5a8e772d687f39dc345b3d936832c51b2c,-0xf93320c682b515e8a77d0df101f53a899d377c16,0x8602a21be0381229b876d8358fe11da037e363f8,-0x40295ea1c67e8383dddd3744532b4c94cacd12f9,0x1b46dd8e195a014167b9280e1babf9723b83262e,-0xa42f35ab44393025222609d8f2f220d5194066d,0x366d37880ff6516793975eaef6990e90f6476b0,-0xfd0f57b4c568ab6d68eb4217e588a195f8e33c,0x400fbdb00e75bb2fe105a9eba7ce3f935fb5f8,-0xe05164b009136c4adf14e829fdaf0b8ad76ac,0x2a0ce7ca85980981436225e8d6e2ebc589c50,-0x6ad274e8cdf7774127a428f49dc8f72773d1,0xe2ac4953ba3fb4a16ca31a35ec4ec286726,-0x18aeab288478350637ff7f05548b4e014c5,0x228c2ec7df5d559167265739731a73d788,-0x25c700e98f8f6ca0dc30b98d07d9f0b9e,0x1f1ab0732204012475dc3c03abe26c4c,-0x12573c5421abad026b7fb671c274996,0x736eb72c72054d3e07e3d4f9f5ed8,-0x1b3de60ea38549ad873c5cb13eab,0x33fd5b111109c4344ca692209a,-0x24a6725224e4e1bf59fa0307,0x495ec3b6339e4c2200000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 22 50 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 50 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 52 indices rho q7 m7 7 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 52 indices rho q7 m7 7 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x10084,-0x15f,0x1]
def r8 : List ℤ := raw_ints% [-0x5ae0f7fb57073496930c0800000,-0x7be8a88f2213b3f324dae880000,-0x4ff661ea7391ab276065eee0000,-0x207e5093958016710d4b3c96000,-0x954ae35b41325664496da61000,-0x2039f740b9b1090f06b539a400,-0x56e2b1b5ed2e45b0fd98afa00,-0xbb6e7a7b89ece2b8ca123ee0,-0x148f235c6762d5b67c9f9270,-0x1daf2a3181ad5992b01dbb0,-0x238308e8314e504f251788,-0x2355acae7a6ee8571c3ee,-0x1d4474a99ebfa09d03cf,-0x14239bf268598969122,-0xb73f0443a74f8ef64,-0x555ac0a974c190ec,-0x201c46e2d1b8a5a,-0x98cd8c9bc8cf4,-0x22c008a13f9c,-0x5b730a98e6,-0x9c7e6edf,-0x84b59a]
def m8 : List ℤ := raw_ints% [0x0,-0x5bbae3020cf4fe4a3a6abde2e3e59dfc100,0xac600eaf63c584a1bfa7f83827b547c2a5c0,-0x9d0586139f1e3fc94b77129f3aace709e7c80,0x5c5db22ade1af0fd735fd6cb458f78a5194fb0,-0x276f1fd9ec3b19a9b72893e23028eab3c5086a0,0xd0540c9906c1580358ce1b6fffd8e1d712704b0,-0x375b2b2ee31fa85c534155bd34ea9f04826c3280,0xc2952e9fbca534389fdec15f160d4758cf55671c,-0x240992757af90a908d5a66dba5de0fd6478c844e8,0x5b55766e230f7c77b18317e48cf1626308ca333bc,-0xc82d816b055567346d3684256f99f2caeb1913940,0x17eacb587916ecda2d75a4d1ca8ae16a6836845b38,-0x282608c7eff5de404368689835f669fe56cf5b1290,0x3b7e2827d074ff2d2335e7db1c3f2c57b6f643dfb8,-0x4e23d7d6ff43826af2b85256ceb89c726a6e3bf840,0x5b415824954482809e3471e634a5e4458ce7929f23,-0x5efa25d0c7fa67b8925dd3e8265469bbe60d28ffc2,0x583c411879bbeacac6227f95c5450652714e13fb1b,-0x493c8f6ed67f619572fbb03395a8ffb1e5005fde50,0x36536cc6a6440c822c0c91c893ddb902028d6f609e,-0x240116edaba5b94a94ca5af5410bda07341640ac84,0x154ceb833d7a0a5c9c5293a6fe65e8c70de845335e,-0xb3b7f152d875488530df4a9b0f86902bb5f29c7d0,0x544c1142df310800b80315f0750e35b56e15e759d,-0x2312818b4be607aa135a3f685791a318a532cca6e,0xce5dca1e17b4045dd1bb9befa80cf09a31e93655,-0x42ca0241940dcb2358005f83b981a4d6af68e760,0x12ec199f741ef0e9583156cd27cb36ac5ceb98dc,-0x4a9a6fc8649b52530cab55c52b35b00940bed08,0xfdd4c9a336380ccdb46e89cbf3cd98f366c71c,-0x2e245f9234689101fd34c9664dad4bd2e814e0,0x7167e062c9f7bc798333433a4c9c503b4df1d,-0xe83445e6e9311c7e5c21066e8ee51bab4f1e,0x1852a37b9c7ad49ca5816051479ed9399a45,-0x20a18c3128eaa01ceaa31846036d359d290,0x220daea580cbb4ca37f3fe560f41e70e3e,-0x1a9edc925dc23c1a4e7db455a23a90504,0xecf3f8f7a18e158344badfb4a6fc9be,-0x5741b194842039edb73f189cb0ea90,0x131759c5552c5cabe2ca0473cf267,-0x215ec8ae3c406201eb47778690a,0x1538ef2c6f2b447432144b22f,-0x259efcd266254ec3000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 22 52 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 52 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 52 indices rho q8 m8 8 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 52 indices rho q8 m8 8 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x84b59a,0x10084,-0x15f,0x1]
def r9 : List ℤ := raw_ints% [0x2f04396aa7c2f10bddcc62b400000,0x400043c6bbb9f38a128d0d7a40000,0x293a6713d110867d57502d30a0000,0x10b860549bdfe0af86fd528277000,0x4ca71941ca3eda9d91c0c0272c00,0x108176a62688ea9ed87b7bc35b00,0x2c60f32404af8fb64d465345740,0x5f7066b4927d43ab8798737320,0xa6e9a876303cf89a2c4ada3e0,0xf00a48ab58ceb214006ab190,0x11ddc8089d10a19b9c600894,0x11af24f0563c29bd121da92,0xe8ef94bbfab2111bf9574,0x9f237aecb9b839888a9f,0x59bb1c0a10993dcba08,0x295e0945eda99e9900,0xf5de2d650a04ab88,0x47f98101e691942,0x1009c5d73c2424,0x29154265cfe6,0x43bfb2d124,0x367e48f7]
def m9 : List ℤ := raw_ints% [0x0,0xa642bb73b77c0ce689e1782b3d102e58dd00,-0x135733a7c5b3378b5dddc84044c59ffc0cc6c0,0x1172144f432c5d5aea6809ad645ade5a0681680,-0xa28c052bca987ff8561b105262d06c36f02aff0,0x44ae7f5e4f9737a174525d861cc0987ab4ed1220,-0x167004e55f064d004af0c26045817b433ca910030,0x5e5ab69bda7ea558185e1a667cc260b95d949ac00,-0x147f40aceb1a75d41edfbc49d5a440af2df946272c,0x3c09c6c08e6090ac88567755a86f99ec433b0d68c8,-0x965b011a4c3d9a278d4f689826c2e7cde8f4c27adc,0x14580a6011daa54cad9334c7c5eb253d3c94a554620,-0x26664ddf2063d7a1c0b89e119e3775d6f09e67240d8,0x3f9e520e9955c3be029a1da5c886f52ab1e8848f170,-0x5cffba20aac996159512f46b373585c78d204839378,0x7871454607d674655c67dd4e222541998c00c1eafe0,-0x8a9f65629af97496b8658499a681d9d03a1b9cf2e77,0x8e1c5f2e34f8418dd6c356fd86b2c6731b89796815a,-0x81f70c909419779d91875ffa4b00b1dc9d01b482403,0x6a1fa1e3251deef52638eb668df871a1ab6ac1fefa8,-0x4d64360c49fd39373f09e5fe6a42747b0690303c9c6,0x32631e57474a29b20f6dd137396ca7a8c04b6b0a09c,-0x1d42bf8757e15ee82350e0672a0d098459018db228e,0xf21fa4a18151d76d7436920a7e5f86977c12eac6d8,-0x6f45c3054e939c605dd075130f9cc597e746d97da9,0x2d4fd32f0588bf54cd7fc536c53e6e65022efb9e6e,-0x104a5aba0e917bf72a4e974c496aba603c9a3b120d,0x525ca28e35831d382a1f0ea93fc61ef9135339530,-0x16bfee61a4f410fcd8cbb3e6b3f80f11a8477732c,0x574e5fe9630c7cb7814e7c7daf189b0bf0d95218,-0x1209f15e9c25b1e078a6a0d912d363c3e170b0fc,0x32df653833d8dc32aa1091da9d6d12c06374f10,-0x78f3246e7bd72eff1ac02135d5d3e32a21eb89,0xeeeab881f88c279f7f33c8512ded390502e36,-0x1811442ae24fd81383d6fae68b95c0237199d,0x1eefed97a59170a5fb82174a5cd62d6dfc08,-0x1ecc98c7718fcdd57c3fbfa118dd0fd3266,0x16d8ea5bacc2b0ca61df325e1e04f4eafc,-0xbfc08b682d66a3cb81fbd290f6b0b86e,0x420ea7fdcc623adbaecf0b3fe67f0b8,-0xd63bf50e553557dc8a27bbbc1e10b,0x156bfbd0dfc8dadfbed37e114afa,-0xc490d474192c4eedef0254f17,0x1348ccf434cebb3c8000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 22 54 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 54 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 52 indices rho q9 m9 9 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 52 indices rho q9 m9 9 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r10 : List ℤ := raw_ints% [-0x134e548c6e755a1c2d579f112e00000,-0x1a3e0754b1232ca93c487dc1b960000,-0x10e0bdc4d8260bee9d2422918070000,-0x6d5384af55bca5434b6394cdfba800,-0x1f439e726b85a15d52003309564200,-0x6b7b720bbce740b9b376508696c80,-0x1204aeb3b50a6c5dc453b4165efe0,-0x26a53cf8b5a3cffc52ebd7724170,-0x4362190128b697c6f26fdf03f00,-0x6093597dd3d85ec5561ac16220,-0x729135e21a249347bb8769476,-0x70e6433503e331eecd44af23,-0x5c7933695400a7e6dcb9551,-0x3ece16547bbf4b753e12e1,-0x232b3677bfd3fd331b130,-0x1014b77c5e9449a74f2e,-0x5ea3bf92c628c274ce,-0x1b5f708585e0f6d42,-0x6023ae5d9779a22,-0xf19bd395579ef,-0x1849816f8539,-0x12e3132f8d]
def m10 : List ℤ := raw_ints% [0x0,-0x12d58f3c1bc90d761d9e8a9ce5ead540110900,0x22ba9d1c6b470dd56da78cefd320d9f817283c0,-0x1f06fbbb5d49557c3741af6830729141bd462080,0x11e426a35140cde7fd578e76b238eb98e41b1c130,-0x77bc9744b16bf6cfe0e8e4b1929ee0eea576d3ba0,0x26b63b916b785997227bb0b44b08c872a97ed4c230,-0xa10ea74f1c851c038790d480e9ac88642d17845e80,0x229a8bb648b16d547919c2afc767fdbd548352a2c7c,-0x643687a07cb1283dc9854d456210fd6b9fd3af55f28,0xf80b0c502b9d30db49c858163c842c51ceee9a1d09c,-0x21287adf0cd6a4f3720e16c9f18eb656f40c48623a40,0x3dcf44595d18117eb48a79ee55038ddd606520854358,-0x65169977f5a261da01b14c0782b9b933c121e59bdc50,0x91cf598410a6715552998489dce700f0738f59ed3118,-0xba3d1727af73812e314e5c0ef0df757506f3b0224cc0,0xd34a607067ad0a41bf49dc98f7c67d02f9308d67421b,-0xd56580d977c1a100468f527a406448317c7ed0ce8c92,0xc02682801d1c86223b89c5a5bf8f5b287aeb4f0423f3,-0x9a62405e32ca8dd1f7e959ae26c1991902dc850ec410,0x6eb3bb7da6faa17b6e63beafaeac06aae04f1f80f6c6,-0x46d0c53d64ce903cb67ca434623fa861495344bf9834,0x285f4d535593d0497eab6d41bd703913f0a2f61e8a96,-0x147ab847c573fe9574cdf2b172c977e0a9bed9638ef0,0x938ef85108536c7373051cec86c0905f6d319fa806d,-0x3ad0f91e2a806aab30b8cb5924452514f1d1b88b52e,0x14ac6a9b85f77421bac46018f7b22eadf4623c66ff5,-0x660ddf78f0358d452ecee0ae2b621d4452004c5a60,0x1b7bb705b25e37c0a56c05c508bd4d59b3541609cc,-0x66a98daf84035cb26e67b363447f2abcfb5f7e2a8,0x149bc32ac8db9fcea884efe034508fe830e9749ec,-0x38591d6b2cd38aa30525fba1e7f4e1d5c70ffd20,0x8192cd62572716d1af178d08349daf4897e9c35,-0xf6df55fce5dbb68b932098ba93c1fe530d8eee,0x17e8e35ea90fa3e7f46381de70867dbe923bdd,-0x1d70187c7d7d26c7e16bc559066b180a1e9d0,0x1bf1e97c721b63000029d5f5e84bf3498c06,-0x13a94a0bc5dbf03346a09155d819b68def4,0x9b7e4ba61906ae18f8b3e2d4b0afa4056,-0x3213d70bd9ccb531a9598e2f1ded05b0,0x965b59aa48f08a18049193a48de3a7,-0xdc0aff1c85137e8a1d07873eb56a,0x71c18464556c9695870decd3bf,-0x9e1ce47490de74cc0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 22 56 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 56 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 52 indices rho q10 m10 10 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 52 indices rho q10 m10 10 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r11 : List ℤ := raw_ints% [0x6b0fa79fcd9642e8208fc1eeada00000,0x91569c4c38f4aa47741ef44284b20000,0x5d57ada39cbe12ea35916dbcdaf30000,0x25bade9ae6b5c4a2ce03fa7fe995b800,0xac56566314043b429859f6619db1e00,0x24f584edbfc00e6921005fd38cd1380,0x62ec65a73b3e61d0e80fd6bb9f2920,0xd3abd2b70b56f884f2e403d6a22b0,0x1701b27196db70876e9aa3b3857f0,0x20e06dc5adf0f9440313c79c6300,0x26df3d17e2546a66d460a635782,0x26297ef7f8f554e6ecb9502957,0x1f1fa893e8cf799866d01f94e,0x1508b9d305f7b37c13d47c26,0xbb6130b2a78a0bf974f574,0x551ba3fab771a7c03d682,0x1f0ee4a69ecf2d8c508c,0x8e5f4a15a486009980,0x1ee4f59419ceea84a,0x4c8a4716815a55f,0x78e6af59041d6,0x5bd821113f2]
def m11 : List ℤ := raw_ints% [0x0,0x2223139cf25c686615af5b3c60b9a2841ee0500,-0x3e6037dd1718ad1a48e96eea8602311059f8ecc0,0x37356e2228438e04e66a497a6e37fa16ac3fa4a80,-0x1f87caedb7345f5908064530a2215509c7b4462370,0xd0f10d6a8739b3e0ee8987570cf4f168df4792e320,-0x42de6eb0b1c369b00a06978a47a6a64a7c3919f45b0,0x1134d90d3df44da4d8d9f6a9d4e64f217752c0d8cc00,-0x3a83be752f8284cd6f0fd1c2498ccd3051c45621890c,0xa79542db30467071c720d2e7925a48c5bc424183e208,-0x19a0de6e78ac406015e0ffd0f6dc8e7cc4b41ec1053bc,0x362b2326b6ffc289f3c4820b06b22255cef9142359820,-0x63be133a8f18b5c8bc68635e6cc9d795be06ddd3ed3f8,0xa110fe9641137d49e0bd13a9398d2503f23594ebf7c30,-0xe5487af43ade8f80808f13e4aaca2b109dcad89080ad8,0x120e22428c2e42729c85dce94178f6137c357644927760,-0x14320671408ca7708108f79cb8da33a2ec61691b8f0f0f,0x14191dbeb37a0e34cea0ef59b966dbd13f47039dea06ea,-0x11d24677f8523b5f5514a901adf6d70dc346d9b4aac7db,0xe175e2f41e734e72891de0de58c9845577aa180a9f8a8,-0x9efd20d685389239340b3ed17aae9989990ce2dd43aae,0x63f12ef72d9b51b37bc3746b4d41bbc4000852d816d8c,-0x37f196e30717fab2d8c80b4c3a21459e35b899b007946,0x1bd686d3dc9c913e21cc8aa4a15b4dfdf8a0b65509db8,-0xc490aa5b71f7af737d1386266819d68367267fc28a59,0x4cb2c31462100edeadd4fee47f58c81d05672ce58aae,-0x1a5bcf93f2db3502532008392b3605ccf6414dd6cd2d,0x7f0d16459721d6160082df552ac0a5fb13d90b0e5b0,-0x215bc25fcc185c9d51f297f201a027112817fe6e39c,0x7949371fcd0613b81aa4f68ac3bdee6d0c10e4ef38,-0x17a72c86dc7142db6e6b296721347bcd1957ad94cc,0x3eb1dcc8896f2bcb2be54bef8054e71639192bdd0,-0x8b6aa1a67ebbe61cda64fe419b200b9a595bba01,0x10025dddf677c2e1528f1c90998eebe5e32a75c6,-0x17d831455705ff8df6248c0542ea23b27b37935,0x1c1be8af1ecbe409928dd20da021eee71e2588,-0x196ec2561aaebcdd46d0a891bedb7acdeacee,0x10f65c079d5db39fe1904b4be5a1bdce432c,-0x7e557a6b3a77d81f6e8faed93bd7aca886,0x2602f5979ab4ba6beaba8e18921471a98,-0x6996ed9736c4163bcbee061722260eb,0x8d4597f5c3b02133329dcfd4e725a,-0x41d01f5221d78ca22ebdf2faa27,0x50ffb4e12be785e200000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 22 58 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 58 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 52 indices rho q11 m11 11 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 52 indices rho q11 m11 11 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r12 : List ℤ := raw_ints% [-0x2089ea97bd141678de16633f8516400000,-0x2c1ee68886084b0d16620599cd15740000,-0x1c4cce7c4f1cbb6e8dec4098ab8c580000,-0xb6c51cccb431ce4b29a5fbffa36deb000,-0x3418b172bd876ef2dac0af4af8fb72400,-0xb274d739622399fca6efc8822ca74100,-0x1dcc14cabc086c1be4edafbe740692c0,-0x3fa043e0fdbe87228bcf2d22de46b80,-0x6e64a7208427beeaa46bc27674dd10,-0x9d58b29cc8b62059bfed5c0705c10,-0xb980ccc2241cc3638b3407fd77b4,-0xb5860cff3556dbc3119157176f0,-0x9380029870ec86512bf07ba643,-0x63443e7450e2cea65972bc5a8,-0x3700f2a5ddb2e6ccc300651c,-0x18d8160d7bf5afdd137f4e0,-0x901f0c99ac0a4f102b5a2,-0x28f9ddf83c4cff9cc120,-0x8cf890d824f3e59038,-0x159668be5a7d5c0f0,-0x21a2e0ac6808343,-0x191ded39673e8]
def m12 : List ℤ := raw_ints% [0x0,-0x3ddf938c77477d39074dd55d6f50768f77f69100,0x700edcad7e0288ccabf0281acbbb9b6b57132d1c0,-0x62483d9ae6fa6839db6525b144211da1ac6942e480,0x379b39e55cf974b4185645c92b1f9380f6aa081deb0,-0x16cf1d7cf301ac650a78bd1c6e1c3c0d11a2841858a0,0x73a3d6e82c1bb112a368108023d2c0096e46a43c7bb0,-0x1d73dffbd2b4e1c614580ba91c9e7c46a13bc8a7cea80,0x631b862e176d34f5aa6daf59171900a81ba3a2bf74cdc,-0x118c2293439154f04234ad849d424c9dd1bb5d8b55eb68,0x2a74721273baf70c9571c65f145647f924c45333b0687c,-0x58b169acdeba3dd834fa54b56c3dd940dd0dd1417b1340,0xa15ad49a51dbfbf5028df1923b1e559033ac2115107278,-0x101526f9b92dccba7f9cd5576413699204fb547ee2e0810,0x169964c4483182b10ee0102671a39865113b8ec9dd46f78,-0x1c17c93c80bf8b345184e1eae268fc759edecf04cff8d40,0x1efc7da5a6ed7c19ad5640b0d62ee322089aba9b6e21cd3,-0x1e64223ae742b92dc8817f76aaf0c8729943b26c61a57e2,0x1a8ae0feb65877b02eccb98850bed031b92f6f709fda08b,-0x14a83e359e918e549f1edc5a302e240cf39d71cc27143d0,0xe53e556293d80d8539669ca1a05eace75cbdb7e44f89ae,-0x8da0edd1ca88d53907c8d1dc9126b2e11431e264296a64,0x4dd9952f696f0867c065b7bcfee4ae175d7eee401e4a0e,-0x260172704f9ccb059a2a43865a4920899176a821014110,0x10703c8a12ac6630b1e16437fac2ff0617cd1f7aad523d,-0x64787ab70dc08bafa2a7049bfde5bfd52ab4060b066ee,0x21c2f043afc2ad6f9df07854ce78b84292051a6405915,-0x9ee6dc4c150300807e2c3fbcdd8fe74cca66e536f560,0x28ad3dc3792de5cfcdd3218598445700e4044de0633c,-0x8ff21b7edc97e530c991f348f20a2c82205b4421b48,0x1b451ff7e5ad826e7bdc8cc2fc8e218eafefe70f63c,-0x4610328b8e835f22cdf544639db6d1fba5a6bf2b60,0x96a474127da4d61345b183f8a2fd4998582708b0d,-0x10ad65521925b91c073549e152c42272f5c869f3e,0x17de2cf7fd334701d6e2cc4694ea312d5434f435,-0x1aee21cc2d0e10b33e42fdb431f761e733abf10,0x1736b1f2c93539a8e52eb29879bffc299ffd8e,-0xeab3e251449aea50fc42bf3c672150035564,0x66d3dca4953216f0a04334a366f8261802e,-0x1ce2ea1ae1e5298c9a72a8df158acf2bd0,0x4a30cfa1c0eeca72a25ff13413567d67,-0x5ab311f6f78bda4d56c6425c7fe9ca,0x26107ec8db3ddc3db609fc782c4f,-0x297b7de2bed1e7b3000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 22 60 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 60 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 52 indices rho q12 m12 12 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 52 indices rho q12 m12 12 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r13 : List ℤ := raw_ints% [0x8e601519b362244b5282d813e5e5d000000,0xc0d964bda718a707889495ebbd6a9500000,0x7b8e1ef363265c6799fb27bd60940540000,0x31cf2c484e3174b89efc0e8f2677901c000,0xe2d8ac417f634367dec4ad7f7530388000,0x307e16a5b5b233c5123509ebafb941c800,0x815552aa162ce4d5de06f1eb174825c00,0x113a7cc5fe8c6d4cdc2d2eaa560eb19c0,0x1dd4aec7d0201544e396eb9d87ddef80,0x2a6c0dd8a45cf82c128bee33bcb32f0,0x31e30359e5a0bf674a33a74922cc00,0x30ada2a0f681ddce6fc2e95afce34,0x276da58a2817e6f1e63246686a18,0x1a707e3e583494e0d61cca243f5,0xe9710ec2f850ed9a081ff4080,0x68f2485fb1804b89b8398b74,0x25d807ce40d47df040067f0,0xab11ad86f62168ce109ce,0x2482b67c195da360ad40,0x58aabfbfa449cae150,0x88aeea9a6edac8b8,0x64bb379db1c295]
def m13 : List ℤ := raw_ints% [0x0,0x70253b6e983192f75d3d12b959c1d6e4096ee6d00,-0xc95bc0f8cba6c249c543230f94bd660e88d2c1c2c0,0xaf0ab5e92cf003c0de8c4236b8cb03d8b0a4c181e80,-0x6222350d4b56e464cfca77aefa65663b739c65d252f0,0x27e0253af776d75c3de944d79bbf1c9edb1b77d397c20,-0xc835fe6d30030ef1e55d39dc57c315444014a02606730,0x327bcbf2a2bd2554ab18fff5c2581e2835542110d70c00,-0xa8208874faa1847a9634a82ebe725493a30976e544a9ec,0x1d737294b8df525314d33753574a66fabb05234de3ca548,-0x46789d392ec4010392630f0c862d401d6ece047bb7eef9c,0x918bf0ca83d763a42fb9ccbacba011e2b36e54f4fa9d220,-0x105aa11c94b17cf2a2ad164ed9aaac8d4211610d3ea29e18,0x19c30f0dae085338ef50067be70c98ecbde4baa4e59c58f0,-0x23bdc4f265cf12eb73c7fb8ef2f06609671869771bdf8738,0x2bd81a73c232f244da068773a18ad52d028f7019cd2abae0,-0x2fb25d64bc4ed451799f4e9f1c41340f5456be8c86f88467,0x2e1cd263e0c81ba7314ae70152fee4d3c58015853ebd18fa,-0x27ac5740b35de6fdb6e38e423e695d349cb414e3ac26a973,0x1e6569ba04cbceeef4bbff5d3c86806ae1134983bd8defa8,-0x14bd54dabec2a4679de4f5093009222aa77a94d19ca8ac56,0xc983c806bf8f86cfbc4972375f7454207b86c286ca75cfc,-0x6cc94349c737a9ca1b9bc54f405871a072f1509db5d963e,0x341bfc73b0497975f59e4ae7f4ed875f49e5323d91a9398,-0x1617825cf71c38a982860df855bcbc87ed356a7b190c709,0x843281245dd4a10f295fe3190e319eec0c2d889b7467ee,-0x2b7030fe5d2b71ed9dc260bc509a8a098fbcabb2daebcd,0xc7a33c8edca9959115ae82c6f1d9214ad835e299e9630,-0x31d335c4c4ddcb122fa684e9155e6713918cc9ae61c8c,0xab9b0c40523979f4bfa4d1146909f0615a24aa3aa758,-0x1f942a9f2c7920c44ea04e5a3aa47f05d0177b6d761c,0x4ea22cd18a44392f669b75c6b58bd45878aba850a90,-0xa3711e0a5a3278ef41f37705bb4fe369055685a939,0x1170d54efa5c9ea87c0dd58c413b90aade0f50cfd6,-0x17fa1b85a8f8552a197be3c2aec21de1a53a6c18d,0x19e24937980ab58a2c9e98a1177f92a61d417108,-0x153f44d7f545778f5ec67f4168eb0a153be7736,0xcb6dab4f3b062e192c99c8f997c3392afd3dc,-0x53d5e998cc5cbe8a16f4040bfadb04c6d7de,0x15f9a1863b6c709fbbbaaeffdf7e183b378,-0x34271dc16a5bfef364f98cf2b6fda304b,0x3a3aaf3d65202025b935c5a5e15efba,-0x1602430144ced2f286fdeedd52437,0x153d11b9cf6905bc8000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 22 62 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 62 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 52 indices rho q13 m13 13 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 52 indices rho q13 m13 13 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r14 : List ℤ := raw_ints% [-0x23aff039c5276e25ff872d9f3d5fa6ea00000,-0x304addd7b1370fcba6f0b5c7b13b7eb620000,-0x1ee8621cd7098d626d85a456e826713a10000,-0xc721a533409fdf474fcbac82aa9cd8bd7800,-0x389c53b17cfc252fa1cbddbe2f3970f9f600,-0xc15c13ea8e6c367934130b8a2a88a19b180,-0x202ee0590013e8471649f1debeb1d86cea0,-0x447af354ab0b0178381cb7745f3a0ead10,-0x765b2de81d9273da007da21f0e8b5d6a0,-0xa7f9442ff315bb11b280fb8ffb3a0280,-0xc516b1a7c77279b3303c59d4cbb1a02,-0xbfd5bb217382fdb421818ef56cfed5,-0x9af2ef9a3907d83f2b370b1e214e5,-0x67942c29c0c4f1eae641e44420f7,-0x38f4b9690b2fddbf523c89bbea8,-0x19809c9991d6589a739f559d02,-0x9276ae176af8e3806304f356,-0x292919b532a35cb2360c08e,-0x8bb0ea2ad9d64a489959e,-0x150cb1678c29ae1df769,-0x202b9a3ae648e9ce3d,-0x1776bad146c1922b]
def m14 : List ℤ := raw_ints% [0x0,-0xcb437bb873d9da6058feb1eff2af557d5119025900,0x169e7bb8009d20a3d9d616db283abaa9b4f3dff30fc0,-0x137e48a04f0ba0772f4d8de43e9f0d36dbc7df1adc880,0xad4d7959f4fdc4a2f0a234fdec49f1be8a3950f2a0830,-0x45c64f06058d5dbcbfe9e278dac1dc9485227f8bed9da0,0x15b052ab505368f24462149e6b69ee0b33c02205ecf9130,-0x56a5e9fe7bed6e1995d0310931940f4e954e70d9804f680,0x11da872d1be88c037a027ea7ee25b5a21df57a7c9abb203c,-0x31847259e331a839706c6e68bae7303f65653f48254859a8,0x75355d7ce4f5786ab52f93338c236184294a741d0159f35c,-0xef5eb6fd402d0605d8c90a47f166f024bdce4f7ab3000c40,0x1a95ad0a7b4a7c60a917ccfe1b855b174c0ca5099b5af1098,-0x295fdb3e4c42110fffbf554f02bfa293712baa643a03addd0,0x38af3ce525cda816dc3c54217105c34a4ddd36b7fa4d222d8,-0x44a1cadb6c00e54870e2398232e92b8f415da59601b3cf1c0,0x49a7107f3eb541cba51c1a320054135884b910d9465ce8d4b,-0x4633b40513cb25b75ee34a87befdb973a9e3b1cd69786ddb2,0x3b825846c070be16c39dbff0e8c0aa9a731ba260a91bdd6e3,-0x2ce446476d5238294d009a0430d3a68c4c898e03d58838790,0x1e22dc20f96ea4c6c12ef04b6bf998321220b684665eb6b56,-0x11fdd4001d38d439c093e01172f510c788f5ab9e0b2ec6d14,0x98a3ce646cffe18b023b6786c9c60fa6282684ac9411fbc6,-0x47bf6d0ca8fbe500f1fd6ce0d8d8e6a6c1abf62b5cbfe430,0x1dd13a65d83adeab1141b2df9e9e4dfffa18c07c93f0af0d,-0xaeb4128d15b502bef9c45a95dcc7e00d0316434bba4f9ae,0x3822bbeb05b0d1a74d8bf784607a2b06615672b68b7f5b5,-0xfbee3b38189405284a358e18dafa584bde6b7936432460,0x3d4d25f38841439fc29439313cbd1cc8e50b3abca2f12c,-0xcd7a784171105b06fc6302f9be4b42b0638277eaca2e8,0x24b9cb9caee9ef3e96c464ac67fb2604a9a15b189280c,-0x589ee35665c06eec6e9a758fa0c71a6e6acfea3ee3a0,0xb209a8616be8a2f5b73dab9968a0be2c30d514011a5,-0x124ec6e3507162640e3323343abd6ba38f73b79700e,0x182b80c4fa0645edf25af9e8c825d40fdce4c7f14d,-0x18f486e750690b445b19133d0bafccd0c68fc5450,0x137fabca420be78e9a761064332b294e5a499cd6,-0xb0b2a6f4720acb356c9662d6d9929e00116a54,0x447552fae75b8c52ca3a160a1123881441b46,-0x10bbcb507c56567143cb0c30de67dcd4daf0,0x24acf81085059f4ff386421f5d6be47fa7,-0x25618eb339dce98a40ec3bae7e36b02a,0xcb8c002cdec87dfdf8f8afe244bdf,-0xadef2c8cd7d0b90c0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 22 64 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 64 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 52 indices rho q14 m14 14 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 52 indices rho q14 m14 14 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r15 : List ℤ := raw_ints% [0x8501301d4af65560cd62745c695fe129600000,0xb3d36b1cde3e6fd006386fad788043147e0000,0x72fb1e78b85c5c4b406db329ed57eb8d6d0000,0x2e406821e96dc7ecfb751195e85b230d5f8800,0xd22443f98ca8c887803d841e8910896255200,0x2ccdf1fabdb888c3a564a29c9766faee27880,0x7727cbb1d93d5d886cfd3c6eee550c3f4fe0,0xfd2a677b61f3b2eb499144f3fff45c10450,0x1b4d6403fac55f5659a0d3183781ccb0a90,0x26ad9f03662a9665a3b70c00358439b760,0x2d4abbffec603c7256472e2892e9c780e,0x2bfcbc2e9597f5a039209623da1adfe9,0x23712dc7692ddcc2f40f34d437399d2,0x17a080a0524673d71804da940e2a4c,0xcf3b4c829ef45c6bcc53885dbf2c,0x5c777e13f6ee37b231b9aaa2756,0x210f451cc80e4a98cdd05165b4,0x93fb607d4fe985648ce9a0ac,0x1f39e67219e7f19960c5d06,0x4ad535b955bf29c0dfd79,0x718fb39aa205d12dfca,0x52228c7d134d59420]
def m15 : List ℤ := raw_ints% [0x0,0x1706a503e51fadbcea14da282e7ddcaf322fd5441500,-0x28a9a83e2fd07543982fa2396894ad01330505e88c8c0,0x22bfba3bfeaf24502f83a9fd0140a2e87bc729203e9280,-0x13240ed9bedee305bb51ff51eb70ef8cca9af2f68a61e70,0x7a334ba780d2e624c473e6317b046c13b2ec2b9e1461d20,-0x25a24fd2e64a18144a4cccc4c627146f3fbb1949e962c4b0,0x94ea78345dd8d2c9095558a4c78148420901c1be1981ac00,-0x1e61869c98acf297e51bf33c946ed7e7171f2bf5ca8e0c1cc,0x5366cce933845751a0f4287ce90d067735d16eee528c94288,-0xc353045028d3de7401239620fc294b0b14ab81391e3dbc67c,0x18a86dfbf2d3e992e3ccdbc22581cdeb60d14d798021e34420,-0x2b5155eb407d9add0ba4dcce7d5b525f730ee05cc823cfb738,0x429e830b1d07212749b63633003bda64ff60432daaabf187b0,-0x5a25ecdf0a8a9c205bfa916e3ae5c1de2a490b01fc5baa3098,0x6bc0432f668253623883ff0673fe8c54f2b081ef795fcc0a60,-0x7216f34fc6178ab79b70123ff091515acaf34a3fd4eee2c47f,0x6b3ab892c8ac3b258cea9e7f9bd511cb71a950665e21620b8a,-0x5992b3a87a8fd840f17ad73a142d82aa8602f91c162dcfaecb,0x428a7a600228e5573ad8d985f3d6bb2dd22b5f068575ceb8a8,-0x2bf4a8e39f00123614cd31a43b3c30958c2c7f6389c3a01cbe,0x19cd32d4fab952e0665a784655ff9162c27cab3107a5b56eec,-0xd7094d6bdd4c9882f75aef3ee20a0a167f0f108a47cba2b76,0x63324e333cb2b9325ecc149b76b4a0e7f20055c3c508dbc78,-0x286a1f1c23bf9533c71f76a61574ac0ddeb5b9444ee04fbb9,0xe7de5856f56124bd93b9d6a17df720dbd80527eb0475a22e,-0x48dc051066fb9252c412ed6440edd6e94d3fefb1a3b6d1ed,0x13f4e40dc286a92331dbf13cf8cf1884da3f842f4c397eb0,-0x4bbf9931426314b2aba60e44730d78e09208ea25b5cb1fc,0xf717d1bcdd44331f0d62c1cf2eaf537f9f4d835741ba78,-0x2ae422335483836acd11e8d9f26d0a73bad929252cc0ec,0x64485890d8fa4d405fb1586d9746c2dd69e58160acd50,-0xc2b0ab73418b7af51489b61e59564272a37d397b1f31,0x1349aa32f6ca3ef9d7f64cf0ee85eaf148371bd8c866,-0x1872199f28cbd718192c9a18b03c9b9582601b100a5,0x18218bad5f2a6270519e52e847dd09a1756485d288,-0x11f073330b6751afc308894bbe1ead6f2f6b9673e,0x99c9dea3000871fa87a022cd30d757835905d0c,-0x37fb988da53059bf809320cf7448cdf6274076,0xcc0dfb6b89c961ff16252b93333141e63f58,-0x19ccdf7c5dfd84803e82e760dbaf0a0532b,0x17fecc2d9f2b9f373dde7f506b986a71a,-0x759ec46dcea37421eb355cfeb8cd47,0x5900e9e30870a02200000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 22 66 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 66 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 52 indices rho q15 m15 15 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 52 indices rho q15 m15 15 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r16 : List ℤ := raw_ints% [-0x1d19522086cd0d25c12dd298c9cfdff804000000,-0x274f99cb9592c1f5f86743ae1ed78ec0e9e00000,-0x191d123d8e2cc2310eae62957bc2f4b9ad220000,-0xa17ab64e08293cabd0c7f248e63f4906b260000,-0x2dcea4a7790b1e45d5684d7aa54c6bbe7a43800,-0x9c16e879f50613d4163e01c0eef11998521e00,-0x19e9a3b4caf6d395b1c6f02b5f562202268b80,-0x36fb51ad926c982ad13bac8a84a0b526f0a20,-0x5ebb24b2aed350318470ad2223e0a92757b0,-0x85fc1bfcad80b479a88691d4f129f323570,-0x9c9d98b9d2e13d090eba2ab50dbd5a65e0,-0x97cdfd2667709f0b826bf0592e92d0412,-0x7a0c32b5357b2b0f22c3d866e911f2b7,-0x5129f932b9b2d2b62754ba9c994a48e,-0x2c5f5c7614ae49292e02e1939a46d4,-0x13bd287c17a3705e278843f03e814,-0x7087914cd6414aeda92bbb8e4ea,-0x1f5c075975404eb3f6dc32b30c,-0x69685d1fb056194604e166d4,-0xfb526995463d8e9e379f9a,-0x17b23e20609d7ad6fd9a7,-0x110539c037aa27b9f16]
def m16 : List ℤ := raw_ints% [0x0,-0x29bc0b170f496ae66845cb68d4441ffd8af6b28b66100,0x491db6f1e8643e391736a16d60f76041fbcc5ab57ebdc0,-0x3df88605b87832ffdf7d2633c1e6773f26ecebcdb27cc80,0x21d8d8a79bd86aa3c0248adf826785db1ad7facd18479db0,-0xd633e03c2f008b6255d0d5c69ff66bbe3c22bee5b3964aa0,0x415f72b40f6db789ca2ae89845b892aeea1e9421c2e1362b0,-0x1004365914cb5dbc8103ac5a8048d07fa6cb4f83aebc8a0280,0x33c6c0fd2032136205095eacd8f7dbae2cb7cdf36a104ffe9c,-0x8cb6be40bb99f69d6468e5d7c03aef3e0f0a11fc6c6f7ab9e8,0x14620fec6c18e60c401112f0ba2df4f4299c3f180faa5d9a93c,-0x28ba3ca008e045ac72632b8c3d62d67af86acf9fddb2a028540,0x46bf59765ee3f732f55430b1662a991df927fba474ea42f95b8,-0x6b89c5659fad2aea0c3c83b07b8436e7ed6278b7d2071b1cd90,0x8fc1b966ecdb5833b505019f1c477ae7f2bb8eeeab0f6f0f338,-0xa9a89a134dae0f097dcb4032e56dcf7b4643514c5de95baba40,0xb145d4e096fa07d99342c500777c528a93d614c172728a6b183,-0xa451f1c2e434b28131439b66f87ae5c295f1ef8e0f4e5fcf202,0x874958ab2e6e4202dfcec466c87d6c98e75b23af1baa7b71cfb,-0x62fbbf9694116a6f4cc42b60efc68bc8036f06009cf742e6750,0x4059dc30b93ac5f68e3b5c5ca9bb3b9a17a1b0da4602f2451be,-0x2524fc25222f48b584e2a20ef05d03ae70f387d46c5adb28c44,0x130246fce1e342117fb946d0c51ae149f7c9fe9c11073cbb1be,-0x89b4795f7406d5387f0caa41e5ed759dc997ac1ade95dc6850,0x37017ae08c42c069bb706063e37f256f70d07a3ca06d003edd,-0x1350987efb1920321604061d54a7c940878f94563ceef20d6e,0x5ef7dc0e181f0b0e4165050b59219ac5e238564ea59d109d5,-0x1966d63f33bdef13e592a03015f1557dd045e4f0c71349760,0x5dff87f1f13d7bfdb3506503e9b7d9d4309c26c6a358d79c,-0x12a61f401bb7b1c87a7c9203f78262f5b8acffdf8c3fa188,0x324c0991ca7c897b25c1733195005f3422c13008d01cb5c,-0x71edc4d2acaa80bab2d80e50430a89b6a9ff1ad56be5e0,0xd5b3f090c9776b19cfff3db6733b1f3dc11c3cca97dfd,-0x14644f8c70688ca50eb815dd0b4915918afdbfcb3b55e,0x18cdd797300bb3d01b49d87235465ae828cc6389b125,-0x17667bf5af079a81962cd4a051b4370a86e820a0190,0x108b481ba77f0a771c630fb6e5db84eb153edc17de,-0x861a5eab6d17aa68dd1d3eceec77db0fedea59c4,0x2dd7adb1f5d7b5d4a16424d145c005620d62b9e,-0x9ba47ccd348fba837f04daacb4392021c6310,0x1227a710d6427fe371834146641ec6ff1e67,-0xf66b4d9a9b70c34bd2597ac7e1046d08a,0x43f269fd95053c552218eb2e4fdc26f,-0x2d8820de899e70e3000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 22 68 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 68 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 52 indices rho q16 m16 16 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 52 indices rho q16 m16 16 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r17 : List ℤ := raw_ints% [0x607af666b9464c5e56c0b840cb30bcfcaaac00000,0x823e4652d691eea1626d146669cb331e629bc0000,0x53237ab0516eb8424806c0fdd7d66a3096b7e0000,0x2161d3912cca72d64085f41e5006b329c5b811000,0x975ecebe796b40692ea846017ae37f562d721400,0x2034502e3f6a9fcaada06ce7a6164742cc784500,0x5571eacda341060cdaccec342f6a7a3a9de3cc0,0xb513a02058222afb076051a692be305b90d660,0x137921631fad63d31bdb9b7c5c347063c44d20,0x1b8084ac1895add6846b7194a1a03d9fb4450,0x20187ff4932c74582292eaf83c0dd876c32c,0x1f0e0ad61cc92c107b5633fd41479eff8b6,0x18eb355f4004cd84c801e8128c8e4706fc,0x108924290c32342d79ad0f5065ab927eb,0x904b86b4112bc51ea22ed3bf67c9478,0x40047069e0f44590d8289ae56364a8,0x16bdd0085f302388112716d00aad8,0x650ef851852b125b48aaff0e39a,0x15262f920bd88d300471732d1c,0x3234baee83a3bc4c838a351a,0x4b5c72ad222a457fa24b8c,0x35d10b037e20a51a1253]
def m17 : List ℤ := raw_ints% [0x0,0x4ba4d419cbb511c19cfe80ae00bb79fb8bdf239ca8fd00,-0x837fba188c3be9b8fbfb888791b9b22b43341468f5b7ec0,0x6e90b08d1fa498e8e1e7bf302ba82e71658465365152a680,-0x3be4009b0de4e37d3c1728eede69e0e6be9f1fa316a9365f0,0x177cac9e00a2fc7fd86839e45cda6d14298a0858c45f8b0620,-0x71ad90561cb2ce6664b246b0327debdfe56d915c68963dbe30,0x1b98e2b5961424329b8f9f06f6411f38d14ff7f8f554fa3ac00,-0x585ec50c513b3ed7ba1480e963677e756d163af91b5970f48ac,0xedcfbe80b4aa154371478473c9ef079d4ff95d71bb0bcf709c8,-0x2218fe233a9d7fe3965d493337da079a39e14d34cd3455b0105c,0x436917bc3dd1e6ffba61660ee095a237af748366fe4c961dae20,-0x73cfaee47005435f8a469128696bb936a7984308d4e0d9619758,0xae05ab15bb8db6e0afb2d316e09882bbc82c8f1c3cdb5eca9870,-0xe5dbb42efa7493909e9e9e4b71e9d051950cbbb6844d789d2ef8,0x10be604433decdf24202a8319d139e2d1353a7da5cda9caecc5e0,-0x1144883f7b367ab5de3e54b9c4b058fd7f3ae317a9e774d195557,0xfc9d43175c37614ab0c5fd02e76fa7bb5250dae3de06dcad029a,-0xcd049d3c735b73759645cad855e3fff17144687e87318f682de3,0x93c305fa4c2d97f2ce34fdab55184bb97722f4bb1cb962c963a8,-0x5e8e02b1bae8b18b0502fd094be1f039ac6d74ad5f3b4ecfc1e6,0x35ad3dd716951a979c1fd4ca8f2ee929c3a3ba6406aed891f75c,-0x1afda2ab1e5fb41a38360605c76a93bf1428c4d1c300f57eeaee,0xbfeda1137d2ffe0764c588f00c0176c13a8361eb68ab66c3058,-0x4b2bc005da93aba23f0a40adcd3f02fdc39252962d7f094d869,0x19d987ffb6b9930a9743b5dac92ecbe54d05e4366f6f7e5816e,-0x7c4d963d6f1a47f16997d8e6ef6a437a0ef9d7b97eb309438d,0x2077c5c4748f33bc5ba926a5558d9c78f4c53e680429035f30,-0x75215c9d53b622e80d87f687e630afb49108fb64e983587ec,0x169cc0840849bf049d229896787bcc2db6c649c52c2ba8098,-0x3b37bf66e5437bf0432d38ecf361b703fa0c9e4c5171a13c,0x81ee63b5992419a58ce1a8f99dd87ecd6b2de27beb7b610,-0xeb6e60e0115118f06b4bc5fa2b72edf5304f4345ac61e9,0x15a1f21e6eda606841faf3a0684ebf92d6f1d96a623376,-0x193edd5c21f2a2628dc07f115f2aae2025973fc37347d,0x16c0de223563053ca60c5f82cebcefe684db66477a08,-0xf4ac805e9519c26fa1941e5d05179403e945056b06,0x75253e080e8f69cfaf2db2b07918dab9f206de2bc,-0x2595f5b8eace9cb2b74a92706258d0376e1b9c4e,0x76cd0e5aaef8403ce2d4df7dfe24535283d638,-0xcc72cfa952adb1bbafafcae4a90a2dc6758b,0x9e246f6582ac741dc1e6ee360ae41e887a,-0x273d71e00dffa90461dea06612b4b557,0x174967752313485c8000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 22 70 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 70 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 52 indices rho q17 m17 17 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 52 indices rho q17 m17 17 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r18 : List ℤ := raw_ints% [-0x1310f42c7e566baddf804632d0b6e43da3c0e600000,-0x19b88d8bee01984717ec898fe30e7d9169ee66e0000,-0x10680c093a7d6e44182d1e74c2868df2df23c1b0000,-0x695132037c383b2903e62606c28f6ffe9837624800,-0x1dd25019931368f6547fbed0fdd55fae4fc0386a00,-0x656b08206fb435b3b06f8adc02ba988acd9902680,-0x10ccf12502f25cef3d74e8e020fe9d1f1de48e160,-0x23908017e33f0e4b2c5a1b8b3b881d2f451136b0,-0x3d1eb641ce4efa26d789ac7e7b80d5187fb7440,-0x5634a1568fe36e3afebb675b56b8c63acdd0e0,-0x64756a0ba94b233bcd6c60704ea7a3d0200ce,-0x610bd22775de4deddc69d739be74f8eb58e7,-0x4dbc18956850a05ba2aa5feaa5acafe5a39,-0x337be721e0db52fa04a6abcbd984128b2d,-0x1c04dcb319e3abc89b5e78e93d6ae24a0,-0xc66bce90ea9438e58928406ce013896,-0x464cf5b75d89d7beddb190fa185b5e,-0x1377a3497f5c3fde2a9e36097321a,-0x40f7c1b031e1726b33161e7275a,-0x99a54eae88b3a3668641a44c3,-0xe5a36b0bff4bae1dffb1e01,-0xa32e5d56b5ba0fcd0d669]
def m18 : List ℤ := raw_ints% [0x0,-0x891ac06ec138302eec8d493b6153cd17ed84708bf24a900,0xec8cc6b026777b45ec0ece5c0794e568d4bd58fe3d5d5bc0,-0xc55902a9fcfd3a88fee4d6860b73aaaf3f040db7f7b59f080,0x6a0a438413fbd6d0a5d84d0f7cf2e482ea4ed6ac68d332ff30,-0x293d560b3ba4362ab101ad44b1de4d796a2029779c51ae39fa0,0xc5e2265bfbb20f654d31a91f9c68af7898c48667dc9cf085030,-0x2f9c6d0fa3b0260dbda8981f4200f71f5d255685a3d364ef0e80,0x970c1446851c41825ed3216451467ef25992449c8411a2d9fffc,-0x19293e84932ca3c381d1a2d4d0e10ed5732b92504664a71a41c28,0x39256b15c7d8bb047cea071b5e2131d0a3af1919835bb8d11821c,-0x6fce1c500aeb3d7ea60c4c07353e3550291a201449dce17ff3e40,0xbe01bf25907d214f6a5aecb7748304d1e63acd479659d912979d8,-0x11a4c40f5c0e57e1c0aad622b012424884dfaecb42413016e26750,0x1707f34d87446d661d357b8f9a768dd290191660f81dd01f2b4898,-0x1a836ce5558498b033eca3314da655a4db638ce7ef7e595cb346c0,0x1afe14ff1eca219dcd92a2366e0a8486a1ea9032a5efca373d577b,-0x18593da7d2973806cb4b5549f94fdf39f243ba34fc8ecaf26de8d2,0x137b8cf35b8731ee408a611db55cd7cb127c2692a3f2a498c138d3,-0xdd57a9f7ff0008349d4813643241b81dd977bd1363fde14033310,0x8b6f876b98d3e2f98d48e77737fe173d413412f433546ec0b32e6,-0x4ddb48909e2f4379ea0bd046bea037d6a1100ad2eefee0c3e9bf4,0x2678b600e7a88530371bab76baebeed265207fe65d4c77276adf6,-0x10c8e6faa235d98a24fd5b3b66eb9fae77b1d59913bac1781e570,0x67241fa29ef888f11349671367ac524bd6bd3b6bb2c6abdf39ad,-0x22bc8a5afd2d3ae4133772934c643ad3b4eb598aa5f614a1da2e,0xa35de09b0efbe5cca5a89b0c225a91c2f7f8776bede324ef975,-0x29ab87421fc096102013ecc1fc332a4273fe7a1edc559938e60,0x928cd5d26d0585e1a33a17b42208eaada398333ce5cae7ba8c,-0x1b872dfbe89865723dd5e7ab3c98d8a9cd3e17e73adca2ef28,0x45fe3a712f2274614c5fe88e072f634c064a24ca4e1256c2c,-0x94bce1e1ad05ce5f0c37fed02b1426807371a8e8a090e220,0x1044a50304f3fcf744c33e00a0f48479a590012af7c56e15,-0x170644795c89cb9fb457e306aa65dc87d2c1d38b13b532e,0x19c57c3f8a06df57e4329e5b0092bc3d2a9b5d8995e1bd,-0x162e8bdad6308f5e4010dac9c895418d2f00b139236d0,0xe2a597d5d1ca31cbf24c1671ad671d83effc73c5ca6,-0x6680d62df1ecf2499ec7c552f0703e7a5b9a2327b4,0x1eda0a1bc8bccd33201cde3f19f87fd86449b3b36,-0x5abcf9311eb8b87c91c24c79baf84f2b1ecdc30,0x8fecbb10a0a2c2c777e70b6346cd174483da7,-0x6579a530959b22182ce39d46c47947d4aea,0x16a7a39bfa74600898d40acc5f8701fff,-0xbe81fc52e742be4c0000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 22 72 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 72 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 52 indices rho q18 m18 18 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 52 indices rho q18 m18 18 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r19 : List ℤ := raw_ints% [0x39cfe442678293e4c5d4e89c29b2e2d8f44759200000,0x4df0fb888816200eb6aae317fa2f1c46a2b6b28a0000,0x31aea68931f0e3277633732b68dc002f912e15c70000,0x13eb0624226330ecb61d48c14d1816ce71fae6605800,0x5a2b0058bbbd329f59914e64398c82bdc678d854600,0x13261c2bad0a215448377b60acae8914ce39f8fcd80,0x32b4e47a4da7e300fe7bb2ca1477456077e849faa0,0x6b3acfdbf4768ab2b1172ae351ba782dd9c5c03f0,0xb813e95936a02015bd99ee6feadc7f00717ccb30,0x10350f1d053dbaca8a51b491d843de53114b45c0,0x12dcb0e818aaae5f7a22afe06467b8ccb14feda,0x1231f2a74b59ca190b8df787718dc1b201dedb,0xe8d29700251e4446389dbc5e48fe9203ee16,0x99ee7e94f8ee5ed3bc188c3678325c41192,0x539d0fc3a940ab22e557bf098a5ef3a764,0x24eded474fd10a40cab33ab98d2e775ea,0xd0daa3653d1a7ede9ff638f1431045c,0x39af0661a254a4daa81da676f52818,0xbff15fa5487fde8d0568542fe502,0x1c4712282ff980c45e62efd5f73,0x2a1b3ac790b23cb7ebd6a967e,0x1dcb4b58db9f2101009c2ee]
def m19 : List ℤ := raw_ints% [0x0,0xf8807cc8be35d7550cc014bba067e3bb5e800bfda7272500,-0x1a99c618dac3b9dd259b2ea19d8c970243cb95c4ccf39364c0,0x1606403f8893a3a06998dbf2ee3cd915a6da40badc03fe15a80,-0xbbddd08393f53fd48ddbce0b2f720344ad144db2c3956530970,0x48784fb1c994080a1e5965f7b84ca4813921e095151533087720,-0x158d1074be889fd8ab22f3cd33af3bda5b20380e3eb26046fb3b0,0x523d7cfcfa5dd0ea2a3ed2bbfe9c66acd2b54835aac7ba58f0c00,-0x1028c43d152953b06f80e6449139a59e071efddb6efa47bce9768c,0x2aa9d29a79c777662e570f6a4ed5fa68abbe1313c56220d596cb08,-0x5ff329f24541c8a8c3eef2880cc32d678894d8a869bdb00f4bc53c,0xb9cffb541d40892c07729651c93fad9e29b99e5cbd371294329020,-0x1386d923876d45a3bac4721b3ad251056d5edbfc9341439d2def678,0x1cb0b5e9fe89735b73a803dbd5ecf6dc2561d7b5dbf0a70bb6bdb30,-0x250492d554eb0e4f4f2a359e32d4b3b4f27baaf9a063e968d5aea58,0x2a1992a93800d915082700d7733488a1fb6b16467bc8acdb97f8d60,-0x2a5178c25af347dfd64746f99316e6c7cb63a17317f46f7dfbcecef,0x25aaab7e36408bd11da18e328b94570c13202483f24881f4b23022a,-0x1db821a83c0a2d254b74241fb1ded3a6732c71f74f6f4eb23a46cbb,0x14cb1f3a166eaaf05bb79457ad59a88b5b334fea3b14d50f56bb0a8,-0xce5965b4572e1f8f6cd2e9cef99d9c2bd46f20dccbf1630bc5e1ce,0x7157ee3e999658bf1885bf42cd812424adc5ebe711a412defeba4c,-0x370b0922df5ba2050ce726a7e5899c28051e91b92611896a1216a6,0x1793c0d0051262c70f5714e91e59dcfd06d9dc323ef4294fa75738,-0x8e13d2a8233eaed7a32494fbe9e40b0cf261d100c5bc731fa6d19,0x2edd7695e5be8c8bf9fba5018795ab1451148dafdd673d826fdae,-0xd79238f83fc15b389b2b862adb5a91cbee1485b6ac86f3aa24ad,0x35b214bd79e8e507f5066b0abf832e1a0d33cbf76994f1f097b0,-0xb81769f61b8702984c13787d1597652d477f62f9eaa067ce25c,0x21a4d56da46007ea1271e6ed1ad222877b0fcdb85f31bc171b8,-0x530b608a4f466d479a2babd11f7d21d06a8a2c03fcb57aa30c,0xaae39066658ec8ee8b0352cf4f64cc7231ec05f2962c054d0,-0x120c4351ed12a7a3b356b1ab2ffef8176878ce6472819a761,0x18957f11cb9aa5ea257b732544c2d38638501185b1672506,-0x1a623270a44fcfc3b9fe93a0a4474db99dee47d1d268b15,0x15ada5c7fff7a6654228e66c8d1590e0f008253e4e8788,-0xd260baf8beb7899560ddcc48de13cafe2564e38ac08e,0x59d4eae7a660d460b7fd7d499371cea50540e7d18ec,-0x1959e02abe61760eb9cb38a818957e284afe9a7566,0x45580c0604a54fd6005ff530ba703d229b292018,-0x655536da6d8ca940a42edc3814320ac396036b,0x411a736144640cacc9002d0c8aef5a0133da,-0xd1364082ce26848f3d5ed536b88e9ec67,0x616262bbc9399ae200000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 22 74 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 74 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 52 indices rho q19 m19 19 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 52 indices rho q19 m19 19 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r20 : List ℤ := raw_ints% [-0xa8e35e7c59ac259f62c40dcc5556ac488407445c00000,-0xe38f6f729421807330f3ecc361110dbe43a006e8c0000,-0x90f68b2ce7fd92bd0144f9471b216380b2a5889cc0000,-0x3a13dfd8741bbe67943caeba160aa63046a0f165c5000,-0x106b8b3d1620e8d3f00a8ec2fe112da29c53d69990c00,-0x37bfe40e7372c8d675209adf3e744d33da5f35cf6b00,-0x937fc6121cf9c63a3d69778dae2f900b291ac5ce840,-0x137a0765aa7f24fecafb6515563bdbc7004dfeb06c0,-0x2166af0d740c654ed194a83ab8d93e170c3e8c4050,-0x2f005a302ed0e1c8ccc988518c5a507df9ceb40d0,-0x36a28049be1ac459aa65f9c60755dfd9d817d04c,-0x34a24742038010a767c3a67a1c5e6ca27f4e194,-0x2a088ad3bb1fd2fcb82017002f0814cbf165eb,-0x1bbf389eb2d558b318e913f9195999b840594,-0xf0bb9a825f0d8806ea9c3f38db8f7a6ff0c,-0x6a1f47182369f03f2320b594a580ee4508,-0x256ea30cba0a5c3209093f1c9a3f627b2,-0xa507c6e758d8d6c9aa88708d42b5338,-0x223b7b5fb40e3cda466d1a0c2e3ab0,-0x5075318fab1e8ac7eb07ede20c24,-0x776a20dbb13c65a0e716ba13cb,-0x542fa02b477c0c0ac21a51e4]
def m20 : List ℤ := raw_ints% [0x0,-0x1c268e22bd8c1964a271c259412bc4cc39b4815bbbef6f3100,0x2fdee9551fb91673b96ce6b702c4157d8958bc28b3797b269c0,-0x2757e9a6114b6e7870c7b4cb4be78f131d186ea11b23b1353480,0x14d09381820acc22c6babaa3d2f88d24486c27794fb4fc12f8cb0,-0x7f741c49612173eb86934db268830521768bb832ed258eb18dca0,0x25974d9406cd49ab631b703f40f3f154405654878dc51a089db9b0,-0x8e3a568fc16c87ea201790d31a2c4d30c902a39a8df53d4e9d1a80,0x1bb2e039950f25fc05587a98176b41610226699163b9c7da133fc5c,-0x4874d442953b339d1a6d60b2b3ce24319d7ef44b9d15602060a1068,0xa1646087b83db5eec3a67183bbfcdc485d11d20cd099ae84bea35fc,-0x1356c30b3122e9d5598f1e8db48d90fcd0496da583ae034853347740,0x202d8855a4272e9f633637defdd8591012ce0890a8d72f93ef9ff4f8,-0x2ec381a86abd454bc495887ca3fdeb7a6c77d0d757b31f4135d33b10,0x3ba68b5b859d87351f5edbd0f55f5e9b1850abadec1cf7d985f7caf8,-0x43081095fc40cf2cafb30eab98be65ea5d209031c72a792c5cae7740,0x4289a81e3e2aec4fb8b90bd1ee5ef8328de01b9296a9465ac4bd3d33,-0x3a7299fcd9c0b4568a4b329fd43527cdea6fd49e5a6ee0a5b8ea3622,0x2d7aed3430ec884c88d81f86f5994a0e1bb487cb17e17fd21e82e06b,-0x1f5bf26abad6e8ed3dd99fb3fa3b83595720241f7d65a59eceb51ad0,0x13270c41d154f876ad10e0f1dbb299a3b29b093e89bfef3d6f12b4ce,-0xa59a06f5631bbf406d14bcbc770bc4ad272d752c796a9c61abe3024,0x4f0bc2dde0d02f071e51c210e8359712ed161c7fdf8bbddc8b9826e,-0x213e95fb48fe5add099ca48e3622c854b49ae6c82a5afb51a2b5390,0xc478dcda01614f02b654812b65c6af24f8b40dbb11305babbc977d,-0x3f7a1e037de1d3273c12acf7973251d576917da8a58b08ae36b7ee,0x11d9517076ec2bbfb9565a7af7144f83f5b763216f3f7632fd4895,-0x457701ffb42a8992f0b285fb2d0e2041d405026b6f4ccbba98960,0xe827616b74bb729ccc1534e6214d5cc6439031e30864af5c5dfc,-0x2946b2407b9b0e3614a6f98fa4a99d943589c8f13af1ec3ee3c8,0x62e558f27a7b0205118d32023cb116f12a317349b5348e8767c,-0xc5098bcd965ae1ad57ee099242621b82114d5d6960351cc860,0x1416de354437b95d8ca199bf6ab22e8108bf73e0b6ba3cefed,-0x1a54710258f1068d4f9bfe41cd39ba9dde979f2dd87208d7e,0x1b15a9e39255e77b9debf4e0c8665f5f8a3fecb3e0f66115,-0x153c8949979f23aeb02b6475d3dbeda666c4e1d2d1ac410,0xc3a7bb311ad2460ddceebb810b2cde3aa6fdd76f6c92e,-0x4ed7905f40ca325b0b3e322a71e2e8e804c1cdf29824,0x14d9fd7840965128eb900b511faa69612cbffaf640e,-0x35055f0078d18dfccd7d80d4151ff7ea9a841be50,0x475a5f46c72f72a2226d76edb169d602e8fe167,-0x29c2dbd7494363848fedb62a9b357a130ff4a,0x78b77128b0d8fa759ab46a8f17e2d5f48f,-0x31c4e5c5c68aea53000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 22 76 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 76 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 52 indices rho q20 m20 20 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 52 indices rho q20 m20 20 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r21 : List ℤ := raw_ints% [0x1dd3588e4e7a0c470a89e6bd751952bbc2d06476c800000,0x282a59090edd342bdc3c0b21d78d8eecb39900204680000,0x19925ff202752a3e2ab8b5296ea0874ccab26cc95880000,0xa3d140cffa5fceab54d718140c7d81e75fe79b04c76000,0x2e48bec751fb2cc856af2eee2b5cbacf80c4f90da96800,0x9d07737b0a6d21484eddf45d97dc7316dc397724eb200,0x19f213542bb46244b72368b64ebbd4fa16bb65f652180,0x36c4eb66e83a89309b6cc7f8196e3f6b614d562c6100,0x5dd685090812534212ff2ca7efdd0d17e1df053b8c0,0x83e9e6be0ef244df2af3011666d1bcb31146a927b0,0x992b59bc51e2857f93b3ecd5fe65ba6c9f9405898,0x93623b625c28fbf63a85b266e747d74ad35a7698,0x758c17832ede983625264dbff4e7f4bb8f7efa0,0x4d7c0e3dfeb91127ef877abfacf71bc2093601,0x29f35a6b05035dfaa5ba9a9f6a15e1fd5f6f0,0x1276208c0f1246607c30390d793483bbd99c,0x67fe4b50138c8f3cb1e363650a8a626740,0x1c987be54c8513b521cde7779a65ef7a6,0x5eafd8c76f65e2403508e2c3753d838,0xddf9c26ad23eae9b490c76d22e9c4,0x1488242adfd532c628ca96e45f20,0xe6d96c91d69d18433811e1db1]
def m21 : List ℤ := raw_ints% [0x0,0x3305e19ef78dee06666e3041c61f54b228972a7644a1f988d00,-0x562a5ee86b1e8e72d14bbe035a209d940a425f44c54c2f35fac0,0x464f1d88896e4ef322baef13444b9f4c09a2a380a30cb615fae80,-0x24ebb792839b4eb570d3163b4c36baf24778255a31be1d2a6ce8f0,0xe054bd8085545bb160bccb3573fbe4032ec26269ba479d22e0b020,-0x41a253b190c5c62f355d40432af717380c37ce6169274b5f60e0530,0xf6436fe7f2cc5ec3d7376bbebb300b29bedea4a4e35ba260ac9cc00,-0x2f8b5579ebd9b454b35db3f45fd14331f39f6efea53aba164a9c436c,0x7b3f9cfea0c7b6125dec8e204cccc75b8e5476722577162b4337d648,-0x10ff2ebaed29360ab3c1923c992f020f348793205e4643722a5e79d1c,0x20445b922254cdd356321c23615b078f4b60fedf042f4a0a472b86a20,-0x3523a27994e938b45609bd380689df079eff271ebb3ef8df0bbe34c98,0x4c66639279284c26c2c4c74129d98b6e3b94b34564224219d26b11ff0,-0x605ca8529e21f634a92470be36e5a60e14cbd97bc9e2f8a5e31ee0ab8,0x6b038e5b65a0fdb8639dda81b6ae92c9be8f352c1d8b47d1be54b00e0,-0x68eaa62ca895130d39717702412b313047402d3c4d37a0ca534767147,0x5af77d4b07f7d2c224bf12ac033759ed1433406dcbfbe3efa26d52e3a,-0x45d1da47d8258d0da1f09832d9a32ab35b505da2aa390fc9681c82153,0x2f73348ae78e4f1abe35070b237d9c897bc62cd7dfe4def1941389fa8,-0x1c8a59312d43d84a3363a1ee99d1cb8db8c0dabe7bd050f72fea7b276,0xf2d09baabff5099bc03190f374305288809a6a18f8b60620a38fdbbc,-0x71ee74d3266dc5a68afa87b7ce78393c11937c0d0c666c7856a2409e,0x2f0d294dccf80f256398fd6e321ab0021af14ae6575eef12c74a9918,-0x110ba98baa8347f3cf17851b3e726eaf8c0fb6e75ad71b4a8e9d09c9,0x564f2d2db69ff8a171cae9e7426b5dad2ece7661ea56e52f7058eee,-0x17bccb118c5ad2b838525acd82bd9d735dadf1446c2534ec372794d,0x5a36902d6e6bc1d1654b38de9e77961b730d523a323f89f97a0830,-0x125e2a319d7aa187ec15c53e8f83465a035f5b2b0045e9035fa54c,0x32d468910078ab3b44f07924d6de6c94c6a95b393855dd63645d8,-0x763348b3308d37ec25be6a680d8cb675abdb4e120ebabe64325c,0xe3f9102f859ab0d62b741d3cc150a13c57f482da2eb99d23990,-0x166f260b9c12de7f2fa08df4deea7871961d46d1540fcf4d599,0x1c48935642ecc61909781fb33ab30bf7583da826ae5fcfd116,-0x1be0b7d0e35276a21459903a71d4c7eca80e249d9f072e26d,0x14d9c7d0eb0b8dcdb90f63c9a33086da6e64cc54bea65b08,-0xb64be6b552fe256a4aaa153fb9bcf6af802d9500ad55d6,0x454aa86342f1897f15698028374312cb93b74c6bb939c,-0x112a7d8cae47d917c52023b618c0ddc52eb66971e5be,0x288efc38ae833a0781ce3e6112a65f990c2245c4f8,-0x323f21047dc22bfb2129f0811c23494a35c688cb,0x1ac8840543037f98467d11817e899b9d09093a,-0x45a26846b654fddd730c3a2e8326dd08277,0x196dce262fcd831c8000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 22 78 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 78 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 52 indices rho q21 m21 21 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 52 indices rho q21 m21 21 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r22 : List ℤ := raw_ints% [-0x51c92252ffabbbc284a3caef05d7195560dd52c4a2200000,-0x6e15784fbee66d9a8e7392231120db8b3081cd9163ba0000,-0x460c625db462439fee1d771bc7563c25d70642addd750000,-0x1c07b4781e670d41757e842900e8185cbc499722ecae1800,-0x7ea1dcd63da1633a6fa2ccac11bb1d2cce7295935b49e00,-0x1ad562c4a487399719ff8b870fb52825279a382ae068b80,-0x46e2f3e58bb8ceca649f3aaf14bd332b64b238153ef820,-0x95848bbf219e24a9a4fdc2878715df971c9d7b97f2e50,-0xfff46105c0fd8936d802e188129eb0dad578c2cb2fe0,-0x1677a275c66054ee78867023bb2a4aa87ae41570d140,-0x1a0fb25cbbc4e9c8a8ee7bf8c1a735f2039f8066dda,-0x190cacf7399275fc019a8f77d3136ca7e29c9a1859,-0x13f468cbed30d69da1fb127a1e07a9b78aee4ac4d,-0xd22fd969508064397048df1fdf977d2a482d683,-0x71a2a80f854eaa64a7c9fb9183f4230fcf4518,-0x31ee42470b6fa8a21c5fe2555c8bfdbb8ffea,-0x118c8205c52f40e8445f3590c04c55c3f2e6,-0x4d104fbf6ea488caa586067108a562afe6,-0xfea62a0ce6a903c6139048365ddd8856,-0x2539c5ef96904bebd784cf38c24c8fd,-0x36f38603ac5daad4b1c174c693f85,-0x268168eddee09530517affcd547]
def m22 : List ℤ := raw_ints% [0x0,-0x5c7aa8f020b13f6b99a7b7773718c982e991fcf65c659447f900,0x9b1fe601fcfdc841f978691f744e3d3534e6fe93e59a1591d67c0,-0x7db1f5b4c977a189bfd1d1173426aa52ceb82f61fbea524b329880,0x418701660395104657124c14d26b09e62ceeb99e3dffe73c763a630,-0x18b26bb7f774caa2b1e237f8649a16ba0ff4a5e1fac31754a86341a0,0x72b561200105759140aad337f29a9b0e36c7923055433ea7f2b9ff30,-0x1aae4d73481a11898e1236afddf4d5ccaa73dae5cb8acdbc0df552680,0x51b827b328f8d904a0ab55fcf4d8d6026e6594f5ee9235dc034d18bbc,-0xd1f86ceb24f52c1e369c8b91823e4f0adb4ea5e6f37fcc1e249faa6a8,0x1cb09063b05b52296b14f335854e2a80b711705ed820dc0cccca993cdc,-0x35f0f2ac4fa796739cb249b06f1749e7ce65407263ddfa345f659e7040,0x57f0b527089fd3a8e4231818cb433186fd25d0b628a3d86b119b5aff18,-0x7d1a9976886c1cd11b6eee1a2e0aeaac0764139bd9be6f27bc887d58d0,0x9c0d120e15f29aaa5bc5f033fdd3d693d968321d42ac4b7343dc4d6258,-0xab4ba79221856effcc02d8941a2510fa70cae9ae3dd189d99e67832bc0,0xa5e57c6db41d02b84aa90e847adb10d005fff00bce9d8bce22079b90ab,-0x8dff9ba31a7ba2c4738e98933079fd21d2007596b5743b3445b530edf2,0x6b84d74785aacbcf7be8ff21c1e90d36824aead60aa10f47ea4b2339c3,-0x4807f522d814820205bcf3a548f50073ec8123f8bdd349a7d279bbce90,0x2aac85c3906886a3f4b710404d60b7489edd30ed412cc0134bd11a6d76,-0x16546bd7e86a1c561badaf13d7be3f00aade6f7899e96e5c583488fcd4,0xa4ce106293176299f26db8b2039d877c8b0a8f9d3dd3a215a2a451126,-0x42d6944b3f9550102a2527ae88631ac249f4c1900aa3d56e68f536ab0,0x17c01096cb855dcd90f7098b053a412337bb2c9d6780bc9dd7793d04d,-0x75ccabb218fb37069bb8bbce56382e51491e46dcf2966fec96fc3eae,0x1fb06637993abc722b94b8c009744cbcd15b7f34b397f3dc12929b35,-0x759a7e079a258408ff0839597c46b4f5fced5ebcfbe1d5b69820860,0x1756d3cb7a9eefbb7d7138dc69129d54708b79186aff910fbbe25ec,-0x3ed2ec9db4d6935beb64afe61e71201ecf9f4838ceefa5c11f9768,0x8dc5dcf255b6b0a0efa6d47994333a8ce2b08f602b08d89d5364c,-0x108a7416f89a7d05a2598e47db15efdc38962f7e00e3360da08a0,0x1921a736d70b2dcbbaeb98f3b786e69e4f499fc2635b33878185,-0x1e781f31dcd102b0ced0addfadd61a6722b2f086c188529c84e,0x1cc45cbdfef8a62a769abec49cad2e584b8df003f6445cbd2d,-0x14841f953669411501ff35a93294bf61c34e9274ee582f950,0xaa24e2dad7738d4e68ca56287c6a87861c9c63eb4e76b76,-0x3cf9d8596491afa3e688da7bf5a260cc7edd5b90090f14,0xe24b9ee4e41a968db88468285cc6b71131084dbc5026,-0x1f09a0b734e3a7747d688dddea88e50d24d322e4170,0x2362935f639909db6ed1545a13b7f9d7ddfc8eda7,-0x112c8c29917d8899b1f8217101135ac1f8e4daa,0x2828231a0a6c527a327a65db36de2608d01f,-0xcfd553c6bf34848c0000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 22 80 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 80 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 52 indices rho q22 m22 22 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 52 indices rho q22 m22 22 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r23 : List ℤ := raw_ints% [0xda44cb48d9b6833a6efb0f7976834601a505a4a685ce00000,0x125a765df059834f96bf9e86a238069141282f26f8f8d60000,0xbac37f510ccab2f27840367c9b42c6373e242b71902010000,0x4ab1997fb32d41b7943ae429df3d7a50ffe2e53700e702800,0x1513fd63d43e369e4e80050b179db49a622bfb24753e4fa00,0x476b3012be767267a4edc7745f5504d32bd4267afaf19280,0xbc8a3e661475fe8b37bd188fe46e079f352cfa32a148960,0x18d635f3adfbf5254ab19a7b1a08055b861353133f8a190,0x2a7bd1352f5bf6422880b290fc41f25eb38b0490ac29d0,0x3b9d90ca686d3dc63327da037d81c539c1f75dae0f620,0x451683511fd341e9de1a02c71c49fc59a7b15a2501e6,0x4256cee752ec41d788aaaf3457eab2904bd267b1a2d,0x34c9f7d94d9a5e4237b8d7f4dab826ebb5106bc81a,0x22b60b1a92641e6aba268722cc910e333718505f8,0x12bdf395dfd147e55c2e0378033aa62ad092aa1c,0x8393906fabbf045835b51f5bc6d5c2ce7f4a3e,0x2e2c5553c0b365df5afcf850a5447fda22084,0xca6bdcc3e26c86c437b54bf6bfd396fffc4,0x29ba30d00e00ccacf547c5866ad11eae3e,0x6165d3df3574085f5a43aab4ce2c8f4d,0x8f72d88eaf1caebabe9a68d7502ff2,0x64437ce80f9625b1fc917e8dd45c]
def m23 : List ℤ := raw_ints% [0x0,0xa79e52333b4142f3067ffc8813dced3d47589a7e87781cc273500,-0x117533e5de1832d96d8e0b7cd6c77463bfbec64c0c027471854c0c0,0xe0cc08195daa09147cc3bf9d08a0afd77f46635de4b03f19f6aa280,-0x745d68ee136683fc81cc5ee6d962eae67ae5083e3e71e85c9aafe470,0x2b8930c3977bb3c903b97bb56870327f7dee2b4d96bdba3e92f77f120,-0xc8aa960fd652d186410f43d48781746f6127c20249b9e87865fbd12b0,0x2e4dbc649095923f0f3230c1e7ed5f554b93106d8f044d80049d61ec00,-0x8ca585d0498db88d34f880e25e96393fe80e964da172a5cdd87eee674c,0x166419cdc1234d9133da9145b936f3e08b1afe4e6ef993ba0459717fb88,-0x308261f0f7cffa0a8a758d3e15b41940a716a9139626c12af443bf30ffc,0x5a5840069a2b08390505cf6e70bbe2528d868836ea0dc03942ea267bc20,-0x91d59aef6394d83f15d5e36463055208438561c0901af51952a665ad1b8,0xcd513b807b35546eb2022ecefdb524b7d4f41e003598611f02cfc24b6b0,-0xfd539468e41d99cd41dbc5e6b5f9a4a712da161cb9849b8652320577818,0x112e6f62877f0e4ed94a906006674bd25b88b42412f0ca73b29b8c68c060,-0x1070b1569163615cf0175be6b69411c1069a95d1b14f2dcd957062c2785f,0xde4e2ced6f81f5257bf04ba8a05d9e183cc4e8106898a39209b3242caca,-0xa614dc9fa2e8576977fc0d324f093b1a933d8c845e60e95c6389817f1ab,0x6db258b4c949704a69aaaa9169b47dced905e8548e9db44904a5484b0a8,-0x4004e602c628fc89b669bcd8dd9bde1037c8cd8a63a619ac85fd01c59de,0x20f81b90c9810ef1b7bfad15d4b34e5b26bb85d8abc9f0fbf0256d29fac,-0xef3d8be38f7081475e8ef26983937a4d34452c3b8b1122b7bce16bcad6,0x5f4a64be836b2b7857cc2ca7fa252dda0d26bc24aab5ce22d4b7f61df8,-0x2136dcf4226e9d35abd06535643dc3339c06fa30ffce82c87ca770be79,0xa160ebb292486d8acb58ae0edf9fabce68af1adcbb37765b7005c6d2e,-0x2a7669b3c7d824b6e5c7147ff06a0a8575acaeb93d9ed7c5dbdad656d,0x99e1842ecb0aa4bf31896d0aea226b87907a7b7e7b7c8af115c890b0,-0x1dc3d202f19d6f769044a2eddca90a0d31bb2f408e3086a6cf7554bc,0x4ded330f41ff39654e8747df4eb5fa3b5ad2a4eea23200f9e4274f8,-0xaaa22374bd6d8941e98b899468ba97a68cd65e28a22a33b72d9b2c,0x1343dc0196151bb3fce50f87ac644d95bafa61fdd4de0f8abc7450,-0x1c3d20c21588515070fb0904edbdb02760cf211e0f93305880291,0x20ea273b66acce29e83cd79f14945000b4ef78edaeb2679f0ba6,-0x1dc1c5027c766d87022859b08a1bd6ec2eaa8bafdeb74664885,0x143a7567bd9a30a3cb0a7f2ce89c2976f8f9cf6ee006d4d488,-0x9f0fb7816fdf0e7fece2d6f024da1131ef94dde9eebbc8de,0x35b8dfd33590909798721c4ca4fc431f5a6eb517d5786cc,-0xba9707d9ddfde5dc499f33727015c7ed4f702fe871756,0x17c28598049874105813eec67237c22f5f265bb22cd8,-0x18eb678a62be2502ad2936fe1096a056f2e28e31ab,0xb029ab5eb662167415d5c52368e7f75d8d5689a,-0x1726b61baac1390168b8eadeddc94b9478787,0x6a241f6b6e42762200000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 22 82 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 82 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 52 indices rho q23 m23 23 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 52 indices rho q23 m23 23 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r24 : List ℤ := raw_ints% [-0x2385853dba79667dd26398b83b9626c7d8b63d2b7f05b800000,-0x2fc4e963a1672e9797a2f87d3ed90505956c2ddf696cb780000,-0x1e5df238c15af2d2d83e299bb99cf353d6423b34180ac560000,-0xc2387160cbef355110484d9546af0e037e338247b64d61a000,-0x36c7300563e6adb028a93f312944dfa8bb89dcb96552d5a000,-0xb97ef360e90043b79511b1bbc296d440ae88d6606c58b2800,-0x1e9633cf787feac4993a3f29d24029c65bd6f43825123a900,-0x406ca3aee59cb8fd70bc581e9d8611794ecbb3fb17ed4160,-0x6e1e4cc98d3ee73fc04833f9b8f007313fec933f80b96f0,-0x9a670572cd9ac9e9afbb92e3317e24c179436e28c4ee30,-0xb2c87ff2525d475214f4e67d9ce6f433fcc0fbda056f8,-0xab82eba83ab0b4d38d827eafc74746b75ac1270a2d76,-0x8857bb42dc820b1c3ce5f9c4a20f873f23e75cfcfdf,-0x598ddf63dec92deac8c3f3744af4a299bab60cf2ba,-0x304c0cd9e54b0edc774dcf898b88ffb7b29ab0dc4,-0x152a1285382fbe1fb9c74e5b8c652cd576edd7bc,-0x76aa9287f7aa9ece9081e90f133c9dc4f9ddfa,-0x2076e493de9f0aff247e467dc97ee2e14e5a4,-0x6ae55c44fcc9e29e429fa5f4a0311cd6bcc,-0xf90cc8f5b45cb0bb1d434ee0692379c8e,-0x16e0e58247e68c7ec6007a44a35781af,-0xff4730641ab073339f0e75c2c6e52]
def m24 : List ℤ := raw_ints% [0x0,-0x12fcef4fcdb6649587bc7f9b6a4006dff115098055589b420710100,0x1f70f60a024ee5b382156a15c0d80c010edad7771904730dc199d5c0,-0x1922ed2e1f725b9406b10e0ed35aa4a61a256d62f60db2b26df931c80,0xcec22b18c5dcccc12fcfcde34f37687295bc189cd72227a687cb0abb0,-0x4ccd6c06e093c62f5e7e93316f79bc8f466ad06c700ec0ed05194a0ea0,0x15f5d578d14793d21d0558568f2d9a2d632cbe526e8952062a364d280b0,-0x5072bce7c9cfff5ad44edd3db9bd9b644daa86ee1399e6b609c2bf83280,0xf261bda00ac21552e1af9deee5ebbe93e6378ddba95e26bce731d85061c,-0x2642d33d9e8bbb1084265a8de44941cae6cab02cfc1086c26b464d886ee8,0x522882389156af6a44812fda35bf06043bc090c067a31f99de9be72ecebc,-0x9798dfb178bcd21215704c789c3a54321b456c0de5c6b96766cc48496940,0xf255c4eae7159bdf1a8f0962778a8b714e9f415041e2d7b89301a7715038,-0x151b52892b2fe7217c94a6cd563cb572bed96b68c7921c5ffbc500e5e5090,0x19c3888674e4b61af6df748e107a28fd94d910ad85565aaba357ee28536b8,-0x1ba4d3b4cb8b522348fa104d7f0d71382e9bc81cd53965d15e148e0e54440,0x1a2361cdee43c252332329b9b92b77da2e0789675e13d5dbddd77f66b6fe3,-0x15d077e406b96b43885be843d2cca56f08d30665ecee7ef5a62e9b876c442,0x10150e5ec01aec9233f8559756029e423854a09920d05aa8664b259e75adb,-0xa795cac15babdabcac9b32929e065a309d161a841e522e297d82cbadfe50,0x605b36520294b3f1033bbe055adb83fb02a35d93c27f718b36da603362de,-0x30d7d74fd9027b7ea36749d5981f942dc6cf5a7c8b5e9966e8d27e835604,0x15c8204484e0d60228ebc7117e462f85f66199c5845c65202994c5470c1e,-0x88570ce72ca3b0abca9b65d34a7a51d2ca6ed5d0c562bb0687402c622d0,0x2e9e43d34283c86e6e415054846043f506eea774a6c893bfadd1fb9dc1d,-0xdde3c73e1359e376ad66a3a3d9e4c54f7fe78c890b1449284d0d65c66e,0x391b98036397af5dfadf212a3abc6ebfd6a3f0961b064b7d4c4675b555,-0xca159238647d6cd29846a3258b62efef8a603cfe7afb8a06d6de58b60,0x2618a85e267ea97614127197556178e57cf04865b1c5f7d08fe52165c,-0x60ff8ef2a9d97a39a0fcd2a607f967d69dcf55a902d684376d37e208,0xce0f563fb088500e220292c19456aa23ce9f8466529a358aef2d79c,-0x1682678f84469e3819d5b7861844b6e3690fc28dfd161f55fdf92e0,0x1fd2eb79f6b22081aa8575e4b6ad7ca021d0c4c9fe71b7be4890dd,-0x23a6b4b5e75e016ff0d7db5099f898b035c57d86c0b2ff987879e,0x1eda49c1519217552b21ebc0eb2ef15893359a839d234769b405,-0x13fbcf77481d2aafd1e9ae472009452299add8218a184142690,0x94ee02be47d262404fe11da289aa2d64822cedba9b1a8817e,-0x2f623cc5e8354108033bc8008aff15bd64a718e8a4811084,0x99f4c734e328bbfd660862dcb328e4932900a50e7db97e,-0x1231aa68728c30d7bb74f232df94d5034ada66f4cdd90,0x118c9626ba5b25a30d41e9325d3b1f23506b7ad2667,-0x70e9fafdf3bbe107478a8857ba694a47b5e9960a,0xd57f086b38e60fae71417c3e8666c26f142af,-0x3631cc9875975403000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 22 84 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 84 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 52 indices rho q24 m24 24 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 52 indices rho q24 m24 24 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r25 : List ℤ := raw_ints% [0x5a70ba75b58d2ed42bd2ada706d0695fd9c454b418e8e2400000,0x7993083769f83a9b9979a91fe6c79bc9afd1b3681f4d2d540000,0x4d405b85dc0168cfb491aca4704f403ee94d121d54a7d0720000,0x1edd9ee1142e1f27ce95d173b13e0fd059bff3f3efbaf304b000,0x8b37475ec2734b685715ae5cbf3a87ff6224337288fa6fa7c00,0x1d72c6a3a7588ea3c72aed164f2902a5a45f433a32b3c2c0f00,0x4da5b0a7154bfafc457c6c6a0cf94542d1832cb5ad51cf4a40,0xa371c3d140358c43c9933fb9b75b39649f71b442169ab59a0,0x1172e3e889338aa312585f4a3d097d5e9f326474ef8c91260,0x1872acad8b8919d51dc2ddacd866e0c24a62cbb2ca80dd10,0x1c493b8aacc9c24f0e11afa1f39ec0dfcecebf574823044,0x1b1cc9de66efacdf899ccf12de5cbbe212f72e9c0509da,0x15887c6edd2cf3eaf8f41d4ce8158a0c56df728d05004,0xe2129bcc598542004382771ad07772f01fc70cc6437,0x79ca53a2260fce28c786353e5635ae5a0d26910fe8,0x354ea620c2ddbb964fce62fbcbefc2e6230351e50,0x12a8172678585d4a607d361fe863979b9614d528,0x518ce9e40f594e0c272f33896d8b73809131f2,0x10c1cbc4f43dec8741fbca1a40e95155a6294,0x26f9cdcb7ed3493f5d420eabb4a462e894e,0x392e8406116b84a70a8590c1ab66b7f74,0x27cbd5caa805bf3ab1d858ee74be2af]
def m25 : List ℤ := raw_ints% [0x0,0x226a71c0a4da964f0605a749b0940c75e4f621389ab09967accd1d00,-0x38a2abe68bc45105d7edbd7d85c1059760ba829f13081088eee6d36c0,0x2cfcdde2849b617929b47bd94aa664cce4569d58babf30607a51073680,-0x16f92484b6e80685ce86f1e56c6f142f81cb824defaf800dead26a9dbf0,0x87965a87a6388208164a7835f7a67efb011a3fb070553e1a6e896447a20,-0x267cc2ba215ab94fb4249ec96b8e08a43b8d9927ef47555619ab4d883c30,0x8beca77fa752a73c376f20b08ccf93be2c01e0606618cd0b518d0e3d6c00,-0x1a23db7977cf8d1022db0bb7341357deae2591df302b892727b8efdfe5a2c,0x417991aaaf56e929f73979c427645118351b8954bf562df0b7b8110278ac8,-0x8b6080ec048de7a32ff3cbb9a8835ad0afc04bbf3ac1e0fae5f98f50255dc,0xfed7940bbd4a350241e6b6339d94c58327649b286ca9c0e744fd59f2f0620,-0x1937f746fadd1eac521e5a7010e43b23a34b89ff6ebbe5aa6a0d045c887dd8,0x22cac736d16c8c0c1ae646ca0e0b75b0f518bccab9172d402e040d7ebf6f70,-0x2a05a7f2c7ead89f31d4dc3661ac04da545a8cadcc2f392481cddcab185a78,0x2c96d350955c4e2381442f350b6f875f3017b742c8026ed7bba45e1b296be0,-0x29ab0bb06d641e6c4781d4fd5f7983356b8c2ef18357b4bf6c750e620ac837,0x2258a6bb6a56c2b3250b849771b99002dbf026ce11feb8a4f1b0d897b63bda,-0x18fda992374b407c77c42f421a7eb13f4b8efcdbfb314d5160ddfa0886f3c3,0x100d1595bbb01a3dba5e9380462c57fc903c6f51850a881f091fee271ee3a8,-0x917f06006d0a721b22cd77a883e319e7ff5bc36eef148ab49f6d16e4c6e06,0x489a15e32393d4e027f307f851cb103134d3657ab078e726140b8c79d6a1c,-0x1fd6cf3cd5243a3c36963d23ebccc1b7d4926a933694c652a3fc15ce5674e,0xc3c21f4141151c67f3e884d2c6d91a67fc753c598240c7f7c0882813cdd8,-0x41aa3c880a6197b0c1b493e380f7789b38dd5051291da63b87e754445b29,0x132307ecf34348067ba1a2fbb3a9c3fb6b42a902475865055e0741e9906e,-0x4d14c8f429e721237f3bac5ccca1733f38cc64482248f3648c7c2352d0d,0x10a567c852fdb45295266e15f3777046e55642ba407cd1f9aab778b1130,-0x30ee71307747440f0bd540c29d25258855aa8350ff685316dd12b514ac,0x792697f8712c0c055785aaca00b85919a16c46b87990e01ccb3e93718,-0xf9a86ebd607ef05d41bf154883e044dc47733d64e0f30a6fd184097c,0x1a61a388950b8e6efe1bc289c48018a06db26d6dfbbc2b0a6bf59510,-0x23f774aa8bc76bde15fc2d8ef3c460f828c06e6d933048f47e2f449,0x26b6e8d0bb47359741aeca3cf870fe49330b45f2987b83832d48b6,-0x200f724f2fa32dc9581f770bdb4ff2e9a747c0d0c57ecdf507b5d,0x13c750db7fddc0bbff2fbe527beb835dee2b3ba9a25cc8075408,-0x8ba54da0e997a3af5f7771b68270e1a902045906be8e14e7a6,0x29d60e56e0eb6552d0a7c4413e36491c5a59114ba3f4fc67c,-0x7f1bc9e1e1afa3b6be8266a355027fc1e7713ddb7a4c42e,0xdef7ec0984c6284885e5d8888d4e4f4776d5a1bc07fb8,-0xc5bba5ac565104e0de9d0cee8879dec2f12f836ca0b,0x485bcf1070a01723fa88e8c37c60e85e964cbb1fa,-0x7b04b2f30c2dc7f484e8169df9aad68ba50b97,0x1baa45ccf597b5fc8000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 22 86 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 86 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 52 indices rho q25 m25 25 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 52 indices rho q25 m25 25 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x27cbd5caa805bf3ab1d858ee74be2af,-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r26 : List ℤ := raw_ints% [-0xe195cfd1b8b609bf5f7de7b98ce5983341a8f9b937bfbe9e00000,-0x12f20b423ddf3344a2883d146dc73c5eacb56d5daad4a66f460000,-0xc0895b11469b293d9c07a3d3764d30aa68418d86f280129af0000,-0x4ce4e2b896a715921a157992fdf389d6facd24b359dcdeb70e800,-0x15aa87967c38b710f93515fa769923206caa7da9d2fcc2c829200,-0x494aa08ea5ece6b91391bf0855f2e53a640a4f659f60cd49e080,-0xc12506f26984df2d25add2cec1bd8bbfd3339a3de82f659d2e0,-0x1965303e8b947095eca0ab6a9842faa18ebdd849a7c679eb3f0,-0x2b59be8ca1e98a61739fcda404ab77987278524f113389a980,-0x3cb2ccc09cb472e0cfce4b0de8b5ae7648bb0f1f4d09223a0,-0x462d219df6721d20d5b26744a0c97aeca80d8fdfcaeb0d26,-0x43362edbad6422ac316429021937035981114c29e56172b,-0x3555ce629116623fd6abb910ed11a1bac408e383a25f21,-0x22f711504a2c9aa9a7c9d49e55f2467c008bef465b0f9,-0x12d1567d9ba96012ab2cf25592984ae7270773f75810,-0x83a41dea3a598fb6407c70e5fd2af4c30725b156fe,-0x2e04a26189a41c2c994c48c12c67ce1a1d55b41ee,-0xc8e506cc19182f3df071d8a41f87efdd13df5f2,-0x2938f6ae233d16f6e289b9eea8f53d9fa95492,-0x5fbc41c9c198f726c1bc8523d2b7879a4617,-0x8c3867e697603a3b2bfc21af0a511276c9,-0x6168cdf1fb59e5f463964a170339e4c5]
def m26 : List ℤ := raw_ints% [0x0,-0x3e60ee2d2acc306f3aea3f35900c5695aefe1c369860160be933c4900,0x660937fd9299200f70a306922cd25dd7ed7a4de8f0729df831025f33c0,-0x508b8e2041bdfea9500c76208563047577f8ea97d7d8f7c1edbe69fc080,0x28dcf947cfa9c54d9d601e677478e92e168b5b311dc4774eefd114cafd30,-0xef8990d40a95ef9216f14dfc7401a9e019dccba72ed54acb951fd17e83a0,0x43834899c911ef5cd65dc9ccec2187ad482ca03bfb92d0844c9d2eb839e30,-0xf3a24271da59f5e53fd3b8ac3d615d80096b8de042c7dd2c38b1e48e73e80,0x2d299d329de8ab67e8c97d7b59b7d820ae011e2dc51088380df4161bc5837c,-0x7034b8bd518e3d3649c61a85e7e20ff0178b9ffb92f093c57dc8964f2e7928,0xecd3c7a93c5caf5202b3d2cb3314012575e61a0a9235322f97ed132eb3e39c,-0x1ad2b6e4806021adc01e492535878b7cbe4143a0b554161ec658a6fb469a240,0x2a129a03785147cc77f5c92dc4c148e9750a17efbd7d60e06e496794aa66058,-0x397941a12c63b775e30b800d0306979eb3284c71e282864bb9def24e0143250,0x44b2cdbae79a1212a06f8db44888c6e0c537c8c309c913751ba1a03bc44b018,-0x48197d02c8c4f062a18e8baad48ef2460ad5d1fa71b0c088fc2db4c2a35a0c0,0x4299953cdc28c1c332f2671fc43e2decf3fd78f02dece856d4c639dccc168db,-0x363a6891caf7c473b761ad29273628857e85b9fe3a616c037ec758c8fc30d12,0x26f2aecf84e016a0cea35e793977f7742db391142f5eca175a5acd8b52bc9b3,-0x18ac486e43a75fe9349a76410b5f4e58302bce5c88fdb6eb02b19f746675a10,0xdc654541a545710342bc006a27cebd9761f67ca8127e43db5d2450a8dd8b06,-0x6c45d4309731f1ca384b763322ca3cd8656b548184d7a748f2c9b6ff892fb4,0x2eb29f676204252f97d2beca4431284b1157c0d6efc16e5e3d106f239e7556,-0x11a0b2401e7ff1b77a87f6f7ac2c0a14d6bfa53563cb0caec24c51bc0cb3f0,0x5cd18654abe162c5999c0aa5d7f050f86b028f9069400de56af25b52332ed,-0x1a803104153ead1d1754ed9fc22e27a6f46703961057d4585e13a94ae672e,0x6868a7c660691e2c1498c8a68a1637cd161706c2925c8e2aae6144b27af5,-0x160410be11dceb4bfa3875fd56c78dc4bfdd0eb60db69e87f69d3b659260,0x3f10991893d95003142ecbf471846002637646304e70092c84641d3d34c,-0x97d2bb4220e63eae1f5bee58abaf9376ad80cc229b02e2d1f329eb5ba8,0x12f72923ac8bb0a1892eaca506e25dd6f92f5fd3b5c174b6dad410666c,-0x1f032ad3ba262d622f53c8ac58c97b0bad0b720c5af2222639e20d720,0x28c2d059509431ce5075edf26ac084835ce804c045d83b7501c6fbf5,-0x2a2522c1ef446f0ba5e343d82a3c327be17412c9f105f0aa9796f6e,0x2162f6016e91e5c561b044d551184ce4a036e94e9c9f1ad0a8b39d,-0x139c35c7b993aa83f9cde5b30ad6bc50a33c1a7854197fb879bd0,0x831e7c47468401efe4f9647a25fab84df1325eee242343df946,-0x24f92a438b86030f30f5be79fea74d540ec3c30ad640fe4074,0x6900650f4a6cf4932635f2c9643ab40ca894a4490447ea16,-0xaad1367570370d850a12d920b594cefb6904c875034ab0,0x8b3d119845baf097c9e7f3e2bee750a58021e13e2fa7,-0x2e5c117374f19a3c0df8878ee6034c56c5d779386a,0x46dd90b33258f23b9eba660fe14ef7b6016dc3f,-0xe1e932e85fa60bcc0000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 22 88 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 88 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 52 indices rho q26 m26 26 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 52 indices rho q26 m26 26 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x6168cdf1fb59e5f463964a170339e4c5,0x27cbd5caa805bf3ab1d858ee74be2af,-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r27 : List ℤ := raw_ints% [0x2282a718deda6288f37ab2a6356d9e1098f7f4782f0de96f4a00000,0x2e5b4205244b3a090107bd18503b0141c32cd1b238c7ac863620000,0x1d6ecf4ae16e79b5df56a8855dc6829d31de79e7b5bf816e41b0000,0xbbff9ad1a47cd7a30a02466ad090e8591add7703481850d49ef800,0x34f2c24f815ab5aa41dc04078212fe3367b196a41380b31c086e00,0xb306fa46ae922713845243f5c1e6664c60969a79da6f4f6d0c780,0x1d78cda92e2731d00cd91d5b89e119dec5379dd2c5966f7d4bc20,0x3df796e27d06ccbac5de1fe5dea5917a67033446b63c414bfd30,0x69b7d1fe19781e39766e4e7129f1f9b4cf26bf8c7b413824670,0x93ee433fd2b9d1a6ed88076448c4a6225a5b12037d45b22880,0xaae9e7e8fa52e88b3c5fda67302c0ccd7f2e55800c3727d32,0xa392e7ab0a3d5cf99ea41b6196a54c1af3a5d8b85a27bbdf,0x81b349cb7ee3e815739e8a21f1b6cffe12983d01c0f9bde,0x54f4b10d56add7a27434e87da62895eeaf0d732e32157e,0x2dae17fb759401b23773ba9061e6317aea19c767a5f54,0x13f3dd172359360ed2574bdc4bb7749a502aaa656852,0x6f7a58632b684b89e1195e2ae892deca7da715c22c,0x1e6182bf6e5a128b407d78539e876f3a4210ea3b0,0x639e023ad6fc695ed8998060c048689045924ba,0xe707f3570a615e358f30f39f45e649c951f07,0x151df06b8b756364c68e6f63026636655026,0xea537851f3bb25c5e57ce1b8bcff83e6a]
def m27 : List ℤ := raw_ints% [0x0,0x710fafb1dd9217c99ac8929115165cef4d2c9322f42e27f596add44500,-0xb7dcde3816eed138785eb25e9b6d309517341f3d483abe51d8d44c8dcc0,0x9041a27a39285f7e3f1220491281ab7d2256355a43b4192fa9fc9de26a80,-0x48b8fd58b2255f4b80f79289e3e0a53267a83e2812a3d607f95bf4adfaf70,0x1a77a672797055721cb1c0836b8515c6f2a0cd0c887efb8144a43b24de8b20,-0x7688266b5405e99aa69275e2690c98916fd863eaa8cc83bae0b13bbbf9e1b0,0x1a8a86227bf0246fbc2b5a640a1c3d7b9d717f850a90aebade70f998cda4c00,-0x4e1fc1eb4094b6e5d90594fa9c88497c18be254872c6ddd85312cfb0f90540c,0xc08f9e70f7d1d9168d28071d4a3575d59481c2c98be1ef778cfd41e87fd5408,-0x1930d1b9faedd7be1a571932050afdbe404290aad1015857e6a2545f232c66bc,0x2d4051cf0b598b512b95d71539961e4ab61d13b8f3a97b5da58a317a8ce2c820,-0x46538520e084df7b7232a4c53a6bdc83265e9a076419ed4514b8087924e408f8,0x5f243314468f748e33d12bd7bd0f96f8b3264dad1ec6cfe62bfdb31cc80c9a30,-0x70907c43621e7225f043bfd2ba81745639251401d7f2aeec0074849c7b7c19d8,0x74dde64182213897c91b4222ca6b0e826d91a31a1ba4c18c3e9acd10876ca360,-0x6ab99ec64d7441aa50e93fed7679f91f8b98f03b69d22fd088ddf63688b3d6cf,0x55da7d42b34e58d06f94a554be45718ca4c8495767704551cccdf3ba5c56056a,-0x3cdff6e3d42658a75fcc55bc7b3c841e22fcffb5cf542995d78d92e107202d9b,0x260a55d67396d22cb356da1a6715e41b97ae34dbfa6b37a22d148bab17c4b8a8,-0x14ee5f7181ce09c7c8219dfb27be1e7b0fb2b2bcfd4218606bcba96e7acf74ee,0xa1fe22e8bac84b0e8a4a8bce7f9bd4b5d6b9523e8cb11f362c299e24334bf0c,-0x44b800a29554c87f2580d469af1ccd76d876b64cb74284d6a49c559894c9806,0x197be79a604325079d27dac1ec26b2c8384398578ec2842ead92ed2010d50b8,-0x83a74a8458a984f5e2e2f46536f4e551b236390e3b082adc06b2d61f496fd9,0x24d376ac768da4e8308c2b9baf1ec69d751cb3bf570a4a475bfe816517b0ae,-0x8deab5a7c582e894b5c6ed0e0e0bc4fe1b468dedf2becf929a20affe8342d,0x1d37d8b95d4ca0c37039c478430b0552b2909446c044a57c8efc26b8669b0,-0x518e1147ad7e3108f71f4ae9aaf817292212b225450b6854cf79d8fea91c,0xbee1f8ddfebd41b92cb18ced209693df6cfae24e31906775b3c8fdd8438,-0x171f9b93ca46d27e09d73b353570efbc160be9d23252d0b94f6d23d894c,0x24900adc4144c8d7126bfcf0cdefcf42605894658095a11ae3b667abd0,-0x2e5167953dfed8792bb469a90353ccd3b60f4b8076ad50c187620a0c1,0x2dfd2b578ef93deb9f8e740e993ad533e6b4a24aebb64240ffb59c46,-0x22d6be62a4eed01f05103bbf09c9dd41930d8bfde3dcb55ef1268f5,0x1379d04a5e98c199572a60289e838bde1f909d396a4b88660eb988,-0x7b45548b3412fa99b9c2959b950108e00469fd4fc7bcf2f3302e,0x20b45b5651778e51f635ca998c549bd85c0177b140a25e4c6ac,-0x56c8822f64d5a7e0c8db879311e08e5762118dc4ce6d9b646,0x82e322f7c721d1526c2e7007f91379d9fd7219a8832a598,-0x620a9c7afe255dee9865df95f6ebd7a4867e8ff9cbdeb,0x1db2223edf7b926f8e3c765c6e7257a80c7f09b455a,-0x28cfd7bfc5a1dea83dec946fb903c25779c61ea7,0x73461ff1f78b31e200000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 22 90 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 90 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 52 indices rho q27 m27 27 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 52 indices rho q27 m27 27 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0xea537851f3bb25c5e57ce1b8bcff83e6a,-0x6168cdf1fb59e5f463964a170339e4c5,0x27cbd5caa805bf3ab1d858ee74be2af,-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r28 : List ℤ := raw_ints% [-0x53047605d4fa3ed2b127b06b673a07489dedd8f1340f048305400000,-0x6f7a21bb32253c94ad9166480f153239366aafa7b4746f56bca40000,-0x46c114596dec8ba446abd015d84252534a104b9de18311acd6c00000,-0x1c3c291f259e93a13afc0d13fef852e34d44bc12837a4bffe245f000,-0x7f2eacd0ddb2c5c146afdaf8047d8618e34396678f074f3a19df400,-0x1add5eda1286cf2d18ad8d1634e2867163fd2c5ecbe12f53e0e5500,-0x46ba206e1b2b6a986755f83c7c4f78c0411b4b40b03fb269788dc0,-0x94a252664d21cf4d8c04262b611c29909f03ece98ed0f469fda00,-0xfd6fb6a279e890c88fb9f7a5d70a348c24ad638a589892fb7b90,-0x1626c9f44b642fdf626b8a15a9cb4ba909b675e9a039f1f21d90,-0x1993b10a6bbd3f352555caafd0cd15f863c20ffe0f2fdbaf5e4,-0x1876411b0b4410f7fbbb268f7febd092ec6575c4df1494e1b8,-0x1361d1839ed81fe9d8b466be17f5f8cd8fa1cd969a385f493,-0xcaf83dab2594d25f395a2acf2fa2369636ae7b55301ba00,-0x6d0ae38a4e68682271f68d15a13cdbe9d056096504cafc,-0x2f95c4f02e9c0a6cbd3826a32fc24546b297b9a024430,-0x10999c2e630cda8542a087f77b9f325e2613865defc2,-0x484e54b69e28c397480e4640d65ce033dc6ff32650,-0xeccf9025096f33223170898640c550ced5552628,-0x2248342ff8a7ef5da8018d133129a1f6fb0b2d8,-0x32110819fce8dd5d735738434fca965821753,-0x22abad91932852c136f294ac8e16d45ea60]
def m28 : List ℤ := raw_ints% [0x0,-0xccec6e726198cb1d688b89a6f6388871bbe0caaf5a93a86d211b10bd100,0x14b5d9a0f84b517a8338c42996389bb6a3d69c02b76a5b8f45900cac101c0,-0x10273716d229cce1cac770492c8018f67dcae416599c1d19caccac26e98480,0x817cdf39751301e11160f07797d68139c807f4b2a4ef8b06a67f31c811fab0,-0x2ed2de2f70eeb399ed4b858834461f0e0fdf1cf28c64cbb0708599e6aabe0a0,0xd048bd1a6923c2b399d7a1f787f3324f5d261a21521c92a63ef539ba6e8b7b0,-0x2e4f317920d291d749defca8a29644e6fea21e83280da65fc1e480cd47c34a80,0x874e2aa9e8c651b3092ca734e709e370229ee79d3e4dbc7b8191eed4cce4dbdc,-0x14aeb048eaf965aeb1581290b82724b821d06bc157f1f320a659b77332eb45568,0x2af02d43505cfd8e57dbb4f6460777f3cfa8896ab7f37ecfa774cfa25f078337c,-0x4c78cf44d213b7ede04095535896749e09addb22baec04239e10c27a1b34b5b40,0x75c6cc1b134d5f43a617fc0ca2b5d95ad311df916873d5041aadf1d383d886778,-0x9dd26504002d7b6b20f8ca51f3dbcaf3aa6533416d6c8b2f4473b26eaa4018e10,0xb8da09d5462ffda527da58f6b038a0852f409d5ec249979890c727629d8d77678,-0xbde236266276962aa666069a020747221cb1bd6de25e6cc7743e8e340a2da2140,0xab75e8eae2fe11590eabb2307ed1a5abe28560f3b0b60a15effe9e22394a2f993,-0x8849f1c11019500ec879d85a45ce6613962c522a85ac3029e7d68ad5916acbc62,0x5f6a7edf4b84d44c057209ea0568293c770b107f0eec7b9f84fb6c4fff359fc4b,-0x3ad2f1dd4edf1afcabb02f90efdd1828db5130e12eb26d72a47531070584c91d0,0x1fe75930c8df3962f59bc78c8ad01c39dcf83d5104c2a8cccc234b39c46f54bee,-0xf323aef51fec4415e5a71a77e8216f3ec4cacdb08f14113078fb08d012531de4,0x6574ad3762ea10c9ce99c7635de44c28a57756df068d1b9088db1e9e2cfc1ece,-0x24f70e83135eb399221ebe2b49aebf24f9edfc2c48aa68691ed1fa8d7be39610,0xbb5f1b5b79628b4e03ef8dd58930eb25d8c150abead5e9860e3613c2f0dccbd,-0x33596ec31ab8f3ccff6242123bffaf155587752a93fe9ca08afecacde9ef8ee,0xc18ee860558f22883a1064f835705520efe1f96fb36cd16bf1c30b8256f015,-0x26e856a44d59eadf1da884d9b8e8d2ab57a34d5eda157237e74769108c9d60,0x69d0957368239a1421bbc4aa32136f6c8949d66a85fe3f95aa817ab0ea0bc,-0xf0c1d0534e85e477d814d9a65adf602dee27cece1f082a5930721a045c48,0x1c4755a85b733d944db3f35e98b28430d687ae44cdbc466d34d5a777cebc,-0x2b3a7cdcee4a035f84f90497e765f172040a678fca7fc23e2744f79c560,0x34c4c8624985ab9372684847ee448771119a35286d26177a68b65890cd,-0x324c66c52e1393d0039ff85d52f85c14cf051834ca9006fc7093f43be,0x246ce9cb8f85f0e2e9f510ddfde07ff70b194ee633a195efa2f759f5,-0x135f8582d0c1e2a745ada3f68140216e42edd4763c105e26ed2a910,0x7408177220d3640bf862dddd9d13e14f3bd044d06451c6df0f0ce,-0x1cf3c14276fd1f184a023fd9c2e7c39133fe3894c2df317e62e4,0x47c2279cdf96bf6ae9e12490ad47a5784f91480110fb0a3bee,-0x644e45e78dafc53dbcbe3d138eb258ddb6486b44a67880d0,0x4507128958c9daca746ff05a6028d7091cf2262ab28d67,-0x1304815fd166387a2c42bb5d6fc1d63acc0f6c5d94ca,0x177f7088c281a0c46bc97721f317daa114b302ccf,-0x3aced55696c3adf3000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 22 92 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 92 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 52 indices rho q28 m28 28 1703103561833815225244160000 29=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 52 indices rho q28 m28 28 1703103561833815225244160000 29 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_28
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<29) : intPolyRF (mz e)=rfPoly (C (1703103561833815225244160000:ℚ))*rfX^29*(1-rfX)^22*momentRF (key size) (X^e) := by
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
#print axioms moment_source_28
end
end CatalanCore.Li2.NVMod.FamilySource.V8C30
