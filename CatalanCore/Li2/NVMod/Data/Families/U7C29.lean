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
namespace CatalanCore.Li2.NVMod.FamilySource.U7C29
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,7,29,size⟩
def bases : List ℕ := [1,2,3,4,5,6,7]
def indices : List ℕ := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def num : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def den : List ℤ := raw_ints% [0x5ab234187a6816eac200000,0x7c24ffd0a80ce20605a0000,0x5076c0b79fe12a4f5ed0000,0x20db3638dc2222836259800,0x97c8619265992231255e00,0x20f705ec10244131228b80,0x597e3b2b3c5ee68623420,0xc294701dd2f8584b30d0,0x15893a3c666e814e76e0,0x1f6b400b072791daa00,0x260b22bcfd622f3eaa,0x2665099f8b1aa1741,0x205804a79753e175,0x16b70b6d0123213,0xd3f13444b05e9,0x65e441ab78fa,0x27eefdd4b22,0xc8c86f506,0x315c52bc,0x9248c5,0x13319,0x197,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x5,-0x37,0x21,-0x3e9,0x8f,-0x861,0x2693f,-0x832a3,0xe28eb,-0x10d0971,0x37b7bb,-0x17e107,0x32584ca,-0x242f7713,0x1e0cd7d,-0xfa6b067,0x904903,-0x48b841,0x217963]
def rhoDenominators : List ℤ := raw_ints% [0x3a898f2c80,0x9e93cd0,0xb46d0,0xba78,0x3740,0x190,0x384,0xe,0x20,0x1e6,0x1c2,0x113,0x948,0x11e,0x5b,0xb6d,0xa280,0xdd0,0x10230,0x1e48,0x50c0,0x1a7f0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-8) 0:ℚ)/(rhoDenominators.getD (m-8) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 8 30
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
def r0 : List ℤ := raw_ints% [0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m0 : List ℤ := raw_ints% [0x0,0xb0fbbbb053fa622be048a616190c000,-0x163aedf8aeafa3acfe6e1734cf632e000,0x15af56ef383cca92b2ca27d68123768c00,-0xdad99b09495e059f2298ec4f02a13f8000,0x645499ca006de349bae5753b6024e71a700,-0x239ff76c41cc0f9e01caa395b373eafe0700,0xa31fed4c35de685ed7a381980f89b9083800,-0x26a8fbc26bdf14610e56fea429b29a8a58500,0x7bca1ddd53d5018332044352204fda2571640,-0x1539b4b588fb23f98fcffc9d403bed7bff8640,0x3272f4b46360ca4a54543b017b33abc7242d80,-0x68ca1e73c9b3455a8a40b2537b3bb61db68b80,0xbf84ad21f9beca722cd7776a1c8a378fb8ca20,-0x135a4f10e86f65173ef9b6ddc74a4d6311f2ca0,0x1bcbd9323dc4711142bf5d2309c199d03ec5cc0,-0x2395161d76ddf0b34e91a6022e90805ed62df00,0x28b20d1feb30169235bc3bfb0d8049af61b83d0,-0x29a7bd0a2e4785197f18b8c92f4c5d8b2ed6ed0,0x26335c257b34a2e4dbff34e1c6fc30ac87696a0,-0x1f66db4fe528957bc1ef6abba730ea03c7e4220,0x1722a2bb732dc4a9ed76be84ad08f3d21b46da8,-0xf443736e4c59ecdb141792de79e86c55cc5dc8,0x902f3287e05e1d3cb84dd3964114cf15f83830,-0x4bfdb881bada3238f62b0f372b0ebf273e97f0,0x23ab5fa483cb887cf7b31c4296c5e70b180058,-0xedcf085d0cf4eb29d28b4401f66787e0a8338,0x579c02185cd1bb46dc56be98f64d783fa2980,-0x1c648245cbd8c45205fa8851cb9f812aa2680,0x80b8141d9d19b59f1609d4b6fd248abf6210,-0x1fa62e2438c008487ce039e38eaf1be59450,0x6b0e18189483444ad870a922335273772a0,-0x133d85658d6ca4900307558b3f350f80a60,0x2e5fe2744b4e2010c206b7ec2b3a4e4fe0,-0x5c07d803a52c0671f64f8d879a6be6020,0x92f3acdeeaf732ac689c2b7d152644e0,-0xb725931840da7a0fa735b7e2f0c3a60,0xaae891fa0e3ea2a04cd31ce5f17788,-0x708aa976891b259da30771b0f4c28,0x2fcb8bf8352a40a9121c423c16b0,-0xb4794bf785e357130f319413f0,0x11d5bd8e1dce67e7d33bdd518,-0x5e40d964fa22c54a4b2378,-0x4263d0d2048b55d100,0x1efb6173132ff4d900,-0xb9e448b2731fbd160,0x36ac8dda21dc288e0,-0xc2658695cdb973c0,0x1eb1b6ef3b6e1fc0,-0x311c57e52be3660,0x256aeda26a94e0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 22 40 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 40 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 51 indices rho q0 m0 0 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 51 indices rho q0 m0 0 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x140c8442f9835d1ef8683ad080d65c000,0x27cca6ea9a6047260e2786d3cf960c1000,-0x2656c11bd8765fc9c3a22bb17c7229d2000,0x17e0027929fa31b2cf75aa470514fdc17400,-0xacd983ab35a78ad34f87ebfa62e23ca72800,0x3c8f4a9f85e87b74615ce4ab22689677c4400,-0x1118977e35f29bc68f38b9f0cb5c4c93fac000,0x3fed7b82001fc8f22c391d2f7881ecad328100,-0xc9c9dc8b343b71f6876ed3eb3c26241d785a00,0x2218996eaaea42e1126a1da4625e5647a3f2d00,-0x4fd50b0fbc1eefacd9cb7f0771376e9251a1800,0xa3497576bb987a9547f8a25f9b7d8e4a09e4a00,-0x125bf571056eb7ed4a1bb8691b6832c27ea6ec00,0x1d345315b6dd5dd27348b7e3778756ce5e555200,-0x29403222628c7f47808444c225fc14080dec4800,0x33e796d627564cd5e9292afd31bf6a118578f140,-0x3a51d883eede6b95064281c22c610062f0512880,0x3a9cd461d83ea4e6723158827363167841381c40,-0x34bebfa0a69561920f46e1961fa1e1f307c51e00,0x2a84a107a4b95a07d136f096ce0b99b567213680,-0x1eb27392692dcb87ea0118c09351eede8021cb00,0x13d5c4886fe0e8a64d05c4376d0c04b05e340080,-0xb748d9e6d3c1b4bf68fb6ab873b7fb0a1323a00,0x5e6d1901a6fdf038e14f5507f24494bb269ecc0,-0x2b487b25bb79635f748f00b90d69b2b49f19180,0x1197ec189d88035dcdd347048b56917187165c0,-0x650a27e4f39c9caf06d961abe63e9964138400,0x1fdc7be668ee3ceebe4bd69bfd9bd378dedd00,-0x8c55b8ac8956f1d454671f45a07ee250bee00,0x21778238ce9e75385fa53d71fc3b6de93e100,-0x6d95eb7d8d3a67785945cf31bbc6fbd0fc00,0x130608f380f4f975f15147ff125d5b559ac0,-0x2c2cd93a2f22e859efd609b413117c22b80,0x543493a6d69fdf12710b73e7092f5ac7c0,-0x80af67c7c0f490c27308b4d00b9928600,0x98d3f1f1a34663be5b78762b6079a680,-0x872a94e536877c6b0a6874f668a8300,0x53c7a12715c15afc41768dcc20e080,-0x2131407668778b1014687012b6200,0x7384f5a8c62323cb4c433e38e40,-0xa591d9e7af258cf726edeb080,0x307795979c01f7ca4ce2140]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 22 41 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 41 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 51 indices rho q1 m1 1 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 51 indices rho q1 m1 1 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x2456afb9643e18c8223cea99e98486c000,-0x474627d2fbe1e24edb679eb711b7f511000,0x43d21f3557d5d7c0135408d1037fce2d1000,-0x29b557e680f91548d86f7f7ee0d2596611400,0x12a1daff7f4a9bf0393d0b235065df69235400,-0x6716e4084179f04a4eab365692abfbfc816000,0x1cb70c8be389deb7adbf2dd140df13765a20000,-0x69e9aa1304c5e38f160547d7dfbfab11c881d00,0x149a74c35dfebe67011389cfc00fc1c06583ed00,-0x36e7cc10fd1825f7deb3e6f4fd45d5c12daeac00,0x7eabd5b263fd1e0437585c2b6bc4c588dc035400,-0xff31a3ee3fb677e63fe3a82b9aebbee567afae00,0x1c3fe30822d82da5fd4b094692e5e27ac9943de00,-0x2c3937bdbc9a03bae52f0e1d7db0646c75e139c00,0x3d71b6f80fc358f1c9c72f92a069520be9d648c00,-0x4c031050f587c0229f3bb8cc219dbdebdc9134840,0x53ec8a5549d7e196e7cd260f66cca045559727c40,-0x52d57f1d034cdb43a61c8987b19fa1c4de34bd700,0x492935d622bee6c5e59ae83cadd157ac41038c900,-0x39d83ea67d9df18ffb67aaacd0c8a75a287b14b80,0x28eebef7cc8e375135e83c8624e5132b916b64780,-0x19e72fea6d98ab28cc5d41a780d23acafc82ef300,0xea386d909835549ee8618c438ce27c4a3af39f00,-0x75f85d7f39ea7597771465d65cfb2ae18aae12c0,0x34d02786948c4b4b0b46bb563def956c9f647ac0,-0x14f15b1462a2e412350aab5fbbf85ecf4dbb5800,0x75316fe81475ea553ac5146808912ec5c883e00,-0x23f57034aa2d7fd72943b08b794ec689742db00,0x99e04875af5fe228ce710253d11c1e7e4a4300,-0x23971af0885a3561b5294f8e78ebea56db8200,0x70cdbfbb642b2815093cc7cedf2134a027a00,-0x12e962f926b46f3babaa663524c0481016dc0,0x2a4cc89ec7d8273d955835bfec4219bf71c0,-0x4d6cb88fe2c3093200bc3b5cd2cb4708700,0x7132edc01e1a59fba869eb90fa8f41c500,-0x800a3b3c1247891d0d0b5e73b2a35bf80,0x6b4264c3067f5fbd71673b840cdc2b80,-0x3e879a644e2427cd7ae688f300b9f00,0x1716e4423d6ac9a35bb5c099002b00,-0x49fdcf215431f507a61e339a7240,0x600c8eca2e9e467b0b27eb0240,-0x18e9a6d8ba480390e7bd7e00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 22 42 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 42 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 51 indices rho q2 m2 2 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 51 indices rho q2 m2 2 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x41dd1e8005b08ceabe0e6936f740343c000,0x7faccc6f7fab548c38bbc5c458af6ac9d000,-0x780a2f7b42fef64a2f556ac2413a9da3e1000,0x48ec17b0f7cc46cdcb57f7d2e470bba2c3c400,-0x202ba35604dfd78e4ceabd726ef585f030bd400,0xafb9e6b34c4dce1ced5f641c2753ca2956e4000,-0x304f2e8309e90561de454ea3f9a4ba8156ad8000,0xafce0329bdb978ab4e29e7aca779dfe2027e4900,-0x21bb42223a39af7aedef8aec2ba8405aa807dcd00,0x58a0f9674b401ad0508973eb6c3d1e210700c5400,-0xc987546ed89e4627d7357e8c425800b096c507400,0x18fff3396df71e41bfbf684809d85d157b31edd600,-0x2b9b0efc4962187fe89b3d63a1876ba7b2993efe00,0x4331e5caea8739c3e83bcaae9afb5b00eb33506c00,-0x5bdb3f438507782bbb9f067957d6e20d23e7a56c00,0x6fbf4161008f12dc4d12a63946f8f899765e1a6f40,-0x79438057b4608ec59416cec93ee33a4b9628749440,0x759190eb1fe80e23c744182fd9a093ac4674170900,-0x65efc00438522f9fe9aee8cb31f1c9d8357357f100,0x4f10e06a67c01ba6d96cd4eaf6a4cb90cab1791580,-0x36d8e57cd1a9eeb73edbedb72e26c30a50aa852f80,0x21ff81be35266a141c8b4c71991ec875a1571b3700,-0x12cdd9a8baf4405f0ebd650ea501e01e5f145cb700,0x942b4c24e78b8714faf2dabc7db7a6087de48efc0,-0x40ca9f87b3a33f6fd1659b11e057c15ee9f220ac0,0x1911407ce5830f8a44333be012148a02952732e00,-0x88affc5a39b9f5e544d5eb08bcd18c2a2c33ee00,0x28cf8c3e7d8e481fbd7e8e6942277860a2d0df00,-0xa9ab2b80465ccccf9dac1a7081fbc483b143300,0x260ef217eb5ad8749b4f4f63c9811aadda02a00,-0x74bfb1e1fd252fa937335dd43c5daa3e928a00,0x12e65c539b17aa5037822d095f2cbe94eb2ec0,-0x28b5953473de992b4bb3f961379b0e7eea9c0,0x4787497f9278e35829f7b510ff4debac4500,-0x6402788b2b1e1113f3c9d5fcc2d9ff84d00,0x6baf27c26a8b2411581403d8b162323980,-0x5562e38b2af729c6dd534103701773380,0x2ec84e3c70d8e2e46e97300a3b940300,-0x1015fe79a860fa3829624cd5b3b2300,0x2f6b4a3a95c9acfc0d77b891d6140,-0x37b5376edffe0323533e6cdc240,0xcccf3c5d75cd529661cd5000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 22 43 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 43 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 51 indices rho q3 m3 3 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 51 indices rho q3 m3 3 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x7760c7480a4fff69787a1eb3a0245eacc000,-0xe4c511fbffe1e3616a30451ecfbd6f1d09000,0xd494a7cb89754ede3a6279e317ab1584cfd000,-0x7f998c93fdbfbb7e36d6792d5db7fcaeea2f400,0x379b0b5d719ddec2bb9742953e9193fba7dd0400,-0x12bf24a36f51f6665527fb17b1f8c1fa8c992b000,0x5167b1bd16f4220632d3c6418a4417b0d59099000,-0x1245d6832dbd99763d0e9f00ce670fd6c3bf933500,0x3757a03e19c6be014b446d3f6ed5a409daf9767900,-0x8f680cfffd65879ab6527bce661131e230b6704000,0x14177f66fdd5936a49289bb7823126b654ca33f4800,-0x274c57306208e10094df9cfcbaa5f11a633421e4a00,0x4384fe64edd5f3e79652c3b91dddeaa3fd987a93a00,-0x66710c83c8e6d322b43e9c6d0c7ae88ed023cb38000,0x89d07d9b0a9de4af9ec384403681a91a264bc5f5800,-0xa4e89f0b993052cc4ea089a41fdb9cae5d89911ee40,0xafec315d61603849ec524d708f8ee8e8d00c4cfb340,-0xa7934c91e096285936ac994a69753e31355d03e0800,0x8ea8e2c467c93d87491ca5ed2d453f5852fb181a200,-0x6c925ddfe65c726c372b5529eb44e3b72f41b647680,0x49d8271d135d7d4a41fd00e39d00b23c1e193dfda80,-0x2cd80866fe3f118064364874418048f4b0011b3f000,0x18471a6b4b0491e34f9fcc06ef2fe51f096e65a3e00,-0xbb120d3a2c8c763aaeb0b8a9d73cc41a08b886f1c0,0x4fe8fb5f22cf3e0ed077a646cba9a58a3295eeeac0,-0x1e2aa3226c8c8a940aa87a0d9fad05b16a72be0000,0xa04b8af693dfbd92b4e7c9deee4087b9f785dac00,-0x2e9242e51134c2160fceffab4bb58a646f8837500,0xbc1ad1c8ed46fdf0153b56e2f6fbffab22ab7500,-0x28eaf658bc630c3f4498571e1ec7fc6fb4e7f000,0x7978f9766b62470c4d9bc50a04b365bafeac400,-0x12fc2cc67f8c478096166bd38a14ac814c091c0,0x275edf655a646e1692764de616715bae3a28c0,-0x4262720325c9e2ec0b6ce0ab4f00caa696800,0x58ba04992456c7712603bcacb9c799557a00,-0x5ae58876d7e6b67f0159bc969d2c8b58e80,0x442df5770e389c328c6c691b6259462a80,-0x23147d7bad641da3e134c2c8f54b83000,0xb38e30f225209533d655b704c623600,-0x1e6775d7c8b2bba75e065aac10a140,0x204d8de2acffdd6fa0e70c384840,-0x69323392ad57c0ab4f9638000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 22 44 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 44 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 51 indices rho q4 m4 4 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 51 indices rho q4 m4 4 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0xd85f693292b0feef2a5d57a59241eb991c000,0x19a05f7a016a149de46585ef2fac6751f505000,-0x178aa566adac8c04b41481cab0833b895f699000,0xdf7453a85717bf96cff59a8f9ff104e2a7f5e400,-0x60371cda49e95b704d32fbb2ad71a2800a3c7b400,0x200a8a4a290938d4ec9302887101fc6fdc24568000,-0x8964676584a15592bcf0d0d218dcfd351415346000,0x1e71a8a1ace45721f6bf8084377886317500066d100,-0x5afd465ae7b0537013eeeb4ac538ebcc8aa172cc500,0xe895e8a91c5e213ff525c1d49e1bcd3566672b6c400,-0x2021fa8348d53c29dd9c0e2f51576c56917537ce8c00,0x3df3306d14dfcec6e4d7406d2d29b29958f90081c600,-0x68dea9562c4c5cdaf5d4aacf7b6983c880f504e13600,0x9cb19b9ac67ced49975cb6bf7d04d9f40a709658dc00,-0xcf7f5e25aaac0f831fbe404878aec3cd1f105ce3b400,0xf4465b49b9fb3fad724af00fd2319d4b474270bfd940,-0x1003b2d4aa0dde843cd5c36bb2443277a471204abba40,0xefd90d13d1985fb1b2fa611b8fab5ff676b3f9079500,-0xc885bb97e7140a428312d18d0b9bba830f0e479ddf00,0x95c40ccc0bd6281d69d07675c1c68abdeae794683180,-0x63e3c7de8f5d417ff40e6cc5995b2043b5c862499580,0x3b6ffca1001a26a1b8dc4391836fcfe0ef05503c6300,-0x1f80662ab3dfcd5ef8cf27bd7f05e63ede03863d3100,0xed6544fa1f69bced98fc89210ac21e084182e0ab5c0,-0x63123c4ee324a24b585d8a0212829624bbc219bbac0,0x247ecbcb14f8badc97e292c955f60a262e9f316e600,-0xbcfc1b55305c8907a3cf50071896ebbd7e958ef200,0x356e0fc3e60b5acd6eabd1aae25293078ec85a5700,-0xd1a8511eaab0257f43e3a6819606f2f1a745e7700,0x2c396077d307c9d186808faa38f09ab9a8dae9200,-0x7f0a253753421cced6c7d5332f846c97b0632600,0x132a70b939682cb0be95150fdf4d77d78c9344c0,-0x2641b6d440e289a5060dac9a9c3371cdb79cfc0,0x3de226bc4543bc072aae3564bce8eaa42f6100,-0x4f08604f4e027afae9a241cf8c1bcab65a300,0x4cfe9c2e73d539d335623ffa6646f4af9580,-0x369897d3bdc611a1da9d720e32b1e0e5180,0x1a5c40fd6db1a8a284817e64fa4a5cbf00,-0x7d6c3cc6cdefee2dbc9647f1487d0500,0x138095730738407f7ffd3e122b19340,-0x12ba0aa5eb6e6a50806944f20ee40,0x36032dc76039aa31fd82540000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 22 45 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 45 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 51 indices rho q5 m5 5 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 51 indices rho q5 m5 5 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1839900,0x7d9f880,0x12119910,0x18863880,0x16005628,0xdd7e798,0x6515a51,0x2213f80,0x88c13c,0x1971f0,0x376a6,0x55c0,0x594,0x38,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x1882ceeaba9e0ce117cc92edc19177b0582c000,-0x2df142d1f00fe19eeddc9b703e27624cf7591000,0x29bc199604c9ad406d0672bd3a6575cbb093e5000,-0x187a06c5c443b8756ff981f68414e5f6e91c799400,0xa6a8849326e3efc5d959b3370ea57b41b06f062400,-0x36d5ec3f9ea9aff373fab2692b7b242aa67a97a3000,0xe83fb9f5b6cd88ff50a26a2e555f85711f4bbbbd000,-0x32d0890ec4ed517a34e850803728a20130f948067d00,0x95e851ad6616fc57d1d37dad73fb54a3a32dc87e6100,-0x17a18cf560fd22d35a7a8a360483b702fdf8da5572000,0x33857db8ef0f319379a34a200a6844e34faeaef805800,-0x61ee8e7536fe793e2f5e518905c5fe38c728ae0c89200,0xa36026903202eb1110def1d79a681b0152b502b45d200,-0xf07595d3ca80bf3c3aaf0863eeef7a29686c9d2975000,0x13980be5818cdf4cd61fe8c130f5b119df0cc17ef27800,-0x16b2d0f197ab2607bf9e248caa812adf4f0d6ff217a840,0x176a868dd6542053ea1b12e79a8e1c9f6ae16e525e9540,-0x158b2e0353cba2eb2972e26490849d6801c3d7cd3ab000,0x11b10431b4e39bfbc0239f4d701ff494756e9092626600,-0xcf83390fc048a0f8016f3cef95c2216293f92743b2080,0x87bf544b78fd1b13da2540086fc746270e5dbf3e2c880,-0x4f2826c47aa11b70c4e61e6ca0a7cc43626b547c2e400,0x29135e75d5b615604d73c35b0e98f7bfbcb1887d35600,-0x12ec61624091b5473a9a32e574a3073161371eb51d5c0,0x7b74bbfe67e76ebb4abaece113a7eab4e348ee5342c0,-0x2c61860419ad02d4f8e73bd1b5ce422e2c6c8489c000,0xdff9a0c10c41336c753c4e7da39ec80a7c2b2933400,-0x3d9eaf24b99f8c52a6749bf8645789eb26690b8c100,0xeae5db8082e50c0305df1721ca56f713c9e2eb7900,-0x300b1b3222e11e3d5bae74431883b54258272b1800,0x85876d46ce18e7c29c79b2cd70b350390d73a8400,-0x137121f5b0dbd8e88cebe23dccc77818ebcb643c0,0x25585ce5783813a65368c680999e8cb24966eac0,-0x39ef0e9de2efd2b622b6b7bcb14c048a9dfc000,0x46ab5476e66a75cb718ce23da5d72e7ebc7e00,-0x416fad3465af74dee8eaa50a2f5d7bfb93080,0x2bd6463d501186e124f6ffa86dccb651c080,-0x13d8d00105fbc89ac001bf511b4043c2400,0x57b5b002ffc90a2cbb06972b9eb031e00,-0xc8376cecbbce3dcf9b3f0287c7a8940,0xada7dff6aab04f4420237af4a2440,-0x1bb90588bd0e591d4ccc7e00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 22 46 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 46 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 51 indices rho q6 m6 6 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 51 indices rho q6 m6 6 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0x5ab234187a6816eac200000,-0x7c24ffd0a80ce20605a0000,-0x5076c0b79fe12a4f5ed0000,-0x20db3638dc2222836259800,-0x97c8619265992231255e00,-0x20f705ec10244131228b80,-0x597e3b2b3c5ee68623420,-0xc294701dd2f8584b30d0,-0x15893a3c666e7fcadde0,-0x1f6b400b0727143b180,-0x260b22bcfd501da59a,-0x2665099f89923dec1,-0x205804a781538b4d,-0x16b70b6c23a4a7b,-0xd3f133df9ab98,-0x65e43f8a397a,-0x27eef5489e6,-0xc8c6d8316,-0x3158dc16,-0x91f305,-0x12d85,-0x15f]
def m7 : List ℤ := raw_ints% [0x0,-0x2c6d1709723e7757fb22ca4eeed7a8ef9fcfc000,0x5262cf34eabc1a615eefe4ed3235767a3c016d000,-0x4a06cc4bb73736095a599ffb83e67269ade3321000,0x2aee72a07064e5cbb90b00afd843ca8c49cd4dc0400,-0x120f9c08f0878e01f5cb1f60b034cdc14c4feba05400,0x5df7c7f9119e404b81e6b52705266e2c06ca044d8000,-0x1893403e6b5b10221da67387fb9a7d793685b5c05e000,0x54f7cef59d6178e60a232d312f0bebc6754ed5b23b900,-0xf77b4b5e6efb5c2338e9634f800b97d08d08f99b34d00,0x2680cad37a318453e9eb7b491e0a16fd86820a8ff8c400,-0x52d16240c098bf5afca8270eefd735c3beed5fc22f2c00,0x9b3d8033de967ec127a742108eb7e1f47c677f18659e00,-0xff48448be817f750d82ab29e77ebf20e83aae302448e00,0x17230ba1e6612d9390605b96e2cccb797556a07dc6c6c00,-0x1db4a0cfcebee70eb84b3b2ccccd5463a10ebfa70b1a400,0x21deb4b30569d8fb616fa6d18b97208ef6c265019ec5b40,-0x225ed0c80622216f327e5c96e5d8b367d43d29e323ec440,0x1f162e024429626906b70f4c6dbffea84f6609d753c0500,-0x191449a5ab99b2e8d3bed25fd4879f8424bf4d58c14d700,0x120c9e6ebf4dd8c8efefb488c31c9ee5c52d4de2eaacf80,-0xb95117a91926406e330d31246b25f9727e6687c131d380,0x69e9e78ad3de64c2333c55be2d7be1e1d6e74dcb1ae700,-0x35d16a46e158e8ddc1d72434ce3c749525e9a9b97aad00,0x184100a92f3b8516030e9d07671d7c28c5a476e2f435c0,-0x9a9d8b5532390cb824f6de0de875a7c2f9f8df29a02c0,0x363eb82d71209627c50b96c049eb3346e318e747f3600,-0x10acda9f193bd84ebf53d6a679596b89f43c1fe89b200,0x476deaf507bc20a8ee4c295fac1dac69cf6761861b00,-0x10884427321843b2004c24ab65e26a1075aa83fd3b00,0x3474416f36c9e759bbf492a85dacb72c363e076fa00,-0x8d091c7a2924046b7f5c2b0fbe4a036525c4465e00,0x13d092f8161d719c6ac624f64008ad00352d13d6c0,-0x249e13484ecac115afebef0b3c197d292269379c0,0x3675a4f49b92dfaa55e5e9375586f732b4a58100,-0x3f6ca3a1aae55a5f928866c443196f19363ab00,0x37ca23301e89b76934daaade1b42f8f377bb80,-0x2349b218d5f4d886c9e7b6d2f9f9cfe84d780,0xef8574f9fbe048b1fc30bee6f91dac7e300,-0x3d66388507ded07c67827982fec6280100,0x808059235c8fa09b6fe62c815f799740,-0x649e6705db8565e843bef0e573ea40,0xe396c69e9153e1bdf03c5000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 22 48 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 48 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 51 indices rho q7 m7 7 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 51 indices rho q7 m7 7 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x15f,0x1]
def r8 : List ℤ := raw_ints% [0x7c5a556d8fd4b76bdffe00000,0xa9dc088afdef41cf56f460000,0x6dd6ad3bf38dac20ccf990000,0x2cbc18973e32ec27d479e6800,0xce0e0a642b8ad3b92c164a00,0x2c9ae8bd17bc1c402d37e680,0x78a4a2c186c3d9fed82ec60,0x10531a206307c92a6b5b910,0x1cc49268b29e8af249cc50,0x29bb792b586858fe13820,0x323290a06ef72d833996,0x3243d605efe48183c85,0x29f25dc7cfe2de40aa,0x1d1f785ffc79f1cc0,0x10be0ab3e0a2cffc,0x7e74e2cc21332e,0x30626a0dfca24,0xeb5bdb56954,0x372127ecae,0x9738ea05,0x1131c42,0x10084]
def m8 : List ℤ := raw_ints% [0x0,0x5085b9c11f11384f772f0eaf10e6e23251a88c000,-0x93c6c23a9ecbbe56c7bee284fdb98a475536959000,0x835f1d65a3028e129dfb13e7d07a814d413d59cd000,-0x4b5bd7cf1d7f665e40f90c5bf6fe2977f61740953400,0x1f594a0c2fe1677cffd08a491a8bda2524d2067044400,-0xa13b5150601e84ffb1d35f49839ac0b46728d2fe5b000,0x29ab7fdc0e8c332654de5af9a80e971c8c44013b8b5000,-0x8e540e7f102abd06bc1e8ad3c66185182b594878084500,0x19963c17288a7add25db979c1a9c1828b0264329955c900,-0x3ee04db86c065c705909bbb9c788d3ef05f2e1883914000,0x8574eb39572abcd86901f25dbe6f037f02e24edc26a7800,-0xf6c1144fc942759bd870a8570dba72ca232e41deafb6a00,0x19010f9e3ff725ccbca29565e219622ded6ba916ec190a00,-0x23bb7b6bcd2632e585036e6546ddff7fd01b3edd25010000,0x2d300b5dfe7a2f03556d0d416b0a6fa8863aca1bb26e2800,-0x32b88b14f6857017f9e949af91017d41b1d4300a6f508240,0x32a3dca5b658c03630af6b2573bc8a80f416d48c00e43740,-0x2d08f896c5709b23db26f7a56c5ca3be264fc53a19c24800,0x23b323e3fe8e4b73f759ddcca6264a023994b59d861afe00,-0x193a2863877a0a15d7fc3804e12794a447bd18ad42fa7e80,0xfe1e8aec10b01291e35e0dbffbc666420152d70e6f19e80,-0x8e5e81eb75c43ec34aa0bb73e5c030355bdc893c083d000,0x46d8f5c683832be2c1f64505441e9420d944b2031f3c200,-0x1f3c936b11ad7854aef759e94e6b514a404cffeac3efdc0,0xc297dda405276e007f1d452724ba678277ccee2b4e3ac0,-0x42a1c42a309d75985add85707615013e687d489c0d8000,0x13f6a32be7f0f097cc4c1d0ca2a5d37807bddfe8ec7400,-0x533725d7cf3dde985bb4332223a37a479961fcf4c8500,0x12b59c946a67024cf87f831e27f911d85152200528d00,-0x398cb75fd827c81330925b4cf70f8f2c9991aa93b000,0x95ac134d923ae2adf1c4cc81c18c7794d4444d79c00,-0x14496c7d08a05e51a49742b0b308542ee7482abbdc0,0x240ef40df99c168a22acf6aeb1204b683f7657ccc0,-0x336587db26e343a35d0a43b0d1184b54c4b362800,0x391faeb5653f1cb15ca134f0b5d33d0ebbd46600,-0x2fb56d739f05e14bbcd9620ea15d7cf6acd9680,0x1c795f01ec5caf9049effbec19903e9bb5fe80,-0xb4f83f2ea5cfbcce62e46e1a0a23ded91000,0x2b054f7f86ba09952ee7fb20b08755c0a00,-0x527d87096945b0b14950d937c3f134540,0x3a489e3246b1dc091845b9bc67bc040,-0x74bc4313bdc4f9a149c938000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 22 50 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 50 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 51 indices rho q8 m8 8 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 51 indices rho q8 m8 8 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x10084,-0x15f,0x1]
def r9 : List ℤ := raw_ints% [-0x5ae0f7fb57073496930c0800000,-0x7be8a88f2213b3f324dae880000,-0x4ff661ea7391ab276065eee0000,-0x207e5093958016710d4b3c96000,-0x954ae35b41325664496da61000,-0x2039f740b9b1090f06b539a400,-0x56e2b1b5ed2e45b0fd98afa00,-0xbb6e7a7b89ece2b8ca123ee0,-0x148f235c6762d5b67c9f9270,-0x1daf2a3181ad5992b01dbb0,-0x238308e8314e504f251788,-0x2355acae7a6ee8571c3ee,-0x1d4474a99ebfa09d03cf,-0x14239bf268598969122,-0xb73f0443a74f8ef64,-0x555ac0a974c190ec,-0x201c46e2d1b8a5a,-0x98cd8c9bc8cf4,-0x22c008a13f9c,-0x5b730a98e6,-0x9c7e6edf,-0x84b59a]
def m9 : List ℤ := raw_ints% [0x0,-0x91f260ae084f361008054a9d4ea279fb34017dc000,0x10922aab4fd2932684e771cd96ca368d2693def15000,-0xe941fc1d7b59dc37f038d7ef900363de947c3b2e9000,0x84614a6d1d93ba7407bcc758011cc40e9ff1852532400,-0x3677bcbbd87dfb2a2d795e6b08804ebd90b9ce1733f400,0x114fe0fef82b2f87a1d5e3e5182f5b4428f332b35268000,-0x46c31e021451a3f7a757b0defc466082166e6ea28bfe000,0xeed3ffca4955c28240f4d3d188ef2aeb4191d67dc726100,-0x2a6911befb950132e9cab74f237664b2a08d3b3e02ac1500,0x66e7f011a57df2889cdba62b28c8b9643d26055f5bcfc400,-0xd796129409d06d2693705a63789d346ca518dc6e741b6c00,0x18944638239b58c853145c4ca308f979698050d14c4fbd600,-0x274c8fd5175b7ab0daaa65baf305087e01185ec1288c16600,0x375b5592dbb241ca335bd2915ee64e873f9e476bd57a3bc00,-0x44f7b8a685209c7d9531151620f6c818f8e5baf8d9729b400,0x4c3946d0a7143a2389ab07eea2c2d59bb77b22c7d5afd0d40,-0x4ae3ad24c4f73ae9b2675a56a5048d26c5615b1c94e715e40,0x417f4c88c1f8a73db6281f48fce300758b4f25d0d2b3ef500,-0x33068ae43414780c170b7d5901309c296bb51983269b7d700,0x2368d326744317752765c81c1a4a5199aff443d8efbdae580,-0x15dfff9353bfee214b1d5c056d041b8a616b2c842a42cb180,0xc03da982f5e9c5bfa8924390534ef3696626639314dfdb00,-0x5db323a55ad9d64cfb081614d1bbf823a955537fd2b19100,0x286bc36a9732962abc9d80dfce7bee2c5c1ef497472cfdc0,-0xf6176513e3cf554ac8f080ff504f5c0ac30523809aaaac0,0x523f492e22bcf2de67d74b5170e45ed6d01459d380ec600,-0x1804735a6990728688687c466740772623dd5ebac52a200,0x616bd94cca727b470ef5b8c9c1e0ae32f5da0ee093af00,-0x1546a995949f52638a3be7aa159a4829862efc626e7f00,0x3f70e4317e40bdce77cb032ee186e9bbdf11445abc200,-0x9f9267c53bf1da1bcfcc4b17e372f5e7753e19374600,0x14dcad1376157195b2c89b2855e2ff1d9ab20f21e8c0,-0x23a7d164f3d3784e9aeb77f0be34d9bf01a113033c0,0x30b0e99661bb79cc6a643d702325d8e44dd2196100,-0x339f98f51c64167f90d657cba7dfd90be5273db00,0x28ea522fbe33eae131965fc572c887cc851e3980,-0x17071c4af023c6ddcddffafab3398e55d1a3d80,0x88f1a1a35047e777cc129fdc32cd6ec99f700,-0x1e2b0b05da337fe7a78cef8a35c0ba7d4500,0x34f6384b7b9023fa050dfcdfb2054de340,-0x21c0501fc64f3c38cff81f13a0c72640,0x3bdb5ab829c53f5e1419940000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 22 52 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 52 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 51 indices rho q9 m9 9 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 51 indices rho q9 m9 9 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x84b59a,0x10084,-0x15f,0x1]
def r10 : List ℤ := raw_ints% [0x2f04396aa7c2f10bddcc62b400000,0x400043c6bbb9f38a128d0d7a40000,0x293a6713d110867d57502d30a0000,0x10b860549bdfe0af86fd528277000,0x4ca71941ca3eda9d91c0c0272c00,0x108176a62688ea9ed87b7bc35b00,0x2c60f32404af8fb64d465345740,0x5f7066b4927d43ab8798737320,0xa6e9a876303cf89a2c4ada3e0,0xf00a48ab58ceb214006ab190,0x11ddc8089d10a19b9c600894,0x11af24f0563c29bd121da92,0xe8ef94bbfab2111bf9574,0x9f237aecb9b839888a9f,0x59bb1c0a10993dcba08,0x295e0945eda99e9900,0xf5de2d650a04ab88,0x47f98101e691942,0x1009c5d73c2424,0x29154265cfe6,0x43bfb2d124,0x367e48f7]
def m10 : List ℤ := raw_ints% [0x0,0x108874f3b6f0f91fd0e89973d1e867d174e42b3ec000,-0x1dbd11012d63483d855f6e048be3da2d354a381561000,0x19e5ecfa2a8fe9264442fda6bcf3cfcc238671db8f5000,-0xe8b8c1985c51e6df9845af8a794674ab4a0a4d0c15d400,0x5ebb08962ef5977c9d6ac8c6d75dce845970d6b75ff6400,-0x1dc750a9093bbc888d912e3cc16ae73e7443fead79ad3000,0x7857f862578e1eb1b81b8f5918d836f8c31d130ca1cfd000,-0x191720afd4926b83c577ae1775692b0bd2dc0acd151014d00,0x466ee8df4341f645982f99246407316b9a4a5d49565ae7100,-0xa8ca16d216e9ce193200b1c79dd73dcee304b2ad95f9b6000,0x15d19b606d23ffe1983fc5d1b8056012d9c91d086c38c4d800,-0x2746de98f4425a3211bd775b1bba25236f84bffd72dcd3c200,0x3df16ec5507c43e85c81a2f8f011fc161f06d07e4038260200,-0x5605c7fb18f255e4eb0d7780476b115ae41bff7276846eb000,0x699b672bb0622f3bfdc4ec65a0dbb6a23aa1d165df8ce79800,-0x72f2b6b5f32c5e4f87822ed04ba1814fc660bb79db496b6c40,0x6f282b61e4ea2b124a7bb4912585a26b54042417c123fde940,-0x5f9fa28e1963b1218cb045555c766b0533aaff55c9b7cfe000,0x493958a888f368cabb208b1b52caf556f4c4e4ed70f1226600,-0x31e8d04f96df47e92618e0bcbd4fb5693c4011558797393c80,0x1e424a6d98225a3d60846f9a2d9afd9882f77212daf49fa480,-0x104bd78e4c6a09d647eb6627b68734a5010ae129e6150fbc00,0x7c7d6b8f58a8b22c7d87d832ab2a1a5fdf65fd078a6fb5e00,-0x348cc45f767a7bf1375df811731346f38f62a9166470c55c0,0x138b19a33d2204aa6b9ba80084ae251650bb812386f2e52c0,-0x66021421aaf9c44547e96d7674e76d5311addd8b5fb94000,0x1d08914f8f20331e97470c81c7a76f169e8d628e91d41400,-0x72994b540bc0002510826e1df5d091c3850ae56d9520900,0x184f34109441990f692872d73cd6e8b4d9c0414858bc100,-0x4642934ec3f36690dea21561475737da114ee2b1024800,0xaae42666896782522699db3f6e5077b3f8bab8fead400,-0x158baa8b2a744762ab0afb146394d0c5514148ba7a7c0,0x23661b79e90bc9206731754a5f98db11200a21bafec0,-0x2e4c1d7e066f637130c44675a2ee0fc757c7a729000,0x2ecdceea62d9b400178d2587b56a37c6a765fdde00,-0x232f4c912c1eba69ceb865494e1411ad68bc85c80,0x12a99c064e03871207931e77b9bd7030ffa32c80,-0x67c6eb1b18119922f39f2b76d7baffef7cfc00,0x152bb352f90f402a8d00cbb1adc2023b1e600,-0x2201bca697a13816c4c0f329053370a1140,0x138a020232cb663fe5b6b2a29bb9f9c40,-0x1eaeae99427ea00be4d6fe00000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 22 54 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 54 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 51 indices rho q10 m10 10 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 51 indices rho q10 m10 10 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r11 : List ℤ := raw_ints% [-0x134e548c6e755a1c2d579f112e00000,-0x1a3e0754b1232ca93c487dc1b960000,-0x10e0bdc4d8260bee9d2422918070000,-0x6d5384af55bca5434b6394cdfba800,-0x1f439e726b85a15d52003309564200,-0x6b7b720bbce740b9b376508696c80,-0x1204aeb3b50a6c5dc453b4165efe0,-0x26a53cf8b5a3cffc52ebd7724170,-0x4362190128b697c6f26fdf03f00,-0x6093597dd3d85ec5561ac16220,-0x729135e21a249347bb8769476,-0x70e6433503e331eecd44af23,-0x5c7933695400a7e6dcb9551,-0x3ece16547bbf4b753e12e1,-0x232b3677bfd3fd331b130,-0x1014b77c5e9449a74f2e,-0x5ea3bf92c628c274ce,-0x1b5f708585e0f6d42,-0x6023ae5d9779a22,-0xf19bd395579ef,-0x1849816f8539,-0x12e3132f8d]
def m11 : List ℤ := raw_ints% [0x0,-0x1df753f9bb94c389aaa59621ec753c2ba3dd8e61bc000,0x3561ed3cd081c69cfd95daf818125439577b60a6bfd000,-0x2e078a2dc7b2eb01bd4fa5af08014c36a54ef1a73ef1000,0x1996c3aea0a9f43e2593c7886b70b84d5b5f0ed19afb4400,-0xa4eaf32bbe55c884546fa84bb74d25b71fb45c31bba49400,0x3348f64c3776b0edbb960ebc0a9ff17b78af8ccb709738000,-0xccf6f29220c39bacce1789be1ec756bd9ebcaa915774fe000,0x2a3eedc90d20a79e4957f9d508f7b008d52f725bbeb7b04900,-0x7532a2934890e87e737373d05f7cd451167d493f3caf8f1d00,0x1157356876bc82f8e27a6feadfd32da6c1083684cef1a9dc400,-0x236a5cc4603a55b4dfc7ec9f3c53db4fb0286607f7cc3fb2c00,0x3eed332aa4be177194e42092d43b835f8b75fe52b6d1b2fce00,-0x61e8de95413700b160509cc6a43a0affc58438052b408eb7e00,0x8614b3372c6c2e82d765f2b2d9e0ffb7504688ef855964c8c00,-0xa23bcb42798203d6381459e84abc7f1b905f9450187cb7ac400,0xadf08a4d8872474a23e2dcb3975f050cd423176fe097165cf40,-0xa59591dcb1efef96c0bcbbbb1121179e05e8fc291b455cec840,0x8c22d879d787615f0d9edca410c6a09c4e2f5bcac50c7b02500,-0x697eea77f73d13770b5f1b15aaf8a2157a8d9965c181625b700,0x46a2ee8262a43f20c7832e5575210f0a0ddb628fdf316c0ab80,-0x2a08cb89bad5a1c13510c186f825197ca00ff21f3d3e4699f80,0x1633282138100ef820b58a4327f4883fe8a3979e59e6ac32f00,-0xa6241d67f1731cebc4fe9b5e42b3d5deeb39e052d7fffc3500,0x44a1a3bf68dfb112833ec804fc74a22244854b76953b2d05c0,-0x18f2b68709f9582a830af972801ef40ec02ecea56091ee72c0,0x7f1c542df0389fd26f71fab3bde414f2877535532a08f5600,-0x23432a095891a2859e74a3c3673bccc252e0f6a009bdf5200,0x876fd40cb07661b9d260e7b70a726678907722483829e300,-0x1be75c183ba8051efd2cf0f58ddbf416317cae6bdab5a300,0x4e2a05c1c6f1d79ff0b59bb39c4be3508b0eb26b1214a00,-0xb7d039729423cc34549715a1b0e3fad95a216f3ab32e00,0x1658152980e269e19446e73b9075cc15fa23e20fe30ac0,-0x2347cb51243d0f9911e1257625a6060c9c2d9c9727dc0,0x2c2d3abc4c7aa0a1530da5994a13d8b426fe3aca0100,-0x2a90da56a008fffd28f25b5fdd8e0a94b6b665aeb00,0x1e55b9741f240cf8a6434ad3b8ecffa9c63027a780,-0xf279bea3a504f5111191da06b17f1d994f777380,0x4ebf1bd026307436b0d60232724bd8626c06b00,-0xeddc28437e8b66643fa5acbed39797d07c900,0x15d64560e5b9520b99bcd43e101fbfd08f40,-0xb4edfb29e9ebc1472d3d615dc4b32a240,0xfb90a3e3c229fbf716875000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 22 56 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 56 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 51 indices rho q11 m11 11 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 51 indices rho q11 m11 11 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r12 : List ℤ := raw_ints% [0x6b0fa79fcd9642e8208fc1eeada00000,0x91569c4c38f4aa47741ef44284b20000,0x5d57ada39cbe12ea35916dbcdaf30000,0x25bade9ae6b5c4a2ce03fa7fe995b800,0xac56566314043b429859f6619db1e00,0x24f584edbfc00e6921005fd38cd1380,0x62ec65a73b3e61d0e80fd6bb9f2920,0xd3abd2b70b56f884f2e403d6a22b0,0x1701b27196db70876e9aa3b3857f0,0x20e06dc5adf0f9440313c79c6300,0x26df3d17e2546a66d460a635782,0x26297ef7f8f554e6ecb9502957,0x1f1fa893e8cf799866d01f94e,0x1508b9d305f7b37c13d47c26,0xbb6130b2a78a0bf974f574,0x551ba3fab771a7c03d682,0x1f0ee4a69ecf2d8c508c,0x8e5f4a15a486009980,0x1ee4f59419ceea84a,0x4c8a4716815a55f,0x78e6af59041d6,0x5bd821113f2]
def m12 : List ℤ := raw_ints% [0x0,0x36504834a3fda269854c201d7c947d0f1901921124c000,-0x5fd92b38ead76a6c245b2b1d6a0a9404e2a01e6e3ba9000,0x51d9611e38638f525b97b285890d21200b83244b10f5d000,-0x2d0d040691902607751971a671795d9d19d6a9c9f11337400,0x11f62954f096956bd8b412f6a60f4cff4ae8e486d6a3bb8400,-0x586e11e2dafd19e929b2be9608374fbb022fbfe3a0cafcb000,0x15d970d96c5fd7801d1b180318af83f48cc4b25c520fc785000,-0x474009602189d83b1f2f70bc4bb4b65eca48e2a9f70edfe9500,0xc361e368fc73377c8fb231b255c66c9b56cdbd779bc80cc5900,-0x1c90887516e25b109e66d0f5609f0b179bc4a8f98ed2f6278000,0x399ebc1f3e0f4a69c55d6d26a623ad865bf023ccd48e5e603800,-0x65132e140fceeb18fd8e728c74fb8335da115c4496d5ff5b5a00,0x9b307444fe3804f462ec1e740ff8d919ff0503f7fbf14bfa3a00,-0xd19c68550b73a397e5f0f43f80531dbc47ead5be0ec5edf7e000,0xfa041c511de37fab87ff23f37fc847c2362e8b31e76f8fe58800,-0x10817f11efcc648d08d14f0a187164f3226ffe396eb33d622a640,0xf78a024e535397623fce418c858bb31e7d3028ac196c3dd12b40,-0xce22b4603b245632e58ce0222fb276aa0a3f4fab21044f867800,0x98952b1e56b00cd230c1d54f80740c6d56c4053742869f478e00,-0x64603dd840b1d55fec130fb65766f04d3f6e58eab66ecf0f8a80,0x3aa2fd324c7c6a08cc96a249b12a51a30fb3555b3aec73dd3a80,-0x1e5f55603aa1f8f087ff26ebda2fcc2345bd7b6518d6067b8800,0xdeb4e4409863b440d7cbadde7a70157baf2091dc470075e1a00,-0x5a09a797041063181405b7d83c0db7e4ca3ffda206045f20dc0,0x1ffe2cef73b289b646f83dadbf1398be9e27a0d341fbc710ac0,-0x9f1e8b4e8df1b0ef37302972d1b96126ec95d73148ddff8000,0x2b0666461dacf49e124ef7ee191f1e2b611c0a926daf10b400,-0xa0cc26044084971327fe1fa6dc6f8226e6f10b2f45d816d00,0x202c9d29057fde51c5687978a2ea57fe555d344d51d08d500,-0x57573e49e5342eccb741ce507e0d75b90cf2b287b057a000,0xc68d7cb0c21c5ce2d11b6ff773471d2a730d0f1a9b04c00,-0x1743fc9bd506101ea4a676b71cd67a5b0403a45a7c221c0,0x234b51ab01e2f01e1bbda4077e6cc322ae9a30bad680c0,-0x2a4bd0708efb3c99b75753ef0e464762a5a174bfe7800,0x26d3726bc4ccb88338b062c7bfa2b62bf0603cfc9600,-0x1a37a2584dd35ec489f15a6a411a0f5783529f57280,0xc5439b8ec51797e6bf2d1a5acf460a3d6e0dcaa80,-0x3bd34ae76bce77610e8076b4f50c46672b5dc800,0xa71f1dfa664904a0c463c3b8cbda118274e200,-0xe05c7b1a095d8796272dbc63b8b8c8895d40,0x68ae19cc385107b86c949cb43d6cf1b840,-0x80df7c16d8d9f8200fea38000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 22 58 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 58 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 51 indices rho q12 m12 12 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 51 indices rho q12 m12 12 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r13 : List ℤ := raw_ints% [-0x2089ea97bd141678de16633f8516400000,-0x2c1ee68886084b0d16620599cd15740000,-0x1c4cce7c4f1cbb6e8dec4098ab8c580000,-0xb6c51cccb431ce4b29a5fbffa36deb000,-0x3418b172bd876ef2dac0af4af8fb72400,-0xb274d739622399fca6efc8822ca74100,-0x1dcc14cabc086c1be4edafbe740692c0,-0x3fa043e0fdbe87228bcf2d22de46b80,-0x6e64a7208427beeaa46bc27674dd10,-0x9d58b29cc8b62059bfed5c0705c10,-0xb980ccc2241cc3638b3407fd77b4,-0xb5860cff3556dbc3119157176f0,-0x9380029870ec86512bf07ba643,-0x63443e7450e2cea65972bc5a8,-0x3700f2a5ddb2e6ccc300651c,-0x18d8160d7bf5afdd137f4e0,-0x901f0c99ac0a4f102b5a2,-0x28f9ddf83c4cff9cc120,-0x8cf890d824f3e59038,-0x159668be5a7d5c0f0,-0x21a2e0ac6808343,-0x191ded39673e8]
def m13 : List ℤ := raw_ints% [0x0,-0x627182df693bb65f4199fa3571cd22ab5d52d8bf129c000,0xac230d7ddf43c9274d2d770ddd6b8c2b85df15d7cc225000,-0x919cef9241675dec7a2d88d85de105fccd76e038a1d939000,0x4f5f1b278c5d92937a387f98b4f527d04f5ee0ac9e96bc6400,-0x1f545ce426fb3b4362f2727808ed8c3651aa0ca3d3ece123400,0x98a8bd133e91c198feb1cde6253f8c184c8ff6c3144998c8000,-0x2551bfe5fb4b130896cd49fab1b80bb4d5dedf5d1bd9ab3be000,0x785d89fbd54e4b91f78423ada1d64dce1ddb2bfd7d0b90157100,-0x14655a1f59ac4da99ffc22951f6ce44a5880b64c32a074e6a6500,0x2f26db32cff90f8753c018e4415a2fe6d4b6b9650c15d3acec400,-0x5df68615af9d74f24d7fd5951dcf085ca3315677b05d8cb51ec00,0xa2c296427e40d8000abd2aebf455dfb7c26cfcfacda18d15d0600,-0xf6a6bd6eb18ca143cf9abf2f8cd16c682fbc461c91effa5dfd600,0x148a6985aa1499d39fef3ec79f75aa03312c0695d5e3b99f05dc00,-0x18280ecd47fb257d933cd0efd63615eaf333b0f55e205ff7685400,0x1924e88458dba29f25d0312723c7af89a80a2c4191b07e3178a140,-0x1735a687c82c86da670c2042a5af2f6888cda2bf47e881aa0d8240,0x1305524d12b0931731e5054d89a9ed1deeadef057e509ff3c79500,-0xdd8859db6353acfcb2e3f2b81c79da94b8ebc3a0dcfe6c732d700,0x8f345de3eb229363e5942ae4c1566cf9269af13c2f0de77c28180,-0x52221cf36028f75854697ca16efbdff272cdf23ee7dcef81bdd80,0x29baca6d711d6d74994e02d16fbdc58e43916b8eb49321582a300,-0x12bd379d3a059f81e8f8f7e60ec3750b3492c4e6f6f60dfe9f900,0x76a48f52fc2cf88cc7c69f92c171150c248d518f105ecfda2dc0,-0x2935eed2f7eba6037b5f676c2eb49921a62517990368e5955ac0,0xc8163915f9c94151dc7f2e1f6cd1e0812a2b8666e98c7a9e600,-0x34bbc20c801e4d7327ae091f49bfb87a0fc9b94dba492380200,0xbfc32e2f82c9309af5bec61c2d8218597c35bc570c6520f700,-0x254312ff9e34889ff88b9b5e58988383b3210c97ba64552700,0x6203952a4f355fc8820b810134df82e84e5960c4e73891200,-0xd75c056e252d6f7b5c21872c7fdce2bdd23745299e7f5600,0x1851d6abf1f5cd1029837d9e8e6f22817998914dad87fcc0,-0x236f893761b635637908344fa4b8b2657cabd6d8ef3d7c0,0x28a0a7b840a93b8272f6c39b715a91dd246f5e73dc6100,-0x2383bb64c39520bb1fcbfa8e903cf19db4b6c7e54bb00,0x16b602173347111b3943c90654369684a07d99bde580,-0xa0c27dd8ae1f6fbb2dc02c3654be2b246af41fb980,0x2d802dc46d618376a124aad3efc25849dab82ff00,-0x757a62a521bf8b80f38350b8959de3365ad6d00,0x9012163db3e2ea318b348726474320ef4fb40,-0x3c8bd34c5c17381ceb93556150065f25e40,0x42001c69f8a4b74e90a7d40000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 22 60 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 60 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 51 indices rho q13 m13 13 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 51 indices rho q13 m13 13 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r14 : List ℤ := raw_ints% [0x8e601519b362244b5282d813e5e5d000000,0xc0d964bda718a707889495ebbd6a9500000,0x7b8e1ef363265c6799fb27bd60940540000,0x31cf2c484e3174b89efc0e8f2677901c000,0xe2d8ac417f634367dec4ad7f7530388000,0x307e16a5b5b233c5123509ebafb941c800,0x815552aa162ce4d5de06f1eb174825c00,0x113a7cc5fe8c6d4cdc2d2eaa560eb19c0,0x1dd4aec7d0201544e396eb9d87ddef80,0x2a6c0dd8a45cf82c128bee33bcb32f0,0x31e30359e5a0bf674a33a74922cc00,0x30ada2a0f681ddce6fc2e95afce34,0x276da58a2817e6f1e63246686a18,0x1a707e3e583494e0d61cca243f5,0xe9710ec2f850ed9a081ff4080,0x68f2485fb1804b89b8398b74,0x25d807ce40d47df040067f0,0xab11ad86f62168ce109ce,0x2482b67c195da360ad40,0x58aabfbfa449cae150,0x88aeea9a6edac8b8,0x64bb379db1c295]
def m14 : List ℤ := raw_ints% [0x0,0xb26dbd34eebc3a8ca6e71580de43ced6992628da51bac000,-0x135380af7e27e370cffa0cb60187595db8e16dd4b21fe31000,0x1032c7236d9a9c64639d47e8bb3d6be696b488bd16198705000,-0x8befd5f644d0e9f025bb8ea0eb0473b638116e25b9580d61400,0x36b2a6615316f4a4634045d02ac74d581fd6db49282200b0a400,-0x107d8dda030285e4f5ef2b4b0e39bf253831c1cadd15578e43000,0x3fd4d07f44ea49f091f6784c2298c2a99ec1cc3d485abae80d000,-0xcbaab2d83e7564477e0a5c36acf5344d1f1cccc793d75e13e1d00,0x2220f2790dcbd8889e4ae57273e82e231e47d29d87fb8ddde18100,-0x4dfe84cc6a1728fccf6643762c2967e418f2c48192fdbe13d5a000,0x9993ccbd2e267b5aae21c4a6da6ca64e54c322609b18f6398f9800,-0x106be30396ada3ccaf0d26b67999a2feee10f538865371547a33200,0x1891297d601c609b5848eba3420e4486df62fe65115bcb068b5b200,-0x204c8d2916db2b0eb4c9a3bb83eacbb7c2124f5068e16f02c7e9000,0x2575866ab8e47a865b0456f8338b84530fe931d008802f6d00ef800,-0x266dbd662b70cadf9ca102159e6b7d9734959609fca6cec8a93b040,0x22f0497f7e29ab3b9771c65c3d742d323f9536ed7b2f7374ea67d40,-0x1c2eedd30fb2dfc2da21c34ffa3547b957ae0bd19ad41fa9c541000,0x142daa490b7678733f990b469ee11f6f4b140b5bd0d9807f51e3600,-0xcd1bb214963162ad9491dbe67ddedf2c78b86841ef88782de6a880,0x7382e442564ff7011aecccdf75e9be0cc5dc643970965afee46080,-0x399298876bb7a218c875f301851894d7f16a2b3f3cdb334d7bb400,0x1955f32379c04fe3e75aeb641c59043bec6f9ef6eba821d9f6b600,-0x9d03b443f78bd271b7fa5d529a194afd11f6373222e106bf5e5c0,0x3551500b99b111092fd4b77fd44373fd45e4bd53c3f34456762c0,-0xfcb6f5c2409fc65a24995181464a1d2cb2a3aa80a26068fa4000,0x40eb0ed19bc3d7bcd39c6a36d536bec0088432fb694d5cc0d400,-0xe5b14d61d61dadf903378c754ff28409c6dcba3449c73b23100,0x2b570fcf66bc0717a6d834db7af1d46cc7b0b112566f117c900,-0x6e73a3bfa18e3208621501f9b1d1a0987130a2479c3808b800,0xea86a7e87a0787e07a225d0b491c29f141912516dafc68400,-0x198487c658571748208b6a0a51b7d7eaa7594a5c430f62bc0,0x23b3ab82d125055ac5d2b4a9e3e434a44138e9df2f06d2c0,-0x272590e00de22ea84b534167cfef63168e539c7681de000,0x2092ab81ab2f1e2e5b939eb18ac081fdad31951e3b4e00,-0x13b767b04b8a4d8b4880b8cce5758d1242de34f731880,0x8338a92af8e0d30d9262ae5ddb14aa65af3f73e7880,-0x22a406ff55433c1b9ecee241fde44821ea3253f400,0x529dbed0eba10dd61b622c8ec72cdff9e7f8be00,-0x5c823a42f7d3ed9768815680d4b4bc2f5ce940,0x230243773fb835f812004652fe7e7a4e1440,-0x21caa20a4a98d85cafdcfe00000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 22 62 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 62 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 51 indices rho q14 m14 14 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 51 indices rho q14 m14 14 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r15 : List ℤ := raw_ints% [-0x23aff039c5276e25ff872d9f3d5fa6ea00000,-0x304addd7b1370fcba6f0b5c7b13b7eb620000,-0x1ee8621cd7098d626d85a456e826713a10000,-0xc721a533409fdf474fcbac82aa9cd8bd7800,-0x389c53b17cfc252fa1cbddbe2f3970f9f600,-0xc15c13ea8e6c367934130b8a2a88a19b180,-0x202ee0590013e8471649f1debeb1d86cea0,-0x447af354ab0b0178381cb7745f3a0ead10,-0x765b2de81d9273da007da21f0e8b5d6a0,-0xa7f9442ff315bb11b280fb8ffb3a0280,-0xc516b1a7c77279b3303c59d4cbb1a02,-0xbfd5bb217382fdb421818ef56cfed5,-0x9af2ef9a3907d83f2b370b1e214e5,-0x67942c29c0c4f1eae641e44420f7,-0x38f4b9690b2fddbf523c89bbea8,-0x19809c9991d6589a739f559d02,-0x9276ae176af8e3806304f356,-0x292919b532a35cb2360c08e,-0x8bb0ea2ad9d64a489959e,-0x150cb1678c29ae1df769,-0x202b9a3ae648e9ce3d,-0x1776bad146c1922b]
def m15 : List ℤ := raw_ints% [0x0,-0x14366e6eff0b52a1eee82d6f992dae6e4f5952a0bb4227c000,0x22b987847d6b6a215a5e09ee65cd1c5441d91db132d9cb8d000,-0x1cd82e393d169ef448c5423edaad4683a95f4d9e5f58e23c1000,0xf6e3603e551ac886c26df83862e47e69782fae534954cc9e8400,-0x5f9590012d40f156b506a5ba9d0e70d956f710cec46ef2d04d400,0x1c88a8cb011e3f3567688d12c4f160fbc9d26a0dfa845991d18000,-0x6d53cf3c7688afacdc2f1310b3d205120ca651919bb9e73c1be000,0x1592afe1ebdf70753a992fc8ac63b3995c53532d477e1bc8443d900,-0x393622d3a5fcfa5e0534d166a78ccd2acea8046ab62546d751fed00,0x8145cfca426a5fa144d8b9d4087472146d0f825ac3a011a1652c400,-0xfb9381b3850865d08dc3f9123f1796879e44e5fad2a4fdb020dac00,0x1a92ee73cb9978068c4f2de7c3664cb1eb64fd37bf94dc92b07b7e00,-0x274135df6d0856c3dcd3aecd455b1b86b62a9f3d099ecbd1cd446e00,0x32eeda0c0838109e6ebafa995fd23ad6e017a7123c66341f3c77ac00,-0x3a4383bda9acd4fe5dd954c48e35e03587e941e42e501865e80c6400,0x3aebc7af3bf7cbba363da955120edc7258b17a576d3bc68b04a80340,-0x34c60b9a1ec0922463e630f4c7ff5ed51704aeb5fed5597152640c40,0x29e88399469e1bcc9b64c55f4664e32003a80dc8e7048b6a45c94500,-0x1d843c43de584c7cd2e023d8d4de151babe686aeacad61605e9cb700,0x126e7839956ef18c746b2680a14772b2ccf809098b442bef0d4a6780,-0xa319e9f533f6848dcba4148765c307024fdbf5c22266c046612eb80,0x4fc188421d4bcea8d31681147d102b9dd40c4d69c39b43bb9383700,-0x2265e818beef0863ecb9f231f1c3f785f6e267c9f59d56392b35d00,0xd0aeb1ec50df7607b2fc60889443707cec120b404f6728cac2f5c0,-0x4547689263912d2450a703f405406359cc58792cb8b53eccf662c0,0x14091b035d94a4f080c7e9d9232cff2f71531b30bd459c0e7e7600,-0x5043ab071bc4b763c831c36ea30423df946a228cbb182a809b200,0x1144de7eeeabd819e6f277df72b356b519ad2616b7e903f60eb00,-0x329f1927034c2f3f7674d2d3e0fad62bd26ff27f71770e0a0b00,0x7cf99bacb81adb4f9e922a1ab614b27015746450b3964571a00,-0x10064c53735b551d70a248e93152436a9eb7983d54c480ebe00,0x1adf6d6d473c22db2f177b8118690e926b0e19dbaa14183ec0,-0x241748269d5fc3f4e86213f9d24dfc03259238eca1810c1c0,0x25d53992acda9ff1684e35597972fa931b0707d8742c8100,-0x1df38da5265aa13f9092829fd4389a84c477539e760cb00,0x1126e2177e83c46ef70ce25edbeb7467a728cbecfef380,-0x6b4543f1f07b36dafbdf0592f97c05dccf0aa1908f80,0x1a6598f111971f4117416f3a9c557096488907bb300,-0x3a1ee53955315584525f474a9f7246aa2c298b100,0x3b6561288154cb29101404c475acc51d9a0a740,-0x143c8fc0e7132abdf625e327709615d825a40,0x114bcd42d084fa141d4ae5000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 22 64 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 64 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 51 indices rho q15 m15 15 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 51 indices rho q15 m15 15 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r16 : List ℤ := raw_ints% [0x8501301d4af65560cd62745c695fe129600000,0xb3d36b1cde3e6fd006386fad788043147e0000,0x72fb1e78b85c5c4b406db329ed57eb8d6d0000,0x2e406821e96dc7ecfb751195e85b230d5f8800,0xd22443f98ca8c887803d841e8910896255200,0x2ccdf1fabdb888c3a564a29c9766faee27880,0x7727cbb1d93d5d886cfd3c6eee550c3f4fe0,0xfd2a677b61f3b2eb499144f3fff45c10450,0x1b4d6403fac55f5659a0d3183781ccb0a90,0x26ad9f03662a9665a3b70c00358439b760,0x2d4abbffec603c7256472e2892e9c780e,0x2bfcbc2e9597f5a039209623da1adfe9,0x23712dc7692ddcc2f40f34d437399d2,0x17a080a0524673d71804da940e2a4c,0xcf3b4c829ef45c6bcc53885dbf2c,0x5c777e13f6ee37b231b9aaa2756,0x210f451cc80e4a98cdd05165b4,0x93fb607d4fe985648ce9a0ac,0x1f39e67219e7f19960c5d06,0x4ad535b955bf29c0dfd79,0x718fb39aa205d12dfca,0x52228c7d134d59420]
def m16 : List ℤ := raw_ints% [0x0,0x24a2a8292e4485c58104d25a45a2cc27efd1e5c35367e80c000,-0x3e68169b5aa824acfe41e30ffdd16576e42a7168a02ac0ef9000,0x336303f32e9118ac3f4998032e4c7b6d5d5c7c5968a303d9ed000,-0x1b3e08cc7ea691540fb2c3614ccbe7e00b0949d38f617ec3e5b400,0xa72f291ff135ed87c19cf3bb1aae2104014da13d02ac156c26c400,-0x316db2221be7d5eac8e65d91894ab99e6db2a0e73021e605dc3b000,0xbb80f263448d79e96355ee62ca463519acd6a86494d665dbfb95000,-0x249e59af95d735f771cc683744d51f43d4e8c7bbaa65603db8b1e500,0x6013c715f2364b73ab00f4dd7a88f042db8807b102ca15149e77e900,-0xd6b15fec26d3deda9d52a8a3496de3541c3274c58ebe5e40c94dc000,0x19d0495f0dea2baa25d12b06770cc5f43fd761d94b636edda05b6f800,-0x2b1b5e3c0921573c68217242c6eb0f8f13f45a435be23746ba0114a00,0x3ee329a6c8056397488576c56891ff1778824b55701a64c759b726a00,-0x508ae6f69541ddead9bdbbd47ba1f4bf4103a3c2d82bef988900ec000,0x5ae4f50778e54c73b5b1bf67e9e89f994f4ded28286c254a74213e800,-0x5aa0acd636710a7eb19493559cb8a7c1b4eeba6d065d6102548750a40,0x4ffab6a5d9f0107809b9a33d2f1e3c5f440ceba9b99258ee93a4a5f40,-0x3e891ca7d0a4c17eb7d20be34b9e2d92c3412e7462536144f6d46a800,0x2b558b471d356d6ffc679a954ccb9efca6b32f7335812ef8d62d75e00,-0x1a99f78c7b11be2d9acb6fbc4414417fa278c91918525893c23f21680,0xe7336f5f41e5083ab866d01f36fb46a4dc38c3126e491ef46ac19680,-0x6eee9858d055ddc1c9d2ac84cd2598b49b4e3c016634567bb2934000,0x2ee4f08db3facd4b4f63f3e405a7582867635c6b436704f50d953200,-0x116839f8b629dc021c2e3c733706695e55c553e2f40655ef3405ddc0,0x5a664be8dbe92fc0504e9a9a688478e48b53b37dfb9af9906305ac0,-0x1985f1cad72a3f080c625b149343980c3e42fa7369c938947a98000,0x63a8a8af946f01229f5c14fe031dcda6a44ab9ca4680edb57e7400,-0x14dc495710c51402e3c2c3cbdcea7e80cc2eeeaeae3acde2fd5500,0x3b5e669c973fe606518088fa803f1b3d3ff98769774799e4f9d00,-0x8df82217d250c9b8a0133e856af69efa2541bbdcb8eb28cb9000,0x1195c6ef9ee3bdd35c102f5629ed26640d06afc2a07f37a17c00,-0x1c666abe5f6de81936fadac376f70a71d1896edfd78cbca45c0,0x249a3ddd0b89fbafd9c3c32afc797dc73b1893fa708c8a74c0,-0x24ab0a4dad54c722c72870b8ba9c77ef4706c5ee5fd92c800,0x1b9b9b857d39810356ba977e1a9757b4e1490567f8530600,-0xef324e66751922c61872fe7bbc72c2180706528d66ce80,0x57d023a00f2610931753830b4a0d19f84bbec9a731680,-0x1421aadd4bbdccd43902570f73a5b975ea8315228000,0x28e6881db06c34de7ff9dab0453d166cf4cc117a00,-0x2621c930f55ccda05984c5b6605ea0c8fba7b540,0xbb1acc00f4094798049a87a9a955913d0b040,-0x8d9bde9bfe96bc27a1f938000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 22 66 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 66 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 51 indices rho q16 m16 16 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 51 indices rho q16 m16 16 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r17 : List ℤ := raw_ints% [-0x1d19522086cd0d25c12dd298c9cfdff804000000,-0x274f99cb9592c1f5f86743ae1ed78ec0e9e00000,-0x191d123d8e2cc2310eae62957bc2f4b9ad220000,-0xa17ab64e08293cabd0c7f248e63f4906b260000,-0x2dcea4a7790b1e45d5684d7aa54c6bbe7a43800,-0x9c16e879f50613d4163e01c0eef11998521e00,-0x19e9a3b4caf6d395b1c6f02b5f562202268b80,-0x36fb51ad926c982ad13bac8a84a0b526f0a20,-0x5ebb24b2aed350318470ad2223e0a92757b0,-0x85fc1bfcad80b479a88691d4f129f323570,-0x9c9d98b9d2e13d090eba2ab50dbd5a65e0,-0x97cdfd2667709f0b826bf0592e92d0412,-0x7a0c32b5357b2b0f22c3d866e911f2b7,-0x5129f932b9b2d2b62754ba9c994a48e,-0x2c5f5c7614ae49292e02e1939a46d4,-0x13bd287c17a3705e278843f03e814,-0x7087914cd6414aeda92bbb8e4ea,-0x1f5c075975404eb3f6dc32b30c,-0x69685d1fb056194604e166d4,-0xfb526995463d8e9e379f9a,-0x17b23e20609d7ad6fd9a7,-0x110539c037aa27b9f16]
def m17 : List ℤ := raw_ints% [0x0,-0x4266d0caa3dc3275f9d8bd439e37120862ac7072072c5495c000,0x702e56b135264e067f287168cd53639c4bfa89d6ad4d7db235000,-0x5b964ea26ddfd35b3a276cd6ed09c03605db23ea0f40b185089000,0x3020c8b0af289a331c60e63da0f3c967b71a265d76ab774a169a400,-0x124adacb1e69b4df529ccc501c1986a70530ee565bfe2977a2e47400,0x55b807d41f8d2a9cf3836e49b90704b4605f55aeba6c47bec5c28000,-0x142020f68bef633235e1ee1cf2142f9dc639cb58619b628a2080fe000,0x3e40cee97d39908b90a5bc96c0e4849e12b9bb84512c0cc20dd558100,-0xa1a1122a704100aa1de0e3136efb28e521b1311221972682b41f1b500,0x16541d93588fa22e556b232df2aef7e1fcf2d69b9e5bdbc7832e29c400,-0x2a78848d9a69288ccadb9392811063f9cdc85782983e0fcae84a166c00,0x46177dc74965e8767323d052b842ea3c1c0de5dce5ff548941b6953600,-0x6501ab71d21062bf8a8141fefd0d957cf8334c10c0a9ee39f95f534600,0x7fb79ae1c930f4dc09d74aabc4c768feab002deb6cd8d50c4b93edfc00,-0x8e37b53ebd9906d636f7546d60a7d07de79231399b9769800f3b8af400,0x8bd4ebd131cd7d91f531ababc4bfa54c669f4c0c3e23cdd0cfce2c7540,-0x799bf9b9bc274e651ce4d9546337f0f79481406183588b8a07b67ce640,0x5da34eda77053e0c52878a408da0e132633a89f113a86870083d693500,-0x3fd96c82a6e8f6b805e560745c642395d14be761233d0d273b7b495700,0x2689433d1fa5c919c97a37b41d0fe1153a71c85cb88e8b14fd17b8dd80,-0x148ffad285b3b74796949331c6e612ac2971b7daab297825adacdb4980,0x9ae7f111b7abc1fa996f09aeeef21142da57c6c9e44583e84d78eeb00,-0x403067391d2e7ccd0f015c0a97ff24ace84f61499bb1a6737ae916100,0x1753e4da97d357fb0790468627f52815f02c35852ee0a00435cf45dc0,-0x76730bf031f3ba6005ddf57cbd298bf29f5d18e81bfeffa3c2dc8ac0,0x20a6440c43cd1663aff1d282a755c9f4049773e1a36fc1f461890600,-0x7c40dbbded5f50b038f56209bdce75a73553f60fb2b7acb2d8c6200,0x194d5a06bdb4db7cbcfa172758c5688781cd74f01cd30b88360bf00,-0x45e804c76bfb9f3059f9034806bb53b5ab70546ed26f630e834f00,0xa1e5cd39f955b5758b8e03f254245cf8b8433a9d8653d7dc96200,-0x135e4f0b44830589064a6a554f32cacbb4021edd304ce80736600,0x1e1df73bd6f6523ae6efb44c44a638fa418bdf61dc9eb3f250c0,-0x253cb52e0e6d5d4369f4b33046e5e47834ef94cbf758e55bbc0,0x23a309be44bce77495cdbe0b49b57470cc94ec9eac73b26100,-0x1981aab2beaa5eb0c36a6b6e7c2ba30946845e9481c811b00,0xd0dd98e3056798f8001521367f93b39e1d10be849415180,-0x47fa2e7069f95eaf9d9da92bf64b963f54b040ec6c7580,0xf5d5d1c95e6a643604749206ffcac237180c2c2d8700,-0x1cca28041ec7a4762d5da445f4764277bf324129500,0x187a46a08fd540894e140ba441ab52eee20159340,-0x6c16cdab9877d9131ac7f7fa732f239c9e9640,0x487172dcccd81203732d140000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 22 68 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 68 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 51 indices rho q17 m17 17 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 51 indices rho q17 m17 17 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r18 : List ℤ := raw_ints% [0x607af666b9464c5e56c0b840cb30bcfcaaac00000,0x823e4652d691eea1626d146669cb331e629bc0000,0x53237ab0516eb8424806c0fdd7d66a3096b7e0000,0x2161d3912cca72d64085f41e5006b329c5b811000,0x975ecebe796b40692ea846017ae37f562d721400,0x2034502e3f6a9fcaada06ce7a6164742cc784500,0x5571eacda341060cdaccec342f6a7a3a9de3cc0,0xb513a02058222afb076051a692be305b90d660,0x137921631fad63d31bdb9b7c5c347063c44d20,0x1b8084ac1895add6846b7194a1a03d9fb4450,0x20187ff4932c74582292eaf83c0dd876c32c,0x1f0e0ad61cc92c107b5633fd41479eff8b6,0x18eb355f4004cd84c801e8128c8e4706fc,0x108924290c32342d79ad0f5065ab927eb,0x904b86b4112bc51ea22ed3bf67c9478,0x40047069e0f44590d8289ae56364a8,0x16bdd0085f302388112716d00aad8,0x650ef851852b125b48aaff0e39a,0x15262f920bd88d300471732d1c,0x3234baee83a3bc4c838a351a,0x4b5c72ad222a457fa24b8c,0x35d10b037e20a51a1253]
def m18 : List ℤ := raw_ints% [0x0,0x785a5a6f48ff1b75d4d8d70a8ec3d0af32d88bcead00594f6c000,-0xc9b2ed2289cb21a26e8717cea264e507b2f5eb54ed5c73d3001000,0xa34ee8f8576ae858229bf638143cc6487bac7fc8a9fc148a1215000,-0x551501571d63b2d49c070162a24b938fd4e8939c21485330638a5400,0x200d22857da8de76f73f11af1acf148b029de5cc88577eb22dfe5e400,-0x94d0d2868c3e26d25f6b098dc3e5eb38080f9cd9d502a51f1d53b3000,0x229b8392befdea3ba5e188ad160c2d674e69c3ad77aea23aba5bc1d000,-0x69fe6085513e9c8962b1266edce2379ada78ba99a560f91b55cfebed00,0x110602903e0e972597b3a06490a43d5ddfc2647aaeff388080d94099100,-0x253a3a64ad43f1898d9a14a055aa6d2601c8f9a767aee2057e714d7e000,0x46069e4b24c55fcbc825527a1da0ae588a88938980eade833f7021e5800,-0x723c3d8fcd39703029b31aa201086e885bbc8774cfd30e8a5eb8c0fa200,0xa2a460b6bf9aafea8f40d2715c6a20cb1512adaafa84844d20d1dc26200,-0xcb12b939a5bd557181cdf7dd20b6248906c616bc54bfcfc21865cfc7000,0xdf2a7ddc39dce8b47a1a77296574d2826f83e896d1b8485614b91485800,-0xd869e7791b3e7081191733c22c6a3158804fdc8fe6190bc535ee0253440,0xb981ef329f23c74be2519dbaadd9553b5ec6bed08d6d55f6fb904cd5140,-0x8caf8e605bcdb643d4a42e2b0af03bf567d1037f3bdc624fee5f1ac4000,0x5e690487feb515aaabc18e7b2d8c8ef6682d3e9eda21e6e9a9526c10600,-0x3807e2476dea8c1f6a2531064460c202a4f8df68655d654b9ef9dca5480,0x1d5f13f33faa39fddc1d4625f5d886061c29edf01fea9408afe035f5c80,-0xd927a24558e3c9af20446317d21a4b748133cb85e29a023b744d272c00,0x58364827ed8067634580b8674bcdfb1c23c0f7781eaeb051352c9e8e00,-0x1f636e0f7bcdff50dfa737b98a0b183a5e10547b8c6133470d5ff0f5c0,0x9bd5fa6707c77073e6c9f04e4bf9f15867a8f53977dca534e68daf2c0,-0x29efa9eb17affd6969781c8b6f6b680e8753b5bce07a01f42d2854000,0x9b8c1e56d7005a3e01b9c348f2ee261252466ed0375da7a6e0e19400,-0x1ed000ba2c9cecb0147cf0b7114e2ded2052363d88ac08bc7909d900,0x52a2c891a3c4f97d4e4e7746138a8f226a80287d20646ad58c35100,-0xb95169b2c8f98236e355fbcd88393c2a48781e94861a31d9ea2800,0x15689d1e2c839b2a261ff9aabafe910afc7d0494edab3352ab3400,-0x200b3015d2d4119b23452a607b86e1fc4d31284f8766da3d6efc0,0x25ff1c780c10b77a83e821d6e8bf23831e906c0affa4e6ebe6c0,-0x22b9c4ee6358dca2908caa5da0ba41bb8a21eb824fb5bb73000,0x179de8b6cd93abd8c6bb7f311e386e7697d791f08f997dbe00,-0xb6b137ce0f3ec8e6f45b3308a01127816c80c132435f1480,0x3b113d5a7aa9487b75c4e85a7c9e9e033e7b41ae3230480,-0xbbc04c4027a761f8c014b2e3d32098a565d2db29e6c00,0x1444e249c7c8a28f64d2c38845edd4b6485cc6f41600,-0xfb5e37a5f4b094831115980de9e5c0b0e1eb1c140,0x3e6c75aeb8a4efd30b33a90a98aeb76fdd58c40,-0x250cdfdbd55d020fadde7e00000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 22 70 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 70 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 51 indices rho q18 m18 18 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 51 indices rho q18 m18 18 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r19 : List ℤ := raw_ints% [-0x1310f42c7e566baddf804632d0b6e43da3c0e600000,-0x19b88d8bee01984717ec898fe30e7d9169ee66e0000,-0x10680c093a7d6e44182d1e74c2868df2df23c1b0000,-0x695132037c383b2903e62606c28f6ffe9837624800,-0x1dd25019931368f6547fbed0fdd55fae4fc0386a00,-0x656b08206fb435b3b06f8adc02ba988acd9902680,-0x10ccf12502f25cef3d74e8e020fe9d1f1de48e160,-0x23908017e33f0e4b2c5a1b8b3b881d2f451136b0,-0x3d1eb641ce4efa26d789ac7e7b80d5187fb7440,-0x5634a1568fe36e3afebb675b56b8c63acdd0e0,-0x64756a0ba94b233bcd6c60704ea7a3d0200ce,-0x610bd22775de4deddc69d739be74f8eb58e7,-0x4dbc18956850a05ba2aa5feaa5acafe5a39,-0x337be721e0db52fa04a6abcbd984128b2d,-0x1c04dcb319e3abc89b5e78e93d6ae24a0,-0xc66bce90ea9438e58928406ce013896,-0x464cf5b75d89d7beddb190fa185b5e,-0x1377a3497f5c3fde2a9e36097321a,-0x40f7c1b031e1726b33161e7275a,-0x99a54eae88b3a3668641a44c3,-0xe5a36b0bff4bae1dffb1e01,-0xa32e5d56b5ba0fcd0d669]
def m19 : List ℤ := raw_ints% [0x0,-0xda23c3e9b44e61c591c905c322c2ea3d8c287d669990a1dff3c000,0x16aba71d0f64e28560e6cfd17b742eff7ac8d69299fe791ee701d000,-0x12351a6d67fe6e01be0626603a5f364728a7a68a08aaad8ed5a191000,0x9681e12af80a8c6bd9d29290c2385467561f96233b0132f3e9425c400,-0x383519da19af3ca0c15b1fef667a227c37e9d58b3bea34083545d91400,0x102a266182c7696670277676a10291ecbf080cb4dbaf9c7c369b85f8000,-0x3b96359602f2f37061432bbe4d2deffa3dfba5460ed83c2e4505d57e000,0xb4bc8622a99621b621836c29cd4c1d2c515b755961c68c9917532546900,-0x1cbc8a3319815c54b399a48d800794d682cd148810000c0a96b1a0f1bd00,0x3e2f8d8f4fe1d0c6ab1457664b11645de5cf78639f2eb99ef9351253c400,-0x73b39255b2324b0c9458a3eae61ced1a3fc679e4dbff61a9fa50aebc2c00,0xba9bbc60c43af3345c9091870772879b85598a3d0842cb07eef0e40c2e00,-0x1068a74bb4425dffbdd546f8c40d53c775f8d498d1f653908f4fd7fa65e00,0x143c14bb84814305bdbb67de2675a08f6527e975b94800a006da8afe4cc00,-0x15f3083935e9af9eddb90e4e5141d902bd77e06d803c29c2293539e100400,0x14ff3bc523d04bdef71350eda7ad2d74b8dd137088ee266557ed040aa7740,-0x11be255e261c8140dc593b53ad8657070eca366ea4c35acea115f53769040,0xd41481bdfae74fa51c32eb310530e3254eb509aefb761b2e619879ab6500,-0x8c160c686b228e8d10efcec31fe703c8b95a3d495ae7a7377eed3240b700,0x51c337b2bfff5732edc69adc975b76b319f20ebf696514b32bd5ba7c6380,-0x2a1c6463b9ea476b127441ff7e4022b5d37ff7c3062439afd1a2e9697780,0x13195ecee71200c1fc4ef5644a73f280309e52631e4abd39ddaea81dbf00,-0x79b340c97ae6be73389d3a2acad109b540fcf3f2846bc378b6a21770500,0x2a66f326be92939b5c2f85a58b8030ba7b3e7fb86eaf1df247c75bd65c0,-0xcdd801c188faa600e777ceb324b04fc2872bad2885cd474cd2357ad2c0,0x36149154181ba5f7f1bd978948de9318afbb7381faea14108c18b59600,-0xc37f8c8a6c20892eb21b78261a85169cf3e93dcfbbba9f72894441200,0x25ab80414d114c0a923387826cd8427445c2cc9c7e315044054ab7300,-0x620e4b25ffe578fee18901f39c25ca70d7960b0c5621c957430ff300,0xd4e73603abfef08e08c5ba17866cb0a00e91570393f03468e15ea00,-0x17bee67942f5f300f1f6b39530785dbf3531ec5d675ef93966b4e00,0x2233ec3cea40ec4ed1726927ce5f5b0afef01a604a453df314b2c0,-0x26e225247b0a3ee8beb828a7daa3c09ac08fd1ed83b5c144345c0,0x21ec3b61b8956e1f1cb60a29315e9ddf294bbbc3de209cc60100,-0x15e9a35cecf18ad251145dec207333289c8049890e793e1ab00,0xa00dfd0b31173eb1be03054ed6843d2961644a6c6ec617f80,-0x3086acfd497a89ac0123ab9d296befea536d326dcb4deb80,0x8f7a0757d0aa990cd5f21daf16475f35d07ee879677b00,-0xe45c639a4aa6f02a49405cb8c8fafd40a6a9b5d61900,0xa14f9d948f0f240e89e9d2129df6129dd5a017bf40,-0x240a508d8dd4fb9a1e80e66b1f6c616888431240,0x12f1b577a63c4d19e2ab15000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 22 72 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 72 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 51 indices rho q19 m19 19 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 51 indices rho q19 m19 19 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r20 : List ℤ := raw_ints% [0x39cfe442678293e4c5d4e89c29b2e2d8f44759200000,0x4df0fb888816200eb6aae317fa2f1c46a2b6b28a0000,0x31aea68931f0e3277633732b68dc002f912e15c70000,0x13eb0624226330ecb61d48c14d1816ce71fae6605800,0x5a2b0058bbbd329f59914e64398c82bdc678d854600,0x13261c2bad0a215448377b60acae8914ce39f8fcd80,0x32b4e47a4da7e300fe7bb2ca1477456077e849faa0,0x6b3acfdbf4768ab2b1172ae351ba782dd9c5c03f0,0xb813e95936a02015bd99ee6feadc7f00717ccb30,0x10350f1d053dbaca8a51b491d843de53114b45c0,0x12dcb0e818aaae5f7a22afe06467b8ccb14feda,0x1231f2a74b59ca190b8df787718dc1b201dedb,0xe8d29700251e4446389dbc5e48fe9203ee16,0x99ee7e94f8ee5ed3bc188c3678325c41192,0x539d0fc3a940ab22e557bf098a5ef3a764,0x24eded474fd10a40cab33ab98d2e775ea,0xd0daa3653d1a7ede9ff638f1431045c,0x39af0661a254a4daa81da676f52818,0xbff15fa5487fde8d0568542fe502,0x1c4712282ff980c45e62efd5f73,0x2a1b3ac790b23cb7ebd6a967e,0x1dcb4b58db9f2101009c2ee]
def m20 : List ℤ := raw_ints% [0x0,0x18b60d31796ce1136183c5a71af01488f8e096349f6562565e9cc000,-0x28c74ad4ee06621035ccfc62111c6706deb13c032e8c7b8802b349000,0x207e444ca5d4895dc0033d3b78ba51f76d815b0c29712f86c6e097d000,-0x10a69413cb1ae86fd63231a39fc2e02bdbb65ad682abe8bf2b0f42bf400,0x62a7058f8907a4adea0be0cb1b5a031992dcf6a20c4555f70ec42f60400,-0x1c1f7850e0111d34b6d62b46dd800fc561a9d3d5496c99ec08dc15eab000,0x66b99ece3e77b9add935d13436abb9ed12391a47d37f16f5c922f37a5000,-0x134a305f0bfe2939a7602a1cae3f170d6ca8ad835b3c5a3eebcec41ce3500,0x3096f1dca7abd107980a2dbed8ba7b012b78ca523bfdc97afc39850e07900,-0x6812345f444d128c63537106b170a09dff3c70db719fbc17fd33488bc0000,0xbf90b140c5d1ba55ddcfd7459b9d36c2147e4c53c38c2bd49c4e9db1db800,-0x13185c017b5f69bf0fccf0508725de04ece1e7dddde5ec304a41c61ca83a00,0x1a8d6bb4d1edc1469a1302678a41f87dedc53a04118ef9b90a65904fe79a00,-0x205840f103432711d93f5fbb94d5a1b44b4ec4df2b6d42a39bda4ba71ba000,0x22a35f32ae5eae7175ad317eb9b12488022e4a3bb3fd11b2a23754fdf04800,-0x20b130fb1f38d51c5ff5c634f0318fc1a160c69716e8c09eb151736a66ae40,0x1b3cc00974dcc7772804cf8d95513dc8918387b16eddbc4b3e35a76de3d340,-0x140c251d80c64501a319e01b9f2b73750a324403abb6f5ffbe5fd20dd2d800,0xd093149eb6c6dc1aed97d7cbba041caeb19dc0c2a4273da764927299d2e00,-0x77bc9ca4d02d030b593de3b4d2d3632404af50e7e799699ff1bbf4c2fe280,0x3c991952ddd19bd8b53c7131989cf34649d2d0c86c946387556779bc43280,-0x1afa66ddd7c3189b6f0d52c7c1b10d2d2cb4bc9b9a9633ff3dc3329fc7800,0xa88c3f499617264efdfdd2e128f669fa83128bc980a562ccf0de7ca3ca00,-0x398108c2f234bd0cfa565b542cace41269b7f1987792219367ecb6822dc0,0x110f7e85d1a205e423872d81ca26af09a265e59af6c598f06e82706e2ac0,-0x4603f80497d4cd78bbe346cdc8adb74b529211c060828bbecf656858000,0xf6ab15c008a7060d7e96be66f0f6d8cdff9b0a6a1040b0468fc61a3400,-0x2e3ad90ca52881dd72fe45775e04ebbbebcf2e32e4f89743a842cebd00,0x74c936759fe793ca0739739d651183c93cade6f7d56edbb2123ede500,-0xf5774db753c6788a09c7c57f55dbc28f34356aaa86016be78e6e8000,0x1a6d210d06fa79b12295dda257b1d76b43a62b9acbc4cafd4e95ac00,-0x249ed3945bed23f3b7a495d747441f0a7c7d71d9a407778d590a9c0,0x27e6c1e1f650deafddf520c255c99b3c7b65acc0ece76311c9a8c0,-0x2137ce6e094e22632ed7b59d133dc3c9409c9c050437b8c651800,0x145f1acac0c749553307e0adc27cb5d0a0ac7f3639f393997600,-0x8c6ead98339163af24277be8b086390de8d3f3e00ba7126a80,0x27e7ff0a26652728c57b3a14cf9dddd3663a6f8875dc2c280,-0x6db38557f288d65dd82094575fc06b91b1d20e0bcfcb800,0xa0d230f30491ebc64800084436b40b67f157d97719200,-0x67804e3149cc4ff02c0b384fbddc4f4aff5f9b70d40,0x14cd403cb92d785f0dca19138f552007c6cf8a840,-0x9af16aa32efb45b7fff638000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 22 74 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 74 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 51 indices rho q20 m20 20 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 51 indices rho q20 m20 20 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r21 : List ℤ := raw_ints% [-0xa8e35e7c59ac259f62c40dcc5556ac488407445c00000,-0xe38f6f729421807330f3ecc361110dbe43a006e8c0000,-0x90f68b2ce7fd92bd0144f9471b216380b2a5889cc0000,-0x3a13dfd8741bbe67943caeba160aa63046a0f165c5000,-0x106b8b3d1620e8d3f00a8ec2fe112da29c53d69990c00,-0x37bfe40e7372c8d675209adf3e744d33da5f35cf6b00,-0x937fc6121cf9c63a3d69778dae2f900b291ac5ce840,-0x137a0765aa7f24fecafb6515563bdbc7004dfeb06c0,-0x2166af0d740c654ed194a83ab8d93e170c3e8c4050,-0x2f005a302ed0e1c8ccc988518c5a507df9ceb40d0,-0x36a28049be1ac459aa65f9c60755dfd9d817d04c,-0x34a24742038010a767c3a67a1c5e6ca27f4e194,-0x2a088ad3bb1fd2fcb82017002f0814cbf165eb,-0x1bbf389eb2d558b318e913f9195999b840594,-0xf0bb9a825f0d8806ea9c3f38db8f7a6ff0c,-0x6a1f47182369f03f2320b594a580ee4508,-0x256ea30cba0a5c3209093f1c9a3f627b2,-0xa507c6e758d8d6c9aa88708d42b5338,-0x223b7b5fb40e3cda466d1a0c2e3ab0,-0x5075318fab1e8ac7eb07ede20c24,-0x776a20dbb13c65a0e716ba13cb,-0x542fa02b477c0c0ac21a51e4]
def m21 : List ℤ := raw_ints% [0x0,-0x2cc9f7e9ac1557f320bed63ee0d325384317103f60e7c23c8b7c1c000,0x495d84866322bedab04e27f0e960a9f61fe25d3255614fe684e4f45000,-0x3a030ac75cb0bc8c4bea7bb4dc66efa0980afc81b0f861efd8a8e8d9000,0x1d7dd346a02d09cdff3aa6ac7cf1ca733ffc822abb8bc04782684a1ae400,-0xad4b089a6fe9cd27851af2626a57ac711c1680206d4afad286bda54ab400,0x30fa703459970bb1dfc66bd6315a800b0b97d9f96d815c99db55d29a88000,-0xb1501f6ab51cf9ae0762062bce0952ab1b2e83ad67df9a958f12bbfb3e000,0x20fce8d2eae62c7f6377c012740cc694a0762f287c13b760e7da7d9d9a9100,-0x524b2680030da2d7fbc534b31d5c504a6f27474343a41bf43a3ec7d2420500,0xae7d263f6f2b3e891461369ef2332e85082a99186c6aca980f431f0390c400,-0x13dd12c0d13264b6e01118bba858a8e57442cd1f203b56bd062fb923f2eec00,0x1f553a860209836a674b4ddf7b2f46c429124d6e87a2889097bdb9fc6f26600,-0x2b12005e4466a726d2e1709ec4ce7ee76f0a71506de10611898f8987867b600,0x33d62731d2ac27a1345f94b6efde766ded2c811ab7086fb5b3b32ac98b81c00,-0x36d0513c9d52a245a89e072838dc3ee059e00c1857b18d093f4c919b7879400,0x330d082afd3489edf96ef5c3293bc7814261ebf2b43172ddf79a3d6be2a8940,-0x29f12bcb685c78a029c7197afd58bd56ec48429ff08c77c93ceee0e9f038a40,0x1e6b45dc7b2b562e503bf817e954c729cdb4521476fed9a88d710ff9063d500,-0x1379918214b8fc2e858dbe44e794bfd665e91a043a010562bde85279782d700,0xaff6955d9ab729ee146cf3aa7b4fba526f47a683ffed6d3c3ff0e2133f7980,-0x57844ef1029906c176fb9e7479923740e3c85c4a795a48364c7b556245f580,0x263fbd6138e320a416cdb80bcb8843d048be4b808280e35345cfa0be73b300,-0xea500b4c39d720b98e9338f0d47bdcd505bcbcf2826ae5a46b837eba74900,0x4e48a17d869258b9740702db248d519edd711178d0b4fb9b1a6c653ad0dc0,-0x16b611fc1d6b08f653e4b3733ce885bfaf6dcf879fda6dd1ff1c6937c3ac0,0x5afee0b41e752bfc5c6d1fc0921b930cac3041c556418099eaef97302600,-0x1386b96e4a9b1886b93e508000317741f3aae0ce8281d457cf95bba4c200,0x38f2887eb35a6439b6d59cf2336e7490badf2a66e8467732d4e7ed40700,-0x8b993e8e1fe32d5d8b09e70b396d225acd2920e3e9f6bc3096a7d6f700,0x11bfd8b993281594d7254790e8b8d33bca1d98b9e4a86025470862b200,-0x1d8153e77451a0640138ba4076c6b0efd8ed80552fd04d4a89e347600,0x275379a965386ea17296f46944d98fa97426ebee8be935d85601e4c0,-0x290e25c5603e0a857a9bec2defa4bfc01359fa023f76ef7907ddfc0,0x209a333cebeb06e680e8fbed1e43d49da83e198c969e544aaf6100,-0x12f95b8ee8a6b9ddb0fcd681bcaa1494e1339c7950795b8267b00,0x7b636ebb50d0ea306df5e98a8975947711d12c6e71ea007fd80,-0x20d913b5c4825276beda2d3ada558d3c497c9218ade1137180,0x53ea9afaa3addf37dec5165b73bd6fc2d3cad845f6708f00,-0x714442ac30813264f94e4ad52d15482a65e11d244e3d00,0x4265a8079cc07c7f57902f069a4dca6358562cf32b40,-0xc00be193efc36a52c83b4ebfc225e1cbefbabce40,0x4f2f5e10a65f4f7cbba9540000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 22 76 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 76 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 51 indices rho q21 m21 21 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 51 indices rho q21 m21 21 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r22 : List ℤ := raw_ints% [0x1dd3588e4e7a0c470a89e6bd751952bbc2d06476c800000,0x282a59090edd342bdc3c0b21d78d8eecb39900204680000,0x19925ff202752a3e2ab8b5296ea0874ccab26cc95880000,0xa3d140cffa5fceab54d718140c7d81e75fe79b04c76000,0x2e48bec751fb2cc856af2eee2b5cbacf80c4f90da96800,0x9d07737b0a6d21484eddf45d97dc7316dc397724eb200,0x19f213542bb46244b72368b64ebbd4fa16bb65f652180,0x36c4eb66e83a89309b6cc7f8196e3f6b614d562c6100,0x5dd685090812534212ff2ca7efdd0d17e1df053b8c0,0x83e9e6be0ef244df2af3011666d1bcb31146a927b0,0x992b59bc51e2857f93b3ecd5fe65ba6c9f9405898,0x93623b625c28fbf63a85b266e747d74ad35a7698,0x758c17832ede983625264dbff4e7f4bb8f7efa0,0x4d7c0e3dfeb91127ef877abfacf71bc2093601,0x29f35a6b05035dfaa5ba9a9f6a15e1fd5f6f0,0x1276208c0f1246607c30390d793483bbd99c,0x67fe4b50138c8f3cb1e363650a8a626740,0x1c987be54c8513b521cde7779a65ef7a6,0x5eafd8c76f65e2403508e2c3753d838,0xddf9c26ad23eae9b490c76d22e9c4,0x1488242adfd532c628ca96e45f20,0xe6d96c91d69d18433811e1db1]
def m22 : List ℤ := raw_ints% [0x0,0x512e115787e6af68ab59e451f77eb375f999cd72dfa4100dbcd0f2c000,-0x840506c35e2f88dfa9703dc3312246b3073c41a9388514d1d0defad1000,0x679d200ed9969cad6b8db508ebd5739238ee15ac85651e2e3c063ea25000,-0x34444e65820882c312930a4de499da2a0a8b1e0e3e539927d363963729400,0x130a7857c61f3ad4c5d11056c3fb6e3c2f5b6e7d0e19ddf920b7edb69f2400,-0x5562d2948711e7eca0b90519bd0437e357192e20a71d5b323e2231d8723000,0x1326e408348c851a93b8bf708f34a1b5cb7aad17efe144d43ad4aaf80c2d000,-0x387e462c6a053b9c1e38aa5a503c4438edcef44fbdc846e8607fa7f37cabd00,0x8b99d3b8e81815e02f2ad265a1d8751e5ab1600c68598fd17f99c680416a100,-0x1251526b29a7e9eae28a09cce58ef4eb4d3f875b05a8a6aa58219c76c2c22000,0x21054bb8d024f4a7b2c58246fd2ed5800bbfca2e8cf9760d31c71b01384d1800,-0x3386ba1c9c45af86b5b12a751ae47fb58204db647fb31db75bb98cf6acf51200,0x4607970b968c2bf0bf3655a94fbb1d362e1d70213bb37ddd467afa193b341200,-0x5349679aacaf00bb2d53640ac4642ef027f1169e04e2401945d4dfae6aa05000,0x56fa36c510137508a145620db0587e9d55a20650633918e8c364019642efb800,-0x4ff32914385b4a8d4f74e016aa38f7c086a034636ac9b107b2d5c29dffeff840,0x40c854b2edd89de0893cf064b358d5d85c012c04d1564866334b790f18066540,-0x2e4dcf462444ae916297a00d46f395ca05838dce6352175eda28a7e8b9887000,0x1d30f723b5587d8c87ef9dc325eb80da32ae603cc9f28337d57521a95cddd600,-0x1037c7578b406ce3a43f3534267cf3e06e2851106eeb1960d89daec144974080,0x7ed7fe3e76f4fdabdc51e27568a833c2ce74eb37cb810ae2a564aca82ea9880,-0x366d360dbfdeb208793be314773bcd4c72f9890b7dcac96dbe3917f62302400,0x146f350ed632fdc5c284d20a6bca97b775c219b4e5a9b6ab89cb5d6dc5de600,-0x6af95b1e425b42799d831b6a92dc6c9b2866b3c276ec5532b1bd388b8c85c0,0x1e591c0139bdff7e4941e811bd353f1dfc48a194b4355d083b492adfc902c0,-0x76b5ac3ca423dced9807fc96e4ca8555a1c988011e98a6169da902c424000,0x18d2dd22682823eff85f6acb01d932ee837d4aa7e7afb0cfa7ef94e985400,-0x466806c40967191ba31ef5042e1ff3ed7c1b13d2f327e2dc8664179b0100,0xa7753e0e463804b76b14c18f4d0cb1f46608e885b3cf6afbcb68da25900,-0x149ab3bad50b47f16aef6a102fa390a532d83d1b42337b43feccdd29800,0x210bf6db3517fc00a15844314ec142b62d44926abbff21490f5462e400,-0x2a5a7c65c458b9b9555cd583a3fddc89a815318cd498259a9c74ff3c0,0x2a59c43a2f43ae04e8f8b9f322eb47c18da4766e2ec8cd675d163ac0,-0x201167009c13311c8b72720b1ceeabf77749a83b88985d293168000,0x11b41f292fb54d8a850335416b47b7498a9f23413ed08173942e00,-0x6c8e100d12051957b0b2bae3f7d52c9e84e23dab8ccc51db5080,0x1b0f9f4345c9b60d139bc67ae69dc308124219e852d812ad080,-0x40380a280c83c19a98cf7e1ae8e595bbab9774a4bae0a6400,0x4fc741caf4c19bcab76775aaf006f8c17c412621602ee00,-0x2a961d7eec455dcea222f9a5baa7b226d5a60da839940,0x6ec81fc5422b457fa33ddf604eaeb7f4b522160440,-0x2875680de2cb1d24dedb7e00000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 22 78 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 78 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 51 indices rho q22 m22 22 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 51 indices rho q22 m22 22 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r23 : List ℤ := raw_ints% [-0x51c92252ffabbbc284a3caef05d7195560dd52c4a2200000,-0x6e15784fbee66d9a8e7392231120db8b3081cd9163ba0000,-0x460c625db462439fee1d771bc7563c25d70642addd750000,-0x1c07b4781e670d41757e842900e8185cbc499722ecae1800,-0x7ea1dcd63da1633a6fa2ccac11bb1d2cce7295935b49e00,-0x1ad562c4a487399719ff8b870fb52825279a382ae068b80,-0x46e2f3e58bb8ceca649f3aaf14bd332b64b238153ef820,-0x95848bbf219e24a9a4fdc2878715df971c9d7b97f2e50,-0xfff46105c0fd8936d802e188129eb0dad578c2cb2fe0,-0x1677a275c66054ee78867023bb2a4aa87ae41570d140,-0x1a0fb25cbbc4e9c8a8ee7bf8c1a735f2039f8066dda,-0x190cacf7399275fc019a8f77d3136ca7e29c9a1859,-0x13f468cbed30d69da1fb127a1e07a9b78aee4ac4d,-0xd22fd969508064397048df1fdf977d2a482d683,-0x71a2a80f854eaa64a7c9fb9183f4230fcf4518,-0x31ee42470b6fa8a21c5fe2555c8bfdbb8ffea,-0x118c8205c52f40e8445f3590c04c55c3f2e6,-0x4d104fbf6ea488caa586067108a562afe6,-0xfea62a0ce6a903c6139048365ddd8856,-0x2539c5ef96904bebd784cf38c24c8fd,-0x36f38603ac5daad4b1c174c693f85,-0x268168eddee09530517affcd547]
def m23 : List ℤ := raw_ints% [0x0,-0x93237f6ea6521dedb692edd49095a545d466c46035595d18e63ab7fc000,0xed9d47bdbd17223f2467f5573acb80c51ca4aa4f328970bc4a94269ad000,-0xb922d1645cb87f44147ae6dc74fe95567476ae748cebe7ac3a693b0861000,0x5cafa5955c2f376aa29162ee3af244d88acb9d8d017dfb66bb743b18d10400,-0x21804a7e4b4738f01a5b94987a09f33b9ee9fc223efce551efd698971e15400,0x950168c30d90458456be88d4a139d8e015c2352aa4ec870df4136561c9d8000,-0x21233e9f7a7777712a6e8c08a06165b1edb9df78ee6c63db1309ac6b29e3e000,0x60e1b4d4b6609c9d2aeac7f3f9db53077c715a2cbed01957c587fa3b1ed1f900,-0xed30ee77cea082fd0106b4916a7c778c6774d6039140be5e2b4aedd355948d00,0x1ed27d1abaec8ed18c681bc91b981a79fc53d0e9c9ff8db1bfe2d07b58a60c400,-0x3700327a38c33ae41e3c705a101b649614f340c4b903168c82c1d15ab775eac00,0x54ea9470e3850ab93bd201b4db4fac4e5d35011ef876535e74d78cc8139e9de00,-0x72213f282d5e4544e7456a36a47c35ae04a130e5c90db67f3d870a1b9bd914e00,0x86279aa2f35539678d74a3d94e5399247776c35b8bedab401151f05ca4863ec00,-0x8a627108727db5879d37deaa967c929cb8c16cea0c4309e0fc49e8d8d5c7da400,0x7d9082471737916b23f80715bdacfd71629d12dbcf1c88f3b8c3b30a19d992b40,-0x645c9c124d553ac9077bb63d4c5c36d35818b4b304580e864edd86dcd070a5440,0x46b4b51028f98026b6e1c6db567764d49f02f17335952efa17ab1e61527368500,-0x2be621fdc3d6e27bbc951d010e44643c5db40d5530e954a1bc62c52bead1fb700,0x17ff4be92b495b85c72363e9724f351f0c806b5f000a9061ec185ab5dbd809f80,-0xb87cc747fadb396f1742c23b4310a69b37fda76db3217771f1d66e2fbf5d4380,0x4db9992ed11c7bdbcccdd82c51a4e0e67171879a1f7df6dbb59ef48a6087c700,-0x1c9e23666757f0909bedf5742e783a0bc454184331a78886a64dc248df8d2d00,0x92b87e7726cb11a66c99e910b6673c121fbba978032f184657349d68f0a55c0,-0x28b4301932bcfcd7bc45e9a04eefacc780159b40deb5ddfa2f1bbcd9903c2c0,0x9b70563eea7dc55abbeecdd196022c8043ce9c74e30b95b950a2088fa4b600,-0x1fac824256335f7609bcb508391f018ab7c53ad86c679c512c84f11f227200,0x575b8f94fc1897aabd7a4aad1f3048e76175de427364920aaa4b7f3857b00,-0xc9920db19cd2d65b2677ff1da7c99ca9b9e1a84c0fa4d55d237ce6775b00,0x17ff30b30528fbc7875d8f77be7778641fc330413f49fcb2962ee325ba00,-0x2520643dad81db348e7208acf02e8e8ed6e13a39d53cc3acea722dcde00,0x2dbda7460c990cfe7288fe99a4c46e90b990756293e8e6b980a2f066c0,-0x2bcb51af5775fbb1673bb25482e260948b73b5ab9899a77a94c2e09c0,0x1f9ba4fba7e4b5c6b10f4092e0da782c765d917cf65786d2f1e68100,-0x108bb1dbc376f85fd722736ca3ad4e21b65df231613c88539638b00,0x5f9f06286bae60691c5c7e445592ebba8f17801dd8657ea214b80,-0x164f954545eb4a52e082ce6eb799abb9818d0ec4694048af8780,0x3129accee3bd44e00bd9d9637b425bac8b2fdfaa1961f7c300,-0x38314f9f48392ad0edb1c9682573bec93450c89aaa0e0100,0x1b4f1efcd5761374d15ab6a7d52a6d3816e43b2f53d740,-0x3fe2e3df68dff08cf150e40b6c8e494e8240454ca40,0x14aac2dcbd4898d0c18905000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 22 80 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 80 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 51 indices rho q23 m23 23 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 51 indices rho q23 m23 23 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r24 : List ℤ := raw_ints% [0xda44cb48d9b6833a6efb0f7976834601a505a4a685ce00000,0x125a765df059834f96bf9e86a238069141282f26f8f8d60000,0xbac37f510ccab2f27840367c9b42c6373e242b71902010000,0x4ab1997fb32d41b7943ae429df3d7a50ffe2e53700e702800,0x1513fd63d43e369e4e80050b179db49a622bfb24753e4fa00,0x476b3012be767267a4edc7745f5504d32bd4267afaf19280,0xbc8a3e661475fe8b37bd188fe46e079f352cfa32a148960,0x18d635f3adfbf5254ab19a7b1a08055b861353133f8a190,0x2a7bd1352f5bf6422880b290fc41f25eb38b0490ac29d0,0x3b9d90ca686d3dc63327da037d81c539c1f75dae0f620,0x451683511fd341e9de1a02c71c49fc59a7b15a2501e6,0x4256cee752ec41d788aaaf3457eab2904bd267b1a2d,0x34c9f7d94d9a5e4237b8d7f4dab826ebb5106bc81a,0x22b60b1a92641e6aba268722cc910e333718505f8,0x12bdf395dfd147e55c2e0378033aa62ad092aa1c,0x8393906fabbf045835b51f5bc6d5c2ce7f4a3e,0x2e2c5553c0b365df5afcf850a5447fda22084,0xca6bdcc3e26c86c437b54bf6bfd396fffc4,0x29ba30d00e00ccacf547c5866ad11eae3e,0x6165d3df3574085f5a43aab4ce2c8f4d,0x8f72d88eaf1caebabe9a68d7502ff2,0x64437ce80f9625b1fc917e8dd45c]
def m24 : List ℤ := raw_ints% [0x0,0x10ab056f88d74d63edaea4f11460f3b8e90fa43ee60b1f8bd214a6d78c000,-0x1abc05e2042e3a3db8442561fa19c427e5b177e7564c38395472c85f899000,0x14aed9a581e6b707ebe22af1d492147c7606d68e5b4485a53a2d9350ae0d000,-0xa47580a33da7c6b6d6d64bbfbaeecdec8b72ccf1f00f1724afa6c7642463400,0x3afd2db3837b6c483d3e60a884f12b59b6bc68d31a814d00fbcb9c44c4694400,-0x10447d74bfc0b283f372816be278992a816b91e39d021b19706ce47a4bb71b000,0x39675c8956a792d1669b1c72623d170923a590fbf4dd76546684be1efe57b5000,-0xa65f1e81d2be25fb1e3b75b255df190a00f53fd7cba1b6f2e7e1eba0f3d638500,0x193a18dbe3c0e8ae20735ac2cc2ec612e517f015e425e5d70c0d43b5718a160900,-0x33f4224419d1542d8bc4c798f69e85995bf38f373cd64c1c6761c7cfee4c324000,0x5bca000dbe51bb7e97a7fd45d08571584eb363f52f1011d304a41437c5e9447800,-0x8c3d85ad9f15f93b811ded2de0e874ca65a9571e5eb82de6161b69286aee602a00,0xba6ddf1d9513c4220a2ce8e157bdb7ceb977a1f6e45596fec24666753a2209ca00,-0xd8a00b003916f071963df44f9defe36999e869d6ee5d721922fb9a1c6bdc9e8000,0xdcc1d4f799785dfce63a3b7c1a3b44eb5287a184903c060fc016b7b37af78aa800,-0xc5c1d1808542b24054e84d61de799efd4692ede96855bf0dc947632a1cf5cb9240,0x9bf0f2c9d5f8efeaa33ab4a0c6e0fdb1e14977409a62e5646734e043e22f918740,-0x6c4d610d1c4345d857c83642d57200014fb1166f8cbfb03fddbc760cd1419b0800,0x423af4969b112d09496243b8fc7f1fd7fc7b303cbf6927fcadd47a3c8d6d94fe00,-0x23a08d9a187cbf3dd29bc47e3431922367fbfda975d135132bd1d9d0984d78ee80,0x10d40e26b5ad4201ef03adfef65d10db79b4468df257643656d5548491f4410e80,-0x6f63a954f1c500f599f288470ed72dbb2375d67270c98587fdc68d16eb6573000,0x2838f76491ca24be11a93e6111688076734a23c677790b4a6e2caa0dce85de200,-0xc9f7d260938027d37f38bacbe341dd7273ed833a9285363a17bd05542c5afdc0,0x36cafa8f6e07061bc87e7db30061e786450a27cb0576b2bb00eedfcca0e27ac0,-0xcc45c0f5c4effdbee183403bb6fe21e3ebfedbb1e18cdaacf511094c2738000,0x288f2f24b3b801e86e13a291f6474ec2f26a641f17707849b16ca6901abf400,-0x6cc4efc3fc96fe85333555ad407155a5c4eb1c5cce57ac43cf1732f6f5a500,0xf372da6abdcfe35aed4ba4aed7fde45399a7615dbf851e8bf9d90798bad00,-0x1c097bfdff634c06d10b0043eff635a0bf5378adc3984de445e9fbd407000,0x29d5603dfc55a6ceaaae68c57cc606e233c3e15d161bb68dd5394c04dc00,-0x31881bb172f6c8225544025d47338471686c297cc45df8a170b17114dc0,0x2d64c4f2b1648859ce57e8e9e49419f8c344c39c0b726994e55b381cc0,-0x1f375e0ce8bced2fb58ebd3c7dbf3e423959089af43f691e27be56800,0xf7cdcd0834221005f392a3ad0a7f24c25e3a4233f6fdda7421be600,-0x5452f31ffdce221897a1cbb2df926b0a9a953da7f8a78456484680,0x1268537df0e87dcb62e5911aa66c6517b6d43b33c9e76b397ae80,-0x25a5ffa8087a9dd455ac6e70680ce547e25cd60efe93b4c7000,0x27946c85f3cd18071423f0f93317968338d92e2dce7b92a00,-0x11823ae854379adbc7a4d2e5f3468d4f95bba52db636540,0x24d504569d3a95371417f1dd945a21170fb7c649a040,-0xa8e0202c6a0794d129e138000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 22 82 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 82 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 51 indices rho q24 m24 24 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 51 indices rho q24 m24 24 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r25 : List ℤ := raw_ints% [-0x2385853dba79667dd26398b83b9626c7d8b63d2b7f05b800000,-0x2fc4e963a1672e9797a2f87d3ed90505956c2ddf696cb780000,-0x1e5df238c15af2d2d83e299bb99cf353d6423b34180ac560000,-0xc2387160cbef355110484d9546af0e037e338247b64d61a000,-0x36c7300563e6adb028a93f312944dfa8bb89dcb96552d5a000,-0xb97ef360e90043b79511b1bbc296d440ae88d6606c58b2800,-0x1e9633cf787feac4993a3f29d24029c65bd6f43825123a900,-0x406ca3aee59cb8fd70bc581e9d8611794ecbb3fb17ed4160,-0x6e1e4cc98d3ee73fc04833f9b8f007313fec933f80b96f0,-0x9a670572cd9ac9e9afbb92e3317e24c179436e28c4ee30,-0xb2c87ff2525d475214f4e67d9ce6f433fcc0fbda056f8,-0xab82eba83ab0b4d38d827eafc74746b75ac1270a2d76,-0x8857bb42dc820b1c3ce5f9c4a20f873f23e75cfcfdf,-0x598ddf63dec92deac8c3f3744af4a299bab60cf2ba,-0x304c0cd9e54b0edc774dcf898b88ffb7b29ab0dc4,-0x152a1285382fbe1fb9c74e5b8c652cd576edd7bc,-0x76aa9287f7aa9ece9081e90f133c9dc4f9ddfa,-0x2076e493de9f0aff247e467dc97ee2e14e5a4,-0x6ae55c44fcc9e29e429fa5f4a0311cd6bcc,-0xf90cc8f5b45cb0bb1d434ee0692379c8e,-0x16e0e58247e68c7ec6007a44a35781af,-0xff4730641ab073339f0e75c2c6e52]
def m25 : List ℤ := raw_ints% [0x0,-0x1e35f9da28063c451ecc8af4f4efb9bf266c59b200f4292d6cc56e66adc000,0x3022e6fc51a85971dbfb294a0013f3070eda9664f02ac932e9100b2d2955000,-0x24fc16e2d6c581df66b10a77629cffd3b2be8d6184551e26b63505e177229000,0x123fa4c798a621af7df24ec445085922fe9fb95bcfaa2842c7a7f44bd98102400,-0x67f29a8ec953246b32086d04f2c0a488dc06ad0fe2a4a14181767e87b2f84f400,0x1c71708076673164e6106132d0bf78c5c53ef0a0803e8c28b56315945acf3e8000,-0x638dc1ec34692c630e97bf05807c9caafc550897a969b35f41dcf29ee053a7e000,0x11e164ca1026a33e4ffca728659908abccf8488b587b15c73c88c1427a97774a100,-0x2afea24ab138c5fc05e6c80fbd64ed6ec850a5a4095ea61f1f0fc79d77ee6ab5500,0x57b913afbafcf035de22cd3fc7a9ab85f1245883726a9de251e423bc5dadb03c400,-0x9979aacef4468f0f27fccef7c72e505d7fd664dd3afc46e45760d1c5ed2437b6c00,0xe81757a635e912ec9b2a6b5b8ceffe4530842010205869cec5f63845a9d0a249600,-0x13137b345103a0fd0a326ad54d3441308f482a04257e9e85e288034cb7559e6d2600,0x15ea5291151f26abdd013bb61a71115c10da358d58b16a86d4600d7f863e5c843c00,-0x16113dfd8180bc48fd5ae31cf82c9cec4da9f11d570e9513617d3776342bbc9e3400,0x13850fbf19188f0f21fc3ce23ba984ff70fd9030571672d160faee641b8a6866dd40,-0xf3017201c1a3cbf428f769158be59865c0a0add0126814ece2ce7e3a28144456e40,0xa6656f5008886a865e9d3d5beaa12cb63b292a81ab0568199ac73b95531e6977500,-0x643d55b1e15de75fed443ba9f6bd1269fee69d61743a06630c139bf2c23fc975700,0x35115c437067c63adcf1da6bc9a43560ee31a06f5d6ed51b661fecabea437125580,-0x18a4d6c998f7e95b3b8df9dc0dbde78e222bf27467da0f5f3f361aae5439fdfe180,0xa030a3526e4e994a01332a2086b2fe6a4316a7d57e8e74d1999ba059538738fb00,-0x38bbc1e1d72fe8d39e154238f697bef1e94a61d5d09d103b9c2237ff6e11dbb100,0x1170383bb4376c244519132402a6443013c9b910c1fee31b84964e637f5c743dc0,-0x4a05f81ee1706461e9bfce336593a5a4df86d9d98f36344a824182e30906c6ac0,0x10d67e0a8991053a4970231a992c1e51cc580c0d463e08de1b0f6d44ab83f4600,-0x341eab0c258a28f12ac57c19877d224730ac44617b9984e367580324bd712200,0x87e44e20709da260abf6d5c86fae60042c7074cbf3bc730cff0586d1c82cf00,-0x126fdf5c8833692b1593b07efa9c40ea0114b12e06e2b4f3c2213a6bd481f00,0x20dbe61833f8a9d2a7f19165062b47c12d5442c9ac1cf5dc9685eb39250200,-0x2f45ba0960d3ee96e314ab2befc98cd25293c9ce3b65831af628517028600,0x35c67f287e73d5e3e76e6774ba47a29531309ba46ca65544517a06aab8c0,-0x2f28593071b6fde49d05af6bd8ac63b1d342f4ec6a4c33aca2b792043c0,0x1ee3317f74141d0728d93cad89cb06bdf2c3c91f969dea67e101136100,-0xe84d3ccc34bcb2702254fd7594988717842886fbe38b696e3efcdb00,0x4a70a11afc82f96d8b183e45142a73b5a6ef086d433644ffa5de980,-0xf3262a983084bdc65fabb218dbe9064a7a0d95ca9cf8f4288ad80,0x1cd6afff1efaeb9c64e7d5159213d884567660e452bb5b941700,-0x1be0b189669f31f1d39ab39b059da0b39a7ba9ef99bc706500,0xb3918bc7dc6d0327f3f9dbe5b0defd5e41030b0c7a5c340,-0x153a956f25304ea45d708e60649800dee25ffddfa0640,0x5639de05853a6fba6a1c940000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 22 84 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 84 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 51 indices rho q25 m25 25 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 51 indices rho q25 m25 25 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r26 : List ℤ := raw_ints% [0x5a70ba75b58d2ed42bd2ada706d0695fd9c454b418e8e2400000,0x7993083769f83a9b9979a91fe6c79bc9afd1b3681f4d2d540000,0x4d405b85dc0168cfb491aca4704f403ee94d121d54a7d0720000,0x1edd9ee1142e1f27ce95d173b13e0fd059bff3f3efbaf304b000,0x8b37475ec2734b685715ae5cbf3a87ff6224337288fa6fa7c00,0x1d72c6a3a7588ea3c72aed164f2902a5a45f433a32b3c2c0f00,0x4da5b0a7154bfafc457c6c6a0cf94542d1832cb5ad51cf4a40,0xa371c3d140358c43c9933fb9b75b39649f71b442169ab59a0,0x1172e3e889338aa312585f4a3d097d5e9f326474ef8c91260,0x1872acad8b8919d51dc2ddacd866e0c24a62cbb2ca80dd10,0x1c493b8aacc9c24f0e11afa1f39ec0dfcecebf574823044,0x1b1cc9de66efacdf899ccf12de5cbbe212f72e9c0509da,0x15887c6edd2cf3eaf8f41d4ce8158a0c56df728d05004,0xe2129bcc598542004382771ad07772f01fc70cc6437,0x79ca53a2260fce28c786353e5635ae5a0d26910fe8,0x354ea620c2ddbb964fce62fbcbefc2e6230351e50,0x12a8172678585d4a607d361fe863979b9614d528,0x518ce9e40f594e0c272f33896d8b73809131f2,0x10c1cbc4f43dec8741fbca1a40e95155a6294,0x26f9cdcb7ed3493f5d420eabb4a462e894e,0x392e8406116b84a70a8590c1ab66b7f74,0x27cbd5caa805bf3ab1d858ee74be2af]
def m26 : List ℤ := raw_ints% [0x0,0x36c1d4db688b4d3d47d2bbdbfbf280aa75a46292a1ba8aa25525d81a1aec000,-0x56aff439fda51de9db369c84dafd579a985bcf75d1deaa6f866d1441daea1000,0x4228e1346aabc7663e495bf2fea22fa1ca8d9dcf140931ff75082f015c9f35000,-0x206a9ea2f3f1edc9b9d3df6e3b42a925068411d98e8972e9ff4d867a048eced400,0xb74f2f9f807321014fd243883136e049cdd6b459ea8bed5433db4cce7e001c6400,-0x31c741b27f0e28dc0ff2763190bf3f6d2f47fb8b388ae333ed2373b785f3b893000,0xacd916f3dcccedfea83fda46950164b78f97d69203f87e14db2c60fbafb3f83d000,-0x1ec97de28f4d0e98150abeadaa5df90cf340aa9b70b229d5263fffc93f76e0aa8d00,0x4962f402a8a639435e2b05e1aeab164b743f18c1cd56f9e49ca87b390bc24318b100,-0x945e6822c94b992799da6c8011e2a3ece0cc834b8e6f805b70c0f74b813a0bd46000,0x10118d4ec3f732466e9296419c5f340d6aa8725e371fa3a6ee62b9730dc43c69bd800,-0x180e318c84ffc872e6d8c75832591a0665a3075fd85856e47382bb96932cf1a238200,0x1f4ce8da97dab5404bf5ec7a806109a5a5160cf13bee1e2c4a16e2a5876479e5ac200,-0x238f06fe6c4936809eed7b4dfab7f06ac5b73ccbc18a8788be825374a217cf60a3000,0x23627f3cb1534c34f58dd19c5531719ca714ec1da247ab5019cc8f7e79e8a83651800,-0x1ee946455a63d2ac7f446f04f5d5930fadef9fa71b7656a4ad49173e5f77317f7fc40,0x17bc3f55980f92b032881e201c0f3d2a365ca638b74833fcb7e674b0cb9ddcee5b940,-0x1006bc05861f914801383db4fad110004c5f1848f166c2d39657e6b3b46820558a000,0x983031359714563776ff3c62c970db32781fb0f839d93204799507e7e48d7ab4a600,-0x4f4d93121390dc156ba9595d286a33866dce60258c00a4389a1d33bc8d0271316c80,0x2435c311200334f8db16d6afea21f5613e1617ff1926c7c343fffd57e110d0ca1480,-0xe728f38557a9bd1c0166533ef3d49a1015b6ebb3f10e3c66652c50e71fea93e9c00,0x504cf98bbf8cbb6a0f75fe6070ac47f3db07bfeb80295d311741b9c194d190cbe00,-0x182ce6fd466c7f680ab7043a7fc5f7065750d31231f50c75aecd9e7d915b23095c0,0x645afbaf55537a807b633623b9dfbadfb3ce61d35682e6498232e51151278992c0,-0x1648ce5ff061939dad2fee699bdb0c65abcc34b18c27845c32f3ada4ca69f14000,0x4334a534fc936b09610947ddb82e2b9e4e6bcc30676a2eaf9fa95d92c77051400,-0xaa583727718e06285d94b3cae9b036acd918e27ea2c1ab0b22e620055edda900,0x1669765402aafda1a48610ad25c6afc478eb77a73f7f3bdf6d99081ec6ece100,-0x26a04aad66981ba44e1fecbc9fa110dc5d2bceab272de2fef79257701120800,0x35910bc7a840d697c17046188eeda30474627f161977d196c3af226d5d9400,-0x3a87301b0325cc891e134104f54b27863591e211fd2f599aa1e926b1537c0,0x3118908f644da4de17da235ce1094aebf697f6fb343f5272211f9ba9cec0,-0x1e9de6e9acb599531f1c438488dd31a3a4ce02f1f0cdd5a27c95e0bd000,0xda125d37f18b8b0e81f3e99ed6e0771c5c02c21548ec2dd824bde9e00,-0x41c75929791ff1f7eecc8999dd59625199e02834c9790709cb7bcc80,0xc8dacef9417d21e53cedd7d517f1eb673b5712481a6bca9749dc80,-0x16186b040a1fcd91e5290cbea2d51871e7d1e75ff0b5410bfdc00,0x13a272979d8d3678b06be706b06603794b6cd59c3a4cd3d4600,-0x731404e149ce1397e2524d1c641bfdd17a33eceeb4e27140,0xc3b79d634e2c2f1d69df6fa39f806fb43251b86ef7c40,-0x2c043aa072e3299c42d3fe00000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 22 86 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 86 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 51 indices rho q26 m26 26 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 51 indices rho q26 m26 26 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0x27cbd5caa805bf3ab1d858ee74be2af,-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r27 : List ℤ := raw_ints% [-0xe195cfd1b8b609bf5f7de7b98ce5983341a8f9b937bfbe9e00000,-0x12f20b423ddf3344a2883d146dc73c5eacb56d5daad4a66f460000,-0xc0895b11469b293d9c07a3d3764d30aa68418d86f280129af0000,-0x4ce4e2b896a715921a157992fdf389d6facd24b359dcdeb70e800,-0x15aa87967c38b710f93515fa769923206caa7da9d2fcc2c829200,-0x494aa08ea5ece6b91391bf0855f2e53a640a4f659f60cd49e080,-0xc12506f26984df2d25add2cec1bd8bbfd3339a3de82f659d2e0,-0x1965303e8b947095eca0ab6a9842faa18ebdd849a7c679eb3f0,-0x2b59be8ca1e98a61739fcda404ab77987278524f113389a980,-0x3cb2ccc09cb472e0cfce4b0de8b5ae7648bb0f1f4d09223a0,-0x462d219df6721d20d5b26744a0c97aeca80d8fdfcaeb0d26,-0x43362edbad6422ac316429021937035981114c29e56172b,-0x3555ce629116623fd6abb910ed11a1bac408e383a25f21,-0x22f711504a2c9aa9a7c9d49e55f2467c008bef465b0f9,-0x12d1567d9ba96012ab2cf25592984ae7270773f75810,-0x83a41dea3a598fb6407c70e5fd2af4c30725b156fe,-0x2e04a26189a41c2c994c48c12c67ce1a1d55b41ee,-0xc8e506cc19182f3df071d8a41f87efdd13df5f2,-0x2938f6ae233d16f6e289b9eea8f53d9fa95492,-0x5fbc41c9c198f726c1bc8523d2b7879a4617,-0x8c3867e697603a3b2bfc21af0a511276c9,-0x6168cdf1fb59e5f463964a170339e4c5]
def m27 : List ℤ := raw_ints% [0x0,-0x633f51cdad7c7bff122df47eb8a78934f539f2a9c5221b463a5497af50cbc000,0x9c242166449a3edbf731e6a293e7413c5ba9be0b91e188ffd3a5b4b75cc83d000,-0x76646c9c20332c544d4095fa3e3e8ecf6fa1a20812ea1aef45c0778828ca831000,0x399d9ff9433eb21923946d7eb3eeb6ba434bedb02079ff70bb7e486239b23e04400,-0x1437fdf0c32a7208ff749bebaca703a8c3616919676ef0bb504e5b1871625f5d9400,0x57328680acc07dc5f15798b5349e582fe1c271452181abb4b90093e9c2ed7a8b8000,-0x12c6f7df2052ee737c24c7740d8262be0d694742810eb2735baad85613b2a19bfe000,0x35141a8a013d96a6e3e9c87c718c3cfbbeeb99986b1ff68178a8a32c92c77454c8900,-0x7d7247a893dd18174e854d70c5b3e482175ce287479f7c01477b4f017d675f1d85d00,0xfb5b5ed2504016c1256de3cd0b91194e017a0e4d346cb8a364afcb49574e6fd79c400,-0x1af78e18f1e04fbc09fb2261a793b67b6e434d025e173f13b76ed63bf7d99be1f52c00,0x27f8fa957bd28d93c2bce470a110dc6a0c9a08b3bfc8d8fc5b8a5696075e4461e48e00,-0x33788117f54203a040cee0c2f4c0b93f1ee201133bb98cf31f72d24d68a2e6fc153e00,0x39d4ed8088b31f1545775d63b545c2f25e0eef95f4c9b8a8c9e2326f545983f1550c00,-0x38e1cdf8e2c58ba206043eedf0bd1273a6b67fb4f0b826ff8e3d069677ffaef3b54400,0x3114e252540aa2095ff868a94c8ee0277edb74799567e408e02992a78b781a91a81f40,-0x2532ae5383ee693560a932fdd4218a77a0ca6bb330b5428b5048fd305b031181e35840,0x18c5250239c6ad3bc04daf90145bdfe291ebd3f06b6e3856d926f8e8ce9db9c8caa500,-0xe7c5bd7339fcb6311ce52b61a2a027b68dc47e337e668808cee34087ac6891259b700,0x76e327ea454975ab2e50dbe8d35ce2e88e08534585564836215860d094941423b1b80,-0x356136c1a43ec4e3e8960c61561b2f57d16e2df060f25a9d24a2fb3ac9a6297624f80,0x14eb2739cb1287b9a63f29a179e5914c0ca42149816feed48a01bcf2d3a34630e4f00,-0x720c2468e2346c2a73002bc6087c01bffc9e54f68762bf5a90afb39a218461cdd500,0x21a18fc2b84c0a3f7d4d86b4f9815fc626c8d406015242b4742f5955a7614721c5c0,-0x88867ffded896545e6c9b016718763406b8e419317750b236ca83a6e74df00932c0,0x1d980c5b845d9493b5515f2ac32f20e6bb01542c1853e8dd49c23947d2075abd600,-0x56f326b42556e2ba0d9eca77a5e48ddc1cea873cb960e9a1cfbbbfde1ad284d200,0xd63a9f2d6c5c6bff92a676456558eaab272dddd1a5c9e7f0a3202e525d1670300,-0x1b542d36dd047c14381fe29f3373bbd0578cc11240a0a6c2bd5bfa9a173184300,0x2d89ccbca86d49475fbeff7e12412438ec23adb3e313aefc88efc23fbcf68a00,-0x3cdc9f7b9d6147a5c6a00bf13de5817474646d05749993cba151dbedd536e00,0x3fda82547fda1efc2f5426f022b6b9e3637a511111bb6a3554096cc72f5ac0,-0x333837654813e07fa62b7ba82999d02ad165feb7622025a51c45ffbe50dc0,0x1e6668efe8eff468bbd256f6e79d92cf90e989edf54150f868e4690e0100,-0xccfb03402bfe27f11388a1ac90fd528d020cbf0fdc4120b49eb2266b00,0x3a2d84d35a273f55a41c9d490f4d37e868cce7cf5569a00d2a5d25780,-0xa6010f09915e439bfc0d7e1d6b31d990bd0f9c8e224c18a03196380,0x10ee9fcdf76c6621cb66027192916b4b18af2cbbef04a1fe848b00,-0xdd3f3fa13641973acb368032284fc31b7ddca847dd2d7d86900,0x49bb9bb81eb8287bcb3abaf9df04a4fc947941bf18f94ef40,-0x70beae060cdd64dd3424532b37c0d781b29a5b2e978240,0x1676f57215a9dd38b9e4b5000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 22 88 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 88 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 51 indices rho q27 m27 27 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 51 indices rho q27 m27 27 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x6168cdf1fb59e5f463964a170339e4c5,0x27cbd5caa805bf3ab1d858ee74be2af,-0xff4730641ab073339f0e75c2c6e52,0x64437ce80f9625b1fc917e8dd45c,-0x268168eddee09530517affcd547,0xe6d96c91d69d18433811e1db1,-0x542fa02b477c0c0ac21a51e4,0x1dcb4b58db9f2101009c2ee,-0xa32e5d56b5ba0fcd0d669,0x35d10b037e20a51a1253,-0x110539c037aa27b9f16,0x52228c7d134d59420,-0x1776bad146c1922b,0x64bb379db1c295,-0x191ded39673e8,0x5bd821113f2,-0x12e3132f8d,0x367e48f7,-0x84b59a,0x10084,-0x15f,0x1]
def r28 : List ℤ := raw_ints% [0x2282a718deda6288f37ab2a6356d9e1098f7f4782f0de96f4a00000,0x2e5b4205244b3a090107bd18503b0141c32cd1b238c7ac863620000,0x1d6ecf4ae16e79b5df56a8855dc6829d31de79e7b5bf816e41b0000,0xbbff9ad1a47cd7a30a02466ad090e8591add7703481850d49ef800,0x34f2c24f815ab5aa41dc04078212fe3367b196a41380b31c086e00,0xb306fa46ae922713845243f5c1e6664c60969a79da6f4f6d0c780,0x1d78cda92e2731d00cd91d5b89e119dec5379dd2c5966f7d4bc20,0x3df796e27d06ccbac5de1fe5dea5917a67033446b63c414bfd30,0x69b7d1fe19781e39766e4e7129f1f9b4cf26bf8c7b413824670,0x93ee433fd2b9d1a6ed88076448c4a6225a5b12037d45b22880,0xaae9e7e8fa52e88b3c5fda67302c0ccd7f2e55800c3727d32,0xa392e7ab0a3d5cf99ea41b6196a54c1af3a5d8b85a27bbdf,0x81b349cb7ee3e815739e8a21f1b6cffe12983d01c0f9bde,0x54f4b10d56add7a27434e87da62895eeaf0d732e32157e,0x2dae17fb759401b23773ba9061e6317aea19c767a5f54,0x13f3dd172359360ed2574bdc4bb7749a502aaa656852,0x6f7a58632b684b89e1195e2ae892deca7da715c22c,0x1e6182bf6e5a128b407d78539e876f3a4210ea3b0,0x639e023ad6fc695ed8998060c048689045924ba,0xe707f3570a615e358f30f39f45e649c951f07,0x151df06b8b756364c68e6f63026636655026,0xea537851f3bb25c5e57ce1b8bcff83e6a]
def m28 : List ℤ := raw_ints% [0x0,0xb3e2c444ca71a0be50f34b25aeafa8affc7907d3b54dd16f49b952edc2714c000,-0x1194a9c5463ddc50ddd508d2dc84c4688ab497eff82053375a39c578c582aee9000,0xd3f01f82f37fc6eca2f87e3ab9e9d2a5166276a8e0dd33e1df319a976479d79d000,-0x66757fabfebfee8d66c04058f59d77c034b939bead34c3f891daeca6b6ff0e747400,0x23b508d8c910f986276563dcca12711649c6f7e3ac36f198bc896c445a6ebc9c08400,-0x98e1ef948f3c42e0f94d1d53f33b29963e771f02cd834b3542d568cc0272bfb58b000,0x20ac494b73de6b6d0def75ca9908407123e833aebb135e415690a3da51d7ba30bc5000,-0x5ba044d1f021dc29e54e104406377c6eaa6448ca378407ac14117b777c77955ac1d500,0xd6bf61515c715ae1708af68c1bcd49f7bd0ccf0d12adff181d4cdaa4e03f3505a89900,-0x1aa869df730f546d462b2ed24b2c2a78be601a90097cbd88508b162228661dc5ff08000,0x2d56c8aceb5f6b1a2c95133cc0af48ea45f3d1280132e4a2ce3088e58372ac90beb3800,-0x428da9dcb0007da15da4524a88e37dbc1d82fb85f9912d8298b3ba73d26536e03c91a00,0x54d2322338408105823b38ac92194c82acd33998d7dd0e0a8a07d26988588203e28fa00,-0x5e46302df00fb40dc0684c6a1f786f2b1a463b9e0c37279484ec604fc99de5010b76000,0x5baa98ef0fa90edf5b33c0dcc3c75778ae21c7394fdaa41601ab54ad00f34a37b830800,-0x4e2362c41a58c98255c2185fb0debe9332820345c5efd2e9ba8e770376972491607b640,0x3a756cbadeb0b9a76f7859a82788759fade77bf6a72c4c64ec8baa3b1271e799b877b40,-0x26656557092eab4aa104893c398046c47e714dbaba97eb894c8adca91aabced540f3800,0x1620c0f7f1b1a02416579a18d7dda025b02495bcd0fbe1c8a059e8641e46391b28ece00,-0xb2cab63724809bc941c824c7a9b9464a1810e5dacd7c6c0e55a96ab2c3df68b2213a80,0x4ef239ede55cbd15db03010c4c37d007ba836ce4f5edcb7083e0c25abc9d1047bc2a80,-0x1e637a32e82245d63ca7822327ed27e3926965209176b9825f6266d345fbc0132b6800,0xa285caa92fa7937da5747da0d98f91479af470524194497466330193853a495eb7a00,-0x2ef1baebb1aaaebd7770c50d91ad81259b56460f59a3e9e77c5271172611cbd084dc0,0xba5ced46158d779a63468b4b0a5927db0835b194882661f7082893ab698310254ac0,-0x276ef100b2b003c966e7e6697bfbe9fd17de2900a53f6cca43ee568beff6dfb38000,0x70dd8ae075e8954263816fd3816627279cb2c3d436918742d8f26b7b89f48b3b400,-0x10e471f7d99b803e4040502db4fd2c2f0ae8b05f62a6ac6b946865ee28f958a0d00,0x216cf00f5bc9442e0cf004b334585809fcdf0decb4b01a5a79141a6e55c560f500,-0x35d6fc92b87f7e154007a7764b6377023823d63f44d87f6e807dd11b583516000,0x45548008bb60844fc6278686ac27b8b8b5f63777109cbcaec2daafb26ebf0c00,-0x45d30410eaccac5d547bffc446ec4504d0382b052175d8077bfbe7e0f0031c0,0x358a6800f6e63e355309544b6df7f8c3899e84ca9951f66ab4b98a8099d0c0,-0x1e3bc0c6afc752ca251adfd72251dea9b4b2d46579b8b002b75d45463b800,0xc0e939b24644d6e791d4db28b47902195c96c0fce12034025be320a5600,-0x337f8c66096d40b7eb2359e7364bd60624f9cd3396c9d76ac97acc6280,0x8943df04e2d2fc7e939f2cdcb3641f07267f9af1d65184f88ea5da80,-0xcfa3a070ce25288e78372e1559b90e1f5d471255aac3df9019a800,0x9bcdd6f8fd36aa68c671255df9a69611cbe3071d293c5a104200,-0x2f3b4b58c9dfb849444b1b1dc079d327628ded9bb978ccbd40,0x40ee4b003dd3ae6ac39b738ff0bf5c1d844441bf1a39840,-0xb767ff37afbba9731fba38000000000000000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 22 90 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 90 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 51 indices rho q28 m28 28 727384358899856852873903134310400000 29=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 51 indices rho q28 m28 28 727384358899856852873903134310400000 29 21
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_28
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<29) : intPolyRF (mz e)=rfPoly (C (727384358899856852873903134310400000:ℚ))*rfX^29*(1-rfX)^21*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U7C29
