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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C29
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,29,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x15e464d9c54543532600000,0x2056a5ff8fe9d3ec32e0000,0x169689e415c4cce7e930000,0x9ed3249fc1adf69e6d4800,0x3149c1722a31cc2b93ca00,0xb7dc9286fe02d2f5cce80,0x217303ab5556f33bd6b60,0x4de365d22df9b6062d30,0x938e246273defd786c0,0xe60b2bf7cddba154a0,0x1295c045a3f0fe093e,0x1400e05f87e3c688f,0x11f43b31499c7169,0xd6c10ce574a605,0x85313565e2991,0x440af4becc86,0x1c50795da4a,0x9708cf86a,0x275cb2c0,0x7b92ab,0x1129d,0x181,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x5,0x37,-0x21,0x8f,-0x8f,0x861,-0x244f,0x832a3,-0xbec9,0x10d0971,-0x7f5ad,0x17e107,-0x2305c6,0x242f7713,-0x602919,0xfa6b067,-0x904903,0xa6377,-0x1277f]
def rhoDenominators : List ℤ := raw_ints% [0x1d44c796400,0x59332350,0x70c420,0x80328,0x29700,0x1450,0x708,0xd2,0x200,0x1e6,0x1fa4,0x113,0xb9a0,0x35a,0x7d2,0xb6d,0xf3c00,0x4510,0x1a38e0,0x33198,0x14300,0x1a7f0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 29
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
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 29 omega7=padCoefficients 29 (omegaCoefficients 28 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 28 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
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
  change m∈Finset.Ico 7 29 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xf57d14a515d40b8650c64000,0x1e443bdb9a80f4abbf55714400,-0x1cf61afe4a968d2522b23981b00,0x11e84c8239e27dd5805c9f272400,-0x80aaf792676a7537448977f0d4c0,0x2cb7ea91493019d6a066831714800,-0xc84250c0052affce97fd4c9659140,0x2e60419ea1a30be0672297f67bcc00,-0x90f72820cb4f5a4e8dfd3f0ac035a0,0x183daf763277fa5ae6977bb76dca680,-0x38211a90b72c1a91c78617ab1367140,0x717258b8c8dd4346706ee5a8e2b7280,-0xc97ff976eab6a3c668a8fb1c32bc0cc,0x13c2cb8f70369817f355500d5da5b370,-0x1b81392cbc223e77ed2f76af67ea7828,0x2210c46011cb0baa6abff72c9e1398b0,-0x25a0fe5c82e5976a7e6907f181b04af8,0x2520c899d6c2c78514ff684aa2522770,-0x20c08f28ed57f2e3c8a2ca1fbd654e48,0x19d64bf4682c0e3b3cb0ceb9dde80df0,-0x123863a137ac0f35aeee246b32b65967,0xb7993ca84e40ac176ff53725b3a3d9c,-0x6718f22277d92b661e7f79939d0d56a,0x33805901f4a8f81d60ea98fd221357c,-0x16d14e8d925e79ad99d4e2911324337,0x8ee805a56c4c53d339eb5156bd4990,-0x312f8e7892a553365561d7e3a57648,0xecc1e558c20d57952a9e3a68d5150,-0x3dcee779817e2a0c417a250a1cb4a,0xde095c3b3c4a8e96163368553bf8,-0x2a673390953e2f6c7bc3aa305664,0x6cb23fad13b66de9872e5878cb8,-0xe5b49fb3f23d2890dd7583a3ae,0x18747c391ba0f65b5997df20a0,-0x209790723bceed1f633f060a0,0x20a11eaa849f1d9af3bbe660,-0x17274bba88c5374221f3cc3,0xaa95782ebf29d8a350edc,-0x2c08f9f6a47495faef5a,0x4d278f7c130983fcfc,-0x1cca4e8f9bc18b83]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 22 39 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 39 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 49 indices rho q0 m0 0 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 49 indices rho q0 m0 0 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1ad9ae420e633142b0d5af0000,-0x34422b6810808ea00cabe3d9c00,0x3152a8eb8eff6c7d902f27aed900,-0x1e129d34a5ad6e1496c94c14e6800,0xd50101ca73f876f93b2ade84b3040,-0x48f3fcd8af9f0d3f16e13e9c9ae400,0x141d7a80f0593fb80be70f3f277cac0,-0x4965eecd99c34cdfa24adc8018f7b00,0xe1dbb3e2b3945e9b230297951b09f20,-0x252a26fc96ea54073a9e50b8da29b080,0x54a4ff31bc6f1404206f6a25b26f7640,-0xa834777f02ab0a46d0f8fe76a5a77680,0x12599ccbf837fb112b6685ecafb221d14,-0x1c482e488030fd3db96f47118e5eae710,0x26a54af2002ac07912e8543ce8aaef698,-0x2ef6715763f1abc6ed17a72420d4d1190,0x32de22299677f84abca61fbf096e0c578,-0x312f1daa84681ce7388cfc31726c9efd0,0x2a7cc5f03e362c28e4b3be3fcf344f8d8,-0x20cc073d83fa1428edf5794fd4824b9d0,0x169cf5fe9e7ce56a50efb59c89e1dee71,-0xde96f5c4a91459db497f0598c7a95b04,0x79fb271ddfb086300c63293a237bfb46,-0x3b673cc39899549426ccff7e83d08164,0x19a08cfac03aa8d579df6e16ebfdf851,-0x9c1563f31568e8f132eb5c06874c170,0x342aaabd0613c6a68a6afee3dc6a138,-0xf3720752e560a4591f9bc12406a4b0,0x3d80ad8b6bd98f21bca062eebe5f46,-0xd55c89fbe2ad49efbf05183fd0448,0x274133b79b1b248a84bb0770629fc,-0x60abebd90b55f77dc03ff1f7a5c8,0xc39f448bba6d59f0715a13e9712,-0x13dd3491594157a8a71f70cff20,0x19212ac9d327e181a6495e10c0,-0x17bd3349b3d3fd29b224fb7e0,0xfc6247997a519b9687ef9f5,-0x6bbcb9fa6f6f124b94d8c4,0x196e3b9d85b969a853956,-0x27f54c5a2849bde5764,0xd02c6504236c5d05]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 22 40 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 40 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 49 indices rho q1 m1 1 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 49 indices rho q1 m1 1 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x2efcf0f3992d9634b575f240000,0x5a41f471347517bafa868cbfb400,-0x540d21dc4fbbcebe94e99c1e9e300,0x328c7ecb092cd3ad856ef1e2ee8800,-0x1610cc0700e3280717cb7b5b46866c0,0x773242cfb3d6a3e2a09afeb1d373000,-0x2063013092b9b96bde7c9ccad527d940,0x74699b8dc5c71258749500de8ec3c500,-0x160be352cbdfcb498d2b5cf15beae7b20,0x39221d6e78a6ab6767aec97e9c12c4480,-0x8007bb3dd06062d6296aca10340b4fe40,0xfa373511dcde8b574e7ad6c308f534a80,-0x1ad544b8a69724c55a6721e91a08cacf0c,0x28a2238a5134f5cbcf81a618422db2f270,-0x3685f56579e223a9da96a567c6974f1ea8,0x4106e730ed5467c4b2e8da92c0e981d8f0,-0x4515793b800c0a9d81b9db78c6bce3b0d8,0x41794557c848bde30a127fc8770143b7f0,-0x37662fd0b4baf189eb0255bb6cd596d308,0x29dad16bb6c15e8272fb91c373f129e8f0,-0x1c38ae1013afbfd341bdbbed9ff75cec37,0x10f6ad5ca543d87fab5e678fb729cced5c,-0x912e66bdb90d28129a8d16c87cee0e90a,0x44ef8159c64cb111e53a158d988cd0bfc,-0x1cf648235d013c5d97678aa2816348267,0xab8e602c45874109b1817879330dc590,-0x37aecac4753347ba8b4bc0dd47895148,0xfbef41dc5964b926b57707474136650,-0x3d9788df21a2109e3c3382bc5f2f72a,0xce544de11e6184a0d0a1c8a8e46178,-0x2490fe0e756cb4c8e6ea0bd15e93a4,0x567ea492f8fe7eafad5489284a4f8,-0xa78c7dc2355a3740fd84a40de16e,0x10387b8404858e64d8af0d252420,-0x1377cd886b90e0312a20112e4e0,0x1157508521a4057571ef91d060,-0xac7cef5d9be72a5b6f2d3dd3,0x442fb1388231ac21b39f49c,-0xeb2f9e4baca3b694596fa,0x14b09fb1cd6edaf7befc,-0x5e075046ae8612333]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 22 41 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 41 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 49 indices rho q2 m2 2 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 49 indices rho q2 m2 2 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x523aa5aa4c0fc6dc3d8e67f00000,-0x9bef5015d396dc6217c2e6f3efc00,0x8f51a9892d852a9155ac4276d0f100,-0x550b43d2d89ca14b82db5bb551e5800,0x249e171846635f25111b91a4def76640,-0xc30bba40bc1de49843dbb050435f1c00,0x343d2b20b6ebd204cc8f728e838e2e2c0,-0xb905d57893f2ef076870c52f2aaeddf00,0x2283a68a4cbb39be0956a3f33c7d4c8ba0,-0x5811069b474c85cb030870664f23b61e80,0xc23a730ac198a40af07601f3bdfae6d940,-0x1756bbddae2e4bb822e1d55a39800136480,0x27604402f3a7e1680c3d0393b49508572d4,-0x3a99bc34184fc9c32b481fe80fffaea0c10,0x4d3c93cc96010f05bd2b631e3c4bf29d018,-0x5a6dbdda4321893aa0b0df2319a1fe69990,0x5e408e0752c3537f60ff8b4ac5cf9734618,-0x5793e833183c185e305004ee397dc9cce50,0x489950c7e1344dbe3206f7563be2046e018,-0x35b1e93041b34253f7d8c415afbbac08850,0x2369b9e34106fab0947c770833196538ca1,-0x14cd378e76e376b5deff474254af9ff1844,0xadccbd99ff663be9ea8a253243fdeba7a6,-0x5079996b4a63a3ce629ded3ccb4364fba4,0x20ee29b7215ca101e0c8b40296a5964ea1,-0xbdbabb3f806462bbec62e7a1ad16a8770,0x3bceaff63d95beb1d5b106a9b0b00fe38,-0x1065af7dee45dd01b188bf1391bc03eb0,0x3e111ecaf57598190d0837e518a45566,-0xc8c2bbe59f4e479bf2272e101a0fcc8,0x2244834d996d5ac65e1242a4c3c5cbc,-0x4dd6d04fc6f19f309d0f4f87402748,0x904b47b5e1b20ff336a353d4bfad2,-0xd5013f78f56f7eae27091a3f1ea0,0xf2679405c932c303b0826b67880,-0xcb74468aa88a39947ec2610360,0x763b42c95490fbe343adac9e5,-0x2b3c7d38346ce44eb9773404,0x880a211207cb54940b21b6,-0xab5da5bae61a0bbedda4,0x2a732a9dce691065d5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 22 42 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 42 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 49 indices rho q3 m3 3 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 49 indices rho q3 m3 3 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x8fe6a1ea051b9c016bb935e400000,0x10d7bdd6cb86ccb7d05d8a240689400,-0xf48672c19d513038ec8f8b4a9f56b00,0x8f352ce4f21c97a9f4594dd319490800,-0x3cd6bf089fefb2234f03e27f7dd32d8c0,0x13fa30e6ec6fa5608d64d45027133ee800,-0x546904a55b79ec5168fd222289241bd140,0x126adfd4b1722505f90f545077a535afd00,-0x3629170d24c0aeb9d40d30189a009f408a0,0x881b5469dc72d91b51fd54665868a390280,-0x1278426895fffaa1db49a44ebea2fb0f0740,0x22f137a2d3a24803778a2ab9cb2b22959080,-0x39fb9885081db1e3d56584a47008ef99e94c,0x54d40e68aa16bd0e6aed03694776d95b0170,-0x6dd96ebf49a453198fdef135f3176b4f7928,0x7e499ed78df84dc2c9ac75f65a21cad86bf0,-0x812adde7e1faacde1fee2dcc229dca3a28b8,0x75b2afa15d47b60723c032b68665a2d70870,-0x5f9c100811c96b60303f78907e3b06c97ac8,0x453d7dd1158cd7ee888f7a512d801f2eeb70,-0x2cace1c5c7c86908735650adc42822f60607,0x19a63b01879fa5d5f8ddc1a0e62b5bab111c,-0xd13eee60cd9215814d63109d4b9beb57daa,0x5e7eaecaefa53536b51ace7a4316b9047bc,-0x25aa56333706316dbc3a4f9fb65c179a497,0xd3189049b2fcea5114ebd8bbe63a4d2190,-0x40a10e7117c3ea4230f328cc833a017648,0x112e067d5f03def24746a5234ab3e18250,-0x3eecf7bb62f34abd65f26945a73fe350a,0xc4834540a099fa41cda1655f9560fef8,-0x204d0b8442fd5a17ce6ec7904ecb56e4,0x46716225249876820c030955175ea78,-0x7cecc2fe36e603e22ae858ddf2672e,0xafabbbd4dc1998964f8dc6eb5d7a0,-0xbd74c3a3938f3615f5f5c523f020,0x95ba11a25408fb21327a80509e0,-0x514350f365b8f64a853b48e9e3,0x1b766828ca379c3f21cda6e5c,-0x4ebcf23c296f13400d2a39a,0x58af2e7f50f19bb2e54bc,-0x1327ac8c116a4c1c5e3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 22 43 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 43 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 49 indices rho q4 m4 4 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 49 indices rho q4 m4 4 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,0xfbd39b5988f051027c841e4f000000,-0x1d1db10a5451c78ac15ed1bb50779c00,0x1a17258448a58a844b9a0cf50209a4900,-0xf15d782164d040dc46539ba4c9e6b9800,0x65337bfd66c8d138dae3dba9e31ac56c40,-0x20c95c38f169b5e6c581a1ab54a74672400,0x88a25cdd9c0423795267c9fe7d73c379ac0,-0x1d649690b1f68751fdd7946d40b1575d5700,0x5530113ee1fc9500778eb0b6dbab31c3ac20,-0xd2e6d3f5d03e45199b8deac084a53f665080,0x1c2ebe1d53a307fc62bf966bc3bef093d5440,-0x347ace5763f5e624d5d75a498ac24a6b5f680,0x55ac929c472eae673f64275133680d934c094,-0x7b3f3bcda8a04a5e81b7b4ef5b3ccd4941d10,0x9cd8ee16498532d040e95b5ba8d40cb362198,-0xb11a803ce3322c086e6a1cf2838dcd7d26290,0xb1cc9425e5bebc0e46a0fc35a69383347e7b8,-0x9ee98ee85d931dbc2154f8d5c88763a6179d0,0x7e86b15866a2f4d9b889fbb5e8f402bcb2558,-0x59bd08c8c8b7722b6de5b774f00e85363d3d0,0x38a812e6a4196fde0e1bf6a6c36e2362a98d1,-0x1fcc6d03365afc898745ea08a907733498c84,0xfd53fac8a6017192dc4e6692b2fc081bba06,-0x6f97727a1e5ddaaa70c2e6451ce9c18b19e4,0x2b550dbe1002db40742bc30a6be9caeee3f1,-0xec41566460235b51f898fdd984b6894e370,0x4641485bd141483561bdf75f8c008c40f38,-0x121b5b21b860270fb4ce225585cce4696b0,0x402c65758d9a1dd8d21383df08c3976786,-0xc17929fd092ebe1856232ce2056857f48,0x1e9e8b931a2ce0b34212b48e49297a37c,-0x401847071dfa07ffc6a3773428f141c8,0x6cb4c5809132a856a5a9490393acd92,-0x918e08fbd2e21319fa7ea9fda3e720,0x94ade8877e2d2835171f652e67640,-0x6e8f9b8becb62b03dffc4dc16fe0,0x37feba31771aa79f1ec0a33c7d5,-0x11786245c797877154d1118244,0x2d98728246cb7167c0337816,-0x2de1998d08e1b0aada81e4,0x8a3adc8249289a0eba5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 22 44 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 44 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 49 indices rho q5 m5 5 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 49 indices rho q5 m5 5 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x1b8b24fdcafa48dc459e7350a4000000,0x3258f3f530cf095e2561b501814dd7400,-0x2c91231047dfb18dc475d830d9e1f5b300,0x1972881114787e5f27f6b08e86e6190c800,-0xa8897fed5228bd6bb952c41347213c87ac0,0x35e31c62ee69e9d532183c5ad7e5f3fcc000,-0xdd8d93d4e5ac830aea6430737cd436282940,0x2f00ecbec2d9c773f0281dc58ad80d5a36500,-0x864c2fa7a5da9209ac94484994e838711e220,0x147a3ab09b4a1236180029256d134a3cf4a880,-0x2b201bf028b1a5991c6852a99a1c09293a7840,0x4f1072f4db812a22d50d298edf8c87ae60c680,-0x7f044eda932ec5ee2f74dc3e8d016c7f764b8c,0xb3b6ee496babcfed2b953af5b84a0ce78cf870,-0xe0d20f01079622a42ed34bbbfbe65c7be2bba8,0xf9637e8abafcbf9d7c260f8d9d2fa5166e2af0,-0xf5cde340f5ccb525abda7bde8468574a027f98,0xd789e8d4190a1eea88829250f88334cea6faf0,-0xa83d6c61be8ae93e1d8fb57c9bd997bad40488,0x74e23c7424988328c55e77e52fab59024dc9f0,-0x4838bb12e3794a3af7ceb5894615ea6ecd21d7,0x27a1c366a12b9bcef0ef1afd5e4d0e775966dc,-0x13460228d4fd62fb604eca1fce852c4333444a,0x8484ed2372438c45a851c98b42b85b4fa977c,-0x3222bdbf90a582ea62eead2b0922db272bfc7,0x109f020a6253875a46ef643921cf2a17a6990,-0x4cd0557bde96ee4f7781a447210e3109c748,0x1331d338ebd723bbf28e1fe8e772940e3650,-0x41d2781d9525decc36922829d9fc9e516ea,0xbf8e43198c53e00f2aca593f4c84cf7878,-0x1d2f1fe97fa1748e83fd317447b8eab624,0x3a9fa7473060fdc227f6816e9c5a213f8,-0x5f0e40529536e618b8d4aede2835cdee,0x792362053032900011e3dccc8385520,-0x7521d1527d18ff33fd538aad720560,0x51e6601b22b364b211987bf08bf60,-0x26ac8f6211e5780703c69550b7f3,0xb210372932a883f356834d921c,-0x1a69f898949d3cf59c7495a3a,0x17baa2618fe8b328da7767c,-0x3e510e3d8f9373e72393]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 22 45 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 45 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 49 indices rho q6 m6 6 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 49 indices rho q6 m6 6 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x303380bc2335ff8179d549cd1f0000000,-0x571617c856c62eeddd73dad802da5b3c00,0x4c2c0e41f97de3ce97b69152253bcc9e100,-0x2af6dc1ae73827b0e832e8bc27e0143ad800,0x118ffd1e2a9b570acd02c0e48e92c3d4c8240,-0x58b1ca84cdc656235fc79c69a04873bb92c00,0x167dd6de9b4855a8b2f740bc488ce6ceeef2c0,-0x4b50bc3d180d0ed35ad0157a4a3c7bffd6cf00,0xd432c83a59692cc2590ccebc9a6ace870750a0,-0x1fe48b35d0c1e9c2f6489b9372d151027ee8280,0x422d14a7b545fb2a41ca394af80a86d8dc0a740,-0x777b07ed614a3f4addcc0957f475dd31eb3f880,0xbcef55cf0d72ff61da0e58ad5c80462c070d654,-0x106fd32237ec11361341e834ed77ca69e1096e10,0x1437ada1edf3fb7c5e166d9fe7e2c6778a2c4b18,-0x16099384a31fce13a025d2a33a5e1f5414854b90,0x15545c18077c77e72882cd85ced95201bc478e58,-0x125a7e0b5541b2f1d004c8ff6e866a51b2366550,0xe0c1a0c57c32562d4de08eb2463e32b48f05898,-0x98fbf6377f90d42d73d6f59e82ec72baa698b50,0x5c87671094a569b0e3415be0fcb094db29f3701,-0x31a724565d6118b0d60f870807d410a50a310c4,0x17965d4ea2257dc9b12b56f15f7cd830e5a0a66,-0x9e3beec12e9b1953cd9d816af443774b710c24,0x3a54a35858e60b95329dce2bd29d1fb7562041,-0x12d096e6402d6d92fab3d90b626cdf1dd5bf70,0x5475e0cf169cc5ae41d5dd6a5a22e97361438,-0x147673f2698b1a0d86969a876b05eb32b96b0,0x43e4009cc69b247c709fba7988efa3a38da6,-0xbeb2128edb8223514560aec85e7a96be1c8,0x1bf6a3d7d1c75439dee3011e8cc762dae3c,-0x35e3c7f8900c9703ec29e2e1b5ac452448,0x53827988511ef96f3a37c0fe6776ea352,-0x653ee575703055f55e3df7cf083f6fa0,0x5c9e443727b458ac452c09f42423a00,-0x3cd97f00b0caf03af6e349350a1860,0x1ac4ba8632c0cfdd5f0207c5bc7c5,-0x7191ca86e51b7586c3af20d2084,0xf4e7ff542b04620ab55b39476,-0xc449c3203a80e3e57d3aa24,0x1c14be41a7c4a3a2ebe75]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 22 46 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 46 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 49 indices rho q7 m7 7 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 49 indices rho q7 m7 7 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0x15e464d9c54543532600000,-0x2056a5ff8fe9d3ec32e0000,-0x169689e415c4cce7e930000,-0x9ed3249fc1adf69e6d4800,-0x3149c1722a31cc2b93ca00,-0xb7dc9286fe02d2f5cce80,-0x217303ab5556f33bd6b60,-0x4de365d22df9b6062d30,-0x938e246273defd786c0,-0xe60b2bf7cddba154a0,-0x1295c045a3f0f6203e,-0x1400e05f87e15a60f,-0x11f43b3149494759,-0xd6c10ce50d12e5,-0x85313560a81b9,-0x440af4907d5e,-0x1c50783c8b1,-0x97087f350,-0x275bb5d9,-0x7b7037,-0x10f86,-0x157]
def m8 : List ℤ := raw_ints% [0x0,-0x545a21493d9e7f2295354126f640000000,0x96ad41509625d9a7a2d9b5be17f4b9f5400,-0x8243c64e47ef96592d42bacc7842860abb00,0x4899df3394219825cb580fa7b43a057fc8800,-0x1d509a155f87e4ab61aba83490c8b338aeccc0,0x9230fee708093e70d0f823df6f506ee0e1d800,-0x24982bf7213f79da188f0bf6f7147e9d4f36140,0x78eacab052c7d8c2cfaf8e16986018da6228d00,-0x15008fe953665e7876b5d92fd02e72eee85a67a0,0x31cbb45708d1bc9158606ce31a9762d1ca035e80,-0x65d3eba25b61c4fca76dd04c18bf2cb704497140,0xb51a1e3ee58716faea28192a13a5b7a61f316c80,-0x119f4a17ee0701c876b3288acefb79c3d72fcf5cc,0x18233fa50946e810f16eec93cf788966f80fd3f70,-0x1d32e5b03aed2a51ed6897adc7f9706f974546628,0x1f481e013698309c24982e7098d5ddc76e6a299f0,-0x1dbcfbb07fde1eaf8189794e413373c38a6964d78,0x191d9c14bb18fd85c527f77887e026b3db70a0170,-0x12da4b184733e1392d5c368da886c5fb57dc93848,0xc9320e9d6f5d0c839c0e265e06692853d4c2f470,-0x7722a6569263fcc19b600a34632b893689139fa7,0x3e86c2eb72847e82cfbfa84ef80b2a5be22e409c,-0x1d04bee9255bb8e5924391381bf65df49c313cea,0xbdf3efa02864355b10c03db148f39df38aa333c,-0x443c287de25f8bd586bc0cad47b45174adb33f7,0x156a4f4566d62d3f3745b4195ea986c8ce9e990,-0x5d61a86954a01c8aad0a2a738ab870cf9dd448,0x15ef444b835430273b12c9e046d019bdd33250,-0x46679fa433d8e6a8b977beb432c9cad5c3cca,0xbed90b1f6b6a29d35f40cc321d0d3ce8e9f8,-0x1aee5eee971c287fbaeb504442aefbc99164,0x31c7657c9341ae995305fe545a1ec14a578,-0x49b25f93a87cc4fd6d3d42b97369a94dae,0x54f673194f6bbb2e1044c81000c6076a0,-0x497d604d97be3f21388c38275354eca0,0x2d55f74d2bc0b08be9a6f11634bf0e0,-0x129087242dba5df37afc3fb9d0e803,0x4883823810f9d1392a2d663ea9dc,-0x8df421d74633d7064644eb9ada,0x6571f1832e5cb5c6a397f43c,-0xca5fc5ffbc0c19eb7ec43]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 22 48 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 48 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 49 indices rho q8 m8 8 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 49 indices rho q8 m8 8 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x157,0x1]
def r9 : List ℤ := raw_ints% [0x1d55031fc74fcd3467ea00000,0x2b3e3404900d05ae250420000,0x1e235c1a999ac4b6cd3c70000,0xd3637d73cb23c89fc5d87800,0x416aff0b56c70a97c4965e00,0xf343ec3bbbb2abe49c4e380,0x2c193d5808597d1236e0f20,0x66447d31e64423ae891ff0,0xc0d53c62c6602a3bf5e10,0x12b0015a2dd935550dba0,0x1800997156da08bd0d72,0x19a3d09ba4d31f9f75b,0x16ce2d491122864da0,0x10dc86d162601295a,0xa508ddbd31c9e62,0x52d79a959985d1,0x21af23536fbc8,0xae0c55d0d55,0x2b4cab8bf0,0x7e35cd44,0xf48024,0xf451]
def m9 : List ℤ := raw_ints% [0x0,0x939dba402bd55e7c851d32042ef00000000,-0x104c6524963e0d999cdd23e7789ec69cddc00,0xdee566f090a8e56e2aec60ba1c74fcea1b900,-0x7ac8dcbb633314500a02f5956fbc3622f41800,0x30fc88d4aa77583a543e0b6b16333f83c462840,-0xf14c0cd85bbebb104e50ce255c21e0fcd0f7400,0x3ba3b03b1e9d936d2c19ac518c05d9f5d552eac0,-0xc2816c93fde19c36c76c2845d4912c2f41dc8700,0x215502b6743114c5ea39ca1b4b5ba7b15a94c5920,-0x4df0a4e294a44d0c0aea0bedde63925c9f9670480,0x9d1ce176fb98c6e599c46c4f38a82e7b50d425240,-0x1135209b9545f615d824bc48cd30ce993f79408a80,0x1a6210e6ba2368a0322b386869f85f34860f1e9414,-0x2391b612851fde1a4bbc0d87342cb6c1ce71e48f10,0x2a53624248ed810ba04ea00a569d097cce5adfcc98,-0x2c93ecb23448b0e466fe32d4da6fcb5c01813ec490,0x29a21d4a843c604d40b0805cdb65fa3fc73cd191f8,-0x2284ba11e8d3cd268e88143f1707cb83b62030b4d0,0x196aafbcfa6eaab57b02f280c85b5724f35fb759d8,-0x109d8e9edfc4702f253a9b1e7a44479d927cd376d0,0x9a240333a40b59bf5957c11e1139bd8ca24e97f31,-0x4f2221adcaee83d890934fbb774e7e1352f22b904,0x23e25cbe13778ca7b589b90593b8fba73efacf8c6,-0xe53a79d11a93fe835571f927f843dc28f5255264,0x503f3226b228aec30b6a42c3f152e2ead9bae391,-0x18819e445ddd49510999981635537115bf767370,0x67cd2ef8a807a5df2681575dcc66ce7f102cd38,-0x17a37776dad8708b666220463ba1f4d4c124eb0,0x4965e111c9765a4a0ea50df743a1de005ed7c6,-0xbffc053f4b4054a5ef0929475c1095807bc48,0x1a10c379065211202f30bdf16efe7b3683cfc,-0x2e326a629e7ec72ab02cb716b01c481d1ec8,0x41516e2fca7d78e92234856de93f5001412,-0x4792e6c701c99e32c5130f61b3d04cec20,0x3a80f9a66b965e9769cc8d2594247a3c0,-0x21dd80bc4903fe62a2dd86f93aefc4e0,0xce5f456a1938e553af908b32f4c1b5,-0x2e5810eb33ec1aedfc6f38b6c92c4,0x524af9814b67d4a3783facfd6d6,-0x3468badcca15e51a1774c1664,0x5b1db9f8eccfd2e6efae45]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 22 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 49 indices rho q9 m9 9 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 49 indices rho q9 m9 9 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0xf451,-0x157,0x1]
def r10 : List ℤ := raw_ints% [-0x14e49d6378ed6f158d870600000,-0x1ebf7c9efb40172bf9d1aee0000,-0x156362db015a698c317d8410000,-0x95b149f5318c6ace9b756cc800,-0x2e368139918bac9282e0727200,-0xab61b88251649f4d8ac98f880,-0x1ef8f0f73ad12dac19f8195e0,-0x4793ce2a0accf5af5797fd10,-0x866de2d43b32f0ea11782d0,-0xcf7e1baaed37759ef4e890,-0x10919c8e936cfe0bdf28fe,-0x1197208af65177c0853cd,-0xf8839a7fa74349dfede,-0xb625c616b6a59efdf5,-0x6e4084a59ed683187,-0x369f6ae17831d004,-0x15d82f7a4df1399,-0x6e750c428a5c2,-0x1ab00956816b,-0x4aa238d82b,-0x87deba69,-0x7aedad]
def m10 : List ℤ := raw_ints% [0x0,-0x1025405f04cb56559e8f31787522400000000,0x1c37215fa4bed253da697ca058b5df68b63400,-0x17d9c083503d7cf5d23dc76f6e8d5ab360e8300,0xcfd424bf3fdb48984db32d42949be92e9da4800,-0x51f2efc5e3314429136b1519df23ac05b85a4ec0,0x18ed25bab4db3664f40c34deb8d3a1e942552b000,-0x615b3d23659c786e78ace36f161ff4d37195e7940,0x13979c327538ff4555df1a6b5d2b3becbae1167500,-0x3503e8abd0aff4f5134d98e79ad6c9da3887b73920,0x7a4991c66febcbafe0df703455c5337fcad329c480,-0xf3102c70909b0d43b2fb01bb0d55ecfddbe5c23240,0x1a3c81ebf6b1f481b7145af78d4a4c79395b7d7c280,-0x279fe51c32d5f6ad21c27d67f4062bf5c90b65d480c,0x3497d80d1b77626533f08e7cd1d755d0c1159477670,-0x3d93be2cc4689c0e2cb2e445ec3db40b5d9a9a0f8a8,0x3fc53519f41dc8351ed9db0c388de41579b8d82f8f0,-0x3a85f4d94e4263d5550715ec4e749ceea5853439a58,0x2fa4d8db9bf81f017058ac44cb94d92fc0758e6e3f0,-0x226b3c652724a679fba39ae5b9bea036ccd034ca608,0x160e6946413e554d6064dc344a39a63419e8d56faf0,-0xc862feb33a0c0bb8e0c357ccdb59d4da116a577777,0x64a5126b561a6110d92ac53cbcb006fb87b91d665c,-0x2c99352ea5a1364a0c45deaf0bbe374ec101e8c78a,0x1160c8e7840b660c9eff1a6347df836a4c04611afc,-0x5edda69429fc644c026d5495211fa31baf236a127,0x1c30e5e38e95220d141adc6f4c17e5b70499fd190,-0x73fdd23ee6c3f28c72fca473aa1f07a4bf90bd48,0x199ba0b5623965f2b3cf7aff1cbec83c08b41650,-0x4ce963f95ca002858c96f55c5018ac2bb3736aa,0xc217d8fcfa310619585b44073cd8c44c3dc378,-0x19593a4fdecf831a2dae6df7dbd45c4ff2e8a4,0x2b10ed06db08dc41536e92c2ee52eab961ef8,-0x3a21c0f82a1826d1e464baf9ea52a572ee6e,0x3c84429cb0d2b0c99d2ffc5b824120da420,-0x2eb7edc91f74e6465a508f22245c7535e0,0x195bb77ea80fdee650a4cc1901788ae60,-0x8f9eb0e161a8ba2a89e03062f791213,0x1da4c027365142675e1ae0c0025d9c,-0x2fb608ce70dd9331c5f086c8057a,0x1b10cc0bf27985cd852d958dfc,-0x2901d04ed59e492c2adcff3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 22 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 49 indices rho q10 m10 10 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 49 indices rho q10 m10 10 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x7aedad,0xf451,-0x157,0x1]
def r11 : List ℤ := raw_ints% [0xa832b4c7dc5cd84c2955eae00000,0xf726c90a2e27149b092f0bb60000,0xab9f6db76bbd3770a52a85690000,0x4aedde1409dd84de9d50b340a800,0x1715377d6155657fa1241374ba00,0x5566693471f3000531975719a80,0xf647c1c4372d576278d2907760,0x23771f9ea59f872373a3606390,0x42617ec30847432ec7c4dd2b0,0x66100894158786457a86cd50,0x81d20b7b89b777fd2d1bc56,0x891e378ed9d19703e5e2a5,0x7859d69a650eb23b88528,0x57972856c546f74ad383,0x3492bfa1d2fb3985608,0x19c85c788f92bc1307,0xa2eaccb46a6d35fe,0x32ae3ca4ee2ee09,0xbff67d677e5fe,0x20a69671eb24,0x393b8e14ee,0x3100b6c4]
def m11 : List ℤ := raw_ints% [0x0,0x1c4130a64863d715d57a9692ccfbf000000000,-0x30dbe808baa0b2d69b8d8e5fa0bc4d70b377c00,0x28db145acd8678fa7bcb861b6fad5f759187d100,-0x1601085c19e66b2b4dd064b8a1f1926a6c7fb5800,0x893d9f29b35194dfcfc562fe653ac53c06b5bde40,-0x2941332b52de3cc9eb31d6d63f796fb5a12890fc00,0x9f2ef826c3695deface12d5c76c7c1755bb7b482c0,-0x1fa29e8ada83a7fb3a018b167cb2b049b32fd167f00,0x54807f852c3b1746a228daae6b66d1dbae75c44a5a0,-0xc053a8808902b01938622a6ac220793ae858eda9680,0x17906bbb0f4d1c5d92fd34c6ea97a33fdf32ed2e9540,-0x281e34b1e31dc152173122e3f91c208f7a8dd3f6ac80,0x3bb2a0185163ed3dc0057d476a79fcffb0ff881199d4,-0x4e069cd9b9fe9f356e02be4cde800dd47031f6d6c010,0x59e7c6147abb9a4fec084baded61dbb3a81b6e202618,-0x5b9275775826e2452276ae695919b40247fb0a92cd90,0x52982b6b8c4061d88e87e00d8e2448db681c410aca98,-0x4209471b7dca0defdce9aba08c5ed8e302cacf855850,0x2ed045c48308736d55b33934b1eee85abaf5d4683918,-0x1d6976262c02fbec113d2e741ec779b64c22e8e75650,0x105bb973a2a045f14b0c0912728e715d7ca71889b961,-0x809f8e121fb7bd3ab45676c8790642329bea1601544,0x37b414cdb74ccd282b6c5f3d62d2b7716c02e30a526,-0x152f7f691f0088ce9114b66a8ac5c880b9091942ca4,0x70b888b4989889d8dfa18ad277e64f702af36ecde1,-0x2098ae64921bfd80bd507802084af3989aa5041f70,0x82475ebd64d7688823afd2918f5f49e1ec0585a38,-0x1be1f275074f77eab5da7fa2846ada9833c9e3eb0,0x50ff100773fb4ccdf12aa4dbfe7baabbba3ab5e6,-0xc52d16d48bbd1ec873f80124891a91459ea6ec8,0x18c3f923d569a2eb15000276f49cf03daf4cfbc,-0x285263b0fae17b7fc33464abd9d9ff8b58b148,0x33f109e6f9a20a4a72b8087763c25b111f7d2,-0x3358c0d35b33e1fc029cfa4b9cde5b208ca0,0x256a9f0852df3afe4604a76e8b1af67c380,-0x1307f65f21c9628659ca64605c823a3560,0x641968ee25782c9b87b7e9965389dda5,-0x12f99ba731d765ff5282d3e4205a904,0x1ba99ffc634245db296e609749f36,-0xdf8dd03a4afe5c176e2d2c06a4,0x1272b4c222b3ad5b050e8b15]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 22 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 49 indices rho q11 m11 11 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 49 indices rho q11 m11 11 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r12 : List ℤ := raw_ints% [-0x430c6eed1524add312aa8ad1800000,-0x62629b0fa68c3bd1caa77a38580000,-0x4436e1868d182e1ae4b5e65ed60000,-0x1dbb3bf892582cfed8cb1077722000,-0x9245358f208eff72df3a5bb820000,-0x21c067d795955bf98e4a6aa686000,-0x611b52bf78e4f679666031eadb00,-0xdf27656c313001a86c51e4a4160,-0x1a072c54f4858fd3145f76f4770,-0x27e2afba4fb26bc206fd60b7d0,-0x328a70971a450f858808a5a28,-0x352672ebda89548324c3fb26,-0x2e6adee414f7c2fa98197bf,-0x2195ef5feffbdc6c9e24ac,-0x140557ca09ae2db5a1581,-0x9bd1d724a58f9e38490,-0x3cef5aa476ef2fa9a1,-0x12ba6ec16441c572a,-0x45df6867b2a6cf7,-0xba8031d69f6ee,-0x13ea3a9bf310,-0x107684c7d6]
def m12 : List ℤ := raw_ints% [0x0,-0x31721522feaeb86635968780e6b8e4000000000,0x54a11f0f8f04e1a215b7155f328e32722eda1400,-0x4605eef23c2edf78f04283503133a13e8e5530b00,0x254e1f91d862cd24f4e712e3bfc0f92f42e5020800,-0xe615a0e558435ccec69411fb6d644516bf948b80c0,0x445ec3e9af9cc1cbacadf1b36e50ca890be69bb4800,-0x104b074c6b78e5475c0c7807c5ae0ad9cb06dba07140,0x332ce873d12f20b48aa824007a5dbd79835b4ebd1d00,-0x86f8fbbe4c9aa72fa17ef04e9492b1f40ca5eea2f6a0,0x12f316c4142d3db7cf7e5617e774ab8fd4501f87eda80,-0x24a57c82ad849857a9271548fd70d39466811be3a7b40,0x3d84c20d5cfa566feee7a21bdde7b2f0d6e87b10d4880,-0x5a37540d8dc8aa031108c0ce8aed92615ca0cabf3224c,0x7423a9220747c90d2d4fe2d2f5c7fa33dc03511491d70,-0x83ba691f22635398b5d4dbe75d0fdaeb5f59f3644f328,0x83fc463a5aab43ceacb76e8a89a5c82b4ada9739247f0,-0x7506652f9dfaf5f47a2a9f4cf6ddfb7c3dbdee05c2e38,0x5be80700c9bbb6938102904d667bd58c245a956d1e270,-0x3ff222aa8751bf79601b046d4c4dc6141414f6b82bdc8,0x27656106d756b042279779e7a885c69286da7fb2e3d70,-0x1577022f4bdf5d3752c479871038e87bb4698dc0fc147,0xa528f663e2769cf7f0d8d09ab67eaffc361f33aa381c,-0x45e956ba91523970e779db9bd60d1c504be251d6c42a,0x19f47160615eec8a0149bf53371a13c4474185cc8ebc,-0x869b228ef186f1ad653621055d69863f7b81037a757,0x25e12f888ca067b3c27446bda1228d358abe1922190,-0x930f3f05ce9b415763b94ef0f556e926936bb36248,0x1e828af9c5dec0f6e2e6d1d3d59b95e16604c8a250,-0x55b65966b539c50f65fed6cc8d55e316e1932d48a,0xc93fdae4c3f422252d66e2b8c87c14dc1169c4f8,-0x184de1091e1b73bb15eea2954271d761a3f33be4,0x25e902e769543013edc64cc00bb75aa16598078,-0x2e9634f0e038eb6d8975920b0808a7dd4af82e,0x2bb60d6fab00d39c39b21f40558b0ae219da0,-0x1e0c9864ae80d86cc50f6138753568505120,0xe50039132d9bd42e0020e0fbf0208257e0,-0x45dc9ba9a5abbc712175977455654ee23,0xc2754d1d1dd27f965124267feb50d5c,-0x1009d6e79424a3a23a7fac01773a1a,0x735c69915ecf54b4c215eae03bc,-0x84bcfe4513696bc50b857ea3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 22 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 49 indices rho q12 m12 12 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 49 indices rho q12 m12 12 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r13 : List ℤ := raw_ints% [0x16868eef38cdd7055299f820bc400000,0x210324f79f4df5ca7334695d18f40000,0x16db78f60848f8c443131753db8a0000,0x9f2831c30f966164641faf2237c3000,0x30db26ad5f81cbfbfbbc2cc001ebc00,0xb40a2fbacae97e2e88acfa7a981f00,0x204ec2ff8fb872d46caab071e70240,0x4a12a415fa884b801abe0311f3b20,0x89e0aedfa0807500dbafe49fa320,0xd2ac071c7768edbe0bb6cb5d650,0x10a13fef91e7beed47948223404,0x116c65cde85023a7c9cef83662,0xf26d2363d8c29e69e04f71a0,0xae8cf3f35fb5ff1bba3136f,0x6775e2454407373d2c518a,0x31fda26dfb78d46390c83,0x13651863f9c384387b4c,0x5e783b43bbae6a64fb,0x15c5d64d45d545556,0x39469dc6d511afb,0x600efafe7a350,0x4d8031495c6]
def m13 : List ℤ := raw_ints% [0x0,0x5687a4fd3db1c2b2ddc76d2193c38f0000000000,-0x92a0718bb47e377b67475104d71cb8b7af1001c00,0x7813c231183e187302a2492def7c44ec9267c22900,-0x3f4bec5ffc27af7a586fddcb03894268a4a85b09800,0x18224e7e0c353ddbef9a2d2063a670cdc1cb711b2440,-0x7174ea0b24cad6fca1010b2aff6bbe167a41a127c400,0x1ab97892d039ced1001b2370d782e733037de0b88bac0,-0x52ef99ab762755142d37503288d1e44b845fa7d82b700,0xd808e66a58ecc28f5db6ca90cbd30e4d5ae3c2b6b1620,-0x1df137687effcdf14705ae8ca8e079d32c851d41d1b880,0x3923399f879bc71d05eaedfbec68e487cef90805c6b040,-0x5e995182916884818b60a0819e21c8ebff0471969bde80,0x88bfa00715a0f56706e46af9982a474c39f79d55c18794,-0xad6e96968358c238e5e9d71d2fc58d1f86f4189f8a0110,0xc1ace66c83ddc7592e27dd5559e8a28c80a6e11a94d798,-0xbeeee76ad7dbc3c7829612a56046f59729ec9cd5a26690,0xa67349a00d1b4d516a4c13d0089fe115bb0c210fa85038,-0x806e2cf17427c3f840510912c3ec2bf20aa1c3ddaf6fd0,0x57b7badb9a4482a14e9a015b0c8375cbd7536f306e4658,-0x350040cc264254cc9579a4ccbcf1aa9e6ebc4ba9ce89d0,0x1c4b17d28e567bfffb82cc444f2acdfcfb7e584b3a2d91,-0xd510539fb269daccb70f736e57545b8bde0c836dc2584,0x5829580e5230a9572d01beb320eb28cce789311e42f86,-0x1ff3ab9c16339da700154841c6ef82567de15633b5ae4,0xa186df0130d24e78b2df34986a1d5831709862ecff31,-0x2c3c4250a8367898a808ad189fe119e622a19f130370,0xa6d06cfbb3591c746cebfce52ca9417767aef875b38,-0x218bd15ea4111ca3a27d6acda09cd1a1fd54d4126b0,0x5b2194c8305194c904e82bc6c7c05da3e3d7839806,-0xce57b737a6d64b2d6e10aea5ce1c4e97df5837948,0x17f4638e65e62421c859ccc6e75ef6ece7159e67c,-0x23c93c9be0067cfa0116adefd209f35ad781dbc8,0x29ef8fd2154df6ad4a239ecf979b52c03b96692,-0x25541bc27156ac94cbae180229651319eb7120,0x1831ef18b21f78212f461b6a7ee9c8e8ae940,-0xac8e8f914c2dd81f6f62b4c55d60c95c9e0,0x30d183b26dc44dbe7f27b544d1494f4395,-0x7c9e4399891758ce7e6725b41fa2e344,0x94c62ca52a9452744c78966fe44d96,-0x3b81c28ba1c78d7d9bd8e75fbae4,0x3bab9f1caadea8c88e17b24e5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 22 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 49 indices rho q13 m13 13 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 49 indices rho q13 m13 13 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r14 : List ℤ := raw_ints% [-0x6a0a8beea8d32a14332fb26f6d6400000,-0x9b3baebc8ff0062dedfd9f79bff540000,-0x6b593f2de705248f85688ca805bbe0000,-0x2ea7529aea2510945e36e6801e7e3b000,-0xe4cb55b8a8e7dbcef1acf13e5d640c00,-0x349bb756f037949a18e3f26347d97b00,-0x96c4ddd3d1ca0c85c3c7c334ce7cd40,-0x158f7a22005fc30737466e706ece0e0,-0x280a7a2aec291fa5b2b00a8800bd60,-0x3d06832b9a663615591f55ce8f0a0,-0x4cdad41f5dffd780f99945fe65a4,-0x50433c7d8ef0de271cb5b9de596,-0x458ad0371b7ab1ba52453d9dd4,-0x31dcc889b7469a66383eddf3e,-0x1d69b00fb86e5277d1b677b7,-0xe22000d072fe12a7e7dc1a,-0x572880a7e03f4bb82dab9,-0x1a542f833f683bad58b0,-0x60313fcea1ee519b85,-0xfa32841b64f8a1ec,-0x19dc1e97e9cab73,-0x147ecf20d9b76]
def m14 : List ℤ := raw_ints% [0x0,-0x976d60bb2bf714b9041cfefac2963a40000000000,0xfe1bb6964a1774658ae47b638226cdfe376b02f400,-0xce04afe5d419eb1590cfca3c71adbaa52aaa17a5300,0x6b7b0df51b2c77e3d27c88633adadc993a012583c800,-0x288ba2b882e034f0e13c79a010a4759c5da273daee2c0,0xbc84cee661f1997ebeda9537e1238a4a896a1cf25a000,-0x2be6f6fa355998600858f454f4db420f700e141c704940,0x86a61c41d096e634549779c18208ef9b0c58ea18c88500,-0x15a7cac37cf2f5a39aca6ef669ec26592c0fde6b8ef4020,0x2f6b788ea5952bbb036adeb1e54467636045d06b6032080,-0x594fa349a753cf1b942f488118d6adc12eec91106380c40,0x91de2c55683b943b5d0d7297de9661287bbb16378787e80,-0xcfe63bc83631926ee88b4b6891dbfb96704dfb21057648c,0x103d0f79d70ac08213811702431d9430859ce28317433470,-0x11db9c83cd8eb40bdd5a1ec59ed8c7d34e32f3a9c974d5a8,0x11534fd708c3f432576a43c6780e7cec903f28b10a6786f0,-0xeda6f9313b856a214124a1662485002f67209c84b8c9118,0xb42f827f04d4e69378bdf3d80b50578338bab1b79b11cf0,-0x78d3d4ebd3c11ab1f886a63af2577252e30206f1edbef88,0x479cb247c3ff69c9b5951633e6a17308a278ed4f2b25bf0,-0x2575d193645ee58a8dd296bdadae303dcd15543bc2bd517,0x1141e87b6bb628a4ba9f4d3d42b5d6dca30665f090575dc,-0x6fb1f2571128317cc069ef4cff811c06fea708eece12ca,0x278568b3c19939b3a68e63399dbc0dab4b576f9094ce7c,-0xc2c2a5f78fb6980a3216c67a800ace0c59abfc2a66687,0x33e7d86c5caf46e719bb2d8ab230a60e695fd87e21990,-0xbe2055404f421b768132a1f188099ea8de93b732a348,0x250ee6632e18f6eb7f9012f4157a8b954db0eb411650,-0x61565daf349474150f87ff819bea61a97295d95666a,0xd47fb2cb3d570a1762d6dbd68430d3536bf283ee78,-0x17b56d0b7dd083a110a2a94e59c9018724748f0b24,0x21e959098eca8685b430394a46c41d79c2b38c9f8,-0x25e15752a011136618403ae8d818e448161372ee,0x1ff930d693cca48478f89659fe9d7e932af8320,-0x13875e4ae8d18e14a0619d35da7c8a2cbbae60,0x824226d7bd21637b4971291458743e138d60,-0x2226cc22ec2c989177fa8cb4bc943217433,0x4fe5afcdd89e53be46bb0be692db0f91c,-0x563ea7c242dd8b5892eb95bfd0bd8ba,0x1eaf03d729e4b956050c022eb157c,-0x1ad06b04129d71ea08a7eea853]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 22 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 49 indices rho q14 m14 14 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 49 indices rho q14 m14 14 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r15 : List ℤ := raw_ints% [0x1c0b001234f7b0ba1b2bead54e558400000,0x290291f22ab8e88f97abcafb979faf40000,0x1c53f6963b38af2cbfbb1d9d9ac596e0000,0xc4bd20a6ff065dcda42c1170b57d393000,0x3c385f87d20d4f791dc3ff4df1eb896c00,0xdd3836fe40b7a1b25bd04c02e24eaa300,0x278f23e24d90782bfddc10fd175592340,0x5a59407933792986e9a4f36402bd16e0,0xa773a8e5829ce26455294305cc17ba0,0xfea2b6cdee107ada803983eeb92460,0x13fe1406079b683a96e3509beddbf4,0x14d1f510cd10aeac5cc1bfa6b6146,0x11fb61f481ca62b3fa714f7df3d0,0xcd8c8c47c875576c06474cef7a,0x78c059f83ff4048907d011498,0x39bf48ff97f22d5392def00d,0x1622ffef0c6eb849c179002,0x6a4f8b5ac193f5141d423,0x1817a77c822d9d074bd0,0x3e1978ab393520884d,0x659233479dc40172,0x4f696e87da2103]
def m15 : List ℤ := raw_ints% [0x0,0x108ff69478cf06443c732be36d486e5f00000000000,-0x1b87d74540dabe444a072cce3c424929b6d8494fbc00,0x161a67b6dba8fe8bef5955a1614a09fa0bfdae7e6c100,-0xb6a5cb87c7cd2cd559c0e01351b7e5b2c75a07223d800,0x442fba657081737261919d14756d6a61de8f75acf57a40,-0x139a3c9dbbb1f5f6ce61ec3a141fa3299316cec9279cc00,0x483b1b9ee0fcfa3866019cd5c747376ea04bd8ef78c92c0,-0xdafe0abd4345992ea7f2259c176e1d69aa75606a5772f00,0x22cd421bf14cff56a7648e637327d5b06a76ea1d7b6f8aa0,-0x4b4494ccac3af3f9661e8834c2deafab4eb7e583b307ea80,0x8bf2879514157c1dc406a155e0620d0f58d7ee6f6205e340,-0xe188367878348d255356d3b7af47ef5517897a24c743a080,0x13cff441954292922d77ab83507f523ddd943724127befd54,-0x186740289f7cc303afefd94df4c810a8f36b93503e7535210,0x1a6f0f10cfcbc279654823b505cb787a0375a15ac928d6118,-0x193e54951b8d52d6b2b8c3c9dffb9243eccbbb3a1f2be8f90,0x1549562e31835d510dff8c5e6ab7ba98f0280c63cc5717ad8,-0xfdca2fe99726fe32525b532c76d1dbec885a6dc57f11db50,0xa71da79493341f6f180803605060278cc3ea461eee2f5198,-0x612b408b9425724b2f4bed71a8e2d8db5711285625c1f150,0x31d07189cddeabc5c9f2d3395417d5ba6a17b89489aa63c1,-0x167716a1dfeaad5e7c7763b32317d4a301d34c875e0ba9c4,0x8e28cfcf7eef1c365260b4525e6b68ffe4d021cb8c2b7e6,-0x311c672838daddbce6e732695d2b56440171c28ddce9d24,0xebeed1e022facc5cc83beba63c14f906773d484f931781,-0x3d311f025e506247550460c1031ba63d50375be0b9df70,0xd9b4e9990de0ad6d0570a76084277eb7e8d838f017038,-0x29202d46f2d35852785d2c0655a73c1daf0e64697c6b0,0x686e11afe9069b8a84cd7636c55cc280e115e67b6e26,-0xdbc65bd49113b53622ade111bd40ff0b47a2c8adbc8,0x178f531ed07044e95578dd76d21b7ec79af20d8013c,-0x204123c4b9b1c532d60db0fc254e5c1b78d2a49e48,0x225492cffb3fb2f3d2d814467d293d8529bb4b852,-0x1b76d6d06f010571e00bfff966f496a4b9e979a0,0xfcc625307341655bf76b9ee1bc408db417e500,-0x627dbbc80bd025627117d5e41101a76126260,0x17ea3ce63fec96fcfe2376f55cdef3a95b85,-0x333e7862cb707c3ddf24148eba0f838184,0x31fd730e31b662c1137cde4a6a9741f6,-0xfd0bc1bf1c1b685371eebdc777324,0xc0b93a2cb20ee8e51ebcba4bb5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 22 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 49 indices rho q15 m15 15 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 49 indices rho q15 m15 15 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r16 : List ℤ := raw_ints% [-0x6ca7f4052a05b5e2f86c7bf55dddf7200000,-0x9ec03ba459986207d47bbab7112bdf4a0000,-0x6d8bf7aaafbc3c4dbde8e80d197073c50000,-0x2f7f5210f100d23e5e6173e374aae821d800,-0xe855219c4dce1370dbe5b0b4dad168c2e00,-0x354544199d9109fd66bffbda69df22b7f80,-0x9830c888e15ed749e9c7280bf7f0e4ff20,-0x15b04e138594949b20f2450849436c9450,-0x28200e351c3d53d3ce6960a5894a83d60,-0x3ce4f5eb09cc3f6dc3a9f44b724b2240,-0x4c53b10c1a5c82e0a804f50343df55a,-0x4f4a0fc1f8f025bd7e25e51b07ccb9,-0x444a3dfe8a41cf7a63b19ff727bf5,-0x30a2a2ed81a62c713e516d88a33f,-0x1c784166ae91dbb94bebba33e39,-0xd8f61c6904b23cd05cdb496fa,-0x52c8a1f4e6d2df7abe0a28d1,-0x18b6ebee8cab2b151d9033c,-0x590d8779ce1878f5f041d,-0xe3d7fcb39ef64f17731,-0x1716134af792faec8a,-0x11db5bf2b147a411]
def m16 : List ℤ := raw_ints% [0x0,-0x1cfbef83d36a4af769c98ccdff3ec126400000000000,0x2fbc568ad1c319cf0095fe3ed15e31fa38ccfbb68d400,-0x25f619c3f942935347ed98b5495778518b186b35565b00,0x1369e0320796aace54b6d751efe653680e41807cccf8800,-0x72c9451ae155e3bf9bc4b6984372df27b5e2f893dbcf4c0,0x20a750991bbbde26e68930b168d0e44df519e4675d43b800,-0x77045466ca8ee5f45777e624ca2746e12cc8fcbc446d0140,0x164c97fc833be1087917a07b232d6195eda8af3eb5b6aad00,-0x380a173fc80ff120baf68804f21d61f8931d1cef39394b5a0,0x77bc01bcc85df76aa0254e04f8331af61da774b8060b91680,-0xdbd3ff7f16dd0d69556aec0bacaca352c1945399a62a2a540,0x15da2517f26a0f421ffb6ac5828617ccfe51d9445935dfe480,-0x1e4bd92ffb8a4e6aea81c3851811dc1e3accd7ab84fa59eecc,0x24c97f2d07f810fa2799c48b182235fde3f8b699935fe4bb70,-0x2741f02ee6fbca078e944b3b44f74c71da861e054ad7fd2028,0x24e8b2949b87a2e532553f5088a5d33c9e961ece8b6029b5f0,-0x1e9e55ba785d6cbd57dbfe3d888f384a7bab8070a72a1e0af8,0x166d75b3c1a51eeea44acb1d4c104304efb8a4e914c4913370,-0xe8112e0113a64f9eb6f446edd03f667c2d6c766f43cdd2b48,0x84657a5245cce7f87174a7edaab29b42808dfdd5800b4f670,-0x4286fe0b037c02fe679dbdfdbc970caa0d619c44d6245cae7,0x1d5f987e5f7692340fa2cbca9f65fa2acbe34ff3e66f95f9c,-0xb5bf1b88e4621b14700be222745bc41f26d4f94a49f1936a,0x3d4e563a3b7f2ce0b1d4893c2f8ca48dd84711af53661a3c,-0x11f1f2f30038041b5bc6a952fb92e1911e3d1d7723ee7eb7,0x48787d94cb087697c98276d81455a673909c731d7bbf990,-0xfa6c2f1e4721380d0ad26a426f67e783d18487e2686048,0x2dd7f1f0a4afc3d021760222714dd0a80564a79195b250,-0x708663f1ba6132bc0149ddcd3ac7f12b53d2a4283bc4a,0xe43dec629ec2c11593a895f23c83c30a275806ac3ff8,-0x1780c68a3956d7ab1428ab9a9bd426cbad78ea6cd664,0x1ec9a8bc161fb722e17c9f8b420e99bf9a823bdfb78,-0x1f362c732a6fe8f73b4d7f068804e5e82637f426ae,0x17a780d50df6e4308dd07626cc16f4421888ef4a0,-0xcceccb9f17e4408487a18c105554b6b316d3da0,0x4a95aab79f89ddf5487130e86d41ef7666eee0,-0x10c2fbe454ba207d4a08e04833312bc7f5c43,0x20e064cd3f935e66c6b04210bc57d5fe0dc,-0x1cf8a4a108ea226261c7f4b551bb2815a,0x8260d5a079aab5f5d69aa30a12833c,-0x568b3754a79d5f3b3f3293bfd03]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 22 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 49 indices rho q16 m16 16 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 49 indices rho q16 m16 16 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r17 : List ℤ := raw_ints% [0x186ecf1ad4f24cf86a083b48e1046dd8600000,0x23aac442f2bbd052a1a7dc0686381876ee0000,0x1896e094e41ec5afae7e8cb85d0f65b4790000,0xaa69122e571587f8adc93be1700850b9cc800,0x340a252f224a30d020912ab14de75b0169200,0xbeadc5469f72391f643354e98a2e48678880,0x220076202d077ab063701f00346ffdd221e0,0x4d6a67c33118747788a2453828dd2c6c110,0x8efdb21db0d9bb4f53176c6aeadb765e70,0xd89db36ce639bb8070d7e9f8773a4e140,0x10ef9970a33b445ca2846f36ebab132de,0x118df2484154755a690eba48bf699825,0xf1503ffd6dc924983c78980e21ff40,0xab63243933107da11db9d780abe60,0x6403b4c5cd69e03d8e3869900362,0x2f783fa065e8bd4b9c51f382ead,0x120a4f614d8570e85c679c4ff0,0x55c76717b0e15e4e39dc3e39,0x133739005e2a2550111db84,0x30dc7bdf5201b8b38453e,0x4ea3c25eba60198593c,0x3c4d1fd0509c2d107]
def m17 : List ℤ := raw_ints% [0x0,0x32b8e326b1fa0330f920b6687eadd202f000000000000,-0x52ca41c4ad88aed5e76669a6e5c00bbcf349e8c40e5c00,0x413ac0b254b56248c228d241ab80fb0e7f7b3ea201b9900,-0x210a39927b23963ea1d3d60c60ce06d27a373e1275a51800,0xc16c7da19d5151f03526904086d13243c72d9b36ff206040,-0x3675f8136a57e6bbd6cee63b67dcdb8f151ad0788b56d1400,0xc465639bb472e0af258d5ce07d2d78867feac1c5c4d150ac0,-0x24647610b34ad72dc6d422a11a91108f3e1d9211adb4f9e700,0x5a69a32aefe1c4fee60e280792913e8adebd12a4dd147ee320,-0xbee29340ec7c6cf972ac823eb627b888e84a91bd8a1fc8ac80,0x15a223b1171de84dd73c84aa8192c674ecfe1ae0eea12a56e40,-0x21f7288c5a77273ca4978e538fe898c8e1dab1fbea8183d7280,0x2e75a7bb1507049dd04ff156476f229ced660f2fea3569f9b14,-0x379fd47d7276347cf0bc3e594f1a9687f2617b3849a95e3b310,0x3a7df88e26065b060d0913eec9d95dc331b89e065635e414298,-0x3626b824daf9e280b534d8c9a2f0a84e5abae370e1483c84890,0x2c33946b75117caced45c8f6f45556d950ebe1de08a71c5e278,-0x1fd4dee6cf30c955825126ea56d9c3ff124ea04fd591f877ad0,0x14389a237b75a6ec4cde89a445667a61e93c9df18449b24aad8,-0xb5227eec5b04885bcfd1366703a7f131576c1529c454a16cd0,0x593922305795f7eceadeff009babe6bf6d6845085fdd9a23f1,-0x2692832c79e0252f1392ab0ad54785c7b32e11ac3094b26204,0xe962037ca8983deb300a540ca02d3209d8b49c90629975e46,-0x4cdf11485529f26205d6c0a3c8a877ce81869ee93fe31b364,0x15efcef0846d7f840c25d949888cfe0de69d4dfaa816936d1,-0x5636b035583c26b5f4b489c9a90a25ab2b6389d45c3b7370,0x12155a956013eb7281020dcb2f4ff85d27473babf32b3938,-0x335332d570b4e4127d261dd763e24bdab53eef377bcdeb0,0x79c20d01813c10005280bd5b4fab103b03e65f95e7a846,-0xedfc811ae2c855c9f62c838754ec697040f8da3669648,0x1788c7cc37499805365c5040b01e6f74ab1adacfd9ffc,-0x1d7cfddfabffb05426eec2b4672ec5024e811c40f8c8,0x1c7638a85866532b03fe938acdea854f4166afd8512,-0x146cb5608755f577fd7df288e394795cc7d54a8620,0xa676f008fc9a295406d87953aede78badf6d06c0,-0x388f52015dedd2b818022d2e2f451211f56dee0,0xbc1de9064d1f238b5d2a86688884dc3bfcd75,-0x1518fb926f6fb991e2a82290dfc79165c3c4,0x10c97adb7dcb67cdbe133d3bf2f49bdc56,-0x4326666ce2bd74a8d0f1f5f03e76f64,0x26d99b99e6b0f0e2c3e503b5cf85]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 22 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 49 indices rho q17 m17 17 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 49 indices rho q17 m17 17 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r18 : List ℤ := raw_ints% [-0x528200dd8699bfc78468fd0aa034854c0a00000,-0x7859e2d8773c523b3a688d308c80c7e0be20000,-0x52e6ba347e16b2965cfa39c54828d4902170000,-0x23dfe7caf6301518509087f25b55808684bf800,-0xaf1b993ccc2653da72ee02907e35bce157be00,-0x280e743616d8ec3fd562297a4bd6885d099380,-0x7225ad72156ad9a1292c057136c4b852fc720,-0x1038bb8ecacba58a77cc52ce16533f59d4a70,-0x1deb1e221a0f822f89e7ee20d7c38ea0ae30,-0x2d40111efe91597a39274384f609d4991f0,-0x38814b6fc475b56e76550a22bfb7d4fd72,-0x3a741bf388fe7040850fd3cab4db0680b,-0x321c76c0640ddbf616be65c09f063aba,-0x2380edc6f28807da284816b70629fe3,-0x14a9769ab4f35b46f813135d59c597,-0x9c6d5d0aa7333379da49c02cfa48,-0x3b3e0313660d743977d732b3359,-0x118941ada3517ea86abd6104f6,-0x3e91f398a0d6161dbd1b6507,-0x9e4618c619f0340da2c229,-0xfd30b7a2706df4fb6a0d,-0xc0c3a798edac64024b]
def m18 : List ℤ := raw_ints% [0x0,-0x58c38d83b7758595b3f93f36ddb02f8524000000000000,0x8f9f12822111b0c7fdb5185c3379fcc29490b8cad83b400,-0x7023ae385f803d11b8d401dd5f57da71862c497c62e92300,0x38458971ca41cb08ebcfbe80570a44d928669172dfe554800,-0x146401c38442c94985fc0fc83756be8d550d16944d095a36c0,0x5af10988fbca5588e7a6f9103224f6cea07ca71056b5579000,-0x1448d56dd3f7716b1f446f727aaa8da22c6ed0c7456ec7d9940,0x3b7e142cdde8b136ab9ee182facffc8e18cd915532753459500,-0x922606217a599704f659fc9313feedfcccbab32603311baf720,0x130f7a853e3de2bdf0427e5e21f55b3bfa6565b86d3c5af73c80,-0x2224c6b430d073e2e2f52beeaca7b19f2ae5535601613c7c0640,0x34ee11c20fe9137b5f2795f5ae1c27f29422c25a57bec4b5fa80,-0x477201d9dfcdaf7fb7e8174275f3301be7a5196c3849f651a10c,0x545c21f4bc9a8b21bb681309976721fd1ea9549fabcbd104b270,-0x576df9ece20a24b816cb26cc26b51c0c91ca8dfcad662cc252a8,0x4fb7bd3accd2456efbb357958447df26d12c1d287e567eafd4f0,-0x4009b807e0d5c1d4fe958d83cb90fd57d698f1bea78474d8a3d8,0x2d58f2414ad201a2a28369fb02f5c66623b18bf0f491d543c5f0,-0x1c4d13d09dd0fccea2a664c70060b5e382fcba3531b3e91de108,0xf8d055fdf4e062aa42403a309ace6ccad9b76e577b137eaacf0,-0x78289ae9359068623284708cfeb148c639387c01a98557e7ab7,0x32de11c723259f048b2d5cf377bcf91a53ea90a552a428e355c,-0x12cfcd5c1a38346db45a256639a81bbdcd0fe65aa88630c260a,0x60cfa316db35fa5835a7d654da167ab6d8fe4ec4d0ca34b1fc,-0x1aef316d5647405bc714554f60d185febe65ef595ce8a30fe7,0x67034f22ed0b35ecfba7f9cb065d9272504df6d4bdafe0190,-0x14fbe1d46db0c4d58167ee823f22240a1889a5514a2777948,0x39b49695457eb21daff5031a9b11ff9f61f860c11ba4b650,-0x84499bd96b04863ca7bd584fd0109ca936179687d51262a,0xf91c624cb48c0d3542640fedbcb58f97c0ab3b3ffab978,-0x17a69df4dfbbbe04598232b4c89f73a92f63f7958d1da4,0x1c5616daf0d8324ecdbe41c5dda63c71188fcbd7714f8,-0x1a076290431560a0b07de806ec0e2581c165366c9b6e,0x11ad9f7991d1815c87abed1c586ec77c09cd9849220,-0x87794aae59b7aa17cac248080ff01a674fc596ee0,0x2af22ca0c459c143397121170d62b5cb7aca1c60,-0x840b95eeef6298c90974fcab59caf48c271e53,0xd8a8f5ec132fbad626127c72ba84be45849c,-0x9b99fc2536a3578b2f06cab4417651d3fa,0x22926a2ef7e3999a3b853530ed660cfc,-0x116f2e4380b1fe1b4b9577e132cb3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 22 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 49 indices rho q18 m18 18 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 49 indices rho q18 m18 18 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r19 : List ℤ := raw_ints% [0x107c06f1378e569cbc6a97542badd437a82200000,0x180731ab17d5a9740a91ee35adf0c6c8cc9da0000,0x1089d0fcf2e72f83e5e3426ed09a7466a2f2f0000,0x726952a40cc7f8542a201c6b294a4e44627d1800,0x22defe0bd8f749f3231adc2d1fd52a926b943600,0x7f8039b3c7d348a947b49593e88d95d6275c180,0x16aeebfeecd29c07ddd3dafc36ff175b7cba1a0,0x3383b8baeefe2962ec2d5c168f957ec1b9d5f0,0x5ee2a59aa239a44a9fa6ac51ad44aa094afd0,0x8f4d13f4f3fb089cb2eefea4e5439acc5cb0,0xb2a835e8ab047acaa0f77b98f603d6d9f3a,0xb87dd5417ddce8e032b34a2845a88ac273,0x9dda36fe17bfe65d41666b0dc550ba3b8,0x6f987490bfa1301fb4b5ee8eb96672bd,0x40c9c5f3cebbc9950988fde422aaf98,0x1e92c1d89d1cae05d8a60bc07d31ab,0xb8b290b6c96ea236e033a1568d66,0x367c07289e535321641e17a67b5,0xc1a59c3811f367bfe572cd94a,0x1e7a7e461f8671028d09e912,0x308188995d3c11b626ebd6,0x24b5876a8d024d6c08be]
def m19 : List ℤ := raw_ints% [0x0,0x9b5637a6810da9c5faf42ea003f45328ff0000000000000,-0xf935856681352b5fc8c413bc12783232e03b37d64ce3fc00,0xc0e06f2f8dcc57e5946c655de6a5a2f83aac7dabc6e96b100,-0x5fe83448c525d38dfb0ded2774b5fcf3f8357c6294b7045800,0x226d0ac8063c4037f321f9ff19be66fb38784aba58933f55640,-0x980a17a87b5ed924e523297996203c4221a230723d43c379c00,0x21918e921864949a4ebc393d02bd03122b7685f21793f28f22c0,-0x616a804f78b2e2b8dca677bd0d646a7b13bc27c21dab8aa0df00,0xecb00b8b12bf82b860f865719f1701cc596b2c5bd4cffd7affa0,-0x1e841b6d6e71dc1d857e405859dc782c0b2f70d9de2278fe37e80,0x36038a61722f7d598be25ee7c308844aae3efc9abf61e543c9140,-0x52b15cd96a37189966d43a7b30f2e1efd2b4d158e2f1f64ecd480,0x6e2baad341bd238e9a6d86e8294939e1626258c79a26f296600d4,-0x8051785edad7c4178f9023b0980cee6fc6ac3e7391d41d7ac2410,0x83184b2b3d7babc75490e6fb0587a202a5585dcd41dff8dcffc18,-0x75bf1b9e7578a2d24460af8ff738dff0bc5c39a6001374bf09190,0x5d1a3b206b212921cafb655078802342c998c94c67b7cb0735f18,-0x40d7040ed1532812de53239c6158607a0fc56a78f5adba2a42e50,0x27c2e583960687ce6a22f7300d40fb402317da4604e79e7632218,-0x1572293c0a0fe4f8b77205e5b25dc896baeb15741e82d9659dc50,0xa27af5bf656c77e8b059f8a884b39dcb358b40af1e5cf61b7621,-0x435caa552ef3f7c0ffc85b6663e998678d2756104c503a780e44,0x185d35b7bb6d1b2ca1622f1c80dfdfa3285bce7044c9885d42a6,-0x7a726421f8626feebfca68e1436d50badf725dbb9be20c05da4,0x21368ce4302bfcd72bb3302aa23c17f4b623a562cbc95c5fd21,-0x7b9d2ea7616fac85074331ab4b8009f4c17f4c54c1704c7f70,0x1873e489cac2a5ea7de31a740353fe8b9c3f8acbb7d1cc5638,-0x4125971c1ecd3f76d1599821e3ae857560757f27ec2a52eb0,0x904c6e0587896d69672c1910ba3d0451060796a31cbd3666,-0x105bc6011e71a9a4e063fc1718754d5eef0384793790a8c8,0x17d9cf50d0398f7e1f3c2dccfca61d908013dfae7a742bc,-0x1b50a0de7d8d4ee9266fed5295a8c0382e34a51672eb48,0x17de758192365245fda4126bb848559307087f426a4d2,-0xf55eef7d2b8adbe3dd3587ed34386b1cbd2c17776a0,0x6e7181a18c1777396f84c86c0c7a13162e4f081e80,-0x20a5a86f1e863ce490b55dcaa55708fe8b7771f60,0x5cbe73ed371111f6658787522a9b40682e78165,-0x8b143b958089755a04aeeb08fb3340e57ea04,0x5a1fb0de4b1c9969a1fb527c35bddf67cb6,-0x11cae9c5c6e5c2335408789e6ba47efa4,0x7d240d1603b40db22d278758c8055]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 22 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 49 indices rho q19 m19 19 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 49 indices rho q19 m19 19 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r20 : List ℤ := raw_ints% [-0x323a43e7b85ce972b1ab6f5c4d7490498e63400000,-0x492a1af83f0986219d7e18fd801a90949bca040000,-0x3252894afb8b92c57ca0034d60fd30a5adbf400000,-0x15bdb363003b15d9258927adaf64bbd055302c7000,-0x69ee919984d6c8042d4e22bd0b03c72bbcb82d400,-0x182f74efaf7a88eb9f311af4609f9a2b53fc10d00,-0x44c644d8f574261059a062c64d908cbe1bfaefc0,-0x9c0468bf30567159e6d114bb9e66c2212736800,-0x11f0631f4248ff5d111a9f6da6749ec95722c90,-0x1b0e876ae889efbea17be1584c7d1f3f4d1ef0,-0x21aefab7bf9ce0f02c9832ba13660be306f54,-0x22ba68af3b009564b14ebbf1a40c760072e8,-0x1da95aacaf05cd0b3011fec248a4a68b17b,-0x14edca77b12d6dc4bafce5ee1127d3bbfe,-0xc1fd6786bd2cd386a7de46da77f4eee1,-0x5b52dc8bbd250770b9652f7f05d4bdc,-0x22638d3a97550dfda88ee0e8c52141,-0xa1d2d42be5f5806fa756fdc52146,-0x23d320d1c2e77628d7563e842cb,-0x59de6592cd97c379b304359a0,-0x8e64ffdf7be80448f92cf74,-0x6b3780de0d464b95239e8]
def m20 : List ℤ := raw_ints% [0x0,-0x10fd6e16361d7e91a772b519806eb9187be40000000000000,0x1b08637e8127e870aa8e737e63778ee2044102e39a1c0b9400,-0x14be5f6eb25dde1a712df4e3b3306ce825815fec5eba9e4ab00,0xa3932c5daaccde586d2980ce0246513df21001835a012050800,-0x3a2d27aa6a83166d4ac83267cdfcc6bd3bdf17e0661ae4f728c0,0xfe7b50eb827cd2e5b2a5d96387e076de9bc2b35a918b39532800,-0x37a13bda730eb2174325fa76a3e80a832bfacdbaaa81a03111140,0x9fc5e1ff28d50e6f3290a07ec6a6dc72e235ccf3d94cc05ab3d00,-0x180064a3c5335f813d187aba9be51b76f41551144876256f60a4a0,0x30f52cb441cfaf802c1beec02bef8111a34cd58d9f156bc9101280,-0x55a4a04dbb7ba2c3a4939f94a2670bbfbc970ca94f624e42efef40,0x8183b8568f207d7e35a41cdbe23df4d7936bd80e6b88d57ce94080,-0xaa5884fcbeb4fbec76ad66decebd7ef7ff9e3daf0cb4f034445b4c,0xc3bffafc43419103c90f4c874c892e591f4384c2593aad77ca1970,-0xc52d6fbe54e517f7d6125d60b7f8697dc3f067422e84fc3fc0ed28,0xae7cdcc312ff2a325b6cbcf471e0f52b8b9d1289070a115000e3f0,-0x87d38272694afbd0a1b487351e628454c98346b5ae41d8c69523b8,0x5d0bed6b885a405b31b42c3ec6c80d2a2888218dc1302325b17470,-0x381296c588570f9a1230ae0f2fbfde949f349d4e399ac85bec00c8,0x1db0e68a0f3d3f64a9f0333e850febf4c9deec94dda35ced3f1f70,-0xdc96ee77a7f96fc1066ebcb2a677f8fcdb66d5e2b1bda3f1f7c87,0x599234a052394b0cd3a50447eee6dd64dd7bd3355e034b5cc371c,-0x1fafdaa0cad5f49d6ee88957b0366ed6ff6a1c6b0b0833ea0aaaa,0x9b86022fb476bbb02b7f0b10f9bd93b43801bc7ad01ceeacd5bc,-0x2920e0e3e6fad5e200a9282cbc3ee7c751ab59a8a84fc4baba17,0x94f5227f783640bb569e3fe92210ceb5a5156eb5b0fdcc47190,-0x1c9cd5332b2455d9c0536aa390ff326d406ff52b2cb31b3ce48,0x49d7ee6565e76b60eb627875f3248e268077adc071637a6250,-0x9e01d5fbf5c3e9231ea4904418e1accf8e66864ea3b3b740a,0x1140042a703344955d4b9d6f989062fbd03c758097abb5af8,-0x18221b995fd5b70cb7ffd3ae22e52b13af5017f1a83a60e4,0x1a68e4e3b8bb32dd4762b2f49a75023a7c2477ca6661678,-0x15f1fd7b67eed1b7e4d95a347631bff56eaf940cee192e,0xd54f5d96488b2c58eea13f55b48997b942bec7fbfba0,-0x5a2eb8b5b3c4848547352e849aaee02793388373220,0x18d82c32c46887d29c32344a501d76ff38e0e1b5e0,-0x412cd8ba3db44967c359eee47ebecd375f82f263,0x59491ffa9dfb8121e09d26d231c56d7479a45c,-0x342fefbb2c5d61a43c0586c88a01832a709a,0x9275a494abae2d681d6e3cd23316372bc,-0x381f679bea90161ee94e7c381ce763]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 22 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 49 indices rho q20 m20 20 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 49 indices rho q20 m20 20 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r21 : List ℤ := raw_ints% [0x92b353ddfdc488a388fdbb3e8810b1dab2d07000000,0xd590002f3274d261ccd57e7aeb3f24ff383bc700000,0x92ca73dd9845ce9a66be852eaa5af37c6cba6340000,0x3f5f870a4a3392254f54c3d71f23ddcc32138d14000,0x1348a84cb8634d5002e028025f61e7e70b6e9bca000,0x4662251612f1946324405fd9e3df06acb76f92d000,0xc7f5bc5f0d1e48be8857eb9cf2b4d735b9590a200,0x1c528a516c2d4ff2e6ff16a012581e278630db3c0,0x340c207a13ab355bb36bf8b51c5b24d02f5f7600,0x4e682874e298cb4831ae8eac45f9cde1bda2470,0x617b66dbae997880040da4b441da607ad60f40,0x645c45e7054782fb8c97e9389e1b1f0a42944,0x55952b50dfd794fb70d65e74dd1749a8b540,0x3c47e54bcb0655dde615c0e77876adee00d,0x22daa7787fb38cf286edd4b0872e35386a,0x105f7e6e680e06cd67d0cf6d4296a408f,0x626987c470adbf4ba766beeb2bf0134,0x1cdde06eacb3844b3e51d0a63f98cf,0x65f1a2e66ae2e84bcd6e53899cba,0xfedf75e7f31351ce051d82bb2d,0x1924c364e4cb9d884792479a8,0x12d978ee760eb3625164674]
def m21 : List ℤ := raw_ints% [0x0,0x1dbb80a6deb39d7ee508bceca0c1c3ead8cf00000000000000,-0x2eedb523b0a01ec1dc7b7c5dff824be50abc8be0140f5389c00,0x23b62f627e52b44def59a456ab2d92b9e0149f752912eb1e0900,-0x1172db8e95109ab6141160d0c4509a1fde1e6e8b15a5218919800,0x62670b6aa32e2cf51c11512459932201ba574d48c200a8251dc40,-0x1aa6fb747370d48277b23a55e5d4424b1cdc20802a29a8781f6400,0x5c50ef5261aee4b3e84a5fda373da5d940e956ff3a244e7ebfdac0,-0x10676a31af3df1826de6d341d55445f1f35144d019ab92d3a921700,0x27035d04a7324fc208b8b293501707b6d69c27bc95939a00132c020,-0x4eb43cb2791664f525737a063ef71b8e09a3a76aeeebf268d5be080,0x881961f657db476180d9f4d4a8b35cd7e92d34978976a4f98d08c40,-0xcb589c7b38728c32d8902b7f74cadace619e623583095573c894680,0x10817172a1234f8f111987a588099cc4a2b6ef2946f3f3adfb99ce94,-0x12b78b3679ab34da5408c403f56634a5cb2449b9fa2abe467aeda510,0x12979d26ce90080b6e1f93080c559ca6911b9246529baeb0fe410d98,-0x1036862a9296fc1999668687c481a1ac103bd13cb0d0b9a3a1b86a90,0xc6d45cca01b8f973af50cd0ca22c3afdc5d58a5c3628d2ffe1c08b8,-0x85ffc7993bd17f8eb6d992604f6cc33326e6ca9f8039fd64e70d5d0,0x4f5e452f607106ab358b0c9c47c9ce84feb548678123405309f0758,-0x29437725f9c5287c440a684101bc9afa13a2db64347cf46da951fd0,0x12ca964cade2b763e3e4691dd3eb7c5d203985ee7c40cf5f5e0a251,-0x77952adcb32d774b09eec362c3de9c8cdfa5665971c4291d7c6e84,0x2961242d69a785053ab6ceb6c242e37ae81685d1bde8725ccf8506,-0xc659e888271b23177f6ab04b0a97282e3169f6545c173000e5be4,0x33240b919f790c922f41637841b6869a998f1071ecb3f39c28a71,-0xb43bdaba7660c1e376e4b4b1dacc72ff6f7dc6fa28e2e51bc370,0x219d7f75d8cf667bc62e1eed22b284d579825d11beb0a0776738,-0x540753d91a2d2d28de41e51cbe852c136aada681056923f76b0,0xadaa7829233747486f8846b7dabf62b9571a8948a493e48886,-0x1241150980dd2b6e3848c5110effd3dad64917d07c864f1348,0x187f7769de72caeb77102d7521dc29754ea33e640dfaf697c,-0x199baf29f68f59fe83d001a5ad690506d9653e2b1d7275c8,0x1439f9c829562dcb8be7f89b137cd017573768f44fa2f92,-0xb9cf4f3c505b1ed77efbdcb29943a78ad99ec985e2b20,0x49bf99acfe184faddcd00e73d6b65b1de1654e2a7c40,-0x12ecc5174cce4224a077df5f911c5517f97d6e403e0,0x2dd2a271c12142ec4316992c8155e7a4858989f55,-0x39526a22216bd58d1a12ced3717fd4167dc3444,0x1e365736234bdffc3e187dbc5687bc8018316,-0x4b524acca2b622063a4255e8f4299533e4,0x19297b75712b34a1d48e93f06622e25]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 22 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 49 indices rho q21 m21 21 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 49 indices rho q21 m21 21 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r22 : List ℤ := raw_ints% [-0x19ca808402b75b0c7da3830f2cfcb9256e82113800000,-0x25865302d277cc9fd210acc4c3755628f2a95fdd80000,-0x19c6cf883eceecbf19c1a8bacd1c8fe8f704bd02c0000,-0xb1efa205426830676da17eaf88d1fe5915123500a000,-0x361aee0726d40a641e13230273836c5258324b624800,-0xc55289b8f4d0966a7e8ea14cf67b65d09882bc7f200,-0x2301e68243b2aef89772fe2b5126a0f0adde7de1780,-0x4f431f8dc65e215240d8250242ce0ecac067b6f7c0,-0x9182f1ac01708a0d1eb6f737d1c2844ac8df3db40,-0xdaf73339561a221182de25d38e79595dd89ea280,-0x10fe913ed97cdc68b2d657d6c9080f8f4f1cffa8,-0x1179291181088901f33621fe8adb434e46a6b8c,-0xee1064f204db9eec46a33f6aba9c01d47f050,-0xa76af498b44f0c0b926d6fcb53919205e304,-0x60a1d0dd2cf2d138cf5f2f85e88fe9f9ba7,-0x2d4e82bdc6b7f1eebcf573e594d5b0184e,-0x10fbe38a8365d9c27ef34ff8fb488e4f9,-0x4f853ebea718a2c9725ed7f842a8ad4,-0x11816b63813f3468197551a521e631,-0x2ba2f8a67d17ee9a029700419ac2,-0x44a5b6fe568ede65e1788ea1f7,-0x3344b79bac07e3e94d5b7acc]
def m22 : List ℤ := raw_ints% [0x0,-0x3408212405ba539e10cf4a9e195316dafb6a400000000000000,0x517c58d919bc8f4dae3bce71e092d2efe058244a21d9dcf87400,-0x3d8205545bac97f994af859d7c50929fb17eb639ec4aecc2af300,0x1dcce31829a3c54861730dd30bf74e6c0fbcf7505d19af7a4ec800,-0xa697d01008a79739bb65e8044c75f4ec89f419b1ef9028c0f04ac0,0x2cb62b2a44f3cf6c61f1936d42ba1d56748e732183917ead2d88000,-0x9967096bc542fd287a7f32776e0d425745ff1341d1a30269ade6940,0x1afd4ec97c209f4f203d04f05f4f7eb09a442ae4f3fbe46a241da500,-0x3f86e25eda46fef5a7e09e385c43504ba56702b215df9a3401435e20,0x7ec6f636eb09c99bd006be947a799647368a701798444b133c121880,-0xd8c27291d3b63c16b8958c9bc84574301f2917dff7e863f806442040,0x14009ed35b99e7bf420c3967474b93d9f08b45509122d135a62443680,-0x19a7f24de22815ed4f68a8e4802fd3f40dd47983a9b2da637862efd8c,0x1cb710228ac92e86b8468883b5d061247f7d38c2b9cb00b362d4bf070,-0x1c223f10590d6982ee731f179cda043356001a20bfa6c4fe4eb0d6fa8,0x182e21dde2c310f349317873c60a57184ed71ee834aa1918f5953e2f0,-0x1240813a64bef083e41bc968482e587ee354e3f397804caf4cbff1298,0xc1a6f4881235b76dcb08da60be4f1504fd8dc832616cb711ebe9def0,-0x70c068cf5922bcca2b5ba459abf68976eb75e3f438053135d067fa88,0x3990134f59f5bc95afecd1c1f3d08a9435ee3e1246088b6bc8ecedf0,-0x19b633a845dbb9a3f5870af8de3538f123f9ee6cbdfdbcefa2c52857,0xa0483be6dd0973cefd7f711f3cda0cec1c45caa31ae99e2bd63a4dc,-0x36410713bc816a2d4e55310eb884451d0b710151c2a2e300d5a014a,0xfdff694827e29d02ce8174fb39486547c9a5cf8177a3ae9fd2c57c,-0x3fd9230bf7f84dbd9490b79362e1819cb964d0855acd84fe4b9d47,0xdaf3c81cc0f63a400ffd6c7ba8dcc4e4b821cd459cf4dc0298990,-0x27a5da285a626b574bd775d17325b353775618fcbeee7d7fa3f48,0x5ffb9cc5cc6586bbbb686b17f61672d11c445a67f0a75380f650,-0xbf91e8df6f2c84212d4b6e67c8aa350068ddaf88369aef6f5ea,0x1361eecd3ce07ebc74e43c8ef777bc33d3b8bc3149ee2fe2478,-0x18f208c6c665fe60b8cf5336aef8ee51d748dec63172592024,0x18e63aeec814f8ad5cc98d4a6771076792a38afaecd60fff8,-0x12af9e1afd9e09096fd7aed2b842b4b568bb417a6cc5a7ee,0xa228d87dea0f884a5cb393d8ed6ce4a2d5aa4355b7d120,-0x3c647ff77d8f79e6c137a29d9cb242920a1360b7bf760,0xe6daa849f48eb02dc3f96b874a72c239ca47dc15b60,-0x203ac6c147ce048a35b6cbab25f03a0a0a7290d073,0x24cd22cadb23537ce9af4cf3177ce9574290001c,-0x117c6df136f3ea86931761384a19076676f73a,0x26b9033e801d6b27c2d01d714f5a384747c,-0xb471e6424c75c4642ab103cccb4dd13]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 22 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 49 indices rho q22 m22 22 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 49 indices rho q22 m22 22 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x3344b79bac07e3e94d5b7acc,0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r23 : List ℤ := raw_ints% [0x4626075c03c0f2cf221a2c9515a25cabc43c85e4800000,0x66026c71866804621f602999f1cc996460864061280000,0x460875566fee4d3f3d733f3d46cd08a5dca789ed4c0000,0x1e3245528dd84d800e014578f04c02b14e6f3b1b396000,0x92cfcd8cd8887ddf7b7581924dbf16f51b1afc1085800,0x21709cc5d8e1dc9b6957d753af427710c06fb947b4600,0x5ed91bbf14b2e189fc257dfbbeb2cb2e41be5f755e80,0xd691724b190dec000ea4eea3578f8dad95796a6cac0,0x1898badcc110c6c8646b9dcd25d9b99f8cc147fe940,0x24f9ca9d2b86c2b1c87ebf2e928475cc768dcfd440,0x2dddb36126cd6ab8e42d9c53dfacbbca2314246e8,0x2f1a2337e3803d7e68d8970d33e520b140af784c,0x280e6f9f3f1e77afb7ceb4a05a28070379efe20,0x1c2114909a4d7d9c475c90b99481d3d791bdac,0x1035def31b6812901260390ce84f2845d5688,0x796556a67ede18eae5b39da6e21f8853b21,0x2d6b9b0c6c278b586a67b079517a0f1eaa,0xd436877926a1c42f5e7f06e759dd937f,0x2e9b48b03e96ec05dddf5d95123662c,0x73df843e7d5ae823f009733057813,0xb5c0502bb81042c78495a470c5a,0x874a122c728ff5bfbde050ad5]
def m23 : List ℤ := raw_ints% [0x0,0x5b0e39ff0a0612549d6ac294ac5167ff37f9f000000000000000,-0x8d85767ce2df51c687d0ea61dd6becf82f7a2fad191fa4e343c00,0x69fc1b52bc5efe13e70628cfe50aa201471cb9b898164f8887a100,-0x32ede9f4ad3702411cefdc66a9af6b3d60908f34b2bef02101cd800,0x11a497ea2835dbfe41ee93a6f4750efe0f0722eea2b400f192f77240,-0x4b172cafd4cb9f6c3d1c2f18ec69bc1f2186b8d347f01c8ac7fa6c00,0xff3f4c89a44963e4099c34ecb463a2d05d61df1ec4d377a0fd0432c0,-0x2c7967601598ee4d622e7ec1d6573396b71e758bbc14d731a56038f00,0x67a01109e59b5402cbb1b685e0c89aa9148cb4fa82c6aa854c5da04a0,-0xcc9d8d2209ce3f952af04c2fe2484f2fd87e9820418ac748509895280,0x159f994fecdc8f939dc43b36c81a14898c2a318d4d9e6ecebcdaa49f40,-0x1f8e526a0c8f95ed73053ccf680f69235d5015532fcb8f20b4867e4880,0x27fb66d0c69aa221270868288eee214daeed0c5edddf829a0e375fa454,-0x2c2d0c076cd4c4fa380c4d36c93c948719478df39b0eef9f9012f93610,0x2ab2a21a25e9ed7f3eb814684922e9eaba58df8482f0c12dfb6683f718,-0x242ceafe01d91c01d3df7def9c7b97428f999615911cc5ec0cbdf0d390,0x1ae55e42ca0291aecda9c36c7d5e119b208e1896da4f156abbc8ac3758,-0x118d377373389fe15da26b898329459cee8dc1e450aa9661f543335150,0xa0c0360fee732908a9f646f2c0c7ee2abdbb457d155cb42db29002a98,-0x50991a6007c8f02ccc61b0e3847d2005296ab41707e0a8d5cbe121750,0x235093318623f86072e0dc4dd0cc51ad43b3d3f2c23d81051b5ca3081,-0xd7ab66464243e2a0a915e1abfdf5e7c3126f48c2fc3ddc403f4742c4,0x476a4019f7ef5386db202862291f161da1d988ff2ac5f2570e394566,-0x1468c49f83ddc94fdc3efac6cca7db5fa85f9b8a60b3db2b69876e24,0x5007844c72fe26627fa13b1e0923ae3f6fc0c1edb4b7448a7ce7ec1,-0x10b08400bdd2bb5c5a42fff87a52f0e2b2f4c459f6e3171e221ff70,0x2ef15286c2015d30a8a7524e393be0cfcb7e027ef7ec8d8b920c38,-0x6e0b56e261af0216b95be413beabea824480430fd04e6bea476b0,0xd410975c1ef3dbbdd10da409520f2ee3cf6b6ed9cd7e393d8ea6,-0x14a5f4f32307d7619273321c8216407509b192fa4ee218f3d5c8,0x197a248e2cf2c33db773e5185d0ea8730b74715b45092de943c,-0x18462196eca39c51f3d0349f0933a6e017e3c00ef7f8739848,0x114d1f401014a9c034e70315cbc5686353614764c19277d52,-0x8dc4fb02db6121103e65e73af6e7d1262b4d7eed47983a0,0x3184c9842f7b5942da96ea48a9d8405a733937bd4cf000,-0xb02497a067393a6cc2278ca46d28568242edf9436c60,0x16ad2ed5ac0bc3aa03cff589ac71260b0262f648f45,-0x17a0526df5baa2d08f9560d86a23350880c38e284,0xa1e285aba92aee18deddd11e3d571f67cd4f76,-0x13e67f0b4dea70996aaffa87ce19b56f7c24,0x50da73c1ebe4abd811c28e3b4f2fa8f5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 22 78 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 78 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 49 indices rho q23 m23 23 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 49 indices rho q23 m23 23 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x874a122c728ff5bfbde050ad5,-0x3344b79bac07e3e94d5b7acc,0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r24 : List ℤ := raw_ints% [-0xb91c6c1da1f36545f5ce61ad95e5c0aa84d601aa9e00000,-0x10d0e6da19c96ccedc6703b385af5f49a9cec0384cc60000,-0xb89e969339024d64e40c2cb8d2680ea8558655fad270000,-0x4f8ec549da42b24e07b1ce29d07778b00062d6a9070e800,-0x1829037fb4b8c67725da4b1c9b25edb713b0a67dea1b200,-0x57fd873c2beead38426662132e85f1435ff7254fc07880,-0xf964ac1f0f81c0d67d3e2cf2944669bb813803730d0e0,-0x233be238d6ce22912553e14a2d184c1260780d3621a70,-0x40918f9b5b04aab114e791e5431181b62cdf84afd300,-0x60f9b8e25c14de7f98a3e32696ebec74a795d29bfe0,-0x782bc563c702210f78c266fbf9998aa71ed4204856,-0x7b464c8b2ba7a731d179e54ef3544231c3fe14e13,-0x68b5ae2e60541da1a287fc7954b6ab8b5ff5fe11,-0x496f813a57e9e2506fdb2949c2fd167d5045609,-0x2a4268462575e1a41b7f4e3b6602b0403b81f9,-0x13bf981cd72455c5a12e9b9c6ec32c4fe10f6,-0x7604bdba1fd488a94f45fe12ae0a1224871,-0x2265bda866d4b25d8340349d097301b588,-0x789dd62b33386e795c51a4d502fea641,-0x12b2d0a7f3f145ad92dcc6f10bf501b,-0x1d40bba23a856f2cffc815baa268e,-0x15b61529203a3dcdd7f8b4e3dfb]
def m24 : List ℤ := raw_ints% [0x0,-0x9f58e57e518aa014137ad4842d8e75fea1f564000000000000000,0xf5d790ec2bded1e90c5588081df167a8c0afb8b81a65663f825400,-0xb6b3cf34aa04fecb910610cb987202bbd2306361a1d4723664dfb00,0x571885b4653dda332ff7088f8eabf872ce11448193f65a43c8228800,-0x1debde97a7017a5dfef0f3996c6f5fc7a9bf6728b32ba675d20ae1cc0,0x7e3f2888027cc9bedd2555238b4910e082404dc1749f63b4161b99800,-0x1a94233a76171301cd3b0ae12e60dbb7b64c993477a13eb5ece9a4a140,0x4965a2cc893b0080a79578d3dabae76c2e6c2beb467e94087900cecd00,-0xa9533d49bb24485f366e52c55cb065045196ac9c70134ad06f9687c3a0,0x14ae1f8ce21a97869b9750ed195ea5949e98e91ec78e277cb55d6e7ce80,-0x2296630335b6047a203a37f51ab5f4a60e3bbc2ba80bf7c7c0ca6c85940,0x31e638c218d7bac143d37ce44345e206d7448d305bb5c873787d30d5c80,-0x3e77277814922ed927391da6e52428e5d044f9b7908a80b7088ba8d67cc,0x4425828a4807be9e657b80986970e0b2eaaa856b2c37ff829c360113770,-0x40fd518116c7f24002034f77ac389c70994ee20ab6cf73333292bd45a28,0x3649b9e64a2b0b3b1188e3098b35d55d45180b5144ec38df5d5f00fd1f0,-0x27c3209bc38081f22565294f6e6f6e023e2a4be542ee88d842be906b878,0x1989f9c9426d5b01d1d82d5cf6fd43d382eeeec1a94c6eddc845aaba570,-0xe5fe09928eba6344d407bdde45b40708eefbbe98698beb64a745a0be48,0x7143596b7f83012be3b6998560e294c54eabac37ba0a6ade6eb1e5b870,-0x30afa4d8d7ff6f0fa771b2ee03572d68d03e0cd016a069975ec0d89627,0x1234e6904771aab3b9248e6f7c8ca6832bef721fea9b82b76fa0acbe9c,-0x5e5e589b0064a3cf31f6416969a6c4bfb175ae0067acb70acac7b09ea,0x1a575129517f5b89f2214cc00c16190a4f98ba389f85a94a5cb62c13c,-0x64b38118fb05218b59e1d74f8f9cea71ed454a178e2c6bdefce75977,0x146eb79ba67da744ac762781dee9f4228651b561d5d890c0f5d58990,-0x37c9b15803b7dca6f0a7853468131fe7d3757abd6ba308f8808ac48,0x7e9ef93e051e6536ebbb1f8f80e05c8aa4d8f1c6a862cf68d0b250,-0xeb8e147b168aff47d849e8752d491808153180b5157509e1a7bca,0x161105a7dda7a68d3540fb708ff13cbf1ee89c0b0152b66f715f8,-0x1a184cb10f83655c1cce0080f8d5792808e7c3e7e65569b7db64,0x17b94ca5e87ef07abc54ff611517a1a2904fc8f1f68db31d178,-0x100d89164436cf27bce60c2105600ea9c70f8604d8f4f60fae,0x7c25f77985e2ad28107b91f1fe1cee6d583326095ed9b2a0,-0x28a68db94b947568b47c636272ab3dd4d0406b36357aea0,0x867e5623b70da4d4010674fea06895ba96e477fd3ace0,-0xff5a57d2ecbcaa0e84a163bbd6262bd288170547083,0xf2ac880027d3c904fd56c946ea72cc1b542f857dc,-0x5da5148d6ebdd8753659e0c84407a3f4d0c07da,0xa3944718fc59c08436465fbdfe32b3fed23c,-0x2437e520ce55654ae696bdb658099bdc3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 22 80 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 80 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 49 indices rho q24 m24 24 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 49 indices rho q24 m24 24 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x15b61529203a3dcdd7f8b4e3dfb,0x874a122c728ff5bfbde050ad5,-0x3344b79bac07e3e94d5b7acc,0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r25 : List ℤ := raw_ints% [0x1db4e74d09c79760e3cb45be04c28f523c6eeb66944200000,0x2b28a1d86351c5524ab57f711e3892181abba32f4aa3a0000,0x1d9994cde1a95684e53d50469b12aae50a18f2430d45b0000,0xcbfaaa7670e73d681ffb13365833db65fc894291a2269800,0x3de8c9b92a899fd91acf0ed72edc83c0d0c807dbec982600,0xe154dcfe501360b13f149b5bba963db46ab4a1519914580,0x27e3c4e3c91801ff67418fafa64831481ea0dda64cdaea0,0x5a1a8c8acb65b3113f76013ef0127aed8d2bef8e41ed30,0xa4fde18c16606cfec69763d482be57f54e774fe8ac3d0,0xf797096bfba2dd920c34745f1138080276c6ec6845e0,0x132870ccab1b159c82d888bc822a686b85ddef0115ea,0x13a20e93f59b79cd601c2f0a871f801feb7d6964edf,0x10a87ac8023a5dedf623c8c2d94708ec16c485e8e0,0xbab3a2b6db02b1a093f40979dfd99bf0b17df9d6,0x6b4cd4c1b8e65ded9bd194f65c37b53ae63f822,0x32124f9187aba001d07e33b9aca0084066f369,0x12ac400500a83214897faa22e9caf107e9798,0x56ed9e9ef4b358b6e784498b29d8e92897d,0x1303df73b89a0736453f832d0af1f94cb8,0x2f10f20c0df4e8877ad0fb677136e668,0x49762a90ac5d430a588de31c9358d4,0x3661a309ef227c59204f25010fed]
def m25 : List ℤ := raw_ints% [0x0,0x116db919d0eb298232216f3e74fb94e7d9b6d6f0000000000000000,-0x1ab26e04308d27412d1510f72e50b1c872a27362dac8b1c8b2bedc00,0x13b15fa3d7223e39dcd786939b9050a17461e3eb4f7028c3bca397900,-0x950a36cfa4b75e3eae75797c38f6185951d651780dd28e7242af61800,0x32c9b584a1f42b90bb2ea0093474ac25e6b800311e9cb4cf7420eb9840,-0xd47a9bb67f54480ffbf2211f5122eeeb913ba0675cdfa0f3f6b5aeb400,0x2c5692dbe51a357a7ceda621030fcdd063c0cf92a18ff5661d533912ac0,-0x794f0d5159fffe8c37734ad6de7b4b70758c0046941a0df8550f8bb4700,0x11525e299fc5caf09142dcc5b6c4fef99a8951e7fd611d3aa21da5c1ad20,-0x21815b3bd8bb97d7931cbb5203ae83eeaacfcae16f2df431f72a6ef75480,0x3770aa8b0793abac443bca937f089bad135a483c3f24260e9181758a0a40,-0x4f164a22001380a73b2495bdc2ddcd51759ff50503342395d2429a4b5a80,0x61d5e0f5d522ce333217727e46c577f57fc0ff1fced1a35877b2c0d12214,-0x6967dabff400eab6ab0ee585cf95c13ee10456c5f250c05bce3f422fd710,0x6333cbd9fa173c82af40324947e54d50936cfc6b41363fe4fc6080703898,-0x51b756291576b73f76470421f13a4b0a5b42f00e2a7e5cb1323b1ebacc90,0x3af88caf715b6804cf1063f0f59b8c3c3b28947686ba1f2212bb796082f8,-0x254905953f5fb5717fe2175ad5ea04062cfda67a143bc4a90987092680d0,0x14a3386cf673c220984a43749e2625221be8b37ff7a8eb5230bde895dbd8,-0x9fbcde461d9ee1a53f5ba18213d762aaebb345d2106c1f3ee1fb7dca2d0,0x435e1ba33f67528a5442f8ed377054d3f57479134b635f68fdffe84e8b1,-0x18af2aafeb174c7a27896dc16ac949820a4823a3592abb848a9b5a84b04,0x7d2c8c87019b44b8a6d769f9f5ae9e615a0552f1387fbff2e13ec5a3c6,-0x22207e710f2286d774a9a005533a58dca8b721fcb7834530ebea8f5464,0x7f31e7dfd00581f5247b00132936d9455e2aa6821546a45f894a3fa11,-0x191bd7f7e2069d85e4a4fd922f3ab1a30599f50cabd532260a091f370,0x428ac3f58da205aa6cbf282cdd32ba361b442589ef60afcf7f9ce538,-0x9234ced88c75130dd61ea3a70fc63efb0628d74445561648806eeb0,0x10683c693d2593772225c6a676a15dfb83764b99336f3e7de83b8c6,-0x17a7893a048f868da71d212fbd12ac493576ef82736d30893cf048,0x1acd2f1bcb3050fb3577e2d0a8be2620b447513c0811ed75b42fc,-0x173dea0234f4a1739cf69d9d3ad5edcdc6f30b44d3c1250652c8,0xeec9c03fe0a75f12661454bf4b2447d3de2611ece74fc12612,-0x6ce2bcdecb00411a17c2646570433270522689bf55f896020,0x21682ac2a7e5fbfdaf30fd7aadd5ff5c230b0d434833c9c0,-0x66c1ec54306b820d1b2f2d5f9159b373c26dab202838e0,0xb3c1f96d2e857bfcbcda15709f385a1c1fe172bbf935,-0x9bc6529d7be51263467499bab1f109414d5ef834c4,0x3627cf37d9b37aab68eb20ebe12f2e786e8041d6,-0x54027513c8365fecd000675c79683ab5b0864,0x103835fae1a2e2e75fc65414bb5a92c0c5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 22 82 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 82 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 49 indices rho q25 m25 25 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 49 indices rho q25 m25 25 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x3661a309ef227c59204f25010fed,-0x15b61529203a3dcdd7f8b4e3dfb,0x874a122c728ff5bfbde050ad5,-0x3344b79bac07e3e94d5b7acc,0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r26 : List ℤ := raw_ints% [-0x4a686c16bd1bcd409ee6eaf7ae6c7d14993b1e259342e00000,-0x6c0e789ee19e1848d6750ec73dc7256cc752a5f34f1f760000,-0x4a135e13dd1199957bf7a8cd9c5af34ff1d3afbf3420dd0000,-0x1fe383944f6305d8b61f0ccefa5932a3a08585fe3d8608a800,-0x9ac6079ca8593e97f6da784058b8dc16b0765abc628816a00,-0x233019f8ffdf09754809ac576139638d596e67a74aaec8680,-0x639afcb113bb42f410ecf7c56b713aaf946008c83175c260,-0xe0d6ff07d59c9a4ee236ccbef572f183ee2b05b98bff6d0,-0x19b699b91c08218663966d44eff992d91b4750663eb1290,-0x268e39eb37320c7ed328ef74d6db06016ddc3a3e65f450,-0x2fb16193108ba496698e812a9635234a5df94108eea86,-0x30d4959b5bf120582d0d7ecd49c3c68dee0e8c9b1779,-0x2963c8cc7e6119be89a718f99dbe05ab6a1184cd656,-0x1cf625db87ec905cf2b907753d3acb2b49dd3714c1,-0x109ff390cbdc9c36de2f8bf74def25524e6af0067,-0x7bf75d07da8d8d54a3313b1daea8cd03ec139ec,-0x2e2a126fb483c7bee0fb76908edbca19687919,-0xd6936487fa203ce2f66bca87b2d0aefb988a,-0x2edb6fbd84c2b8429cea1cb0647c3783243,-0x73c31e440dd8eef812a79527007b08097,-0xb44e8559115a8b62c6c8abd637b87f1,-0x852aba1444599f7b109238a059a99]
def m26 : List ℤ := raw_ints% [0x0,-0x1e8003ed2d9b88a3d7ba82ad4cb84495bcfff8240000000000000000,0x2e6550aecfcc56b1c771a0f62fae94bf247dfdcbd532ac02ada213400,-0x21f9e2c9de6fce2df1df8d8235b8d7e2d23e94612c873df54e540fc300,0xff32e27655bd2d125def61771dbdd49c6a8e6b7efb46b4d5c006f04800,-0x564734bbedcd3d4cbff877567af6fb74df7ede13a55fd3f780984c51ec0,0x165fbe2a9a2a9208fcc67877afcd3b9c8cf305af7ae9f00ea77b94787000,-0x4a0e87d5d5f0540e27176a632db5caee57ebb16cca6b0a3238f690eab940,0xc8c9c6ceaf34f83d7163e220dcb73df42a258df0e92b24ae42ed6320b500,-0x1c6624fc33eb7aad3e5d4b79b5fc7c2ccd4930d9b517a38cedbe230217520,0x3662a74b9f46660b84eef5f8e59b5341d80a9a391639c61c8dd18c3f7b480,-0x590c5a26a5af79eea241ca116c26aef305b7bc369e47683a23b1d84465a40,0x7da192b8fa22a042d3b399490eace6433b02d88fd9cb48e36165d6ea73280,-0x999be1a19049ad0d5472cbc141a6b7caa2ca21a956fca07f0236181a27a0c,0xa3775c145c7b6b811ed6228028d2338874e98625221b5781a59296d10ee70,-0x97da27ddaf407207b3e51da560943fa388f10394bc18e86f03a7d075a2ca8,0x7b5e706ccd728757a5f64d38066d3d94e6aebb6c648aeaa51aef116cbb0f0,-0x57bbd8dc49f37e49ab01bf6a716512a57af8fc60feadbd38a5e6010831d58,0x369ce8755bc6a153a1f3ee6ef1a1ec015e84a47a39c4c1dbf3bcc8b8c67f0,-0x1dbb109a3674376037ae4fe19cadbaaeb75e5b3f0499d0105666418cfbc08,0xe213d022144b77f3c1f6a1681e4bc587e89d67536cc8cf05c0147b3a1ef0,-0x5d8e2023b06b641ada72ffe07eb3a6379d2be16d2cac3028c0d9dbf99df7,0x21970e1245c968115af974cad7dfada6d6020660e02e37ef97844507c45c,-0xa6a7eeaf59fb2c494be1edf562b54597b644e460174654301cb55cea48a,0x2c6140c202207effce5ad300bddf597ae62ca550e5e15c0a28aed3108fc,-0xa1420ebee2da814e9ee70311d7dc260c042b79adcaabde31f705170ea7,0x1ef7eda608986277e288793865f7b5f2c9c7c74e3234a6a773f04eb190,-0x4fa6fef47e5b841c79eb778c7ea939af24052d712f47c709fbe15f548,0xa965c6a045eb27b98bf8593dce8ec0b223aaa99018399532c37fd650,-0x125801f6d679a7c32ad8e471af7c462de7f800d70cced6775bab55aa,0x196e83e2e160116d0877af16c03a4b9a514c67c7b65e634ad9e2f78,-0x1b99a539746d12f2356d2be6494c3dfb6ae2608ba3bc5ed9df12a4,0x16d2621d3eefe0e54c6b1830e2a26ec3a7cb0d3741d3e99b68af8,-0xde6b078505f702bb79c4cebd6c0495cff949b7685e96f01d86e,0x5fa33a0764427bb9ca8493768dfffdf74885267c12520a4020,-0x1b7b3c6ffe6a1182417b913987a2c044efabd0e9088d0c7e0,0x4e8dffb9482d711711aab292ddd8688366aa76580c24a60,-0x7e90d45d83ebd77cfc866de0a656c08c3464481794a93,0x63fbaa0b14b6f834f431e00e19703ce5497323e6b9c,-0x1f4f51d25784034d3632c99d50e6df3d170f8427a,0x2b2174f9d9d58180fa6fe75b3b8621cb844bfc,-0x742f958fedbb6c993487a3498cae9d3973]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 22 84 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 84 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 49 indices rho q26 m26 26 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 49 indices rho q26 m26 26 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x852aba1444599f7b109238a059a99,0x3661a309ef227c59204f25010fed,-0x15b61529203a3dcdd7f8b4e3dfb,0x874a122c728ff5bfbde050ad5,-0x3344b79bac07e3e94d5b7acc,0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r27 : List ℤ := raw_ints% [0xb634fc75c2dc883439c60a010189bac0de2be600ff8db600000,0x1088018a6ef7f88d51b480f366f52c616187f460323f0f9e0000,0xb53ec48a9d39551631f4fc8d17f9e2e70a58d14e31df4650000,0x4dfcfe3bbf86ad589c4181ea7789181e5ebc9686d70b3c30800,0x17a553344529832f26745fc899b2f7338dbf16fb9c65ecf1200,0x55f7e77b32600c65e423abe46603f2f8e9302f2d5a02af0080,0xf3354774409443ace51e425ec4673b7ddcafaa6d60cc065e0,0x224a740737ace7ccbf03b9afe8a2c3974e0846900115a1f50,0x3eb4098995efdc824dc2e62e33a66339211a100987df11f0,0x5df3992a2ccfbb205631f2b98c09327f3b6eec5d388c110,0x74203594c81e000be42cae12af2ff6fb6979253532ddbe,0x76cb52778ab13c9f6fad62be653fa3b0887f7d93c98f1,0x64998857a76e0b70dfe06268816ce2a3103a5f2ada48,0x46525aac18a87918975f622cb8f9e4fa891266264a7,0x2852a5c575b807eccee6be8f469aae574b5fe5fce8,0x12c518d7d48b0a7bc09ecbeab64373aee60ffd7af,0x6fb1305c84218327b7654ea066a68389690c04e,0x2066b69ba47db64c9b394de59db8b6f659c241,0x71084670b7dda6c7474ac566525f98b2bc36,0x116c62fbe1eedc2255c2cbfa9dde7f453f0,0x1b164819c1bce8b0738e152159d37113e,0x13f6bc7f69703d754d233b52ef1f828]
def m27 : List ℤ := raw_ints% [0x0,0x356006df0fd02f1eb98664af464278060abff23f00000000000000000,-0x50a558748aed9216a47463344f21d24d1ae95bacbec582448501807c00,0x3aa48f6e6ea9ebf9feca72f451ea664b81b37e433d6a6d73d42dda99100,-0x1b53d5a1e30485a3d2c9d79f969a6f076a5db3cae89c52db07e421ed5800,0x92b02a4436eca239d77c11596768396658873cffffffa48a08bc2ad7ce40,-0x25bbee072f52590a30be11a9405e43e790406e6d2e02e9e1a283e23b23c00,0x7bd8aa077e6ead5eeff49d2b32ce9a7be3c71486b53f9d64a11ddbfb3c2c0,-0x14cd0df55344f6bc859679ce0ae73e014b2867c19995c2140b6516428f3f00,0x2ea2d77d13d4f7f354d3d8471ed2934b7647edff773362a23c337e1b4f99a0,-0x587075ceaa69ccce09b30625585de1d61715853231e7c520b9e76e67456680,0x8f51f0061f182a985fe9a1bd99f141e91560263e1c2df92dd18cf9c7b00d40,-0xc802bf8d82ce130b60a4bce5430d87d957fabe6a64bf13698c67ccb663fc80,0xf1c2468259c8530e6f0512400f91970262a5d0cd19fcbf91c278907d94e7d4,-0xfe2a779daa00cb85880f92b55b290dc1569256f185aacd76a01c43a7028810,0xe916b34de636119072058d62e625ec36a4f4e67fd1b59b9554be49fdc55218,-0xbaccc3c27940f5360904d8f359065e27f28a67ba7b712e3c53e3d07a875590,0x82edde66b7e621a5c0000d3b8ee8e2b108ac7f2a70d7ed12ac4fa1e9dbc398,-0x504088186e9269bdf62ab478e9b8b73ef93dc441290b52761d63d1e4324450,0x2af9735fa01b60967595517ab58c074e7aa88c8af1390ef59505152faaeb18,-0x141144f990eec54cc6e4efd25887a63aad58da911d9082a9afd4d12845a250,0x8262af3235503d5edd08f232f65561336693e3b896d830ab738935bf7d2e1,-0x2ddffa409feb8c181c4ffd9179d6d2fe905f3d20fe065b3f170394a574744,0xdeb2f4f6124436b6f29f60f6e8f2e09891413e62dc94ff69501ea34fc026,-0x39ecee09b47a12ceddecfa9a7c0bde1b67eed6363a589366cac62ca1cea4,0xcd30a130cc3ae82b593b502a4a895594ffca24445bf99f53a82d99b9c61,-0x26552a10cdb9317b8d462d614307ff72a18c6d13a03704c6ee9fcc85f70,0x5fad5f684e0c0e170b527e2f71f3e9eb8e8d8b7c21d0086146993b9238,-0xc4eb5f301f53f943c497e1f2951c2f8cf9f6a771ce51745a015239eb0,0x1492a6d5a958e23c9e0723e425904d9f296470eab691103111f91f6e6,-0x1b6baa34170b951969472a808811a287659e4b3ab2dc72dcaf3462c8,0x1c7eb4022b9f712aefdf2a05ac595a989b323e4662df2e85199f5bc,-0x16754faa736885653af88082eaae53914e04b1c1f2299b1d76a548,0xcf89f54a724030b30187fa75fb32d396d724de2b2365d00b01d2,-0x541d62eb1d6f0823fdeb2e3adaf85af3dca82e0e94cda4aa0a0,0x16a0aa0b2230e0a2bbef471579b49e212f6254158d47e2d980,-0x3c15277448229fcb1a6f363a51aeb65c797f8adc778a4960,0x59207912521b6c9e1b66dab096d7f87a45dad7c644c525,-0x402a6d8b985e30fd9f23063c8e442f55537524286b04,0x1218bc7e2cbbbc8603f89ba071e9ccf64e77b6ba36,-0x1622df00fb6aa797f1ca28f21d62919770018a4,0x3400e85ae371e492aff7da015f49e9e4595]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 22 86 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 86 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 49 indices rho q27 m27 27 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 49 indices rho q27 m27 27 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x13f6bc7f69703d754d233b52ef1f828,-0x852aba1444599f7b109238a059a99,0x3661a309ef227c59204f25010fed,-0x15b61529203a3dcdd7f8b4e3dfb,0x874a122c728ff5bfbde050ad5,-0x3344b79bac07e3e94d5b7acc,0x12d978ee760eb3625164674,-0x6b3780de0d464b95239e8,0x24b5876a8d024d6c08be,-0xc0c3a798edac64024b,0x3c4d1fd0509c2d107,-0x11db5bf2b147a411,0x4f696e87da2103,-0x147ecf20d9b76,0x4d8031495c6,-0x107684c7d6,0x3100b6c4,-0x7aedad,0xf451,-0x157,0x1]
def r28 : List ℤ := raw_ints% [-0x1b50d13b249f0007db8623d179e6cf72e737cb1c25d7cdf000000,-0x27a36156e1c36ddaed9a2fe35132027d294444a6b513833d00000,-0x1b26984af9b1c53fc20e5c80f1ce2791ae601dc866b061f5a0000,-0xbad80ca9d55872720fb59298e8dda8dea4a0f7f3e4b5726e4000,-0x389fd87d30a626533c88233d8619d94adb1f73328b1a71048800,-0xcdc3f030c019c6b61b2153066a5c811351e4904d724563d3200,-0x245ce84df4e911493c9009b56daf82faebaf5f6afa2e84ec680,-0x51fbd24bfcb6a2e836af8ccc2670c779739fee6b638a2d29a0,-0x95d1cafa4bc6f12bb4108251bcebce9908f97c2e28d9ceeb0,-0xe054bc9bd9c5c8086840eb8d7a0a4a3fd4438a1a7df12710,-0x1151341fd0eb57bdcd2d54d1512065c0a6be2bf3c47ac0a0,-0x11b3803b78cf7034dbab4de7cae6f5bdd064bbc2a27009a,-0xefa2fb5d4f4276173fcb15e196439736ef9efd6ebd777,-0xa75b7129960c6fdb248c63c5ed70a4f4f140ac98ee80,-0x5fde0a78baa780f9015b49aacc5a1fe8ec1c0199201,-0x2c93a6eea5cd6a230bbff87dde7922e4a05231c808,-0x108f1a246a1c73b170e9b592c3f7d10d1c58bf3e1,-0x4cc260e44f64e52350c075cecd7c89477e6c042,-0x10b65e9f4b0192d4a1e2970f40c593c40c2bbf,-0x29278377cbe508bed8e99c8d1aaefdacd682,-0x3fdf116170eef7ae7bd381f87ede0bac98,-0x2efc961dbd4e3bcf573e7165fcaf22ea]
def m28 : List ℤ := raw_ints% [0x0,-0x5d680c065bac5275c4ab3032baf4520a92cfe7ee400000000000000000,0x8c352dcc5fe93628d45485accb34b3a494be19a3de2d4bd3a07288d1400,-0x6541fb0508b957a9f2ca3cea57fc4d563452126d5765aea9020d60e24b00,0x2ed954632d2cb1a83654d41f1fbd0f27fe614eec6e2354ef9c18498a80800,-0xf9984b8142721f52c3ada6410b153756f7cb9c05077985fe9211fa015d0c0,0x3fb3e8c1239344ddd700b01aea5562f224f376961cd94b2af68b0a64c70800,-0xcf5be5bf4b7d1e771fead95256d75cb1a77d62450667e6658d262a48bfb140,0x2286e6112409491a6a5b61a4cbf2a6108d4444a79c716d54a6c93fa78255d00,-0x4cb50a2be1725cd2f3fca35abe49b1bbea1370b696fca89c0397c7a4ffb12a0,0x9013378cf70077628cbc3b81ff8c734eab151569ff1f01872a4a8f6afc44a80,-0xe720e130e56ac399a1c6a8681cb220b179219f8dc7eba93953113745bf1e340,0x13f1f435625c23d61819d31ff574e0ab8aa7f3769164a9fe814382cf17303880,-0x17d658cf6baf6f297db8f7031874d5b0185ac738a4c8cdd76c6032f54180144c,0x18c32e0111ae5d788b81a0f6f9fd442796e8cd514698f4957511ae2116b21570,-0x166c25a78e1e0b72f00be7d577f7817b933663dd76f0eff0c8213b9593fb6728,0x11ba95347207204e4aed91ea2767cbc0268d23d6108b45036dd7ef65fa4e7ff0,-0xc3fc7624a67ba749ae6cbc3f3d26892de3d42ecf2764406c5fbb1d046840938,0x764db13c6f4989898294a8fb919d585f200aa8e7f323343fbb6b4f12260c670,-0x3e52b98e8ef67360f54922252e7ef872edf699b13044198184ad7e83834e3c8,0x1c98fa898372e65985b1384f3809314f2744c94b6578edc8f9d18261241c170,-0xb65a0f1a8723eabbd8492b842cb9e82885d350d718274adea61b7e8c58d7c7,0x3ee050f5b9183b1dda66e53412fd8c76471fc43cb2b7d975c594cd9dbcf61c,-0x12aa925df13111c79a0c33f2bda3fb3c42932877c9d47bbf56ff870d17b12a,0x4be0d93bbcad39ff990ebfb1577e2e933200e37e20356355726ea0589dcbc,-0x106063ca05d0c1ceb4315e2c104c646c65f31b5de44148f2d463884f75cd7,0x2f9d4c0f792ae2bf40f9d0fd8c5ed00b110c6fae619c65c3920790c94190,-0x7350e35c803ae61de229339b1896e00e05222a39d88979d0322c6a9fa48,0xe5a6f1ea8e1098ac69dd7780be8b7c9a142b5e528e3c9c3bed2c72a250,-0x172476585f572028064be0bfc7ba757764b38970053e8b4bf5cbc9538a,0x1da578856f82a7130f08346283f970658011fcf719ff57970dd4f70f8,-0x1d7d8c882792d5641616e4906601a12207d73f891bbcaae9896145e4,0x162578a08fe9c569bda81fc369ea8c6367f61b3b8f44bcf4e012c78,-0xc1fae55ab4bc9853d4373b87892812d95e6f931ad485b8d254a2e,0x4a12c546ad1210d150642af2cb31c0ccd1957523e7b6d7e119a0,-0x12a58c31c0ed94dcc7378b50003706bdbb6b16d8b40a7803320,0x2df9828184b87e16d9cda53484cf253dcda9afb9f841dd3e0,-0x3ec4f993911760cab696fd0879c59b5bc635b084a2496a3,0x292c75f98af92ede0f4b9ae6009b2226b85e074c9fb5c,-0xa74e670c8bad7e910cbf65fbc567bf2b246824471a,0xb5b84b67f383a6909701c8c31ce04197d02a1bc,-0x17452e68c9541aa88f1e2606584f19540023]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 22 88 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 88 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 49 indices rho q28 m28 28 108998627957364174415626240000 28=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 49 indices rho q28 m28 28 108998627957364174415626240000 28 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_28
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<29) : intPolyRF (mz e)=rfPoly (C (108998627957364174415626240000:ℚ))*rfX^28*(1-rfX)^20*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V7C29
