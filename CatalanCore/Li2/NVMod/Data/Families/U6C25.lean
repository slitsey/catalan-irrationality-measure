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
namespace CatalanCore.Li2.NVMod.FamilySource.U6C25
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,6,25,size⟩
def bases : List ℕ := [1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25]
def num : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x48fde0093cd002c0000,0x63b41fbba9d719cc000,0x3fec390252bb7227000,0x1992adc8695eb904d00,0x72888594a6304bfb00,0x17d68ef5156440aff0,0x3d38f03cd8a2f1780,0x7c1ca34d78fa5cc8,0xc9925fc2db2cdf0,0x108a1e68a24b1a7,0x11a0aa7f2bee70,0xf410f596f215,0xaace33c37e0,0x5fd70e7ff6,0x2a7e826e0,0xe8d18b2,0x3b6130,0xa9e3,0x130,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x2,-0x19,0xe7,-0x3e9,0xe86,-0xefa3,0x7ccf9,-0x54df1,0x5f648,-0x631e6d,0x16497e,-0x776523,0xcbc48,-0x192c265,0x602919,-0xa0447f]
def rhoDenominators : List ℤ := raw_ints% [0x69296d00,0x1ab530,0x2cb0,0x1ad,0xd0,0x82,0x3c,0x23,0x80,0x144,0x5a,0x37,0x294,0x8f,0x3e9,0xc3,0x4100,0x4510,0x45ed0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 26
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤25))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤25 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 26 omega7=padCoefficients 26 (omegaCoefficients 25 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 25 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 26 omega8=padCoefficients 26 (omegaCoefficients 25 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 25 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 26 omega9=padCoefficients 26 (omegaCoefficients 25 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 25 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 26 omega10=padCoefficients 26 (omegaCoefficients 25 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 25 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 26 omega11=padCoefficients 26 (omegaCoefficients 25 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 25 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 26 omega12=padCoefficients 26 (omegaCoefficients 25 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 25 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 26 omega13=padCoefficients 26 (omegaCoefficients 25 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 25 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 26 omega14=padCoefficients 26 (omegaCoefficients 25 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 25 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 26 omega15=padCoefficients 26 (omegaCoefficients 25 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 25 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 26 omega16=padCoefficients 26 (omegaCoefficients 25 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 25 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 26 omega17=padCoefficients 26 (omegaCoefficients 25 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 25 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 26 omega18=padCoefficients 26 (omegaCoefficients 25 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 25 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 26 omega19=padCoefficients 26 (omegaCoefficients 25 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 25 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 26 omega20=padCoefficients 26 (omegaCoefficients 25 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 25 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 26 omega21=padCoefficients 26 (omegaCoefficients 25 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 25 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 26 omega22=padCoefficients 26 (omegaCoefficients 25 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 25 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 26 omega23=padCoefficients 26 (omegaCoefficients 25 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 25 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 26 omega24=padCoefficients 26 (omegaCoefficients 25 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 25 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 26 omega25=padCoefficients 26 (omegaCoefficients 25 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 25 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 19 li0=padCoefficients 19 (liCoefficients 18 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 18 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 19 li1=padCoefficients 19 (liCoefficients 18 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 18 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5a,-0x15e,0x38e,-0x666,0x7d2,-0x596,0x0,0x596,-0x7d2,0x666,-0x38e,0x15e,-0x5a,0xe,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 19 li2=padCoefficients 19 (liCoefficients 18 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 18 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xa,0x24,-0xe,-0x16c,0x666,-0xfa4,0x19b2,-0x1e2a,0x19b2,-0xfa4,0x666,-0x16c,-0xe,0x24,-0xa,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 19 li3=padCoefficients 19 (liCoefficients 18 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 18 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x2,-0x36,0x1ae,-0x632,0xdb6,-0x12fe,0xe86,0x0,-0xe86,0x12fe,-0xdb6,0x632,-0x1ae,0x36,0x2,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 19 li4=padCoefficients 19 (liCoefficients 18 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 18 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xe,-0xb4,0x2da,-0x49c,-0x2e2,0x1cb4,-0x4006,0x5136,-0x4006,0x1cb4,-0x2e2,-0x49c,0x2da,-0xb4,0xe,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 19 li5=padCoefficients 19 (liCoefficients 18 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 18 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2e,-0x10e,-0x32,0x10ae,-0x3c8a,0x69ca,-0x5aaa,0x0,0x5aaa,-0x69ca,0x3c8a,-0x10ae,0x32,0x10e,-0x2e,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 19 li6=padCoefficients 19 (liCoefficients 18 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 18 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6e,0x24,-0x1076,0x4034,-0x5232,-0x4424,0x1723a,-0x2186a,0x1723a,-0x4424,-0x5232,0x4034,-0x1076,0x24,0x6e,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 19 li7=padCoefficients 19 (liCoefficients 18 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 18 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xee,0x83a,-0x3782,0x230e,0x17886,-0x43ece,0x46576,0x0,-0x46576,0x43ece,-0x17886,-0x230e,0x3782,-0x83a,-0xee,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 19 li8=padCoefficients 19 (liCoefficients 18 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 18 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ee,0x297c,-0x3926,-0x292fc,0x807de,-0x4097c,-0xf90a6,0x1c65f6,-0xf90a6,-0x4097c,0x807de,-0x292fc,-0x3926,0x297c,0x1ee,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 19 li9=padCoefficients 19 (liCoefficients 18 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 18 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ee,0x9f42,0x228ee,-0xdd612,0xe256,0x44fe5a,-0x63ef2a,0x0,0x63ef2a,-0x44fe5a,-0xe256,0xdd612,-0x228ee,-0x9f42,-0x3ee,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 19 li10=padCoefficients 19 (liCoefficients 18 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 18 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ee,0x22494,0x141d2a,-0x12d42c,-0xc16512,0x12c2b6c,0x1039ffa,-0x2e3b7aa,0x1039ffa,0x12c2b6c,-0xc16512,-0x12d42c,0x141d2a,0x22494,0x7ee,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 19 li11=padCoefficients 19 (liCoefficients 18 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 18 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfee,0x6fc8a,0x7795de,0x133094e,-0x44a1b5a,-0x525a83e,0xfdd3536,0x0,-0xfdd3536,0x525a83e,0x44a1b5a,-0x133094e,-0x7795de,-0x6fc8a,-0xfee,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 19 li12=padCoefficients 19 (liCoefficients 18 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 18 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fee,0x16146c,0x25d37fa,0xee698a4,0x4c16d7e,-0x52bf746c,-0xc740566,0x92300eb6,-0xc740566,-0x52bf746c,0x4c16d7e,0xee698a4,0x25d37fa,0x16146c,0x1fee,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 19 li13=padCoefficients 19 (liCoefficients 18 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 18 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fee,0x447c12,0xb048e4e,0x769e992e,0x154dcea76,-0xb54e2296,-0x4a7284e6a,0x0,0x4a7284e6a,0xb54e2296,-0x154dcea76,-0x769e992e,-0xb048e4e,-0x447c12,-0x3fee,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 19 li14=padCoefficients 19 (liCoefficients 18 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 18 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fee,0xd1f304,0x30e7714a,0x31c403774,0x111f7b7d8e,0x1c24b388fc,-0x10deea66c6,-0x3f667d76ea,-0x10deea66c6,0x1c24b388fc,0x111f7b7d8e,0x31c403774,0x30e7714a,0xd1f304,0x7fee,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 19 li15=padCoefficients 19 (liCoefficients 18 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 18 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffee,0x27ed7da,0xd269da3e,0x130c53218e,0xa2387ae3c6,0x234b32d8552,0x2e34f9131f6,0x0,-0x2e34f9131f6,-0x234b32d8552,-0xa2387ae3c6,-0x130c53218e,-0xd269da3e,-0x27ed7da,-0xffee,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 19 li16=padCoefficients 19 (liCoefficients 18 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 18 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffee,0x78e865c,0x376a4951a,0x6e360e2c44,0x5332928371e,0x1c3eb52989a4,0x4b9ce4a7d3da,0x687e0053c776,0x4b9ce4a7d3da,0x1c3eb52989a4,0x5332928371e,0x6e360e2c44,0x376a4951a,0x78e865c,0x1ffee,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 19 li17=padCoefficients 19 (liCoefficients 18 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 18 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x12,0x99,-0x330,0xbf4,-0x2178,0x4884,-0x7c50,0xaaee,-0xbdec,0xaaee,-0x7c50,0x4884,-0x2178,0xbf4,-0x330,0x99,-0x12,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 18 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^18 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 25 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 26 at hb
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
theorem cache_li (j : ℕ) (hj : j<18) : coefficientsPoly (cache.li j)=liNumerator 18 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x1000ee3a6e4b20fb6dbf01b21000,0x1b79eaed99333a10f39ed082d4c00,-0x16c7acb00fbc5080b5c66692872b00,0xc256665f14d6cdf7728c140f848940,-0x4adffe92f7fc2156f6fc16683597980,0x16349e971ab387a9a244a058ba1e7750,-0x545d2aa0647056b78529b4ace0bad420,0x1078d98d91c54370f9bc710119df59890,-0x2b1f7ffa6d263664d171d07e9de548040,0x5fef9a0e800b3a323ac158f24813c8644,-0xb747b5f09b985dc1856032ef25df79008,0x12f14df7c11074734492904125af948664,-0x1b46eff5b07f2c93ab7aae891c04d93040,0x225b293b9ee945c3a152549ca3809c8660,-0x25f81f4ca03816d8adba96dd0b621bc880,0x24e552bb3c5383d6bb5f8b5f5ed257de90,-0x1f8eb9049fc534b5913c935883291e4170,0x17c2e325ad558bdd06e13318ca3674eda1,-0xfbce469448aae0f8ad5dec561c240c3c2,0x9275cf8d9ecd5a7949aaa989c6d642c29,-0x4a9c5298e80cc3a966353e3707427df30,0x212a98e48cf634d2d20a09838a3738094,-0xccd54c0d8cb1beaa38bb2c1248109938,0x4438d9f336ea859e26e71d8036b95084,-0x13732050225f80e48c7a21ad345017b0,0x4b2d7cd29d88c36fe636b9a2932d842,-0xf315e4b86e117306b4ed90d07d2ab4,0x286d48c4f916263cbbe6d20f3a2a02,-0x56a75bf309646f643b486348e0610,0x916dd7f5de3660be45e5d79c8ad4,-0xb7ca528ccb4d68c349550cf03d8,0xa5649d59755531605e9299a374,-0x61542a59ae4982a7ba3201b60,0x20802a6b84a9921fd5e6dc41,-0x4b0fe1af41ca38cd629492,0x25f8ff6e0e56626c1319,-0x36df51f2160e8100,0x195360e5e2cb9e00,-0x90b7e08f591dd00,0x26976f1528d4c00,-0x73c64d3f7a7e40,0xd9edbe959b480,-0xc1b6e24c1840]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 19 35 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 35 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 44 indices rho q0 m0 0 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 44 indices rho q0 m0 0 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1901743b4c556388db7a72a639000,-0x2a52f0e8f2f28ca2dc4a372257bc00,0x2294e420fd49065708116d517b3c100,-0x122a403a9fbf971f51b7d589d95dd2c0,0x6e46ab02434e075226e6d2f83acf4f80,-0x2031b88eee1c3bc26ec80a8470d8cb830,0x785ac1ef6c4199672cdeb670089cf6fe0,-0x171cd2f9aa361a3786a5a5572a5ba20c70,0x3b7bd76281dbfd9dc83244603d418ac200,-0x82074cf5928855e6c384892c83963e6a1c,0xf3f3eab3a6b2c20448f4a60c8ae839c3f8,-0x18bf1182abd0284d54c62777e00ac5482fc,0x22f3e603da4768af288f20bd80df367d1c0,-0x2b270f0a48131ff614c6537ca676b9a6fa0,0x2eb6984f25e053a79a62c9dace15488bd80,-0x2c6d64fc31d6e930f6770858d705d8114d0,0x2528d77623e63007723af3b7197e65db6a0,-0x1b55e34041aca6e475382e186bc5ef63637,0x11aba590292888d5ba1a67c83996f6aee3e,-0xa05122428945d9981c5b16968b0217306f,0x4f851254e6d5045ac47cc4dcce64887a90,-0x225ecdfc93f497a51eaf7617d70e20414c,0xce126b27d16b6751204019242f7381548,-0x42837a7727f6e42d814c8eb7c4b27259c,0x1256f56d7e9df66f2072336297d9b4630,-0x4466579ca7064735fbc9eede20c8cbee,0xd4d5615f79311e79f3337498a8c3f0c,-0x21f4124fd1cf79a92a8764a1171202e,0x458bd95732a53d8e093160490eb7b0,-0x6f0412c13ac2d7b5eba3d25f2b80c,0x84ab6974f23372a8376ca7209ca8,-0x700daeedf6011d918e87d53e54c,0x3d46346de41271ee7a485db2b0,-0x12c095968c44c25f26f293697,0x26e859dc1b99d5ba86d196e,-0x112de6f81201ba384ad7f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 19 36 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 36 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 44 indices rho q1 m1 1 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 44 indices rho q1 m1 1 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x2712459ca7456b85d6ef5323b91000,0x4138432c88f6be9b07a710268a0dc00,-0x3489666815b682b5dc8d2445092b6700,0x1b3279177f46669e390e8082f8803f540,-0xa2a83a2b57ba590ff5773c91eab273880,0x2ec346c5c94823ed5bb248ab9dbfbc7250,-0xac1487e4cefb8232b831d38fc3925a3520,0x20838462e80a5187b71419893b1d1cad190,-0x524abeba1f10ae654ced68512cb64133b00,0xb0d04b531e0ccec921c84a6c48267a92c04,-0x145e2440e3a9530c30505d306814aa8d3148,0x2074b21c3647f2313683c90b726b439e08a4,-0x2cfab39ff455030a631808844bd322bbe840,0x3673084bb7980dbb734d9a5ab7814b90be60,-0x39c04bfaf2b29582e1621a906388dcd4f480,0x35c5b3195992e8dbe5554ebb6d6b0924ab90,-0x2bfe55d108f9afb77fdf16d3f1007e0225a0,0x1fa03854011192ce83e01c70e77146f23a91,-0x13f52417d18de95bff01d2b4487d71aee892,0xb08e532741f212ba32a0310170d65024f39,-0x5548b252541f797641ed9928523c009adf0,0x23d8afb0a0d646095937950c4bc791a0254,-0xd0ab04f0f42db15bfe29efb9f65cc5fb78,0x4145f52ddb8e12306dc83df1f9df7431c4,-0x1168035c7f4523a76f72cbf8808d13fed0,0x3ea2ccbda6069a2c67b20e2f7654548a2,-0xbb860e1ec0a86506bf1b39eebb8d5c14,0x1cb0794a691dda97cbbec36fd7e7d622,-0x382230162a2cb8b801fb90b58ec7fd0,0x552efb20aa2eff8e7ee116dee82694,-0x603204a08670bf68af063261ae318,0x4c2f93936b7d4a1a8ac3f3f325b4,-0x26ab3faec954abda54135a88510,0xad4dc9e1ac42d80a0b7b01b31,-0x142a076ebb21071ad1d0d7e2,0x7c4a32d2e3b1505d60829]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 19 37 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 37 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 44 indices rho q2 m2 2 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 44 indices rho q2 m2 2 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x3d0c8cc4c55c78011fd5f1e7d129000,-0x6489e9166a0b2e1d1321b03d89297c00,0x4fdf992902099fa6e57a8352a74f7f100,-0x28c3ef5562f8b4d37e2a0d1a7bfd02dec0,0xf045ac6f2fe7be321d564b1740eef02f80,-0x440c60083080ab129c69dc5e9cd9f874b30,0xf69310b0b44be1b7b286614e99adfa915e0,-0x2ddadc47cc989e4078af306e2b90b7c91b70,0x722c892c3f6451e5e724d002955a4c36d400,-0xf1350f42a9b6aa1cc0ec449211948ddbefdc,0x1b4e0fae0e4960abe4099b3fb42f880266578,-0x2abb73dfa38d0a5c915852aa601d13606b2bc,0x3a1ff2b519142ae8b52ee9783853ea82a1dc0,-0x4503299a58aa00fc2b3e4d9574fd38348e3a0,0x47bd2cc235c806e6d022cd95d9a4c2cf21980,-0x4169902357e799c51f25214af86ccd645e5d0,0x345c8bd2c1e01092a59bb0869b3625bb2c920,-0x24cb0c645e6fc495f53d6d3de4a2eb6f4e527,0x16abc740434ed591187c4186a309f140a3b9e,-0xc399ffefeebb1fdcbf495311836036297bdf,0x5c06fe5e97b5d2a713106ed073ff4329a590,-0x259ec2f7ffca08c3a9f55caa2ec32045e00c,0xd4a39c373031e934091dff2efbb8921bfc8,-0x40772a0601bdbd3996614061014f5dc495c,0x10a02e3680a85bbc482fee7adef0785d230,-0x39b7e6468e4262c3c0ab08c8b4006abfce,0xa63c002520bf6c8771538d38223d8cecc,-0x18621c8a046804686fb3ba917ec94d20e,0x2d8e1f17ae425f798b01842109b3a4b0,-0x41af3e3defd020da6c79b704c91f8cc,0x460b3a174f05aa31e8b02c1abb6928,-0x33f8aee0a84e8d2394e58e1ab800c,0x1874ff5acd2fed6a74f405968e30,-0x643203f0b128028b84ce2de787,0xa72b446fdfc324bbbeec21ce,-0x382bc8e12a668dcadc55ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 19 38 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 38 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 44 indices rho q3 m3 3 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 44 indices rho q3 m3 3 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x5f639bf374607b81c1be49fa36d01000,0x9b0a7c6443bfee7db0a79de2207ed1c00,-0x7985e9f9840b9a826679de153dbbcbd700,0x3d2b534e2a1189679164d62d7cf58a3e940,-0x1636fee77a6b10898615b835ecb5835cc080,0x6333879e56e8f072b1f7a8fc7333f58cd750,-0x16214227d23205f98feeb9a4336aebf988720,0x40d4f937c8d3ea5377403249f199dd21f7290,-0x9edb81fe35a4af3a65e2dc2b6ddecf7306b00,0x14a18852349e4415022214f72313ebe56a5c44,-0x24bb9e4ee059222ff97333f6ee54895b39e5c8,0x387a1a78040c45030b0ba80223927cfe5932e4,-0x4b6bf1bc088b19bb3e4e58db4d486308939c40,0x57db51ab9f530298b349c8f10ba60eb56a4a60,-0x598898ae1877cfd95bd6d1d73883a9673c3880,0x4ff7b239480e11c69714fa6e7e7cc4df74e490,-0x3ea5857f0d50f59cdfeb5a0e1695e396cb6fa0,0x2b09c514edfafc58b7620d92220fb1859c3d21,-0x19e63295e3f84f9a434a869ea5bec46c1cb4b2,0xd9f80ab98a92db22e757f673adb9ca0fede49,-0x63e65e76a71b993d315f47b3adac53912d4f0,0x27b92bc05eec0d3a8a03586c83dc82c0d0994,-0xda0763719399ae1b80dd0ae3fbaf155deef8,0x40106e5f68c068da6794c5829fce53b6b404,-0xffa82830742de4db0014ee9be192b19a3d0,0x3582ea5a9b07ba7ea98c4f333805ae65fc2,-0x943c1ac5e083f72e2cf2c378641a573f54,0x14d72740e1b8b399554035d7860ef95142,-0x252a0fdb6e28f174fbef667ffc48644d0,0x32e3338a317d409cb2bb91a41a61abd4,-0x3334b68f607814e53a1b6eb0aa96498,0x239026bfcea0ffa27cfe8a671bd6f4,-0xf7fd9ec34a0768d68d13c9adee10,0x39f94578c072d0588b45b4d13c1,-0x5698cd3284e10ebadc7674902,0x195f5ceecf0819760f0d239]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 19 39 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 39 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 44 indices rho q4 m4 4 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 44 indices rho q4 m4 4 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x950ba3ac65d6c0fabeb95396f5a519000,-0xef2ce2a686f1964cc82a5e744a0b27bc00,0xb9061e2cda9cb2a59ea07227968085a0100,-0x5be2658386f1d6baee097bce8caad0596ac0,0x20e8d8ec07683bcc9ae330c6d88cc1edb6780,-0x90df8667d9ab5c94bd84e35f0b2bb7cc07e30,0x1fd88269faa382fd87afe2684a73fa149933e0,-0x5be35378ced81c62387a774b952c43a266da70,0xdda54ca55795c51b6a2890f138b55e2a226400,-0x1c52676fac6213fa7de6dc4d24ab954af1d2d9c,0x319609bf23e88018f2dce8a7a8284ac6d364cf8,-0x4aec288d03373609f11ec953257e43e69263e7c,0x6243164708f1d78916b1a5d6a9e191edf0c49c0,-0x7054fbe2b4182100be63da553af7423ac32f7a0,0x704200270c6d2c14b411aa31eff9065abc6b580,-0x623d008aa82cae496ffffa25ece12931c61c6d0,0x4b55f1f7948563c7434e86397a4739019bdbf20,-0x329cc02590658320cbd4b07779703d22a874217,0x1dc05242143171be45f8d08a237a58e768f6e7e,-0xf448d7cf77673af7483055afcb6540afc5564f,0x6d152109297a791e8e470a04cc8a86e0de0690,-0x2a31e5bdf6af7155e9a725d198d789c92c4ecc,0xe0e8527689a3078d6903201b10fe7eae43048,-0x400d3d8e8f1cdd2cdc20aff2a48d9aac4611c,0xf72fde6401bb719663715ab62d6e4831a530,-0x31e7a439afd51d17c4bac4504d7a5c5097ae,0x84f11c2fef3a9317706c54ec08ea225d18c,-0x11e8cbb3f273af7f39567936a9a2c4219ee,0x1e78c0b507c912d6a7ffd86e76f139f7b0,-0x2799d38269bb57f9f042fa504b1c3398c,0x2593683d9205bce17c82cc79eeb2dba8,-0x1867c83e421c8e44c07948fbbb60ecc,0x9d7293a454fcccb344f6c7a06ed30,-0x2190f52015b99e24656e8a0b3e77,0x2cd8999e5799d40ce19a2f87ae,-0xb747c41ad52e72a4900d55f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 19 40 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 40 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 44 indices rho q5 m5 5 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 44 indices rho q5 m5 5 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x48fde0093cd002c0000,-0x63b41fbba9d719cc000,-0x3fec390252bb7227000,-0x1992adc8695eb904d00,-0x72888594a6304bfb00,-0x17d68ef5156440aff0,-0x3d38f03cd8a2f1780,-0x7c1ca34d78f273c8,-0xc9925fc2d8c0b70,-0x108a1e689d18797,-0x11a0aa7ec45b50,-0xf410f5434a3d,-0xaace30de8b8,-0x5fd6fc6e5d,-0x2a7e321c6,-0xe8c1bcb,-0x3b3ebc,-0xa6cc,-0x106]
def m6 : List ℤ := raw_ints% [0x0,-0xe8e22fbd5f1f8d87ca01929bdfd1f71000,0x17118e292fe7a05548ef8e73a2698ee15c00,-0x119e7f7e43f5448f764a723f2d27dcac84700,0x8a2b31de13a6eff1ef4867c1f142e899b1d40,-0x30d24eef24d159d73f4d26118ccd6b9de70880,0xd3f12bb48dc65c7e8b38c34a0fc1c478ee0c50,-0x2dec3c470aed18c0204e11f49697cf828683920,0x828cea16e362974b6ded01745c221a48e0fa390,-0x13619c0c037e6d2fa00e40d792245f0d24a06b00,0x26ffc6fe059ad8ff827546ce742b1127c1403084,-0x4329bf0a8b8839e22e9ad52a0dfad83c1e9ab248,0x63c2388716c68e3008086297f39153ddf7208124,-0x8087611aa707d4f86039659fb44fc46e8ccc9040,0x903cde9214289c761fa5bb06057e033d7ab69660,-0x8d6334c41204b07c93b754f3cc87ad8da9493c80,0x7942db7c31e85f6b0b8d7a33fa5fa41e9e670d90,-0x5b0cdf655999a073bc35dbf36ae8f6db7e5bada0,0x3bd4d789272219eb0128390a4896d6547dc8e0b1,-0x225caec3dfe80b6128b7e314b5f019981af116d2,0x1134fd85c6df52fcdcf7f2b4fd7191e314a3ce59,-0x77cb1353952e327457a2f7d9e118d6e3fbafbf0,0x2d150c847be9dc90fac03ae12190d5eb4f324d4,-0xe95f7160ce724f5be965f15a1f728215516a78,0x406afed248be1c17bea3fbee73f0965e441a44,-0xf0663de191bd950c8fd7b4c59ef3fd8c8c0d0,0x2ecf105c39f64c7eb37e7881f81cbf55958e2,-0x77e34b19a89c62fc5a0a84c19de474273e94,0xf78a51f6e47fa9ab5982bb5e2b200e25e62,-0x191ae0e3d1ffc5130e6dea9a555042d69d0,0x1ef30ad692f2e64e92f391a053c4c7a514,-0x1bac0c17fb70584c1250c54b40e10ce18,0x10cb10e091ff18021c40e135c2a07c34,-0x6420511b8dfcbbc2a054afdcb8bb10,0x1371f5ce84f812a9a68a92739cd51,-0x17379c407fabe6a017e54da6022,0x52b4b5b6d981f4861fffed49]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 19 42 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 42 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 44 indices rho q6 m6 6 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 44 indices rho q6 m6 6 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x106,0x1]
def r7 : List ℤ := raw_ints% [0x4ab3d349743ce2d080000,0x65c15a9a0695546408000,0x41080e38a501ffba1e000,0x19ec31a2198435e8c5e00,0x739e8dd99b7f82329500,0x17f30dc93f3e69e814a0,0x3d2adceef4607f15d10,0x7b31c01d7c460bdd30,0xc68a03cc94c0c4fd8,0x1023c8bf53401c57a,0x1101cc979d247f09,0xe828b0d9b7662e,0x9f8df9a5de503,0x576935c90d0c,0x258009b5ae3,0xc3c842466,0x2e395b55,0x729f96,0x9054]
def m7 : List ℤ := raw_ints% [0x0,0x16be16a97e4a14d242ba275138db81209000,-0x239cb02abdf0f780f00b6f6c188aa3401fc00,0x1add142bdad95473e521556663366415651100,-0xcffbf143b9a9e3dcee3800030e0dce113eb6c0,0x4886f4b821d92bc153149842892ab40036c1f80,-0x136980ba57ef9e3a47fe7043d88887fcc96ce130,0x425bc0d4007ca75a422e2bcad0f779a4ed0131e0,-0xb9ec02c8a1d327e26a2e99760acfb835c4600970,0x1b3075453bc9a954def17ddfa8efc564e81b17400,-0x35dd19139169a2d3d949a1402db3b49aefbf3475c,0x5b45e60f8a97858b2c69d725af22ede569a9a2c78,-0x854f1aed7514e029c445288572a0bd56bb409063c,0xa8c69db393fb6830e9ad19ba81de1185dbf8835c0,-0xb9fb39626bfc48ae241668e0aeff5bb6efcb94ba0,0xb2de60e7bc56a5e16d54d60775889f496ad0b1180,-0x96620ab0f334ee3c16764aac6a6ffba86225f17d0,0x6e95d6f85c04e1d1171ff578364dc76be0df8b520,-0x4717e909d17e3ecc9892fc21ce415afdc7ed6de07,0x27e61c202b55d4ecd1ca393aab076704143714f5e,-0x137fbb875e033bb758dbdb3cf13888f5f30e727bf,0x844b79ee994e619c6265b0e8bcf8f3d5e493f790,-0x30713585489e9a63f915a13a16bd62ff693e698c,0xf38d58e0b2245e7ded8af13ab578eaf7854a8c8,-0x4128dd05d5c8ce80d1b6a3bf2f7da9674ebf4dc,0xeb21bd9f8a29ae65e31936ac3c9967f4a2e830,-0x2c2653d23b3363041c3a929c4d3640a12b0d8e,0x6cb21a398f1afc24b0ab7bb5a8853920e804c,-0xd6ec26a48af25a15c835b710d9c7d43a3fce,0x14c77c757edf5122e3dfbe8b3e4850cffab0,-0x18494f670c853ddae8d9f9a661abd3d464c,0x14726cd44581c97ba80a0a8afb5bee7628,-0xb95804b0ae0c54eb1417a9e49539298c,0x3fc472de033afbd48625d81492adc30,-0xb45095b7c51ef86b56eb8ca21f467,0xc04055a33865ac1e3151e76cb8e,-0x254dbe688c74bf38b972d9bcf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 19 44 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 44 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 44 indices rho q7 m7 7 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 44 indices rho q7 m7 7 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x9054,-0x106,0x1]
def r8 : List ℤ := raw_ints% [-0x2926c152b53cf5cce700000,-0x37eb5520afa87c346670000,-0x23a418396946006300c4000,-0xe29ddd38862d927b076400,-0x3ef39cd550a96f3791fe00,-0xcfce442ead7e9c5fe25c0,-0x2104ecf479ded6ac3a160,-0x422627723a327e659490,-0x69f15de32f74c76b590,-0x88c9469090abebeaf4,-0x8edec13853c877746,-0x7897d31de08ebfdb,-0x51c97db9578ef52,-0x2c0f8b1e5e77b5,-0x127e87841b474,-0x5dc2394df85,-0x153da2bf5a,-0x318e1327,-0x38c42a]
def m8 : List ℤ := raw_ints% [0x0,-0x23890368d553c0888842dd6ee8d6f9c2e1000,0x36feb6525d6b1632fc318f5c06812d14319c00,-0x28fc8e7b2e46f183e804c09e32ddd8d3b1bb700,0x13965c4208258324323df23d56b9c7300e5b9140,-0x6be3cd06f816e798eb5f3efe18af9afc72a1d080,0x1c7ef593fcf639c525db4028528e27ae64a5a9150,-0x6014da697810d6913cdbffa37b29cb14d69bf0b20,0x10965fc1c5fb9586512a1bf7cef7b183952b1a6490,-0x263e8320d7490f2812c857814fcd96aec0238f6b00,0x4a9d4ee70749fa7013daf617a58d66247b7b6848c4,-0x7c71784f4c6695541f60132f9a17b05ec164f546c8,0xb2c6ecd1c9a0d0037dd3185f266c65164d77563364,-0xde7a31148121e62edddbb3377f3b0abbf2addec440,0xf0cad47a1f4f32f1565bade02ef49c08d8b6c7a260,-0xe3466554f3f2d26d595ac30deafce0a907bf368080,0xbb5be5c73474880d1d3250634438e58ad17d072690,-0x86f61cf3b567037cf32e89fb7d18d68c75770d8ba0,0x54e6b04a9fb66350e24d6b1fd5960f2d82be66cd41,-0x2e91de87031f123abb70be1cbd502d3eaecaecfaf2,0x163709ed494a30325517e613dae6a09d83748e6f69,-0x92e78056b3f43d0fde28ef66dc0b9892b22e392f0,0x3457df4f5bb7457f40e19d668f5186ef1595c3414,-0xff9aea7642a327e7cd101ee12a3ab9691a791df8,0x4247ad5e74189599113268afa8306e00d1516484,-0xe7416a20ddd0290800ec75e81b54b0ae91e2dd0,0x29dded2456fd2ee1e54ea18d8affcedb8cfc402,-0x630f442bbab4ec3661b123a7423708836271d4,0xbb82ce19f0016a28aece5cc9430085c22dd82,-0x11466c78fe4e8199c581bd52c550ac064ded0,0x1321a9ab5a2bcf6ac703d34ff927cd137254,-0xf27ecd179df3f44afd084cc71a615b4f98,0x8024a821e48233459e545b334c4309574,-0x28aa37b442848ef153630722b43d1810,0x688a246924c3363224295e18caafe1,-0x63760c29161d01e02e3547004942,0x10d1580d38adaf4b16d6e66959]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 19 46 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 46 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 44 indices rho q8 m8 8 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 44 indices rho q8 m8 8 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x38c42a,0x9054,-0x106,0x1]
def r9 : List ℤ := raw_ints% [0x102f775b332193d63b7380000,0x15f2a6739354a33bdd8478000,0xdf4bc7bc88b11927a2ff6000,0x5880a6abb970047dc8946200,0x188302abf78e034a859bca00,0x50a3fd76e75dafb3e3e9f60,0xcc38fec66b5fe817b9b540,0x19750f3364f42c6918b770,0x2890179ed1346f31bf4d0,0x340f1bef16a6521a4bd6,0x35fddec2661fc56f36c,0x2d30ceac4f942c542c,0x1e5680065bb19eae5,0x1023e3b0cab0670a,0x6ab43aac7b690b,0x2121b58bca0c0,0x74e9f11d25b,0x106e32ebe4,0x11dadeb9]
def m9 : List ℤ := raw_ints% [0x0,0x37861553cd52dcd554e879fd4bcfe6407f9000,-0x54f4d17810eb2fe5f1bcf9e47a66ab6f8d83c00,0x3e9396a15ed4f59515635594073d2f8787312100,-0x1d8b6b1a25ac6345f937c0c67728d385f794ec2c0,0xa0b58e44e4e551541f5542cf017d233998ae45780,-0x29e669a0ea3496838406b02dd1469aad9c3f637430,0x8b64e193b150de6b0f9554569e191b33e5cd550fe0,-0x17bb87af4d926e0ec9f01e2150d4afe234640dba870,0x35ef34cdc8dec4bf61020d1b62626ddeadffaec8400,-0x67a92e0ae41da85adbdab8aa02fe61eff55c114fd1c,0xaa36869e3e61146c5adae5fd5e5b77dcac5e17d03f8,-0xf09784f55f6552943e0549e0859e4f6dd0ef558c9fc,0x1265f7a622c78a5e8d14e29a5a87dedccb39a40ee1c0,-0x139043d88833fb1f69f213aa74d4bef973bac8d5dfa0,0x122055dcf44d8e7b6301522a10af5412f6ea65532d80,-0xea7bdbcde436f941d92bbad9adf57b233b0e19cd8d0,0xa57e1a9c3a3acb1daeadf1c4ad22bbcdd73b31dcb20,-0x65e45b021f11c4399209ce5812899ecea6ac039e8f7,0x36a2662e35612481035bce8ef686a080d6e5aaede3e,-0x197150b4d99d6b07a612673601aee81877f0dd4602f,0xa4013c30a2adfb3bc65034ab7640e9ae0f8106f890,-0x38ddfa540a40da7d82837b4a12d7c200107ab7f04c,0x10dba4548a61fb60627704e62eeb3cc5669b7e2948,-0x43c9e3503912eeef2618be9a31959ce08cf52c49c,0xe4ab9814726a7b06f93ead2ff25de9870f72db30,-0x27e91165783ed7a7aa7053f76bfa4df2a0a4816e,0x5abb035d89cb945378e079732057c9699c4db0c,-0xa45caa374a58150edfe5ae35b0e4791bb123ae,0xe6c3bd9a0cba798bd88b393c4fa6b3af22db0,-0xf20456befdb0a96ef8713fe295a8175fdf0c,0xb446dd14388d7716fb69dd22f9be63338a8,-0x58c857cd73d86c5ca13b4e93a5cd95904c,0x19f66d091bca85f395293a741928b7b30,-0x3c9faf883f8e2786383d987c74e3957,0x336fe3a08f93bb21fe804f8a5ed6e,-0x7942132d193be2ef6cb19d193f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 19 48 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 48 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 44 indices rho q9 m9 9 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 44 indices rho q9 m9 9 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r10 : List ℤ := raw_ints% [-0x51743924ca682ba6c347cc0000,-0x6e404c561927434f24d18ec000,-0x45f63e84b0ac7fce6cbcbb7000,-0x1baa5f57d93db159754d0e4500,-0x7a47c1f1c64bab1dbbffe0100,-0x1911deea12e2950dfc8157a70,-0x3f47bb6c5c64ef0bf72a5c20,-0x7dbca36f4e57759bbf8c748,-0xc77bd6cdfff8a1fa143b00,-0xfebfeef33eb2a12ad3edf,-0x106ae5dc4151628ca231a,-0xda5ed2b1775ee8e33c1,-0x916acb78ac4f8c4cb4,-0x4c9d07a338ed3e1e1,-0x1f47d21bd889f0d6,-0x991b390c79cb97,-0x2121d43543af0,-0x48ab309ccb0,-0x4c5b58fcc]
def m10 : List ℤ := raw_ints% [0x0,-0x56c18152f0d1790d54ab3e9bc674d7c4c751000,0x8348c62ea8dd46a8b53e954c079bab5e4d1ddc00,-0x5f9a391aee62f0de7d7fbfe85caf7c57d95f62700,0x2c9b956d12967fbe459df2b6713aea2b89d7194540,-0xefb3a22a64742cb76ca85182c16794c7d90ce51880,0x3db5c0720f94862d64a58757e8923dbbdce58676650,-0xcaa0429b27331e425378770f334b142bffbcec6fd20,0x2208442838112021cd62a480ee4f4b2be55fc880b590,-0x4c41c90560af5624dccdf298b2b7792f73c7ccb16b00,0x906d5f81af49999a1b600312c32d037ed23fae46e504,-0xe98d300b0fdd4c10febfefdea97c49cde817d8f42348,0x144e4b0d56a80485d10b3ec91d1c5a3af0f2077bc89a4,-0x186f289cfea56b2e21a84e806fcd54ac934dfa3b03840,0x19884fa707e2f69289de81519404a516bd5f5e8b76e60,-0x173a6754460c7fa724f761387ecf55a7a196496e40480,0x126c44121c0bd430e14a599e3fab884e53ab904d42f90,-0xcbe050bcc6ea04e86441da2606e60eb2d8a1115a09a0,0x7ae0609d187bafd6f1b701c6ab13799fcd78b54c92d1,-0x406ace4e4d16caab3eb18a31fe515949d4bb09bf8112,0x1d4a208cbb4f97af7a76c11a4cc3b98fd7e8cb9bd179,-0xb80f688f2e4f8c929afbf12ca0c06f28ee4924f99f0,0x3e1c908b12514aa7e6a44adf7b74503bc814f877754,-0x11e27fe9dfcecdb12cf0b575f5f5070b919cdf08978,0x45b3905aafc8af5dcce3a06084dd85ac108820d2c4,-0xe34ce03af0dd08d9385d385928650cf0b3e20ead0,0x263d2b6931a89022184925a270114b540f638c122,-0x5381217f693a77ececff1e9cb7d63571bfb81914,0x90b8536324ca3d99aee02a6529826a27f3deea2,-0xc171ad3bfb539a4b816da5b3525c895e5ba3d0,0xc0034c7d5e249cfb7b7bfafacc636a1145394,-0x8664a0e98eda9708c2a6bb9cbbd1f9b66918,0x3da19228d0b2e6e8876c21b028ac96762b4,-0x1097cdf39d34995a714b1976b433870510,0x2329b193bacfaef5a7cca28747d84b71,-0x1a9745274c556d66b8c93fef9d2462,0x369e8a4fcc934b8d5d4b9b05669]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 19 50 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 50 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 44 indices rho q10 m10 10 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 44 indices rho q10 m10 10 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r11 : List ℤ := raw_ints% [0x15c56a20b7007cc84590b7100000,0x1d6b98e23455a9dcf4bd905d0000,0x12a2afd0ee5bfcbd76868a728000,0x75ab5606c22deeffbe80644ec00,0x206ec00a21ce8a479d317b2bf00,0x6a1ec3cebebf5ff7105a854240,0x10b1a1e8d94f52d57bc111bf90,0x21104e16a816e1ecdcb934b40,0x34439750429ecac6da3c63f8,0x4276c08e0318181b8789f14,0x4433cec0afcc0893b55261,0x386139eaa75f42e9180a2,0x254c3cdedd50aa0472bf,0x137f5e59264f06a1554,0x7e2e7fc42c842389f,0x2629769c008b2b02,0x82456df51176a9,0x118a2e897f2f4,0x1201490f590]
def m11 : List ℤ := raw_ints% [0x0,0x878e5a1198474d24d44b91d366169123776e9000,-0xcaf113fd7d7e7021bc7cbf89586c1b03587ea7c00,0x922741d895689be362a9c43902a05aed4376ce3100,-0x436a8bc44e58570075ea629ff8e8519cb806cd58ec0,0x165fb70b2cccffa075228bd51f98592942fbf03c0f80,-0x5b081d80c8d86f64c521ab19112772782c421dc73730,0x1271b0673b77e3710b8b90e22897bf7bbd1f92dc2cde0,-0x30e915ab1d2066410c3a1bb39335c0e915c0c01e8b770,0x6c172560e23df943213c932eefcced5158ec3dd739400,-0xc9cacff97d2920e535470855d298a9302af5cdf840edc,0x14173f8314a2e795b3e0a0b2b995e830a5b61cce7a5378,-0x1b8372bf9a4d9d663262e43cc3a5c38791d317411549bc,0x20918f14838b38f21b0412f2aaf25fd974b3fa2c184dc0,-0x2173d72b06260ac1f1946df127396c793949ba4c66b3a0,0x1de3a241d83fe6544bd956955ad6006396572da5d70980,-0x1742a57557959137d29b91ef23c6216892d177bdfe09d0,0xfc4fa99a15d46fa62bfa22bcfb47d779d835bbe730120,-0x94e352ec49383810c4aa3a181405b35153da013d752e7,0x4c53588e7f451140eb8ccd655232f32d348bde752fb1e,-0x21e379ad712259b475e61c77bdde54b1e43e552616f9f,0xcfa2070aa15f799149e827284fdd3fbbe4977c340990,-0x443192a84ebd6c2df305c8df57d2f9ad2beac4aba30c,0x1312ca77aba189564ceb1a86d6e4ded726a1d08d31c8,-0x480a6f062ae650c318bc911831c7e72b00fd7b4905c,0xe3175628e8f4dac411e5406a8b3b65f67f3dd87e30,-0x24d175802d921de344b51f5263be70bb011a5cd34e,0x4d36ab695f7280ca846d6978f0ec76051ce93a1cc,-0x7ffa31c5cb73b31b44ec17db6bee005c7af6a58e,0xa2c98102dbb0a990f565ed576bb647de9bb90b0,-0x98d783790033cebf8e0d0beef850d45f2dc3cc,0x64725e67a4a1763af8dbacc1b381a8ddba328,-0x2adbe5300f051d386b5162165aab2c04030c,0xa9d473d0e8f755518ec3f1ccd08553ca30,-0x1465bd83cb3a7390c8808fa004870fd47,0xdbdb653d9ea0a776b08fb951fecd4e,-0x1897a17f8df4a5b7aaa32cf8bdaf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 19 52 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 52 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 44 indices rho q11 m11 11 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 44 indices rho q11 m11 11 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r12 : List ℤ := raw_ints% [-0x52237934b72e2c699dd3a34c00000,-0x6ed64f98839c7a03187e634dc0000,-0x4618293b1f14ba46e7e3c68320000,-0x1b9ce67504d09992e1f6e6069d000,-0x7988146be6a8b23228250baf4400,-0x18cc5f15cf42e8f63b48ec10e800,-0x3e430d250d9c719ba1fa97575c0,-0x7af88e5239ebc227f3b70dd8f0,-0xc1c48f37ba0a4f1729f173bc0,-0xf587ce8a12ee5780f25c5cf8,-0xfaebe4ecbbf3f71ba6eafec,-0xce72e10ff7fffcd6b0f26f,-0x87d479252630132c74d5e,-0x468d6683205060f9f5a1,-0x1c525e54b6a0d6028ac,-0x87cff0f3e3bde0581,-0x1ca8a49b5fde6ffe,-0x3ce797f9945807,-0x3d75838ba80c]
def m12 : List ℤ := raw_ints% [0x0,-0xd3ce6cbb7def68898bb613da4f8342c76a9cc1000,0x139cfbcbaf48c99cbe8735caa6cf639153a45e61c00,-0xdf938010a029c3f913ea4f333cf165f929272c79700,0x65fbe82e74e2b28f80d8746ac56ec356d22ca6483940,-0x2174e1bb9f87d9e9d83efd937ae163dc94e18fff8e080,0x867f5534cfdd2a8b83d52fe34de5e365cb4ec5f598b50,-0x1ae9a14ccb88ae12ff2834f4a50d79ae35141dc4720f20,0x46724e4955d56dbc356a84589e925e3912665220039690,-0x99979ec224d97b1eea8874ac0e45ca201ed84fffa66b00,0x11ab8cb2ac98e8baad0a27de7374a86bf753ba43bec4544,-0x1bbc93567f3f3452a99eff395e0b50da69d3963b9a3c7c8,0x256739ac420e521d29356a06145a30a99cb88e5f985c3e4,-0x2b9101e8baca13f1d32d3d0f7290c64d83d1bd378ccec40,0x2bff494b0390db2a74f10b85dbd2bc408c776931beffa60,-0x269dea7456b3b9345f07e4110edf00ee4d9b2051ac1c880,0x1d7e6f28fef69288b0bbafa342c2bf6517a738b9c4d2890,-0x139a7a403033d3f67cb9debca3f9c5c6c881a3fd05f27a0,0xb53f98eb25b9974243de4b6323a74b14829f5529c3c161,-0x5adf2fc9119475ce537c60af7efb22fb833933fd26c932,0x276769133e7abccee0b54c30bc9a9b565bf97e18da0489,-0xeb68209cb3857208479c5b938779c1e87ba81414610f0,0x4b40d33e0c404b8c270ec1fcbb7ec4cad962088f82e94,-0x1471eabc5797d9aa15724142503b82578f71521932cf8,0x4ad5f8d0047ee8e17f77f11c44aab9780801e708a504,-0xe401eee414200a406d406c88859c6e64f40bd2df7d0,0x239ea7eb5566b547e2409490b289418cabfbbc17042,-0x47b82326678e15bafd3b9abccd45e8343996977454,0x71a47c03e34d1f444004f1f409c5620108e84b1c2,-0x897eaf288ff6fad1184413bac9212973731eb8d0,0x7a0a56ec5469cb73647dd4dbe7c63fa66dd88d4,-0x4b418bd5e4836437e7fd67ff3954e2dd3f9a98,0x1dda51bb333da0434a914306783a7696423f4,-0x6cb96880abff447445955455315d2038210,0xbd536ab4fe2d9a14126518a666d563001,-0x7191651cef8cefecd47eb3dc8fc1182,0xb117306aea578efd00de09a2c479]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 19 54 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 54 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 44 indices rho q12 m12 12 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 44 indices rho q12 m12 12 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r13 : List ℤ := raw_ints% [0x1185ffeb531dc1c8087119ce2100000,0x179d8ca49402d65aeaddb123c990000,0xee9cb14c3a806797d52557ca414000,0x5dd986cf4f0044ec78232224199c00,0x19c54cac7fe6fb651db9c008ddf400,0x53f894b1c81f66dbe807d721e7b40,0xd25e5c8778377aac3320b8103200,0x19e79af423f817e9a1b907c223a0,0x28b4df65ec75572bc0365c94e50,0x336bc4f502d7f9b52bd9e3b014,0x345d84e8491e044ff9efc5048,0x2ae955603d048df407e97110,0x1c1a5c46f0710e74b6cac11,0xe84f56b20d066c272222a,0x5cad0538b951930adcdf,0x1b926f38bbcb817cfac,0x5c46b4ed213c208bf,0xc206e6f76e77ea6,0xc13f43c433639]
def m13 : List ℤ := raw_ints% [0x0,0x14af289e4f4c61356ea4c7f051c3d18579694ed9000,-0x1e5672b226ece4031661ceae00674af812b0d378bc00,0x1563a047bf4f796c37cda09ba55cbc1e898edac4c4100,-0x9a6bbcc7663052b905bf6480188e6d048163ef9df1ac0,0x3217530f08ba7fd996e04608ef445c43b0d1cbdcab4780,-0xc7063cf8c86eb63412554090b7fd14f29ef813756b2a30,0x2757899bc903e881fb82ad6485cb789f44899efa7e86be0,-0x65aebc0eb1cd7c3200c06441da56d5ae31b7d5d27a63670,0xdac79361da3e7117353e6c5d169dba24f9fcfde2c96a400,-0x18d2f4b9149916c39c6cc300c57aebb75e5c4ab43d5e3c9c,0x26682123e6bf4ca2e4f7dc3f52ea1decee15958df2a99af8,-0x33037f98edb59ace31700d94ee8664c748fbb986f682457c,0x3a7bac0bc57c52a6a48b7f10ff0cf6d190900aa28a3079c0,-0x3a1563d821917e57fe88c3a341d7bf2cd2f44d8020d9c7a0,0x3217a41b3893e198b1c8fbf002518a57130559eb3a56a580,-0x258e319bc53d4e3eafeecf85fc12ec78f747c7e06eb5aad0,0x187a1ae512a4d21a96389475504f1cbcac521076658e5720,-0xdda754488853e9512c1cdcb53b0446f61ed4e43cdc50bd7,0x6cb3d451486f648cb7f5c7c70cbaab37ea8a22ffa2285fe,-0x2e0a142746d3821981629a341bac2dca175a89fcfe1c60f,0x10c36efab3051b59555d02b690725fa7b8a52ad852c2a90,-0x53753a36c9b5cbc91cd53c1467df658bff622e782041cc,0x160649a956a901289cfda8356ca9a4bfcad7678db24248,-0x4e1f872d4564f10c5116e418c0572b5223d3c4ac9181c,0xe6080ef8c97296c34fba38c159c3dcc9c13ce4c6d130,-0x229eb791ce77cb4cab0e3135ae2e94e3123d07b9e32e,0x42e81347644f555216fc5e126b2442ee6186509948c,-0x655105df6333137ffadf88d62957fbaca09290a56e,0x748a92b068dbee6ca8a4cfeb0101db970170f23b0,-0x61bb825b64da7245fbef2d802554b1705a3db48c,0x388269e05c663907d8c189e68956c83bca635a8,-0x14d2fbd90b9c710c36d8eb5850be10d3c941cc,0x45a6f71737156881b30bb3c9b81a03c2c930,-0x6dd4be8495e9831e9b7820a12b96d23037,0x3aa3fa7ffa913948f39e2c0572e94b2e,-0x4fabbf195674935f09688c2c8f91f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 19 56 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 56 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 44 indices rho q13 m13 13 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 44 indices rho q13 m13 13 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r14 : List ℤ := raw_ints% [-0x37196fb37bc7b21eb5ef823251cc0000,-0x4a2b0fa623422c76f35f2a6eba56c000,-0x2ec70a3e4f4dace398c1648e1db1f000,-0x125f4a308c728323ab5b4e8a401de500,-0x5097a2327e6935ff17db2c554c34700,-0x1062511897eb04d4a7842133a75d870,-0x28f7850ab48c3450b5cd4167d2c040,-0x508a5d3bbe56554ab1e892f98a688,-0x7e418f9f1fd08addfbe1024e56d0,-0x9f0e954d259d7536adebc9079df,-0xa17bf6f1468c162ebf628006dc,-0x83df950671ca398d72e2f0465,-0x5606559bc1cac1d463e83fd0,-0x2c3e74f2d63230dcb2db5b5,-0x118eeb4b93c7fa4511c5b6,-0x53127ddcea229c2b2ec3,-0x1140829a0618b30f404,-0x23f769e87baa2accc,-0x237439818e8e50a]
def m14 : List ℤ := raw_ints% [0x0,-0x2051af775be757e37ce178677fc1f7608db48b331000,0x2ef0d11c3462e1c215fea2e1ea46443b1d344a6ca5c00,-0x20c2a4a95d9415697fc647715ed4dac03335a080000700,0xea088b33507c9f4d2ebeee8aade5ffd85482c2dd9c6d40,-0x4b16737433a4593d83822824a8ace5eccddcddf77252880,0x126f4b4d2be6acef874531bd3ed505bf2b040d50fec60050,-0x399da922afcdfd016598c57e085af26ff74fd72106324120,0x9313ceaa3a0f91cba2d7c2453c4869eeaa55a7d70eb40790,-0x13860c2a616a7be6216ac1822d8b5789c775aa06a9bee6b00,0x22f7a516e0fa98f263b96c1a86c03cf75fb842236022ca984,-0x35568596823e0e1d9ae11b498518437f5ab652aec5830b448,0x45ccb1f10bcc7be740d2887b8a3c88c18b41142ba25382224,-0x4ec743d0066e251ed76d1f872d61ba40bd7dc4e3fe338e040,0x4cf69e29601201cf750b570653ced5bd322ea0bd1232b4660,-0x413ba1a41eb4c8e9db557d7b43916ec1d0aa97bee50bfcc80,0x3004ab87674df8192008eeee8c5bc659d44a0746260711190,-0x1eb1c353a89aeacb41d2ab0af3108a8a31f3b6472725ae5a0,0x110491d3c9239e10b0d9630cd90ee343838530382741ee8f1,-0x82a2b2a4678d94da7ed90718248f8a3ca482a4c23ad2f352,0x360c51eaedf97a71c52508cc4326eb510ef26afaa6881899,-0x13312d06cf9f3d9d51ee085ab16e6ea7db63934b312df7f0,0x5d023da371d7e4fde2e9adc0bcf2b873fcb16ef7afd99d4,-0x17d77eb32389f463bf08f854f21a2614fc4926249c48878,0x51f2802e299ab94de270b335678df4d5c15c0409bb1b44,-0xe92939ac1e73adfc807a587e117d52bccd0e23e9254d0,0x21cca18be0347fe65330911e5994fb83fbb422b00f162,-0x3eaded9bc457484ec33b16fbf338ca850ca178cbc394,0x5aac6f7dd020ba8cff8a8e7749b92a4430d21c246e2,-0x631cbf44cdab3d7ffa9862b6e8a797a688f0631dd0,0x4e7b9f7bcea2f4b80e3b0e9b0fd093cb8200e5214,-0x2a856c08c9ad45bc1281da3cafe7cf8096bc6418,0xe8ba5d1fd01fb0d001baf8ddc61a35e5921934,-0x2ca5c0915a12cc65763a3ccd7f32479ef8f10,0x3fb63ebc5d690e4e733de9781389008ed91,-0x1e444bf89e47b0b7d3990af24e0ca30a2,0x23d44365c41b845a8a7a59b34bc389]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 19 58 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 58 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 44 indices rho q14 m14 14 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 44 indices rho q14 m14 14 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r15 : List ℤ := raw_ints% [0xa1bd9103ef557e7cdf8286f095db80000,0xd97caeae61fb3983ca87c46a356138000,0x8902621728caabeb33a0e15cdbb31a000,0x35be2ed80c129cd2c8b07b302f2d21200,0xeb6b5372d9d8ee0cefc6158b1260e900,0x2fc907cecb4dc23a8f21345c64a54860,0x7746f544cf7f9900a5ad97197669290,0xea0cade1b43b4641f16b541c33c790,0x16e1e0dee6b0f145bd360aad1b14d8,0x1cc22e5960e6ba75562c3dd62fcb6,0x1d1e97d09390a011a0371cf10681,0x17b560a72239429788f96fa36f6,0xf69c391223e65d9fe33268a5b,0x7e5849bb77829a7d020fcdcc,0x31eaf64a2e8e047a9aa2f0b,0xeaf6df951eee994d86b3e,0x3081712a217f17968d1d,0x646a76b7ee4a85bdda,0x6229a615d9ed4f14]
def m15 : List ℤ := raw_ints% [0x0,0x327fa22a7f99795373204c21b79f1286dd6a197fc9000,-0x48a6e394d5339cfb26e6966c0c85193f9da1b449c2fc00,0x3234f5e5a1bb07a5dd61a1c18c3e742fe3c904200bb5100,-0x163025cac4145e49a992be96faab2a957f2a985f513766c0,0x70b14d78845c76d835a023e775e96c4c756fe2d6e5e9ff80,-0x1b5c7116b9885e81ed35cfe9841faccfd6c539d954e524d30,0x5487202a39d1ac00c8a50da7670550baab89ca2be6983e9e0,-0xd52d589485a90e11adcedda2d08bda0469bce279bac232570,0x1bf10bd8fb28d9ff4a631c8c54518bab06957c896096e5b400,-0x316264762926273c4aa36b6e3490ae5ba9c4b76447f5dd465c,0x4a49accdfd05d7caf85010cd22277f73cb5c9c4d98412a5a78,-0x5fcdcf45aae8936b10f6431ffc6d715f53a66dcfa7ae3f7d3c,0x6a7a1a5ead0e9c5400df3e0d220c78fcaa06eea85de77365c0,-0x6659af7590d9c37d8db8bb5ee61721f1836c4298de4b4d1ba0,0x5546fdec2f74ec79518477b1766f2eb3a90950cf760bd20180,-0x3da533d7f52a0809bac1e70cd7c9752284dc6d28c89456bbd0,0x26a79850ec88ce7450f70f252a5027b7d7196d6da5f385cd20,-0x14ff5d00b1e640fb1ff07807fc69dc7860d092656c150803c7,0x9db58e3307c63e3e785736434f8bc2c9479c5184c0b005ede,-0x3fbef9dfe75161912089688a966e2488e41cf7e33674fd37f,0x1613a6e1d8f7f9e3a7968f4e6c0c30cb3d02ebfa55d405b90,-0x6825b0128a6aeb5d4ec24ae63a901b6bafba7bfeaf308c8c,0x19ee856efe5ed5a5b579e1e070c7e5da637279ec1b45dac8,-0x565c8fae945efe552fabe8c14f45098cd86789e32ac1bdc,0xed68dc8604f7918102a67dd1ee471675582b86fd70d430,-0x212440db5f3efadbe99fc7d691a53e4caeb4538267910e,0x3af524a41872f9b0dda60dda7d53402fe80f7da31734c,-0x5172622439a452c0994497d19c0523b5b6331cab034e,0x548f0cf7960e04d21e2d6cd825a41873f13f1bfe6b0,-0x3f3065dc03c988e69e38c19d2b2fe32d3384fa714c,0x200eb2620cd6ad15232a61f019e704ce602997028,-0xa2c124e61db2fb4e3921c2e519e80b609be0c8c,0x1ca2281b7812b45d3bc662328545c5b9d77830,-0x24f498f329570509c7d71f744cdb04a0c227,0xf9d9cf6e17931c62f7c377badbe5b470e,-0x101b5ad7f8bee220931c252c4e53b8f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 19 60 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 60 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 44 indices rho q15 m15 15 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 44 indices rho q15 m15 15 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r16 : List ℤ := raw_ints% [-0x1bfd0fc744fe990b18aab3243cd97700000,-0x25996f1d375d9bcef9bcd848830a1c70000,-0x17a95771f86bb317ab2dc670a1c492d4000,-0x9454d39c1c39817a5e13f168767cd76400,-0x288f026118fd2ef9c7430fe7faa4928a00,-0x838983a6e2e930a9730a35dc60a27e5c0,-0x147d3150fd89641fb7c3c4b5b30c90da0,-0x2822b84aaca53321094755c68bf26510,-0x3eaa0901f18ab637695c242ba815f30,-0x4e9726ff7986fa48606fdb77305534,-0x4f63c8a16dedf096aefc54e50340a,-0x40779b425eb0d4eb769091ff5e23,-0x29c9590048340daf68e5958468a,-0x1556279ace0d4d26ee10365edd,-0x865d326f1467e2c89d725bb4,-0x275b2193192a95fc2c4acdd,-0x8156f7d74b6736c38fc82,-0x10a3186890becf0ac59f,-0x1026fe82047f4829e6]
def m16 : List ℤ := raw_ints% [0x0,-0x4ee76d62675fcd9263e276f4aee88cf2b9f5c7d7aa1000,0x707aaeddb2264fa243955ee96942ed68464ca9b340a9c00,-0x4cfd6538838ce88ec93f058d8cfc0aedca0598e0a30f7700,0x21afe4dab82f1a9ab37259821523d172158fbd6757809e140,-0xa95413a0da711b3aff74d314c56faa1e4fdca0e2b7c31f080,0x28ab4043e99bc621ef6ef51e69c53d5e99cf9d64539791c550,-0x7c39f59e3a48180958e4bb36293097b1eba8f063b1d8199320,0x1359bee9109444d43ddb97de4f9bc787d18e3922eeab5330890,-0x2814c4306f48eda7f81edae01766e4f704b15ecab05a7896b00,0x45ecbd715ae0a00e6f3a5341df767647910b0babc9756e051c4,-0x67c26d23ec4bc421260b4c350cc69acf3cb15ac9cadf76f68c8,0x83e717f4365135b2e422fd4da52f0235aaf196f21c33dfde464,-0x9064f309e4d1ce3b8ecac3be82632f9a80314d3be1c61981440,0x8898d811f6943141fb33bc184c80495329e63d00605d2335260,-0x6fe729e8ab98cf1bbb99e29f709566a8af172264a7118ae1080,0x4f74937582f23b67364e92437ced22ea431bd7bd6d8bc3eea90,-0x30e1ecd942718dfc07ea34ca637e572ae681cca3f16782b43a0,0x1a05269896c2eb524fb50817d70ac3b2e84e37ce541e9499981,-0xbf3ea016e679f56ee0944754b0b594297296a7440249161f72,0x4b871cdcfa9740b2500239b891ed8b61efcb89459fc6461da9,-0x19834c3dedd9900fd5fc7a6c02cdf6b15de3ee19fa9e1e4ef0,0x7529f8ad5a4e1d8a48fd421d981117901f275cdee9072f914,-0x1c55fe5aaa6bf312b7792529e7cc4dca738ba245f6ad01bf8,0x5b6dee6420ea9b66b620f01ac84e07c0364ccb41c5c67584,-0xf2ce33b17e25c8a8b6da495c42d14369c10ee1e9e2b01d0,0x20a22c4171b53efe2f290385246002d4ae7542dff986482,-0x37ac72fae00bb7f32e1a4a9f57c4c504d1419992a446d4,0x496a9be2774ba89b57ccdedaae212e7064f9a3babce02,-0x485c6e7cc3a93b8b1511511f4f08e16e4d601f8dd2d0,0x330008cd905bbf5fe0933f49a41e179776852d1ef54,-0x18363936b4b558fcc8c7a670db3178508d1f7a4598,0x71f16da04571c8f942670da524a10b1573688274,-0x125eee534508f27b2dc7cd6c24c69cb0e582c10,0x156edc32854aa4c1b0f6f79fa95a55f961421,-0x80daf272feb4e53bfdb27f86607ff6a1c2,0x73cf658b60c1ee208ea60852d926399]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 19 62 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 62 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 44 indices rho q16 m16 16 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 44 indices rho q16 m16 16 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r17 : List ℤ := raw_ints% [0x49afc40cba938194fa3e299e7f9533880000,0x62e74c803e85bb6db1d26572542e96248000,0x3e2e6be55f15bb6c900e998034a9eb19a000,0x18566b765b93deef22228ca9ee181eccee00,0x6a5a5a72237dce3887a9a39f578aa9f1e00,0x1587b7925d56bd0f3558bdb9f855538f7a0,0x35958d16609203086f367d8fecc2eab740,0x68cdec377f6f7d2b8bdeb1230e9425610,0xa35ae9754b77bbf9107dd450212e1090,0xcc7ccf7c54e1e7e98f4420d12e1fbda,0xce22e09f35edebde20611572f7d36c,0xa6ffff8953c77f94275ad04faa7d4,0x6bf6df3180c0c3bf3950120db51d,0x36f748c2f2299225265375d167a,0x158feb3a9d9a5d086d07966e63,0x64abc1bdc02efd504e565638,0x1496c5c8472c1541aa55443,0x2a2a11a0d8b90146d0070,0x28b35d1d49856a6fb81]
def m17 : List ℤ := raw_ints% [0x0,0x7b499ae9c185b134bc11d9de514b5c3b42900840f9b9000,-0xae3092221de45bf44bcd021d950503e23dd7c92815093c00,0x7620c86acfb4c80e8a237e77bf55025f87f84a5deee2b6100,-0x333084b1105412ac93997b012b2dad84dbfc414df3166a72c0,0xfeb824592cae6069f52cea8a2c8635a98884d0f5241d303780,-0x3c892c2606e312089ff8ebb9b9876f7f8eb71ae37dab0afa030,0xb6e1a7548208b3406c6da672d768c84e3c2c774c25cad3347e0,-0x1c28e33f1dbd4a46f9f42624959531d951a740101de999de8470,0x399fe54f7dbeed83ca0165da7fb202a630873e983678bff0c400,-0x6342281cffc6a9d152eafa7fa10bfebb1c946f6ac94ff116ec1c,0x91539bdda1f6b591d327092b7be0891c2fe2ac4f0b5048d411f8,-0xb6278a5a896d0ef7d3b8e4515c7a2cc7e2abda5ced985068b0fc,0xc474ae1378164304d76ed7b83937265175b3f3931add787d11c0,-0xb6f11635c2bf083c1aeb0b2296bdebe32ac3e21e2d777b8eafa0,0x93635c063b9eeb9e2500d31547f3415a5191ec8b6172a6e91d80,-0x66cff3d2dd438828ceba0855b0f7dfc4312134d1565b51943cd0,0x3e11e9a4c98b413984fd0cd03c31c74fa4b7ed7baa836f0f6320,-0x20619f623ed95cfed38f4c7e5e33a86eb532dc0e237e7d042ab7,0xe8ed919fb411ede3791e3574f65cb88f9ae0f88ded1949d65be,-0x59e36ba76d6ad67ab0417c2c748d24d2447ded44f7992dd07ef,0x1d9e2b1cf81b0a71411fed4aae3f90f324b8103671ecfd19c90,-0x8468ce6973107683f6e95e81a50f5112b22cb45c0039cb434c,0x1f1a7d17492aa5f849362345ae5c10d31b328ad32fb1f87b48,-0x6139b886304c8bb20c1330d742f8357a6cc827c7558fd5b9c,0xf96444b5223a16dafde2e672251a34eb944f29649df98730,-0x20439a9543d25fa2cbb3231e627485d1ee788cb25bb7bcee,0x34c546e1370f3b3027e44e3d745b4d862719c412191fe0c,-0x42669af0ede2a4f628af254a95d10f799a9c9595f79f2e,0x3e19e262f2fa404c5eac22a5f40adbc1ffe0ce210d9b0,-0x2941cd73c244972497b8f648079a6cb48b236762ba0c,0x12510497bb414f03310e548a1567a6f823f4773d2a8,-0x4fd91f7ce0445b04477e1c87c0309025bffef234c,0xbca5b3d9c702b60e7d4b97af156a1e0b480d730,-0xc6dba97828a619c9ac4716370c59e0ae2a317,0x426d94df1b123104d40e4e7eb8f5fb8a0ee,-0x340648f40b65a954c3314394e7e3f4ff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 19 64 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 64 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 44 indices rho q17 m17 17 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 44 indices rho q17 m17 17 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r18 : List ℤ := raw_ints% [-0xb9acf11ac1231246146f8ae515e003a2c0000,-0xf9050674d97e1f7ce4185d0873c4a3cb4c000,-0x9c6cb07da22970bf0112bf5b3155c1605f000,-0x3d2a798245109c85f5b33145f8c48321c2d00,-0x10b02d45ee11428f11ea7f35aca9778958d00,-0x35fdfad7aa7f714bea3434b37726fc19d9f0,-0x8634f2506ddf9fad451868f31f7b58c5fe0,-0x106215dd7e40132334fa3b2f3fe05e62188,-0x197f3add2bc9b8403922040c509761bfe0,-0x1fdd06e38ab3506b95ebd78eec1c83197,-0x200f794fba79b190eab669a351a8fa96,-0x19eb78f7703b5e4d56551ed5510c029,-0x10b7e46c9b5c54d992af0f0266200c,-0x87d528c21045c56cf34a213af7d9,-0x35215bf05b25be9bc2a77fc2066,-0xf73f1b56bea1bed587425894f,-0x3260df1cd7d290912cffb2f8,-0x66bb9bb9f552f4f773d820,-0x62aecf1ee956d1dda8c0]
def m18 : List ℤ := raw_ints% [0x0,-0xc0a3020d3e60e4e265dbe46b5f05c01c98010ce586311000,0x10dd535b0e2018ef7d9bdc00789aa7f7878a12a4ea0de6dc00,-0xb559867e909e90aa805d021f89e6a76716f24cb93e6865e700,0x4dd9df4355f7fe40a8c79b2d57a83595279162d501395c49540,-0x17f9a1c77c478d5bba2327e7f3ab8e16b89453c7b8ec79673880,0x5a3bdd6c8e7d3586e034ca08ed302a41070bbbcdd2b6a4f1da50,-0x10daea0c25f2efcbeec86ece9fad2899b028bb041b004a55a0520,0x290f14d239031dc78692ded750cf152d74d984566c4d1cdb19990,-0x5307bfe4d4e65d554b6df58a2227723521179c815294421776b00,0x8d3f1eda8f0082d0e8b7fe4bab8228c35309e2cccb249b6237e04,-0xcc1a1d3fde3187139daca1786c085cf7a2e9b6ee94b3d6f7c6548,0xfc4ce4709502e2a727ee55604a51ac842c3de62201d63ae254aa4,-0x10c25da5aa19e264cc1c07f68771d85ee02cf4c7be914214ce8840,0xf5da93414c1a242f30def72a9798274249dc40090afdbf9621e60,-0xc2d5d4b85556d8ebf3a6b7ac6bcaa3b13628a0129e735e4bc9480,0x858c282e0121a18b5fe88e8e4631da7e2d31874c81f174635b390,-0x4f21e31cd1d88cdcc1950b03bb3ea9d4d7519b95d90edb44e41a0,0x28774f9f217289ebf99bc9ec1f2a81706a202c54c03e12ed86311,-0x11ceadacb7cc0854f63fe1d00220dd01eb6bb6a7eeef7ad846d92,0x6b7323b21f1002cfb0478fd9d8e6e0547518cdd69bf4aea523b9,-0x228951c76895891c6f9d02b4aa7c5828f679cbf5a95f8c5e15f0,0x964e95fe60100ad38b0c86152cd06a220e28aaddeebf0ff8c54,-0x224ae6e54fb26a1ae63b729f4d8ef795802f3b5d1a575a96778,0x67d65643364b8ca7c773e627d76c9817d7de298fd2e554f3c4,-0x10139eddbfed835611679929dca9f5cc57eaaa0b31b6a4fed0,0x20064c58503d024e565e931af52d9960e83d5f4f9c7d2e9a2,-0x32334a578379efa5671d54c7a674a564e6d2856614943e14,0x3c3fc4e3529ee9519961ee8f075913e75d1e9a37f406722,-0x3570fce786776803318739845fe4163daa1449b993d7d0,0x2172795309bc6e99d75231a1f4eab6cd093722c9fa094,-0xde0aceacc8a7d36a947de3de25142ed9215ef8ebf18,0x3800fc533f081ebd47fa67bf4adc01bac642aa9fb4,-0x791b6d105c94871f9610c3cde526fb351d5a5910,0x734b259158e6384f33e273649346142b1433b1,-0x223b5aa9fc657fcf7b21d5e0df236bd284e2,0x175ccf28a4add37c336207ba3a9c6b4a9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 19 66 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 66 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 44 indices rho q18 m18 18 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 44 indices rho q18 m18 18 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r19 : List ℤ := raw_ints% [0x1c23075fe7fe81b8d3bc9eef15273d901000000,0x25b55c4cfd75dc750864f5afa0677b599640000,0x17ab0f12e871bbcbc2924a338bb2ad8669f4000,0x93f303909f04edd782f904fb50461ac1bbd000,0x2853d0ffc6be5b43adf29dc53c0b9092981300,0x8256703fc5b217ed7d7ed0efff558fd93e700,0x1439ba85885c986109867f08467865823c610,0x2774673fc4a1079aa0f8adb92898b3c47620,0x3d51975de268705ce1f45ba133e4f89d278,0x4c83738945bf0c71b8f2188f0fcce41560,0x4cdba4d6357f2f0cd5ad39a9bba542269,0x3e05adb229d2ed727dd073400f8b5d2a,0x27ec1931f09503e5fbe1eb6b92427d7,0x1439e0d6b311471225de9419d14874,0x7e41fc00ec56c993374a95c53027,0x249dd61c00dd1c05c30adb5351a,0x76fcec3f5691c1689c69adab1,0xf1c08a038a0a7f63ef3af48,0xe73fa3abfc4243fc48be0]
def m19 : List ℤ := raw_ints% [0x0,0x12cfeb334b17765a1bf2794e7c478fc2cad81a426a1aca9000,-0x1a21b1dedbe158e52792c9f21c0566546b07bd21adb5b8b7c00,0x1168f6eb7e2cb36ea3cc3eb99804ea11f96223722bfa9fac7100,-0x767f1e28b96a1df3e9f2b80fbf3baeceba5c68a78e3cbbc43ec0,0x24254b69f336c54c2aef4e6fc45d5271b407447df0fa14335ef80,-0x86af83c2ad20efb0743ad05d3d4179355297ab60c79721fe62330,0x18e5554d4a90472ddd1772453d314158b25dfac5996d3d6b7485e0,-0x3bfb292cc75e9c7fdd9785c94b5096bfac3a64ae283c2868c75370,0x77e58a479bf3eb87d76e48b256c4d4c34186ac6432f5f11f47d400,-0xc97c1afc1bab44dab15b763aa3826440ac70bc60846b572bbceddc,0x11f6abd3b486d0318d8e27aace07d884edd07fea25b60869a764178,-0x15e7b22960060d2a213a217295442a03cb1c4bb152f51b879d5a0bc,0x16f289e6cc23b30c984d67643ca2e7ce73f8ea3c83567387b297dc0,-0x14b84a43323fabaa9513e7f40b60bab5c3cccadb2b7eaf8f59c83a0,0x1027b3652748484b2100004521419587ff219ffd4c63483285bf980,-0xae2077e5cf5b68f950637d948dbb3cf89ee2fe16ccab5cd6c12dd0,0x6548afd64ee3ad6e77a632e2114adbfee5c179b040188011011920,-0x32c6d9a589389a0ed548f07324948f8313e1642b4f37c1a2ec70a7,0x15dfb8d4c0f4fd77406e19f07283e00b57a93d5186288289187a9e,-0x80fef560a1b9db37ada49302719ea8a5e053c01374bb33c61d35f,0x28728d1c3701ae048d943675bca8047d818b75db7d8016c10ed90,-0xab5e8a5b05fd897f991315f3dbdf2742b5a4c7d354360373260c,0x25f8e4d24e05dfbde1faf383b6f9aca44df4a00360abf192a3c8,-0x6f5df8bcdabf261808cc94abd100bebf2b9ae2c1c949820975c,0x10a62095a987e505a969e25a001fd961c41d673d80588b3ea30,-0x1fe87989b30994c93c3e38180868e8772e54b93871410246ce,0x2fec01dc47c40f48d2d508cc985cf986c36ea65d6626df4cc,-0x36d5ee534c86e978ffc32e7915cd6222d72dd480d90e590e,0x2e1ba90b3b4bd4092b1da987b603d07250ae29b0334fcb0,-0x1b2b99be1df8a92f83d1bd26d42df227b1928be8494ecc,0xa87780d228894e4d8a2ab2a555f1eca073e3946bdd28,-0x274f67645a1ae14b22f0a1e1336520f84f1975d460c,0x4dc3a27a66aaca385aa7021288c7aec0287dde630,-0x42d4cc2b9be96b1ede49dc4148b7a402264c307,0x11a232ac0df1d064a7d5fda7315df54b338ce,-0xa7ce212118302b8314d67a85bd48a956f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 19 68 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 68 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 44 indices rho q19 m19 19 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 44 indices rho q19 m19 19 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r20 : List ℤ := raw_ints% [-0x41ef3a4d274cfeef38790e06e2f098280a800000,-0x584e213ed2b4c9c09796def955cfe1dd84680000,-0x3762b5acaa75c594629e39af4e6a3ae8178e0000,-0x159f0550ffb2fd288250db29034db0ab05732000,-0x5e367922d6b514cbd808314f2430079ee08d000,-0x13034af9f906bf0952c73c4c2d62f2909492f00,-0x2f2831ea6c6c527e6288e238b0a95dfb632900,-0x5be2f73b2d45d0d3a742a88c1f597b46e00f0,-0x8ea0c90e3e77b1e7ad66fd1ab4331a410be0,-0xb1ba48b15f65b7a46cae90266c899e34ca8,-0xb24246f45d399d12dd71b10e3c71c35ca0,-0x8f9c54fc334a5e061ae3075aca24516f7,-0x5c44d8f604fc52d6bfadeac35efc26d6,-0x2ea6c81669353060c4fce19d55e6169,-0x1228d727c16d6ab2bf3bb8c1ec5b8c,-0x540cf8f405810d9a6ecb78611199,-0x11059f159520fe0d910fcc4e4e6,-0x2279243b5476ac3b385040cef,-0x20db0858b1843157a726ab8]
def m20 : List ℤ := raw_ints% [0x0,-0x1d64df802554a8eccbaadd8aa22fd0a05cf1a907c5c9dc81000,0x2880755d1846e5cc7acc3ed45b260fb6621c17849f6bf09f1c00,-0x1ac1bf32787bf5934d5e6c8767036ba3c8b676b142bd173735700,0xb4820f3bda6762e629bdf15b2c1570ab9d931c61585c5d0408940,-0x368d8cdb687acdb6d753659b6c640c891ad6b9689b16dd298d0080,0xc94e207e0f41f2366d21ddd393b39783dd9aaa009a42a0916b3f50,-0x24d4d73b5d3a323a9342a4c36bb99db85b794fc7fbac147d4459720,0x57c997edd027c1b991f6e485dbfaf958ce023a7b061b5eff0f0ba90,-0xad802a16d0a86ec58ddb8d83cf84d326e3728579c09d08c1bb86b00,0x120191b241a28437c6cc2a3f9335e58d90805e97245f0512e4966e44,-0x195ce6496da8b6f4997638a87d2b44020503562fb5e32014aebc29c8,0x1e8441501d087f68ee35f4fb37f4c277c9f073e850212bd6de6094e4,-0x1f849b4c1d8b5c9e0802d9c5d64d38c8d410a8f886fe98263a803c40,0x1c0841466c62322e5b6a1558be40b13347d73fb59f624b087821aa60,-0x15820b65a2d9e4102fdb0d9c7eb2cb9ba19c55c22aadf009bc7b5880,0xe3e149d05e1959d356fbaaba58e4c5a12203c14d278e40c71d46c90,-0x8223cf0884337e3f4f66131e027cdd8bd397830a13c7393bce1dfa0,0x3ff8a6149c9a56c39b7c02b59566dacd2f9949d491b88072c18d5a1,-0x1afb040ed3ea6de8f28bbcd6534596dd690abada294492f3113fdb2,0x9b847ab6e68041b7fb9a26a48322760cd930818212e8b748b73ac9,-0x2f929c8274d5585ee016c410e8228fbfd7fb4e6f23b59556644cf0,0xc437e180124c1617114a2aba889c96b6644d4fa57c5bbc4569394,-0x2a396dd10e40357a2ad94c200a70cbe6b57a298ae4864d36beaf8,0x77ef2edeee262cde6a8164945eedca2b2c1f28ce67db776cd604,-0x114f3a3d7525b94920898752827e2f0a6a4ac1f86d10467d4bd0,0x1fe8c2ef716fb9eec4bc0d855615b378e0e604784cc4345a0c2,-0x2de67d370c681e319f5e6ee2507c065876f4e370ce39f2e954,0x320e2e08fb0dc26ee98d8ead6eb78c3c2f6e77a4a47693242,-0x27e0d7d9ff72382903e9923d7a6bf8ec8f7fd1cec27a2cd0,0x161ce96066b3471b2cc2656789cc1a214b30ebaa5faa5d4,-0x7ffb4867a0f24fe438107a401d400bea52336cc575098,0x1b9c7da44a861be1a1fedf1779fdcf5ef87fd527b0f4,-0x31f0e09b39e554ff98f02d0c2c65ec387fab231610,0x26bb21b3d305f6ca24a4fc15d34e86e0a09adc41,-0x91478cf747c0644b2722f158d47144930fa02,0x4b4e47f5020767f784cbdb5d10a4b1c6b9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 19 70 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 70 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 44 indices rho q20 m20 20 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 44 indices rho q20 m20 20 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r21 : List ℤ := raw_ints% [0x95e2f9108638c3d3f77aaab01d898290257a00000,0xc89e31479a9ad17779f5555833f9fc55a05aa0000,0x7dbea2957d080c22d19b3d092d51016183eb88000,0x310d4537c8924497c12dc3dc77fd39057420b5800,0xd591ee3bd7b1e1c7ada337b23234453aed174800,0x2b100b8c23f94c06a276ba9fc11fb9bfa22f0480,0x6ab4b0c7d19bc95598158c785ed0f753f4ab500,0xcfb41d6a0a176a0a083d34393bee85440a56c0,0x1420934efd580a936ba34d31300709423b6390,0x190c9b615738453f87fc18ecb6767140bca28,0x191700c2fb0c27859bb155391ccc8c4a73d8,0x142eccbac74f033080b785a0af362515478,0xcf2252093b8d04bbcbf1ae57f41e5d209,0x6889459f2bdd6e21186297c96bf7adfa,0x289bf689a8e5c64061c859d09564f97,0xbb88d1578c48269f01f8bf2fb1864,0x25e24846bbd4ae5080ff6feaa8e7,0x4c81ba55eb4aebd0d01f233442,0x48af5adfe564e5cde2daad91]
def m21 : List ℤ := raw_ints% [0x0,0x2ded9d383a5447f1fe3afa289d6ab5fa9139981c250b68899000,-0x3eca6e8ac700f7692351771ae577e848b19be4bf3918a7f89bc00,0x2924a49e8ca22645e041a2f5bb27f701d304fe76576f59014e8100,-0x113300e0540eaf3478ba6e337f9bf0393868c7b417646ed4e50cac0,0x526ba8ae4f33a623ba7fa94dabf4f1538e53b52d95d6297f0332780,-0x12d45885127b1891b4a2054384706b84381298c3eda40f9a0d88d630,0x3693299bd5549d7970c9c6b6761420a14cf85e8bef55ba0ec4a5a3e0,-0x80b8444b058fecb7c90e97fc110b7e54994eb82d29db3387d53c9270,0xfb9813308d434a9457b03a11383e7ec0a6f16005ae3d1b342c7ae400,-0x19ce82f4896aba3eefc917d26f941253537c8cabfc2f93eff5add0b9c,0x23e70ae2daace3d5c0bb0f9a16c114bbed115e5aa98bace9e8f5868f8,-0x2aa22c650b098e59d4f056aa617c2487b9acde5cd80aff74d55da0c7c,0x2b6be4f89ec90b2aa9705eedb6b1c38581bdf6ce31e6e0b0e6594a9c0,-0x260c8af744ebf76906c779bf4ea1447ccbf215ce8db712aa8712497a0,0x1cbbd842edee189f6c5a757dda9743a75c10f11c69104cc63820a9580,-0x12b50c7598fad9e46963a2b682cb40e8204b9fd81016edbdd54508ed0,0xa7dadbc6129f6c955a4be0eb4415d69767bd5c43118f1bdfa450ef20,-0x50e9cefcde05903b5e85ac39018fadff7bd869abb06641677a32c597,0x216a2bd5309059fdb933c0ffce3b8a40693a464dfa89ed804cde7d7e,-0xbc45044227ac1f36b17763c263c0f4d0cd2e3c7028bfc76074da5cf,0x382ffbfcfd0191bf0b9872cca424b33d9b55654109b5bf8e2ff4e90,-0xe19c2c8087d4f8d0552e24325bc368158f7435b14881586afef4cc,0x2f256dea67180d9c5ec8204632d7f8f723a7f204cba0bb2674d448,-0x81ad9618e3fb5ae568570142ce47740fe1a33882f965ba7fd8f1c,0x1210a46883b61e159cc61a1da7452cac84639bbe33fe29622fd30,-0x2006263653aca87765b44498e5a8b20d3133b5a0a9e30e050eae,0x2c1b16b4263958bd0574c19e239638a9bb8e2d52f0d4f84178c,-0x2dd1eb79d6ae529e9763f727e6c848be00225bd41520cd10ee,0x2291e6d2c663a06d0e65bde3b07077945e2b5ba47924f4fb0,-0x12074ad175408fcf7b39832627d99c85bbadee923894ef8c,0x6156c8a9ab1e8cc1fa9f6ff716f4aae4c58a4a1eb00fa8,-0x1367d5376f06243b0a28bc14296317b9dd4050f3d34cc,0x20136ee5e88559f6739b6d5f60b8dff6a1ca53da530,-0x1670ccfffcf020cb08d3414dfeeed476babab11f7,0x4ac79b8f27e803e76879b498cc3de1d52aeeae,-0x21c8bafb066af5d4022cbfe9deaf03d8cdf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 19 72 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 72 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 44 indices rho q21 m21 21 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 44 indices rho q21 m21 21 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r22 : List ℤ := raw_ints% [-0x14b96677d6bc587e8fcedd386fc782a3db2d4ec0000,-0x1bb91179eeee6af65423ef572f1bebdd0ed6fe8c000,-0x115d9b034c58a62f91510eaa7f961cddd5e5a877000,-0x6c5069682edc411b7a51afd5c539da1ade440c1d00,-0x1d740539cd55eea52e53fcc4d315d123b72f9cd300,-0x5ef1a68b33b23f1fada26e96c160b0e3a44d18ef0,-0xeb0f28024310fcfd702dc1c5df33e466785ecb00,-0x1c91c6838c74665a40655f309108097109870048,-0x2c3ffbb56402495745a493b0d6b5d73b1c77e30,-0x37023a24d29e851770fc95d8eb25b57ed11707,-0x37079542287787cf15871307104b38f57f348,-0x2c34f28ac70999d511a929219ed73faedb0d,-0x1c50316b77a3b6942c24f6b9f84594cb168,-0xe43fcfbc0401daa2267c98a6c7d45e64d,-0x5881be5ca965d2c9f14aa4926b8bb6e6,-0x197e727abc0adeec46478beb9d8f73b,-0x52374ee70f9a4ca814269723463cc,-0xa59ee34a72355dc2f531491f7ac,-0x9ce8193f51ce513ad448ae7ee]
def m22 : List ℤ := raw_ints% [0x0,-0x47c345a7db23b06a1d3c26df75f6bc5782e9fdabf9e1d356f1000,0x615edf76d08ccb1abc5ac980a91e028b29fb956ac9368674735c00,-0x3f4bffdc66a70915fd130080a4f052ffdd44b2cae16753deea7c700,0x1a3d9d8dc75259ebec059f1966ddaabdf47c45824ad2a2afee31bd40,-0x7ca6d635463a616188ab5163bc81940a9a728282b1f41e3cffeb4880,0x1c37586dfce9711481016787694a489b89f96457865b3d5090bd2f450,-0x50fd9a875778a7a2d75e68d99a232f70941aacb0ee98f7b1e604e4920,0xbd13714aa017fbcdf343fcecb549f619416cfa135ed11f12607416b90,-0x16d9563a16b2cfec701c756441755c69717ca1df4408819c17c34c6b00,0x25124260aca0c101142e1d5aa77fef37ce1943b480a174238a659d6284,-0x32f35b86e4cf3143f057ce089f17ea2ac02eccb5679d406a8c5c5b3648,0x3bb9eafbeeaa99a0da4fdb71f0b6ca0e5d79754950702fa6aa54060324,-0x3bffde3e1699cc178a232f455e23190839889ba2cb20977efbcf113040,0x33cf7f1fa2c3a9209b6b22329fedd0498f2bfdca3bb7ffbcd55f6bf660,-0x26848d6f1594e20f8ec9821476d168541d50462054957b377f21da5c80,0x18a8df5c2b80378d4b4358dc469d2f76d09cae96201f7420b9451a1590,-0xd94fb9ca88e6050c4dbcc8757fe0bce799d2a3c7839280a8f29a41da0,0x66bd6ba1a84d9cbe992c90fb4ca0fe687dcf5bc735c48bbc578218131,-0x298c733e8f8abeb3484d7315cb5ff694182b9ac050d4dde880f3cefd2,0xe4d8c0041c9963558e539f11fb139d6b5756ee94979891e89c9f72d9,-0x42a26e3c6e59ccca204d270af9c077e60dc2b40d5e04cd4397d7f3f0,0x1047741b4392f56d056294e749aee5f664838d7dc38f6ed007774ed4,-0x34da90e4177f6acd65f4905af7cf82db129c3a112c6f1033cdb2678,0x8cc2abd47c8ed1220127f87ff040ca0e884736fa1dd4982a305c44,-0x12ec655985bbb9bcba9bef433725887b4bcad451a403c14100e8d0,0x203ff4699e4b47350d9c95e89a920ece864e17e9279863f6fa9e2,-0x2a833dfab6ffaadcab72dbe39d20a67d001185dfebd38d3b8894,0x2a0e1c1ead69a9bce4135f416f37604e25bdfab8c79e7994f62,-0x1e0893b8276d510506e86edf7163322588501317a99455d1d0,0xeb8f31bbb9bf8467a83cdaa0ce0e73507ef7babdbc323f14,-0x4a1ca09aa32734449c27acf33cb59e7fc87ac1786f97a18,0xda5456cf515a41ea3ba12bf4d0c9e213e7e25fc7af634,-0x149a5592db7dde277ec8476d915f0f4f0ea2aaef6310,0xcffb135d657446ff2f63009251f66366345d29dd1,-0x267a1efc3680406c71c669eb8d3911af1872122,0xf26d4fdfdb8aa97eba862cf16c0e8a5a9c9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 19 74 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 74 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 44 indices rho q22 m22 22 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 44 indices rho q22 m22 22 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x9ce8193f51ce513ad448ae7ee,0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r23 : List ℤ := raw_ints% [0x2cbce1cb821c0ebc1310d285f28d6c312b75dce80000,0x3bd09200e06eb483669e1bc87df5997bf3b0bc0e8000,0x2572560756b6d0ce86f8f583ff23499abe47452b6000,0xe96b7a90f4d07f15a70b5affe069b46e2cf5d1b2600,0x3f6e01d4ca4c2a46bf7ffd085b44fdbe3d880143d00,0xcc51b9523b052358361ab59dcc5cdbf26cfaa84e20,0x1f97199fcbf5e640dac416297d30eb53ad5c2aca10,0x3d6107348e64fa97d79b88a542ba8188d0debeef0,0x5efa2c5f207aee9a822eddd66b81f0848de804d8,0x75f29998fb76f331b63967d7808d75af8a95c12,0x75dbf9ac1ad9f6d73c07e0c2b4bc41a88da519,0x5e9007d669fee5ce60a31c2cfd3890ac00f3e,0x3c7b90b7a54a5115f14011502e9cf7783733,0x1e6dbfc35b3292fc977210eb7affe413f4c,0xbc7a15658e2fff56b4765f0668c625df3,0x36310746f8277998f003a18504dddc96,0xae69cb3f1898c4fbf2aaba35edb365,0x15e90b92208c70e9c927a0813623e,0x14b4bab0beefa2b2e6e506172f4]
def m23 : List ℤ := raw_ints% [0x0,0x70211cd64667c3a5cdadfcbd28518648bc8d9c5cb670da37d89000,-0x970819469c44ea23760f19f2fc1adf5fd04d1976da653215f43fc00,0x616d8f81c2236b92572558915d37e05164e132d4d5d2e2b2d0219100,-0x2810aedd42d44ce78dad911995b2142b802e2f8e0888edaf9c1dc16c0,0xbcb5e36560179b3b4b445baa1a1196570e72398ab3b9e2e518bdfdf80,-0x2a55d90e20f593e0dfaa52d7138af94bb74ebfce72ac8c93c19c5ab930,0x785f9883e799a7dcf909df55cb51044b61de2389ec15f221488f04a1e0,-0x116387189902cef714d560a54a443582abe3bdd1d7c696554488f0d4170,0x214483e88314bc4ad4304ee96ec6058b3ca50491c2f9c52507e9f19f400,-0x355f6347d7b56a4821bb5e8c4576d812aea6eb6f21ad2c9ff3f1ba1055c,0x487c4e9d728513d2a00e4503abce95295e54f2324786436a5fda0ba0878,-0x53e628216e926ee155ee13089b984321c794126be436e5c015c2605b43c,0x53267f665a66e81ba2b4e2135c9170da8d0b3ee428ad36eb394121a95c0,-0x46c57a450dd18bbeffc965ae2f5681eb04bf55e1933f21392c0cd04eba0,0x33ce54fb4d9987ac00c39fa3aec51de0ae31a5b3a4ac5b6216b39f4f180,-0x209ee25100013c5180b8b486f990ab15f9166ba40fa06bf74e945555fd0,0x11a6035dc9edf22512eeda6eb0b37f78378c47d8ec0390172154c14e520,-0x82f3c6e4c76c9d36ced74f46f8c94d558570e33c2a0dbfde8853f81987,0x33dd77fd96c889bf1facca08f9159ab051d8f79e58fe9976ccba8a4e5e,-0x117479042210841a012d71c743065e255fb4f14cbec1c4df1f9b96ef3f,0x4f577cb22734ced3b04b6ac39126c64f6afe11b967bf2196c486dbf90,-0x12de914d4739f13f1dafec9544b05e8b1d733007fc6709cbf90596f8c,0x3b7c3830f4bc28cdfe961f8d3a0220795642e232d127198b68178cc8,-0x995ec57d795d81a4513b55db8801d7ccd9f8ae5a2fc989632c002dc,0x13e4d84012427fc6b8a0a37344d3b2df326992b6739f5d84bf9c030,-0x2095ca5db57769e23eb306c82851be81561ddd6a79ecf35143f48e,0x29194c3e9b77e83c320e2cf4a2eb8e74789b4013508b802cf264c,-0x26b2a5eaed6e66fbe0ea934f9436ef0196ce85eb2a7ac4b7a6ce,0x1a255e0c529ef174bbf4d51d74d7b10ed7da3aeb592d972d2b0,-0xc0a79554045cbc4c248189bdc7b8ea516ec5cdb292c805c4c,0x387b49d890bb94f8435c3c9bd4415608b0ebeedffee6ea28,-0x9997da1fe86d5f36b115ce5991d54c4ae4b442ac37af8c,0xd3bdc328ba31fc8100c0da7895a3cc6fe368de1f1430,-0x78712cb89e3c8a5b6d88c91fbbb6e81224d5e07fe7,0x13ca68b7e335e593df2d805c4c5d9ab6790da28e,-0x6cb1255ccae7383723c21ab1e137cc704b4f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 19 76 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 76 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 44 indices rho q23 m23 23 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 44 indices rho q23 m23 23 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x14b4bab0beefa2b2e6e506172f4,-0x9ce8193f51ce513ad448ae7ee,0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r24 : List ℤ := raw_ints% [-0x5e75d3d19007eb08de48f43400de5e600fa23c1f00000,-0x7e3b8f4e2f74bb2f57df15c6b2ee7b5da5796f9ff0000,-0x4efc49806b86c30f86115714941086c2c389396a44000,-0x1ec11060bfca9c099fcf73442babbb1c6bb40afa80400,-0x85a1a793ce22fbac31ea012f4ef7d30cb2529c161600,-0x1ae29682e5c7bfa4b7783d48325406b127cd85dc53c0,-0x42759b9fcd4f8e5660dbfc111716c2a61339a3117e0,-0x81069cd62153edeb2cbf06c9bfcf19b3d5178eb490,-0xc77acf2c9c8095a1b293ecf10f7353663282539d0,-0xf77d60f4826bd1e36ade9748ad142fe8f474ac54,-0xf70c8b1f59698a8c6ce5de49130b61025d3c6ae,-0xc5fe17e8b7fcc38d79cf7543f27623ed1370eb,-0x7e7b11a03713710ff2c34ed0a83f78766f242,-0x3f8bd3122ba9716541cac3eb0eafd38b4b45,-0x189062559141a5b600ed8c998fa27338e34,-0x70d1aa6f6675ae485522249cc228a6fb5,-0x16a72eeec783f7f4081966147832252a,-0x2d70ecc473bf4959fe5427655e4ef7,-0x2ad921fc230204aa90856ba51f82]
def m24 : List ℤ := raw_ints% [0x0,-0xaf33bd0ece0221b3115fdae78eff61d1a69d4450dd1054f74261000,0xea5271a9c5c91105f019773297b3f61f438677c9b53e1e424da39c00,-0x960947583deedbb99df201b331d85735d5b745e8d13192b6bfb733700,0x3d37b6e4b13404eaedeb74b7243f72081113679edb61a22bac578c3140,-0x11df8083986905dad3061ac22eaf8b8ffddc90f523a61846d26f04a1080,0x3f98f3e2fc7db7d5c09a8c6d223ae2a5a2ec66ccaef8594911b6c4df950,-0xb32b8bc9226149b8f17570e13696d90e2bd6844d77f54ac2edc6c061b20,0x19a1911c46dc6e50fe19379df9623b87bbbe6e2e437fc3345a823984ac90,-0x308832b465b0b62cc6142173607c0648eba3e64ab4c2e29ca6c460336b00,0x4d02dce623bc2f5c4773f01f947bbad2c19115e63b31e4988b4f05a09ac4,-0x675fb1882f7cf200459d21aa40a8587625fa3d7f7173f95d7ce9d8ce0ac8,0x762b5299ead88b81ce52f3ecbfb375653f54b65cf1c0ab958b425f4fd564,-0x7390fc4c13f6be57848f51ad96994590c8f291a272a1d987cdfdfda56440,0x60f85a354490c34e7b4935b0a6b3d5fa7beecc40013dc48270d6684b0260,-0x45e84a9f1368dc4e328d463215b117ca0170843d3f9adba1893bc629a080,0x2b4d156be352261d12bdaeaccbc4cbf0e984288b869f9419fe499205ae90,-0x1703fa32c814ac54243d3f29ec3b8b93c121122ee9a9e627e32161f2fba0,0xa78999a85dd514bedbd7efa6c5721d0fe021d44957e2ccc3caed4e1f5c1,-0x40fe117b582c3565ee627641c864e11b7a334031b575834cb8bdf1963f2,0x156295509c03b3b629234e793e9e4a573312a2cdd7a2e75e363ab21dbe9,-0x5ed833749f9b6ce0274753c53235b9f7057941036d25302608b8900af0,0x15f51fb00a69f16c05839b4eb9cf746197445668cc48dfd3829becfe14,-0x4334a5cbdb855ba06628f685226b85b7e1c02df79b0073c95b9e299f8,0xa7ba3615d5cd0e8e0f3f2741f6bda0a21decf6862a1ccf2e2f1dc684,-0x14fcb5e7dd8613e8cf7607620aae465a463971b5b71d1ea7b34cd5d0,0x21078abd12739f7523bbcc21e5850b8cbc5c557962549cb125a2502,-0x27d8600685cafbd50653c2041658aaa80c683fd73c5f0ee24d5bd4,0x23b1df5180060d41d6535c9a0d5b60fea8d7d4626bd9f166dde82,-0x16ce3df69d37488ecbd7709aef3ecee844b5024320b7ac4bc6d0,0x9dc9393de450d7c2a1ad7d415836b32abdc79667ec4521ac54,-0x2b153c7eac1b161f4fb1203cdfdcda556b2acf89baae2bb98,0x6c17cda90bf870a1ee8a62f256376656a35f31921cbaf74,-0x880176f2e83551cfbe5e196f086955629a05d8c0c4010,0x45babf9da7151e83977a8e2743fb5fc0a9039850861,-0xa2cf80dd77581061f3a5fc5edbd84813da0c1a42,0x30b7aeb294d829d3a8bdac5d2fe96108d6dd9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 19 78 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 78 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 44 indices rho q24 m24 24 8851357879958761795198771200000 25=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 44 indices rho q24 m24 24 8851357879958761795198771200000 25 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_24
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<25) : intPolyRF (mz e)=rfPoly (C (8851357879958761795198771200000:ℚ))*rfX^25*(1-rfX)^18*momentRF (key size) (X^e) := by
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
#print axioms moment_source_24
end
end CatalanCore.Li2.NVMod.FamilySource.U6C25
