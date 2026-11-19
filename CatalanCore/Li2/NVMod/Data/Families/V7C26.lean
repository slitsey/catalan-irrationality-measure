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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C26
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,26,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x48fde0093cd002c0000,0x63b41fbba9d719cc000,0x3fec390252bb7227000,0x1992adc8695eb904d00,0x72888594a6304bfb00,0x17d68ef5156440aff0,0x3d38f03cd8a2f1780,0x7c1ca34d78fa5cc8,0xc9925fc2db2cdf0,0x108a1e68a24b1a7,0x11a0aa7f2bee70,0xf410f596f215,0xaace33c37e0,0x5fd70e7ff6,0x2a7e826e0,0xe8d18b2,0x3b6130,0xa9e3,0x130,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x9,-0x14,0x113,-0x56a,0x32d5,-0x1d0c,0xe0a8d,-0x1f33e4,0x5a2d01,-0x6b5110,0x75b4217,-0x1bdbdd8,0x1662f69,-0x1182e30,0x242f7713,-0x1207b4b,0xfa6b067]
def rhoDenominators : List ℤ := raw_ints% [0xf05eb00,0x356a6,0x2cb0,0x1ad,0xd0,0x41,0x3c,0x5,0x80,0x51,0x5a,0x37,0x294,0x8f,0x8f,0xc3,0x4100,0x8a2,0x45ed0]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 26
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x12,0x99,-0x330,0xbf4,-0x2178,0x4884,-0x7c50,0xaaee,-0xbdec,0xaaee,-0x7c50,0x4884,-0x2178,0xbf4,-0x330,0x99,-0x12,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 20 li0=padCoefficients 20 (liCoefficients 19 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 19 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 20 li1=padCoefficients 20 (liCoefficients 19 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 19 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x68,-0x1b8,0x4ec,-0x9f4,0xe38,-0xd68,0x596,0x596,-0xd68,0xe38,-0x9f4,0x4ec,-0x1b8,0x68,-0xf,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 20 li2=padCoefficients 20 (liCoefficients 19 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 19 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x2e,-0x32,-0x15e,0x7d2,-0x160a,0x2956,-0x37dc,0x37dc,-0x2956,0x160a,-0x7d2,0x15e,0x32,-0x2e,0xb,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 20 li3=padCoefficients 20 (liCoefficients 19 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 19 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x3,-0x34,0x1e4,-0x7e0,0x13e8,-0x20b4,0x2184,-0xe86,-0xe86,0x2184,-0x20b4,0x13e8,-0x7e0,0x1e4,-0x34,-0x3,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 20 li4=padCoefficients 20 (liCoefficients 19 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 19 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xd,-0xc2,0x38e,-0x776,0x1ba,0x1f96,-0x5cba,0x913c,-0x913c,0x5cba,-0x1f96,-0x1ba,0x776,-0x38e,0xc2,-0xd,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 20 li5=padCoefficients 20 (liCoefficients 19 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 19 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2d,-0x13c,0xdc,0x10e0,-0x4d38,0xa654,-0xc474,0x5aaa,0x5aaa,-0xc474,0xa654,-0x4d38,0x10e0,0xdc,-0x13c,0x2d,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 20 li6=padCoefficients 20 (liCoefficients 19 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 19 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6d,-0x4a,-0x109a,0x50aa,-0x9266,0xe0e,0x1b65e,-0x38aa4,0x38aa4,-0x1b65e,-0xe0e,0x9266,-0x50aa,0x109a,0x4a,-0x6d,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 20 li7=padCoefficients 20 (liCoefficients 19 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 19 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xed,0x74c,-0x3fbc,0x5a90,0x15578,-0x5b754,0x8a444,-0x46576,-0x46576,0x8a444,-0x5b754,0x15578,0x5a90,-0x3fbc,0x74c,0xed,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 20 li8=padCoefficients 20 (liCoefficients 19 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 19 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ed,0x278e,-0x62a2,-0x259d6,0xa9ada,-0xc115a,-0xb872a,0x2bf69c,-0x2bf69c,0xb872a,0xc115a,-0xa9ada,0x259d6,0x62a2,-0x278e,-0x1ed,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 20 li9=padCoefficients 20 (liCoefficients 19 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 19 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ed,0x9b54,0x189ac,-0xfff00,0xeb868,0x441c04,-0xa8ed84,0x63ef2a,0x63ef2a,-0xa8ed84,0x441c04,0xeb868,-0xfff00,0x189ac,0x9b54,0x3ed,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 20 li10=padCoefficients 20 (liCoefficients 19 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 19 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ed,0x21ca6,0x11f896,-0x26f156,-0xae90e6,0x1ed907e,-0x288b72,-0x3e757a4,0x3e757a4,0x288b72,-0x1ed907e,0xae90e6,0x26f156,-0x11f896,-0x21ca6,-0x7ed,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 20 li11=padCoefficients 20 (liCoefficients 19 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 19 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfed,0x6ec9c,0x709954,0xbb7370,-0x57d24a8,-0xdb8ce4,0x1502dd74,-0xfdd3536,-0xfdd3536,0x1502dd74,-0xdb8ce4,-0x57d24a8,0xbb7370,0x709954,0x6ec9c,0xfed,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 20 li12=padCoefficients 20 (liCoefficients 19 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 19 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fed,0x15f47e,0x247238e,0xc8960aa,-0xa252b26,-0x5780e1ea,0x464b6f06,0x9ea4141c,-0x9ea4141c,-0x464b6f06,0x5780e1ea,0xa252b26,-0xc8960aa,-0x247238e,-0x15f47e,-0x1fed,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 20 li13=padCoefficients 20 (liCoefficients 19 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 19 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fed,0x443c24,0xac0123c,0x6b9a0ae0,0xde3e5148,-0x20a2b0d0c,-0x3f1da2bd4,0x4a7284e6a,0x4a7284e6a,-0x3f1da2bd4,-0x20a2b0d0c,0xde3e5148,0x6b9a0ae0,0xac0123c,0x443c24,0x3fed,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 20 li14=padCoefficients 20 (liCoefficients 19 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 19 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fed,0xd17316,0x30157e46,0x2eb58c62a,0xe033b461a,0xb05380b6e,-0x2d039defc2,-0x2e87931024,0x2e87931024,0x2d039defc2,-0xb05380b6e,-0xe033b461a,-0x2eb58c62a,-0x30157e46,-0xd17316,-0x7fed,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 20 li15=padCoefficients 20 (liCoefficients 19 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 19 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffed,0x27dd7ec,0xcfeb0264,0x1239e94750,0x8f2c27c238,0x1927ab2a18c,0xae9c63aca4,-0x2e34f9131f6,-0x2e34f9131f6,0xae9c63aca4,0x1927ab2a18c,0x8f2c27c238,0x1239e94750,0xcfeb0264,0x27dd7ec,0xffed,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 20 li16=padCoefficients 20 (liCoefficients 19 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 19 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffed,0x78c866e,0x36f160ebe,0x6abf69972a,0x4c4f31a0ada,0x170b8c015286,0x2f5e2f7e4a36,0x1ce11babf39c,-0x1ce11babf39c,-0x2f5e2f7e4a36,-0x170b8c015286,-0x4c4f31a0ada,-0x6abf69972a,-0x36f160ebe,-0x78c866e,-0x1ffed,-0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 20 li17=padCoefficients 20 (liCoefficients 19 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 19 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffed,0x16cb91f4,0xe4bec33cc,0x2578b4704c0,0x24cbb5a98a28,0x1041ce20558e4,0x39398ee0788dc,0x6a08ef18049aa,0x6a08ef18049aa,0x39398ee0788dc,0x1041ce20558e4,0x24cbb5a98a28,0x2578b4704c0,0xe4bec33cc,0x16cb91f4,0x3ffed,0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 20 li18=padCoefficients 20 (liCoefficients 19 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 19 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x13,0xab,-0x3c9,0xf24,-0x2d6c,0x69fc,-0xc4d4,0x1273e,-0x168da,0x168da,-0x1273e,0xc4d4,-0x69fc,0x2d6c,-0xf24,0x3c9,-0xab,0x13,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 19 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^19 := by
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
  | 18=>li18
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
theorem cache_li (j : ℕ) (hj : j<19) : coefficientsPoly (cache.li j)=liNumerator 19 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x1cb17823012614af1b9000,-0x325bd97915604b3a0f54c00,0x2ab776e438e33fa86c54fd00,-0x1752eb540715f17d377bdb3c0,0x9361d4c7a936c9b8ed9960240,-0x2cd9bb49d33b2fc3740183afb0,0xaf0b80f5552852413e0ff2a010,-0x23270548895a9a59c0e3c27d450,0x5ec6d87914743974b86e8df1670,-0xd9759d983d5c89083aec9cd7e1c,0x1ad21c5c6c50a35bfc8620164414,-0x2de42551b7de483f192388b2ecf4,0x4480ba9968641e09016c769556bc,-0x599f97585c3cfcbf042109089160,0x671e458d5427f4b805610ae99d20,-0x6894bb5585cb3a0f93d739052a50,0x5d9e4e537f8477c26f21b29a9370,-0x4a018c50a43ac42f5e0d3a149957,0x33a49a2a1e75532db935f739b1f5,-0x1fc61534d7bdea282b439d62502d,0x1133487ae9608053916f353b837f,-0x82af75ed270bfbb5f4719bb2ddc,0x3637bb9bd64cc2081de24762c94,-0x138c88e1cb3b73c13bb69bf68e4,0x615dd20f2a10b7509ca21265cc,-0x19f31ad4414c6343e5a572b31e,0x5dc0171656446f977cb5f9dfa,-0x11b2e28f24ede41e1c8a7d23a,0x2bf2b77cbd95df1ebff198de,-0x57c38f3b97be8d4df04f1bc,0x88e6e5a2e3f344b2371ab4,-0xa045342cb46cede33a7f4,0x84f8e4b55584598af9fc,-0x47a7b6e44a81712ddc7,0x15b12a99916bcf9585,-0x2cb8e7d167e7d86d,0x13b674b84345ff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 19 36 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 36 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 45 indices rho q0 m0 0 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 45 indices rho q0 m0 0 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x2cd54bb6b1cb80519b11000,0x4da3c5c23065fadaea43ec00,-0x40f62baac7c31ebb969a2c300,0x22f9c4e45517fb5f43278b3c40,-0xd9da1603b12728c4ad961a4dc0,0x4152f8a31304501a76f6e06c2d0,-0xfb1d934cb06a2875e7075446f70,0x31a6489ce6625280cc625a252eb0,-0x83bc694436cf96b29de1e6764490,0x12950cda60d507f467e7bea3b8504,-0x240d469ad7e97600d227a9109974c,0x3c9d08f7fa6da67313df7a71923ec,-0x58dabb4ac22c486a9c13fdbcf1ee4,0x72175e225d1a36a62d57d551256a0,-0x80bf205a9a2f8e6108b94ac2f42e0,0x7ff83b7dd683fd4ea6b4d36941810,-0x702ee41e0f7e1cdf68a864825b930,0x56c556f7252a5c104c7450aca6fb1,-0x3b30bda61faff7b1c6870753089a3,0x23900f4aa59b45b55dd0e4ab48a4b,-0x12c7402d1f7c0701b4f8eede650a9,0x8afe4d434d6dc037e543d3902e44,-0x381900d9e7aab1a96da37436f7cc,0x13a56d1970bb924817455d3aef3c,-0x5edf4af9a9821c1ade2f6c90694,0x187719db4aad82d50d844c45e72,-0x5552464dad559203c26a5bb9b6,0xf819026aeabefe5da29938736,-0x24f2239a422ba31b9be3c2cf2,0x4685453515461738580b1464,-0x68a4ee6d5977c03e0df13ac,0x73d852d4efbe695a9782cc,-0x5a31b0853f57e836ee8c4,0x2d25f0cffbdb077927c1,-0xc84e90e383da3de193,0x172c2e6c6e8c0128b,-0x8e9e6482e2dba9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 19 37 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 37 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 45 indices rho q1 m1 1 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 45 indices rho q1 m1 1 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x460d464d75cdf87f824a9000,-0x77be47eeea1e9fee598160c00,0x62dcd2ca6d30273b182af2ed00,-0x348158d140bdb9bfa6bfb68efc0,0x1427b58c48f48e193fb03945ee40,-0x5f509d977e368672856e2f5da2b0,0x16905175b16041385018569125910,-0x464cf62d5f19ed05d783962960950,0xb7a0cff57918eb623eb67f9c9b770,-0x197c9f5a32dfac7a0c9a14916135dc,0x30a152b140f136261c2951afcecb54,-0x505d8f282a7e42250b2cccabbb1e34,0x73baf57430721f2440a4fbe281f27c,-0x91e2cbe8f51581c289edf61b195160,0xa181fc5b9101ab02ad88aa6f996d20,-0x9d607aa392670d53801f420ea4d750,0x87244fe2cc408fe77de3ef060eb6f0,-0x664d5d50f4842638b1a59bc11922c7,0x443bb84da70d388d473e25e84e0645,-0x280acd62ae452a89dfeb69ca7000fd,0x14a0b9184a38a3caa2c9d81e8d41ef,-0x94c4361467e87438b6c616603179c,0x3a6af27fc53cae163732b3072d5d4,-0x13df8093468f480055c9ed3d11724,0x5d0cb3b4b0346cfcf8c080b0358c,-0x173783d6c7d2d413e05e03ea42fe,0x4e26dd816486415f8b4012d519a,-0xdaba50a16e1a46eee851c843da,0x1f3effae9dd21713dda0edc7be,-0x38fbdb614fbc7b9d484b83f7c,0x5064f041c2736bb0479c87f4,-0x5419b1b8ed0388d6c346f34,0x3d63ba83371a2cb5fa503c,-0x1c83455577f53e753b237,0x73b86a6914554f326d5,-0xc012b12554f4ea13d,0x40745afd0f0366f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 19 38 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 38 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 45 indices rho q2 m2 2 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 45 indices rho q2 m2 2 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x6d74bdd90811d4473b9481000,0xb8bee4cc8b8ec5d8dd0d072c00,-0x96902209bb65062f60c38b77300,0x4ee7b1354ea0ef0ee155a439a040,-0x1de0aff90cdacde7b714dd591c9c0,0x8b523b0e87ea8e4f7646daa9e2fd0,-0x2081fe75fc53109c5ddea0830fa670,0x63c937e476c042c43e9a441fb6a1b0,-0x100ad35cf6a89590f8bbbcb18279590,0x2310f01aed5196bd2490669ac93c544,-0x41d2c0eef7eb8a797ec6434d3231c0c,0x6af4954a445bc5c63aee215113fa2ac,-0x97597d27faf44ab28add78e3a4cdd24,0xbb5b5a94be01012412d47169e2396a0,-0xcb8cc27d633785b6e0bb4a3e88812e0,0xc27f4e2cb871e8b7e2658b953951510,-0xa3a530ead7f6f45ce1c8830ba75bc30,0x79451ad59ad1b4192a8b9f5ba35f441,-0x4f1a7e520a885e07af01c182e248053,0x2d59bf02aa3b2259954db96aee8cd7b,-0x16cbe9aa67fd43531910d1c5feb7eb9,0xa03699852dfb3193989b39054f3c84,-0x3d37b55e8542b0ab554ef17f52928c,0x143b167d5f2768b23ce339cca084fc,-0x5bd8b791614ab33004a1c5a3f8dd4,0x162c2cd732ea7a54d897c51420a92,-0x48089891cc9c2128d7d083d88416,0xc20231043a245e38a7fe5eeb596,-0x1a943d94487dc506f44661c5d12,0x2e4b5bf82540ed771f4bb33ea4,-0x3e106c529f6da9275b9d1ba6c,0x3d4ec2d1b27e6ee39083558c,-0x29eb4abf5026e8b4249e304,0x120b8245b2adaea3514151,-0x42e943a6bb4fe537f343,0x637b1fc1b106cb35bb,-0x1d1d3a17dd931db9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 19 39 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 39 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 45 indices rho q3 m3 3 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 45 indices rho q3 m3 3 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,0xab0668a31c9bdbaf4d18099000,-0x11d22a41a76ad77118330ab34c00,0xe576494716b5a6388e4ca4ab3d00,-0x76b42a25fa8b5025a300ad4338bc0,0x2c5a3386eaf0836e33d4555c45b240,-0xcc0007ebb9cc06e8a90e6452848db0,0x2eee8cb69aafffff9ba218429bb2a10,-0x8dfb09144729b5a4a0b2e88c23d6650,0x167c528ec667df6c6d81a40cb3838670,-0x3064eaef454f10fdf1f56f54c3ad239c,0x5965a06c90c64cee3e42f198657f5094,-0x8edea6056d9bd5ece620247bbb52f174,0xc6b9507c592bea59d1d9a1a6cabdca3c,-0xf1a66c74abc4ce60e0a4638e1ec59160,0x101b5b49a60982f5ce9dbad617b801d20,-0xf189a89c23c9e5755e3c8d3cdb5ed450,0xc72bb81d5e75f0895b894001bde20df0,-0x90857d6f4ab2ad23154ffbd3d81a7db7,0x5c36f5b2ba2c29e2044555ea53de2e15,-0x33a86f2c2c7d493d1d976b6a02a6e64d,0x1957a4c381ab5fc1db23b0befd61455f,-0xad960ec4703906e06a879d3e60c075c,0x408c07f01ffe3713e24c0a424ae1514,-0x14b925c692628c9ee33b85ca0217f64,0x5b398d9aa35a42995d61988edcc04c,-0x154e754c3674fa07f1c25ab9097dde,0x42cc659f91266eb8bf211192bdc3a,-0xad18d85a6324c760f49aeb563e7a,0x16bc5affdfaaced77fb17536f29e,-0x25ce2c6d004cfeacc0e751bf33c,0x3022b6965cfe14db7f058d9b34,-0x2cde0a9725c1ddf1f2187d074,0x1cb5cd4447980c8895845dfc,-0xb712cd494f280ef7cbf027,0x26b79c5fd243bd07dfba5,-0x3382c68ca52ef205e8d,0xd24ef8ab91167ddf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 19 40 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 40 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 45 indices rho q4 m4 4 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 45 indices rho q4 m4 4 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x48fde0093cd002c0000,-0x63b41fbba9d719cc000,-0x3fec390252bb7227000,-0x1992adc8695eb904d00,-0x72888594a6304bfb00,-0x17d68ef5156440aff0,-0x3d38f03cd8a2f1780,-0x7c1ca34d78f273c8,-0xc9925fc2d8c0b70,-0x108a1e689d18797,-0x11a0aa7ec45b50,-0xf410f5434a3d,-0xaace30de8b8,-0x5fd6fc6e5d,-0x2a7e321c6,-0xe8c1bcb,-0x3b3ebc,-0xa6cc,-0x106]
def m5 : List ℤ := raw_ints% [0x0,-0x10b3a037edcb38741e8758ef1000,0x1b83aae51a45c9cf15bae83826c00,-0x15df2f04f3fe1a3717b7e6e9d02300,0xb2c3005a29d24f57998349a5fb4440,-0x41ee21027eb7b392297284441b545c0,0x12b37d5b39e759eed7ee85e98ad32cd0,-0x43e510b51b724a02ba4b056418650d70,0xca7f5fa106af150b8f793c6a637d04b0,-0x1f9a223e44a61270873022e0557974690,0x42fd5dc7da07fa5ba1f05fc2fcfb97984,-0x79d15cce40fbd0ca93a7a14a045075ccc,0xbf899a35623be9d72456f88d7fb685d6c,-0x105f3eadc3e5111a4fd5d509486025ff64,0x138fdbe0a1d23fc54db975723b1708d6a0,-0x147bf02db29b1804e5ea7cba89bfb962e0,0x12d6195db35bc42e54589ccd4a1885c210,-0xf39eeb326cb78e64861dc645d5d5ca330,0xad21ce30e3a73044dabfdaf7a54e88dd1,-0x6c1584e1fee32c49b9ea35cf6f67e2e03,0x3b2c8248fe74a222cfa0a3ba6d3c887ab,-0x1c55ef1984602edeec36c4cbcd12f8dc9,0xbd30825b8ac1b2b4929be03e26b65ec4,-0x44779a713ad174cde923c0923ecec94c,0x155b4a53eb683f67408a559e055686bc,-0x5b288457848d7cc9ec39c5feddc7114,0x14990000564105a0f87688d639e10b2,-0x3e4f46403def5c48d0f5fa83de4c76,0x9b520559dee074b15b073778091f6,-0x138da1d03f6e3c3439ffd95387f32,0x1f06dbbb56ef03b6c0b1f08b3ce4,-0x257f7d6026afe6d7ba6ea3bbd2c,0x20f509fd7b0c9c88110b96044c,-0x13b7efa489630b3fca99a3544,0x74494a0dceab27aba33ffe1,-0x166ab2086209dc67c2ebf3,0x1aaa0a1112e46443cfeb,-0x5ee7068ef9d3730c9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 19 42 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 42 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 45 indices rho q5 m5 5 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 45 indices rho q5 m5 5 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x106,0x1]
def r6 : List ℤ := raw_ints% [0x4ab3d349743ce2d080000,0x65c15a9a0695546408000,0x41080e38a501ffba1e000,0x19ec31a2198435e8c5e00,0x739e8dd99b7f82329500,0x17f30dc93f3e69e814a0,0x3d2adceef4607f15d10,0x7b31c01d7c460bdd30,0xc68a03cc94c0c4fd8,0x1023c8bf53401c57a,0x1101cc979d247f09,0xe828b0d9b7662e,0x9f8df9a5de503,0x576935c90d0c,0x258009b5ae3,0xc3c842466,0x2e395b55,0x729f96,0x9054]
def m6 : List ℤ := raw_ints% [0x0,0x1a18aa57638d88356fb37af589000,-0x2a7ea853c013511921d4c617bc8c00,0x21610dbbbd71fd07dc344b844688d00,-0x10d7b0039d34b98c2a13fe040e55e7c0,0x62237d53f630920b1d0043e25159b640,-0x1b79e9a15a2f24015739ae2dce0ec28b0,0x626b449ddb17cb30a1db927812a470b10,-0x1217bdc04e264482bdaa84df701f901350,0x2c8857c695a59bd3c52ef58aa98c444570,-0x5d0178468eb816e79f7f7ff54123636d5c,0xa68a33cdbe485d65abc66c61ba55cea9d4,-0x101b36ec77663d078b791b138328987f8b4,0x15aa209d70c4adff03b82ac0933b3389dfc,-0x19712a534415c17fb10eec18da6c8a7d160,0x1a2a76eb23467937aae0d9ca2b60b72cd20,-0x179ce56d6a4cc5f80ef933f20bb29520150,0x12b73f705957852225199bbd98e748ed4f0,-0xd0787da2dccb69ee2e6fa57946fac197a7,0x7f5c3432734499695e76b8d298cf19c2e5,-0x44283b1f252cfe563772c27c3215b5f09d,0x1fdcb99520e243a6c0737d8994e0914fcf,-0xcf63e0661c201b06c71faadc44404331c,0x490d7f58927dc50e7f63b55d1e5090854,-0x1623cb50890c917ff73effc892d3d6ba4,0x5ba1aca3649d442b459c51c05e78370c,-0x1407783620f8572ce8bda602530bc6be,0x3a74ab0c0b42736e59904ef3025b0da,-0x8c2374be63d44f55443cc07215c31a,0x10e75db15f5935181d68db3dc3ab7e,-0x1995d498a81c84707b2e450fa22fc,0x1d5590f0ed9e883bff1874b1a274,-0x184b0424f303b0d6da11f5de5b4,0xd93fdc9a69988d370538c87bc,-0x49fab3d4ca102c48c7919d17,0xcfc46fdc930d9638af8d75,-0xdcc5045dd5b21833c0dd,0x2ace08a71d75b98c4f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 19 44 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 44 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 45 indices rho q6 m6 6 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 45 indices rho q6 m6 6 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x9054,-0x106,0x1]
def r7 : List ℤ := raw_ints% [-0x2926c152b53cf5cce700000,-0x37eb5520afa87c346670000,-0x23a418396946006300c4000,-0xe29ddd38862d927b076400,-0x3ef39cd550a96f3791fe00,-0xcfce442ead7e9c5fe25c0,-0x2104ecf479ded6ac3a160,-0x422627723a327e659490,-0x69f15de32f74c76b590,-0x88c9469090abebeaf4,-0x8edec13853c877746,-0x7897d31de08ebfdb,-0x51c97db9578ef52,-0x2c0f8b1e5e77b5,-0x127e87841b474,-0x5dc2394df85,-0x153da2bf5a,-0x318e1327,-0x38c42a]
def m7 : List ℤ := raw_ints% [0x0,-0x28c68a288b8d24d37e88701fa61000,0x41a74af786a7975f9cad8e65169ac00,-0x32f98ff88aa1efd20ea0889c991bd300,0x196a50abf314745ab64a9816376bd2840,-0x9246af399faff0117a1dd27c724f281c0,0x286f8aea45d1bc4d8624e8546775dbf9d0,-0x8ef2dcc0cc0c883905bc2239944494e470,0x19ec96fce9f237524d609218d19cb8d17b0,-0x3eeae3e1bdf7e05e0b91085d98d23588790,0x818076febf155bec59fccb931f0a6ae71c4,-0xe4699cb2aca671382bd8c819074a211a98c,0x15bef93de46f017530fb7bc5a6c120c3442c,-0x1cc6d48e96d84892a24106e6cebb6214c5a4,0x21396644241ca48a4c67998159ce848c16a0,-0x21917b7b67d8a23561a49620ece6d70fb2e0,0x1dbc79180cb416bfac99800f312e796c9f10,-0x171da4266964c046e09ca3b2b8ae5fcb1a30,0xfc490ef28f6802a492608272fcb1ea19061,-0x96dbda4f50c8a7b1784a383e251834326b3,0x4eedac88e633f763c5963f7faf34af3f4db,-0x2406ca33c62f047a4925f69ef3133d13dd9,0xe4a15fb62ddb92377b16dd3a84d00ee504,-0x4e64b835368fe89c5033e69cbb004c2c0c,0x1715a6942f2f0ed5219611f881ac12a47c,-0x5ca39e2d2bf50011f948a811e03a58854,0x13966448cbc8e3606126cb3dca012d8d2,-0x37252c27ae7efa5581e0f19e2befbad6,0x7f1d93a22e98c4592cd4643e7721456,-0xeafc518d78ffd3fa958304d9ab6352,0x1531d69c0f95b2fbf0f62594675f24,-0x170a2be3a972416579ed946d8abec,0x11f722337e6aaaad071d59313f0c,-0x95f4e90917badc29d79b8d8b84,0x2f215b4f4f94e72dc43bff771,-0x7866da9996b81427fdf5fa3,0x72343478b38e0fca51d1b,-0x134c3f8a1b2c6aa24d9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 19 46 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 46 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 45 indices rho q7 m7 7 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 45 indices rho q7 m7 7 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x38c42a,0x9054,-0x106,0x1]
def r8 : List ℤ := raw_ints% [0x102f775b332193d63b7380000,0x15f2a6739354a33bdd8478000,0xdf4bc7bc88b11927a2ff6000,0x5880a6abb970047dc8946200,0x188302abf78e034a859bca00,0x50a3fd76e75dafb3e3e9f60,0xcc38fec66b5fe817b9b540,0x19750f3364f42c6918b770,0x2890179ed1346f31bf4d0,0x340f1bef16a6521a4bd6,0x35fddec2661fc56f36c,0x2d30ceac4f942c542c,0x1e5680065bb19eae5,0x1023e3b0cab0670a,0x6ab43aac7b690b,0x2121b58bca0c0,0x74e9f11d25b,0x106e32ebe4,0x11dadeb9]
def m8 : List ℤ := raw_ints% [0x0,0x3fb637df5a0c898a75b52f317379000,-0x65777b11c233f981e888d3cdf351cc00,0x4de5bc231ce0588bd8b6b4ca18e62dd00,-0x2663a930a2b6fbb80e41802c36148403c0,0xda4f712bc92220ecb092e8a057815ffa40,-0x3b9ac3fddc5422f8fc5ce2e74b1de2d73b0,0xd00783e8bb67a18780ac9f609259b80fc10,-0x253aaff20c7cc32c0954e3c2ef34eca91050,0x591ed2358393d6d0464f79ceda80e37b7470,-0xb4d5ed7369d7bf3e5eecf604140f47a3531c,0x13a43001a46d0c47398b0cfd6395c5bbe9714,-0x1d762c39ba5dde50247512939bb8a01cef3f4,0x265db01f1d0650fd67140d63dafe455ad2dbc,-0x2b8f5e86f1cb8ce34097ac2096ae4c9ab1160,0x2b3f77fe1a60f83d4bcc3ee49afe590ff7d20,-0x259da58dd6922efc603d952775cd5a4f15e50,0x1caf5e2b068f2f3386cfeaedb74ecce9e2bf0,-0x132d0c5a2f85b1f5c22dbc4bbd106bc76c097,0xb39bf1a61158445294af95ee931a233df4b5,-0x5be2c8c928c358a8625b63f3f52d9f298fed,0x28f4df9c96d5fb500ea750ca149f0c26513f,-0xfd7193c5878236ba4fb15ee35e97342dadc,0x5498e42daca81ed8b670134314a206a6f94,-0x1834a1542d9d2b033259d7ec52368cf9be4,0x5e2f51aa79f487ce66457ebf24089b99cc,-0x1343021438b5942417b6befdfba564bd9e,0x344d88e190f3663b28f9bac7eaec72f7a,-0x73e5e0f420fa63333d6fd2be2b7cb1ba,0xcd26630ca9c494a313cf3ca6b14525e,-0x11a26e2749ca7bc8c972dfe6f0f0ebc,0x122a2c362334628ec6866c4ccd5db4,-0xd53aaf12e5e8886b63defbfc6ef4,0x67bcba082982f18424eb50cad7c,-0x1e10217be49d179d56d8e20907,0x45cb60f6d0b0fc2fd2b00c45,-0x3b0e70746c595e7def382d,0x8b23d09e6cb575bd1bf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 19 48 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 48 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 45 indices rho q8 m8 8 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 45 indices rho q8 m8 8 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r9 : List ℤ := raw_ints% [-0x51743924ca682ba6c347cc0000,-0x6e404c561927434f24d18ec000,-0x45f63e84b0ac7fce6cbcbb7000,-0x1baa5f57d93db159754d0e4500,-0x7a47c1f1c64bab1dbbffe0100,-0x1911deea12e2950dfc8157a70,-0x3f47bb6c5c64ef0bf72a5c20,-0x7dbca36f4e57759bbf8c748,-0xc77bd6cdfff8a1fa143b00,-0xfebfeef33eb2a12ad3edf,-0x106ae5dc4151628ca231a,-0xda5ed2b1775ee8e33c1,-0x916acb78ac4f8c4cb4,-0x4c9d07a338ed3e1e1,-0x1f47d21bd889f0d6,-0x991b390c79cb97,-0x2121d43543af0,-0x48ab309ccb0,-0x4c5b58fcc]
def m9 : List ℤ := raw_ints% [0x0,-0x638cb74cfcb396e857eb19bd446d1000,0x9cddd1323f266155c0ec42e9cc2fcec00,-0x771db925587ba89a39ef64622acd0a8300,0x3a0ad47a674af351abaa8f358af7de34c40,-0x1463c7a05c674a22fa21011e30db94d57dc0,0x58003b731f0474f014319f6856e1f72596d0,-0x12f513b96b5c220b7b749fced3a35b9de2b70,0x35952aca35a0b3512d31da1bdd572c4d1dab0,-0x7e8db206eaed4f0dfed8323272b4f40e05890,0xfd3a6f9ec174c87d6d32a9c106896826aee04,-0x1b1b806f4bea08481b0d3cdbbfe960d5f0c24c,0x280cc4e755b3670df2f66df02664ee4c5d16ec,-0x33567ac23b5de1fce48aa153a5bd6406a16fe4,0x3955d04206fc1abe35f0df92c3ea131dad56a0,-0x37f386d8201ccb04146acd7f6a3bc72e8502e0,0x2fcb14daa8b81e7f116124f06fb4239628ac10,-0x23c2d59ec5cf23e2b82480387c323c9fb92130,0x176f0459416e8680980dc188b458b284688bf1,-0xd6e9e693284845dbc942502ccca9ee8a11a63,0x6b868dda1757ae37df799209bc366865f450b,-0x2ecf1ef8c3bef97008e87df9efde55ce89ee9,0x11a797537d270db2cc408bc8f4572e03b0f44,-0x5bcb16c58f8bb57e765601565bb703c57acc,0x19855e8873d88c8d3c8e95e1f2fb1c529e3c,-0x60480df5560da5ed1bd8475d8ab46441394,0x130b2b11237aef82a121a1a9e6b038682f2,-0x31ddddf1a64c9aa1890e097e9a247b2f36,0x6a329476eea48dc4b58410ce841c59cb6,-0xb3ef56562d11173e431eeb8bc3172972,0xebbdd8070a358e5d405b76be525e564,-0xe5f790cfb4ac78188cd358124546ac,0x9ea1c1f04c19e628869eea5bdc5cc,-0x47e8e91de6fa76c467fa276b25c4,0x1332925f16a5ec526190751b801,-0x2877acf2183bf51fdbc51fe53,0x1e870c39829b2422d274d4b,-0x3eac87a2fd7ed27009e9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 19 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 45 indices rho q9 m9 9 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 45 indices rho q9 m9 9 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r10 : List ℤ := raw_ints% [0x15c56a20b7007cc84590b7100000,0x1d6b98e23455a9dcf4bd905d0000,0x12a2afd0ee5bfcbd76868a728000,0x75ab5606c22deeffbe80644ec00,0x206ec00a21ce8a479d317b2bf00,0x6a1ec3cebebf5ff7105a854240,0x10b1a1e8d94f52d57bc111bf90,0x21104e16a816e1ecdcb934b40,0x34439750429ecac6da3c63f8,0x4276c08e0318181b8789f14,0x4433cec0afcc0893b55261,0x386139eaa75f42e9180a2,0x254c3cdedd50aa0472bf,0x137f5e59264f06a1554,0x7e2e7fc42c842389f,0x2629769c008b2b02,0x82456df51176a9,0x118a2e897f2f4,0x1201490f590]
def m10 : List ℤ := raw_ints% [0x0,0x9b8bde684ad89bcb095f5837baea69000,-0xf2974838423bb94e25d2dc814f0ab30c00,0xb642c0860d7197dbd004925dfc7a1ea2d00,-0x57d6f275a667495c1c4ee173c4611619dfc0,0x1e821a3dd3e72280ab3ccc6534ac6899c7e40,-0x82211f2ab09dea4e8a0be6323c9f56ee36eb0,0x1bb149b7de81082848ef82c7ed47edb439fd10,-0x4d498bd66df0f4edf85eed0d5a449f75455d50,0xb42755791b2df6d69efe85567cecb6eb581370,-0x16394a893c2272820b2934648e424f4ae2e94dc,0x258685a8894887916c6deb1935677ccc84c5854,-0x369fdad333be17ccbf6b6990d26b6fcd9232334,0x44f13a1ef8f62bbf5bf09bfe6cdf63abfb3397c,-0x4bc1d470998312b9f7277e675fce349c2255160,0x48aec08cd72a8f4ad5e93b0adec5b03fe3c2d20,-0x3cfcc87487a635eb6c6854fa40de2deadd7eb50,0x2cc91439d45d1fc39270866cef3bad838b912f0,-0x1cc5d121641f3ab9cd3258b208629dcdeaee887,0x1026cf07d714583760f801761b114a918149385,-0x7e77a11a1d9ba5c3e87f2a1db09cd8d2b9143d,0x35c6dffccec2f4160e5c1ee4ea929b7ab9b9af,-0x13c809d2e7893a49575dd431e1060f4ef7be9c,0x6422df479f164b04bffa2d8e2707a7c718ad4,-0x1b0d7ba69a6a52251fa1cd1bff133e2a05024,0x62f36639affe28c4b459d010b3e4a4d9a88c,-0x12ed3e90eb8dd05abfb62d8b9736ec7b427e,0x2fc905f3d585c117b9a8ef206d1adaaf81a,-0x61c73cf4520b9d446154626e5b10d5aa5a,0x9e864a01b807272f4c33060d1dd23c73e,-0xc5c1262ebf76389a8e084bf41f98767c,0xb695c1abbbaa2bb9c994d86309e0cf4,-0x76554ea47341b7d3b8f7a7d756ac34,0x31f0c86b112a79388d8bb74888f3c,-0xc4565cd7bd4746a6789915123f7,0x17778d4b03b24eaf3135ba4815,-0xfc63a9e55f9f5693516147d,0x1c380a5cfeb2c476ebe2f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 19 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 45 indices rho q10 m10 10 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 45 indices rho q10 m10 10 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r11 : List ℤ := raw_ints% [-0x52237934b72e2c699dd3a34c00000,-0x6ed64f98839c7a03187e634dc0000,-0x4618293b1f14ba46e7e3c68320000,-0x1b9ce67504d09992e1f6e6069d000,-0x7988146be6a8b23228250baf4400,-0x18cc5f15cf42e8f63b48ec10e800,-0x3e430d250d9c719ba1fa97575c0,-0x7af88e5239ebc227f3b70dd8f0,-0xc1c48f37ba0a4f1729f173bc0,-0xf587ce8a12ee5780f25c5cf8,-0xfaebe4ecbbf3f71ba6eafec,-0xce72e10ff7fffcd6b0f26f,-0x87d479252630132c74d5e,-0x468d6683205060f9f5a1,-0x1c525e54b6a0d6028ac,-0x87cff0f3e3bde0581,-0x1ca8a49b5fde6ffe,-0x3ce797f9945807,-0x3d75838ba80c]
def m11 : List ℤ := raw_ints% [0x0,-0xf30a8b82f4f2736d3ea4f9d7140e441000,0x177476ade86d4f35e57ac06780b80b7c2c00,-0x1170d60b4995ecf47e4e22c8f964bd14c3300,0x850ec209a1ceeff8a3764c444358ac351b040,-0x2db44f9b1967829cad81ecb593a60a691a39c0,0xc0b8d175f4936028a0819e6b3f307b1fbd03d0,-0x2886f0f85ba2802f3b27c7635b9e0541df7e270,0x6fb770d772b38ac346acaab14de04a1947e4db0,-0x10113d85cb0281d5852ea534dea928a6410fb990,0x1f4a828a5b2139895921c55e9d708dc9767f2e44,-0x341a5264e3f5c9a1aa5ab98be2d691dfd161670c,0x4abef665adf6f3ffeb14f297759366644d1495ac,-0x5ce9008345191ea48a4b8f71584e3f83d46a3e24,0x6479ffde52c1b934ee2643c168990a476d6296a0,-0x5ecc0d20ff37744cfba462c5b2ac4d01def352e0,0x4e27ab47eb87e6915da8847bfc1b888f2028e910,-0x38566f6292e66df7c840da4fea1303684043b830,0x237e2d7c3418b2962b7dcad17d498028f35d1081,-0x1383fe07053edcee7aafdab0771df78dbb47b913,0x957cc5b5d053b2668312ac364da27f3643ea83b,-0x3e18f0b38bbfb763c331fdd168124d406c2c0f9,0x16478ff8324590752d35f4cac1f8a00d0e51d84,-0x6dcf8b4dadab4b0a64ed918a1f14662b39758c,0x1cd3b49126814ab1b2477c974bdf67b96833fc,-0x6639481d2ba3c176234c88ef6d2e047cb52d4,0x12e810e445d38bfef75ca61570f4021732f12,-0x2e041ab32a66db1db5c6b01bfe74f9ed0996,0x5a721b310ac9029827878797ed1b70b8b16,-0x8c430ec4fb6fda44b9d568d73ae0c9f192,0xa685fed9f271e2243db4d70c2b7c70fa4,-0x916f46995e6e160e2cc83183de524d6c,0x587eb28d90c772cb12cab9a4e18588c,-0x22be14caa4636f26caf2c39f9f4404,0x7d9b371b31c63fc63f2ac381d191,-0xd9c12b0d6602bbf202f4817803,0x825d842e2d86b593a8c2907b,-0xcb34b7fbaf54111c5eff9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 19 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 45 indices rho q11 m11 11 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 45 indices rho q11 m11 11 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r12 : List ℤ := raw_ints% [0x1185ffeb531dc1c8087119ce2100000,0x179d8ca49402d65aeaddb123c990000,0xee9cb14c3a806797d52557ca414000,0x5dd986cf4f0044ec78232224199c00,0x19c54cac7fe6fb651db9c008ddf400,0x53f894b1c81f66dbe807d721e7b40,0xd25e5c8778377aac3320b8103200,0x19e79af423f817e9a1b907c223a0,0x28b4df65ec75572bc0365c94e50,0x336bc4f502d7f9b52bd9e3b014,0x345d84e8491e044ff9efc5048,0x2ae955603d048df407e97110,0x1c1a5c46f0710e74b6cac11,0xe84f56b20d066c272222a,0x5cad0538b951930adcdf,0x1b926f38bbcb817cfac,0x5c46b4ed213c208bf,0xc206e6f76e77ea6,0xc13f43c433639]
def m12 : List ℤ := raw_ints% [0x0,0x17bc079fc9ebad45ab1e1c6600f564a59000,-0x244b82605a1b02f01c3d89f0091f91f204c00,0x1ab8186acb015f4db41dbfcd2d74d2914e7d00,-0xc9bc8c8a8007f55191855495dfdf283b337bc0,0x448d74a4ef029a62722856c30ba44231f534240,-0x11dda2daf297fb60e48748063865e9ed7f9919b0,0x3b6ac3a1a20b5ff79d05e340c8bfc97a0e630e10,-0xa1d23bd7a1ab6801e92a3a0440955e4b9ca1fa50,0x16fb8687466ee372dbb7f26baff0c810ee7c92270,-0x2c2ccc6efa413a102f5a796cb8f4f18230f92f29c,0x488e2d3fb59c1a0d690671a3068bb251cea0d2d94,-0x669b6e3bc94a27a34a5a086ab66fe6f57343fc674,0x7da4e5527bfd524d74efbdbacf460b712713a813c,-0x85c1b0a80e90baaf31133496360e2c33d91109160,0x7c20e42dbb95cf8d53adf291b90c36ff65156dd20,-0x6492b799a3229fca427bd3b2602a91206c578a850,0x472e26128d284d37ad8c18d2c549c0e3a232889f0,-0x2bfb9c5f304bc63bba15eac9666f04f708a9dff77,0x17b12c5c9db098c00865eb2e11fedb0b71d906f55,-0xb18fba0b68d7ca3c053c17a041f1fcee5ad4cd8d,0x481071e8983607c6717dd7be2bb3f8d803f7f91f,-0x19388841ac88db371c7005b685416fd3c15a9e5c,0x7909b179c746a96788f46f926384aedc6b59a14,-0x1ee00fdd2a70237a7b1c725f46fe2824377c864,0x6a2419748bda0c2a325a0add5295570d7d234c,-0x12fade811dd93cd4215ddf3fec3d09ed38355e,0x2c861017c16c2ede51a54237a4171a975aaba,-0x540a0dc5ede7117842cf97ed1117b5e54cfa,0x7c9d9120ff85792dfcca35dbaf4cceaea1e,-0x8cbc90360898b63205ef0832588b301a3c,0x743297d97b7965ef22e2acc6b16d8f034,-0x4256149c2b19dfc13a5944ab5ecfdd74,0x18350fcd5d0e2db0afcb480cba3ecfc,-0x506a815eb320a3e02d87e866ddde7,0x7e4a608ea3086f58cb45c1610e5,-0x434f7dedd90845911dbf0a5cd,0x5b6b7bff53b8d564c2c19f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 19 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 45 indices rho q12 m12 12 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 45 indices rho q12 m12 12 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r13 : List ℤ := raw_ints% [-0x37196fb37bc7b21eb5ef823251cc0000,-0x4a2b0fa623422c76f35f2a6eba56c000,-0x2ec70a3e4f4dace398c1648e1db1f000,-0x125f4a308c728323ab5b4e8a401de500,-0x5097a2327e6935ff17db2c554c34700,-0x1062511897eb04d4a7842133a75d870,-0x28f7850ab48c3450b5cd4167d2c040,-0x508a5d3bbe56554ab1e892f98a688,-0x7e418f9f1fd08addfbe1024e56d0,-0x9f0e954d259d7536adebc9079df,-0xa17bf6f1468c162ebf628006dc,-0x83df950671ca398d72e2f0465,-0x5606559bc1cac1d463e83fd0,-0x2c3e74f2d63230dcb2db5b5,-0x118eeb4b93c7fa4511c5b6,-0x53127ddcea229c2b2ec3,-0x1140829a0618b30f404,-0x23f769e87baa2accc,-0x237439818e8e50a]
def m13 : List ℤ := raw_ints% [0x0,-0x2515cbe9ab803ebcdb5f0c5f617f6d42b1000,0x382e491f7b32875904a4c37c8641540a276c00,-0x28f53844a66076ba6bba38e39c913302490e300,0x13223310941555880220bce558657b5be52c5440,-0x66f1e6888e0f47fa9e25e41269dc4bc810bcb5c0,0x1a89d0e130daad7e83367c5787e15579053ff40d0,-0x57440510f5ca6dac8e76d925eafce8366e0690970,0xeae10dc2634ee6f613432444b5e9fd39a899570b0,-0x20f35f0e3830c298098da2248a9f524795bff7aa90,0x3e86d68175848103a7906d5ba34503c9f2601f7284,-0x6553df6efbea556c63dd64f4e61fb4035b410457cc,0x8d4be90fa78d89fe871b189d10540f8f27913c806c,-0xaa7d14940a5b7a124959b6b05dd45c4c719ed97064,0xb2b5731c3bfb860342db109351db92c66a4d69d6a0,-0xa32a72b972dfb91f3a8bffbf3bcb05af7bfc04a2e0,0x81f3c37f356022cdb08a9a195e0b6218449adc5610,-0x5a51feac2eb1dd821d1c75c7d06d92e98b8627df30,0x36bf910b94c2ea4522c37d5fe339ee22fc7847ae11,-0x1ce56e780ec38bf7d0edcd3f0cf4d4928fcb61b2c3,0xd3eb339c3d04726f417fe5327e4f2e90de4694e6b,-0x540a7689041f2198b25c54c3b5007801e047db409,0x1cb14f9219637dcf2a46b41eeee88f0fad7a34fc4,-0x861514ae79bb18b9126be4ac1018caf914fadc4c,0x213c14deb2914e0fa7ba79f5779228768e8925bc,-0x6ec0e5b0e49fe918ddce87ab91b0b73fe9a8614,0x13254273f7eace9e264730b528f45bc76acfd32,-0x2b4763364aa04928825b31359bc9c5dc77a9f6,0x4e6cecc7731d141938881efadf208f3aa3f76,-0x6f273321b0e113e8616ce8b7bafcd133dbb2,0x775b58415c88c7f88b6615e3e4e1f7f1de4,-0x5d1b2e07947d912b3754a652dda304802c,0x31d5bb2a724974f602062e18d8411b74c,-0x10e40060d1741bc4341ed42e45b22644,0x33846473a14ca0c6eb64c14f09d421,-0x493e3a9410b6f7f554e3bf877cb3,0x22bd7fbbb6140b8083439a16ab,-0x291ce2fc3176d77c4b1e709]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 19 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 45 indices rho q13 m13 13 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 45 indices rho q13 m13 13 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r14 : List ℤ := raw_ints% [0xa1bd9103ef557e7cdf8286f095db80000,0xd97caeae61fb3983ca87c46a356138000,0x8902621728caabeb33a0e15cdbb31a000,0x35be2ed80c129cd2c8b07b302f2d21200,0xeb6b5372d9d8ee0cefc6158b1260e900,0x2fc907cecb4dc23a8f21345c64a54860,0x7746f544cf7f9900a5ad97197669290,0xea0cade1b43b4641f16b541c33c790,0x16e1e0dee6b0f145bd360aad1b14d8,0x1cc22e5960e6ba75562c3dd62fcb6,0x1d1e97d09390a011a0371cf10681,0x17b560a72239429788f96fa36f6,0xf69c391223e65d9fe33268a5b,0x7e5849bb77829a7d020fcdcc,0x31eaf64a2e8e047a9aa2f0b,0xeaf6df951eee994d86b3e,0x3081712a217f17968d1d,0x646a76b7ee4a85bdda,0x6229a615d9ed4f14]
def m14 : List ℤ := raw_ints% [0x0,0x39f20e9d1bf8620716c4835508571ab8349000,-0x56fcc65e961b6f9ddc085b62c5c6134fdd98c00,0x3ed239a1849f732f6e3b8f49372434127bdfcd00,-0x1d0f90de9389038df938180d07e5734a6ffacd7c0,0x9ac578370fe87b732924b410f9138267a67084640,-0x277a5bd676bafba1fe22b05ea5c09999c2888974b0,0x80639a294766bfac2234ebdf6f056765b6a73d2f10,-0x1559b708187dbf854ca9dec66d34e3671a92c0be750,0x2f59b95903274dd5333a71d363665c28fea89eda170,-0x58baa65e5abe20c9b44369a4521505d9e8a36ba2c5c,0x8de8f12f0a34bbb6d90e418cf83cc91cb62b4ba56d4,-0xc32ccb27f9753c8b3194f4e9019e112e57cc1441db4,0xe81c6da1e5c0bbfb5d6adf2b4aa17fb2019041ec4fc,-0xef9f7189274c6e18f6b07dc98cbe7aca45857a6d160,0xd74c009bf6d1b9875c3da162d5d9ee4b7e2196d8d20,-0xa896d293feb4934dd91e8a63dec111ae73423e69550,0x73175378b45bb46fda5bc4948ffbcce64398d1590f0,-0x4472f30af371f84c43124e0d54bd2a51d887266f567,0x236786458613c5dfa6c2874c035c550e3955f315825,-0xfe1cea683c5b7fc4014fa566931209343b3e320bdd,0x627a9ca20d4d1eaf9f6661cc766bf37b8645f47f8f,-0x20cd2f8b42831c6bcbfc41b8675748f6d525f73a1c,0x9542f41a2c0bd0baaa5679e25beef59c94a09dd54,-0x23f30d4899088751305676809196b6eef6daa44a4,0x741f9bbbec0c7405394c8fedc51a5024cc74ca0c,-0x13672f948f8807fb2b0bc62f555a9442ce0a763e,0x2a41d9437cb976196258097fdcebbd5768de75a,-0x497e3c2364be63581eef1f0d4e72af4f92399a,0x63859f93fbea32a16f2fcf8ca12a726f89afe,-0x658f6fc0b7d5dd50251498f0d142c433b9fc,0x4ace78a30312f492b4357a6235ca54f4774,-0x2583af5467b4bfc366537e3f0af9a742b4,0xbccf26d4988755005e6213d9555686bc,-0x2105882a9c927d66a62d7d564ee26d7,0x2a79a8e0416fd3d718abd710036b5,-0x11ec4ab3c9ffced635a5d243c1d,0x127b6bdf8757727916f74c0f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 19 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 45 indices rho q14 m14 14 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 45 indices rho q14 m14 14 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r15 : List ℤ := raw_ints% [-0x1bfd0fc744fe990b18aab3243cd97700000,-0x25996f1d375d9bcef9bcd848830a1c70000,-0x17a95771f86bb317ab2dc670a1c492d4000,-0x9454d39c1c39817a5e13f168767cd76400,-0x288f026118fd2ef9c7430fe7faa4928a00,-0x838983a6e2e930a9730a35dc60a27e5c0,-0x147d3150fd89641fb7c3c4b5b30c90da0,-0x2822b84aaca53321094755c68bf26510,-0x3eaa0901f18ab637695c242ba815f30,-0x4e9726ff7986fa48606fdb77305534,-0x4f63c8a16dedf096aefc54e50340a,-0x40779b425eb0d4eb769091ff5e23,-0x29c9590048340daf68e5958468a,-0x1556279ace0d4d26ee10365edd,-0x865d326f1467e2c89d725bb4,-0x275b2193192a95fc2c4acdd,-0x8156f7d74b6736c38fc82,-0x10a3186890becf0ac59f,-0x1026fe82047f4829e6]
def m15 : List ℤ := raw_ints% [0x0,-0x5a8a36d57bb4192b13930d34dd0819bfd221000,0x86b9a41fe2f5989acef76db2a3057e2cca3eac00,-0x6068fb03835ce4f91ea4f9b6c0917aa5518889300,0x2c2d25123cf7e85a073bf646af0780912e31d73840,-0xe8f4380b3fb3abe74b7e7cc1ba84a6eebd9278f1c0,0x3acf5f43866cee4744ee851a0c919a60c1230194dd0,-0xbd3658683f897a3aeffa9bc36b4b8a4d1eb42a8a070,0x1f1d010650a4b68a47e9092551a386b4035b274a43b0,-0x44322dddad04364de5e4b38e5a08137e4bd43bb92b90,0x7e3a73c17c1e512fc50f7ac5f3c3fa8732bb1903fac4,-0xc74c1983e7decc5822a60d029bc6349843334526548c,0x10e6a3f22026cbe5469a592df9cfbc339b84f4d73972c,-0x13d0ad16d29f32f27111083ef461efaed6ddf1a9d46a4,0x1426dca10d069b5d635cd94ffa1c617b8d34c093116a0,-0x11d25639d86ed88336b6d6707daf8c1dc807b7c52f2e0,0xdb93e824faacaa1809a6965f7186b6b14c3cc191f310,-0x934384872e90ceb47bad3ab944145c3cf06076c29630,0x55f2cd8c8796135417d58e7a1d5b37f12242aaa9f4a1,-0x2b929e908df232033c85ca31f874b5e4aebbf0d4b773,0x1321cf06bca0dfe7d71f45270d6284ef6abff539679b,-0x73f0e6b21d326c2143e77b46660e473f93c8ac88819,0x25ad8864e846c00d57031f36c6cf4955b729c47e604,-0xa6f4e1710c2fe732c1a68c03b9a3a150b0aad06f0c,0x2712549a61efa2ad2437b2b48c5c48cbd50eaf337c,-0x7a535d855843588eb5cce381dc8fe9c09487ced54,0x13c0ec176c2a6458cc0c7016b5466158060a20d52,-0x29704b230f53fc80bea772397c18b22ebadb7056,0x45262193237ccdc6ea3da179867c0c5c37619d6,-0x596ebdecd2be8890ff6c6b6dba8dc9b85f07d2,0x56b08bbbfdc4f8c5c5d19b283a5bd4dbe5024,-0x3c41e8f198e5e00a78354a95e94be1749eec,0x1c4b03c38d6ce5592a1cf8ca40fb20ea20c,-0x84104a51dcb7482909b7ffc183a080c84,0x152d0f88407ef35003f9dfb671d44fb1,-0x18a13e0acf1457b19944e87f20bc63,0x93e3ccfca04530fa9f781ec0fdb,-0x84e3770c2ce52e12f112ff19]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 19 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 45 indices rho q15 m15 15 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 45 indices rho q15 m15 15 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r16 : List ℤ := raw_ints% [0x49afc40cba938194fa3e299e7f9533880000,0x62e74c803e85bb6db1d26572542e96248000,0x3e2e6be55f15bb6c900e998034a9eb19a000,0x18566b765b93deef22228ca9ee181eccee00,0x6a5a5a72237dce3887a9a39f578aa9f1e00,0x1587b7925d56bd0f3558bdb9f855538f7a0,0x35958d16609203086f367d8fecc2eab740,0x68cdec377f6f7d2b8bdeb1230e9425610,0xa35ae9754b77bbf9107dd450212e1090,0xcc7ccf7c54e1e7e98f4420d12e1fbda,0xce22e09f35edebde20611572f7d36c,0xa6ffff8953c77f94275ad04faa7d4,0x6bf6df3180c0c3bf3950120db51d,0x36f748c2f2299225265375d167a,0x158feb3a9d9a5d086d07966e63,0x64abc1bdc02efd504e565638,0x1496c5c8472c1541aa55443,0x2a2a11a0d8b90146d0070,0x28b35d1d49856a6fb81]
def m16 : List ℤ := raw_ints% [0x0,0x8d77f5ad914967534e95c4a2995ca83bb8539000,-0xd0b815b3f73fd5c01e2229c393b89525fc01ecc00,0x940a64da7bfe5c57253580c252909efa705dee1d00,-0x4335cc9e64c3d762db2ad6cdbdb5150e9951321f3c0,0x15f0557314d88e1851ae0f6ca1a2c3e5d2c3537f8a40,-0x57bb0aef906612d5b447a6c09126f21c68f2259f7fb0,0x1175052dcc5d2111524e2eb72791b649acd0b81196010,-0x2d6d9639055487445e08166b386f349b833f7e2202450,0x626f50c83e0e9d23551567e395d6df7f9de9650549070,-0xb404b48f9ebdff643c5d4ba93752a11cf1ae1226a021c,0x118a758ef5b727b994e62f1f92247fc96ab1fa5aa11414,-0x177c6398f379a952e7a2b9a5054ba1b30816d89f8368f4,0x1b27186d15d635b5d21a6c2124c34d82d3a5474f37c4bc,-0x1b358cb751218d0d1354e9f51aefc21e2a71dd55521160,0x17b0b120434747c6182eac50c4f5da4593b12c8bee3d20,-0x11f18e31a1f25201cde2b6a0310bed72039c9f46f4b250,0xbd3281b250bea3d8f89d9d68ca910fc8671e8d36927f0,-0x6c6143a549bdda50ffc2cf0913e9e0b9df956c8abba57,0x35dc86af20e8d40790df970824450bfe59f2869241df5,-0x1726bf6a712d0a717e70249b04b161f5b1c0c650b1f2d,0x892130f3d88b0dd92e0fb1cf4628e76016377689bcff,-0x2b7b45df511f290b549a980c1374c17671e5463d51dc,0xbba03cfec43a4ec6f70b33aaec005951ac1c16d9494,-0x2aa9b81b6521dc5c8294dad86bbb967cc10656804e4,0x8172e311762739e56e955104e05c29a8dd2e235ccc,-0x14330f311beb5a23e99bf48a8fd20f07ccaef6e51e,0x28ce7b04b044cd1f3b8c424453e6478f3567c4dfa,-0x41508f7a1fd97959bbd2d50e6cffb50d1ac5103a,0x50a584173d2b4a64d86c894672332e148d1b9de,-0x4a37c9477712c91c3c22bb0c9aafa9400515bc,0x30a79f01dd6092db9ec04a4d4a81a1f1e52b4,-0x1560201b2f8a50403244a46cffd9be081bf4,0x5c7804f6797fb6e10b542a44bf88bc1c7c,-0xd95bb44544c4f8082bbad79215ceeec7,0xe47b2e97420c004e3ea013347a8985,-0x4c3d1b4b814c4b355449c003276d,0x3bb2514a35bf9b77e20eacd7f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 19 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 45 indices rho q16 m16 16 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 45 indices rho q16 m16 16 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r17 : List ℤ := raw_ints% [-0xb9acf11ac1231246146f8ae515e003a2c0000,-0xf9050674d97e1f7ce4185d0873c4a3cb4c000,-0x9c6cb07da22970bf0112bf5b3155c1605f000,-0x3d2a798245109c85f5b33145f8c48321c2d00,-0x10b02d45ee11428f11ea7f35aca9778958d00,-0x35fdfad7aa7f714bea3434b37726fc19d9f0,-0x8634f2506ddf9fad451868f31f7b58c5fe0,-0x106215dd7e40132334fa3b2f3fe05e62188,-0x197f3add2bc9b8403922040c509761bfe0,-0x1fdd06e38ab3506b95ebd78eec1c83197,-0x200f794fba79b190eab669a351a8fa96,-0x19eb78f7703b5e4d56551ed5510c029,-0x10b7e46c9b5c54d992af0f0266200c,-0x87d528c21045c56cf34a213af7d9,-0x35215bf05b25be9bc2a77fc2066,-0xf73f1b56bea1bed587425894f,-0x3260df1cd7d290912cffb2f8,-0x66bb9bb9f552f4f773d820,-0x62aecf1ee956d1dda8c0]
def m17 : List ℤ := raw_ints% [0x0,-0xdd0b6fdf3302b1722aca033e0fa0c6dd500291000,0x14370a9cc6943e0f18734b6cc4650690b59c301ec00,-0xe371d7a5281c286ede997d12c2bcda75fef81e34300,0x665665fc8bc8916844b10dc99a0e7c32ad89a3f65c40,-0x21180c649bd3ee2f465b8fe0a7aa4edbb572d9acaedc0,0x830d1e281b90814a07582ffc6c24ce162b407e3082ad0,-0x19cfe0da082bb791732feabaaa9045e1b827428f9da770,0x42745e589ae0f56d6794ecc2455eaa8502e2e4d97fc6b0,-0x8e63732bb5a91f67f40eb3fea15afa1b42445afd053c90,0x10159c6d499b718799d12ea1f14bdeab811e5ee98290704,-0x18c46d878675452edd431ca66dfb1386e930dbdd3a01d4c,0x20bb51fbf0502d30f526ee02a350d1d2338ba981cc499ec,-0x25532b95279a196d8aa3b52aba7a823d9fa8038b3c800e4,0x24dcd094f79e9b54c4d33b9ace8fbefef5075bca2f656a0,-0x1f9ad50afb97ed37366298a1957306d6ca47318ed6842e0,0x178cf1addb85e242072030991d179a77fc813d11d78c010,-0xf40b242851a95bcc71d91f1e6d7a82108555310490dd30,0x893c4837715be5bcb7a47c93e3e1a6604d8ba687ce7431,-0x42ddedba9bf610e1f1965ff442a8dde0c35a2895f17723,0x1c23aa6fedabdcf276c7e7ebbd5f5c45ac2581c7bc23cb,-0xa2ecb9b39a95bb10d185b8fbc480401a1ca5392f34d29,0x3268b33e069e1ef15447a904c2a47892af4ca2da12044,-0xd3d27f23d2b9dbf249a6d23ed111bd67f87dc5f4edcc,0x2ecbeac38938768b2d762201008c1a7752e46c181d3c,-0x8998f370e282975c7317bea7ec6444e738a20a9c894,0x14be80957afb41bdd9b243144e52dce3335613a7f72,-0x2858f2107f1198b71207dbf8b67677029623a6bcb6,0x3dec99678573168741d0a8a20c02c54a78fb17a36,-0x48f773a827d449f3ba1cd25955076038ed2f95f2,0x3fb894c59ea8123932c1dee081706857cd0e664,-0x275ff57a0842b54345df9ed5b1bfb156cf69ac,0x102cd8e246cb032a43ce25b6c0ae55187d8cc,-0x40ce36265e1fd8b0262d7bba81af46136c4,0x8b7bc3253387f616494f85569a5ccd441,-0x8472fe0b4a331450a7095c73f5ce713,0x27495a06908384c2f6efff141ac0b,-0x1acecadde71a0cf8b60ab14829]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 19 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 45 indices rho q17 m17 17 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 45 indices rho q17 m17 17 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r18 : List ℤ := raw_ints% [0x1c23075fe7fe81b8d3bc9eef15273d901000000,0x25b55c4cfd75dc750864f5afa0677b599640000,0x17ab0f12e871bbcbc2924a338bb2ad8669f4000,0x93f303909f04edd782f904fb50461ac1bbd000,0x2853d0ffc6be5b43adf29dc53c0b9092981300,0x8256703fc5b217ed7d7ed0efff558fd93e700,0x1439ba85885c986109867f08467865823c610,0x2774673fc4a1079aa0f8adb92898b3c47620,0x3d51975de268705ce1f45ba133e4f89d278,0x4c83738945bf0c71b8f2188f0fcce41560,0x4cdba4d6357f2f0cd5ad39a9bba542269,0x3e05adb229d2ed727dd073400f8b5d2a,0x27ec1931f09503e5fbe1eb6b92427d7,0x1439e0d6b311471225de9419d14874,0x7e41fc00ec56c993374a95c53027,0x249dd61c00dd1c05c30adb5351a,0x76fcec3f5691c1689c69adab1,0xf1c08a038a0a7f63ef3af48,0xe73fa3abfc4243fc48be0]
def m18 : List ℤ := raw_ints% [0x0,0x15961deccbfb4354262dba510f86b36b9cd04029000,-0x1f559952436e243e967715def351da421bc40b300c00,0x15d9fddbca01a3e74576d9687b91e5a4d7a8560c96d00,-0x9bf2d4ed4194299ce7f4ed711eb74a2613b88c4eecfc0,0x31f967c1b6bb4edc29d98a90af9db4f4be51a735bd0e40,-0xc40609a46baa2dcc5af7bf25ed8001d8f7556a45763ab0,0x2639f64f778f8df4db54aa222ba235af828fa0dcf58a110,-0x6164c54e4513c7ee113406d6d88e803c64a386980cbb150,0xce67738b30144940066a4a4451de1f0fd0bb82bc2fcef70,-0x170c672a9f42ef073c787254cfe46351c2fc4d28cc0433dc,0x230ffe112d77793aa0c4d1cf1060c08294b05b0cfaa2a554,-0x2dbf7d1992830ba074cd62b3791c51bfdb40b0956b04e834,0x337781c411eb064d112e846c06ffadc8e81376734959407c,-0x321b5badc69ae4b33ff08dfc200fb6bfbc3f30232eec5160,0x2a50188172a4af81a096d59d70e715a51c8b8ce55a96ed20,-0x1f067845552643368700febaa14b27c756fa2ece6a35ff50,0x13c0678b219a25a7659dbb53c5e444c470dace81b2cc4ef0,-0xae7c2327abf83547bc655dfaba1e0b832a48b57dc7d3e47,0x535d4864651ed4f8a36efcc5244d544266b3275b25290c5,-0x2259cecc0b1856435e8ae00131277120dfbfd08dc2f577d,0xc26e57acc956ca0b42ff9455ca2f2a3329e9625b89216f,-0x3ab3c7bff723806819e1a27cb2da3a583d957db900a59c,0xf03680c8a5fe58062ff9c23de6bedfa36aa6af48bffd4,-0x338f11362f6e94f01392ea40a31fed572721b18bd4924,0x92e4f6b056e4f9c491cffff4c24b4d363da4e1df9b8c,-0x156479af435d37a68a5c314bd70256ec89488d3861fe,0x280ce492b4303bda2e4426c56159768dad8098b7e9a,-0x3aebe98032c8b48f720b06f9ae6f01c67a650870da,0x423a9c165d8507a35e48f78e0bbf2f7f7a5d126be,-0x36db2a9558b2bf5e12bfb76f9652f41d43c9ed7c,0x1feea5460d48bb1150104c80f71d3b901af51f4,-0xc4212ed6a34d0317e5178207ed7153c89a934,0x2d74acbd92dd36a7f92515225e2aa1146e3c,-0x598813f9f43b7b5c7c40a768d7a58425b7,0x4cc40bf7016b0e1b76549242f61bd955,-0x143ca75fafaa6dc9916f449bdcb7bd,0xc08d1ddb7779bcc4e2fa2ab5ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 19 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 45 indices rho q18 m18 18 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 45 indices rho q18 m18 18 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r19 : List ℤ := raw_ints% [-0x41ef3a4d274cfeef38790e06e2f098280a800000,-0x584e213ed2b4c9c09796def955cfe1dd84680000,-0x3762b5acaa75c594629e39af4e6a3ae8178e0000,-0x159f0550ffb2fd288250db29034db0ab05732000,-0x5e367922d6b514cbd808314f2430079ee08d000,-0x13034af9f906bf0952c73c4c2d62f2909492f00,-0x2f2831ea6c6c527e6288e238b0a95dfb632900,-0x5be2f73b2d45d0d3a742a88c1f597b46e00f0,-0x8ea0c90e3e77b1e7ad66fd1ab4331a410be0,-0xb1ba48b15f65b7a46cae90266c899e34ca8,-0xb24246f45d399d12dd71b10e3c71c35ca0,-0x8f9c54fc334a5e061ae3075aca24516f7,-0x5c44d8f604fc52d6bfadeac35efc26d6,-0x2ea6c81669353060c4fce19d55e6169,-0x1228d727c16d6ab2bf3bb8c1ec5b8c,-0x540cf8f405810d9a6ecb78611199,-0x11059f159520fe0d910fcc4e4e6,-0x2279243b5476ac3b385040cef,-0x20db0858b1843157a726ab8]
def m19 : List ℤ := raw_ints% [0x0,-0x21ba8ec1feb899337ba7731ea8427858250564401000,0x309524ac7d15dd8c4b7e7a33dcdde5074b62517b12c00,-0x219b76cd7c1a09e63349c74efe47cd03967e0d6850f300,0xedd47a00c3fb9bd39c0dbde46bf81407ece7dda66dc040,-0x4b8b1274cc99ec55a007535acaaa143ca6e5c00bfeea9c0,0x12596d7560c10881094b022ad0ea6944d00d5ac87398d7d0,-0x38b32a0d19ac74063a9cabf7e9b979042df554b0449f1e70,0x8eff0ceabe2b788c816de22b4fbbe09b79f483e08dc8f9b0,-0x12bd1ea60fc38b1d43bc9c011374d33173acce272f61cdd90,0x211ab8f738f099c3fe9ec0f1e6e5b041d020664580e0ed744,-0x31c3bcbfe480c6d81f88aed5fdc53058ad2b3cdc8bb16720c,0x401eb8464730aef3863489bfa9d6aed7e63ec5a0b38e648ac,-0x472ecb6e44a9bd82db71aaedeee88a9f1f53a3279ff8fdf24,0x445501181c54da105a526bfc19bbf39ad1a66a0bce0c796a0,-0x38d88b439439681685612ab582410ed2f46a708d2c93e92e0,0x2905c756bd6b43e7d3158b899da9bfbd5a6e6415b7a1fbd10,-0x19ad1139c610dd9699bc8b53f7a16931b846da83f72afb430,0xdebc8c6b238a8634ce5fd86dcb6be8e7015440dbcdd8bcc1,-0x685d47d1550ea7930b2bb34324e9001f9090c9c7d4a3a1d3,0x2a1ccf3f3bfa4eeecb9f37cc2a66eb3a73626d7f8961b2fb,-0xe90a289b787958fde6c8d1a644ffd41c6b9779eee7f1339,0x44a90c2bd2d85bb111f57e74b88a3c1520dd80932b93e84,-0x1119b00df648a9ce0ff0970f09af05b9994334cbdd7188c,0x390d6ae448926d3e13cf60267a58b15552d3edb405a2fc,-0x9d7ba48bd05bd4194880bffa7e30e0b523eca350457d4,0x1626887b1be5a7909355a82c6f2b2062aad5892787392,-0x27e81b6b3a2a550bfc358b76fdc52772bf89fa95ef16,0x3842500817b3804080ef3f090018fc9ebd04d6cc096,-0x3c4c04a79a52140e156566eff21fda2e9e5c83a612,0x2f584ff4e8fc0ed1d9a560127e1c38ff14f1f20a4,-0x19f29325d26d8014eed58992eca28b5fce95a06c,0x94d5c6eae094b8f70f80aafe58924ff14a1b8c,-0x1fe82dca24eef2f0ae997ff9c360f0699e504,0x397ab106bcab611709ce206f52ed96ff1d1,-0x2c7bb95746e641ac79efaffd7014eacc3,0xa6b98c329e78fc15a55279849f1b3b,-0x56693a43bf9429e30147c4dd239]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 19 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 45 indices rho q19 m19 19 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 45 indices rho q19 m19 19 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r20 : List ℤ := raw_ints% [0x95e2f9108638c3d3f77aaab01d898290257a00000,0xc89e31479a9ad17779f5555833f9fc55a05aa0000,0x7dbea2957d080c22d19b3d092d51016183eb88000,0x310d4537c8924497c12dc3dc77fd39057420b5800,0xd591ee3bd7b1e1c7ada337b23234453aed174800,0x2b100b8c23f94c06a276ba9fc11fb9bfa22f0480,0x6ab4b0c7d19bc95598158c785ed0f753f4ab500,0xcfb41d6a0a176a0a083d34393bee85440a56c0,0x1420934efd580a936ba34d31300709423b6390,0x190c9b615738453f87fc18ecb6767140bca28,0x191700c2fb0c27859bb155391ccc8c4a73d8,0x142eccbac74f033080b785a0af362515478,0xcf2252093b8d04bbcbf1ae57f41e5d209,0x6889459f2bdd6e21186297c96bf7adfa,0x289bf689a8e5c64061c859d09564f97,0xbb88d1578c48269f01f8bf2fb1864,0x25e24846bbd4ae5080ff6feaa8e7,0x4c81ba55eb4aebd0d01f233442,0x48af5adfe564e5cde2daad91]
def m20 : List ℤ := raw_ints% [0x0,0x34b37f0f1e006f607135a3dfe6e7dc09b9d86ca419000,-0x4b5820f77108d18af68c3afc4a1fb5db65c99f504d4c00,0x33b6afdf95ae49ba51bebe39d9f772bd83170ef2ac1bd00,-0x16afad4a1fa5e7d59ed3485a4143437ac1804d9ce02f6bc0,0x724f82e99402fea5df59d2e57a438f1ab6647edab104d240,-0x1b84659af6de2e67410da707bd3c7f0dda80cab1d4458a5b0,0x543aabc640e4cf97d588f67047420d928a35b158d536bf210,-0xd2532cc354c3f44f2cdc0516343c2944786ea29f78e4b8e50,0x1b465f6562f43105ced6302d3e3316e91c91ba9619f655be70,-0x2fa7e8626138ff799311708663fd751142d08045e11746819c,0x46cf33a08af2d61df2fcb522e57bd8d203949a632fea744a94,-0x5a1e1c0f87edd2f9467747de571f1de676b5c605f2bcc3db74,0x62bed137e4c84f1f0eaf72797244f6d712555c95d0b212f83c,-0x5d7c1cd94e866c15990312114a7103d6f1c20581c0bd3f9160,0x4ca1929eb6f1e5f122cb438a398ea54da4f60e3c5297f59d20,-0x366fe3242a265e446edfe130cc55995e6fb66aa334fe7d7c50,0x2181045972d6741ac0196db437c4f7099347ce5b8d5a2805f0,-0x11d742c6d1bb28f51a96133283d605f5904d6baeca0dcb7137,0x833018908a3bcd6371d6434784cb40ba501da9c13bbb38095,-0x33d82e6a6c765514e1c2e0f610edd2078505ccc6231d304cd,0x11881c045eadf63df6e765e89c53f7a3670da2cce7aab1cdf,-0x50a7433c5571f91dacd5a95a9f3b46d50f1b0e7eb838f55c,0x138fab4e87c7e56947dc889828fcf12ad352ff59b4fc5f14,-0x3f661e91849a83a144d7c0701cc7cbaa3fa753851d25164,0xa987d4887d177def4429ddb3701416faceb7a2d0b4464c,-0x170693fe4e25ccedbe334c54826d6b636293bfcf9fccde,0x27e8e1c81f0459161d075d3029927fa5349aa68e8193a,-0x35e567bf040eca764cc7c14a6edcbeaf6568d6a8fb7a,0x370e679628bca46367d9152be8b4299e5e58887c19e,-0x28f5fb127e74dc07855c7cd3b46af7c7171eac013c,0x151f990386ac4dcbfb9ece3ddce1484d01a778534,-0x7115ce5b116bdbe3141e95118ce2aed59ef2a74,0x16693d5f50dde5972028d45d1874bf03033bfc,-0x24e81d2d47443ffbbc0a82d62d8109e8bba7,0x19c557d403a8eae16f47b87b137cdff625,-0x55d11dee29bfa63cf9a987ea04d3d0d,0x26c42623367b76f61f40df63755f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 19 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 45 indices rho q20 m20 20 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 45 indices rho q20 m20 20 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r21 : List ℤ := raw_ints% [-0x14b96677d6bc587e8fcedd386fc782a3db2d4ec0000,-0x1bb91179eeee6af65423ef572f1bebdd0ed6fe8c000,-0x115d9b034c58a62f91510eaa7f961cddd5e5a877000,-0x6c5069682edc411b7a51afd5c539da1ade440c1d00,-0x1d740539cd55eea52e53fcc4d315d123b72f9cd300,-0x5ef1a68b33b23f1fada26e96c160b0e3a44d18ef0,-0xeb0f28024310fcfd702dc1c5df33e466785ecb00,-0x1c91c6838c74665a40655f309108097109870048,-0x2c3ffbb56402495745a493b0d6b5d73b1c77e30,-0x37023a24d29e851770fc95d8eb25b57ed11707,-0x37079542287787cf15871307104b38f57f348,-0x2c34f28ac70999d511a929219ed73faedb0d,-0x1c50316b77a3b6942c24f6b9f84594cb168,-0xe43fcfbc0401daa2267c98a6c7d45e64d,-0x5881be5ca965d2c9f14aa4926b8bb6e6,-0x197e727abc0adeec46478beb9d8f73b,-0x52374ee70f9a4ca814269723463cc,-0xa59ee34a72355dc2f531491f7ac,-0x9ce8193f51ce513ad448ae7ee]
def m21 : List ℤ := raw_ints% [0x0,-0x525876879ee0ae06b0e3d00dd8ca47cf326229c0671000,0x74e0570184ffc278c21d063b15590c26cf0b08ed78c6c00,-0x4f9d42c2e97329b52b648bf0f3c6307d7a400cbab681a300,0x22a65a8e8b4381ba0af1fdc4c8eaf35024363d01138616440,-0xad24f25f350464be87cb61183ff49368bc647b7f29de025c0,0x29511b7acac822b1098d27d36c6be508e28b5aabcafd6854d0,-0x7d4fbaa09f1304f3291be899b7cb8f67dfe35d712280740570,0x135e49be211a9fbc8a98127afe6d9be27372fb12e2a3e68dcb0,-0x27c745b053cfe561d69126f0c29a90f40cb717aa04fbbd10e90,0x44c1b58bdb659733bcea679dcc2bae88e1e264ebefc42f9ab84,-0x65009fc13b4d81dbc928a2cdbccfb6749f8c32231525bba12cc,0x7eff8d441c79af363fe8a37e4ab57e2ebacb8adcd0edafb636c,-0x8961acf790c1ee19555e8dd4402270f28436408ce125c8f2164,0x804c6b94c7a463a7270d2cc237acc5250af891cd8bcd102d6a0,-0x67a6206cda3d468e71a13f70a66af1e7b3d86273aa1bdbfe2e0,0x487e807881e729e568665d26bada0eb559484ba31ba3ff5ea10,-0x2be18deaa60ec0562c5186e292a0d98c8be8f3542f6885c1b30,0x16f3fbc472ac1df82309b845af09bb9831c2cc57ab61fd55e51,-0xa5910e97f95311a81d424a17e4a35d12d9862fdb3afba1e783,0x401681b473406898acff01ecfecef5b30314fc4feca7ad452b,-0x1530e321ee613b692f1234d590ebbb1790857bd7ea56adea49,0x5f240aa0378a653adab3fbfcfaf67cbbd9443ecff8b1680c4,-0x16786467b8e19112b76741b5a7af81391c1a95442b4d9af4c,0x46be31e3580a2936a458dcf7dae540a6aeb1f7d9207d84bc,-0xb73b751421c36c969d73a25621e36cfdfcbaaf8f15bdb14,0x1806e25cd3163856b998af4cd2cefd03daa4bb8041809b2,-0x280df6655f5a562e77cd7ae01084e743dd014329736776,0x33cc4ae9ab91723e5df0a4c7a1dea6cb6ace092664cf6,-0x32692d1a1fe7870379a74ceaa7af559a695304d35832,0x2384b32c6568e655f3a88b6cb30e207d1aeb3ed3ee4,-0x1139cb1ead09739dfc31903dc94e31ce1cfadc032c,0x56050694f5cc592ca65263ca5ed28aacd1b62a4c,-0xfc00fa670ed4b19a54c3870f455a1d336a5744,0x17b30cd6ea9104d66534fcdf34e2e195b3861,-0xeed2ec6e90bd90917e3f46c41a30bbbd73,0x2c27cb425325f1028b9c3b88d3b38d6b,-0x1162d6c9615139d46c0ac21b2ad49]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 19 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 45 indices rho q21 m21 21 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 45 indices rho q21 m21 21 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x9ce8193f51ce513ad448ae7ee,0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r22 : List ℤ := raw_ints% [0x2cbce1cb821c0ebc1310d285f28d6c312b75dce80000,0x3bd09200e06eb483669e1bc87df5997bf3b0bc0e8000,0x2572560756b6d0ce86f8f583ff23499abe47452b6000,0xe96b7a90f4d07f15a70b5affe069b46e2cf5d1b2600,0x3f6e01d4ca4c2a46bf7ffd085b44fdbe3d880143d00,0xcc51b9523b052358361ab59dcc5cdbf26cfaa84e20,0x1f97199fcbf5e640dac416297d30eb53ad5c2aca10,0x3d6107348e64fa97d79b88a542ba8188d0debeef0,0x5efa2c5f207aee9a822eddd66b81f0848de804d8,0x75f29998fb76f331b63967d7808d75af8a95c12,0x75dbf9ac1ad9f6d73c07e0c2b4bc41a88da519,0x5e9007d669fee5ce60a31c2cfd3890ac00f3e,0x3c7b90b7a54a5115f14011502e9cf7783733,0x1e6dbfc35b3292fc977210eb7affe413f4c,0xbc7a15658e2fff56b4765f0668c625df3,0x36310746f8277998f003a18504dddc96,0xae69cb3f1898c4fbf2aaba35edb365,0x15e90b92208c70e9c927a0813623e,0x14b4bab0beefa2b2e6e506172f4]
def m22 : List ℤ := raw_ints% [0x0,0x80aa3933e83f0fea7463f515a2bc1033beb9613ca109000,-0xb5587d30b662987420a038d5a3a662fca3813df30cb68c00,0x7aa087bb166132a9699ac273a7447360c54f5b9d12f270d00,-0x34f5f423140d63459cfcff0e67180159d73d55d8df07bfc7c0,0x106835167e968431d0fffb030f4fb16b61ccbb03e94fedad640,-0x3e1cb95780c27a8202cbe10f3419131330f1e7686812741c0b0,0xbab407c1f83e84bebe2952e0ef1a5ce9209b08653232dd45310,-0x1c95fc500e10ebb688f2210f31208818f4c9fe852a1e122cbb50,0x3a206cfe6689432277dcf4b0bc3ec0b7a917af5fa87afa3dfd70,-0x636abfa0649fba8a7203d4380b3b6320210bfe030b17620aab5c,0x906b18e33ab03440b879a8555849684548980da509909ddf43d4,-0xb3724d277f8b313ad16116911e0bf2553f40c1471ba169ef82b4,0xbfaf1c2f18a20a7c5a74698435dd1d4a33a7a1b55a74e570abfc,-0xb09ed5da3c1f509b66c9a3deb4ce55b243af8a5dd4b32c85d160,0x8ca75add50719cfe084fb7f48ef15bd754fe551af4b9e9e84d20,-0x60e07e2580746bf378a263e11cdc90abad338dd9b39cf35e2950,0x39aea8b795c3b5bdfcebfd54a984f02fa8d68999da3d3b254cf0,-0x1da47f66a255674a7fdb063872812c008eca70f26e9062d54327,0xd1c6f91055f084ee8dda5a5e6d0d237a5a502657decf39abd65,-0x4f8aea6080d629da5ce1a079908327c902f98230f39dc5f771d,0x19b81bbc6f34f1143936d3bb3de10dc2a8c33c4ad2e2d7f1f4f,-0x70b1b9ae4ed1e7abe6be92439a8c0c743dabdb33774fc2011c,0x19eb0b93c497da73998fc76a598bd1bca90c151cd52a81f254,-0x4f41b55f8a5d71ffd140b5e42313cda48eba3805e4a2b5da4,0xc6d0b06f618c605858b5c9efe1e2a3a3a482e659e9201d0c,-0x192a209d0863822ff07bae8ae71e76a1f122f345b1f405be,0x28567fb50296f912bb6647089142ea61b1448b6b6c0bdda,-0x31ef55c19ad85d319c657651f10e60355953e4fad5501a,0x2e4798eb25ca3c545b8903d86f1880b9f4c5f0a1c6a7e,-0x1edd7ef66b15d0ab79d704d5639e71ed36c04e1910fc,0xe11da9362f7da86ec3ce6b4074e1bce03437b82c74,-0x417fd3b0ce8cd54df8542aee7ed03ed144de7dfb4,0xb13145e90717c61468e6d9b858c3fe046d045bc,-0xf381a101e224d24d0fa6338a385fb142ea097,0x8a4ad14d7f1152e6796d9d4838e2bf7aff5,-0x16b608ae901d1601b3e8cd254028e075d,0x7cb87d323ccaed96c475109d07bcf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 19 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 45 indices rho q22 m22 22 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 45 indices rho q22 m22 22 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x14b4bab0beefa2b2e6e506172f4,-0x9ce8193f51ce513ad448ae7ee,0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r23 : List ℤ := raw_ints% [-0x5e75d3d19007eb08de48f43400de5e600fa23c1f00000,-0x7e3b8f4e2f74bb2f57df15c6b2ee7b5da5796f9ff0000,-0x4efc49806b86c30f86115714941086c2c389396a44000,-0x1ec11060bfca9c099fcf73442babbb1c6bb40afa80400,-0x85a1a793ce22fbac31ea012f4ef7d30cb2529c161600,-0x1ae29682e5c7bfa4b7783d48325406b127cd85dc53c0,-0x42759b9fcd4f8e5660dbfc111716c2a61339a3117e0,-0x81069cd62153edeb2cbf06c9bfcf19b3d5178eb490,-0xc77acf2c9c8095a1b293ecf10f7353663282539d0,-0xf77d60f4826bd1e36ade9748ad142fe8f474ac54,-0xf70c8b1f59698a8c6ce5de49130b61025d3c6ae,-0xc5fe17e8b7fcc38d79cf7543f27623ed1370eb,-0x7e7b11a03713710ff2c34ed0a83f78766f242,-0x3f8bd3122ba9716541cac3eb0eafd38b4b45,-0x189062559141a5b600ed8c998fa27338e34,-0x70d1aa6f6675ae485522249cc228a6fb5,-0x16a72eeec783f7f4081966147832252a,-0x2d70ecc473bf4959fe5427655e4ef7,-0x2ad921fc230204aa90856ba51f82]
def m23 : List ℤ := raw_ints% [0x0,-0xc909f9611ae288de55dc2ef1ce45d950da01a7eebb9e1000,0x1197133799ed683189cf6a773cb24daaabf79f0cbc3dd3ac00,-0xbcf77cf3c9a1310367e642dfdd0a36287a58363fd8ea255300,0x510165356752d70dd8fc1708bbb72ad934d1a89d923d1354840,-0x18e62be42e7e035309591172d31d9ef4918162f89ee6125b61c0,0x5d7c21f882ac023a54f27cd21370a62c03a2d5b913515de3a1d0,-0x1169177dc18ced3b735b1000db94546c730a65ec7246d7a535c70,0x2a42aae801992a0928a0d4289551cdc525a84114ad373f5526fb0,-0x5519930acd3d0a20be5133a47a0695504cb1c38f1623df682cf90,0x900e927ffb9fc5bfde6d1fdeacbcf47cb252b4e81b9130131c3c4,-0xcefc74d3121a52a24918bddf5f2e33f176cb6c4a2aa95d207bf8c,0xfe36b74e584258acf32258b1d1c4a8dded3656dca7bcf8a52aa2c,-0x10c344d314243876e4cd9c74e7e70c3028104c78eb217ef10407a4,0xf3e105a3065f324192b47df0f1bf48c15c499151fa56b70d616a0,-0xbf7c9bfec964d9f157753820bc5489164bdcfa8153071184632e0,0x81e739e1690f5d01ad119fafc3924b434d35959d2034322ca4710,-0x4c18a630e4374dc56cf9bc84f71c75447ab28e2710fb9d8731230,0x266cc406dcccf33c6d1d99438a916e9d4cd3766baba3d46c9e8e1,-0x10ad225a86d897bfb2d0c69b09602363689d5d20ab6ee5a9df833,0x631d945a2ebec0dfda6ebc22a3e34e15df38ed0a9274bae50a5b,-0x1f57365d546d475bb0ac96b0ee5cf02814c9e894fc3f0912e259,0x8606d6f2fc2e2c5907a3267bff294f383b3715e4966c8fb2704,-0x1e03ed4da7e0c5a2d5791192905ad3407e7a4be6ba84713720c,0x5925306782911d4f65d8e9de7fc8fbcbf4f3593c7c1c09827c,-0xd88b47843c83730b80dcc0c0b141a36ec27a19568a8ab9254,0x1a736c3187a1d8e06c6c5e0e7f46b188dd71671164b2f61d2,-0x28c202725e62ef0fab8654fe95d16307ff9b7e43a4f785d6,0x3047f3b60a633173e7d08c1a1f2fde874b3c64c89ea7f56,-0x2a981fcb9272e10f9d0a7b13e5f8a2212871035dd0cc52,0x1ae0417019b14d68b1fce03376fdc2767834c281b8124,-0xb824f2d8ead6e31e8140e72832fe87de068d68b51ec,0x31ebbd1f93eecbf9049d79f354bb029513bb00c50c,-0x7ca49874f3932c9f8aacf641a0f4552ee326cd84,0x9c5ff835695e6454a394833518b03616dd37f1,-0x500edac96893bcc7ee444ef5d64ff4ccc923,0xbad56d4a381688e791ef962fb6d09329b,-0x37e6de10efaf80ea0516b9c2c2e959]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 19 78 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 78 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 45 indices rho q23 m23 23 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 45 indices rho q23 m23 23 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x2ad921fc230204aa90856ba51f82,0x14b4bab0beefa2b2e6e506172f4,-0x9ce8193f51ce513ad448ae7ee,0x48af5adfe564e5cde2daad91,-0x20db0858b1843157a726ab8,0xe73fa3abfc4243fc48be0,-0x62aecf1ee956d1dda8c0,0x28b35d1d49856a6fb81,-0x1026fe82047f4829e6,0x6229a615d9ed4f14,-0x237439818e8e50a,0xc13f43c433639,-0x3d75838ba80c,0x1201490f590,-0x4c5b58fcc,0x11dadeb9,-0x38c42a,0x9054,-0x106,0x1]
def r24 : List ℤ := raw_ints% [0xc378fa50993afa61e8c22b1afef7e89740617b6a580000,0x1051a84c496910d55d336db1ad7f039dfd358d9aae98000,0xa34bd83cefaa4a49f1ee1e2348eaef2c7571cb610de000,0x3f8c4f3c8087d1e954d22b00b670bf237a6c4522f5da00,0x113f79d1f98d5ad19c65992cb71f1297052aded1527200,0x377c9d5f2584846dd59a0bd94ccc866dc6898d7c151e0,0x8911b66142579fc34ff09d482e26f84f9efaff661b40,0x109e9dd113e648376daafc05b11d1fb93fd78b163db0,0x19ac91be280ae2b9d71972e7eefd8044dc4cfddef50,0x1fd3573dcd9d2df501d8f5c9384e008713bda335fe,0x1fbd21f810a4467010a1782202db1403b6fe9f88c,0x1969025f8cce8117aa0694df87f73eaba6acb2fc,0x1036d27636e4b342584e7486a3d8db665a50ed5,0x822e14b630e3c03fb9a431388ce60bb02d2aa,0x3240f15a1ab9cca04c8f7c33b83f3b6d927b,0xe677704ede8e9b0da148bab78da32a8a30,0x2e3347cbc92a682ef7d5b2c0fe051baab,0x5c82709ce2b67eab48cd449fd059d1c,0x570eb96f5d31c308d4a486eb71b69]
def m24 : List ℤ := raw_ints% [0x0,0x13a1f95a7ba01f5db66280959d24d238e54a296650526f9000,-0x1b4e3483a4af9dc2b343bdb9de692e5aacb2e883e6209abcc00,0x12354140f9ee227cf56d368a07a9667bb13db63f9bd2fe495d00,-0x7bfc7809356ee698788f349363db0bcb669b7de81dc4d23be3c0,0x25d244f6150b80cdcce6c937a4728f96f15744215d9ebb3031a40,-0x8cdddcd5a90b1b913b9ff99af24ca9a41e21387adb76b46dc8bb0,0x1a03686f8658ff54cb2acf3d824ddb8de41b9bccc8ece9cf22c410,-0x3e93fdfc5cac7d00299800a72e25869d561167fe64a764524c3850,0x7cd262eee63db35804eec0937b397008b4854fcfa6812aa904ac70,-0xd12d942e5d74722c5a6453e713a236f9a70daa4f5b5e707006711c,0x12959945b7c037eb71f62c3d0bf8502c42dc20f86bd93f43600d114,-0x1690ce35c817e386fad0c73cc5417e823ca1394f9571ecd432b1df4,0x1784f19e98344c11e612e95959d5c81c014c65db04f22ba87ba1bbc,-0x151c06c3abf8dfc6367784e6676a77ab285a99537e2e8c03be91160,0x10584a7d57746098e4a88b9d0b2a628f7eefcfd6b61e8a2e81cfd20,-0xaec5fd4ae5c3959492728e5d08e775505239243b0584a27cab0650,0x64be1d5c352ddc65a9b7b7efe28c82922d6a5ccda3b2070ead23f0,-0x31fdfbdb8092f3256a13edfbc64b018382546dd90afb245098a417,0x154aa33f4ac3fca1f3344b4b576478d6b4e18020684c016e091735,-0x7bfc3b873c7d3e1528becdb998a60f08c85cdc9c4a53aee42fe6d,0x26577ae1f3cc22abbe3fc885fc5363fb7087872e56ad87c5b98bf,-0xa00797c1e38207eabad1892fb0e4143057dc27839dd0861b88dc,0x22e5a57a9c4800235e17fc1c2b02e3cd1a32a22e2e762d4bf994,-0x64a75b66ec7dc3dbf044713eb14f156700f173fda8eabe8ade4,0xecba2c669f51d7fcb4717ce77568a7a9dc25981ef47cd5dfcc,-0x1be65e6ba079efb40e180e5e260188c2bcc6e726837e51ec9e,0x29505a3c900630e841f2f89107cb10589dae705241c660c7a,-0x2ed0756fe4206dbcfe9d026c07116c10df586979ddbe0eba,0x274bdcf70812c626ce203807ded394b4b4c15517bac015e,-0x17726cd26eb42b3fba8c48e9ae4b67b52c498ab002dcbc,0x96d645764fe53890525f03e9352dbecd4ec7873e87b4,-0x26146c293e81d957b0f1746312ecd640c261fcf08f4,0x57b5a96e4c65e330d2697a432eca3a126b4a74b7c,-0x646b1a144c633c393a37b3e778bfec6adcec487,0x2e556242bc85a9ec4fe67b6417d913498d6c5,-0x60074778cac713fdf3adec1cb61fc566ad,0x190c815a3311a74130a10557dac393f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 19 80 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 80 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 45 indices rho q24 m24 24 37836498433536811008000 25=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 45 indices rho q24 m24 24 37836498433536811008000 25 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_24
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<25) : intPolyRF (mz e)=rfPoly (C (37836498433536811008000:ℚ))*rfX^25*(1-rfX)^19*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V7C26
