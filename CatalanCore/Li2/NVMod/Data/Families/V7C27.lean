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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C27
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,27,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x769c8c0f02d204780000,0xa694919187ca8a178000,0x6e1b1e9f810e0b1c2000,0x2d8d1df5d065a3ca4200,0xd3b086d9f76d347cb00,0x2de530a78d25eddd960,0x7b531557f56d0912f0,0x106e7799abd39c83d0,0x1c3aa7eea1d234728,0x27799766356cd8e6,0x2d2f337749ae907,0x2a6a6370808492,0x209a009b49ed5,0x1468bab536dc,0xa4e4a272b6,0x4223ca8f4,0x1494f792,0x4ca23e,0xc8c3,0x14a,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x9,-0x5,0x37,-0x63,0x3e9,-0x743,0x146c7,-0x31eca,0x5a2d01,-0xd6a22,0x10d0971,-0xdedeec,0x47a315,-0x460b8c,0x242f7713,-0x1207b4b,0xfa6b067,-0x904903]
def rhoDenominators : List ℤ := raw_ints% [0x11d707100,0x3c17ac,0x2f7b0,0x6b4,0x270,0x41,0x3c,0xf,0x80,0x51,0x32a,0x37,0x294,0x1ad,0x8f,0xc3,0xc300,0x1144,0x45ed0,0x198cc]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 27
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤26))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤26 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 27 omega7=padCoefficients 27 (omegaCoefficients 26 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 26 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 27 omega8=padCoefficients 27 (omegaCoefficients 26 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 26 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 27 omega9=padCoefficients 27 (omegaCoefficients 26 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 26 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 27 omega10=padCoefficients 27 (omegaCoefficients 26 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 26 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 27 omega11=padCoefficients 27 (omegaCoefficients 26 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 26 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 27 omega12=padCoefficients 27 (omegaCoefficients 26 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 26 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 27 omega13=padCoefficients 27 (omegaCoefficients 26 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 26 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 27 omega14=padCoefficients 27 (omegaCoefficients 26 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 26 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 27 omega15=padCoefficients 27 (omegaCoefficients 26 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 26 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 27 omega16=padCoefficients 27 (omegaCoefficients 26 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 26 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 27 omega17=padCoefficients 27 (omegaCoefficients 26 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 26 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 27 omega18=padCoefficients 27 (omegaCoefficients 26 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 26 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 27 omega19=padCoefficients 27 (omegaCoefficients 26 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 26 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 27 omega20=padCoefficients 27 (omegaCoefficients 26 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 26 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 27 omega21=padCoefficients 27 (omegaCoefficients 26 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 26 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 27 omega22=padCoefficients 27 (omegaCoefficients 26 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 26 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 27 omega23=padCoefficients 27 (omegaCoefficients 26 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 26 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 27 omega24=padCoefficients 27 (omegaCoefficients 26 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 26 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 27 omega25=padCoefficients 27 (omegaCoefficients 26 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 26 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 27 omega26=padCoefficients 27 (omegaCoefficients 26 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 26 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 26 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 27 at hb
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
def m0 : List ℤ := raw_ints% [0x0,-0x4bc4a13c6f088e9e64c84000,0x8d9325e3b70b04ce7edee2000,-0x801baaf46339110c0648883400,0x4ac6ec6de17df5fd576f4b5ed00,-0x1fa4424eebf517378ae0c5c8c0c0,0xa577bdda8bb79150038d347de200,-0x2b762544c3d938d1e472c00931c70,0x96c8e2487c0606b3e65b0a48254c0,-0x1b8448c51695332462e32a33f5f6e0,0x44977a797b1fcc2fb398c58f2017c0,-0x93902b187a77228fddcdf414fe94ac,0x11447ab15e6448788f0ce2431933db0,-0x1c51b31cd57f557a97793b4a93f7948,0x28e2f3d175afd667e4351a734f3b330,-0x342a2b7eae3c0c4ee0cc905a906d5bc,0x3af9e554b2f94909830d4a2adbad040,-0x3b328552bc0e225cd9f36086b33c5d0,0x34cfe124c04c5054bb801f9dbe44d80,-0x29e437596bad6a11d5380b95a0f806f,0x1d88ccdb062b0203bba97084a29b22c,-0x127cc9f44f4412dfb3387c66bd68632,0xa419e109270858347f52673f3d9b8c,-0x5079e2b92916d4e4861a1b21044fa3,0x22c449eac7c5811fe88a927e1dd770,-0xd2c3adf8bcef2f5578b8503d331f8,0x45a5b80f8c2bd5d982d8505d419b0,-0x13ef10ff33ff424d14362e58b7cda,0x4e62a5bf81f779a0dc61932553d8,-0x105da3b0ef87f3560286ad9d2154,0x2dd2eda5ca8244955c738f085d8,-0x69b853f709ac73bd1e65336a8a,0xc4931c61cd4498087ca09ebb0,-0x11e12530c2090f66836a0bfc8,0x13904d464d7d12aced500d30,-0xf326e74420cfe6b1382a0b,0x7ae0842a79b4141d5e72c,-0x22f07e4197a1a0615602,0x43c4696cac980e9d4c,-0x1c24c9f1c0293da7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 20 37 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 37 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 47 indices rho q0 m0 0 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 47 indices rho q0 m0 0 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x7b1f8602346de7c163c568000,-0xe30e56a4379220835e82b41000,0xcab7a67284ef043f3aa2a1ed400,-0x74b66a755db983611fbcc5282f00,0x30b2790033c869c26266c559deb40,-0xfb04dbabfd2db4461211e56eba200,0x40f781ffbb2a4d9d6d98f3b57e6a10,-0xde02c8d0995aa8c7c284f6d851de40,0x27e4003233674aa0604d70e3e2f0aa0,-0x61dcf6e0e584874896cbb0978eec340,0xcf1c8a1864f683dedea270febeb1674,-0x17d485be0239a0564ee5e5f66fa067d0,0x266897dd162b75c4a1f797abe9ed9ff8,-0x3677d778ee84695e64f69ade9b92a650,0x4437daba52724b87a01fa468eee7cee4,-0x4ba9f5ac24c7f61de499d8593b354700,0x4a75379db391714084554656c4a89150,-0x41137467e4eab4485ada900f443ee7c0,0x3287b1fa433007a1e2e69a93ac1e5379,-0x22d7ca3aeee79f4415c5118d7b80ab34,0x154fccc44b802fcf26eb44a643dc7c1e,-0xb8a7799c9fb9f0653a5934b619b7ad4,0x584b0ce0f71222fe553422baece3565,-0x2524ddc153450930164c2077ab5ca90,0xdaf721431295e55947f24d2dc75d08,-0x464028e68c780f3b431c7de92dd650,0x137c7a63c341343617d97915182896,-0x4a1c2baf50a02f91c3b5b1ec7c5e8,0xeee1c78c0811e02f189c7eaa214c,-0x283a045029c104027cefe1e53be8,0x590412301b54a58e8c22fa545e6,-0x9e23c1ca2f9318ecc44120b310,0xdad7821c960dffc672fe60f18,-0xe25b3dbd7bd77be989848d90,0xa4f3d3c117158c0aaa05f7d,-0x4d69fbe13bb5bae6725534,0x1428cc41dc38bc643f94e,-0x231a46068a78e33e214,0xcb92f94891bbdbc1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 20 38 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 38 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 47 indices rho q1 m1 1 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 47 indices rho q1 m1 1 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0xc81339c39532989a4220c90000,0x16c4615f7425fcd6e6f1eb41f000,-0x140ff2819549ed018273e4245b400,0xb659e62b86f8d0dfe510810620100,-0x4b0c2257c2e65ec257c9fae6a3fcc0,0x17d71e4bd54cae7348e69eba1a60600,-0x614f2ad11997824e882db52ccf00370,0x147a62adda83a216c5811b73189539c0,-0x39fbbbff763b82277aaa79371df770e0,0x8c0b35d98a7e2392d07acc474346f0c0,-0x123a6cf594d614e9d705cf2076a6c676c,0x21018a22ade64cb376dafaf0e919cf7b0,-0x344c03a5413cfb6831ee3532fb79419c8,0x48de0e3d1b83fae676677b64b67eec930,-0x599d3edf8744c4eded6ebf3ab9ad36b7c,0x6189d648bd8f5a6e9b4462ba85acd7d80,-0x5e2049a673b8bd793ae946ea950f945d0,0x509d34ecee01caa2238d837f891ca1bc0,-0x3d49ef8bac042e86d23d33058527d35df,0x2957ec6572849d2c828da847291bb25ac,-0x18b6f50c03ba36ca74c38fde375b7a152,0xd110d0bba3b3b25dad8a9d3c4cc2120c,-0x617be125e798ec54851c6daa4f16b453,0x27f0d6f03ec298faf4237a1251adc3f0,-0xe4fb234e8f1bd4ca94a91f2ff766f78,0x475445a74b1b5e3430b7546a88cb830,-0x132cdf22879f7cf080913c78f12677a,0x4687d27ed833bb978e3aceff62e1d8,-0xdb576815934b4610a59b541f6ee94,0x23891d4e972f340faf889074829d8,-0x4b66eeda867a1d65357defa58e2a,0x7fef14940d731e02d65b392caf0,-0xa842ae7867e19535d2ab0c0748,0xa46663ca73eed604e41727570,-0x70497b468f7f89749c97173b,0x30e2538c78fb1d1d485b9ac,-0xba4ad1b08db1bb8bbb222,0x122df89f9ea78ae0cacc,-0x5bfbf825ff8e0f897]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 20 39 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 39 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 47 indices rho q2 m2 2 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 47 indices rho q2 m2 2 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x1451f3dddd27237faab7546a0000,-0x2489cfe072e785842743a00f23000,0x1fca10b9d31711a4728a7900a09400,-0x11d30bf0ff0d52e184778c9188ca700,0x73cf650fb2db07195afa7cbad641f40,-0x2449a0f49a0dd16b1bdad036e1a69200,0x920adcb839fce480206fe0ab39f40b10,-0x1e4ab755111f4f834d420090b3ec9bc40,0x5480f4c0c22639eb2c05c649e729db4a0,-0xc8feb5d5d9765f8265fc05ae6dbb31b40,0x19c093f34ecb9a2f29456814dc17de9db4,-0x2de0b02441be2efba7ffac72c638c156d0,0x477b58df5db194ed4b8c26137a0cf69f78,-0x61e2da3a437df137e995bacb2d90225350,0x763e0c6f7123371e9a3e67a5c7da75c324,-0x7e53fef470144407344a190fb515c8af80,0x77949a0436227d2212c1d10fd7cafd7250,-0x64620422c498d465ce32362b3927b284c0,0x4abe50875de8f51f6549c8bfb268013e89,-0x3155b93e99855f8211e2b32ddcfe090ef4,0x1cd448b39a9092a41067833bffeb39ecfe,-0xee22d86ede06d665156058b325215cc14,0x6c4c84d4c6d2c620094bc4c3940bf3135,-0x2b3848c22be6a6a993f7ada1902053e90,0xf0fdcdccb3bc1e224e5b890daa193988,-0x48e4893e60a75d8ea1a487fff9f90550,0x12fdcadbe69a40aa8282bd99b122e8f6,-0x438e04279bc5dc39b3703378140ab68,0xcaaaf6281d23c637db9305f928f00c,-0x1f9544c4e4fd3e9ea8f04cc9cb9e68,0x403db15c8a5b51bb63ab39f6cd146,-0x680e4111dfc0360e5f45996d1690,0x81ff0803d4c99d5f6348f6ab098,-0x77e4cc576759e646e0cb1cbf90,0x4cae86cc65e492ce13e3cbccd,-0x1eeeedb9047155ad975b86f4,0x6bb010c10bd081d4949d2e,-0x969c0459cbad27181b54,0x298a9b201c32d6cf51]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 20 40 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 40 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 47 indices rho q3 m3 3 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 47 indices rho q3 m3 3 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x21052c48875f99af7569e92c40000,0x3aa8a75f1159859b96c54edad43000,-0x3267885d59299ed098f9d18c3627400,0x1be77d09029549c85ce2805cd3fae100,-0xb2f2ca0493b63be854b14fa4ed0c68c0,0x375300e71596eec4ecb250392add9c600,-0xdb9c4f6c3a1bef727a5984ab05d659a70,0x2ce921ba33be22102153d54e427fe1b9c0,-0x7b79028ff214e7533a090722426d75e6e0,0x1214f366e3edb3c01d23b5971b4715e74c0,-0x247f978d32d1aaab9225d22c28764d1762c,0x3ffdfdb286b40f800e152540379eabc06b0,-0x62132f97c8be874e7f5f299bc9b2f604648,0x8407e0d672a651d187b7c96d8777617fc30,-0x9cb1e0e4da69a55acb724a8cb9923081d3c,0xa45ef14a5160d906889cacb09cdfd0b6a80,-0x98a89d045a44e6c58cd4e2f8ae0fc9090d0,0x7da392df531e2f8a03ad5a044c7cc4d0dc0,-0x5ba389605b57281971bb9401bc69c0ff64f,0x3b32b3a9403d76efa6eb84381d15d5a0b6c,-0x21d277bc9ea3bc39ec96f7bede1406e7372,0x110dacfced7584ba1a87e9e6d9e042104cc,-0x790b2a1cf4cc9e0d8a87fe95d156d45403,0x2f0eabbfd89363c6c46209255a993188f0,-0xff3882acdb03459dde945bd575c685ef8,0x4af5d54df79eed76d6c981cbbcdb27f30,-0x12ed809198bfbc4a7d412f620d44d741a,0x411baf19f5a964f75dd55e1172053958,-0xbc67da4d3cc6a2eb37ece1931522dd4,0x1c3c5d3ac3e7779b693696b12013b58,-0x3709c63f002226570625211b9c4bca,0x55127624a9009f0dcf156b3572af0,-0x64e5af63d6054c03ddfbfbc315c8,0x57c6d505cd837b65a8aa070fa70,-0x3485edf586a0f34ba57e74bb6b,0x139c9099174f297ed2b27fb6c,-0x3e4b8782b1bf57c1e6ca942,0x4df688730a0174d2cd18c,-0x12c05adc56f8523b287]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 20 41 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 41 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 47 indices rho q4 m4 4 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 47 indices rho q4 m4 4 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x35a867f5dbfb59bd1ecc1ae7e80000,-0x5e33abaf238d80de64e336f3157b000,0x4ff8dd60ce48c6f4be70be611de55400,-0x2bba140bac26b6dd28e910a5ddd9a3700,0x114dddb9e533d776e60650451c9a35f340,-0x547bc5e29ec38cc4d0f4b31fb2e7adf200,0x14adfe77915c99d8b818148f0eb57729c10,-0x42bbc90d3005bcf26eeec2558c7fdbca840,0xb4df1db98690c3d186f2321b088c13536a0,-0x1a19d53f76df7860a5222d0761d98b909f40,0x33e4416ae270d6db5b71aa237d5bc869f0f4,-0x5990e67e4553aab49fb265fb6823ad0babd0,0x8710100b35faec83a982b8cc9a776e57f6f8,-0xb2cc7ed2d3355b07d5c766225d23fc1ae850,0xd08a2058954c4f0e186d62af2ce10c5b7b64,-0xd6d6f2af060d212821ee03593b414a2e7180,0xc3d1ac709f03071d26c84fa98a781f5fe150,-0x9e09eb045cbc48e5b61e4b94e016a2657cc0,0x70f13646d4b55df0cd9d442cae92442d5099,-0x476b86d247eb62ba699a43260cff5b823634,0x27e73c2ee19bf3cead550ce64a366b9e9bde,-0x13a72804db1fbc4683aa9edba38890706354,0x88174d39416e0f00d2b06a289af6019b205,-0x338b8bc1681b8a0a0e98e403cec268ffb90,0x10ff18c5c0410e76b1c8aa333463ceaba08,-0x4d8f8127beea27b068cac06ee0ce0c8a50,0x12fae4c6d909ce7b959684c81e29fa3b56,-0x3f217017557c40e83aeaa88ec7912f1e8,0xb02f53a420a462cb49988bb2387732cc,-0x196326389afc127eb064ba80ed2da8e8,0x2f686d83b9e518236dc366192cb4aa6,-0x45e59de4bc828825b24728b9ef0990,0x4ea7fabb913f40b36803666e4c818,-0x407fcccabe815d544b7ee8193c90,0x24136137906f6079647a13d851d,-0xc74809edeff6356720d7ed634,0x240ee27acfc843f30f4e970e,-0x28588d156ac98898a98694,0x875c9c5708b3001abe1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 20 42 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 42 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 47 indices rho q5 m5 5 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 47 indices rho q5 m5 5 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x769c8c0f02d204780000,-0xa694919187ca8a178000,-0x6e1b1e9f810e0b1c2000,-0x2d8d1df5d065a3ca4200,-0xd3b086d9f76d347cb00,-0x2de530a78d25eddd960,-0x7b531557f56d0912f0,-0x106e7799abd39c83d0,-0x1c3aa7eea1d1b5e28,-0x2779976635461666,-0x2d2f3377447bef7,-0x2a6a637018f172,-0x209a00960f6fd,-0x1468ba86e7b4,-0xa4e490611d,-0x42237a3da,-0x1493faab,-0x4c7fca,-0xc5ac,-0x120]
def m6 : List ℤ := raw_ints% [0x0,-0x5731a8ef857871d3520babb8d900000,0x97547a46df45bd87d4c344ef35b63000,-0x7ef73f2e2b3754398d191f4c3b4b53400,0x44964ac5f18431419f6b8b58f06eac3100,-0x1ace8f3760dd013172a7d9a26cafab354c0,0x813751772d28b87a597042cc51ce0a92600,-0x1f3746ffba207e2b1501e5b6b2cfd5ce6170,0x6360fd4f1e6a8a4e6adb3003ab2ba1a865c0,-0x1099df33fa6e6ca16a777241cc6926d4bece0,0x25c82ba833dbf4bd7195a1213307ec3f400c0,-0x4a01592a8bff5bd39286ca6d7dd2dfa3820ec,0x7dc8bfabfce226c18ac3f61461c83888161b0,-0xbaae61d9f941aa308887a9c899b3ac36cbac8,0xf315f40a47ee1296b488fc9464cb28b6adf30,-0x116b3ffc79ea797397289dd52f4380fd6a6afc,0x11a0e09182ad47beecdc92bd7a86bb82dcee80,-0xfc5c87db641619b2566544a2dd7404bea37d0,0xc7c5e5655e62615cd3bdb7ff96089057fe1c0,-0x8be9ec8c01bc5e28e9f93ca9816b588c239bf,0x56a01dc6e9e2cf510b71848e4f27011af082c,-0x2f566bb621cb9c9823a109c3b7ddc59961792,0x16c6fd13f9ac35f6ac816db765619a8834b8c,-0x99e5c3f554c854255e1c9f74d39fd5432eb3,0x38cb5fdea6bb229cc2aedb3c806be3f727f0,-0x1237e2c9ea328b7194825946b5f05c1f9e78,0x50bb7c475a1be3f3fd49a2893c1e6b06a30,-0x13256dde42cc74888d1757f509a361702ba,0x3d92eaf61f3e7b2eceb5a524bd1ad8a2d8,-0xa5b40961a26dd5da9c4b10b5bc549d114,0x16f3bbc8265f97b04773cac2834247cd8,-0x290c294d607a28e05c010723f555336a,0x39b3a5ab3d0433c733e597531190df0,-0x3d9304db2ebe3f5e3763af3841b848,0x2f8f066d1027889b7a79dff79e170,-0x18d7b06441e5eda2e2774a559e9b,0x7ec1f940a0511c950a5c21382c,-0x14e1be696c8238515158fd262,0x14df58cf797be9bd69bd44c,-0x3d0b0041e2299a735b77]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 20 44 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 44 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 47 indices rho q6 m6 6 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 47 indices rho q6 m6 6 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x120,0x1]
def r7 : List ℤ := raw_ints% [0x85701d90e32c4507000000,0xbaf08737a9c10955f80000,0x7b37ede1dfa801f58c8000,0x32d0a695eaf14a386e2000,0xeb4dc5d5d95480cfa1e00,0x32ce2635a4d33e64cc100,0x87df24f87b484b5774a0,0x1200f3778958a30b3710,0x1ebb1572db4f4138930,0x2aa51fd411fd58a498,0x305d806fcf900117a,0x2ce4bca71c4d6549,0x22069a77b19be2e,0x14ec32027cc083,0xa5187c3a250c,0x4019fadb163,0x13055ee066,0x41a28b15,0x955b96,0xad94]
def m7 : List ℤ := raw_ints% [0x0,0x8db0b28538e3b8f76552f70c60a00000,-0xf32e13d7376902ec4a05823546aa6b000,0xc9b383f54b181e3ea1efe6276b57d21400,-0x6baebd2e339b4e9b53affe4fbdc67882700,0x2994809b5d40517794cbcd2ee4e081548740,-0xc5f13499cff800c6832900ca5d891adf9200,0x2f35512af9d02d86c33aee7970463c0e9bd10,-0x9450803279e4ad34adb7819ad9cb8563ecc40,0x1870799b006ec2d0a1125795082809b30b38a0,-0x36d75bd08f2c16402aaf4cf31a2f1114623340,0x69dd217bd3619ac40b487aabc231bb178fd834,-0xb13c383bf70463ce6e8ea56de061a3ac10a8d0,0x102f4b39f2160735de86cba04dea673f2d64678,-0x14bc3c689f5eb7fc45975c7d28c8be46cd54d50,0x176027b966df6cd28dcc6e493940b44b68737a4,-0x173eb223415e407d122a2d38ed7e7e4653b8980,0x146bad550f91066e290dc3aa88a6266e0c29850,-0xfdbfcd489dd2afb367010ad6e3db8187f088c0,0xae335809e5a49c32ae1e8740dbf1e273ec6ba9,-0x699e48aa8dc873da27dc5726c5ba6c73a3cf74,0x3875f1b567bb72fa6fc0193342b240904fd8be,-0x1a8b8a781ba6bce3d38c5c34a9f4d2964a9e94,0xaf05d76c707113df4df0005ea8cd476f80fd5,-0x3ef0962984ff984be253e24f2f2b741928c90,0x13a452dcbbad3f1b764f37a76ec56b590f288,-0x548684b1082554e50ede45e9752f325ce750,0x136d19aadc7e1df4c1a40a6cf23f52e583b6,-0x3c6647cff2bdfe464e506afa65eaba14468,0x9cb6971803baeb6dd2d3dc3a925a93818c,-0x14dc703105e8f1f35574e959c4c50e8b68,0x23b7d201b14b9c43520dc4441732c1a06,-0x2fd9e33279f50c9079934662cb487a90,0x3064ccd5af11aa5415c0f99ba87af98,-0x232e7fcfe0bc4c26e5a78a035ebd90,0x1125da964a8649e3f6b93fc0d7a6d,-0x50bd48c38eb859799318960bf74,0xc190637897d81f194f667eeee,-0xacb62c6e5774ed426d0e5d4,0x1b83fc4db75e87d550171]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 20 46 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 46 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 47 indices rho q7 m7 7 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 47 indices rho q7 m7 7 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0xad94,-0x120,0x1]
def r8 : List ℤ := raw_ints% [-0x506c5d271d958e6fad600000,-0x706d4425f0033424b0160000,-0x49ed0ad846c3589717ea8000,-0x1e677ae68e11827069fba800,-0x8c5ba2c5e388c2f71423c00,-0x1e331c9b8566e72b72d6d80,-0x50718f116d675e44be61c0,-0xa9c478b057a0ed0384fa0,-0x1203e62de0bb10c6ff410,-0x18d84c446b7c7d6d49c8,-0x1bf8b3141ca1bafce74,-0x19bc92ad86eae33cee,-0x134c9fa6d8f745edb,-0xbb62910ebbca502,-0x5ae1a3f2f28eb5,-0x2286e4d046c04,-0x9f2f1bf1905,-0x20f092d172,-0x467d4ca7,-0x4a6532]
def m8 : List ℤ := raw_ints% [0x0,-0xe63f22187c720c9204a6d1741d0400000,0x186e660c60db7a61649b9c20272de9f3000,-0x140a06131894d34f66d8204d09dfaac3f400,0xa9383e125252b2339b046833f5c0fd124100,-0x40930134c1fc094c8f482e6094f24880200c0,0x12fafd621b5ffad53f66da3a9707536f250600,-0x47864c995647079c79e276d8203d73dd749870,0xddd166c2719bdb3f99646c15d7c32c744e01c0,-0x2410cf5a6c4a2ea66ea1d96d3e7d751f09592e0,0x4fd19fd9dd0ab71f937dcbc587d6d194fb76cc0,-0x97e3da0d5ac819e03506d85999029bc7bc1b7ac,0xfa8c44c3cec5a16e1219fb76f737aeb46955cb0,-0x1687b8e3a5a8e493c2f3bc53b288aa5b8ac5f748,0x1c683b290d4eebed716d500a3f96662d5b5af230,-0x1f7f10653b13f089303dd3353652fe3451ce14bc,0x1ec84faad31e441cabd848fc41111014d10c2e80,-0x1a8edc024e87f41374f1c478a2d7f95f60dc1ed0,0x143d6aebd7813a4f0beca189c69f6af7e66d7dc0,-0xd9f682cb85a64f58db536ea2eeee1d17c84f42f,0x816fc81f7e64045eb1764146f96a9de23addcec,-0x43b2fa46e587585ca7774bcb114a80d899cbdb2,0x1f1ac519dbd032dff12f49178d67d92b60e9e4c,-0xc827afa73daa3a84c3c9509527bdda3eeb8463,0x4624dfc09843cbc767308393847bd930f01ef0,-0x154c20fd12f072fce3bcfc08cd8030205b75f8,0x5900726e6430cf84cfe926b473d5211d6d530,-0x13d26775b7983400c1cd88da8230dde3c7b5a,0x3b93ccad388482d39994317634856556cc58,-0x9502d8b3c8b505aaa566c8aac9fe5616854,0x130ee9774eac833060eb9ec1dade2f53658,-0x1f3ae094af4c5fa656316e8ad281da750a,0x27dade9ba4183e0457a451dac48740cf0,-0x262d9c0b17011cfb1bceeecb080d52c8,0x1a1aec0e3706d05809050eae3c20070,-0xbdcce28eb1bd8e0bc65b7a79ab4cb,0x337dcbea39465525dac4a5a15cec,-0x702ca7a9474ca55457d4d40d82,0x5949ebd6c85cac8a04ab430c,-0xc65bb57b598abe9f8e367]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 20 48 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 48 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 47 indices rho q8 m8 8 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 47 indices rho q8 m8 8 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x4a6532,0xad94,-0x120,0x1]
def r9 : List ℤ := raw_ints% [0x2278236a2c17c0b37837700000,0x30185edd5cfbf5ca6590b70000,0x1f8eefca56471dc11cd4084000,0xcf2df3097cbd8cd58c5a06400,0x3b9e3d4a46f9a96e0db20fe00,0xcca08d09e84d7875729518c0,0x21f3923f5a7a1820a270f560,0x475fbce1d3a91ebe9f46ce0,0x78a58ba006195c5d4e5e30,0xa58820f284ad006e126dc,0xb93fc8ebab20c2c9fc96,0xa93f9cf462ae3ebb010,0x7dd9e225c5269fd1ac,0x4b98d4c12422d241d,0x24351c4cfbdb908a,0xd8a6358216b4f3,0x3d2c40df48880,0xc523f270d17,0x19672753a4,0x196925cd]
def m9 : List ℤ := raw_ints% [0x0,0x176269767ca39546d478f145caf26800000,-0x2748b5616d908bffb170e1dcc88b8e7bb000,0x1fdfb553f6a7b14a3d44601f8aa9209a2d400,-0x10a2a61121eb2ce469045ad765ea01806e9700,0x6467e01b25158783d5c0dff3f3502c304c5b40,-0x1d29ffd437d81e795fe6d44df7628fa462c3200,0x6c8fadf02682cac2bea48569dd59ba15b86ee10,-0x14c7191ff8959e06d7aad11dde32264a9b401040,0x355979f521faa6f3e950b2cdfaa5bcb430975aa0,-0x747b5b8fcd307cc594829249fba5aa4256304740,0xda9155ca9073f87edbc5f54980266c7140003374,-0x16352ced96cb4f3525c24d86d41c228f2aabdd5d0,0x1f78ef2cc27dacb4b73884ba4035ab51f88bf0df8,-0x271012c1f54d462275a80f152c0aafb394c620250,0x2a9b702d04d155eb2c381132e8b5326a57d8b37e4,-0x28efa9a7f85401dbb82dfd800591cd6720384b980,0x22b1912d1b2c29d3a7d473efa958f37c19a13bf50,-0x19f3684c842541b9e5ecefc92b636c83f3041a4c0,0x1120b2aeac72e2a2491fd51d1be33bb073be387b9,-0x9f6ce2606b7b9dba1630775d220483c5e0f2f4b4,0x5198ae4612e20dbf9808d814d39fb6ba4e5ca39e,-0x24a4422d270dd18f1670f345a618323488460dd4,0xe6246d29fef97e00ccc81f8fa5450fcad0abaa5,-0x4e9acd1d264780e13d7993b24b181294469bd90,0x17388f1330a39c690b0cff8dfee7c179318b308,-0x5e3c9a3aaa1ba68e406be426c51429fc5a3450,0x145655f583fa60c670d87918e95f9d8efe7216,-0x3b158dabcb8a1ab19608206cbb9ff15e74ee8,0x8e6dc9dabfcbfe543dba430b74d15331bc4c,-0x117f7207b5a4372f18ca92cfb60eed7ed5e8,0x1b6e9e7471ed7151520f294e8f49e453f66,-0x215549f8f1c4e6119c33641bc800fbf390,0x1e3a0df41158a779a5ca3d1879a8c0f18,-0x136cfd6d948a21da2a62cda4d2971e90,0x83909d31335a540c752bf53ae254bd,-0x20dfe848865fe382eccc1ef62d4b4,0x4105a9c5d54ffd744e1824a84ce,-0x2e24d15479e20652eb7e1f914,0x59557d8026d7582a2a6001]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 20 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 47 indices rho q9 m9 9 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 47 indices rho q9 m9 9 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r10 : List ℤ := raw_ints% [-0xbc601668508fe012a0aec180000,-0x1066759c5ec9fbf83ed142e18000,-0xabdc7005ccde543e31d856ea000,-0x465ee98602ba487bf5aa2789a00,-0x143401e196ece5abc9d0e342b00,-0x4529d4ae7caccb2483b550f3e0,-0xb7123d211c0d00b6761dbc170,-0x17f95d7f033a5e01ed141a830,-0x285f2e3621834b2e9bfc5628,-0x37270f0a35d7408928a8ffe,-0x3d6a2edd0d70bdffb876bf,-0x37c8fd331976b892b4654,-0x2932e6cd2efbef094981,-0x188c2519bc389a6e880,-0xba480b0d9212305a1,-0x44d577565336feda,-0x1325a1b4ddda4f7,-0x3c88ddc4a5926,-0x79b4178e610,-0x75a63669e]
def m10 : List ℤ := raw_ints% [0x0,-0x25ffeb608a89d2931944881169c9e9000000,0x3f2f730b1f4f7983bc24b5861bc2422743000,-0x32ba6cbafdd0a9e3c90270f8e9ceb055e6b400,0x1a306b5ab9674b66f2ff979377ab14714105100,-0x9c4e346b36fbdb7e1864151102acdc756216cc0,0x2ce0c050967a95c390e03f890e1ff83c8370e600,-0xa5115f07d398b9a4023a98f9133aeaddcb843f70,0x1f343f98edaca280630a05422e8816dd004cc1dc0,-0x4f19d635667cf923c1887e2a34398a2d2992b18e0,0xaa6e12b7564b8de785633c8082b27fc4e236418c0,-0x13b6cb04ba8dacba15099e7a44bdcf6678fe293a6c,0x1f98135d24ead50afde62686e183340a88f6aac7b0,-0x2c1d2caef3f0137fa3125b6d8343a242f7c79c7bc8,0x35e992507a6bc7d7f9b5199e6a1301f01c186e3530,-0x39dcea0b3cb66a97becc90ec1cb5a807a4f582da7c,0x36aa2bb039d2faf11eac75a9f2f27d97bcd276de80,-0x2d84ebf3acfce36b73e38d0cd85c5c92860c8355d0,0x216cde23133828ce839ea5e6c7191ae2a73dc479c0,-0x15a321b0cfd0af1383ee07c78a31a6896f02d2259f,0xc5550b5faf1ed30b35b5e5379b7781b7467216dac,-0x62d900327397a3b6cc547d2becbe36356e66bc5d2,0x2b63d60bea026c8a84b84fee1b83c1d134ff4dd0c,-0x10a0866ff6d683aae28720ac0e109dc7b781b4513,0x588fcebca053d775e830a797d29210d1184a25f0,-0x1974b5c83dd4fef522830ca71c941be30adb8578,0x64524a5438a69f1dbe7e42621b6a950259b3030,-0x14fa64e615fc9ec69e9388f1f0d03d56ee89dfa,0x3ae72f0f5e23d7fa7e9718311b5ac1540dadd8,-0x88d3d73b10f523361eb1a1fe1fe78c8f57394,0x10247043d5304f3b86cacf4c2b105d7b087d8,-0x1834007751ee76ab8e609085475f771bf0aa,0x1bfd48b93570905fe5bbddee1ca05212bf0,-0x180333283c0dd79159a6928201788a7548,0xe7e790501d6c38e230ccca4c8bf9af70,-0x5b5dcd99f7056e3f764daf2bcb2bdfb,0x15025612d377e3a18341c68cb37dac,-0x25b22db08b1f2fa82282c6b47aa2,0x17d67fa8220e214ebea115ddcc,-0x2837628e7f3fa0408743a57]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 20 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 47 indices rho q10 m10 10 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 47 indices rho q10 m10 10 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r11 : List ℤ := raw_ints% [0x36828ebbc18f6787555ce92100000,0x4bd1ae2fba837546f82122b690000,0x31937aa23d6969e000f672d3a4000,0x144335715ae5556e67b4badb21c00,0x5ce3307f785374db834bdfb8b000,0x13d44b7d5a25e50546dcb3743e40,0x345a6d8ca9e62eace21e6a45c40,0x6d6158bc0fb35ab983aeb278f0,0xb798cf110ace459bbcd563280,0xf9e408a79f23bad2788f2bcc,0x115177cae569adacb19f0c54,0xfa7868510927c13ce1875d,0xb7efd3e23b5bbb9f69f22,0x6cdef2798d6d0fbe3a47,0x333b687273aa4b267d4,0x12c0cc26df49fa78f7,0x5281aa8cccd3f942,0x1012461f40d314d,0x1fba9a5984134,0x1df42a9619c]
def m11 : List ℤ := raw_ints% [0x0,0x3dbfde7ce11ff62f090f5d1c4be81aa000000,-0x65a8a22a139c4fdcaf2c6520e348db1718b000,0x50c86d6e9cc95d55b26e0ced4b89a54a5879400,-0x294415d05cd1e0c92117a03f2eb6b6b531320700,0xf39c64343ead302a64d1462141d797446ae36f40,-0x4528b8ecba979a7eb591c9ef32cdc2b812e4ed200,0xfb6c4529948194dc4fe695cbbfa73523b9fed2f10,-0x2ef5076f80055b7ac53154897ebacae672a7751440,0x758d437efaf0e2c227360c763d797dbf3cb7361ca0,-0xfa0143052e3be7214c7dbd98fb5b68baa0fdde9b40,0x1c87eb49b2fb5634176939b2054094bf79f6550c2b4,-0x2d164338367930f79500d0926fdbce31e779dc752d0,0x3e0a706139148f3f78dcfca28dae47638e1eff1cd78,-0x4aacd596925b62f12ae53f18775a195623e83cc0750,0x4ee20edb21eef6b9b96714b4692441ed57dfa79bc24,-0x494b62967b8cdba3db35f01b82d76791bfbebea4980,0x3bfa947c31638dfab78ee5e7264f5aec964c6ebf650,-0x2b3ef0a94b9ff4f6de3bb1588dd306e6188b72840c0,0x1b763f242ea0b0b339416bd42ddc407354c2a5954c9,-0xf56fb408713f29d1f84908a145c40a9a87f1c88df4,0x7858344924253f4d77e1b75780c69922f552d45c7e,-0x33a4f526ab14e5bcf4c27c95c3e23a82df0beb3114,0x1352026370e34ad73a2107f3831a0cfca03cd30275,-0x644eb3aad47c3808f08e7d0edffccb74f79953e90,0x1c0de2d117bb755b772acc6a81a5baa21e6e5bb88,-0x6b5d656563bc79737cd8c75deb55c9ee00c8d150,0x15c09a16a344f2b703f516192cc2080e656aa676,-0x3b05b5c12f7d4e739021c4ac31e07286b1fc168,0x8417886a14ddb140e00ed365146270486d230c,-0xef5fbc0069b6917a5e9e7415121cbdd974868,0x157201e068ad9be7fdce9840c2307914c9ac6,-0x1797683c300f449727a910e7ce6160cadc90,0x13230cbb3c57a4ce2287e9dabd714330698,-0xad7642176169d2ed564723754614e4f90,0x3f8ec21ece953dfe1dd343536a53040d,-0xd7009f2a4c8bc8e640afd74b32ddf4,0x15db1d920b4d6e4c14bfc51b438ae,-0xc4f5916b51457dba2d21800054,0x1218e84cf505690af7ac5791]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 20 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 47 indices rho q11 m11 11 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 47 indices rho q11 m11 11 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r12 : List ℤ := raw_ints% [-0xde0dcce6c43410678b2ee431200000,-0x1347333f8b066c79ef4e073fbc20000,-0xc9644f413e86c25f6bea8361da8000,-0x522dafea0d78f006863521d707f800,-0x1780b36737f2a5909188e648f89800,-0x501d9675e1b4d9dbd5ff73f352680,-0xd30c467699772d6c11f18eb03c00,-0x1b7d5249c453f008a03ffefdc680,-0x2e030478879cbb3caaaba2b0b70,-0x3e6d3cce87b67acdeb7b031fa8,-0x44f8d4d2611166c97ebc17b78,-0x3e16a3c2a5dd48bfb74f0ea4,-0x2d611de3bf6832ce1faf76f,-0x1ab6489bfc083ea57c2aee,-0xc7d3c986c50a76dca2a1,-0x4896c88ca69a55d00dc,-0x13c74b1952c5fcb601,-0x3cf5dbfd82466286,-0x76b4c2273a0887,-0x6e2248bf91e4]
def m12 : List ℤ := raw_ints% [0x0,-0x6457c98aedd3f00c6eb8f74dfb592b44000000,0xa39b0acbe1027406f2a84d7251fcfe61ee93000,-0x80b7d4a071571615fe4767b253a45322de3d7400,0x411412653a1052c7868195ea9be48e9ea928b6100,-0x17c1dd6352d5a86d99e5c57eaa353eeeb2f8d198c0,0x6abace4941238d7df283e5eab703e4255184aac600,-0x17f9bca7e9d6100ec25757a7a6efebcae44df285670,0x46cd9b1da0938b3cf8f1ef8642a0766070ab40ef9c0,-0xaf167e47ad0a1524303b4d33944c311e93616e37ee0,0x16fa8f646133f645500d0339143571d8c0b3043f84c0,-0x2967ff14d22a8cb76f3c8929cafaeccc22f53856692c,0x4089cea63265920070aaea5180ca3d73cb9d37fde2b0,-0x578a4eecb14da6ca5c18437f0f3954c2fdd63b54c848,0x67ccd9d03a6c2124695fa5cbc00e3c63d7dff1a3a830,-0x6bf1f098e054ac788d996fef8a04763b85ef75547c3c,0x62aa8a564bfb95b3fc74ad90eeb65d732eb5b3f44e80,-0x4f5d4b4bed3831bfc6e5961f916b0f9960590a7d1cd0,0x3832d25ea4da77fe32863c810566aa15caee1b9235c0,-0x2303bd13c6e7698601b8aa4674898d02565a08317e0f,0x132b8125069f0d3d0c2701def03698df363555398a6c,-0x933c077f3acf1fca69229a1cbdd8a997452c4204ff2,0x3dc712207d1bf92f9f3358bbc1be2bf27a7371547cc,-0x16908e4a1df52221bd047bda76efe2567981eb820c3,0x7232c656505ee143bf4417b2749b0c8ccd51fa1cf0,-0x1f140ca37f51d824cb23c1ab7950bd09f4bbebccf8,0x737f2096cc576716d2626aed1c9b7d2f3e4d83b30,-0x16ab89e90fa4f2f115dcf0fa214fb37127f128a9a,0x3b6f63994d1cde2c805897c94b6c76b6662ba758,-0x80206ef7f0db2b549917d43e6ce7a5fc6de32d4,0xded894eb444c74019fb0afe305eb4c6c6a7158,-0x13145fddbec632678d0099c560b72e0cac464a,0x13f4d7380bb2ad371094d1be81cac3b09faf0,-0xf4c239e1369fb48ffe3fc630c67ffc1dfc8,0x820ca6ef7d88859428cc297ff1bb744e70,-0x2c47f826223158e0bf340085ed5012a2b,0x899e83249a79b8d6c5637ec63162a6c,-0xcac20a13de06a31c18738ae7e39c2,0x65abce88d2c0058d6f39fb6648c,-0x823fbff99c6394b5f52c5047]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 20 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 47 indices rho q12 m12 12 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 47 indices rho q12 m12 12 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r13 : List ℤ := raw_ints% [0x330726add6fda48f91da8d1bf2e00000,0x46cc17d167a0e8b6630e1d3e9b4e0000,0x2e29f2d8a78ae7a8cb497754b76a8000,0x12cf58401f9ecfc845aa1c3f4baa4800,0x55ef588cffb1a9de044e80673e3d400,0x1246952ccf3dfe48fb2859a0b5c6180,0x300c5dd8ea4db380358458a1a9a740,0x63e9e74d10ff04946e66b678df940,0xa6d26d3da09575d34f6846934120,0xe1b58243ad9cd480c62053a6768,0xf89816c4576507be8ff12a6194,0xdefd79c0f9cd013410ab94890,0xa251fbe59ac59800a4700c10,0x5f1aa1127f511b3d9a08081,0x2c3a0a6a93a5bfc3f5152a,0xff6fffd9793710e80aaf,0x451577a1f7ad5772f2c,0xd30aedde3626ae737,0x1968d0f5919fde26,0x17436f9fb80761]
def m13 : List ℤ := raw_ints% [0x0,0xa30ea781c278661433ec91deb870e64e8000000,-0x1076006ab076cef0fd0b1be16e43f6e8f83c5b000,0xcd3687b8883be1544e5567b6d796db505fc005400,-0x66b7f43c665485a44835703e62de37ae62b9e47700,0x251c77ad6b191a82359f7467a0f824b2d87e6f5c340,-0xa4f10346329cb5daa16657dbb8d415c265501337200,0x24a459a637c90f5fe8086fece6df3df77baca3558010,-0x6af7793e390d4d72a83213e3a4d9033eef8d16885840,0x1055cebe39327201ae3e21253984ac341126133437ea0,-0x21e069291de1c970e0fd18da8e94fa9f843f48c982f40,0x3c41a51b09adf6035eb8b8546a953dc89ff29389ec5f4,-0x5ca8622e56831e340224100a7258b836b9ce27a8a9fd0,0x7beba077ca4d2bc6cc5163c84aa6c0a91449a2ece04f8,-0x90c95a73aa1583cb05e63fcb28c1a03c9bc29e7605c50,0x944309640ccb4c4df0e564f2df7d78b1d7ca479290464,-0x85579f027f699caab6c4b6e768f50fdb4df513d925980,0x69732e1c9ac479487380c2b029be6a9550108e698bd50,-0x4958cd6687711b80ef2ffe03956450d1f7115f5ec1cc0,0x2cd8836365c906749dc272dbc4181586b2926dea362d9,-0x18117b75eaea7cbe505b971c78e11089d5ae393c57b34,0xb4ffa657b88edd3762a7ce1efbf6bf944ff72ad1e35e,-0x4a4346fb28b537a39ab06870b3d139d9fd0d9f9a4854,0x1a7c58f1c62e710b13ad95268bc49091133342d2b745,-0x82abb0eaaf308f3a645d62c792068c78d91c8cecf90,0x229a608a8a66c2785e772a60ef2fb3999fa67f58c08,-0x7cdeeb2e5b6e53f7fd44a87a4a674a51392bcf3e50,0x17be635d266244330d59f6f8d88f54eb83af1380d6,-0x3c239d6f1a27d470185a8e1996de535383bcbdbe8,0x7cda4be119912fac7e483c8757a8071c584675cc,-0xd05a8a5e7e0c2f4bcdfa1f47190d28e221b62e8,0x110a9e1629685f88e918ac59ae59365ada18c26,-0x10f08916934a12060aca1e804305e796c8d590,0xc435cd0bc498dd4a0c4657996dcd87f29618,-0x61b673f38544ba4db2f05bbec379d6f1090,0x1ee4eefe3f87ec91fbdd8a1cd5bf67585d,-0x5824c06ba59571c1958243a70b613b34,0x758f6ca23dee3a0ea865e29cf0ea8e,-0x3476710548d706de25cbb1c23b94,0x3a910ac17e9f3dd0838667821]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 20 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 47 indices rho q13 m13 13 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 47 indices rho q13 m13 13 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r14 : List ℤ := raw_ints% [-0xac74f45e2680acdb34a858df2f9780000,-0xef03371d796d7d8b97d08c9cd04878000,-0x9baa4c3fb354142b91c797f785f3a2000,-0x3f58389afc91018da134e3d0650068200,-0x120faa1a7b95e2eeaf91f073ca116a300,-0x3d5bf053ef89387019d5fa5e6c1d2960,-0xa108a1ca7a0d1d8825e8bb831185b70,-0x14e3474690576e65b4a4e18c1befa90,-0x22ccad82276fc166acc3fa968214e8,-0x2ef8035ea770f42a81874b0e93806,-0x3396f2b94464545d84ed3bdf153f,-0x2e2232ef55561d5a9352a17d7be,-0x2176f1978a834cb87a0726b925,-0x1387719646cc01d7f20d9c14c,-0x90a5043ad6447f2b5dff075,-0x33f02c1019df15d9059b4a,-0xdf5e347e66846d3ec1a3,-0x2a56bf843427e91fc52,-0x50db8b4eb0c867fac,-0x4941cee5199a4e4]
def m14 : List ℤ := raw_ints% [0x0,-0x108f7d032dc03a5e0d4606d09ebb7763f90000000,0x1a81a6bd77e5aff68c5173944b35dd284cc44e3000,-0x14759427ac80c1b07925ac44d6cfb77f9a8ec083400,0xa24376b57c0c0170dab1894b0baf22a44771d077100,-0x3a090708f763d7d022c5d49c2d15963d5dc4844e84c0,0xff40ccc83858dc7b1b6a0a6a3e26eaf95424746aa600,-0x3817a3fade5362be93eb6cf81e5f7d3ef0e359e97dd70,0xa1e8ff11ddc4342b665ec13063bbfcc7896fb239b95c0,-0x186ffc8026a7b5a7d10ec3b8f0f9472e46bafc4fa8c4e0,0x32108081441fb8b94be1f11d12d49c4d7870139fcbb0c0,-0x57ec8cf2df27882b0d79ab1fdde4ef97fc2ffbf4d803ec,0x856b7aa29b65dc691778629f05fefdd05440140826adb0,-0xaffa45b1cfb79a64065eb2591388c969ca8091718b5cc8,0xcaa58cd8338337f9fb14fdfbe2a42f60a86ae623ee4b30,-0xcc60e66914ddbeff662139f3c8a7b556805e511f9ab9fc,0xb4e68c811ad7b250d7e9c0d5b6b4fb2d7fcd2ecdebbe80,-0x8cadaa77bb7b5e1c46f285d24573a9a40d25dcedd573d0,0x60228cbd3b859e632a82f1af5c7ae088b9e8d65e3c31c0,-0x39b103fbe4d4d098d8df955d45ecaa0c476e4485ca6d7f,0x1e5b52d5a1beb7134f7f9663f400860525060426e9332c,-0xdf8e0d2215983ce169c38a9df49088153153555387c12,0x59b3b0426dfe362aaa4bec322cc336ee3d7e9103c9e8c,-0x1f3d9984098bcced0c358e2f92c1c66b5be22e0d5c773,0x96425dbd47139622a35be9fcf2864ced9059b31a83f0,-0x26b7f14cd77518fdb56e22d412cf9291434c7d0dcc78,0x87ab87ae8e700d90c721a11f7a64cee427ae84ff630,-0x18fcffe1cabeb62ab127bf6158402529e0984f0e13a,0x3d22d96dc8a841cf927d2f39c0cf8edeec6ba9b8d8,-0x7a345feecb9b68dcc7ada64e6d885cabe7a8ee614,0xc39cfad25791ecc2cfb1b0739c8298ddcbe672d8,-0xf4742d6b1a7d871ba99d88fc092ad74972315ea,0xe6d08eb6bcca07ef93b51d3a710a10b3f9b9f0,-0x9db6c01113bc4c6f8a72827f5b3ef8e631248,0x499057b9f2426ace9c6265c5cf3f1a765d70,-0x1594f238101d972ca026523729f6801295b,0x387c4f53d41619fb2002ce599d86f632c,-0x44287f1bfd40434e2c4aa030be06ae2,0x1b0f7649fb4bb8db1a1c8c1b3974c,-0x1a532220bdae127ae2afdf1537]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 20 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 47 indices rho q14 m14 14 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 47 indices rho q14 m14 14 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r15 : List ℤ := raw_ints% [0x21f1218bf637c066f20c5abb1a0dae00000,0x2efebae7b837f8160cdc7ac1a7291760000,0x1e93066380bd1abbd3d72416fc205050000,0xc6d48e3c60968c1b5f4ec876be8530a800,0x389e3dd233b4c2be5a324c9f4b2cf64a00,0xc012c86f9d3ae636218e0d48446207680,0x1f74a5d47a2d26ad8d9f57a9ac1897460,0x412b0ccfe3d41218026bae80220e49d0,0x6c5c723bd238d6bc4b4cfdcfa2a0510,0x91f071a9f43f6d097bb9c920d86ff0,0x9fe92f795fd4c7a9f2874e285ce36,0x8e9ce7a515d99bfb0e32b8c684c9,0x672287093af404c58c582d311f6,0x3bfad3a25f6d2c8999bedf12cb,0x1ba8240d39f58b06ab61700cc,0x9e2e50997dbcc38d236d8db,0x2a4c24cc6fbf4512826abe,0x7f81386fa47383ff7595,0xf1c773f605b248bd5a,0xd934964a23880e3c]
def m15 : List ℤ := raw_ints% [0x0,0x1ae92b252a585ed8d591cb1301f0a20274a0000000,-0x2ab1a66d0a1e7771fcc56b9e4dc32004ee687a2b000,0x20a755ce9c41d14561c0e3ae2a53b4991b752ccd1400,-0x10088cbef60832922c2e9a4135c5da22b520e99bde700,0x5adad8b734de90edc9204034e335fd0bca4542eb75740,-0x18b8be3eaf4ce44623928a49bbd1b2f763e3c8fc2a1200,0x560182904f73e90379b29001714c14576dd0cb55e0e110,-0xf588f67efd43a301101d6e976ebae5a782718e8ea7dc40,0x24a2f0cb11e8952733ab6ab9fd6de245d25792e1fe980a0,-0x4a2a1d1e14e3dcf0538e8d93b5714e6dd9e216195ed0340,0x80a26b2a24af7b1b1a615cfc9838948bf602d710df97d34,-0xc0ab262ab325cf30ddd9451ca81c1e8e5f373404936bcd0,0xfaaf2fe3c22b2fe3f8e6dedc94d0ec953021b971f8b3478,-0x11c94c20acaf5bfec7ac8bc521473e1de66b379015c40150,0x11abe4fc66b71a6a8974c85089209fe2050d4b075ec350a4,-0xf659fe0683208fd3aa4de75e0eb06ea2658c4ed2d316980,0xbc6cc2b23ab123a15ecd6ceccbf2fec237a6f92fa771450,-0x7e8781be0a777c2efd6d0abb1c08ae7e939b1d09e4838c0,0x4a8a10aa0a68df554c42ce8a5a056c8c37b9a2d592bc1e9,-0x2675dc0ac7adf7211e9d4af22bb566a0992b27d48097c74,0x11564f8f26058fefc1ebec05c0043bb37941501c1c4183e,-0x6cdd028cd2198f37f0b872bea44de6b1eae7cbf16e9394,0x2506b4cb0d79bce18c30db3a25993479e9581650eea915,-0xad9f16e3d754c5bf0cfd85f9eab817948a41943727090,0x2b888e25bcc7f0894137010bf3ff61a60e8a2bc1ca488,-0x941c604b91b52c49f6fea5ee7387c6bc2d8a5a007b50,0x1a6bf7458416d4af01600c32f1a46280691f11076136,-0x3e6e948d2cc89304ab483887f13f09da9cd10e91e68,0x7820de2c8fa48063689691122b36b937f013b0748c,-0xb8630716b79b03e665e5ac6e6924702ec9bb9a568,0xdbf3dd0dbba5bed39c6e1fde048d21775cc77386,-0xc52cfc7bb35cfefc544c0ccd2eeda924e555e90,0x7f17393dac659679ee7e27a71bb8045e883d98,-0x377c6ec12c21459211a7e80ca215846516190,0xf17fb7243425327b589118301b7e207a1ad,-0x2436ecd9628bc7e7325d223d7621cbac74,0x278331331c0327c41a840c7f0a3a7a6e,-0xdf3d1af73ca7f83bd65ebce93ead4,0xbd40a4154479e868ab88d551b1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 20 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 47 indices rho q15 m15 15 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 47 indices rho q15 m15 15 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r16 : List ℤ := raw_ints% [-0x64a31027403851595169768aed379c200000,-0x8b37154479a2f9e4dc43d222c860cba20000,-0x5a7baf6cb85828349e03caa0e8c492e18000,-0x24bcc9671c33dc92afeee347b57e7dfe7800,-0xa72ed58d1e64c0e2dc3ff57258dc4bcec00,-0x2366cfe05a937d42518ba7d0386cbebe880,-0x5ca195d750b7349827f1b178c0a68919c0,-0xbf9b919c284e749c6ac6aba88dcdad060,-0x13e0d408f0ac2f82d0eda2cfee55a9390,-0x1ab86611543ed1e1c6f1fcfa2b6564d8,-0x1d3743a2b07e365b166e5c46cec8fb4,-0x19fe51d598b4ee80d46b9ae6694002,-0x12bf6e751d3d1f2e98514ee665b23,-0xadecf143b21b136e4596185d19a,-0x4fecd94f944edc1a248c29c3dd,-0x1c75c8bf7899fd447befdf064,-0x7939b28b2c69e1ca1cd295d,-0x16b91fb36a1d8fdb42ffca,-0x2ad55008c1c7d7c2421f,-0x263655c58c1b199bfe]
def m16 : List ℤ := raw_ints% [0x0,-0x2bbae61c64cf9a205b0ce9fee3270743fd840000000,0x44c9111e7dd3ebf3556e779210e73287650296e33000,-0x3424d69c8c9bbc0a64c7d8908fdd4a1e09170a006f400,0x195e593a98f8f2a49a257287b608b5072a05748ce48100,-0x8e6290cd9fd01bb554ca13e3902c95946629e30a0430c0,0x265c22d73f8c3e6026aae81f500e83ef9d4c084cc708600,-0x8414a997819375e2895d0bfa9d83d9e88a338249469d470,0x175094f5e443ce7dfa19031828625331a755c2d8cb11f1c0,-0x370a503e5dd55fb20a7020bd7b227b4834b409168ef0eae0,0x6e1fa4c38b64fa04c3b46ec124ef90b6201fc9475d0c9cc0,-0xbcaeb996283a07e7d6dadac52a9b8727c28eb3380374caac,0x1170451fa50ef71f93033e391868fd64acaccfaf277f428b0,-0x16633b138f629b7d5f7643bf1afaccb77972919eb5224b948,0x190f601ceddc569b06c256550481d8184a3f7a743fa011e30,-0x18887ed345645b7e6a7d29787e4511669d6e58fe745b953bc,0x150bb8071a6f6cb3cc8bbc09a3b43665831184d504e5a2e80,-0xfd5dafc0caf96b84ae53f26a5cbc42a89b33488b1c3b5ad0,0xa7376cf8284d37c8cc18f4bcbc8459a97aca06cbd25c6dc0,-0x60b7e8ab3ac9072080244e7c0ea537dcac204fda874663ef,0x30f143c9d53ac77bf6ee6e58bc5a5cbba91f8b09260a27ec,-0x159c3514593df77485b8081721d7635e74435790d1906a32,0x84bb0f5237369dd23cd932450e944c567e39c7cd159a14c,-0x2c16fddf88162d5bbf1eb8854547e0e54b301689306e923,0xc9913ac784524024a18c7617ab9116108a955f00b05af0,-0x312dcbc84e855fdbf8158818f9437ef84d6da60c3103f8,0xa27322d3d3329ad92a26cfff2c9155ef0ade388b96130,-0x1c10b840ab623168137809ffffdfb7829e9d179ba41da,0x40094e5ecb7902bfd6b0178877283b331e2e2c676258,-0x7694799092688bdf522ba4618034147b1ad8d3acd54,0xae7977112dac618b584995fae582076dacf96e0c58,-0xc696f95be7edaa52348eeeab593c6d36e980dff8a,0xa8efdd5e64d7bffaa1c669762076d7c85b0068f0,-0x66a810624dfd6f45af65ecdbd0f4bd84c288cc8,0x29ec3014ecdd7c93f6c2fee9405554a08cdc70,-0xa91223d7b7da3e01269af159e2564babeb8b,0x173a1d6c31e8ea660af88140f7d7924e7ec,-0x16e732f5deac25e79d731192ae80c2e02,0x730edc04024bdf0c23f9fbe340360c,-0x550163385bd81312beacdb17927]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 20 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 47 indices rho q16 m16 16 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 47 indices rho q16 m16 16 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r17 : List ℤ := raw_ints% [0x11b4698d4778b36c33af0644350ccd17100000,0x1878c5b2076eb5ebf7687fcec3662521b10000,0xfe42e12d69faed9cc5fb090cf516761a5c000,0x67221ca63895ec69be5d3f80ad1f5d7c1fc00,0x1d4d5597526a4077ba47e2566acbf6e25f200,0x632941c18d147ba803adbf3a84b4085de140,0x1032150549d6db7742afa0a281220afc31a0,0x21740f98e5126abed6003345acae1e09ea0,0x37717307e8b8ee1e97ecdb343793230150,0x4a6601861e3c825c2cde03b0c746de2a4,0x513125b04f9560c72cb1742dd0140d1a,0x481572f8fe07254447342635b1d5f28,0x33de2621ebd35e8665cbef10c44e54,0x1dfe9bd7c4bb050cec8ab99194725,0xdbe2082383448efd52e38e230fa,0x4e08c31f07195e51de62259a3b,0x14b1e85455c02aec371f71878,0x3dcbdf16299ee9272855a27,0x73e6eb240d154cb1d42b0,0x66cba87e4d31740d34d]
def m17 : List ℤ := raw_ints% [0x0,0x470fb5ee23d15a7493f4fc3e311f6bce7bf680000000,-0x6ed9d600556224d03482d9e1a46f81c30ca2fac2fb000,0x534f8b1e793e9531f0393f8edea5a742fd41ec20add400,-0x282b91a3487a363ee54c53b7256b6cbbe8281c12b4e5700,0xdf5f81b5093edf5992f41c808276fdc8bfde342bafc2b40,-0x3b995e353f6702825be6e44f0ae24542fe1338f6fa92b200,0xcb2734e6bf8e3a8e55dd851f32f67faa52bdec82e0205210,-0x237c4eb6f0d18e6a11141c8d8fc7893a19ff236f2a47fa040,0x52dbe0ebaca66888211a9dc59815cfbfcb05cc686fe6a22a0,-0xa3e4e81c73ab94f757992cc2b2949b8b41523495d96611740,0x115775708d8456eb2d8dda74fb7bfd4a7b96ca405101dc2874,-0x195303f692a6bc845a72fc5191dd2fa9a3e32dbfe0e6c0a9d0,0x2016058388ab5dbab19385e200921358f402c1f5324818dbf8,-0x236c39f30cca8dbf2c334d7712ea210450a0cd9156130bf650,0x222d49daaa70446e3132255c471389b3015b7a8ab89bc6e0e4,-0x1cdf4c309befbbe5f68432f467defb6fd095231071cf317980,0x156005c30d64b6a03ad352c8df5bdd131bd053fa1597c1fb50,-0xdde0b90d90039f22efe6d188db8a0be3acb915818eccc94c0,0x7e05dfdddd5e860c81b9401008e892dca53829ae6d99b81f9,-0x3e8d209bf6ba04483258442b82b6857086e5d4702413fd1b4,0x1b0e6f89e1e7a22da3bdcfdd3a737ee58337f14e4fcffdb1e,-0xa29129f175f8ce5cab9168e2d4c868633392249105b352d4,0x34be40679176b6285a19034fb88aba49ee3d4aa90558a7e5,-0xeb18f3b093ea43f3b06a9648697602caba1ac6ba1fd2190,0x37d04b9b7ba6934da3a749c3bbfe05f15e0c246c0038508,-0xb2fdb2f2026f6af2846a9324a1dd35c439cfbbbb618850,0x1df1a63738dfd884c945201d45a8e3cb5c681f5e66a796,-0x41f68a9f77953491e5cc573a7d3763c8677de7cf608e8,0x7586087656ea5547514422143b938c2b85c5e591df4c,-0xa5b5078efe5ebb3abfcf528f1a57185036b0c148fe8,0xb3e4a5e5d0e0724f7ebecd2caef19cc37b1dffb0e6,-0x9125e1ca40b2f8530ca898bf849dd7ac3345b7790,0x531ab30f16f36e10f09c2b57716ec12177677d18,-0x1fb98e23ab3f682062d5e3a339db3dd42fa4290,0x767944ae9e6efe9dcce48d3933df0d80f2ffd,-0xee6da186be24cecc2b7c310e920ef4571b4,0xd4607bd00e124c50c653857d0ed98c84e,-0x3b47526edba78a2e226bf3d8cf44e14,0x262b16bba05dd357257cf0f67441]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 20 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 47 indices rho q17 m17 17 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 47 indices rho q17 m17 17 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r18 : List ℤ := raw_ints% [-0x2fa0bc024bc1b36af20fbe4a1a6d8da40180000,-0x41c870da44ebd9e46748b8adbe5dd4fd0818000,-0x2aaed9d1d4152fb4cf1b7eb79c5ac246424a000,-0x114c33f09a651359174abe33880a7a916961a00,-0x4e8e9c3fad19beb36b2d119805ab1ba1271300,-0x1098fefbee861a39b7479ab9865ed5ecbe8fe0,-0x2b52a2723dcdd1ee240522fbfa7c489f8a0f0,-0x595f4c056844068a26287a0d325f3fbbe3f0,-0x93e93071bf94617d48b265f81d25761c068,-0xc62c2888de4f6ec4d5aa0853d418dfcdde,-0xd7e609439b0bce3abbf4a002c2efaf977,-0xbf50f8b66da5c75d8ab579d5365828d0,-0x895f4a1f0be8e1c94a1cfbb475ff5e9,-0x4f4147cef0b3531ba3c603eef485d8,-0x2437aab6259b28385b64c17cf3b99,-0xcd0c01c9960b65427bc3b9dbc6a,-0x3632e1e7652dc45bf0993632af,-0xa13b3771be5f3851f04ece2e,-0x12d189addae4862e8efc180,-0x109b9c0ec26c72e731e92]
def m18 : List ℤ := raw_ints% [0x0,-0x737987a2fa3432fd706e19e50fd30f2f8970900000000,0xb2afd4a9a4acc03fd0769ae65d386751f1ceec30a83000,-0x852c80e6c02800dd3f9b0dbfc9bb644d442da1430f9b400,0x3fa8140af3fe3521938c64d19dc0f725d756a9857d729100,-0x15ec86734dd30597ab4fbd8ddca2440ad828217dddfde9cc0,0x5cb72af49314f9682a6a948bc2fb465c6a1bb6f670e1c6600,-0x138f1c62bef117f309473194d1a7ed14841d53b3188c653b70,0x361af73465d1f39185104d131749ff9c38ce0820f6f41e0dc0,-0x7cfd34f5b6d7d53e257bc86786b2eab49974131bc87f41f0e0,0xf47872c3a7dcee75bdda9fa851cbacd47808c2d818a80e48c0,-0x1990bba7d59221ce967ccb02a2489cc95a3308186ba31cf7d6c,0x24e05c87ec0c4287a8325d4780f6ab987d8ad18c02b896153b0,-0x2e1f373586c73c1ff3351a63a11af2f6a1ef8c2508b780d5dc8,0x323ad7eca64d64648f29739f7e3c6ee1bf05947e9fa47ff2130,-0x2fc5e45a1863eadffdca64f0f6f10a010010f062264b460097c,0x27c06a1c68dc2b393213278fbabec24b1d05ab5598bf46b9e80,-0x1cf642a39b580d0e8a345760e3479eef238a8c4a57feef9d1d0,0x12792b13f73372ba845da08c83a999b7c5b62b67662152ee9c0,-0xa4e1f323ddfb6c016cd25faf7bd00e770599358c441bf1d15f,0x5048d2ba14a363eaa4cf42b40087f7915fe5bbf1f88b6528ac,-0x2205f5881362d1fb000c1bb7c05ad1c6f16d8695a5c7963a52,0xc7ffae1c9246ca0e45e6af6fc57e3197cc7aedd55d99f100c,-0x3f6150da5e66cfbf7addcf90c7bc89d8256750303c23135d3,0x113737f838dd8cc433b401bba69a363938bd00c230e4aa1f0,-0x3fa1507d2f2229d602597319e79789915d1afb3c7ce4f378,0xc618851672976fda7d7cbfd93c42384b0e3851bb8cf7c30,-0x20163cf815e0d4fff368ebd312f949841bae62267174c7a,0x443ad83331f54a4fc9f0427849d0e7db4fd8b7724623d8,-0x74ee39b424cf809c3a1ccc9fa70c7520923f524492894,0x9df10b2e08aea29c737f4a8dcfd777231e2d57fabdd8,-0xa378679ec2688b0a98baf98c1b89c610abef0f4a32a,0x7d0a2f41ef696e343af1d3d9fd3e27b8db390907f0,-0x436a8100c4f79ca4a2852ad728c0caad5c690cf48,0x180ae83a3efb36639eb75ed7a55b4c27b206cb70,-0x53162c7f095aaed80d9338027acaa701e9a0bb,0x99018bd2cfb942bc3ff7bfa2364c57ef78ac,-0x7b0fafc39e2f33b2125658e65478d4a322,0x1e8772c0b1699542c380b35ada5b00cc,-0x1121db9a6daa07d4e193ffd1f6c17]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 20 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 47 indices rho q18 m18 18 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 47 indices rho q18 m18 18 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r19 : List ℤ := raw_ints% [0x7b1e1d7f9418565a216c177ced51ca349c700000,0xa9ee9dd5ca5eb06ce2b60546ab531665c24f0000,0x6e2d703882329c783d40b5d91b1c4d623148c000,0x2c9d33b4d991db55654fe4387bf350bc5ef10400,0xca6f21c0262f790f01030d473fcd3980325ac00,0x2abaa2cfda19e6c0237266822e098545ef825c0,0x6f697e169e600e3f81dad455e982f3f4765d00,0xe591bdd5f150cf5ccd1c5faa9a4b5132cebb0,0x17b73ebf12bdbdc9d2647a8524c49a7b160e0,0x1fbaef4fb5cfff89589b21111e63a56ee6c4,0x2283e2e7338a0e80605991a475d7eecea20,0x1e88873402ba354dee386daec4d36fbdcd,0x15e202f15c41f82af4f8eaad41cf662aa,0xc9943b3f1ab47e70638d6279d3b1b8f,0x5be709d6c82e38e6adffe1bae439f4,0x206f5fad601909ba89d5a4831b78f,0x88c63532741248bfc9e68f090da,0x1958ab45c87f18ddde935b98ad,0x2f284fc4b3cdedb061438b08,0x2970d7d2bbb45ef775a6b4]
def m19 : List ℤ := raw_ints% [0x0,0xbba57c68d694d2dbd6b2ea1439b6f8ad3f56ea00000000,-0x1201b5c7fe41b7352c325d0875da0a9dbf4adc02806cb000,0xd4fca132ccb485111f78defdbbb1910a3248107ac8629400,-0x64f33045fdbe71e3c8c365f72e2aaf7879bad965ec885c700,0x22769dce256d52abe01ac49bfa04222367242e9f7c1d583f40,-0x90698b4b8cca67f3f1283cda2de9ec58d862ad7bf6340d5200,0x1e2c9def41900d98bfa1c75ab4b4a78f491687cef1e5b34d310,-0x52a35dde7cc7be0277a56316bd7e06fe5edd02222bf48b3a440,0xbce9cc227de18e46d5f1b34a9aff784b41d1177af9caf8764a0,-0x16d7815c6c6710afb069074aa72114c8934344350341f1086b40,0x25c804c44bf04d9d0442dca7c4101af17f23d640de558b9607b4,-0x35d79f90865da5b5149f2f138456fa60d1b88584ab9a7b8566d0,0x427d92adf89e148e514b569d005210c88d1804697610911e7b78,-0x4772f261f1c9320911ae87a9b424c607511fa19bed32b91d3b50,0x43001d1f3e5e119c9aeb688564b926d70710d42a1cb1e1c5f524,-0x36ec796c3d22ebc50ca354cffbf6f743bd2cb674547a73828980,0x276339f0de840aa274883d071da4da30e105f3dcb57466dc7250,-0x18b46f91cb55e53565156421560cf6295c24eee9047ce9fd30c0,0xd898f1b494f72b5906d799ef5407c49b420fa53e6d8bee4b309,-0x6779ca19dfbb9e0da1093dc90e20ab6d3971c5430bcce75baf4,0x2af7be72d0b1ff147f4abb7c629ff53ead71705af0212a80bfe,-0xf720550c0c683f0be579995e4b5d36a646c54de00a2e97c614,0x4c7ff222e29e050e66beeb236af6455659b9edf09b718783b5,-0x1442abd5b015f93367fa9bd7f6a64562a30274ec6d8c3fe290,0x48dcb44cc5d7368ad9ad80f875fe4b0e39cbe487eb4baad88,-0xdc31788487006fcb4074e32d11f05d2b597ea8211b6f6550,0x22873b6d52134e9ddabeab2b6109a439fd3383eef097b3f6,-0x46dbdd5e5d6ea74d579f8e3bfdf075d9c3a4d7a28fd1b68,0x74c757f923e4044633c07f62e54b2669fd5b4cf9cd760c,-0x970e4d43e5d5a51ea046d4e77b9fe2e2677123b86a268,0x94fe610358bfb08988bcaed034b38a6ec3157ad1a446,-0x6bfcdbe6022d9493eee76913cc1e0b28c4c63542090,0x36cbb2ed62a70ec3dc42a9b3ddc418f5d90a03d498,-0x123eb5fbb1db09308a4ae7fcae50805e149f2b390,0x3a4fca3bc7b4614d8a9aa0abb418afcb7b6534d,-0x6234e7b82831815949045c528b1d9468bcaf4,0x474b0f8329d1451d089bd7c694046c1b42e,-0xfb78681c5e26b3258ac2d6997436a554,0x7afffebfb0a32053f631afed86fd1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 20 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 47 indices rho q19 m19 19 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 47 indices rho q19 m19 19 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r20 : List ℤ := raw_ints% [-0x13335aeacb084aa9732145cf6326bdfd68f4600000,-0x1a7c1aa2651b47678da4483c87007dcefd39160000,-0x1128f1fa855bcebf08d43b32d40d79b968ea378000,-0x6f1808044bb73c25de8f1a9963b045f6849b9a800,-0x1f7ac2101daa663ac230320dd65c93a7d842bb800,-0x6a3809fa24805eb41d9e2ba446d3433684ab6b80,-0x114b008fbaa92dc3de5e944f3e7eaf7b6560cb00,-0x23985d8263e2116cd1fa34f919e552a411f3140,-0x3ac449d5a3a0d986b7f3e755d40243670d0c70,-0x4e86bcd46f09cf045ddc403163ab1889a44d8,-0x554cb0779b2e8cfecdda01a9186b0bca7c28,-0x4b57e0c56777bdfc6faddc0c1c26620f888,-0x35e80820f5a1798fff3a57a70f38e70df7,-0x1efa4be60fb580eeaa18e99690292d806,-0xe18095b408d21a3a167dbca828d9069,-0x4f6723ea462535e38e778e50d4c99c,-0x14df831e9147460a8229bcccf0719,-0x3db60315018393f41e7767bb6be,-0x7270e4b3faacbb7cbd57f026f,-0x6432670f22894ba9c655900]
def m20 : List ℤ := raw_ints% [0x0,-0x130ecea2a5cb1d6a53ce2bc60ddc9541986ed3c400000000,0x1d0a4c4e0eaf8df75c6bb636291bee7170bf270cc0a9d3000,-0x154cc5ede04aeb3a5d9d393b08f0b7baa5129d913191a07400,0xa0356359cf31b4dd7c9eb09756d5848e610771c094a4c1a100,-0x363a36ab6e70b61757951a9e98bdbba15da333081b6eb89c8c0,0xe1353875383ad977ccd05c594c9698281f8f25b2f40bb4e4600,-0x2e9e5e2a9aac64286c807cfbef60d8079cc18c05e84da3c11270,0x7e6eae2a25de614c8644609e576e266d807971841ffd9edbe9c0,-0x11e1577d14a1a70f39c34948af21aa852024bdfba65b468c1d6e0,0x2238ac691387cb81c7cbd0bfd2da61c2c2fc3f3a1b5138bbcb4c0,-0x37f7ffb1084b8b87078fc0ad3c8074a87d50a11dcd3476e36dc2c,0x4ed214eee926508ecaa6c1dfc651a88d8990cf6bc594341892eb0,-0x6020bfe547ac35b82cc8c7f40ed39e00fac95ddaae1d498b9ca48,0x65f1a0076287dc16b4f14c4e5d9036533be11cdff21c7073b5430,-0x5e462b09f0f01757568cfd06d3374fdb710fdd24bdac426ca9b3c,0x4c2661f046b54b99ccfdc91b70c2edee003ee2ec2883f48280e80,-0x35c30e783ced1a3bc5b12e86a2dfba62f93920bd7e84b727bd8d0,0x212a277c8278b5a15df521cb88f60b417841c62667ac8e9b7a5c0,-0x11da9c336c8a407e6c1b80d98f717406bb3c3aa14d4d95b9025cf,0x85e9e7609b5db0b88c1d568ef93de3920a51ecd8e4ea7dbaf56c,-0x367e08529a43535ca61381e22d11ec3f15108119b111cc3a0c72,0x132ab98b962e4d322798503f0655b8e5eac72084f9b2d80baacc,-0x5cbc79019891c2135af3ab0d4aa91e8c723fe07321777cd5d83,0x17f28eb21de3dd3543b5fd9c7f995caa1b0f13a4b8bd33058f0,-0x53cb567d6dbe7f93732bfa699a45edb9990364b1f5a5e11af8,0xf5cb4c26871275ffa3880c3f21b32a5d4b0108ddbfaed4730,-0x254ed6653ce361443370bc8df2b61accf29309e6d92caa11a,0x49e069370e9d41a01c8c5873e71cf65eb507846ed9477d58,-0x750d18d47288bd4a51f35ae7fc606b74d3839e9fee537d4,0x90f2296911b7115e6b33343cc7adbdbe17e4d6df9e0758,-0x88304e73c01dd389183bfc5d58672c1cf1cd2d708a0ca,0x5d7b7ca4cf477f88ab36d9223098c864596b2c9a96f0,-0x2c9e623dd10ec787bc03592db8f1464943124e259c8,0xddcbde43c840554abd3fbe9b1055c1065c8cb2a70,-0x28f34bcf62d42b7072965e3d85e08ad900e578eb,0x3f0ad6cb5be9ac57b8e94986b22c3558efd56c,-0x294b173a6e1a20422174bb253d12d5ceea42,0x8169c803b92a7c84c3efed8e3018eb78c,-0x372ca8362c29a8a41ddbdf68ebde07]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 20 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 47 indices rho q20 m20 20 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 47 indices rho q20 m20 20 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r21 : List ℤ := raw_ints% [0x2e6c8109378f3d36e23886c6e41eebfe6e5b8000000,0x3fff9f423a8646123c855ab800c5b9939deb7200000,0x297083eb8f029c036f1c99badf6419ed8782e0a0000,0x10c1887aaf8c7f1f650ac9d5017cefe6f8c70ba8000,0x4be921dfc0a61b573f43c13c5cef928912c2d95800,0xffee41ddf340d38bf2fc29a9b00e1f63adf46a800,0x29a13b969cdc519164f34ceefb4111e305b9a0480,0x559b2dfd246f79ab338e262a2017ef48c5828500,0x8d2f29322635e94b1a59889efa4e04e7565b6c0,0xbc7002a65f836b81c122de021a7d892b18e990,0xcc6e9b608b57aa96b37e861c4cf0c862c2a28,0xb451dab3470f216ea25613f1e742e7e645d8,0x80d156454681bb35922cdfc516bdb201478,0x49e6d18897b43efeeda199e49e7bf76e09,0x218f7a9836ca83ae81bd47c4da11c6dfa,0xbcaf76293f2191be4f7de47ec734397,0x317cbd7e53ebedef30bd501dd6f864,0x91ef3a3598301ab067a4a20e86e7,0x10ddafd351fefdbd26cd83f1442,0xeb8142587d8400c1c525b791]
def m21 : List ℤ := raw_ints% [0x0,0x1ef80fc84d6a0fccc82f0721d686728a97b4181e800000000,-0x2ed87bab033cb957745f749527cd69150fad39da4c0959b000,0x221912799ad49cf4cb9ec7d4ba7dcaef3ff0a6a151f38ab5400,-0xfe6f069410d648c22311f1702ebe9e8e4a3fcafa79d9fd43700,0x55682af2ffc13f804f9b214502818c274a7145a0da6ac09f9340,-0x15f9fee7e0221030b5e14f38807df51f508954e1085039339f200,0x4820a93163dfc5189b715e94cffbfe2a8381dd69a2157924f6410,-0xc1c1d6bdd5c858b1089ce7943f7293d0235af32942511d207e840,0x1b20ee83b6a1e26d30f6849c2ad3c92ddf0f782b917707042346a0,-0x33611e04c8f2643241b8ffcb25d2c3874a410678464e9fa376ff40,0x531b614278259bf90755701ad56632db5e6968f16985cb882a5af4,-0x73af58b8b8908874468a3e0093911ccc272c3a2dd1462b5011f3d0,0x8b5d818e81ee0df8d785ee40d7f514d136d2b1be3a0c21357b92f8,-0x91e470c2976f11c16416a75ca9f97bcf8f170193a610fc062cd050,0x85139b07a0ac777c20dbff25e60bc201235228da86c24a4826cd64,-0x69f075ca1e2c0c1c32b2857ce9831fb9e913fac6cc26715c2c9980,0x49a542b5369c557599fa0729a9c4b485a86eec296091dda2b97950,-0x2cb04ca00176fd4dbc6ec535ec8ade8f50a2b09d56b74aa22e0cc0,0x17a38f99e2d37f6247e4751ee313daf26853800c0a8a35247a6519,-0xae0106b8847b75bdfb4f75a610ad2af36acff0daf5b7b18c47834,0x4564d2c0749db0b4fff7daf18b329a3cf2e134a102c2bbaad8ade,-0x17e2a2988d8e78035ba4682d9a1f3acf57006819ad10c59bf2d54,0x70e5b6c1951b9769025197de2502acb1fa8a6d3f38ffa6270c85,-0x1c6d1c182dfcf9f9642999be0b7ebc500710c53eb67d6f0bb390,0x60c62249bc7a2a711cc1da4e51bb7416676dff7ce76750a9e08,-0x11381d022e8d0ed08221dbc1fd2e568b740899995116ff71250,0x2878f4d9ef6a1ada0418dc418779779d187c314ba33bf6e656,-0x4d508a6d316b948aed77c48cc9fc9d73e9b1016497020d5e8,0x75bc7550c1cbe35ffdd402d48e36d814dccd190bbf21f8cc,-0x8b85cd2eaa78814801210f1b30813aad7a8910247325ce8,0x7cd319d7dc56ee3453e9006f3c378840f31815ff0aada6,-0x511b4c1397389481d5c828aff84c5ddbb68ba9ce05990,0x2464a7e55e039f6845c931f6d4e3f69c73f003b8c418,-0xa8b49f80ace0938c39abf98a4ca1418b381203b490,0x1cc632cb181beb1653ae872c5ca18efefe10a5b9d,-0x28790508303cbd3cdea735191d9b9f3c527f834,0x17e963f23e1d6f073a51912ead815fcf91e0e,-0x4293388de18a77e986be76df3bf5423094,0x18bdfabaf077d2456b0f58f6a2ad461]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 20 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 47 indices rho q21 m21 21 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 47 indices rho q21 m21 21 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r22 : List ℤ := raw_ints% [-0x6d1d9831b73ad346d94c027ee85673c7b77e4ff80000,-0x9657b59940c96535d410062c34cb2501566ecbcf8000,-0x614a835bc363324245f4709a2d4857c848b74eae2000,-0x2750822c26cc3792c7b2e4c0806c47cbec34b6b36200,-0xb1fc662009a7544be9bbafbf4a5c5f9a760e40c7b00,-0x2579fdee4aca0ecfc1355b42d8b69e3979cda126760,-0x6174a54dacf0e22ffc4a299bdd0b0d518bcc16a1f0,-0xc839ffd143a35bd8b36e94cfbdc7327457f565450,-0x149e6627bcd0fb8a21c624d3244ae4f29041e60a8,-0x1b7d99e7f957970503717aff4bfdf1d0f38b8d86,-0x1dca2492d36cf36fcd7a5aeb262a737ae3c1467,-0x1a3e2a2c6ff5fb81d1a05d646ca35b947d4a8a,-0x12b8b6f09fc0672bce6ee25b0173c92baf3cd,-0xab95c1028690cd26e634384e6a1a9874224,-0x4dca5188827d8b0e37bcf2e12dc659a50d,-0x1b48c5867218e09df24ab7b3f4f49b03a,-0x7242c46b7bffed5a07871975b00541b,-0x1502e3093b681e38c89791fe813eba,-0x26c125151346a1738dfa0115948c,-0x21b9a250f1dc4d275b4a5f8ca8]
def m22 : List ℤ := raw_ints% [0x0,-0x325319a57dcc59acc54c6b96fc9a7a213684a7319000000000,0x4b95e472e907d050b246c6f5ea7dd38719b2cf41712e9c23000,-0x369c6851b97a6a36fc9d315788991ac38cadcf0f8d5c88bb3400,0x1945b98c92cbbfea40853fb6a7c1203047d8062f7744128e1b100,-0x86a39506daa87072d627ba76d5921dc9719f30cf962de1371b4c0,0x225a477869d66de86785e73f0609e283f9288cd6d8438f65e62600,-0x6fc02206618668430b6f4b559d03f554f8324291c109c55d245970,0x1296a85abeae85d5091a5a095cae0d665704a5ea41cb4b425e785c0,-0x293cbce16acdba72450b581a8f504d7b39ec2f8d3fff978a3769ce0,0x4d4d196dd2135b5505d76424a36997b2818dc33f66ede134c43e0c0,-0x7bb083e8adb83f63b05456b7153ab8fd711e802b45b4d8832a5a6ec,0xaa389668b37bad2c7fb36498c09ca730eb7d008124a95f007f6b9b0,-0xca9b21d154fc00c4a000b152e7e0c3daa460d410420a4ba9ea67ec8,0xd167b238f92a109a6f60358015a761ad48c23d7ae4f569d8438b730,-0xbc718060acd3c4b9551fe43d58570e73902c36e51e36aa15e00c8fc,0x93e02fdb414b4a7268604f9e04908e28a843ef02bc8f10861477e80,-0x653d27039782468e2a33a1b327f48191c1d5852ae0c8bcbe0dc6fd0,0x3c7072e287b1b1d387da657cdb22bd9c0580a08da13210d4b1aa1c0,-0x1f6b1a0a1a3c183d78ab0c8d0568de5fea21d76b1fa18674edbd13f,0xe2fdf4c04eace23b2fecd9537c61e47969b3e59089a7859f484e2c,-0x58bab5f18ddf2bc99a07c048bb3842934f6043fd3c3d6c6b4e0092,0x1de3685d2a1dad303717e813eb91d09229bfed7865cdf0284a318c,-0x8a03e0f8fdbe4ad7b0e0159f17ee8fa534483335ae392e6571033,0x21e22754710479951269f9f6c1821c96c9510cc9b0eb62ed87ff0,-0x7039d332bba6731a8c36f0fdfece0b94e3e8610aca4adba4fa78,0x1360efe0474715e4b1fae29fef0990c0d712396fb16123fdc230,-0x2c137765559c284c639d1edb33133a2108745691753aef0dfba,0x5135aba9f182c286f8f3e2eca19ce9abb04b86b5a81c44eed8,-0x76d38a7d3716e95b1f3baf5760b1989e86809d3c7577e3b14,0x86b59bbe3e91e2c7c7ca5a234fd7b0b09490e1f675a168d8,-0x72b4e5db803f2c9b05abf447f6cc664010d7b1ad705986a,0x46848d613ec4abe0330bf130b5f4ce6d1c3cafe47c15f0,-0x1dbb0df754d1c49c3f31eddf27f7a686cdf94503bac48,0x8073f9d8371ea864c0d38cd9907a67932fa7670f970,-0x143a74b06fcf1599fc39eeb93d598344dae9cda41b,0x19fc04cfe5c09bb224cb598c6d350be8f0e2be2c,-0xdd7d616bba5c3a1c433cffbe2ad83df722362,0x223c86e4bd1ed76a3f5de774d2beeb21a4c,-0xb1784636d9c0129e74caca5ea10bef7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 20 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 47 indices rho q22 m22 22 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 47 indices rho q22 m22 22 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r23 : List ℤ := raw_ints% [0xfa03063b7d2d2f44c016da27e3b24bf470ccc8ec00000,0x1584d42772e1ceab8c08c045601a20c4eab2a9a9740000,0xdeafea6118713043836ba7ad900e3fd8aa98bc0258000,0x59eee35aed5474439fe96a4f0d6ce5983c4b148253000,0x196e3a096e7b8b59fad71ae746b2cd2f706a3886dd600,0x559d6992e02ba04cfb6d6a8f2c9e7f4fe8d81b0aac00,0xde7831d7082757ece0d8d2fa8f6741cba3b114d4620,0x1c8b30509414372b7bcb486079e03afcf0fb4e59e90,0x2efcdef5850664a5a59476e936108e902de2923df0,0x3e96607870c01904da3d2a48254325efa8b47be48,0x43bffc63a2029ddaa563370f5c68f1adc9263312,0x3b9d64eebe613b775e35a6abed8cf79d4c8c369,0x2a79b677110222404ffee358d6eba113f26d3e,0x184c141f93427cd4f9d6e484e42e801d55c93,0xaffaea6d7faf74e2805921400c065598d4c,0x3d9edd0e077f6f4f9d612edc571866ab13,0x10194451a0a26df4cd2e481cdbd0a9f96,0x2f44f8cfc96100e3c38eff2e1060c95,0x56fd42ca53438dcbbb5124e2a253e,0x4b82627447f5a012db3de15bc04]
def m23 : List ℤ := raw_ints% [0x0,0x51c709acec6c11b8c09c2ed55a7b0675f8978fb08a000000000,-0x79fc1e2e1090b9692ac73c2d2461856f281c1fbc53b4d3f6b000,0x57810595df42c2cd101a516eea2da1a91c10fcebf88295a481400,-0x2830fa094238e75578181a0c7ecaa333817bb0f1a167ee2ca9a700,0xd4717fa5b15d6a244bca5923e51e16cb316c5ea280d33efee62740,-0x35c26c8007cd23a698dc8a63b36690dd19aaee00bc07ae368b89200,0xad6073aa2151e3fcb6793369c1d256a1680bf2830d8759c55b10510,-0x1c9429811a83c89ebf0bb3b3cd6ae393b691bdeada4f145823006c40,0x3ecc27065b050c6d52622ffc6dced6d453d663a28f2a6302bdbfc8a0,-0x7489fffafc515564f955564fcc3eae8e25103fa8e56c03560f80d340,0xb881c67597be23bd46aac3428da6d71d812ca65fcdc49d6696106234,-0xfb16e1da151b86c55218135018c528b9e885b28d8b31c92b1e4350d0,0x12756ca0728adcbd77f0a984df008bd60c0c79aaa5a48277cebc7a278,-0x12d70d16b41c5170c0048e5a167c0c954011feb9391dee43eb7bfb550,0x10bac783938d6471984dd49530647f7d9f7f65c9a6b185dca44e3a9a4,-0xcf179629044729ebeba8d4f18202b5f84fd0a9d1f92bad11e8d7a980,0x8ba738a277c0af5565fa0ff35b0b2c3d00df29c9dc2be35a377c1050,-0x5209a139d6ee6f08ff1a3724584e3db61446c483d0e7b69d647328c0,0x29ea594c88f89e8701aecc39030c91a69c9487f526c3dd664a00a829,-0x12944b98e2933f8fef95422d9c3ec95e08d75f39493dc16742794974,0x71e7aa9fb64029da99235dec5734b31edb17f9f4f805e1c912f37be,-0x258d42d29b1cbfe3c31757eedbf71c06dea587e0071f2e3a8c0c894,0xa96966d88fa27030c71dcf7b1167155fde8a88a6a32af874e81255,-0x288da990164922fe1be982f432b872f6deee1284080d70e7619490,0x82aba8b8e7d93bbe4e87d2946fc3ac738e091abbca9f32f33d688,-0x15e512af797fa424aa2b228fe515256d2f69fa075da9750758f50,0x302e8ce5a3836341a85e41ad3137bdeac75c8a0e972fbff69eb6,-0x559ab5e78babf70644a536971a2d2c90e885fca3f497bcbb868,0x78518092627f47f49457d561aeeb3df96da82c82bfd36a278c,-0x8270acdc5d635e7738e32add027c26e2a5148f49779c23f68,0x69ab7819b7476f1783d5f855f12eb7e247a157e9759e2d06,-0x3d6ee4d776a0d8b23060a44dd8ecb2476a9205fd7712290,0x1852c23f6de79248a5f81f8564b6d713528efbeee9cb98,-0x61e4ffff75084b933642e92a94e86b6ab06365a64590,0xe39fe30765203118670d0779e96d5ad20cb35d98ed,-0x10aecc6a620b90edbcf310116413bb54eb4773974,0x80318cfdef4c9836d1d26c5d1d8c5038f0e5ee,-0x119996afb23859159c4848fbbd53d5d22fd4,0x4f8941f311ab0d8615aec097d0ce31f1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 20 78 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 78 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 47 indices rho q23 m23 23 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 47 indices rho q23 m23 23 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x4b82627447f5a012db3de15bc04,-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r24 : List ℤ := raw_ints% [-0x22fc4625535764abe215baf55536b14c950b46831e00000,-0x30285b21dd10d2c49b59299b1e578c25e0404b45b9e0000,-0x1f21b8d43596a3719e4e90f57e5e0ea726d4ec5ca7c8000,-0xc90db0a9000ae6ae7fed7d8086090d91bd3726c17b8800,-0x38d19a5a6274f9c24eac470ae3a2748e278440650dfc00,-0xbf2a1a9c9e8daba385d3d0d0ef3996f286324f38c0f80,-0x1f065046400a8f5d2023e0dbb20e0cde9f10af0b1dfc0,-0x3fa4342aacd858b5f1c37c0e54f8d4a1ac705e018920,-0x68adcd26e224b19e4c0037b80f698fbde902e30de10,-0x8b4ec58f563f255316a73ee1af185fb97e21480da8,-0x96a716525e7fb5b3c67e7b80eceaf393339d809d4,-0x846c5b238da445271e449ea4d9d5c815d6311736,-0x5e3e29ca4cbb3d5cf842fec5cd7cba3b42723eb,-0x35d7853d2b2c776f5dd8002adccd633337fe32,-0x1856e2fcf27313c9d13dd9e6caba219e01645,-0x8827d4dbadd8ae4ab950f07788e23b04684,-0x2383246fdbb2b4c11b8febd6c58ab66b35,-0x6814bb4c628306d949b650bf9e637162,-0xbf2686c0d69b443e616590446b4a77,-0xa58d01f917f128c934c9f9da37ea]
def m24 : List ℤ := raw_ints% [0x0,-0x84e36fb9002f9ccc38fdcc1ab307ea7fb3f6497ee04000000000,0xc4e90a27111f781253b35aa37e935e3d4899a2ec21700b3173000,-0x8c4553e56b76956309c66598560a37c26c44d672ab3349d109f400,0x3ff5b1f3fff43110b54ea869993e6055b2c3c7b9279adda8ce2c100,-0x14f819f5b84e3bfd647c01a371113fb6795cd8cd0037f8f61ec260c0,0x54392b4fe7263a23279aa0d7b198697bd6659a446ae64a247dc40600,-0x10d58e0184e265197e5d7812f0ae886f029177899f4f9fe844ba61070,0x2c01bceb41e009bfd3892b5f01c994eacf2a3647884b27aa8849ce1c0,-0x5fccfc78d76496a03aa04810101c3722e16627479d8e1992ce64642e0,0xb00be3881178659c767bf58aa8bbb6803c9b9598251c5b0b3e88fccc0,-0x113d717d9392145ddebcddde49b3f8482da73e1940cceb1a0e7a829dac,0x17347b285240bf1f5578e2fb605570c99da5197e294314420dbce4f4b0,-0x1afa81e3c3ecdaa5c4a7e745901f3b8bb10a7e01d218e044ee87d7fb48,0x1b32a32fcc3ff2488065b1cf8e0343fd72baa74d7c6ca5789c0daa4a30,-0x17d60080abea613a45cbcde4d8f821b76fa25e453a25b9fcbf401652bc,0x122f596590c89fa6c86ca6e7747915aac349cd330de7d198040d01ee80,-0xc14cbe24a4b14d2e848c1113249f4a47a4d25f8ca5edec93f202696d0,0x6fc04f5572e7000cfa03cb3b96b95c276af9e69fe9e6acbdcbefbddc0,-0x382074877ac384a1a61dbca541c9eea61c248931d77a83c418d3643af,0x186ca7e8dcd672e7142703c77d602dd5f560a4c915e36787f3615f2ec,-0x92cbef46c437008cb86808219b556aa278c4281463b44d2561a636b2,0x2f5e3d62d9373b1189add9cffad20e4783e434da718e40ab8ff1644c,-0xd0c8f3055fcc8ec2b3c6ce4877e2b98623b6b57e3974b68e17cfde3,0x30bb0711f44b3c6f762e41bae44c818991ab9a7f5aa42e448ca16f0,-0x98bf4753995a8614d475bed20b1922a855676c6f533bc7427811f8,0x18d52939edd80f508fe4f3bdc12bcb44ade6f86dc286fbcc3bed30,-0x34dd16bc32a72e01876a949cf6c13fe0fd5ca58e54f69e3a0a85a,0x5a8c394383e0b6d2b72418cd62afa5e8423a69227ec1304ff858,-0x7a3677a63d38398ce71037b0eadb9ba0aa6ccb3446357077254,0x7ea8621e4defb2ade7dc843b87cda99d2f0e2add7c96866258,-0x6192eef24e86f3d05cd96446c2dcffd791d6c1f0cbfd12a0a,0x359e6fea4f218819d9ead4ef3c0dad862626d75901c484f0,-0x13ed1d3e35eb394daad332d33af1e0f4396b5069f5346c8,0x4aaaf4dc40cce81adfd8be3bea008e83f6334e49f3870,-0xa02514eab8c1e9bd9b70fcc59e20c59ccd38dc3524b,0xab5ebdfa0525289d84f7124a36ee22083d030f2ec,-0x4a2d1749285a056543137a0fc7c296f78376e82,0x90b62e9e411d09ed55286f6a50fc15a7e90c,-0x23a2a12e0057c1ca01d67ac55f8aefee7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 20 80 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 80 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 47 indices rho q24 m24 24 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 47 indices rho q24 m24 24 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0xa58d01f917f128c934c9f9da37ea,0x4b82627447f5a012db3de15bc04,-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r25 : List ℤ := raw_ints% [0x4cb43b68d6fe01054107082f685e0dbbcebc391dddb00000,0x6989be8d4f1f4cd495cd3807e63ba186df1fe1e8141b0000,0x44319ad3cc02a63179a511799d98a45402dae79816f74000,0x1b82efd58bfe9109b58d653b436d49b9941c0ac09491d400,0x7c5485bbdd8c468ef34a2f0a66e1878ea043570a8c10600,0x1a20e64cb182ae8edd0f81fc158a9025381dc25772e55c0,0x43cdd8cdfb26577807b25e1bead39288b509333a30cfe0,0x8afdb09f2d5b3f7df0128cf50cc61c98b9e48abd04c60,0xe471780544739946a6b4b149ae8499bdc07958971970,0x12fc4008b8250ea0efee9c87da703dcadc9573c2ce2c,0x1483632b6c237a7af3f6ce1b1fdefccdc50fb5773be,0x12037d9ed1b9ec896161babd921c83efe21e7081a0,0xcce71c4862b2681a8cf2f03bc02251d24569da7c,0x74edb9141e0416ddc9a821cc08f5f9c979e452d,0x34caaaa993c01af4376557c7d2f34364e5f62a,0x126e9cca717d463991c1465ec9b116da6c4c3,0x4ccdc78565599dff6c0a1f1013a81fe62f0,0xe0ba3797d845dc2d7502cef09a8fd3377,0x19bf88a6b8ee9db5f8cab04c2e83f5dc,0x16413dca42419a54fca6cbcee0c92d]
def m25 : List ℤ := raw_ints% [0x0,0xd7f1958ca04d5ecbdc9c6bab62ecdd0f8470376e2c68000000000,-0x13decabbb9084d7f5642dd21e85161f971b924ebc7e0c017d43b000,0xe0f42faf8cce60c68a0c0308864cf8e630d8495e5cb7eb569f8d400,-0x65d9aecb97d299909ea28c078f9a740c9ef1424329b83d5619761700,0x21250d4b5414f1609d36e508f8e80c2e67ca20c49a155b26f3d7ffb40,-0x8417ee4de86c991f50e7f79ef0345b1dbb057b0f5d1d83132b7293200,0x1a2fcd70e01203cc72f44bf46916ce5d3e15ea2c78068cc416d3aab610,-0x43ddf5e969edfa8ce91bea08833db733baf2b43ba1735b816918613040,0x926779cf3167e0ca270a958205ea362172164bbfbb48b505359a7eeaa0,-0x10a7651b65d09cc80f5e2da8623791535efbf1ee88ec91c435e1e39e740,0x19d48adaf0fc14b756d88819dcc95a030f6d0c39d1808ae94f074735d74,-0x226511ecd352dc89b8f87443f4e770881f19fbd381581a846b8cac67dd0,0x27888b1b84769025fcc861539959f8ee625f39310e2dc359a803fd229f8,-0x275f8872fcb7d0768b93cc75009249dac8aa12465fb9f507e9037aaea50,0x221003f2268437b8fa267d9bfa64725d483edbd96b4a00a1934cd4ac9e4,-0x19a16dc8025f33435184cb1dab65c9027bd7b6c348d1673552323ebb980,0x10c73290551835ca0dc4cdb283a32bd5491eaa5ecf82d83be2608f73750,-0x98c29c74bf787d0c4abc29974604b99d7c444501a9091d23d2f26084c0,0x4b6e1ba47fdb028dfaa4f13609e35d7dfcafa2115e3cfc6596b4dc8c39,-0x203aaa1b83f6686d1e2f180d8753ede87f97c9d7b90de4fca0e6f56eb4,0xbdea098601f4a029d8cbbb2ee6d5d4f929e913d80de2c698f0059f29e,-0x3bfbead84ca901f92f4d7ace5e08dfb7943286a5427f5d932f767d7d4,0x1025241e374e0e4c34de23405440f1a13f1c6ec280132a061d8d06525,-0x3ac941257906682f4e55b2194b7f7d292927e8d8f48ea0e69e328590,0xb33e155f28fcfa87f9d01252bc09cf97973321017486d552a6ed708,-0x1c4528fdf9c3e0e6e50a288356571cbce890383f727886e1497dc50,0x3a351f8a631c61e32f20f6488eff01ae2e1144914fcb1aeaff3d16,-0x60189cef275c22a03761c6d4a24cee36dbd7d6e953c0088f042e8,0x7c8379185c28cea2d2d0f3223c86a22b4854a8ac2f69d15cc24c,-0x7b500e30219d25941b7411a53bb90817a5ceb094c529ce8c9e8,0x5a4cb3eb2a2a46beb71a8279c1b353564f63e5924515058266,-0x2ee17352ad463ed5923de03014f317b558f8dbc3bb8e77b90,0x10582c3b1f5ebe8b0ec01d84e0cd7becaeef254156026b18,-0x38fe9b026f8d59a9c1d1878ac81f844abfd9deb9c36690,0x70b415bb4cce93856229ecadadddf91ce03f54975b3d,-0x6e0444df6f90e402e77c4a612c1264c6b4170aceb4,0x2ae89df8b88fd3c4c04e41b492c7a030bca8ebce,-0x4a573c2006033b8d5c23c4d035366cfb5e314,0xff6250f0529fb2448dde3de2d1c641881]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 20 82 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 82 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 47 indices rho q25 m25 25 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 47 indices rho q25 m25 25 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x16413dca42419a54fca6cbcee0c92d,-0xa58d01f917f128c934c9f9da37ea,0x4b82627447f5a012db3de15bc04,-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r26 : List ℤ := raw_ints% [-0xa4fae69dda69c96b2785998ebc30396733a5edd6d01180000,-0xe2e843511cf6c27a01cd2ba68607303919570e978dbf18000,-0x928da5962793afd59ca9d63700958053984858ea4f4f6a000,-0x3b18acb84cde7de6d33f591f87b10a45764e4eff541685a00,-0x10aeef83f01166539836045c93fc321040ae9e6318d6fdb00,-0x3810fede41fb70af3822c4b48f7097fc77795a2fa7ea8fe0,-0x916834d6ae45762a83c1e98e544a8323a84a61885486e70,-0x129e07212b857d37f4f57841db60745cfef641b91d0abb0,-0x1e93e72cdec85b141ef29a78cba88b0fdbc09799419da8,-0x28a10f15d82bfc2b1f97254315617734a94995f179cfe,-0x2bdce4fb8502cff30ed01dbfc4d2eb707054348ea70f,-0x267bd991078602ab76f41492880745191662f167bec,-0x1b5532c06c6156842ca6c0c335c0224f9fc764a6d1,-0xf94c73c6bfdf8b82055d551a319dd857dd038630,-0x706d03e9aaeabcad8ec8273c68ff5a7f840cad1,-0x27343caed4362c81647e146b3342dc6deb50ba,-0xa3224482d6fcdf5915083116537142aa61e7,-0x1dc9c8c9c4ac980d169594dc7c7911ccff6,-0x368487e974f5ac81cce9557d4896731d0,-0x2f091000079f33b94e4526c7f3f5e26]
def m26 : List ℤ := raw_ints% [0x0,-0x15ee89304847dba0b467e2ef680c0e73937365a1308290000000000,0x2016aaf9eab2d897fa6cca99e28d4576a0d8c434d44dfc853b9c3000,-0x168e983a744ac97fea9de36a83d95cd3cda4aa15da0da04b7594cb400,0xa24a4b9679119345ff5badb91efe305af5533d2b0d6a0129654d4d100,-0x346f2ef1c6f098bad396b135235d37db8450415d56243f5c5c7167ccc0,0xcf643f3966641a7358522cc50ceb1a0b9c969577c3fd23b68e28c7e600,-0x28c98a2fe8a50b0a18570858d8a984280ed36ae051929d9183d29cd3770,0x68d20fc5387cc81d3c0ca89f99dbf487260b9386d4ab3ec6bcda417fdc0,-0xe01eae5058ed43637fe5e2a03ece7d83fc2964eb90274b493b9e0f6c8e0,0x19417430694cb15c97f90aa0eb826d90b2cea4baf062c25059c1ac4c78c0,-0x26c8915cd110284a2ef8ce7a3255215c780d74786284742507ca4760806c,0x3319a17eeb42a4d6af1eaac4d6b3541b5c5212209056c2d5a040913edfb0,-0x3a141bb9733e9c8aab1fce040550bfdbea37032c40ecbf816e5e6c5abfc8,0x3927dc7e1bc4f086526e5bb5ebf0d890782bab20a897180a631e37730d30,-0x30d1e827f37dbc6612ceef4535cef89c3c223f3a0aa1afd3dc36af6af87c,0x243ccbb237cd80e52126bb9072c3a28a740a35ac370f706dcc1a254f5e80,-0x1760af7034b4d57b5595dd78ba76a70d53ba5d042396927f86c7e5554dd0,0xd1898263a66ef2307bbee937a73e3c364a9b9b4068fba30a6c54cff59c0,-0x65bc2e9a6513544e895f563ef01cae7a90ef3aa0ab25dbcbacc5017ed1f,0x2aaf531b2deab321e50d32dba503cf14fbf9c9ce00664901e6d2af8a3ac,-0xf6a006ab0c34633ee39a6246be062468b0faa55aa85a27fb2cc038ced2,0x4c4063a17822c1fa588bf004cadb1923d3cc9f567edf8f516e1544030c,-0x140d800c6487dbda7872b702a494eaa1ef130a13d0b8182ca6c250d693,0x47305a5cedb9bb255884af4e22d9e06195c75d2cc45f24813971c1df0,-0xd32078133ddb1df8cf94ae6f3271c38fe76caefc7e1b9c77e5e9e178,0x204d0cf7bc40d73f06f6b849fd8b12688ec79bb7644d33bc0132c830,-0x405067e1514060751700ea07589651d291c7002994acaf61a0a9afa,0x665057062a7568e7175a563e2b022b92b2e02f342e07b1bbb219d8,-0x7f3a6d0adfba5fd6ada4f168752ab1fa491b5fd4656684b381d94,0x785caadb78087ee44a4ab8c0a0b926c527601f64774bcb8673d8,-0x53be9eb431bf057b34c138bf0065ba7817ce5865a4ae01af5aa,0x290e7f2730be9d62e628fd436783a98905a13fad370b1ae3f0,-0xd6c014f5e4d49605476358893bfdd3c7c88d35979af7a948,0x2b889d4c2a9bd5cd4b096a25a547b641cebfca4938ce770,-0x4f55f902e5711d1fe40b39278a0962a444c18fa8ab37b,0x469f94767f037e71bf0665dd8c9c290189fd2ef33ac,-0x18d0862c05bb5650b3ee8a3d6d84040c72fb9eba2,0x262d6144da5f27773ba59420840202171ee3cc,-0x725bc8c175f784a8b05e4d4fbe4bfe8dd7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 20 84 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 84 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 47 indices rho q26 m26 26 259520542755628986703872000 26=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 47 indices rho q26 m26 26 259520542755628986703872000 26 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_26
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<27) : intPolyRF (mz e)=rfPoly (C (259520542755628986703872000:ℚ))*rfX^26*(1-rfX)^20*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V7C27
