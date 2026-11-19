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
namespace CatalanCore.Li2.NVMod.FamilySource.U6C26
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,6,26,size⟩
def bases : List ℕ := [1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
def num : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x769c8c0f02d204780000,0xa694919187ca8a178000,0x6e1b1e9f810e0b1c2000,0x2d8d1df5d065a3ca4200,0xd3b086d9f76d347cb00,0x2de530a78d25eddd960,0x7b531557f56d0912f0,0x106e7799abd39c83d0,0x1c3aa7eea1d234728,0x27799766356cd8e6,0x2d2f337749ae907,0x2a6a6370808492,0x209a009b49ed5,0x1468bab536dc,0xa4e4a272b6,0x4223ca8f4,0x1494f792,0x4ca23e,0xc8c3,0x14a,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x1,-0x5,0x21,-0x4d,0x743,-0x15c9,0x18f65,-0x54df1,0xbec9,-0xe28eb,0xb24bf,-0x17e107,0x32f12,-0x192c265,0x602919,-0xa0447f,0xb194f]
def rhoDenominators : List ℤ := raw_ints% [0x7ce131700,0x1e0bd60,0x2f7b0,0xd68,0x270,0x104,0x3c,0xd2,0x80,0x288,0x32a,0x37,0x294,0x1ad,0x3e9,0xc3,0xc300,0x8a20,0x45ed0,0x33198]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 27
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
def r0 : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x1cd0beabddfdb33b2335e103a000,-0x34c5ba56cb1e8533df95f5b3b2800,0x2ec4d58d2b643bea135e2cc8f89400,-0x1ab731cbb51c59265299f81a2bc4f00,0xb0dbacc7aced7ebc869c9c22c998e40,-0x3878455ab09e1b7cccbad55dee6b7340,0xe79d1408299e3d6140ab3c386b429950,-0x30f6e737a0571e165a6028bfd7f04ad70,0x8b3b5a8f2337c5eda7480eb81fe6cb630,-0x15196601fb7bcc6fcf771925481bf16b70,0x2c180164b69e89e3e7fc1813747d814124,-0x501514946c2d36b947a1b07e7c927bd8ec,0x7f347f46dd78675d8a1507633a8aa5aa4c,-0xb193ed16777775c81a0f719b3eb2629b64,0xdaa896b05cb7d3cb9c390c4db936526fa0,-0xee1a352928ed6486101e2e50f1cab03d40,0xe5ac84d4a83a4f5c4fbef4e58aeeed1610,-0xc46b190e4a611061921a7aa552e17ea728,0x94f0578954c0d15794926eacb0a1bb1d39,-0x64112634981e30b5b88e4dc332f797fc8b,0x3b7bc1970882e6f5ba8ca67bd996726f63,-0x1f36863e9c42f048aa098158e11478e7e9,0xe69951b344dc66e91b0cb0667715d7264,-0x5d4ee8b1385d9314f550205f05e81deac,0x20e94be6d2e7d932b3a537645b79e091c,-0xa0d4464da45053cd5e2e94e2cbe5c664,0x2a2eb1af2834baaef3ff1ff0d926d9a2,-0x967193703acfc3585a877d6061b19a6,0x1c21692d81db5374c6bcaf6f9d91d46,-0x456e87170712d955896dd8bb6f5812,0x8a5e708f44f4ba546822421a67404,-0xd8600b3e15756525866e43087bac,0xff4e74fe3886865d38d6fafdd2c,-0xd6e9dc5480492f59169857a9fc,0x768439b54d63a0d0779fbfc89,-0x2526ede6f7b7f30948db49bb,0x50b134e2ea1cb2173809e3,-0x26740545e7202c272289,0x3a9b33ec9850a080,-0x191df1ae8a6bb280,0x85f508f83793b80,-0x217d423e0de4ee0,0x5e8ed927aec2a0,-0xa81a659be15a0,0x8d8f7dfc87e0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 20 36 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 36 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 46 indices rho q0 m0 0 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 46 indices rho q0 m0 0 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x2ed335d748bc434019378da5e4000,0x54913d1eb3e20501a22e8223cae000,-0x49e2cd7adec11ad5f2d1ec7adab3400,0x29983e52fafd2a0fc49b2cf60bbb3100,-0x10f47bd5a594b02af6fc05e9e80ba11c0,0x554e0a34e5b0771cc282deb71506f8040,-0x158722454eb843c2b24100dc8954dcb2b0,0x47a865cb461de7631cef11e85468590410,-0xc86e06a694ac0b1c68633951106ff26fd0,0x1ddcf71e20bdb22ad30d1a001a89d0511f0,-0x3d54e354ff26f4b72311db0c3c3a75d21dc,0x6d69268140bc54a5fd24416bcf44fb66054,-0xaa9c6fbc1713ceb9c20dfcec229136da1b4,0xe9ad97ba8b47902ced495e0c17db9df39fc,-0x11a2176f4085eb06332a940417989ca2c860,0x12d07b041178a25603c51b3a3093c2385de0,-0x11c5160703b78f945b4c7454d43a5f7ed770,0xede43ac363805f77f271a2d24a53d189a10,-0xb055a4ccee298f803cca983213255147987,0x73b4211bb7f6ca5e5eddd9255e9aff37bc5,-0x431a0cf0e9a6cae5d9ceeb69a3bbe61819d,0x2250419ce1ea96398141d3fd1e756e2b60f,-0xf6bced1e54f2a02749297978f4c2f5829c,0x6109cfeb92c27f2113006508da1e62b354,-0x21370e85083427e104d36e8d353d1093e4,0x9d3cb90e30faa072840836ea9c3a36a4c,-0x27deca19d6d31fcb97977c22a1d3a4b7e,0x8927eb629453e9d1324d8d8c16b0629a,-0x18ab8e89a45c773dc192d9bec571af9a,0x3a6369487a01df7e6fca0760173607e,-0x6f2792b0f568615403a1a683bf077c,0xa5459db077e772b48900ecee0f8b4,-0xb858c46846b95b456e4377180bd4,0x919b4c0a6d324d9be197c1e19dc,-0x4a99685623f2045338681344f7,0x156ded5ba4e36d45d47d21d55,-0x29d002414b9d775cf5a8f5d,0x11649815b53e38ae0840f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 20 37 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 37 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 46 indices rho q1 m1 1 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 46 indices rho q1 m1 1 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x4c17377dd631ed4828fa462d928000,-0x8790e7b17da4f1bf7f417cf7d371000,0x74ceb44c598725c561b6fcc7f17ca400,-0x40d415da506e78da287d45d14e228b300,0x1a0b15a7ec099f56f6ef50110d2e97d640,-0x81166f207064becc5020e367daabf97bc0,0x2014f312f18f690441e296840403f9593d0,-0x691f3852f13ba12ef8771cc76425d337070,0x12151d3e1726e748991680141e7c57332130,-0x2a65bcec1deee9c0c21b43e78e6f48308010,0x559935b7951bdb76c29e72b26f8efb872a44,-0x9609397079f2a6c7496debcdf4bcb59a5d0c,0xe5c0365b2419bbabb54143ce6fcff293282c,-0x134d5909f63184e1d2cc1f31443af05b199a4,0x16db65e4bc4ce5c5cf97d8e6556c9db5d7fa0,-0x17e7547af93af63712203f111149b771d2f60,0x161c97fece87afcd019c1270039dd7c274570,-0x121b077b5bbe00d2feda54d42cb2b2af68c50,0xd1f4ae146a6529f83ff07f2af0db7ed9c3c1,-0x8692e3558c13e02c41f66ee1f55d8d84dd53,0x4c287ae15a9eb8116ad620a0b95ce93ee31b,-0x25f584b7b1cb35a46b5af331c1dc352ccc99,0x109b466f0883adafff91edf620944a695284,-0x6593ff4eea3ea1d6a50b8614638b077c98c,0x21be578d60d2753341da2330236469da63c,-0x9abf47d789c68120167ad2bdeff82acb94,0x25ef2c77565607bdde1e8ff8b6367e5292,-0x7ddb803c14b24220c9b168b48969a3316,0x15c5d409a8853679bf59c3b6b79bdc456,-0x31665435845a67230878da576e3ac752,0x59cceee3ab48ef0d5a7ee3a244b77a4,-0x7ee391259f16e8badab1e6ca69f8ec,0x85b3adf2ea0e06f743c8863cb8e6c,-0x62ffe5f235630c8bc241eee058a4,0x2f11a02f4f2a454efa8f2f1b0d1,-0xc5fbc276fff2412ad8b2f0a43,0x15a9b2727383d21c6c40cbdb,-0x7dcf4dcb1230ef7f48919]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 20 38 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 38 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 46 indices rho q2 m2 2 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 46 indices rho q2 m2 2 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x7ba5ba2c7c1121954296b20a0e10000,0xd9651d55cbc1e1dc3fd6a7e710db7000,-0xb8ca524d194aaacb8e48b85f51bfc2400,0x6524fe19443453acaa54015fd185f93500,-0x280ee10a8583a0945b12e6f6eaff4e7e9c0,0xc3ad3946c0aea7d214c18480367ab222c40,-0x2fe864f9072082b28a4e7b99dc8a864b55b0,0x9a94b7301eb3e097f247a0ab9a845f8afe10,-0x1a2c34502eb0a91e49f35710476ea6c71dfd0,0x3c600404891d3adaa42031b511c02557212f0,-0x77ddf58b56c414568a09fe1de59bf6cbea59c,0xce7fbcb28c96490c707152ff28bf417a48694,-0x1369df9c58bdb4ebe1c6e20c86239ff5bcc7f4,0x199e6c2338e6d1bb8a25222263c124fb5cb9bc,-0x1dc360a1343a5d22c26d355fbd913c17ce9860,0x1e841a06965c45fbdd2b5c0e491609196a8920,-0x1ba7850f8df3554c19de0125655e648a762c30,0x162a5f7f0fc45203ed9fe64f24a0675528b990,-0xfb61521530f705344373c1c4065d943fabdf7,0x9d6d53aaf982e8d56fc4283305cc8ab88ded5,-0x56f41ca600846e9b3d07e72bfbc21c13becad,0x2a4002427ac6e9c395cd452fc18b7a6a8fd7f,-0x11fed82e35a7bd0786c960420d36b510c4c5c,0x6b027ce09b87efa7de639c17ba7c0c8aa214,-0x22806bb573eb0eefdeff7fca76aeb3b186a4,0x99483d99f407c1e3cdd17aae349263d120c,-0x24530f1201d734cc68e720af89a8c34155e,0x74386a34242d54e10c6dd4004adc06f6ba,-0x13556c82e3bec1cd12a3b03ae56b9336ba,0x2a0a2f3cf51e224f03ac2efbc9235dd5e,-0x48f1ee74379fec239d48c15d8ae1cd3c,0x61e64b4e6e730c81a7b85622f899034,-0x61610d382bb69b858601f333a1cfd4,0x4388a0b08e2ae3a262a502c3b541c,-0x1dc37c4d9593952c87640ef81067,0x726d9db82b76d5d2b4ee350065,-0xb389fa4b7d816d55fd32136d,0x38d8c20f8f2cf5bff3517f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 20 39 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 39 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 46 indices rho q3 m3 3 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 46 indices rho q3 m3 3 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,0xc8ed4e88499bd6928c34e15056da0000,-0x15cbc6138d075321dd25fefe346de8b000,0x1248a0a89759023501d74dd77106126c400,-0x9df720c6391063d86f39b27b48fbed44b00,0x3db2c967e1eb0417cb7116dc548469f05240,-0x1291dc6836235282bf72ff0c4a781de6e6fc0,0x47af66374bf2647de3a0d705d51fd10c898d0,-0xe3d7d45078e91e83e5d89083000b043869970,0x25fbc80525d9a4f665126d4eb98192c6171230,-0x563b79ffc1ebb9d0719794bdde86cb61972710,0xa86870b231b1a0586dd6f8698cb9b6dbf84884,-0x11d3befe180e48547f59b356c24f0525c8955cc,0x1a59569a8c015c0dae2ceaabfa783466fd382ec,-0x2225271c32771ddc9c404e0150c979409cb63e4,0x26ede1ec0f6dba167f495ba5902efc131725fa0,-0x272463e1d5c37b236ebe4092ffedc92807123e0,0x22c258343d2761aee7466b22152215ad2d889f0,-0x1b47271b35b533a1de8986ae0d8f8fdf0addcd0,0x12e9f20a0f9329b54b5ba478532864c85055bd1,-0xb9348ca25562634c755241c9884f1b5af73303,0x63dc43f2a231b2c293e6d8ad4abf7b1e3f6b4b,-0x2f4f10cc3388d9de0ad0e709d52690ebfe43a9,0x139ed1f1a9f215e34effce513b6478d9f8d6c4,-0x716f5ece646946b992e145abfad32b363994c,0x237fb25051a92eeba788bdf151144d32cfefc,-0x98c9ab5251b35d6e3627ffb5fb2213ebc9d4,0x23001b854da6db880d71f8447198a66f55b2,-0x6bfad71e306c9f9731fe2a96f95a7b17976,0x11451433b2540d8b7096740bbddb4d09eb6,-0x23fa7e906726856e5c0141fdec9217ab72,0x3b905cf222a89be9547764bb6b3c427e4,-0x4be34b262bd661ad9b75ef5d293a602c,0x4734eb84ecb42e241164ed482cbccac,-0x2e36068061eddbaeb8cd6f541f7c64,0x12dbbf5d919488f6eb731cd9cede1,-0x4230383c2f67e0b5195b87358f3,0x5cfa217746d83c4467d35160b,-0x19ac3ccde64f46f705be629]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 20 40 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 40 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 46 indices rho q4 m4 4 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 46 indices rho q4 m4 4 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x146819f9d779d3cae23d5ee228d2240000,0x22f9db969411b4845d47ac653c11830b000,-0x1cf6d439abce8c81c31ab6531d9135e5a400,0xf6f48870e0dd51dcd1e0ef81467ddad59500,-0x5f28011429b1cbac7ff39888efd7a3e1d15c0,0x1c3e4dcb3d117f07172a9a09a26d54432ac040,-0x6b7a1e1dece0a739d9bc5f32bd355fbb0940b0,0x1509a6762ba6c20a5775f0cd726761369e59310,-0x3744dea045003b3aacb5761d40b33394db050d0,0x7b868d1a993c1a8d312cb7a1d38515af86c85f0,-0xed5f9a9a14497ab56a65046ed1de979f7ba935c,0x18b62c7ef288d8f23045af035075a7a999c1cfd4,-0x23e63004608eaeed71b39303faaf2faeb5907734,0x2db24ca5f512547e5e76d0b1b3e726687b14c57c,-0x3324451ee79cd24a53e8ea6adfb2a72debc59860,0x3270b7ea52b99a7b1cd5bd7202d34e36eb21ee20,-0x2be749c5b7360efd58caedee35c25b0a2ad8da30,0x21bdf46988f0665aa7ca749596f8e749aae22d90,-0x16e426c75da880d1603a2c92a2ed59b466d980e7,0xdb186e6cf16ef72bb4f8baed903b6064c613ba5,-0x7357298c8390fdb1694318f29ebfd4d1964fcfd,0x3548f97d400e6f65afbdddd30e96174c88291ef,-0x15853de69eb6d2367d775d619cd61c7a1e84c1c,0x78fa89b9847e5b4c0039b067af534c5d2d1f54,-0x24bfbd3001f83c8aaffdc2308636aea609cce4,0x993ab858dfbf93537bfec747089479c7bfacc,-0x21edfa584c0e29e96e423bd8d9b1bf54e703e,0x64ebb148c6ed8a86da9062a6933e5473875a,-0xf83d2ed815e1555c84ab41226234c35635a,0x1ef56fe0526639a1919306b131823ef463e,-0x30e1c761a3d512d49cd1ce2964b6b530fc,0x3b16a35d484eb8730510decd6701b8c74,-0x3443b30d81c03f3157fc89ddd70f5e14,0x1fb61f6051db6c9e7918090ec3902dc,-0xbf86c2d0eae4971e8fd34234f0657,0x264f836ebc82aa7ba5ec28542635,-0x3022e17779be46d306b8da37bd,0xb96a473006735153775c5ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 20 41 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 41 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 46 indices rho q5 m5 5 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 46 indices rho q5 m5 5 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x21292a35fe25f829afa3ba2f82557a80000,-0x3825070253e3d651edd1fc113e58c0e43000,0x2dea03b36ba3d6800f418e35b1bfcf1520400,-0x18275e42cf36dc4e20f19ea68f8490c7101b00,0x92f37cf42b795df44b94c526a24b0439a33640,-0x2b06d978327f72cc582bb26de0982bb116bebc0,0xa17491dd67389b6ec8426133a3900a8725e85d0,-0x1f2693628e025d1a0c6c8bb21b841e7ef7a8b870,0x50a0f8e49b2c336b3d63bb472f8a4f3d4ee72530,-0xb1758168fc2783691cd690ca7470843b0cd5f810,0x14fa63bb57ec2d20c4e80fed692487f1d093b28c4,-0x225fc7e7d0a8d78c1d12b4c7378b76d24837d028c,0x3118644b760081bd41d820b0da1950e5087cdc1ac,-0x3d673ae3f156bd4b6fec9ae0a9f3818b0245bf224,0x4379a6f91f5718468d89e46a698637eb99c5f9fa0,-0x414bf6280d23b64f775c9b033c6789b6259ea55e0,0x37b86ad419506d26b39c737091f7a26917f04eef0,-0x29f2c52bd4056efc135a29ec00ac788de56a1afd0,0x1bd9bbcbce746231033eeb5f26ab1400760f80061,-0x104992d95f4e10ede20f026902009ea77cd30f3b3,0x85f7d9d177f43bcdfd99fa8a2bbdec74bbf7167b,-0x3c5c9bf37426b4a79ea9ac5c906d1a0ca122edb9,0x17be3f15fa85f931e6fb4a31b555a709d2d36504,-0x81caa0dd1625e435fc1c065d9524851195bc00c,0x264559bda25d24678adab31dd59f75ec17c04bc,-0x9a9724f5b5841f543ab5c927c529eedc550114,0x2115f81dc769498466305af2e6a192b44ce1d2,-0x5ede07fa33b395a42c34cce1ce9a9b0f1efd6,0xe040a8c0878f3ba36dfef50eab8e6bb59d16,-0x1ac76d996668d0d98a003dded42e7617d392,0x284f1475032290b30a80256c20d759c5224,-0x2e342d90261b063d5eae2ba1617a08b0ec,0x267f4350368977d550d60ccd031c6276c,-0x15d1bd23435dbb5ccb55230000c396a4,0x79c52b0ef72a7bc0144b0a48ad6771,-0x162fd1476c7fe291e5e09682f2ca3,0x18e9dda28fd0b4d51cce992c13b,-0x53a77ace2d543c0436e64439]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 20 42 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 42 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 46 indices rho q6 m6 6 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 46 indices rho q6 m6 6 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0x769c8c0f02d204780000,-0xa694919187ca8a178000,-0x6e1b1e9f810e0b1c2000,-0x2d8d1df5d065a3ca4200,-0xd3b086d9f76d347cb00,-0x2de530a78d25eddd960,-0x7b531557f56d0912f0,-0x106e7799abd39c83d0,-0x1c3aa7eea1d1b5e28,-0x2779976635461666,-0x2d2f3377447bef7,-0x2a6a637018f172,-0x209a00960f6fd,-0x1468ba86e7b4,-0xa4e490611d,-0x42237a3da,-0x1493faab,-0x4c7fca,-0xc5ac,-0x120]
def m7 : List ℤ := raw_ints% [0x0,-0x35e2e497bcfdb343bd6a0e8d33cae7100000,0x5a279ecb177146cd113557bdec36701d6b000,-0x48d4afacf54dfc52434cc166ca383e52446400,0x25d5d0dd60c50ed9ea7a7edacf8c988900ba500,-0xe33bb2e2ec24a0c76047da30b277fa3973311c0,0x41a7723c5a9c3aa4264822240935888ed64d2440,-0xf302eaeda17aba0ba763eda21d2b7089ebc90bb0,0x2e3a78a2fa8be2e63b8544445d96b70e52dbb9410,-0x75ec969a8377e97d6833ade2e33cf4698789465d0,0xffaa939ca2b9c2a7a7a3272d5cd51e0cf0aaa1cf0,-0x1dc1a7b6b032e91fc06956d07863779505e056991c,0x2ffa8fe6104cc3dcef1a33b04899d0c34bbd736d14,-0x43641f9ad0b4f9fa30f117fbfc4bbc2e3e2e00da74,0x52d6494b6716a23e962399d0f2b5fdb435e6be4d3c,-0x59671e9b0108ef07728283c09eafd50d1552fa5860,0x54e88e91b084ab8b1ea693b5b791d3a8e975d01220,-0x470d5a63e4181930b30c2036f96f3cdafd946ac530,0x346895887b2e2e5c169f04ba9493e06604a9f7f690,-0x220f10977bef30ba9d3842ebca83844630227979d7,0x1379e1a983591abde83cc1d4565cfe019b812b6175,-0x9c75c55cece0211f155969410210a49b68f0b464d,0x44c37ded8c83454578ec2f7a52059523f1a83215f,-0x1a588426add4ebd3b23afbcce578979c9408bd3dc,0x8c0e311fc1856107bd96b3830a29da8d903ade94,-0x2816ab805d1ec32eac2aa6741832c4cf127fa124,0x9cdef6ddd2c3df7cbe57a94acbea55c4aadd98c,-0x2072be61cdecbdb9d00f2e6e66905060347071e,0x59ad0af627abbcfb9800d5fa3a612424071dfa,-0xcbabe4f5111991c6302d1ca9ee14c40bb4dfa,0x1747cf530adede295e898838a74329e3fa11e,-0x21648c61aed06a047b05a26989d707b03cbc,0x24466845a7c22218c5fdcb53451bed16bb4,-0x1c736cc533340b18258319ccca90f77d54,0xf0cc8ee4f60c7d551bee8df5403e329c,-0x4d889069452a80be6b39170169c6247,0xcdace2545d19de1c1ac065f4b2905,-0xce3db321584df570c7b0cb3e10d,0x25b98fc5e75e8f2793364515f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 20 44 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 44 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 46 indices rho q7 m7 7 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 46 indices rho q7 m7 7 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x120,0x1]
def r8 : List ℤ := raw_ints% [0x85701d90e32c4507000000,0xbaf08737a9c10955f80000,0x7b37ede1dfa801f58c8000,0x32d0a695eaf14a386e2000,0xeb4dc5d5d95480cfa1e00,0x32ce2635a4d33e64cc100,0x87df24f87b484b5774a0,0x1200f3778958a30b3710,0x1ebb1572db4f4138930,0x2aa51fd411fd58a498,0x305d806fcf900117a,0x2ce4bca71c4d6549,0x22069a77b19be2e,0x14ec32027cc083,0xa5187c3a250c,0x4019fadb163,0x13055ee066,0x41a28b15,0x955b96,0xad94]
def m8 : List ℤ := raw_ints% [0x0,0x5790b376931c434e13cc57a57429b77a00000,-0x90d0465b71b89381a102dda998a02b9a633000,0x7399faaaf93fdfae61dca3f35255967e961c400,-0x3b52c0d7494088b799e88738a78a49cf2e88cb00,0x15fd2e74977b5c815fcc521384e9ae6e47d07fa40,-0x64571a49e84e474cceafcdad9b28222763b27c7c0,0x16e7570bb3377c42e6159b589ee164a07ebe5022d0,-0x44c1602b4693478c1a773f5a01806958461ae19f70,0xace721367596ef0a488917ece0f344784114daf030,-0x1715f20676d6bb745d9c8e4cc5b702bc135e1faa110,0x2a56aef84717ec2c92fec9c366b380442c87591a504,-0x433190e63f68a847f71e420ee696052dd4711397b4c,0x5cd7a448cc2c4aaa21aac9ffc6798c15ae4d5f96c6c,-0x70309a6693d89246f910df08cb4252ea785db8c6464,0x76f32ec53faf224b8c0e93677d3d4b19bf874905fa0,-0x6ee5c1393dd96f0d6a03ba5c0f96e05174a5d8eede0,0x5b05eae5fd9fccf0f22ba0ebfbb54f63e9dadf6f5f0,-0x41cb8d3e3749c0e4aa6040ec7982372b469acaad4d0,0x29dc95b60003f3c38b7124d0babf176436b0cee73f1,-0x1769345157ad0dfdd67dd0032f56b65c795b30c8763,0xb7b670a00dd2720f900c12bb99cf1e83a1e4944cab,-0x4ec463e48f50a8688fad2cad20cf759d78192e10c9,0x1d65d5b940b56883fad5b2145f2d6dec9bc7964f44,-0x97fd22aca703b35283a9e4589a0b24265e8103ecc,0x2a3b50b07b3b62d4ef93706e1b5432cd7452aaa7c,-0xa016499eb15ebe002c6ab197ba782f7dc00db054,0x20001c137cfacc03142573830470191936ed7bf2,-0x553a7654148b0ccd3c5f136e87ab8abdb738436,0xb9f04e0bab8984c6dea1af162a99b5fb9fa976,-0x14565bcc02ef994e04d9e5a17a03f152b405b2,0x1bc90f6e8f7b98569a07481eccc7cbcea5864,-0x1c96dd1310949c001fc0d3296ba98305f3ac,0x151796fecedbc41f8e41414dff3d331e02c,-0xa6784e1bc6e846225f92bde5904e4b6e4,0x316e8291a254f1620f789d12dd2e8001,-0x7734f1992b624931d0665d6a4beb53,0x6aab9112405f27d05691cf112f6b,-0x11013785712f058cf2ffcdb349]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 20 46 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 46 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 46 indices rho q8 m8 8 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 46 indices rho q8 m8 8 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0xad94,-0x120,0x1]
def r9 : List ℤ := raw_ints% [-0x506c5d271d958e6fad600000,-0x706d4425f0033424b0160000,-0x49ed0ad846c3589717ea8000,-0x1e677ae68e11827069fba800,-0x8c5ba2c5e388c2f71423c00,-0x1e331c9b8566e72b72d6d80,-0x50718f116d675e44be61c0,-0xa9c478b057a0ed0384fa0,-0x1203e62de0bb10c6ff410,-0x18d84c446b7c7d6d49c8,-0x1bf8b3141ca1bafce74,-0x19bc92ad86eae33cee,-0x134c9fa6d8f745edb,-0xbb62910ebbca502,-0x5ae1a3f2f28eb5,-0x2286e4d046c04,-0x9f2f1bf1905,-0x20f092d172,-0x467d4ca7,-0x4a6532]
def m9 : List ℤ := raw_ints% [0x0,-0x8e4b23a0af0ded5ee02c0e6cdcc3ca26400000,0xe8af4713d0f6b8688387b1c45cbc52516a7b000,-0xb79b1d19ab9b8560f42d0d609d9afeec9cd42400,0x5d1a6c5230caab1333560696153287736d7277500,-0x221696bb5d46b957bf4de6c06eaf8a39283ef50dc0,0x999779a7ae7ab7f0c6ab0392b2dc6536b46f3c0840,-0x229a62b58f2d48700e7c55923650660ad0b4d6846b0,0x667b43d682ffce0d41ae2d36222c042af485d039510,-0xfe23780c901142f46df871b185a112649cb12191ad0,0x2171dc73af70d86426b368aac400c015e3241cd9f3f0,-0x3c6c8bbcde01f61223ffe91b2cadefab1aef24686adc,0x5e6a72ad1ed3f6c961c3c9a7ecfa87bebbb318e4de54,-0x805d3b74d7256ccef60abc040a3bb60b8b2361baf1b4,0x988725ae98b37a2d97ed71521c00597068d58953d0fc,-0x9ee90c96f19432dd5fb79353699610a93c235e501860,0x917812b2a6136e0fc53b8473ed68404329e4bea79220,-0x75239222a524015072ba6d0e1285a34c82e432819430,0x52feaf513a7c8e1855a5394b3d1a88b098776bd06390,-0x33b5100c1fb53d7c7bbfa8a228538af60b7358952dc7,0x1c49026a9f635f031fd754f5ae05d1da3d86fe0de445,-0xd8d9e2f9fbb8fa77c6715b77252f7d206b680e6e49d,0x5ab69803327fd7e5f6effd9d1f0a6411f3d513787cf,-0x20fbc733b5fd0f25d84d78eddbb1e949db50c88479c,0xa5da7fc38b8a44e8c4aff5db79feeebfa2f8d149d4,-0x2cbc91d9feb0918974d0a6a32ccadea100864da164,0xa4453ee145e6500eebaff785bd42816e6ab1c0c4c,-0x1fbada25882c4dfea4a678f72bdde351b8f75a3fe,0x516d549e3b39df99388cfa161d7ce62dd2016e9a,-0xaa99a8931c38846190cb114a769f63af752529a,0x11d965d29d156a9f5940233651a8617483599fe,-0x173798ac437a5d4132fc7bb0d2f6eaafdef47c,0x169d372ff3d1e57f4e3852592aa4ddc625af4,-0xfaec09da72ca8f4d3b6683faae3a9aec494,0x7353552282eefe794619eec08c8f16b25c,-0x1f8d4dfb5bf0f6b06a9375a5b3f252937,0x451be12d9a0da4232d7e58cafa568d5,-0x3726a4b44ea4e0382ca28cf9f8f5d,0x7a961a9249e28dbdfc07ca63cf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 20 48 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 48 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 46 indices rho q9 m9 9 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 46 indices rho q9 m9 9 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x4a6532,0xad94,-0x120,0x1]
def r10 : List ℤ := raw_ints% [0x2278236a2c17c0b37837700000,0x30185edd5cfbf5ca6590b70000,0x1f8eefca56471dc11cd4084000,0xcf2df3097cbd8cd58c5a06400,0x3b9e3d4a46f9a96e0db20fe00,0xcca08d09e84d7875729518c0,0x21f3923f5a7a1820a270f560,0x475fbce1d3a91ebe9f46ce0,0x78a58ba006195c5d4e5e30,0xa58820f284ad006e126dc,0xb93fc8ebab20c2c9fc96,0xa93f9cf462ae3ebb010,0x7dd9e225c5269fd1ac,0x4b98d4c12422d241d,0x24351c4cfbdb908a,0xd8a6358216b4f3,0x3d2c40df48880,0xc523f270d17,0x19672753a4,0x196925cd]
def m10 : List ℤ := raw_ints% [0x0,0xe73a19e51c76a1ba2c479770e6be287e2800000,-0x175fddfeafb53c546006f3fd14a1197ad83903000,0x123cbf4847a1771c93e835b202e3c38a5cac078400,-0x9241191ed6ab707c41c65af1269737a8ee594ffb00,0x34e90cbaa72684ecc4560db4593ca0417f15b657e40,-0xeb77532e6dbe9a7fd3036e8a4ab1d328ad7fc4de3c0,0x345feef72577de39c0d856badbe8a3bcdc27d9430fd0,-0x9913b7a7ad54c727d5c6752223436c4610b280ab5670,0x17672753647d52999b0be7fb67b6d5002065ac8ef0b30,-0x30955a3eb46cf8dd71b390dffd3420ee404d47e477a10,0x567e13bcd3ec73c487fb781e82147609b5a4cbe7e4544,-0x85195ff0c489090475ceacea74dd716bc10237668800c,0xb21a35c1e8e7172b4478cdf918b57e083accbfb1e432c,-0xd027484838c22d18cebea692781478cb5284c8fd17aa4,0xd5264dcedd86242226320af5d555dfa496f737f281fa0,-0xbfa167daca05bf71cd1fae50033c91ce656f8eff8dde0,0x976c3631a24e547051bf20c6c25fbd62321a6dd5894f0,-0x692e4f9a1ec7f5547417554a8288520b13669e94ff1d0,0x402deb58f2e5d546cf49cec55f4df716354346fa44881,-0x2258a396acbcf31f3aa75f6a151d404fbda98ce226613,0x1014aa7a8973e4c90594554c7b5ad991ea0ea55b595db,-0x69060fb6d391e6172c582da676aa5da832a5a55c34d9,0x253492a82ee57ec0bf162e734bd4465a180396abfd84,-0xb5f6a335923f5202bfb4774b5826b56ceb69f3d998c,0x2fa59dfee54e2a412911e2d25f6436f68c8b660bc3c,-0xa9780bf54951df3abd40e907a9ad6fb3bfd82e6394,0x1fa099e8f0dd6d9ad568877bbb480546c48036c812,-0x4e310398b0394f3faf8709aa944b35877fe535e96,0x9d48bd4ddfb58d6b51215ff24e39cdd2a69a7bd6,-0xfbc5c62fdcf2642805907f650f2136ae75299d2,0x137a6bde7be7bebb5e00ed43ffd6266c08de2a4,-0x11f31317375dd05e3760905c7aa7dc90127a6c,0xbb148af6b7c81b6756017908dd3ee3d90cec,-0x500c37fc6e2354e5fe61a752f1a65da4324,0x1428ff9d329b98fe7cabe09e52be9dc991,-0x2812989a0032dc5b8ec5f2d797adc503,0x1c80ed6ee8f39eb1128ab5733b109b,-0x373574682a1908d86879be54359]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 20 50 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 50 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 46 indices rho q10 m10 10 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 46 indices rho q10 m10 10 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r11 : List ℤ := raw_ints% [-0xbc601668508fe012a0aec180000,-0x1066759c5ec9fbf83ed142e18000,-0xabdc7005ccde543e31d856ea000,-0x465ee98602ba487bf5aa2789a00,-0x143401e196ece5abc9d0e342b00,-0x4529d4ae7caccb2483b550f3e0,-0xb7123d211c0d00b6761dbc170,-0x17f95d7f033a5e01ed141a830,-0x285f2e3621834b2e9bfc5628,-0x37270f0a35d7408928a8ffe,-0x3d6a2edd0d70bdffb876bf,-0x37c8fd331976b892b4654,-0x2932e6cd2efbef094981,-0x188c2519bc389a6e880,-0xba480b0d9212305a1,-0x44d577565336feda,-0x1325a1b4ddda4f7,-0x3c88ddc4a5926,-0x79b4178e610,-0x75a63669e]
def m11 : List ℤ := raw_ints% [0x0,-0x177be6a144e40c6ce87f4561776f501cd01000000,0x2594c2f44b0889495c36c120e88a1ea765aff4b000,-0x1d00600d83d5fb3e8c04d43a54d95a3953012dbe400,0xe5f57029c5bcb8257f3a9e38558bab5c7e337a34500,-0x5239a1746742570797ac158da2ad14a58af63029c9c0,0x16988060b347ff042faaa5c907a9ee7b60998b4082c40,-0x4f6ac1b89363793361163c0353d1847d4709f8c2231b0,0xe521a8367e98f26c70b84475d23c22dda5c2028f56610,-0x229064896ee3d4232af1e7b594cc4e63fe5f6c2df4dfd0,0x46c333ab82dacba09a223035148134f060dfa4c089faf0,-0x7c2be010d230c254308d39f5d9a14a8ed7f93d3865189c,0xbc3ba33fcd2ecb9b8c7f79f512d7479267cf1afd3b6394,-0xf7f823aa716293a2241eb5586f01082d19338983f5fcf4,0x11d1edc1b16ef94a29fc096e6abcbc497790bc4923410bc,-0x11f085f9f603806a2b2613b06162232d38583e17e61d860,0xfd7f0f791bbcfab46db57e3e0ee6b32d541190e6bd0220,-0xc499ec87134265a5fd688763f9a9ac2b7e2cbfec534330,0x85e90a86edf38451f1acbcfc55fec05db617120cb05090,-0x500a5146df20ee28dd7677ae29a92c65f439699851c0b7,0x29e9755960292bfb15b838a8edbd0cda3d29adc198e415,-0x132d274cddbcba79ed530d059ee11126f487a3deaa17ed,0x7a38ae1f58eeaa56652191f8f5be239678394d2e4653f,-0x2a302ad45968fdffdee527067521081ded7cd8a81775c,0xc8b1e5ac2e20c85ab0445174f891cf2c4408fc598914,-0x3303d521bfcd8b63872a54329d137007223e228945a4,0xafbf235e868652d7f10c410b37f346d1e6c3dd50b0c,-0x1fafbb3d58d7e7c0f3cd832f64044005e4d22e88ede,0x4b746ccebe959eb86acda3beaa40c790ec5397693a,-0x91af2da6e2d694d2a26ca46a22bae11e43f6e013a,0xdeeb0f2c97b28526eec5795fc82e3c9a0bfdc0de,-0x10677b8340d196027383bb0826cc6a2f9919a83c,0xe4b28d956a2175f156b90f6e0065c324d46e34,-0x8bd6e4e28984520a428f5f6435780a8d52fd4,0x37a8b920a67a105fe625b501c90192791e1c,-0xce4994b48208be26056dbc34fd33f37f27,0x173d2178b3d160df26c33aa1c49eeb5a5,-0xeb9d1f14bfa410727347e5233f92ad,0x18da98ea8179c4a7cafc0d326d3f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 20 52 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 52 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 46 indices rho q11 m11 11 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 46 indices rho q11 m11 11 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r12 : List ℤ := raw_ints% [0x36828ebbc18f6787555ce92100000,0x4bd1ae2fba837546f82122b690000,0x31937aa23d6969e000f672d3a4000,0x144335715ae5556e67b4badb21c00,0x5ce3307f785374db834bdfb8b000,0x13d44b7d5a25e50546dcb3743e40,0x345a6d8ca9e62eace21e6a45c40,0x6d6158bc0fb35ab983aeb278f0,0xb798cf110ace459bbcd563280,0xf9e408a79f23bad2788f2bcc,0x115177cae569adacb19f0c54,0xfa7868510927c13ce1875d,0xb7efd3e23b5bbb9f69f22,0x6cdef2798d6d0fbe3a47,0x333b687273aa4b267d4,0x12c0cc26df49fa78f7,0x5281aa8cccd3f942,0x1012461f40d314d,0x1fba9a5984134,0x1df42a9619c]
def m12 : List ℤ := raw_ints% [0x0,0x262956c60ff29430f9ced0be6214e22ed21a000000,-0x3c70c3c205090a6b9a1ce0184ed73703ab201a53000,0x2e258e3d89e864d5c1bc431f84179e904d46f6b94400,-0x169e4ee191136e185e65cd367dcb80f569d18bee02b00,0x7fef2f5f64c9d2be2fb2141b452ce51266676ff174240,-0x22bea78155e4be869437b6b0bd24410982e6476085bfc0,0x78a2c6058c465db61a711171ba963b2e982e99313accd0,-0x157ae15ad68321b957ed43380092797c6517cdd8dadfd70,0x332ae6abf79eeb40ee056cb7f4dbbedb01b469a2123d630,-0x67562f94d0af89ce2b17bf5b7198c318473494dfa29e310,0xb2c786e5a07a94d7d079b9a4a7388efc822b3c9b3e36984,-0x10b0b406c80a08a69fbc021bba39a7c0590b80b5ce26d0cc,0x15a6b8645c88291fc5941b8d34faad15e8700d1a3f5305ec,-0x187f9338021d3d2ff67aeafae83d67572ecf2babbee774e4,0x1840731f788d88a6292e8e6db5a638ff58a59081e482dfa0,-0x150b698f384fa091ac95493c51dc491e3720d780749d2de0,0x1005cab31f67e6737579f07e51f5a4fa43c2873797a463f0,-0xab41a3097b0b5649895c653a0a9c5bee0e80c230d845ed0,0x6449fb553187928fd4044f97339026d89898208dcc95611,-0x33644ff71f619b06f337468433bd00873f442ac05635fc3,0x16fb4e42757b0215eb6b6dcdb9fc7389be8568754e2820b,-0x8ef4f3ef3030f4404fd9107e5fef8986525bda161a49e9,0x30159130c97877b298aeb699ece398edd5b135408c4fc4,-0xde7fe6a1d1a482065280f654bc729f8acc87a8de0204c,0x36e723ab46af176cc5779a8d545df743e8b20050fa9fc,-0xb72f7a3d3e5e9a7aacfff99d97788800ba5fae2b0ad4,0x1fe7492623b2d42520c08011fcca5d1a674effa97632,-0x4929668eed801edec422f610045591ab0d93387fef6,0x878c2cf0612b229ac4911827915437a43efbe8d436,-0xc62fe8fa5e9a97191ff1f8499821fab6fbe8b8ff2,0xdddb435f35639a8b606cfd19646c53ba2349d0e4,-0xb6adbcf16b00de5e53c4ed149972c1625e08d2c,0x68c711d27ad9e7bf74ad139528fe645a0d85ac,-0x26c36062749ba23385b318f937bfab6c8d364,0x8407bb0c769329193068180a03801201c21,-0xd7a340f1f4c0e4243157a0e190bf269b3,0x79ad9638c39341583f8f868281594cb,-0xb2f28b599d35ac68f37d00a90469]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 20 54 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 54 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 46 indices rho q12 m12 12 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 46 indices rho q12 m12 12 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r13 : List ℤ := raw_ints% [-0xde0dcce6c43410678b2ee431200000,-0x1347333f8b066c79ef4e073fbc20000,-0xc9644f413e86c25f6bea8361da8000,-0x522dafea0d78f006863521d707f800,-0x1780b36737f2a5909188e648f89800,-0x501d9675e1b4d9dbd5ff73f352680,-0xd30c467699772d6c11f18eb03c00,-0x1b7d5249c453f008a03ffefdc680,-0x2e030478879cbb3caaaba2b0b70,-0x3e6d3cce87b67acdeb7b031fa8,-0x44f8d4d2611166c97ebc17b78,-0x3e16a3c2a5dd48bfb74f0ea4,-0x2d611de3bf6832ce1faf76f,-0x1ab6489bfc083ea57c2aee,-0xc7d3c986c50a76dca2a1,-0x4896c88ca69a55d00dc,-0x13c74b1952c5fcb601,-0x3cf5dbfd82466286,-0x76b4c2273a0887,-0x6e2248bf91e4]
def m13 : List ℤ := raw_ints% [0x0,-0x3e032d01d9ea30cf95f013355f61ef8c156a4000000,0x613bb8fa298924a2b71903efecdf4d86a94590a1b000,-0x4978a821d02ce41ff6788591b3111688bf9134497a400,0x23a0769b76213adf777b86aa9eec3c9f778051ade01500,-0xc7497b977d5cf19baf29a9ca56e95d155cede70c3045c0,0x3581084d8791d33a4b64db030271bbbe1e8fe1476c09040,-0xb79161b52badd8f335223cf8fe4d55e1ca28228ecdaccb0,0x2048a005bac31b3f40450423fac184642d74c2bfbb8f4710,-0x4bebe40f4de8423921e1ecea31e0391db877155968e874d0,0x974b50b9f90244a6c2a78e793fc43208d50dcbe30ea2f1f0,-0x1022243588f15795db9e19daaa1923259bb88c75bd935a25c,0x17c06a2a56cf43e6c622f5864a113118577cc62dfb6403cd4,-0x1e59436be20481d9546ae8f5c099d0a6cd39ae93222593c34,0x21cce2cef4ab73dad3cc6b712060579954a6635ade75ecc7c,-0x20e9057e4cc53e4ee991680f325cb9ee64d79cf942b459860,0x1c10e0b187ce4de9aeb71d39d19ac5c69f65fdfbfc8c53220,-0x14fb4ebc65ad32dc96baa2d6e3202ad07d982f1e7d0964230,0xdbfd13c27ff01280793a8b6c6f3e373ebd60b5764ea7ad90,-0x7e3d0ee4c371fc3b1960c93d556c39b1642b6ed7dbdb72a7,0x3f50b90c32e3d0f30ffe17d1720112b0965fb34aa8af70e5,-0x1bad21d3a4f6c2a1f3aee299a9ce1e9fc2080686fcf1f03d,0xa80a853232cae53c3998d58788df9d9f776f8328e49e9af,-0x371481d60b28157033e535886bf966832bf03668ba1631c,0xf7eb952d9e1aa719de385c6ed44d0ec8afe176c06b7c54,-0x3b6271bf3a82c84e0af4c6c1d0b95b4277328ae006ade4,0xbfe2ea719284a5b8c9a5bf4062ae8491273c5805175cc,-0x2046ebac952d988537523d085b9e0b3bf8ffcfd7147be,0x474434a4f2d6af47c140b2f22fcbdea3098e1f36edda,-0x7ea9ea14b90ea51b61f4a18afbac3066ce4d48eb9da,0xb0e6205239204bca431646aeeeaf5cf48d3b0bb5be,-0xbc2f19070188b7309f6aed0f2224f01c067c657fc,0x92582e6ec9ae07501a92c5c464ddc1d3caa4b574,-0x4eae72d723787eafbb938c59d39c3ede7386f14,0x1b091f6597d77a2286a3e7a926a76b27b425dc,-0x548f90ccbd822b57e431faddd577699aa417,0x7d0f5e2a2d86d466111a01b35b2e83df75,-0x3ed04751496888c68e2bb48370673afd,0x507e98f2a92f3e5e1aa375a15ddaf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 20 56 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 56 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 46 indices rho q13 m13 13 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 46 indices rho q13 m13 13 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r14 : List ℤ := raw_ints% [0x330726add6fda48f91da8d1bf2e00000,0x46cc17d167a0e8b6630e1d3e9b4e0000,0x2e29f2d8a78ae7a8cb497754b76a8000,0x12cf58401f9ecfc845aa1c3f4baa4800,0x55ef588cffb1a9de044e80673e3d400,0x1246952ccf3dfe48fb2859a0b5c6180,0x300c5dd8ea4db380358458a1a9a740,0x63e9e74d10ff04946e66b678df940,0xa6d26d3da09575d34f6846934120,0xe1b58243ad9cd480c62053a6768,0xf89816c4576507be8ff12a6194,0xdefd79c0f9cd013410ab94890,0xa251fbe59ac59800a4700c10,0x5f1aa1127f511b3d9a08081,0x2c3a0a6a93a5bfc3f5152a,0xff6fffd9793710e80aaf,0x451577a1f7ad5772f2c,0xd30aedde3626ae737,0x1968d0f5919fde26,0x17436f9fb80761]
def m14 : List ℤ := raw_ints% [0x0,0x64c52923021c8f5153a61f36baff2543a2cca8000000,-0x9c780c92c39c305172526b8f0ad9556deb0e3a2ca3000,0x750b16b37d673314466733086b930184ff68a837cf0400,-0x382a552f1934e0595659e3c4465985e3d764b882d235b00,0x136cb04ee0bee8c7639123c87be22c3351d32926e7af4640,-0x52829263b1ddc65f589a6b6ae219951a7630954623495bc0,0x117cf0d15d274718832c8aa1735d3d027e0953c94f68e59d0,-0x309e2d6a5823be8cc4efae9f55b1e0a617aabf13ddf591470,0x70e7db6d377be1237b5626ad37e9d1008bfaa70614005d130,-0xde119b48da3eccf28d4e5e093bbcaaa1adf7ff9a83c085c10,0x175c05ae3dcda77cb4b59d699735de5175222e46763245d1c4,-0x21e749e566693ef6665e5728768c70105c7e4e65cef1f12d8c,0x2aae10a14b82a5d3c4840434981e995bad6772d08a2ece74ac,-0x2ecc80531449e7a3ec4a832783fa9e8cd16901e494f25c9324,0x2cd3e4bf529a7ebd5571c8255105b4a1827b8c8a79b34e9fa0,-0x259415896cfe787cded37e46068c70edf8f4354c829f6efde0,0x1b9711159062ec1978aea4836f32d0c15b53930f6da358c2f0,-0x11bd165430f8997a6c1b05bd5ca10aed6417675f923bfb7bd0,0x9f9ecd025557460f7093f256e8109a5bf1db53a1a85194ca1,-0x4e5e68b06833b4c3820f847f1fee926589a975cfd4ba1a473,0x217d3eb6f96f0528d5baa0f40fef4fa8752911c49b240c13b,-0xc67d0cb939d879897e94d0a59207182bfb158e652378dff9,0x3f678be00c92943c51d2304f6037e074982dec1661b80604,-0x1159c25cffa7abc2afc71271c6c9a7bcc1da9fed1c4ad30c,0x408c2a554c05563aad5bd84dabdd487128299f1af85f3bc,-0xc9f8b35654bc2ddd287755b4e24a8a975bdf108097a614,0x20cede3c2923b2914a48c3503f49d3d1a0eda52ff3e652,-0x45bb222098fcb81477338d5e70e0480398a1819124556,0x76db820d513ccc8884433fa414ab377e2b83360c9296,-0x9e7f74a93f3f814ea29684ef81b158e431b68548812,0xa0270fcd1d7cc812c91749f10384883ee22170e324,-0x758ef2cbd91bcdf37aec1e1adb6257664e1d00bec,0x3b34f432100dcdc05757d6d8a6c8bd22c3756a6c,-0x12e191aded62f6cd7fa423147f63bb408e707a4,0x3630993ee518150919dab38230df640a627b1,-0x4886b40d9ffc40fd7c8a502fc9f007a8963,0x2069d0aceedbff9515ad7e4cb6e40ebfb,-0x2431c59c3c425658101d78b14e0679]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 20 58 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 58 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 46 indices rho q14 m14 14 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 46 indices rho q14 m14 14 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r15 : List ℤ := raw_ints% [-0xac74f45e2680acdb34a858df2f9780000,-0xef03371d796d7d8b97d08c9cd04878000,-0x9baa4c3fb354142b91c797f785f3a2000,-0x3f58389afc91018da134e3d0650068200,-0x120faa1a7b95e2eeaf91f073ca116a300,-0x3d5bf053ef89387019d5fa5e6c1d2960,-0xa108a1ca7a0d1d8825e8bb831185b70,-0x14e3474690576e65b4a4e18c1befa90,-0x22ccad82276fc166acc3fa968214e8,-0x2ef8035ea770f42a81874b0e93806,-0x3396f2b94464545d84ed3bdf153f,-0x2e2232ef55561d5a9352a17d7be,-0x2176f1978a834cb87a0726b925,-0x1387719646cc01d7f20d9c14c,-0x90a5043ad6447f2b5dff075,-0x33f02c1019df15d9059b4a,-0xdf5e347e66846d3ec1a3,-0x2a56bf843427e91fc52,-0x50db8b4eb0c867fac,-0x4941cee5199a4e4]
def m15 : List ℤ := raw_ints% [0x0,-0xa3c062d8e36e68e427edf2b8efde9c8de88c910000000,0xfbdd0468a20ba2fe778132d8c325c5767372b833beb000,-0xba8fc45e362739872ca18117ef83f511f936e96f5376400,0x589e9a3ba585b98e415c3c701c0179e4f40402d2b491e500,-0x1e53cd375727866d68dc9bf5ae0069efcfd5f7e93953081c0,0x7f6b992b14439bbe3390c2d7b2363c1a9be332d134b153440,-0x1ab39a146320618815121405a4456665d36964e2884a0117b0,0x495c13a881ebad07de71026984f87da266e93c8bd2509f3810,-0xa84798ad44cddc4070cba4c5fcc3d3c5dd7806fd76f37fd9d0,0x146c2f58d6ca87216c0da8f994783bd766732e9fe366ecad8f0,-0x21ea35134c80af9e93c57068f455ed3ec86f22ab6155f14c81c,0x308a0ae9e80dd1ea3673d59553c32491c6770a59d77dd90aa14,-0x3c373de70b298539c30831add70e6e0c28b6bdf0aad722fef74,0x41055549ac9dbe76ec2c5ba802d682aba8e478f7491fd03c43c,-0x3d493bf1639f8b0ffb2bf4702312aad69b3ef8d6118bc8d5860,0x3282e84310b4c2bf29207d6c2c68126d4756b76b20e96d36220,-0x246db608cfae8b562b73c949ba43f8492729a72bb2570635130,0x16fbba0e8d65b08ffc689ce63210a7c0d62f72e9d0e72673a90,-0xcab98804f39b8f53e6c41910f6b5a8712184d62f8469877397,0x6171e9b0f6ca37fda9ecf628876b58c2534f83f4a0b2775ab5,-0x28b68892b1fb623fb2436a5ea63256b83a110cb47760d1bd8d,0xeb922dedecda6aed824b2eaecada2c6fe1bce971697c3851f,-0x4956b340dc6e11b85bd38caffba1a5a58703357eb2574cadc,0x1385b2dcb25a33fa1e9e7ba54709bc0e9088aad034530e394,-0x467eded2743e5e281f0c3b4c6118ff531852f0f3a1219a24,0xd5961bedb2077891275301e5297441541c75295b1a78c8c,-0x217fe9dc9af386c443008e0bcae59c65d69bc1308d72e9e,0x44862efc4ec9d8e1e66cb6b0b9fe53513d308d63a99c7a,-0x6ffb5ce65468b8a7d81fd38c964a0b8bf815e04bc1c7a,0x8e8736fb845c9f07d926bf83f7efde007aa53fcf589e,-0x88ba29b56b5953ece42280d8ef43de585232d0bc3bc,0x5ead96239473cfe42179ec6100a9ea1e095e15b0b4,-0x2ca33f3854d185e740f27bf076c7adcfca0198254,0xd33b2fc98b3809bc6cd7360a5471293d0d7499c,-0x22be7bef19a1e2b5507561fa49c81ad36ec807,0x2a0e88fc3dd1337ce73bf7521136acc6b645,-0x10b83020c7a2cf6d253be9284434f6d84d,0x1044d115090b1f2395be999b34d251f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 20 60 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 60 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 46 indices rho q15 m15 15 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 46 indices rho q15 m15 15 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r16 : List ℤ := raw_ints% [0x21f1218bf637c066f20c5abb1a0dae00000,0x2efebae7b837f8160cdc7ac1a7291760000,0x1e93066380bd1abbd3d72416fc205050000,0xc6d48e3c60968c1b5f4ec876be8530a800,0x389e3dd233b4c2be5a324c9f4b2cf64a00,0xc012c86f9d3ae636218e0d48446207680,0x1f74a5d47a2d26ad8d9f57a9ac1897460,0x412b0ccfe3d41218026bae80220e49d0,0x6c5c723bd238d6bc4b4cfdcfa2a0510,0x91f071a9f43f6d097bb9c920d86ff0,0x9fe92f795fd4c7a9f2874e285ce36,0x8e9ce7a515d99bfb0e32b8c684c9,0x672287093af404c58c582d311f6,0x3bfad3a25f6d2c8999bedf12cb,0x1ba8240d39f58b06ab61700cc,0x9e2e50997dbcc38d236d8db,0x2a4c24cc6fbf4512826abe,0x7f81386fa47383ff7595,0xf1c773f605b248bd5a,0xd934964a23880e3c]
def m16 : List ℤ := raw_ints% [0x0,0x10a18a0a071936a72c0e2aa6c85c9be6699e46ba0000000,-0x19587ae20dfda84dc50a68cf9bc7c9280792b8b6f99f3000,0x1298944a479b56294f18a9e42783e80777c1f4cf52668c400,-0x8bf18632a13b3eab708971622fcae56683136941ecf718b00,0x2f66fbc7e062a9593dd9b559f04f6dd2a06d0ad70411e98a40,-0xc50c1d58028d7d43903a75cf1f3d1a787829bb6eef88acb7c0,0x28d62b70723251ac5ce2b3f0334667616fcf2bc79cfa3a2b6d0,-0x6ee7bc2a010f4a6515f86579b6a00d569f8f2516d258b459b70,0xfb5bf32367986a195880514b389e71f5594ecc8b9651f95fc30,-0x1e1fc33612065aa7a81271cff5a9adcd6fc08338aece46f1e510,0x315f64e97c9f404a44115a92f4e2d737869de67bdaa935a3be04,-0x45b28c740a41312f0e8428da40ad70067ccff79bca886b20564c,0x553a0661fcacc688da3d187fe43264f416dbbae6e9ded4034f6c,-0x5aa5544085f8fcf611753c5aab5987f21e9f66b4ee69961b1564,0x5417496d814b02dd6a9225b33463b11d0ee6c7b4050b62115fa0,-0x4427cc8eb9dfe56750434105914b25f551a0301d5738da28cde0,0x304ac01cc2c3d6464cb2ee0faee03f4dfa3ba28d9527871031f0,-0x1de75b309d04f8fe9f4b44b05b3329f52739db82c943891dc8d0,0x1029739b71fb8e69400ebb835f2ea4cbe9411fc4291c153b3c31,-0x79b563c0f43377335b45087161695af7e418ee883a7bf7fe423,0x31b8f7d4f979becb1954e110860040c0451cf4328aa5959836b,-0x118e36bbc8c8bd1274614358a56b142e1e77d1cc134d3280709,0x553ac10bd4467495515c8ee1c23f8132a4e6e780b4e17b6044,-0x1611c2ae04ab9b2338711199d4b8497f7771bf51e8002d71cc,0x4d5a0cf839d1ae6c186961db3ef91e3e3d5f2787a9474597c,-0xe2e73a64febcf61a24186358408ba826b7b8347178de7554,0x225b62d8415bae940757afa7a83693db163a7cb768cb3872,-0x439ecd9d511cae01d08f988929fbdfa565bf9c43fde91b6,0x69e9de2abbda716a6c9e700c70d114e4130b5c28be16f6,-0x809d46d7528055cc72a023d97ed4808864082691fa232,0x75140cd177f88d7e5123e9c12de6de697c44c35d5964,-0x4c6f83c745c8f06848e694ee2bdf194fd0e7e3a36ac,0x21b68d8b4952478442e3dd023233612f135818fb2c,-0x93dac8dc350d22026195e716fa9027d3b1c49fe4,0x1649174e4a4fc2e1f025db255f870cb5653fc41,-0x18629dcebe30ddc43f1999095dd671379d413,0x89ef1c85aa12fcb3bb2ede7ce3a348462b,-0x74f57e1b74f661324a44d7798d25989]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 20 62 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 62 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 46 indices rho q16 m16 16 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 46 indices rho q16 m16 16 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r17 : List ℤ := raw_ints% [-0x64a31027403851595169768aed379c200000,-0x8b37154479a2f9e4dc43d222c860cba20000,-0x5a7baf6cb85828349e03caa0e8c492e18000,-0x24bcc9671c33dc92afeee347b57e7dfe7800,-0xa72ed58d1e64c0e2dc3ff57258dc4bcec00,-0x2366cfe05a937d42518ba7d0386cbebe880,-0x5ca195d750b7349827f1b178c0a68919c0,-0xbf9b919c284e749c6ac6aba88dcdad060,-0x13e0d408f0ac2f82d0eda2cfee55a9390,-0x1ab86611543ed1e1c6f1fcfa2b6564d8,-0x1d3743a2b07e365b166e5c46cec8fb4,-0x19fe51d598b4ee80d46b9ae6694002,-0x12bf6e751d3d1f2e98514ee665b23,-0xadecf143b21b136e4596185d19a,-0x4fecd94f944edc1a248c29c3dd,-0x1c75c8bf7899fd447befdf064,-0x7939b28b2c69e1ca1cd295d,-0x16b91fb36a1d8fdb42ffca,-0x2ad55008c1c7d7c2421f,-0x263655c58c1b199bfe]
def m17 : List ℤ := raw_ints% [0x0,-0x1b0680504b88f8cfa797054f05967d566ba132ee40000000,0x28d214dd71e16fba425a4d641a94f2b9ac11984c0588bb000,-0x1dac841beecb32684dfa68e336e05e4fc0c3e5898c083b2400,0xdd2c19df6cf943156d3f69755706007d032da5a8f01a98b500,-0x4a2bde405dd89ce35fa14f36e6d7fe9dd2b79fe9305ced67dc0,0x13122643dd844078eee17d721608a58d80bbcc594c61c11a1840,-0x3e8e3cfa6037ceb33c1bcd7a68ce4fd64c476876dfa8270012b0,0xa7fb8ec4790eef670d556ecf81dbd6dc8960a9bf3d68db5a3910,-0x178428b2a065440e474c2c5dd3869e0fb33c99eb1f2a6b88c0ed0,0x2c8a697cf8cce891391c626dcd8e87a06bb21cf57941c5294aff0,-0x4810e75c6881b2f424f094c2489e2ff495a39aa27848890c849dc,0x645e24137c61a47cef82978cd5914dc5d98cf6c26f1b6115deb54,-0x7900b57e70071c13a5e1d85b1f9ca96547f3f7c649e3a913956b4,0x7ecb0417fdb101c529d6dcbf6f81a336fe8f6ff699920669eb7fc,-0x73cb013ee0d152b17bef99c643c71dd5949745420f49e1dab1860,0x5c4f2c4254027dc0eddc06e16911819ef389801b2e2f2b96a9220,-0x4045a920bf09ea6a84ae822ca48bb6a8cea71f958ad88ea0e7030,0x271188a92681acab653c18d88c8b2a1ecda751814d01b0924f790,-0x14b4356b2619e26a37971f30b0539ecce4b0634a47a4aec57b387,0x98aefe62a6b11d0a7afe32d0a5d0f16f4b4a72ee4ef9b5e27185,-0x3cffe5b3fbb18f05928ec226ddce4de11801c337ea45ef3ecfdd,0x150753242705d3bf944c261155c4162382beaf0f86e7fe9ca78f,-0x638171b4d0cc562e92afcae66609583ffa28a18dc1071bf6e9c,0x19105d052f3d0cdd94aef2efab2e08e969358df55c65ea2fed4,-0x55430e5645232140ce46f11086346a31767d1c737c78a44a64,0xf21fe5f70a7fa97bfcce50ddc210c009d0bc0915edbac0f4c,-0x236329806267ba1f28dc3ebbb6b0080d61d83bef0ef23237e,0x42ffad094e26814e0e7cb026f583ad70daa4401ea21a151a,-0x648c56e9b85a7058a23e08ecc42da18a8ef6083d35cc91a,0x74721dcdb5e123c86f70a8986c7440fcfae6a9e7ef897e,-0x6489d0f8f8e42003fd2addd2458e61f83041b5a5fab7c,0x3dd92570a6901dccd8e105813422212fdc4156419ff4,-0x1980f35f323be36c1646571d592d3fcfae60bb4a994,0x6797c887559e8e9cbb53631234f045ed66cab495c,-0xe4c9736dac8b41939de1ae641f67f4e9bd8daf7,0xe230ab3f83ddd4be0f07e6228680862ee0a15,-0x4717f60c1c8fdc08267d9bc8c12b42bba9d,0x3488a4571b2a132b0f4ab443237fb38f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 20 64 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 64 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 46 indices rho q17 m17 17 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 46 indices rho q17 m17 17 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r18 : List ℤ := raw_ints% [0x11b4698d4778b36c33af0644350ccd17100000,0x1878c5b2076eb5ebf7687fcec3662521b10000,0xfe42e12d69faed9cc5fb090cf516761a5c000,0x67221ca63895ec69be5d3f80ad1f5d7c1fc00,0x1d4d5597526a4077ba47e2566acbf6e25f200,0x632941c18d147ba803adbf3a84b4085de140,0x1032150549d6db7742afa0a281220afc31a0,0x21740f98e5126abed6003345acae1e09ea0,0x37717307e8b8ee1e97ecdb343793230150,0x4a6601861e3c825c2cde03b0c746de2a4,0x513125b04f9560c72cb1742dd0140d1a,0x481572f8fe07254447342635b1d5f28,0x33de2621ebd35e8665cbef10c44e54,0x1dfe9bd7c4bb050cec8ab99194725,0xdbe2082383448efd52e38e230fa,0x4e08c31f07195e51de62259a3b,0x14b1e85455c02aec371f71878,0x3dcbdf16299ee9272855a27,0x73e6eb240d154cb1d42b0,0x66cba87e4d31740d34d]
def m18 : List ℤ := raw_ints% [0x0,0x2bea90827abe9451705568a069148bac6ee5f2c3280000000,-0x41c2fa7fe37886cc3d33688ff33180f0313d8c71bbd5a43000,0x2f6056895c2d55d025b2f1ab8a8b9ab5242ef4100721dc68400,-0x15dd4617d9b2722fc8b2c658947157ba971694f6eadd769abb00,0x742e686175731ae11b2db271f2b764ecc8a53429d600aaaa0e40,-0x1d9239e58bce75dbd96c0040ce55e7682a19d2cb6c734c82bd3c0,0x5ffa7a24dff2c67a1ffa8f119d7555160b0a550a2602aae64e3d0,-0xfee7da4d2c8ec56309bf3737e4436902192e2ffd3aa8a4f529270,0x23468d4de11517bf12cde70e1840e1b8854b9b8f35ffb777e75730,-0x420304887ec2c1c7f042e68e7f73537f3857fba866c793b8b77e10,0x6976b0f71c81d8916ae166950592f3d33a70cd5dca79f990c56e44,-0x90f1dd14101d9d36a960dfff27e6904c86d839ed29c49977190b0c,0xac5303174ad32609b62c60f3cf4fd7c4a78bdea37498af6050562c,-0xb1f04e76d222e3caa34933c25f16800e7c19f9a7e8ec8c83113ba4,0xa0015474bdf651ca9768ae0bf0b46021298cebaf3079c0e6811fa0,-0x7d7c637154a313404fc709b025354c46bb8511d595714645ee9de0,0x55df63e819974e555384b53f9ae9955d0c1c47d91ffb9e5429b0f0,-0x333fbaa2fd315fa4384b11ce13c80d0b9550c6e6661236a19c45d0,0x1aa243a2984a982e6bc3280e49125ac1d2f234637a21777b74b4c1,-0xc05ece4cc9e05c1a8aa5a9c54f4d4e9ebaade2ffed96b2a01ced3,0x4b2a5278318445d61115e1502d7fe31f836ed22c35b865e4af89b,-0x194d48ea2be08865ce11830853c9727c0da6daa91264088f2cf19,0x74b2be419921b6d965b46dea17a39042d7ae21e2de5dd6cc9e84,-0x1c97d88ddecad1cad8d9f423aaf9d6373cb8f4fe35971d06bc8c,0x5e663a0e93e0c294415d9138210f6c9d9a2c6e6d16470709b3c,-0x1037cd978a62a3dd3cba0a24e431386a11601ff7474fb26b894,0x2499adde1a55a1a74c6fc33b4ece7539ae4a8ee0c3c1698c92,-0x42a48d5b275e9f28f2aff2bcaa68d42d2334d790a2a2d4416,0x5fcc2b9078890e089340b1d33b7f364bd3679573d835c156,-0x69c3aca2d508237bb9c04f1ccd37d8eb4a1f332a5b2fe52,0x5691547f7c7e707413b6850946aa042b883c31ba2373a4,-0x3226b5865512e4142f9df4362c196372f604fc8bdcd6c,0x135284311ef9728fc4dc6369d64a37bfa3d6e400f7ec,-0x48a4cbb20e3428716a4cf55841e3587145a515dc24,0x92d671265d5ecd200c4862d8683c3f939fa429d1,-0x831b5ae7bd13157b261c9a99856a7b22a6f9c3,0x24a0f293542752cbf170a347ba34fbd1d35b,-0x1796946bbe9ba611510ee4ac4650d0d99]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 20 66 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 66 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 46 indices rho q18 m18 18 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 46 indices rho q18 m18 18 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r19 : List ℤ := raw_ints% [-0x2fa0bc024bc1b36af20fbe4a1a6d8da40180000,-0x41c870da44ebd9e46748b8adbe5dd4fd0818000,-0x2aaed9d1d4152fb4cf1b7eb79c5ac246424a000,-0x114c33f09a651359174abe33880a7a916961a00,-0x4e8e9c3fad19beb36b2d119805ab1ba1271300,-0x1098fefbee861a39b7479ab9865ed5ecbe8fe0,-0x2b52a2723dcdd1ee240522fbfa7c489f8a0f0,-0x595f4c056844068a26287a0d325f3fbbe3f0,-0x93e93071bf94617d48b265f81d25761c068,-0xc62c2888de4f6ec4d5aa0853d418dfcdde,-0xd7e609439b0bce3abbf4a002c2efaf977,-0xbf50f8b66da5c75d8ab579d5365828d0,-0x895f4a1f0be8e1c94a1cfbb475ff5e9,-0x4f4147cef0b3531ba3c603eef485d8,-0x2437aab6259b28385b64c17cf3b99,-0xcd0c01c9960b65427bc3b9dbc6a,-0x3632e1e7652dc45bf0993632af,-0xa13b3771be5f3851f04ece2e,-0x12d189addae4862e8efc180,-0x109b9c0ec26c72e731e92]
def m19 : List ℤ := raw_ints% [0x0,-0x475d2ad40775b104568aca04aac162f83435aa7d2100000000,0x69f8157d61e9c7fc169a94caabaf9ab22e0f82f980abd08b000,-0x4badd3564cc1a8677a22a810c4375381b99dc523d92f0862e400,0x229c30c40f5577243f44eac82b353500f5287e5ffdd7d44048500,-0xb62ce3bca92de783352b03024774c61fe9b16ab310afb781e39c0,0x2de9a45a1500198985b6776ad25dc4bdf397f7ad60905b34333c40,-0x937d0e0b0f1de80fa282a187bf2e5b954eb7e90864673a75a2bdb0,0x183825b5fecc43905c1a4cb26cbb5574a1434d0f6589e258ac14a10,-0x350647b40cb603948cd8d0b39690363610dbb214ffb4cb7a3a213d0,0x620f359437f426c1c2d6a6e453931ba26a6e1381a3d9960029776f0,-0x9abb9d0959e8dd4977cf75994acb35b6ce58d1459cd17d1b38de79c,0xd1e767caa41568bcdd43f4231317628f7ade49b87bc268e4dad4094,-0xf6273fe5c10a39f6eb5d9d3a1b590feb5fe35921624bdda9528b1f4,0xfa85fb58006abe7f2efefa50f4294f59102c3aef2210ff7d7a767bc,-0xdddc211b220b9762030845067d0da05b4dd4438ed0a885c5b80d860,0xab3509e0a28d9c7f7ded83c4473646e2de37e0590544acf9df4c220,-0x732bbc94112aee33cc8404510085d559af4e43d4c49165a5c409f30,0x437ea4724dc7a9f920fdaa890a09bb60a94d879f991c92dd213e490,-0x22674f24446aa49a8938814969880544d2ee234b3d15ac7adfc2277,0xf366f272b61247fe047857f139541f9a29c47353d20ec9e94b8555,-0x5d05cc1ffde677618d42624e1c4fa7faa95355597dfc1abc87772d,0x1e93d9c4823b9442e87e7e0cf466fcd8473341e894bd4d876bc0ff,-0x89778eebeb840581cd68d17249a2a9db72bd502e777ed82d50e5c,0x20c35ba1a3fe263bedf9d54490c0e7d9231c0806b568e54250e14,-0x68f843c064a1c2c08503d9c914a23b34cd4a9fdd0844aa8efea4,0x117450e4ce9a0e17ab960608e2724f246cb04c3d5289ee61be0c,-0x2601f63708ec938dd7219273a9d34838e195f02d0a741d2065e,0x428a1c86c1ef431c3d266e77c0698a5fc84b5d35eaecf0f7ba,-0x5b9622e5f89c1ee8767407958d78975939850f00dfcad5fba,0x605adbf57915a7dfeb072c0021a30b35063eda899c6d285e,-0x4aba7dfb10e6af036a3cea32dbc800cc4bbaa1ad1c7cf3c,0x28bf4a124180a7ff0f1ebc691d06808fb2ff004bd5c334,-0xea8c84d5c960bd4361b50474c4f35db3ef7b6dd724d4,0x32faceccf8cd2cd711c17f93bdac0f5ff6aa3d9e51c,-0x5e42fd1e4d301b7bb3b41b3221d4b9c8dd677cce7,0x4bfa90a04fd1e78249ef5a040ee0d6151d5aae5,-0x12dd52a22d0325de53e70b12f2c9af8f031ed,0xa967b2ed22e82b8a6b3ca6acca993f8ff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 20 68 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 68 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 46 indices rho q19 m19 19 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 46 indices rho q19 m19 19 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r20 : List ℤ := raw_ints% [0x7b1e1d7f9418565a216c177ced51ca349c700000,0xa9ee9dd5ca5eb06ce2b60546ab531665c24f0000,0x6e2d703882329c783d40b5d91b1c4d623148c000,0x2c9d33b4d991db55654fe4387bf350bc5ef10400,0xca6f21c0262f790f01030d473fcd3980325ac00,0x2abaa2cfda19e6c0237266822e098545ef825c0,0x6f697e169e600e3f81dad455e982f3f4765d00,0xe591bdd5f150cf5ccd1c5faa9a4b5132cebb0,0x17b73ebf12bdbdc9d2647a8524c49a7b160e0,0x1fbaef4fb5cfff89589b21111e63a56ee6c4,0x2283e2e7338a0e80605991a475d7eecea20,0x1e88873402ba354dee386daec4d36fbdcd,0x15e202f15c41f82af4f8eaad41cf662aa,0xc9943b3f1ab47e70638d6279d3b1b8f,0x5be709d6c82e38e6adffe1bae439f4,0x206f5fad601909ba89d5a4831b78f,0x88c63532741248bfc9e68f090da,0x1958ab45c87f18ddde935b98ad,0x2f284fc4b3cdedb061438b08,0x2970d7d2bbb45ef775a6b4]
def m20 : List ℤ := raw_ints% [0x0,0x73f765988c1f3fa70ca18847957a40d354d7350b55a00000000,-0xaacdb476f0892730f4a832c883c40bb615cb2ae2833735d93000,0x78f3a051657fcc3299873c2e3991ec1fd25decb19229f11a84400,-0x36d3fce7e5e874b02088d68db06cd258b4a06b89eb3cd7434eeb00,0x11df2b88212ca66aae5e0b892c2a3f69b2e6928fd124b6e69b4d240,-0x47602f85b4b6ead74072ef00b7925bb6a5fd1aa81d0f1c960a2afc0,0xe2fd6b71a8aa16aaa84426335f8c8bb53a6d0ee01b74f7f9771e0d0,-0x24e247868a55a1658cb7f94f5e6d0544017e4f80d7aff0c8bfe6f970,0x4fdd8b2185530aeb800556bac088b50e0c5fb24c88263817de04e230,-0x91ff09bf378d9ee24a2d60dfdac775ed354d8b6e4d7cdbdb2a422710,0xe3969feb2b799700128a25ed82f6ee0dc4a6f74a853832eeab0f2284,-0x130cee69d2e34fcdbd44bd3d7d03a019a807541ea927fc8fe2dcc0bcc,0x160a7b838d14957545eea48ab868676dc20383f0da0700d84a48048ec,-0x161d6911bcc3be14db00d64447380bbc70f5eafba28e1e549b81145e4,0x134aad9da393cd585bf09e1f1b5b1d3975c3e26bbf374bfb5ec63dfa0,-0xea6c32d51dd4ac9b646a525b0eb773e7519fadaf9a3342dfd16a6de0,0x9b0b84826edc2470742f245f82d6b399ca1c67614385a78d6f663ff0,-0x593cfd46c825c58b21c37d05e2825ca2b445c77f92dbe5422299f2d0,0x2c9eb966be23322cd2461277f87d7395313be2e2f7a0436750fa4651,-0x135417c092fc7910d8d7a3291b9bbaee1642a9ba3f7f5b726d4e1483,0x739cd4012b72c9bbc725ea08379610658b683a9f2bbfab97dae50cb,-0x251cd5300f8ae5bd416855e121b81c05d36fba1935b9377406d4829,0xa2a23c691bf2b9190d4de90cce4f3ec59d22cb822de60202d600c4,-0x25b3f7a64d40bd51d293efdb8b536106b3c92a55f75daf5c55734c,0x7537e4e8e2a3b2f3932511b197bc150a80ca46eec8b2f1a3878fc,-0x12dcb592afe911134299bef901745550bed3ce65b3a91c627afd4,0x279fa8627ce559c4d4f033074b31b9f77d4071f0f82bb6cf02b2,-0x42add9e41d35df3c842ec13edf6006491df4a52ba8aef24bc76,0x57d9d5cff016dcbf4b24156d14574f585f6c6c0cf23f61f1b6,-0x58098ce0247c5acf8000acbb5a42c5344ea2c9ae88a16bc72,0x40a9f79188d35c0c22a732379b4110cb491294d5d3eb71e4,-0x212b03e2ed49a5090ff4ced88eddf2116176bc17243902c,0xb22b8a35646a27d8d71b9715b32badd36dab6e7ec20ac,-0x23ccecf4f7f39284207108c2312d14b58eb652bcfc64,0x3c852dad6fba3756e3b66205e706344f7525384061,-0x2c0587f48c3f59d798a5ee9bdb48a98c78ebaa73,0x9b642d6713ea9588d5dac098e695938cec38b,-0x4c03bb6a0c0013154583dd59f872be32a9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 20 70 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 70 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 46 indices rho q20 m20 20 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 46 indices rho q20 m20 20 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r21 : List ℤ := raw_ints% [-0x13335aeacb084aa9732145cf6326bdfd68f4600000,-0x1a7c1aa2651b47678da4483c87007dcefd39160000,-0x1128f1fa855bcebf08d43b32d40d79b968ea378000,-0x6f1808044bb73c25de8f1a9963b045f6849b9a800,-0x1f7ac2101daa663ac230320dd65c93a7d842bb800,-0x6a3809fa24805eb41d9e2ba446d3433684ab6b80,-0x114b008fbaa92dc3de5e944f3e7eaf7b6560cb00,-0x23985d8263e2116cd1fa34f919e552a411f3140,-0x3ac449d5a3a0d986b7f3e755d40243670d0c70,-0x4e86bcd46f09cf045ddc403163ab1889a44d8,-0x554cb0779b2e8cfecdda01a9186b0bca7c28,-0x4b57e0c56777bdfc6faddc0c1c26620f888,-0x35e80820f5a1798fff3a57a70f38e70df7,-0x1efa4be60fb580eeaa18e99690292d806,-0xe18095b408d21a3a167dbca828d9069,-0x4f6723ea462535e38e778e50d4c99c,-0x14df831e9147460a8229bcccf0719,-0x3db60315018393f41e7767bb6be,-0x7270e4b3faacbb7cbd57f026f,-0x6432670f22894ba9c655900]
def m21 : List ℤ := raw_ints% [0x0,-0xbc720517e3b2c76f74867d7452e6a95769ddb6326b2400000000,0x1135fc8aac4199725fa73a4148c15068bfc843624818bbc235b000,-0xc1677404f3f6143b732cbe3a4628b3c16e222be8fc7445396ea400,0x56ec013cb81bb633634e880d95df57a0550aa29508d184e68a55500,-0x1c14863812e620744b1b610f6ab5f986246d36cb0dc37afcb603b5c0,0x6f197152e5d4c593c56e024804fe0ea4d4f23cdcb81cee5b4644a040,-0x15dde80bb0e316296b55a0a123e42a1d98880cdcb5da86ea0812418b0,0x3844db7aa32db63b0b1b6aaf0d32fc95e70c189ba618f2a23f1556b10,-0x78883fd66a48aca3914567bf088bbf008e075679641c4d948e976e8d0,0xd9d9f6706256ae96492d1ef50bc9a373fc725854132b3590d5a2a2df0,-0x14f9263bac73818253886bff5ad9a66926115619d93fed517059af615c,0x1bbd008448aecc4a086ac62cb1eeae1408f3224710ae11a7e0b797e9d4,-0x1fab52c55ff64bd5a09203fe4538479750e99e6799d90fbcfd3be54134,0x1f55225d3a651b8d5f9b24d69fac2d6c6bd588b4382f95bdb3d911937c,-0x1aede5c149938c166a05eb33476d871fa94c19aa29e0aa9c02c0209860,0x1421b978dfe623e123dcaac50bf88f8222f6a38bf1aa0068615d27f220,-0xd17e9150cbc71ab8d483cd45898f976622fe3acec11b146b7e076de30,0x7670babaec71acf8b4846a12814b976c0eb6de1cd53dfc7d40c1b0190,-0x3a19d095cb89eab99e4316643f85f523d4c4b17c4c1bf2bfeeecfb067,0x18a890f84d806a2291d3d5eb6a9843533ad82775af4e2c2962f9a6625,-0x9049ee94b7d8a06bdbeb3b30a1b5a8bb21ae07c2eeaec2bbb99f037d,0x2d3c23b4d77a5ae3d7fb6a225fd50e1b466f4dfa103f3a6cbc0e416f,-0xc139629361516e34553b10b4e3741c1dc56c60a647f352f4ddd6a1c,0x2b92098b381eca092eb9c3f2897d7f593b3d16cd1ac77641d3e5154,-0x836fe117a3b0edf63a5297e387200a0de58151e7c50e031ba5f6e4,0x14770541427c19aa5ce806d27fa207243bee52f882254f07a758cc,-0x297715ff4a6c9b0c4ac90d38f9d75a03d49ee07ba4112578eb73e,0x430dff4b42d723b91e58a7bd08c9109eb4c83a36b7a4fe88e45a,-0x54893955dcc77d6db184fd8da242f9fe16482e9ddc8d61c805a,0x50a8fe3c633442826f5ea967ef1c8673f8cedd15c24a6f153e,-0x38150ca77760849bff57e66aabaf5dc0f3c1c7384c53deefc,0x1b0b96c84c93a7ff95c46423c8638e468ed53cba1ec75a74,-0x877fbd488284cdcf9bf359c8625d15ed442805918e3414,0x1927ddd04217cca5d4d3681a3097225dbdb8de1a4dcdc,-0x26dc61497b43ade89c5fa5dfc8c61f3ddc0289d8dd7,0x197ffc9862f589a6daf5d0cb6fd10ef16edce68b5,-0x4ff83b9283f9955865ab1f3db284521d2b8e3d,0x22191b196117538ca3443333aff6e1f656f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 20 72 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 72 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 46 indices rho q21 m21 21 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 46 indices rho q21 m21 21 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r22 : List ℤ := raw_ints% [0x2e6c8109378f3d36e23886c6e41eebfe6e5b8000000,0x3fff9f423a8646123c855ab800c5b9939deb7200000,0x297083eb8f029c036f1c99badf6419ed8782e0a0000,0x10c1887aaf8c7f1f650ac9d5017cefe6f8c70ba8000,0x4be921dfc0a61b573f43c13c5cef928912c2d95800,0xffee41ddf340d38bf2fc29a9b00e1f63adf46a800,0x29a13b969cdc519164f34ceefb4111e305b9a0480,0x559b2dfd246f79ab338e262a2017ef48c5828500,0x8d2f29322635e94b1a59889efa4e04e7565b6c0,0xbc7002a65f836b81c122de021a7d892b18e990,0xcc6e9b608b57aa96b37e861c4cf0c862c2a28,0xb451dab3470f216ea25613f1e742e7e645d8,0x80d156454681bb35922cdfc516bdb201478,0x49e6d18897b43efeeda199e49e7bf76e09,0x218f7a9836ca83ae81bd47c4da11c6dfa,0xbcaf76293f2191be4f7de47ec734397,0x317cbd7e53ebedef30bd501dd6f864,0x91ef3a3598301ab067a4a20e86e7,0x10ddafd351fefdbd26cd83f1442,0xeb8142587d8400c1c525b791]
def m22 : List ℤ := raw_ints% [0x0,0x132394846d20284151d5a8bdd06b6d32e0c084811ee1a800000000,-0x1bc13036a52555446c11d8a105ff33f21e18f91b13bc338f73e3000,0x135688c290ce58a6e5e2bc33ea2bf4f24d43c80fbc7941e79bce0400,-0x89e73967a1f0ae1684e0cd4066b678ab9135002fc2c3671410be1b00,0x2c29b586fc31dd2ea21c5999b720e33069d71c496c195f672938dd640,-0xad2491911f5bd4ba950573f671e1170e6749a5a1eb53aa0617f2d4bc0,0x21c0f6a8d013d3db3395a708cb423996b47ab028f6bdffc29748b6add0,-0x55fd35fed7f5dd9d1e458d38e7db040cce93d7a2008200501ee939d070,0xb642ce944a77224824c5b98f2ddbbd94a6b4a5d585cf5c6f3a4a499d30,-0x145c839f873e72e99907b28b736b72bd3e6750dbcd91c69336707aae010,0x1effc5d2086106b88bc9a17560e6e6d829e3aed73691711939610491ac4,-0x287ea74ff9ae4b3cc493b31b932b88fa6cc08f41fccdf6e0a1a4376188c,0x2da2376665e3b0c19cd18de61b8ee915de1b82e6bb628ac81361289e7ac,-0x2c874c8d8b49ab60e5faee6279ac619733d21052a9905fb177522917424,0x25b6a50b49a954737635791e7cacd1fb475798c4e1d45c2dbb5938f9fa0,-0x1bc1ee071a0fcb1d39bb10bea964b718c9d8903ff8637494400698e3de0,0x11c179c882aeeeb6fcb8470d2d0a4589b952f336da9ed6bb1dce34edef0,-0x9dcaf254672d0145d27d3973e0bbda0eb4dc4d454d1be0e882c6c1cfd0,0x4bf35a46f2e3deaa237576e9360e658306db82b94348348b9cfd5180e1,-0x1f95aff5e6db8c15f035788355cb583a819edd0fb52f34480d0f666533,0xb4d0f0539822d380ea44ee97d4792bd81a8b2aa3d751f69c89adfbbfb,-0x375d0b012e6def9001f05f8b3e242b7340b319b633a805ecfb5bc8239,0xe685ada5879da78ab668862331e1981d9eb514d4d101f9c51e9dc704,-0x328ef10c4b7670d4da9297552cd666bd0ef82e1ac80598b72cbc560c,0x93f9791c36a74ac7677a1b6669e44b13ecdb988135e559f7c5db2bc,-0x164a4a3271577dba3597e20de6addbace5d0c512fd1e3682a949b14,0x2b8d4bacb45267b972cf15620650480261a50d5c204231b585bad2,-0x43a96eca6a6a5069012254bee0ea415da26c698cf8ceae8b95ad6,0x51983dbb8e71225004c10ac26749958d3b79e91d4ad768df0816,-0x4a18815fcd8c850f892190b19c682b3ad12a226a4da442cfc92,0x30be67e84ab2be4f97b0c033208243bb6f597e3351f9599424,-0x1616951e77b811f1cab139a7e0e41ac8e9916328ca6203eec,0x6727d0793ba6129aa20d16fab5825def18c10b05fd5356c,-0x11af642ce68b432c891de140bc8d1021a8afe885a040a4,0x18f46472f433429e63b860ccd6c7ad3358661ebacff1,-0xec47a3718d1e285bf27d4b58fa0f3639397149623,0x2923d62e3670941c9a6962fc91320244fab46bb,-0xf4a6dff2626e3d8c6b9af4e45815a9ed8b9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 20 74 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 74 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 46 indices rho q22 m22 22 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 46 indices rho q22 m22 22 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r23 : List ℤ := raw_ints% [-0x6d1d9831b73ad346d94c027ee85673c7b77e4ff80000,-0x9657b59940c96535d410062c34cb2501566ecbcf8000,-0x614a835bc363324245f4709a2d4857c848b74eae2000,-0x2750822c26cc3792c7b2e4c0806c47cbec34b6b36200,-0xb1fc662009a7544be9bbafbf4a5c5f9a760e40c7b00,-0x2579fdee4aca0ecfc1355b42d8b69e3979cda126760,-0x6174a54dacf0e22ffc4a299bdd0b0d518bcc16a1f0,-0xc839ffd143a35bd8b36e94cfbdc7327457f565450,-0x149e6627bcd0fb8a21c624d3244ae4f29041e60a8,-0x1b7d99e7f957970503717aff4bfdf1d0f38b8d86,-0x1dca2492d36cf36fcd7a5aeb262a737ae3c1467,-0x1a3e2a2c6ff5fb81d1a05d646ca35b947d4a8a,-0x12b8b6f09fc0672bce6ee25b0173c92baf3cd,-0xab95c1028690cd26e634384e6a1a9874224,-0x4dca5188827d8b0e37bcf2e12dc659a50d,-0x1b48c5867218e09df24ab7b3f4f49b03a,-0x7242c46b7bffed5a07871975b00541b,-0x1502e3093b681e38c89791fe813eba,-0x26c125151346a1738dfa0115948c,-0x21b9a250f1dc4d275b4a5f8ca8]
def m23 : List ℤ := raw_ints% [0x0,-0x1f19d1573154416a24fb323472ae9172ad38d751d22eb1000000000,0x2cc4b6761508702db19a489780629f69c8fd1eeec3d9179e2512b000,-0x1ef3aa14a2c26537edf09a8e3128d916bdcd92fa4fb28e960371e6400,0xdaf178a1ae710e06c66538afd1e1da4ac9482c471ef3eb876584b2500,-0x45860a09fe4c04647acd203a4e2f20200301933a532fee40fb9842f1c0,0x10e2877f458f3c7c8727fba972f6db3ce853bf44ebfa533f8513e724440,-0x342d6f23c9177f8c0a6dc94e970b40518d7273d516c8a82b52a836f23b0,0x83a089b5e9ac4049b5a1e9054582c6abe974c123a0252093036a9679c10,-0x114214bd063a1db93dcb73ffaf29ffa48540c7c1a67b216842d7dbcf8dd0,0x1e83ad66637818d207c984afd19b9cc373fdf1f8a4ffa8bbbce0bed3d4f0,-0x2ded2521d11e772a42561d7a922d02824c59dc13c113ba8bc4349e12771c,0x3b456529c5efeb47a01a129470e97974a0298f935e9209c67afa748b2714,-0x41f0bdcaafdff52ba3ca1501d41be3634bb937d108d72233d86ecaca4474,0x3f791276b3f3a2f0c64339946addf2bb07003344cd7edcb89690e80cfb3c,-0x34fc684462f13988754d54c5a2bd93e74208f0dcd7770290dfea894c5860,0x2666e5dcf2ab17baeaae13048c9378549432b15d8aebdd50c5c5203a2220,-0x182a06d2be87b302b67c7f358b217bbbbd7e350f9898af2c843f71de2d30,0xd30055c1abd7cdb9c2e680f600d8ebf59dc14c16886414066e7f7914e90,-0x63aa78ec430b74d26a7b8f9798a9c40df963ae757593df775a9b89c4d57,0x289dc264f2ffb4da329ad58826a25d30538086ed776f521dd928463e3f5,-0xe380a76d3ea472dd3d43d63e82207dc056f2e9d0d6a8166602f95dc4cd,0x44090d73212298b7a930ac8e1ecf09063ea222b60eb65b90d0904898df,-0x114237d64d917099feba92ac980fa57ba5a32d4049bc32e890492441dc,0x3ae73512aca37efb2e37fe6100f84f285e957a96e682865ec79020894,-0xa73f65fe37a9f12a98fe09a8e6f7bf9d26ae09c9029a07a9fba97324,0x185eba4b8e02a4000f2745231aedecd8bab5e9683bee09f15e6f9f8c,-0x2de8237a7f7765b44cf4b77f354d0bd820b38dce73b6cbde73a161e,0x447fa431e55e646d40f451601145cc47a172223096ca31721e7afa,-0x4efc7ea0c7496542f733dc4bc1ffb12b43c43239fac20fadacafa,0x443c6de09529c1a5907c49c854ad2729fdf4ecc68f88b9d2301e,-0x2a737f63bba4119e23336c661f39315b137b90398a858ffcabc,0x12110fa1dc2027c7266a0a597d4f814b4a61cc8074e307a5b4,-0x4e9b6fe648feb4fb87bf58925c243cb052848f58fa031754,0xc704911f533f4cc2d7d09f134c99d8d0a06ab92561f09c,-0x10066df9f83f4cd1368d4421b58781fc2daee40930dc7,0x88cc9194d15634f9e0feee250d4c6e4e9f3c6e1385,-0x1528175dc8e4cf790a8925935edece5ee6121f8d,0x6dad5d100b3e7abdb15c78945ed1efd668df]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 20 76 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 76 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 46 indices rho q23 m23 23 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 46 indices rho q23 m23 23 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r24 : List ℤ := raw_ints% [0xfa03063b7d2d2f44c016da27e3b24bf470ccc8ec00000,0x1584d42772e1ceab8c08c045601a20c4eab2a9a9740000,0xdeafea6118713043836ba7ad900e3fd8aa98bc0258000,0x59eee35aed5474439fe96a4f0d6ce5983c4b148253000,0x196e3a096e7b8b59fad71ae746b2cd2f706a3886dd600,0x559d6992e02ba04cfb6d6a8f2c9e7f4fe8d81b0aac00,0xde7831d7082757ece0d8d2fa8f6741cba3b114d4620,0x1c8b30509414372b7bcb486079e03afcf0fb4e59e90,0x2efcdef5850664a5a59476e936108e902de2923df0,0x3e96607870c01904da3d2a48254325efa8b47be48,0x43bffc63a2029ddaa563370f5c68f1adc9263312,0x3b9d64eebe613b775e35a6abed8cf79d4c8c369,0x2a79b677110222404ffee358d6eba113f26d3e,0x184c141f93427cd4f9d6e484e42e801d55c93,0xaffaea6d7faf74e2805921400c065598d4c,0x3d9edd0e077f6f4f9d612edc571866ab13,0x10194451a0a26df4cd2e481cdbd0a9f96,0x2f44f8cfc96100e3c38eff2e1060c95,0x56fd42ca53438dcbbb5124e2a253e,0x4b82627447f5a012db3de15bc04]
def m24 : List ℤ := raw_ints% [0x0,0x3289f42db028ea4c7c1831953a5bac5a597c5de4f58bdfa000000000,-0x483a812da3ba1b11ebb6775a1000623c703b6a1a5028205dd9ed33000,0x3190484e60bb18f1533c854e7d4d02cebb40b4c5e97d45281961f7c400,-0x15bd9e8c2163583f91bd0849c1a987d2a3ad1359f894a5fbd4573184b00,0x6d8ce13b672f3b5e5a41f640ac51aa5a69b7564adfcdcf185bea0f91a40,-0x1a60706121e74a26b23f59aa32706be87e7eb853321737ef87a992a7a7c0,0x50c55d8011f1d94189ef61cce50003215fddfc599dcdd619fee55cf04ad0,-0xc9d16859c5154708b011baef3c6a2f05247f64fa5533e58775cbfc721770,0x1a320d273a20347957770a9a023fbf3d8c4325b9e7bbff119102717c08830,-0x2dd380f54c8d68ff685c0b961ce11c5b943a82c6a7a32b66ff40af49aa910,0x4433322e5d1480c7c38b720771289fa1039b62d008c7ab318024331ff9704,-0x56f9762fdd2386f867c8670d88933e420f4cd7dc7ede7e91c39eddb5ff14c,0x5f8be59933172fb38ee6a79a0f60af73c73caf5bf11e8d8618f96d84ff26c,-0x5abecd91d08167527bb925601a3d921431188046dcf9388b3dce366ec0664,0x4aada5e7680bcce4848e4a6dcb11d953217c7e5c312ed9a0b8585626a5fa0,-0x354e3d25438d141ecc50678250f396ad528a7d8bee98cd63bb6c0c15c0de0,0x21002ffbcbda065897ee1477d7980b26c582bcefd59669dcb462c1e0c8df0,-0x11b2eba9b2772a7210d5f97cc072f8ce64698e68032cfe5394eaa59dedcd0,0x8347c8bd925afe9ed5332b10a1c7c67a9a64054fcfad0ac8f789dee8f471,-0x346ed4393de193fe5187cd1c4fd44c3618b66003aa5afacf2b915e7770e3,0x11f5fc1df7a497a35ac8b151e4c1394daca72375c309cb45fbc2ef0e6a2b,-0x53f0e7e4f47baff1db73885dceb2fe25df2fbe8bf2af0b842ccbb068d49,0x14c197b248da1eb8d8a586dcdf3a752cb508c1a71d62fd8196656e63144,-0x44e53186f1cae8d5edf4f014e4b3e7f365532761f553d7d273d9d224cc,0xbdc17a5aa7d2c6d1684322db7757edcb143dee599a4fe8ec51136087c,-0x1abdea05b5676a6526e47cd8328ec7956a7c50752542070502f8cba54,0x308e5ad604fb30ad37279e94f9e3bdb28fe230c7ebaf362cd051d4f2,-0x4590a9d927b1af3867615ed84418de282b227adf1544d4e59ad7f36,0x4cad00ea7b99af20a49207a9b1c7b2fee0b52196d3ae94ab376476,-0x3efd478b0e4ef47645c03d25d9ec21ae3f938f5bef2e02231deb2,0x250a88521b08afc6bf95793f669fa25c1ea21981c32498ee1a64,-0xecc36ea18357fe910e6b6105cc26b20235425e0d30d61c99ac,0x3bf3c9d204db2350dba71e0fbf501f299b0fa7376b10af62c,-0x8c07a77542e7e04fd3383871901b033750395128781e8e4,0xa4a6cd3dbe1689820ce1d58e6861c7a4302ae32f76881,-0x4f2e871a3de661c8dbf2ce1e191850827e547816cd3,0xae0488bac459f9285575a2b5fc7ac2f4357e8ceb,-0x31275adbe152f4b2c5bfc43ddea2e2f710fc9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 20 78 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 78 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 46 indices rho q24 m24 24 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 46 indices rho q24 m24 24 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x4b82627447f5a012db3de15bc04,-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r25 : List ℤ := raw_ints% [-0x22fc4625535764abe215baf55536b14c950b46831e00000,-0x30285b21dd10d2c49b59299b1e578c25e0404b45b9e0000,-0x1f21b8d43596a3719e4e90f57e5e0ea726d4ec5ca7c8000,-0xc90db0a9000ae6ae7fed7d8086090d91bd3726c17b8800,-0x38d19a5a6274f9c24eac470ae3a2748e278440650dfc00,-0xbf2a1a9c9e8daba385d3d0d0ef3996f286324f38c0f80,-0x1f065046400a8f5d2023e0dbb20e0cde9f10af0b1dfc0,-0x3fa4342aacd858b5f1c37c0e54f8d4a1ac705e018920,-0x68adcd26e224b19e4c0037b80f698fbde902e30de10,-0x8b4ec58f563f255316a73ee1af185fb97e21480da8,-0x96a716525e7fb5b3c67e7b80eceaf393339d809d4,-0x846c5b238da445271e449ea4d9d5c815d6311736,-0x5e3e29ca4cbb3d5cf842fec5cd7cba3b42723eb,-0x35d7853d2b2c776f5dd8002adccd633337fe32,-0x1856e2fcf27313c9d13dd9e6caba219e01645,-0x8827d4dbadd8ae4ab950f07788e23b04684,-0x2383246fdbb2b4c11b8febd6c58ab66b35,-0x6814bb4c628306d949b650bf9e637162,-0xbf2686c0d69b443e616590446b4a77,-0xa58d01f917f128c934c9f9da37ea]
def m25 : List ℤ := raw_ints% [0x0,-0x52202cca3e427cbc49a750927ed4f812d16a18940f034b64000000000,0x748f0479a879c9751a63e01e6706d05e0d6ab1a9a23ab1339c829fb000,-0x4f6732c15b7bdf9b6feaf044c05961e76899986749e3ee66ec291322400,0x229092808dde35d61cf6cc31fd27097375b972d44b80af3ec11e43c5f500,-0xacc7a068d5bc5876f697271d7b88ce74c297b1e5dcedc6a01e8e3057edc0,0x29406deae3359f49cd02f61d8f049ca6b42245b9f31be32766f8a90202840,-0x7d34c74c801be0f665301284711e9ee840d9cfae3dccb97c9045e911edeb0,0x135efb41819f8065086e59ff7f194fb7a02f68ca3d990b1cf3b7529558dd10,-0x27d593e4a659258d9fa6d6a37eb479373029ec638d908fb6e171f2204102d0,0x44f698061f9750e9b4063537a5424f325472c83dd5fc3438dbb0df6f0b6bf0,-0x6581df62df0e3c3b71c17ffe2fb3a010980191da6c754b677d83628538e8dc,0x7ff20f7b972c7dd9ca2d6324031d97bcefad8795c2593e339b45efc5883854,-0x8ad203ca6b11553320bbfec023f64cd4db3dc0dc0c74bdbbdefa09cde6fbb4,0x821d1431e0e8e56ae7e61191b63c5b808d2a861b32a1ac0116cf518dc55efc,-0x6993fc2c6f811e54056a26e66b70481bc04d935e015288ea68e5c86df61860,0x4a3c7720cb3db9d96b1bbd01ef90573410d2f90a17e839df65003a30b15220,-0x2d3957d85af2692200be5116339b523821844a32d45e15bbba119581c38c30,0x17d6bacafb49035af44715c3c912cdd08a81440d2ed3a934ee425d052dcb90,-0xad90b6b0414480940519642fddb6749f97e8c0488a799b04ac78c91dae947,0x43f207295e0c77fc897a57bdbf3206fab0740b80d2d6499f6d0683c79cec5,-0x16c68d4f8f4be81c5dc7328b3234c0e4b5b369c665771a670960505110b1d,0x67f85bb2ac2c0f6c10d78530d2cce7e8a89f747bb9313d6415bf9876374f,-0x190f5955fdc40becb8b9eb68703a9bf8128c2872877db0c30f0d8e19559c,0x50e4728c1b4105de748cb368957003cafb44b5f95b90ac52df5c0ef73d4,-0xd8190fed9d29ee3144fac3fca3bf20b39c97d66f9d912da0797475b364,0x1d7308c57278e1558cabd869260d022e119b2901ead3fec1450661524c,-0x3387ac4c68aa629f519d48c7255a40db84707de5133ddc0087ceb02fe,0x46dd101fdea95eafbe170050e071d69fad7ea56d645051c7f3305b9a,-0x4aa1fbe23d783e8c3101a62f775d7003b7e286023249a2fedbadf9a,0x3a470c77e18e031f69b4680b12818a3181b60d95892a53054958fe,-0x2060d4fc97bd57792e23114a4d10112d1d6f19c08ad8c9d0f227c,0xc22c0c4f8f88fad0448653874e60884c7e3aa8d2cdeee93e4f4,-0x2dc293daa2c5b8187601f63bcd458d94a5d4983ba2ca2b0e94,0x628eaa288e0e07704544f67a8ff01e9d9b453212dc2ae05c,-0x69ba828055eee538669b5b4ac101148402960b83583cb7,0x2dd1c298ddbd6f20ea43f0d08d02b011eb1bcf5f7b55,-0x596d57868a1895621ed486a34a4c18e31057535dd,0x1605d4313d661bf728f66235e0e38d96fc734f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 20 80 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 80 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 46 indices rho q25 m25 25 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 46 indices rho q25 m25 25 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0xa58d01f917f128c934c9f9da37ea,0x4b82627447f5a012db3de15bc04,-0x21b9a250f1dc4d275b4a5f8ca8,0xeb8142587d8400c1c525b791,-0x6432670f22894ba9c655900,0x2970d7d2bbb45ef775a6b4,-0x109b9c0ec26c72e731e92,0x66cba87e4d31740d34d,-0x263655c58c1b199bfe,0xd934964a23880e3c,-0x4941cee5199a4e4,0x17436f9fb80761,-0x6e2248bf91e4,0x1df42a9619c,-0x75a63669e,0x196925cd,-0x4a6532,0xad94,-0x120,0x1]
def r26 : List ℤ := raw_ints% [0x4cb43b68d6fe01054107082f685e0dbbcebc391dddb00000,0x6989be8d4f1f4cd495cd3807e63ba186df1fe1e8141b0000,0x44319ad3cc02a63179a511799d98a45402dae79816f74000,0x1b82efd58bfe9109b58d653b436d49b9941c0ac09491d400,0x7c5485bbdd8c468ef34a2f0a66e1878ea043570a8c10600,0x1a20e64cb182ae8edd0f81fc158a9025381dc25772e55c0,0x43cdd8cdfb26577807b25e1bead39288b509333a30cfe0,0x8afdb09f2d5b3f7df0128cf50cc61c98b9e48abd04c60,0xe471780544739946a6b4b149ae8499bdc07958971970,0x12fc4008b8250ea0efee9c87da703dcadc9573c2ce2c,0x1483632b6c237a7af3f6ce1b1fdefccdc50fb5773be,0x12037d9ed1b9ec896161babd921c83efe21e7081a0,0xcce71c4862b2681a8cf2f03bc02251d24569da7c,0x74edb9141e0416ddc9a821cc08f5f9c979e452d,0x34caaaa993c01af4376557c7d2f34364e5f62a,0x126e9cca717d463991c1465ec9b116da6c4c3,0x4ccdc78565599dff6c0a1f1013a81fe62f0,0xe0ba3797d845dc2d7502cef09a8fd3377,0x19bf88a6b8ee9db5f8cab04c2e83f5dc,0x16413dca42419a54fca6cbcee0c92d]
def m26 : List ℤ := raw_ints% [0x0,0x857448c8a52c0ab1f7afe2ee0e1a131e944c67f098655a828000000000,-0xbc235245e74da969c3a10f563bc4bebe55cd3ae5e59532a6378c1983000,0x7f439161349d6b120c839b0d419fcf2d007241dab8ae765040502de58400,-0x36fd702736e318166272499e42dc526de1f5c4223562391275059318d7b00,0x110bf682a2898319fba7a18df122066ad264fb31aee587c8c5855b80fa9e40,-0x409671d33f1674a021e4e6cee64f6bc5d770d8175bf99a99cbfe2275adc3c0,0xc25944ee24798d3184b45b10eca5976bc3cc67bcb424e163d1dc7de6abb7d0,-0x1dcb9c97f0bf81aa9baf7aa7599db334d5e7d228d81cdc167702d147326ce70,0x3caee25c5c28615e20b4d8c5ce0d3704c1e15f61b6c7a3091ff99030ca4a330,-0x67fde473a9fb823650c89c5fd4885018082f8f1eb8e0dc5c6df578beeca8210,0x976b6f4338ae863d82935e7f2e5026d48463edaa2982d6b4857bf5d2242d744,-0xbcadc6186ff32bf6c90e555d1b9c2b33666cc71a7acf2f17e5dd3a9ca9e560c,0xca3aefb0fb3e1468e657a68a3f98ad30fb06de70666d31306c6d9e73a61292c,-0xbb18428e4d49198298d51e4099bad5d8bff2575db8759802f80fc9aea9f3ca4,0x95b7ec0624b37d5e97a464fe2e0e4dc343c13e1345dd58f4b36d06ade6a1fa0,-0x67b7fd7975488d8cc9b6d652c4d19af32c8183d7fcf5473c59c34f02985dde0,0x3e2f40b0183363aa8fa8b0c4a9b46324c28f16389b9b7d18e22f0ed1c484cf0,-0x2038d217d2264928b059d3e527391dc786265c671ae110db62d15b967bc19d0,0xe64eb315d5de2ada92cba1ceabfa78e7b7a381ef60ada8ddf339cbf7483101,-0x5860811d575fe03e8c8f775e71ac5c67a3aa8a6595e60be4536590d988e793,0x1cfdad0afbeee35a09ffb248dacbc927839524adf9905270be1d9f8f6c8b5b,-0x8145acbd642f5fa3ae51528850b3da718bafc3e516e03161d49201e827959,0x1e5f2442e71a91dab8dd4536f1a7850fa855480a62fbcdc23db7899ed7f84,-0x5f55eadeafe84d9a5e17282be5c060c5efe06152bd8e4a3a22c1e4219f8c,0xf6fe6ff641cd873b92a77bbffbd25271e98bfaec03adee4e25fb45b3a3c,-0x208b285bfad9e668681193529875f2f6c36abb52d31e7b1e17edb9b4d94,0x36dced8d7b5faa20a1d5103b759db4d8705707bc4c8216dc3650117112,-0x4865e7474b4df753efedee0f06afb6602b28e409c600449d8b0f18996,0x48d4ab7c3bc007e4a2043d7f9852ba1d9a9ae4709c9b62d92d4366d6,-0x3608a3570f0fdbdf3ba63dd53abc7c7bf2d4d9a0734eb30e3db82d2,0x1c5986079da3e42e6a34e2dd769c80871e9ca668bbeda8e34544a4,-0x9f6e311a49d79beb9cb6926e60ea37742e5ecb8cf832ffd5606c,0x22f3ad99ddc01dd7476f2349cd78030ec7062ebf0ddcfd022ec,-0x4562d6f1cb968290c4cbc4c604efaf79460cbd427a4203524,0x43e32599d13e744b627532c1760107fb75043312f8a9a11,-0x1a81acbe9cc02f1d451217d3271ad063f513aacd4de83,0x2df0c7282b32de878b119ead45a5e938f0fd3ac61b,-0x9dd41cf66246d9900c071901d03d607d0fe7d9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 20 82 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 82 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 46 indices rho q26 m26 26 168175799719216474108776652800000 26=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 46 indices rho q26 m26 26 168175799719216474108776652800000 26 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_26
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<27) : intPolyRF (mz e)=rfPoly (C (168175799719216474108776652800000:ℚ))*rfX^26*(1-rfX)^19*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U6C26
