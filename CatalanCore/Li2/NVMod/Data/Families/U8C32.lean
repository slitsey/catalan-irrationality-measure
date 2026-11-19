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
namespace CatalanCore.Li2.NVMod.FamilySource.U8C32
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,8,32,size⟩
def bases : List ℕ := [1,2,3,4,5,6,7,8]
def indices : List ℕ := [9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
def num : List ℤ := raw_ints% [0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def den : List ℤ := raw_ints% [0x525ed8503b2b88d03531000000,0x6e6dd3a7f05e51d06f2db80000,0x4673361b7678e664bdddcb8000,0x1c774a0ca154bb74c45eecd000,0x82de4cb2071ac0dd98475dc00,0x1c760e2df3f029f5c8a748f00,0x4de4d65105c039a128aac5c0,0xac0111054ad42e765101140,0x137e5eeb3fed0dff2f6c4f0,0x1d638014b4779a3ed09e10,0x2527a6f2de14210e48914,0x279db4c9ad3f68a3ed3c,0x23bdb4b04eef5f3d571,0x1b507e62431b126478,0x11aa76a4da1caec4e,0x9a3b14f8fcda6b4,0x469c2fd32979ff,0x1ae54fdcf09a0,0x86b9364a0e8,0x22110cd164,0x6c89f0bf,0x1061c58,0x1c2d6,0x1ec,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0xb,-0x37,0x3e9,-0x1b5f,0x8f,-0x97f,0x3272b,-0xbfb3d,0x10d0971,-0x75b4217,0x4e0139,-0x7ddcbf9,0x485eee26,-0x242f7713,0x321567b,-0x28b1643f,0xbd5fd3f,-0x1338b3d9,0x12f5c113,-0x3217d6d69,0x2ef7dd47]
def rhoDenominators : List ℤ := raw_ints% [0x19b632e31a0,0x32e07c70,0x2b0e60,0x49cf8,0x7920,0x4fb0,0x1fe0,0xe,0x1c,0x17a,0x12c,0x717,0x1104,0x4e,0x444,0x1aa9,0xb60,0x110,0x1320,0xa18,0x2860,0x8d50,0x8595a0,0x60038b]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-9) 0:ℚ)/(rhoDenominators.getD (m-9) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 8
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 9 33
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤32))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤32 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
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
  change m∈Finset.Ico 9 33 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
def r0 : List ℤ := raw_ints% [0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad88000,-0x41338232d71ad1d815492623f9660841648400,0x456ef38570b35397c91d8a2befe455a39216b00,-0x2ff06a8f05c5645c989a2787c06f412d1ccdef00,0x181fc178ac184ff9c62cc60bb59e29fb2199cabc0,-0x96e38bca7f8a4d51ecca5f5694a3355c3259378c0,0x2fb1089a87d52c34084a5aec3525d002115dc24680,-0xc8667c492240b35df8d5d7de14fa5ebd50938df480,0x2c99d099cd022cfd85fad6f41a213b978722a5012b0,-0x8897f9fb6f56510196a107fb97a226eb21be76b43f0,0x16be752c8221eedce69721e2ccd285af9166c4c69ea0,-0x352eff8c8e10dd56ba68a83cbeffa863fea3ac3e3ca0,0x6def9f09e0e65bbe68b424ef231100858e8c5b8ed750,-0xca0a4ddadc5f9a711fc29a5107caf2da557dda61ad90,0x14ba45a7ea512e6bb569548a32469def1d521f1906bc0,-0x1e804bc88ff3275878aa2a54cd51d8ee4d8301cf1c040,0x285aa3fd7915611588942ba895529d5b39af4407022cc,-0x301c7a59db8b3d394bf57bb1ccea7de0115335704261c,0x33c6a199a66ddbc775e42fec28b8d923b26162e280a08,-0x325ac24952f92f2b71184e69d8c95d73c3286952dec88,0x2c4988976874e10ae3b057237522dd45fdebf23eaaa44,-0x233ba9645f27d4e4da7d1621ba642f1015c58b85fc694,0x19596565b0805e8de572e4f19ab4cc4c51271b1a114f0,-0x107bb170b1579e9cdd6db3ce6224ee92aada7e0560830,0x9ad1cc3130e3866f0f899315637a34dea1e9df64032c,-0x51ec11c2dae3a55d5df4a8cd8fe03e83ec3dfba982fc,0x26fe5abfdfef2582d1029cebc106ae0ec4df8f36f7d8,-0x10a6eff5739f972930d6d2debe68313960cff5a06d98,0x65c11c011880ba20622cdd8b9e294f94c8c2f39c844,-0x229e549786382255a2c9fbd84df561bdf7f48919a94,0xa714edf6e9667347506cd968096656766d5c1ed060,-0x2c6f3a80eae7b05b0e0c3b6a8de1b0194e2ab0a800,0xa590f167fb2c19caa15c84d95f13938bad94a1524,-0x217ced6b340644c5b35b55715b84ceb3d040d3854,0x5d3282d70f5d33884a53943d20172e6aaf5e1798,-0xdc5ab3fe9c3f7b1b0da5416403c661fdaf9c918,0x1b406c6614803d77d55fe150820136c4612420c,-0x2c487d418b101def084f803755a4519e9a01bc,0x39acb161acffd79a5e27b0619734f14412690,-0x3a4e9f543775116183e66115b280c8e5b0f0,0x2bcd725b4e279c0aa521e8d17005fd57454,-0x16fab543ace30c88a1244b1b4d0e3cae04,0x7a9fffcf905bca6b783e90b4a04f9d88,-0x1646ac4307a81349ba398ce57762148,0x1a5bbede60d5bf028e135b175543c,-0x6449713edb0815f076e31b9a6c,0x218091932cf96b2153f240,-0x10c048c9967cb590a9f920,0x6e5c39e4d062ca4fab1e0,-0x24c968a19acb98c5390a0,0x9ae43f4a1ffaef088460,-0x1efa730ed3322fce80e0,0x46cebdd8be2991d8020,-0x66fe2b69cec819f460,0x47a5aee56e74f0aa0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 24 44 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 44 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 56 indices rho q0 m0 0 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 56 indices rho q0 m0 0 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b100000,0x80f998fc2db0ef8385ffd9d0833867965e95c00,-0x87d0d497adc6dfc5b9091b7e84ffeecb66e13d00,0x5cb4f38a179e79d4cfa0229c3b92f2c421287df00,-0x2e1cbb29830f1efe9193db3840d72cd8ea43e77440,0x11d03d15b82a226a805f9831473b90f9a2c32e050c0,-0x590018dce962d375b9cc884d4b68a8fb4bdebbc8b80,0x17162b63a82be3487adb1834f93c74b5faf139465480,-0x512db527fdcc70efb01a4c7176992870f5106faad750,0xf56dcd5747c61528ad16088b81a2b01fc911bf97bdf0,-0x285496e3bb84856eb9f5f4b03cca58861577919f9d3e0,0x5d0afb6612ccf87d560b4d2658da2b5eadccfdd5de220,-0xbdb0ca0d568d516e86f2997385c34bbd06f2d19707d30,0x157b6cd9a5b5d9dec9405946bb7c5154d243e789787d10,-0x22c116ffa9b8f84d7bce43ccd411d052bbbbb86cdf3d40,0x3262d4769f83cf5d2ca331a6d75f274b2659ea552dd0c0,-0x41a6c0815e163b37e6ba727033c3bba0273e8cffb67634,0x4d0d39241f67df9f1147e4b4ae3ebdb909e0e325faff1c,-0x519782e238ef2552c387221dcd76af599f21a0c0e81718,0x4e0afa56359a7553de997bc8a3342118ade1a56593b368,-0x4378f97e5b2304111b4f1f656fefaadb5a958bcae3af5c,0x34bca95c7c67800a4b43add5a87477022b812d4bc37df4,-0x254169696181d5580966afb6d70ca51f67124a7bbbaf50,0x17c57986209744eeda416000580ac9aaa19570ac0cea30,-0xdaf163755699d915afc8424f1ee56a59908d0e93e8b14,0x71857ed9864c0cd1740b8c74b88a4285b7e725df6897c,-0x34e7942753b7ab6ce09916f0b4e96741476e26eb3b408,0x1619e25b80d59ad5bbead00c4ab279d3cbdde90fb66f8,-0x83fc6501618b373ecb2dcc8c66195e8679855e16521c,0x2bd6a7d3fdeaa132ecc2e557f67615b0bfa531ebae74,-0xce525f3459e57a995ef734d09320fec2f44def72820,0x356fea4f2d832ac3a0b16f3c7f7a98a75d4c2c660e0,-0xc1a18037dd4c2254f4c28d8fe6180f494f3c804fbc,0x26064d40edf89e1f66e651cd77bc1913e000fa0134,-0x668d9d3751c4a11a7cb7ad0cebd6a867ad01b4a28,0xea7c91baac9450478c39667e30e4641cf9fde258,-0x1bf9b3428a466168831d9a98c70751a78c7b1cf4,0x2bba75c019369c018384840abfba813388a56fc,-0x3698f151ea04d10b9a74dd417afc2d33fdb6d0,0x34b296d1399b1a6ba3ba9c06162945d72a0b0,-0x259b45f4670ce849e7919e73c6935aef19ac,0x129f8dbfb228a9fb1719e9860c778622644,-0x5d0de9a2146e8d20627c7f8a8d45602d8,0xfa94910ecd25f90e7882e2a6fa4b128,-0x10edd4e9b2f8f2412bdaf1eddf2e24,0x39c8f149c2df0dc3c8447cd64cc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 24 45 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 45 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 56 indices rho q1 m1 1 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 56 indices rho q1 m1 1 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb62000000,-0xff2f31dbf260c1f08d23f5d99e42b7e2aeee2400,0x109c8ad4bba965ea2033480b9629d1cebc85e11300,-0xb366fe78d65719cd8f66554a4a901a8a93f86a4d00,0x5838acbefdd4b3c08ef8c7f7c61e4d7191dac3c4dc0,-0x21af8db7d1aabb6cd8beac925585a86036e8eab58a40,0xa65027203b7fcf75d1c38c56f680e1609ced6a574300,-0x2a9ee5d6c45f7b52d1f31d82a741d8074473b59349100,0x940470dac9e8337cbf8510985630f6fadbcad01ff8c30,-0x1b9dcc96d026052a26728408e67c5c46041ccd832828d0,0x47ac5d2de7381f0e9dc9d703e6848788d28207bd849740,-0xa32b42dbc5636f8e236596d9111887799107fef495e5c0,0x14829b912377b3c1df664180e57e7acd079ba9c0ae308b0,-0x24a627099ce530368809fc4d672ccd92d6fc60a4a12ca50,0x3a72fbaf54f40264038990e3550737fb35683999188e500,-0x5380acf8d4449137e671fb21de7b833da53e9661bee8900,0x6b2bd38b6168725e22914922fad177d3024715ae863c20c,-0x7bd8096944076ef7b756183417deb8a70ec532a9c58e834,0x810ffc945fc3bc2c3083d43e770a3b248184590d2054fd0,-0x796ece034d3be0e9c2dec06f4c7de56d432e47a50da0070,0x6737be6bd70b17484dfa130dae098ecb8631d923bcd7f7c,-0x4f45e5e3080ba7373e2ab5cbc38d07dfd3f9512cb295144,0x36fec98c8d8982c6e300fcfb6d1d32e5da56451377f3cc0,-0x2270108850657ab4d3b91ab38f0e332a5a65010eb2516c0,0x1371182dd51cfa314adad9d6ed9d5cba2a28d59b0c8e35c,-0x9e0f56c8d4dbfa01d8acb1f04d89fe8d64d3835907cce4,0x4820ad7a5e63310c2ff91745ad49c1101301c8b0695710,-0x1d7a68f484a96de0c6a6390de9a781bc5f6c151b2cf5b0,0xac0e34df7da11af15da0136db5cf4e547818435cb4c8c,-0x37cb3048d00a96dfdc912e47b5f70f9389d8471ad7234,0x10010411790fdf6222cadc155d9d23da13fad3dd07700,-0x40964bde138b877932a95ec08970ac7e512518e3cc00,0xe3949412539a72e7ceb129119acfc0067c90cde6aa4,-0x2b63137aa27dc237bb12183a9791e7cbd2848e7d21c,0x7162ad075406537260ccd47b3de005752d96bedcf0,-0xfaaaec6ad0d949b0631b20e769cdd631667a1f4d0,0x1cd7ca4b35f0beb2dcced8f8593988ce42f4dab34,-0x2b5ac1f9e2ee4c3ce8173d5971eba0e63f40d50c,0x33df6e87954e2caac8c2f562d5bd81257ff4040,-0x2fc75791ca83fbc5cb90057993de0d90387f40,0x205eeaaa896b5e686ca234d7c51f28a6d9ec4,-0xf1f37a66c2b004399a6ca9da06743b2c0fc,0x46b26e4e648015ec9ff9a7e8a550ef35f0,-0xb03e3231cdfb4a5da8104c031722e650,0xadefa42728ba0e8db9c0487cd07754,-0x214942af194c490c690e99ddfdec]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 24 46 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 46 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 56 indices rho q2 m2 2 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 56 indices rho q2 m2 2 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c40000000,0x1f902a380d94f5b85847e2c00e2ac22a5e24565c00,-0x2085b974a21080e3896c3449672def80511dbe9ed00,0x15b67a1a474389e92ed0619aa83bc668ebd7b10b1300,-0xa8ef504063865e34e221272832613d14706349dbe840,0x3fc58d7e65f8b41738f1ebf4de58f21fbfd4522f7ddc0,-0x13733048f522096be88e4d706efef1df33468aac567880,0x4ece043be7972dee5ee987f754f1da31be9803bb480f80,-0x10e5d1193be56458e06717483e9f4a01db94dbab20b2a50,0x31d15aa06fd989802953f53f49f14abf001961fd7982430,-0x7fa6fb2bb641e87c74444aab45ec988ef23773d53582220,0x11ed50d88e1a1728a5b9c5cc94f2dfdf318ad721a4fc7fe0,-0x23930a3d881f718e3253fd9c5221bf83305d0611037d6df0,0x3eb2d7e470fc4424f9fa996ea2f55d8a1cc48675ddc6ec90,-0x6297a3848d884f52d505edf1572ea398c91dc1e1907855c0,0x8ad32d154592471f63f838152d8e86cd4c6b5d925cf03240,-0xaf899e8d21d32bc78e53ccbd1fabc52728041368420ad6b4,0xc7c1e8e38ad63c0c767d0e8e1b8dcb9040e1f170b3bf85ec,-0xcce915032cf2cf470a822c82e0afa27c23945c4512d8e2e8,0xbdae2c8e8da2bdb30d11355c6ec3cfab9743630fe449a798,-0x9e89cacc18af078c354a4b2bd53bf8ca06ccad44a1a0034c,0x77a94aa9d35c442b6360e2a5b6ac7ba2e9cffeb3709c6bd4,-0x5188b685ebbb56586437957eb37190914d6284134ac95870,0x321ceedd049fd8050092af3a36d45e897cc099aeeb4a4d90,-0x1bbfc01308415139e31a0c99ecf7bb9463c1b92df67f0874,0xdd1ac924633c7b20041d0fa8d19a5ff4bc04f2af2e2f5ac,-0x62ce387148e8d32bef6e018a125aac8c990c93d18d93138,0x27822757d955303b9907748f39edd72d83800fdab157f48,-0xe163f2e1d9ba73fd17f2217bc09229860cbad950464b2c,0x475c238a7f6c85a2179a48a83605410cb6976289fcc374,-0x13f5e730a0b58b5409cdc1740400464ee82bd3125c4c60,0x4e72a45175780e7120e32cccd24bf94ba78947e265ba0,-0x10cc8d145cf90d15a3b33ce91040975a752bf3f843b7c,0x31bdf740e0ab515d54ea5aec19209e70ab5c93853a64,-0x7df187925e893436685bcbe27020409f29bf8c85c58,0x10d2895c47f352b7536eb7c1f48a89309d86faeaf28,-0x1ddccdde99e302b1230847311bec4865ba5e405304,0x2b26c0bd595cc0a8424db1a14e413e587f040285c,-0x3174fe306df1947b4b7a3a1e56ee8fac0e8fc9f0,0x2b7345dd9333ef7e84e1ce360084cb2be335810,-0x1beebf1d56d6f6c43c5a87625d595b1324ff0c,0xc4d0fe79d36a809dc24e3b4f0f682dcd0dd4,-0x35c4ca0acfb00c5b72d3d0cb8dd209dc368,0x7c005f63ecc93a74a0ced8302f4efd418,-0x6fac21c1b4f74d76d4b284c40634454,0x132b2bc6236409747a2139ea31a0c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 24 47 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 47 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 56 indices rho q3 m3 3 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 56 indices rho q3 m3 3 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad8800000000,-0x3e7a382970c7188d996c5749837433fdec516752400,0x3fb38790e6006ef2598a01946b1d6c504e997c167300,-0x2a12e5ce48c204fc4582cb395f690ff394480cac84500,0x143c73dc0d69f524bcedec0a69bce7daea902960f08dc0,-0x78dc7a5388d80880467a04d89a3433a9ee9d3281e04840,0x24712432ad741eb98d71a0ad2fe3271067e7c4919e4df00,-0x91ee5c13f7a193b8cc7138f097282ef302166017d7a8d00,0x1eeb24d245bf2b7554b63642267d62f08067ca7c000d7230,-0x5a0ae0becd3568589bf0c415557a57a1290efc505cbb1c50,0xe3d7afb88e9a6873b86bbe03d318c349f9d8fdbd1f7d8c40,-0x1f9683e951352198b522103f449456eb7329707e7f0959ec0,0x3ddc5557f31cd4cec2e060cca92f035111f1b6597f0bd6130,-0x6b8f2df5e2a9e5f38c80694dccf1d90b21386aecbf04f9a50,0xa6cbcf93a73b81205428185722e75b0b26a1c747bf6a38100,-0xe785d1de868a0ede25cff6f1d3da4ae2a3d88484992654900,0x120783cce79446b988d92d79e1c0f0010322b413bd2b9c1c0c,-0x143547c033cf6f3488d36737b9c6ab8944f8c25d91ad20ab94,0x146867c1d8be0beb2d064cab427def2e23b920b18a092aa010,-0x1296b20052252587f9168c3541af4b1dacd6c9ceb046527bb0,0xf47a77da7734ed8c3f4b7d07786adee898fdd9a6154e6581c,-0xb55f756926ac00780b4279d287e75fe95c50d23725f37bc44,0x79653feaf6d7eb50ef4bf9a3e685448fab88c862f4c1f65c0,-0x493e6dfc6ebb378faa66520492109da54b00ea99b353f74c0,0x27c8d61b79868acdb24370401404c90b48b5bb034e44d579c,-0x136b8e1d31d8cafa239b6ac574f857a78e259e9109dd82e04,0x87fc984b1369df374e438128e8262323e6f8a0513a947350,-0x353436f4cb0455b6903ea7b53c3c398e012be52c0a1403f0,0x128ae31c0a9b5218f6b88b6e02e04985b3074203797a53ec,-0x5bb6087ba27bd791176cce50fb48bd382cd04fc3e499374,0x190414af029cd8f09e6ac317a99094c6f72e215cbe2ab00,-0x5fbe03122d62719315f82bc3998b3fcccbbafaa623be00,0x13ef5914714c2fb186068359e116b3c1dfe821dadc5424,-0x394b33b29a92c4910e2b9861912eb8af42e99444379bc,0x8c8654d7184aaa11735915b2cfd225c303a9228721b0,-0x12243c1f3dcc90f4fd992ff0f7dc7eb759be78352090,0x1f0b583e86ddff5a37f9418ddcd80f78545137ffe94,-0x2b1c65bf0c346967d29ba580f3577b7fe7cae8bb8c,0x2f501a055a8254ac6b3cdd4eedc8421f05fa45340,-0x27a0ee06ff74e15a416370bcf037fd5925f94b40,0x1828c4150bf4efe0a6f1932059f80e6cc6ef504,-0xa05f09e168b81c786c4a9a801fca6d8943d5c,0x28ef10050d93c35d2041766ff909d0f987b0,-0x57454807fdee1c830818d69e8acfcfa810,0x47aecfdb8fb5479fe489ebb1fa2cb774,-0xb092303d7743980eeb3e6255fc12c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 24 48 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 48 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 56 indices rho q4 m4 4 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 56 indices rho q4 m4 4 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b10000000000,0x7bb29989f76eb883360409093eb3dc53a5b3b82f5c00,-0x7cd372d8d3df825829529c00820fbbb24967fc98a6d00,0x5194ee793d2009fe3fcb951fc530f8bfb5ffb395db0300,-0x26d1743e48e78b6bd5cab8f9a6991eeffbd93905de95040,0xe54eb49590eb6011583793dae1354e6fb59eed9174db9c0,-0x445e0e1829472d3531adb294e3f3349bef61229f41536e80,0x10ea4f30f9120aa7f759b4b63715902987654783c39957980,-0x38ab99d5e981a8c61106c73c1b7de8bd00810a982a665d650,0xa30f3887ce146de92d65c0c0e28bd90d22881232c7d787d30,-0x19788e126fa2815830c1dceaa443c349d8bc083e048de143a0,0x37c9dfde0c695a5075670fce9728721560d35e3bd9f650ce60,-0x6bd789748687945bae3090c4680628063098e505a30ef99ff0,0xb904f8588c8b14f9cf50a7d17d70fd724f91bff6467bc52390,-0x11b0096173834b38fb485bf58a9b7c5e5f68bceb8ae52411ac0,0x1834fdb082696a719599269d710bbcf4cfe94af50485992ad40,-0x1db9b8ffcd183c56db2844106f6c36b93bc72094cfb8bd369b4,0x20d2638b5b001aa530b01d2d694b134073a1be57087cf12782c,-0x20a32db20585c8eea5ea3171a6f1b40cc92f59abac2fd5acec8,0x1d41c73433e5a2477e92de55cc9f93ad0513518e76fc0db73b8,-0x17a7c19067eae098ce3118a5bba0ccf7278beb5971517aa29cc,0x114076d16e7f2a438b0565a7b534759b7258eb5713d4cd66e94,-0xb5813707f38c94636e5c3e6bde5bb539d12545bbd43c9999b0,0x6b83b483afb092b529ad3282eac18e5a47998f279d1d7a4c50,-0x394b1286cfe64fff66b562671ef49c962157fba4fbf093ed74,0x1b6a4c5564a87c1414612f1241e948e75c779823e57bb568ec,-0xbc06033451ad0223e5583303a6af99f6501d6664c1b2475d8,0x47fb8508ff7cc411c31a4e4cf1a95857b0965bb905882a2a8,-0x1885d77eb59889d6ebc14f754d3a808352597e3785ada14ac,0x766d0d537b96eaec75742da990bbaa22085f80470e3c4a34,-0x1f80222f6a72af54aff0259f40a2039d8adef3fdd2f93ce0,0x75667e8422c1b31b3f44369b2061bff3f0c72fc8245cb20,-0x17c42cad540b4d3f9dbebd1c971a17d9b5aebf65a58e07c,0x424acadb8b59b4b4c2a702ef88e488e69ac589960f5524,-0x9d7c11098739f4b28da14cf776697bb75fb8f70130578,0x13a57da3252b3388e94918d9c10054518d33038d17e08,-0x206689d62927aa3bae55b6911f1fdff801681e3ef884,0x2b3a283e95ae5fb38c4c9f93cdb48f14a40fb64729c,-0x2d689ba183e9c90517d3bbb7676e464103c5293130,0x243e4771d8d0557e5e39d8aa5bd2888ddadbcb0d0,-0x14f11cb643b058cdce2bc0319588022653478e0c,0x82e16b7e353f693cb7a8d6e230f76a9a5aac94,-0x1f30c13258c0347dd73bebb739d3fa4c4f448,0x3d6f48d0baeab220f75901833e6f92c2b38,-0x2e00fb6edc43174dcb4d6adbc1cd8bcd4,0x65a0a77b1eccfd04854b3a856fbb4c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 24 49 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 49 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 56 indices rho q5 m5 5 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 56 indices rho q5 m5 5 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb6200000000000,-0xf4f5a2eea940775ff22c11578981ea1168b834dbc2400,0xf4b586d27bb22d114ea2b0df67c3f5bc832ca23c6e3300,-0x9e4a796d3bd414110768e70b113f26f11b49e18123f4500,0x4a870f97bd6d051c5f94fed4ece2f71977c0e03d0cc9a5c0,-0x1b3870d5ae6970690cb1c3da489224eb2bc146f1c1536e840,0x806d21e231f31e1392f973dbdba5ab28390f00855f07c1900,-0x1f6afe9c15360bab018ecb003701750481d6d0a0992cd86300,0x680c05be9b3b69a6f847797073e763bda0f8d0775607ac1e30,-0x127d940d580618c8a34b1ec109beaee6125a38c511abc115650,0x2da7a0ae08f65d024afcaa01d709f8b0e1c4a521b9f6979dac0,-0x62c1b7b608fea99dca1a6ee07fd7d92a4d2061f0084c2c0b440,0xbc7854ff2d32ea5a4bf1f19a47f697718374ab062e72f230530,-0x13f1e16c4a537ac3092e0c17f6579b3cdd238b98c405ad92d050,0x1e18bfa2059afb7b7b2dc08a7f15148c3d1a13da0780405abf00,-0x289e8326776d1c1a8e0ff1e98c93881eda011111f5f407c08300,0x312ad86bd6baffa03d64922d1407bfeb5cca1f9c7b95f059340c,-0x357d71fdc4548844171f9ea111204792132b502abdd8f25a1114,0x3461b1495283cd1444e9f9f098cad57dcce673555be8a4251e30,-0x2e381c0c09491f404a3e7e8f5fb3fc09eeaba6ccae951c9a3a90,0x24c35f9bbe7457db2748e3314120c57ff8621e6f553f554af71c,-0x1a5c4d6127ea1a60b6b07b43e6b243034993ed0ce4ff907d41c4,0x1108020f88bb863c8f1d9b8c1ca97efb0fd922ca3d68a8dd0e40,-0x9e7e0a9f98971cb745104b863929c40d97bcd81ba19fe17ea40,0x52de1dda477365d232e3cf7e52f9c03a0b63463546096f74a5c,-0x26dfda9207850014bde194d6c681d9c1fffa2f302e40c3150c4,0x10527093e0b9d603a4ae30f2dd8eeefbd329da21b9c50ff57f0,-0x61d63bc32a6be73dd544b84d2566ac32eecd625fa66dc4ae50,0x209513a203a2bc4ed1401a2f07286201f939dcb1ccc1a4e32c,-0x99a2986640fba138a0a0c58a4b3418c1076f06521523314b4,0x27d9bb72c81e9f98d183282e8aeccded746a29b3e417aa700,-0x909f4c63558792d5633062f118e60e4dc3568a0382204e00,0x1c767c4c6b31ff331cad8d204f0c898ad43c53b988bee3a4,-0x4d0b5a497e4c97a867db06c2514aa3eff59d4cab0f7e6bc,0xb13f99c6390085f8b996166f902e42e3341da9a2b42510,-0x155cfa7153a9648079ffa7c65a49a336e893cd09301830,0x21f213e54cf96c60aa75de963e8d1693b0523baf61814,-0x2b7ef5093497f4f3697ed6a468bdd258c8036bd3fb8c,0x2bb78411ceefe10512affb52fb9ff50c5fea14e16c0,-0x213c1bc7b0c583012837058cedebc08276da0635c0,0x1230deb40f7748a0547cd0f17fe999d19af985ac4,-0x6af83d6cfeeb87902e360ef3fc62a0ded14221c,0x17c912ba428ed8309442e0a0491ea0746f3310,-0x2b417799de125d1cc798fa4e6ce3098d31b0,0x1d84763a79de9bff07dde94fb8cc2d07b4,-0x3a7a467ca68ca08e276b5955759906c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 24 50 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 50 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 56 indices rho q6 m6 6 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 56 indices rho q6 m6 6 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0x525ed8503b2b88d03531000000,-0x6e6dd3a7f05e51d06f2db80000,-0x4673361b7678e664bdddcb8000,-0x1c774a0ca154bb74c45eecd000,-0x82de4cb2071ac0dd98475dc00,-0x1c760e2df3f029f5c8a748f00,-0x4de4d65105c039a128aac5c0,-0xac0111054ad42e765101140,-0x137e5eeb3fed0df921084f0,-0x1d638014b477983018ee10,-0x2527a6f2de13d0d5b2414,-0x279db4c9ad381e2243bc,-0x23bdb4b04e7db692a61,-0x1b507e623e2c8ce378,-0x11aa76a4b19f58866,-0x9a3b14e94903a0c,-0x469c2f8893d8ae,-0x1ae54ecc53a60,-0x86b9067172c,-0x2210a68514,-0x6c7fb919,-0x1055f58,-0x1b982,-0x1a4]
def m7 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c4000000000000,0x1e5331e951ba0cb0d583de144da7693e06a3ce669c85c00,-0x1dfef11b334dc92a8ea6c574f2d2fac421721eee3d622d00,0x1335315704a1d4e88ef5dcc0c7fd59d5d98ddce3deceae300,-0x8f3560225662866efabbb32c86a04342cd751e99b5068c840,0x33c1538604135d7299db025fe52b9dac3ed9993b36451dd1c0,-0xf18d27abaf35496616eb51076828d9d110a923f03d41dcd880,0x3a70daa28c0a8492728dea31805956620aebf9691ad42b0ff80,-0xbf59e2b55e8d33db75fb6d74c876a32d34518d04891c725b650,0x219c8b9f3b39655717b3aae422d3d0d54d94ab0273d791c09130,-0x5200b796281ced48d7721b820330991e21c0e5b0257e216e4620,0xaf373266ed86a900f6230a15b6cd1a3ec2ffe5b66fddc87e77e0,-0x14a30c82002bfae1e4a5f7b525546efb51e50c74957218de2faf0,0x227dd71c1e1d92c0ee5efdb6c11f4b44410268a25a05da8098c90,-0x335b41d2ef5dc1ee2b0835d0a8b324ee537c823acdcd6e6b585c0,0x445d2a6ac6fc703ca7cdd74c931be408a4b2adfcb304014ff5240,-0x519586589f5c7807bdacc6329b1ca5bb6cc7f59588af83eedcab4,0x57771be4a31f595a1498e17d35d1fed84bb35b277be29217d1c2c,-0x545d8d54b6dd6f5685ca8de7225a8159a1dadab82f99e7d6f0be8,0x494882911ab10f611a74ebb24f5037835020b588952c56ce45598,-0x395a29a4c0f483fe99fb0131a45b623de1ecef64fb47ed47a9f8c,0x28700afaf361e27a8405d68c0d86072643b36668e0fd43fc345d4,-0x19ac8ac55fc1e647d2a4b3a1e914cad793483912cabcaa8310c70,0xea9ef352d7cb164f3850954bdcc5881c693ad0ed5c0c05d4f590,-0x785f70ff7c94474761125de5a779fee0194dbd0957c5089dd5f4,0x375d7ee5fda99adb85909ded5af642e1b3ab8c02e13f787f8b6c,-0x16c578a08568791ddc1d5f48a9ab509a7f88988c9cdd3d4e8438,0x859402b00cb7b69f03ae38e55d546386b3e4cf24f368313cf48,-0x2b7cdf841ef3a72e4aacc2fa3f985a68a3adccedc3d748463ec,0xc8390de87adf139a15f37623234d79931c5a77e2c3ba3a61f4,-0x32a4c524c47bc0217637b85f38f42a898ddb50b53712d88460,0xb2f5fa9d5d979ead05761b77ec3b41ff603afb9ae700b23a0,-0x223d2979552f7b8f281136ef61cb9dd646799c3c6d5cc287c,0x59eda787aace6ac85f89676215f9a25352298ee13e658024,-0xc8536684e41469a2db2fea2d1a9904db97825aec59db358,0x17527e24f1cc19ca92df481e7a8524e8472cc13308fa528,-0x23b245b103a9ac790e237be57355d551a785941f9188c4,0x2bea23484a10b1aec3d84240160b931980ddcc5a3b55c,-0x2a36cd4589d2f356e8a3432bfa14c5105ec736a65df0,0x1e8d8af8290ff88eef9a20766f2c01dcd49131e4810,-0xfd520ef7fce70b81201337eb9ddbe1476ea2efc8c,0x578bea2617aebf34d31f68d369cb8c54df4c2714,-0x1226d6ab355225133771f1259447c0a2ea27c68,0x1e75ee3a8f13ebabaad36084cb9a9264fa818,-0x12ef5dd9e324d8d628e15e5f6a5fa66b494,0x21a3dcae6b5ab284bfbd0893fb10888c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 24 52 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 52 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 56 indices rho q7 m7 7 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 56 indices rho q7 m7 7 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x1a4,0x1]
def r8 : List ℤ := raw_ints% [0x87239ae3a1136c75974464000000,0xb4d9d067361f92b12631d0e00000,0x732696f1666dfbab7710b4260000,0x2e6d42469d388aa52d6ddeb9c000,0xd4ed4133499298b4418f2702000,0x2e2ed0f6b22eea165f9a2c4c000,0x7e040eba0e305bed0a2db7e000,0x1155372879e6818a00a5b18740,0x1f4f52a8ef9616c8337cb0880,0x2eff58334415682f7c32cd50,0x3b1ed5e529118cb86d7f6c0,0x3eac422bb25aca9f96125c,0x38296124a6ad365e7e9a8,0x2a94340e31308ec3aa7f,0x1b46a2c051f445ecc80,0xeb5e77c3cd36ff6ea,0x6a348d27db7bec50,0x27b6740df17f1d2,0xc2228e452c240,0x2f7868a070e4,0x9001a87448,0x14186c747,0x1de47c0,0x16dae]
def m8 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad880000000000000,-0x3c141710e4cef50f0c108e3cbe75b7b402c85fe6cf432400,0x3adaa4d83721a2421878e65bcd973548747104965180f7300,-0x2550dc1955c9f45e1ac4afc350cea6bec89cddbdb66cc16500,0x11369f583024b8f3820cbb7f3e04d9edcdd0544eb0b26505dc0,-0x6281c8f930cda3af4969f90e1b7bdbff99f9e4a10217b5ed040,0x1c6e483324a5212eae7f64bf51840ece26b6af82f70b7eaf9b00,-0x6cdd576e58c0ad3a5b1a05523a2fa8019e34e44cf30b47339100,0x1607e5b128e5792631c2dda0b1f54872cf58c518e7fedee0f8230,-0x3d360fb57d03b1cf104947eed9321cdfcf01631da37db4f070a50,0x93974ce87fd7721b4445f45aa853c7b96b3e16a14ba97f302a340,-0x13791172f24e9dbba8eb7f5dff21cf4720bfe9c2af1316191557c0,0x243e22b42928a84a46084cc9c08e043561b86eaf676ab9064c4f30,-0x3bcdc652d5d7ff5a9a65f8951eef8762a1e323b5d33e8c18b33650,0x57e0f421b920e416bcad1e0df856adb28f3fee8c1d644ee1861500,-0x7366bba0fa1575891827122b640d0298ab54e433d1035b052fb500,0x87cc77bae01bf16b40c68bb575e9af4027cee231faa300d3d50c0c,-0x8f7e451c754228c09d3eb97d4944ef4215419e79b959e4c6db8714,0x88595193d64e02282fa900cac371c31f579d720390d39bf12b6cd0,-0x749d65f42c129055f6349f13f5a8b62d6c7cf79639c536b6ea2af0,0x59cee0dc825fd4f52eee1f29e9cac5cd4204402d8585276629359c,-0x3e460be526cb25f6ec1defc2d8ad6f42f9febcf2c0bfbae6e1ff44,0x26dba10079211d93e246f3b092c119caf71e37a61cb509651d80c0,-0x15cbff602871672aa7ccdbe3932aa07c163babbeee3e627754d9c0,0xaf977fec435cb13f3405eb447618316beddfdfe5df462473d611c,-0x4f3113b6ab5fd24543f4a667b03ac51e043caf3dc9c019f979804,0x1fe88a2413f2363fa08dbe82a8f898fe12f991871a87c464e5310,-0xb72f8ace3696133c8d8e11fa825d443e70feb41ee6f09fcc0830,0x3a4d871929985cdca9ce964e404fd9ff063e5cbac31e21315dec,-0x1061b5e7c19e3005fd386451232271c3a9080e10da13015be5f4,0x40a5b8252ceb3268e9d1d6fae7e4c0bcc7c3dc60ce62e5a1300,-0xde6e7c5234074de82bf63aa44add7d77aa47896da3f8b81600,0x295db20d2c1ef527e7bd1eaf16b53fdb67d7ace54affb00724,-0x6969153b8c38a765f0459227dbe7a7de3269778fdada02d3c,0xe35413473fa1b0ceeef56050690774871268de069ae1c5f0,-0x198f242c27030bbe824e73cd6318b7abdc727a4e27e84050,0x25ac1c6832bb319d82d1a3aeb642598991ed627d628c814,-0x2c7b6ba70f5aa6df3574ce09f90d91d3c3d161fc3f2f8c,0x28e143834df3aaa4bbdfe28a05e13800e30855a522040,-0x1c27a63ab537baafb6ebd2cfa4a4669485b7c6003e40,0xdce3afe2a289b3959d48bccefd74a4b59f11609084,-0x47bdb29b1d07ebee81f924dbd55747ab02c873e5c,0xddc8906550fe8bc12569ef98cce3cc9b46d7ff0,-0x1573ebaf1ae56222f43a4040ab176135bfdbd0,0xc24cec49cf8abf210d92a4527599bd2f074,-0x1358db4cdcbceca1321d4c47f8be6abac]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 24 54 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 54 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 56 indices rho q8 m8 8 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 56 indices rho q8 m8 8 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x16dae,-0x1a4,0x1]
def r9 : List ℤ := raw_ints% [-0x75a936e16ae549a7d95b044e000000,-0x9d3681d16a3ac75554987c07100000,-0x63ed4ca3875ec7178a081614f10000,-0x28364711653508e139e1bf755f6000,-0xb809124d8b4e7080b5e46340dc800,-0x27d2bd33f4bfa6773fe3558ac1200,-0x6c614a0bc5220c308c8b7d406880,-0xedd22d127c665cb77546bcc1980,-0x1ac319c7666c07fbba054d283e0,-0x2805e2140467cec9e2eb5d3660,-0x3222d4788b744e4cdd693e248,-0x34e4da961a86107f51d1d408,-0x2f23016d753b44d33771d72,-0x2381bed5b60c6239d777e8,-0x1692c9c4cbf41bc142885,-0xc1086e4eefcb01725d8,-0x5626c6dc56d5b18768,-0x1fc7f1e7cd7f5be70,-0x98bb303c8b833de,-0x24874df8ef23b8,-0x6b92096183ee,-0xe666e84788,-0x14276c42d,-0xe082a8]
def m9 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b1000000000000000,0x770cb96a683df3be042233808106cb84713a39cf319215c00,-0x7386364d9d8d75663042a0d8783276f7fedb2f1f9bbd06ed00,0x488a63697d777c67cca44ffc11823149b7b927d8333c9218300,-0x2121b67a0bb58021b1467aa27c0c646106e520d35383a569c040,0xbbaf53eab5282e443f5c3e456fb92efa7e00f4636f3218a999c0,-0x359b819a441a2de878b284fb2d9dbc28d4a1190b8a8e584cc2280,0xcb161967862d7bc7b65a0157471f2f720ebe7b50fc1b8a8b16580,-0x28a6680ab90451c1f9138bd3b9a3024eced040f7097fe32aee2650,0x6fad8fb6367db135af3467cf64551b3ccf72fa70a882341fa7d130,-0x10a2d0263510619b394903569958a577b55366a99c0275674f3b0a0,0x22b401baa67f3f67836d3f80d2c6b0f06e0e920f311783fea88c960,-0x3fcd680f925726f5aad99dea340686a8337c2873babafab1ba379f0,0x67f5984d2d10aa166608f9293f4605fbe72bd3ee96dffb7b17f1d90,-0x96c9d72bbd0f38cd42cef40e76242ab95c62312180cb052e1d7d0c0,0xc35f8ad6922d291fea86b698dfc5bf888d78901c2ef6c101f7bd740,-0xe2bd8e88b2f0eed00e00688b58a919fd105acc7792b2482ffca93b4,0xec2db71cc1b7681b0401b07e630f7a66e688e03141663f1c79a772c,-0xdd1d90a0047cfed9b6f4f2155a9f7fc6f13a3401779b66527d23b08,0xba3aa38101f86e331d6ef86b35394af1658f023d06873e870a24978,-0x8d26d7669acae2a17ca1b57f1b8960ff6657b320fc6cd77b57f524c,0x6044b6d943fcf24fd5ac028e5607dea889970277ec67f154b5e0714,-0x3b0b679d1f8c1f705a5e71195860954ed8631aa759065b21fbc8730,0x20880a11551c1c05664ab022eb0baa9839f759b544f4e315ba7e6d0,-0x101351661da3150579e1c78a86124565fa9b61f75c83c78e4841874,0x71c0afe79258e746d9a3689c49a98df40de1f5ff3cee14fc153eec,-0x2ce7804b9944f612b2c63b7f0dea0e33e48591e28774e0c9c8e498,0xfc4fc386dbeb49c6c3768793cb283034462e9b35ca53160227de8,-0x4e820eb27e2bd1e93f7e063aab069e2dbbc54e584dee5d1aac62c,0x158a035c4440f00932806d766e44b50e7f2b7f7ca36034b5059b4,-0x52e26351d5b1eb937f465e7bfd7f08177a44b5eaab4f67c46be0,0x115a8548a954547f35fa9d4fedd764d758e2ee9bccea11ca5c20,-0x32304dd64bf509723e418c9e005fc0aa34491ee9fbb5ff0847c,0x7c113f05155c1e3572ce39e5bd535a0f550d1c682fb9528424,-0x102fdedbac5ca0d2c1a7726a81367ca06854900e89cb62d738,0x1c1d919825e52fd708997b260fe157e743c7958c90b874248,-0x27e555f923a9c5b6153b8d590815845b5238a106e4d01c04,0x2d32e17209c718223f514b75f4a57524ced240c99dc4a1c,-0x27b26564f3753d5f50b80455600b5594a41d852cea62b0,0x1a011d82b88169dc0989c55d25a69442f03189289b750,-0xc0f2b23920efe6f3687b32ccb64fde16ca29e4da50c,0x3adba72fbcf8b79e44896143781129ab274027f494,-0xa976a8ef265e4f56d0ba4804749cdaf4284da288,0xf1c25f6b560d1cbe877365182b60a7208af2f8,-0x7c9563802650c5fd87915e81708b2b281554,0xb1fcac3b3fc1f2f4f750cab422eaec1cc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 24 56 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 56 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 56 indices rho q9 m9 9 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 56 indices rho q9 m9 9 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xe082a8,0x16dae,-0x1a4,0x1]
def r10 : List ℤ := raw_ints% [0x483d077e4a78caa63a0e85ca28000000,0x6062cc399f15e7f02af7e42922c00000,0x3d2b8d934bb3bdf5272800cedd7c0000,0x1892fac04ca4fc25e099603278178000,0x7041e96f84a0887350b9163d1b10000,0x183dc9f6948ade517935ac0f90e1000,0x41d2d106a7864f68f93fa117d13400,0x9012a3af3d0300bf54ab0160d6980,0x102ab3d7e733de373ecf0a8270400,0x1819de45fe1321a20c09225956a0,0x1e154a780eef47f5e0429b8e6c0,0x1f9c08fe3bee8a8f61a7f84518,0x1c09ee3b2384dba92ab75a020,0x15022f4c243a8b93d09fc14e,0xd46100b010b447c3933748,0x70af9fcc7d7ecef08a59b,0x31dc2c9a9debb2346780,0x1233f38c97b49100998,0x565ee0101c6c9a9d0,0x14549b372185fdc2,0x3aa8c9f4f7d7a0,0x7a4c8a05c5d2,0xa4fa7040e8,0x6d0456b3]
def m10 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb620000000000000000,-0xebf440b183d1fa21e186839e9a02997ff30cd001700b0a2400,0xe2daf7a2a7debf4f1575e83a6e69f3a0cd7ad4fe6daa286b300,-0x8d1a62d0b3c14d680fc118a6d156f08120f777bb65d9bc830500,0x3fd2b08db903ac569754bbbabfc48cfd556722e61f458ccd9d5c0,-0x165f5d677f7d982b7b185e19977e7b3b020e037696cd291e1f9840,0x6533d5d58e83d165203f9bb756b9403c7dd9e182b9d15326e48d00,-0x17b64c8ace1fe81ca967f060c502961bfbd3d40f8a5c6e5687b4f00,0x4b204485739b7253318f4b51a401404724e1b12e08521844d09a630,-0xcc1f0272a1905ef6591f385d3baad5eabbe25a860eb6fc7d72cc650,0x1e0ff77b0efc98282f39cc27ae0c36a5bd78517b3ddb6e9ba4cd47c0,-0x3dfaf3ac63e1ae3205efc6aa278bd20ae2c610a8f61d133930b81f40,0x7095aa2bd3fdd9ddcbd4eec64e87911af78a953bc4feb2403e113930,-0xb52d39c10b14c8b44223d66e0aca2c9908db0ab54656bdd55daa1450,0x1036fe6cddbfb51a654d0fd884c484ef1ffb4bf004a94c2ee483efb00,-0x14bb88d22c77e5893f38626046ba7c920d975904fd1c0ad1ed5bc5700,0x17bbdaac5171b05f0033b912cf386574d18b00f394ba2a8241f366c0c,-0x185fb1e3fdba97fe2228437fad38718f2556e34b860d0d8b06864f714,0x167c9b2b3c5872bbce1ec78e9f78096b323327ea5bfeef5acc543ae70,-0x12a71d3e75db235d7bf6c97bb5163adceeb56c4c2bd43c14dd8fec850,0xdea8837b0da6b23e53d7ef0eb65e46d864f97b2fb4235ec8e3702c1c,-0x95620738dd97288350abd9c1d3af02cf6a02a2f325ee5674450bd2c4,0x5a114bff78b766549bd2cabfcfaa76003c21055772380f82909fef40,-0x30bf2dc6f85203e456d110bb7a4217228cbdaab4cb4ef0a039c80d40,0x17a4d1813b31e97e69c8cc62a1c1cb480a83eeeaabbd082742b181dc,-0xa4143a8cbfaa8af695dbd92dc22895590870166de806c6ee6cad744,0x3f7611b83ab7f4d63c2db4bf1bfe0922b64d1cf14769349d44f2d30,-0x15d02da5e32490afb7761156abaf21e4259676fcea21f6e473c4310,0x6a2bc5c3ec0b5d55421dd78c85003ddbbd36c19de3c9d47a3196ac,-0x1c713d5ea2eb9ecb78ecaf1040395057cc8c8bcd97fd1af1d73734,0x6ab8b441e413ac46c29b33b4e3280e23965dc374ba47337aabf00,-0x15c0ff34cefc99cc1dfa0fbc17559aa9ed595f7fde731705b9e00,0x3d254345e003545634250101a83e4bab06988a5650ed0ae9f6a4,-0x929d0b7753125c8620f2d75ba5824c0732644f0bde65cc1ddbc,0x12833c07b9250076682c6341d29173fd87df4e1fb071e71b7d0,-0x1f0a39ad473fb4125d5b039c87c3408d5d54a9a215bc6e3770,0x2a6487244fdda4c4507f42e441744f161b632350347390c14,-0x2e10ed655190bbcff1f5aa9c20834b29cffaec6fab7e098c,0x26a64928f69f6414088de4d106c3329b26b0781a7afedc0,-0x1811fbcbb7c21bd08a9c344e3983f1cf4e65054b5b42c0,0xa8d1aa1663e51174b1c1af3f3f8794de60575adfc844,-0x305747097b79b8516a858dcecb28214a27d5d96d69c,0x818dd8fa93667790f53751d6c989ae1c5a801cdd0,-0xaa498bc9baa9eb2fb56cb72b2646d9755ec84f0,0x4fdce655d76a833eb2af825fd621e65064f34,-0x66507f7152d746893e3cacf84f128e52ec]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 24 58 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 58 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 56 indices rho q10 m10 10 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 56 indices rho q10 m10 10 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r11 : List ℤ := raw_ints% [-0x2313c77aff6ea9e8c94d4d37a743000000,-0x2ebe65346d92dab121cd5fa02e9fa80000,-0x1d9fdce646fc4d15022e5f71c94f8a8000,-0xbe21a7aefe0ea6cf580a0eca64ff97000,-0x3631aec72a379fa4f3c27a1e82e395400,-0xbae7d9be95fcb2a19fb8bd8961d8fd00,-0x1fa7e495c66f543b06066d75abc8b540,-0x45223173baefcbf924bafb67d365bc0,-0x7bd105a0be751a0754db3af666ea50,-0xb8131cd4c5003c2115392a110e130,-0xe50e564f1482ab5838c51bcf3a5c,-0xefd7d33defce943810b53882234,-0xd3ea070b8f6d06d404adfdeeeb,-0x9e11d6e41a0a6c6821a06efc8,-0x635be34e73a4cad762ddad3c,-0x3467b50b06dcfda1e08d094,-0x1706b8bab7640b20ef51b2,-0x85654e87f31a994b1360,-0x272b3116355dffa68a0,-0x91be841e54d14571c,-0x19e3f7342fc981cb,-0x34f5b8b93389e8,-0x45b0380159d0,-0x2c89e65f1c]
def m11 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c400000000000000000,0x1d3c0703ea31ab86517fd1eae8a6fe7c69640d302c91563a5c00,-0x1bda865be989c933b7b3da8c1aa5e57e5353f92d92e5406efad00,0x112a29b34c2071d683c2ce776c7d7a5167712f7a701050502a2300,-0x7b0b62503fc9bc4d748669fb2a1384ea3ffccf502997d3215bf840,0x2ab678e27c09aca279056f6e3194e35056f4b21b743e12210f6e1c0,-0xbf48db215e5c5f4f829f57bf378e7646b82899da3913e0201357c80,0x2c5c098a127bbb3a849368bdc4cc8a73ccd08f23bdedbab63f2a3b80,-0x8b1015df7563b10ced153bedc2473807e871360a922520feae5c9650,0x175c019f1794c8b20781b20844ddd7f1174d429405bff51c32ad90130,-0x366e86e7a4e62dfc0cc9aad7fe632df6d2195ae5939c8d3fb45c2bf20,0x6eef9c8e3dd38a788d9803591ac21be07b3acd47754b50aae788a16e0,-0xc720f5aa5b074f434de77b487b6a494c947a4ddf2cf86f81888b188f0,0x13c8a865ae59e958f9466d51876f48962ca3aeac93f55727ee991c8e90,-0x1bf91b0a97b39fd35e74ebf350192da22fdb35a538302cd9a0f0b0c3c0,0x234d44f62278cf25c722b139ff740df1fa22f6b197b05a24b1a2273440,-0x27de66875b6259c2a57e25ce0577758890be8801e5d231da459c8fccb4,0x285fb957b71ca5a8ae5d6f48b123af9a952e11508f9e2e1d7dfe481e2c,-0x24b5f4fe0997b5827118483db1f7bac2ea5841499df277526a92128728,0x1dfef113e22930d55f4eb2ff1090618317f7d1f968602c5d222c9b6858,-0x1607e46ca419b621dd302423e82017ed602aa78cbb8807a48b4e1bd90c,0xe8aa5297d965ebb54df72b747bfea24bb8897bb379149b4f00b8c6054,-0x89eaf5794370c74c0c94516ec26f4c84f4dbfaaa11a61f132b4e1bbf0,0x49552861e82a813701571a3d4ecb956ada24a7ed9b748c7d5c3cebe10,-0x22ea6337925f3e3faf0ea722dcff25e65328257c71548bdf6120ad6f4,0xeda49058bda21cb3df8884f40112df2896188bcda37453e68c9ad26c,-0x5a0f850c8dbdb7ef1eda379eb982dc2adbb9601328a4764c5f2067f8,0x1e4cdaf49eb4d723d5abb80729159c10c5bba2ba35d5f5a1d91bf188,-0x90304acaedbf7972ad9b3312f74dc143507ca2fa1ab37c7fecd686c,0x25b783cf3bbaab3c8a8c42c56411c8a90549b487242a16d6bd4fd74,-0x89fdc67da29b1de60ffa86892e3044fdfb1a2005f620bc8a95a760,0x1b6206d78e648cb9a3077a53eb7b8714f95c7079c5a49e735240a0,-0x4acbd2aa0b9d4908a1443e147115bba4de98aefe0fcdc253f287c,0xadef9999b3396285f9835c04f3bc67e6a1c4b196afbfa3f39424,-0x15407266a60742353accfdc5d07736697083e3f4aae2d3c03e18,0x2263af39b545722341224216e62aa7d1cde25061925ea13b468,-0x2d313528c272da1fb360ab0c6f24ab24545cab99d928b6e344,0x2f1649edabb44597e365a4dc1933dceeb2fe8181afde80edc,-0x25b986635eff217f10140295759886084c6ffc4a153bc170,0x16536f622b6a94d0846d71f68904a425014f5d372b02c90,-0x93efa0e1b4f5c6cfbfb5f162469cdd01eca32c20c998c,0x27be2a55354d008d40938bded99e825116a6e37c1a14,-0x6316f0a17fb76dc9a71caa1c4366bd479b6c8381a8,0x77f26a7a42d4037efdcc29f95c438573f89b9cd8,-0x332eda32af94f333635f0be41c41accf4cde14,0x3acd0810dedc2b4019fa21b2fba08ffa70c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 24 60 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 60 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 56 indices rho q11 m11 11 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 56 indices rho q11 m11 11 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r12 : List ℤ := raw_ints% [0xe54ac0f5da7e067d91c7b3d89005c000000,0x131348bf5a2eda4d01a9fef961c905200000,0xc1301f527b3f5fe823b28770639271a0000,0x4d63651a61ec9feaebcf663f6fdd38c4000,0x160692424d3710a6a2664e633eb918ea000,0x4bd6d8b590410e1609208a7cd7b1975000,0xcd2628b68c07bc09b5998486fdab6e400,0x1bf257fe84cabe537d87e1f0517dfedc0,0x31f164a8e756b95cf1ba764b087c3e80,0x4a11dafc990b13f00d7b5b7e5724f70,0x5bec13caf24cc21137de0ae2c48900,0x5ff63c882e8a28425c58b6b0ffc34,0x54803ea79a0c7ffedc144bde2528,0x3eca259f1f720334148971d9635,0x274beaca6646513b33f1efdac0,0x149f7dce7f1d80823c2355a74,0x9026607c15ae61e70e02850,0x33d7b1a0eeb319bc081bce,0xf1a12c6bd2c095dc9e00,0x37a94ea6f7a62f89a50,0x9c6449d0644f2dec8,0x13b618f5c0763fd5,0x1979e9808f2f80,0xfe8cebd7000]
def m12 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad88000000000000000000,-0x39f733f46c36b8ccac48b6ac8ac4e8dce21cd98d5659971112400,0x36bd8da1a9dec3b0be3611d28a88e3e8dd3f13617b63c339c5f300,-0x216db04853b6830b96564b0c69bbd5932b37684139b4b5929fda500,0xed68293eff4373b526586a2e3246f315e5a33b407ebd0b004bc8dc0,-0x51a06f97f583c2c88f9eca77cac3d3567c285506aaae4ea4d1d9a040,0x169fade45a5abab431e2ceb3c8354c8433646b45039ff2c7c57160f00,-0x5319ae45b2c8a9d6fec204ffae170ea7274037b0012a1772b23b9fd00,0x101d1653a07fa20f83e39f1c0e462c6e13204d2b70aeb9d6d4205aaa30,-0x2ad8c6eb580790788e6b22e5ec891e1ace3beffc1d00225f7a8984c250,0x62bf413f72621437b1f04b6478df7b8aff83a1d8731b2bc3dafe06f040,-0xc6fb4efb06b3c5491483cc9ba272bd9114d72c4fa984cfab4611d9c2c0,0x16102bb19b639dec1bc1e608ee2e5f195ca8f6be4ee2bbff3a19a0c2b30,-0x22a697316a3e1f19df0bb1e861d2a4c24ecb51f9cff473e8fa94545ca50,0x3062b84840eb8499f292a6d08587cb5d53c98982417ab1b96584277d100,-0x3c47435c2897921633b00be02100c10613a78200fa7396c577e8764c900,0x432bfb6f0082aece2a262446cc95ed58ae0c2fc257558b46dca89f5340c,-0x43161c4e631c337522a51a0783feec7829fc1daa1f3fc0bf03dc60c0714,0x3c20e2486629d8745f101b8dafafa57f6ba4f4d9aa0830fc219b73af510,-0x3066cb78f03ddb1c87f4e6d2f39686742fdc4d00547c70b41072c25f8b0,0x23003f71b41e1dbb448e1dd491ac366bff17f9894b4be15637a585fdc9c,-0x16bb52edf34acd0f3d7d0f64ca27cebe3386ae1d45f9c38907c86964444,0xd3fce3b7dfc07acca65f9cd49736bda601f4b754942b6047b86bb981c0,-0x6ebf296bfdcf2818f500f4050106de5c57c5d77ee434821d0f59848cc0,0x33c3fb44cfb6439c838b1adb0e87c7e9360e516361da47e3b98b3db49c,-0x159945ed25cbbe4ee0ce9c09d0c3a7dbfd36286ca7a53fcf03cf570c84,0x8055342c5f01d45d9647dd01254f34de7e2bb82668c7ead51f67cf050,-0x2a4370eb798e691c7cee6bcdff9979589614df9f2ea77e15644bdfcf0,0xc4a20f8a2cb33d5c799c79834fc3dffe8e980f00bb90f29dcce8876c,-0x32391b0e03f4d305c804c04a4062c5d6af885c7bbe737ed8e2a9e874,0xb3285670263fe5e13599c5cd5bf1e1c67f4ae0aca1b1aca80126b00,-0x229bb2ee7564b32a7e475a6408cd031176c06af544e1e6e74d40600,0x5bdb35cd9c69c8a537e1642090a1046f93151bdc6f42c80a12b224,-0xcf238bd4b7338cacfc25c37470752e9a7e0b57eaeab0c813b9a3c,0x187c2c1cabe047d3cd3a25b7212aac150b7f288fecf7ea86220b0,-0x263b051f3e55c18909e8ab43aae38a4ae042c0dd4b22abdb1f90,0x3053f377e200888c9ef3c3c2e71053f727e021afd94de92da14,-0x304400ac84c30ec75809052f358ba349b630c41384454ea18c,0x24e92347922a75290876d5377f4eda02e2ff54bd40e179740,-0x14bf9be2c7b8cee4afa076d20d68ddc000f2ebc5c8c9db40,0x81d30c2c10ea2d2b13c1af30f138f4763d7b126f857a04,-0x20b4410d63c122ee1cf5997abb46a85d552cc684fecdc,0x4bd1e45e393a6af699bc943a757b912dfe8535e32b0,-0x547cd08fa07f6fe5f9db1933e3c16152aa071cf10,0x20cb6c9045ac1e75e722bededf641c6f97fc9f4,-0x21c91d0b31fa25d59f06d1c205074583c62c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 24 62 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 62 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 56 indices rho q12 m12 12 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 56 indices rho q12 m12 12 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r13 : List ℤ := raw_ints% [-0x51e7726024cedf400ecabc7ca727000000000,-0x6ce8770afa02766c830b6df91ebd824000000,-0x44dbe30bce5b77e29e673e2ac2f7d82e00000,-0x1b8cd6cf1da7d5a8bccb7fac8078403e60000,-0x7d4a63e8e7637a082e0c848c350128b3c000,-0x1aec63b57a805773ba912d90e3c700016000,-0x48b68000baec2bbf5340fb9ec2783acb000,-0x9e355b6295e81d84d09367e08569151c00,-0x11a2f7beca0b28e2ecb2e9576f63791240,-0x1a19d0470d0f83ea3945772e5ce7ac180,-0x2050addf1626e2643c37f6d3624a7090,-0x21a586e15372d3c880d8c094251b700,-0x1d8a822a6504a16ad39e3cc4be73cc,-0x15e0e2a9f74f1f2e05df07cae5ad8,-0xda438dcd1ab958f2b2769da89cb,-0x720f9a69e0a3d9d9cef1e2e540,-0x3196581bd8973aa20a66d358c,-0x11bbed6439175d84fe75d7b0,-0x521e3ba3669267c5a56432,-0x12c598a649a4a14932200,-0x34434da3faa655df5b0,-0x683c1e77e246ba138,-0x84e6f1010c5602b,-0x51983d3841080]
def m13 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b100000000000000000000,0x72f4c1633e96fefd6a8f01d91ce03ac3a1ede581d74d94b1135c00,-0x6b9f99988cf88cbac1024fef09dfa80325364cac16c784391786d00,0x4124124ec52eb461bacfbc70f7f0cc46b068fce73dc49b799a09c300,-0x1ca6c2f44f2fd6400c4040993f5889cdd79e4ed18d3864da852e87040,0x9c257ca1163fbe3889f704f3534dba3e2233cde0a443381dc56eae9c0,-0x2adccdb25bf6783e0f2933f870fea01d51f2c243e0be7ac3d8bf762680,0x9be3060f13ba6a06e0eeb1ee36f9e21aef4103ba95b26fb94af1314180,-0x1deb9fa5305823260b50fea8e9adfbf9056410ae4188666ac182a63c650,0x4eba475c66984f737883f48776fb04d0a0bb52f736ca68d7c42e8063130,-0xb37c21e28fd453bb3bafb834670c6b2e6f809323b1f35186ac21fe681a0,0x165a76826a0e8843f0297cd46b6051ac3243c627a84af048e663ed649060,-0x2733b0467c4e4676e42c29728132361b4c5616c1438c0900f634e38a97f0,0x3cd6882f7662a3db0c0a541593b71f0bbbb755317173abc1279015be7f90,-0x53e9884d43fc8d82e8afd8c3285ce24907b0ba9873646c2a8925db737ec0,0x673633cab7a0dba08cbe0562e9066bc25a045d352623c2e40b8610b14940,-0x7181247d12860e1b115e8bcf555f33f86bfc33c347936ddbf6aa900255b4,0x6fd0f43177a2a3f2b980a3d302617b7be03bdefa3fc9f79ffac86238252c,-0x62cd5b714bed692709eb12c0dacfc2dc3df8ecbee1c93a1acb41ada34448,0x4e5d2d6ca40d1d6229237a9d6fd07d2a25495b6f3024ccf74cc894802e38,-0x37cd24a5bddba47f369cd45330937fe522596ce35a337b0029930121bfcc,0x23a9c98125d17e35f0b2378b56316b01f5e365412abdf911e7040f9eb994,-0x1470d2ffe0c1031065ac60e606e7ae25e2a3f820bada3b0f7c4153be32b0,0xa7e37d209a145826eeea66f50757a45921dcdef8eebcc9f28e3cf303350,-0x4d0c0acf389ed508de0fa3c6325b3f543024ff1bedb0fa76f03a5f08974,0x1f88a18374e89f70111e23f2e93fe24b69c7ab3d77f7cc49b3c264ed1ec,-0xb79b30384e684b98aa8c66f52d0739575b48a4efb6e12a422d0660fa58,0x3b308d26bcfc9115a519d2ddc0fbfb6c587081c20a6b6f6fb06d054e28,-0x10d3f0cd18a6aed755d3c7e15ec82f00f35c60ea70a38f8d5815e73eac,0x4325f17eb62a1e7c6cddc2794512c230ccd76dbc020c7e8e9cba85d34,-0xe98aeae23064790af6763b56539fe25baa3cb1f52993c9cec623c6e0,0x2be9d4579404760a809637b749b994abc9ba7f9ed261b98153954120,-0x713e5a1810e0dee5b544cd99efac139c481115cb136b367c2ed847c,0xf79956d43fae2d57412f3cb8557cf3d0572cc2213a95b4eac0dc24,-0x1c4f6c90145435c179fd9dcbf4f4e4a9a393380a620fdc720213f8,0x2aa440f7290b73d070ff4237d28be3ab55c3f85a785b737a5bf88,-0x33d685f1a8dcf1f735e13874ba8bd070b52d0ccb91f60e415284,0x319b6918a5b0bb9beec8073d1153ca2bca4427dee47e5b6eb9c,-0x243284ea2dfd7cb82c0e8356e7fb6d6e482d6c4d94e1268230,0x1351741f462c07d18800bb7463c71824c17ff0035b1e95fd0,-0x7215b818ceae124dcd469a38075db90192b938ee216d20c,0x1aef4ba3fa0b370ce138906533470d0403e463f0ca3b94,-0x3a0918b0509ccdbb1b9047e40df62b536b298a001dc8,0x3b8250b9201ee261f7ee5da8519205c332f47d91b8,-0x1501edc6003671d0aae9731ae69d9203ff902ad4,0x136876097c19934870d6c08375359a184784c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 24 64 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 64 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 56 indices rho q13 m13 13 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 56 indices rho q13 m13 13 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r14 : List ℤ := raw_ints% [0x1a40fe748592ffac8f1b876973bb1a880000000,0x22e08423de2268339648b56f74ef2e25c000000,0x160770e8b4ce6bcba2a9ab34843e86179c00000,0x8cdd02d98b5a0e35d679ca05570a2c00880000,0x27fd5c20a63eec9c9c21489f3d829f04c80000,0x894fcff6eff5add59265d9f2ae4e21683c000,0x1724f414302ef0904eab19b36a9a338bd8000,0x32473826c91e6f4ade53f1da6c1caa6ff000,0x5985e5ecd8891ceb37ae7fb7102da5c5c00,0x843c625d7846e6c82e569ae1a5bef6f5c0,0xa36073c248be0d6c41e637b3f16ab0880,0xa9b6a727ed161d698b9cf22df56fed70,0x949eeed0b1340352485e74a26341180,0x6dc0e2da9ec78e50fcf4b4a09b4834,0x44362cf7b7bb3dd4bda4d39c4ac28,0x238430bc624564f2fe29a8341035,0xf606f1a52f5a09a0ba4ef60a40,0x579275922cc4fe0cb08319a74,0x1934caf92e2480b52d891c50,0x5b9c39932fe50ef1698dce,0xfd29861cedff5eed2d80,0x1f4789b69f1a4d5b650,0x2775b2682d0fb29c8,0x17e9a4a710a55d5]
def m14 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb62000000000000000000000,-0xe405d023a31e7fecb7f9536a47f7e10a6168ecab912650171582400,0xd3ad708485d3f4cd87377bdb1f68423892f9a3e7f4983ce1c8953300,-0x7f030961944bf21336af2d9af29ea17876632084202f1f0cfe96f4500,0x375e18552ec3dbb7fda3ba268943586374dea80844f14b57aba8f485c0,-0x12afc7d07d7107505936e9b6e9a5e76675498123532bf3aaef5540c6840,0x514ce07bf72bfc6fbc2684c2b6fee1f18ebed6cc4079a888c58f8ef2100,-0x124d1915b13ee130861e04314f82244757c8861dfdd9c86ff48c71f69b00,0x37a46a409902d2b0b9f4a9bca766ba42981cb9aac1a0bb39140acd9f0e30,-0x90e742d1fdf2e305866c511e16dd8ecfc470a7a20b3e758b9870af33de50,0x146da357062d637d8d0901b9f3422e969c7b16e4cd24c50ee2c5afd74dcc0,-0x2842f0d2b0f5939650f51c0696c83094bdc60c465237e301774b8e01b8240,0x45cf66e991a85777a3ff2442f566e22c654f65ffecb1c4d45643688fe4530,-0x6b12e35ff0909089b41409c1ac555dcd3be9a51d0b9387e69339b7ce15850,0x91e614289049037a31e837a0f689c18433bae6e18eede61452f7ae7e25700,-0xb13544330de2e4a7017bae2468dd091c06bf188622d07b36d82d64a1a4b00,0xc059b21fbeb2ed008f5dab30ff609a07036f4de2a368498307a1b4b0e640c,-0xbaefc15147ad8a09bbea9fdb8d97fb5557d1632407e19be66010e8f22cf14,0xa2ddff82bef155ca615272c1ea66355dcc3895bc93e73e28a919bce36d0b0,-0x7f4ba0a58c74ba67ba3cc6751a61b45dfa5dbed9e5111e4c5b09b66bacc10,0x5944fe4095a056329951043f3ba0127c57d80d92b8324932e2ac19b34af1c,-0x3826860aa15f422b0e9f0494476d528235873452060f3e838aefd1d1a53c4,0x1fa6bf0d605ad61acbdc33af658389bfc5bd8585757088e8ab5865fcf6840,-0xff78e2b5f4bac4ea78f3b0bdd858e9c255c5cbf099b0d98aff4bea0fe840,0x731de19b84b3d2d6f3fe31e252eaaa78204cc8a7bd02eda0d7fc6b14f95c,-0x2e3801e194fd885d4be4836e8f3173f15c3265fc463f87498a2caf7f4fc4,0x107ba293201c382679ba27064505f8e68918c2055c80f791d86148427c70,-0x5339d15a4c989ef59cb4286b2dfd6a9417038a0ff4b21134cb3126bb5d0,0x17226a18fc71c28e33d2cfe3a50448d140cd8a5b3a1352a7387b289d82c,-0x5a22acbce582ca08caefa3830503f1b73670282707a50f47f07939f9b4,0x131a3b8fcc0cc06591b0d5ae4c5789ae416d2d61c9fadddec229843700,-0x37efc9dade3b49c5889204def797a7207582c42f20e6ae726e97bae00,0x8c2330ca51bd916f9f9a1ecfef84f92bf5adaf5ec92abab95cee79a4,-0x129096a329b99eadb94cd80adddad3b67d9d930f002f9ccee59aaabc,0x20d887665a760b4a99a7d755f6e232f75355a4abbe9fcce9b955090,-0x2fb6e34969ca28df93e979c2e65faa91f153496a268d4ca96408b0,0x37c4083fa810a40ee4e56d8566569b4cfa71cabf5403119b4ea14,-0x331e281d7c85313d855166b17df10620ca56eeb10586a0fe378c,0x239361f82278ebd4f37a2f0d0e606789b0c1a68c447435b0cc0,-0x12049a7413eb77ebf8bf788cf2b4bf973a022234d4eb0cd7c0,0x6461749aaf508936da0de2e444eff9b9b401428d8f32e5c4,-0x163348043c4c0eb36ca8eccb22cf54520da4a05b3a5291c,0x2c6fbf26c0ecb6114d1f95ac5251b82a7d796d7fbae90,-0x29e9c7a04677d18945bb8dbe4159210e0bb3bacda30,0xd74285d855c937624408e956dd30e598492178b4,-0xb257e5de1a4c6131116806215ed50ace6456c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 24 66 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 66 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 56 indices rho q14 m14 14 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 56 indices rho q14 m14 14 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r15 : List ℤ := raw_ints% [-0x7b1b2bc9a2468d558f50cac96cabcf86c5000000,-0xa366601b2578701108e0f8402bc1a636a2180000,-0x671c5845b2c2775bd6415bcf65fa672ebfd18000,-0x292ab179e63e205950cb0dc3f89fcf9642591000,-0xbac8c60c3c90715390e3335b5ca7f80ef940c00,-0x28097ab1c09ce087093b6cc454d010577adfb00,-0x6bd56d1cef6e045aa06ec6f0f9322aecbb88c0,-0xe9ec4dfa34fe71814d4f7bf545c301fdb1a40,-0x19fdddd0d957a7bd1da50fb6f71d60da59bb0,-0x2653d126e157b91a2c7982e623b9ea527750,-0x2f43c9a0dc3a1a0271a44c3ab255f7abbe4,-0x30ff2ceca1c37fefb6e13ad5b827d6466c,-0x2acf33afe77067b2fc3d769b5dbb92e95,-0x1f88a406f05601af0fa58a4960255e58,-0x138af48ac5f623e5140636306bd3ab2,-0xa24af0b79db9095adf44aabb8cb9c,-0x46036d1dce43859f0eec21c61bf6,-0x18d1f3d5905cffbf9d89cbf17e0,-0x71c71c08044d818abb5054e94,-0x19b52e50f3a4ed21958f4fe4,-0x469b063471dd32e0c12c1d,-0x8a92be77f08876019fb8,-0xad52706afd04ae73be,-0x67f5608e6ee1cb94]
def m15 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c40000000000000000000000,0x1c462762bbfbefb9e177b91492b7b2262cc134a8c693a3b2cb9ac5c00,-0x1a07e97e57d10646c571751864ff0b75d54dc065b29c399c5654112d00,0xf7ca4fd650af0b77ffe6eaf8b85b85f5d76b9414b667bb8d9ed80c6300,-0x6b13b9ea588ec8a8f014ab181b1cc41f04fecd78269038eca2a4dcd2840,0x23d09d8f3758ebf0688ee1d867b4283fb509f2e1d6320a85bd8cf360b1c0,-0x9a622d62ddd27844b2ead7df254171a66c73eb223c150ddcd1d178cba080,0x226c28de477bd963f696a3f13a568d8dd8300440c38eaae53fe1863c0f780,-0x67a1e2c711be5ac62757ac75503ecda33c6e3e931a74fe9d155dbdc1bb650,0x10b27611c54c662383d51b9875b0bf3eae629a2fa65ce7d22cfc42789aa130,-0x254539cb02ac95ff4c3c870e6d4054391185c2e66e1fb8720c33dd3e265820,0x48aa0fc04221cafa2fbedf3b5c4ffd020350e7b7446676c251a4c4c650d5e0,-0x7c9774ec247676827d9a538e10b87fc34121440258ce1288f6e8552a1026f0,0xbce55b547d6b01c1355b4fda7d97a7da4f92bb6d730c7527529b15fa49b090,-0xfe51d3a4bc97d05999706db0378798d6b674a733b8200d00d85cafa92601c0,0x1311391c9e16da4429bf740c00f22b06014267c56a9f3c18579e953aca61640,-0x146e57c0bbbc6ada8d72ee4e13917adb8a1a3c34753aef4ec10020a52b7eeb4,0x139762a6e0d42646ccd528bbefe858489984725e3b32a328050e2ca1b029c2c,-0x10d50e56a132d62901c7721f81d142c719d47c7660efc33412fd9ffbb55aa68,0xcf74feb6532bce8f791bf048d52c7a146a5fbaaf2ad10cfa6ebfc62e9a6318,-0x8f4bcf393b0a8e557f8d065c98fbd4a5ef37720f42427a86a572949dbd668c,0x58b7a8680675000ef654b7934f11ba2f6cc12bc8fc373e917851f806ae02d4,-0x313009adaa7f04c512d936f5d69e6cbc2fae71a475e712ac11b1b9be7bab70,0x186301338640ade8f86f8a1326df2e374de08999a1f3d706b0e358da310690,-0xaca60053715f6ae69dab64800be5ec18322559ba87758b97625e3f8aadff4,0x4400e4e23ef751f1033b7a768261f265852bc40056fb5306e776aebf89d6c,-0x17c49a22a1966f8bdab3a311bb77e4b5af21244f35ff7865c564d27efd3b8,0x757b791efdc857a44db9772d36f854c1a21328e300dd9745e6d67fdddbc8,-0x1fedf5c928f3437b8fbade4e7ef367d2e4017593a2f84559bd3cd1e0f8ec,0x79773a686bc1d3cddbc1275d950f2bd3c5f75cf7c6c041825e596d858f4,-0x1918aa63a992848c413ec02c2a6c6d65691f6c51981e83e1bf0e26a0a60,0x4785b4400c4c741c29b8d53626f4daa30b24daf36b7a2248a855c31da0,-0xae0eb82df85a49c1c05ccbd65e91dc5a2c9475a59c7199f24e67a387c,0x1659b45d204b49e144dfb46ca9191331a4aabc4b1896ae57f5e4a2c24,-0x263c50b130e8d47e8eaa3f3e74d9af52e4dc3bcd9e062f6f0bf900d8,0x358e898050e45f2dd4187173d38c2af05836d1357d09148fbe4bba8,-0x3c291afd1489f66e7ac46467e06f2e1448f6f4b88f51b7100429c4,0x34ce30a1687e3cdbec66d7bf61a6029638a0aca5135dea5e4105c,-0x2309b778655a8c970933200ea896c443bef2356e1760ff2c24f0,0x10d546634b42813f3852529ba0cd84b561025b2f16b90785110,-0x586d5f0ecfd3f4ca6f64b1cc438c1b2203dd96fac60153e8c,0x124f9d5ff3b6eff8c15705b2a6838ab94979336ae6a8d914,-0x22087bb39ad63817cc21074a1a5b74a2f4c9d0089afee8,0x1d84a1f27acd1571ba065d7e8c8060c04aad0f5dc998,-0x89d3197bac9d09798a57342bbe818d7f0065dab94,0x666786eba0edcce3ed7c69dd4c3b22dfca758c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 24 68 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 68 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 56 indices rho q15 m15 15 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 56 indices rho q15 m15 15 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r16 : List ℤ := raw_ints% [0x21731cdeb1fe9f36466af9af51b0009d9b54000000,0x2c5cedbef7ebaf36a4dd590c584e5518b891600000,0x1bf87b3a2083822874c8c654a362618749760e0000,0xb282b593f90e7d9d852aa6d6cc2b96120ba06c000,0x329235df9598edfff750161f008cbc652233e2000,0xad3fea61e0472bc5e0a1feeffd331bad3833a000,0x1d2123f1bfdb5560802e1df47b46eaf5c39b9800,0x3f1bf4ecb5aeb383ffd5267f9ad44c7e77c3040,0x7009b2dbfc9ecdfe74b9358743cb943be91080,0xa4f55fa84cad70e6236844599894b7c5c7590,0xcb1540f9a64a41f7dd6ed1e20eb82513a440,0xd2230024a624cca55df623744c86624fecc,0xb73a2ed18d9039a0da0032372989b2b9e8,0x86a9df4e072b84522887a08733e0c0ecb,0x533fa4931335cbec4402320b471b18c0,0x2b16a59c718026cee8deedd0b8be15e,0x1287d64e1c12516c8ef91f171df0d0,0x68bd3ea6b27690ec7f53fc2d548a,0x1de3b31399caac83b7e80ede640,0x6b911925c60dd224051520b3c,0x125e5a7f69f43dcf35f65388,0x23d59d303c62fa4898fec3,0x2c817c6125712298b600,0x1a792526c01544ccb2]
def m16 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad8800000000000000000000000,-0x381ad2ac22ae9cf09339068d444544f5cca1560700be0d2a6a7bdf2400,0x333ccde2a5c90fc40d04db6489cd0710470ff02cae8a8ad14575a147300,-0x1e3b174b0fed8dbaca7c39998e38a5a9f7ecbaac19ccc60d72c404a7e500,0xcf3c4bd07171ded88cfa346d3453feeb65dc090d320574b738bf8be3bdc0,-0x44b518525e3de20de30bb9769b8ed5282594efedcd97d35dd59c43a13f040,0x1257e05c73c772d0ec927df72bef68a9e7f445c0845fec174d0cf8b99e4300,-0x40d454fa604970748eb9dfc43d398adee7f06c6adfd61f4612ad377d56a900,0xc14ca334035a58e547d951046c792dc2d087ec760082dd06fcd2437d7cd230,-0x1ed5cb0367cef63061af32c858e177f2996707dd84a45d55b575ac1fb719a50,0x441f8179abeea4deb98f95303d3d20f27686485d79b0ee248bd36caba01ad40,-0x8368aa87b7834e55df17b4fe91992830c562b75a75529f5a9e52c451b93bdc0,0xded88a47331c2f3f5c29c2a0e66c617ad1f78f57b29a70a1216be9804dd8730,-0x14e0671d9632a0be019ca5486946e85ff2097d13c8aeb075fecd1dff5add3e50,0x1bc6bf101a36427fe74cbb67c7773801074ad7570c5940d4f73c0a0ec690cd00,-0x20e9bfda1979c07d492c06032dd7ef2b07f0f347ea6bd39127b68dba6eca9d00,0x22d1e47e53b3de51d5637d7faa9d4962faa92fed3ffa3ae660c0a05a76f07c0c,-0x20f2d95b5875a2062f6af4b5d60697005acc17013a72cac5e51971c17c292f14,0x1beb7d01ab6e21ff73d0c84866e10f6971fc042b7899c716c24db110d85b0950,-0x15330948dd9883ad49b674bcdedade956619b63c33b161013cb0f113c9faba70,0xe6ca5eab147817f213614048541e4e00bb38fa2fefc5ee4a5891bae083b239c,-0x8ca8809edae9619a2bca654ec30b29f2c45230634a12b99dfeeaefb5f64a144,0x4cb6562bdac4333c92895680cc8231c27cb5bd3e5d5bacf9b6f6a924956b2c0,-0x2561e67b1f60f59d89bd9830a15aac7cb5a0d8011a35cef1cdf7034389b0fc0,0x103e5fdfdd19d6cd0ee8102debe361c53964e54e2d0b2ef87b93e841528701c,-0x646f7a2038eb32038dfef4e4628a50ab75c420a1568af3b605871e036c6104,0x22677a3b69ef5b1e6fb2b1797bde8057878ccff76385f320c4bc68a2c18990,-0xa67aa043e297890336aded031d4fad76a23941833ce045b85cf84b9faf5b0,0x2c3d0d7bde1a62d185d258944ed5e0d08fdc430a66fa92936c307ca5b28ec,-0xa45096f1d93719dc15e3ae0c7ef8f5cc058de4b2384cd3c91dc8d12a6af4,0x2118921221f89afb94434e1778d2e22375ff492b5da71ea4a1ce6a134300,-0x5bca3da7be5bf507652a312ae997507d327e49253b71ce1e62123ed7600,0xd8f73f80f70ee76be2e7a06331db4ee110a8c915883e8e898126ba0d24,-0x1b002ddc2c1d86ecb2d3fcd9afb0e6ce2c7cb745ec677f39cef16d6f3c,0x2ca793faf00897cb36793ef45e810bad9ebce858a4d1a107747717f70,-0x3c4bae949b3b0cff9aaad6eaf436c52db79e513d2c316a14e2027ad0,0x4114177504bb5da18b8b186a34d2e560847cae8bb99cd847295fc14,-0x36adc4e0ee489f8bd9bff65f994eb0d7a913382adddbb1e8756b8c,0x2293bf410121b7dbb5f01b115f80fe87093e5f6133dc63c165e40,-0xfc02e834947a7f487c60150954f19e57c5941d7cf0e98002840,0x4dfba9bd345297d9df439c467c93a170903bc321c526adab84,-0xf1cdd6ad47d323a53eecc3711e0b0cd09fbd6c7b62080b5c,0x1a123ffb143b91d136171db1f16659f2aa2f73b37fee970,-0x14c96ded6cc14a957a4d10bd74ae2fb69e81192cfbe50,0x58395635f04a5b1c22bdb90f7a0413888db4c27b74,-0x3ac9bc9cceff9de8568fbf0a1c653566e0110ac]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 24 70 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 70 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 56 indices rho q16 m16 16 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 56 indices rho q16 m16 16 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r17 : List ℤ := raw_ints% [-0x8849cc091141215dc51a7fddb6bb6312c0812000000,-0xb49f651d0d86e5db9ef2344cc912d43250115f00000,-0x71cad3eeed39e05f1c6133c7311bd64db97d01f0000,-0x2d59d8d9afefebe7de776ce65567170c8dc805aa000,-0xcd5ff24b12bbb1f78f9556d75f8aa37005bb3c3800,-0x2bee328ddd6bee475a6fe519a9999a5d0bffc14e00,-0x760da51026495d6e2b0d6b452e5b5025e6b1edf80,-0xff76ef2a9c99759e6df7f1e9241f9826244f6680,-0x1c4f33e0c1418b8255a922f8d75c883facc7fea0,-0x299f99a9c75e5ab5443299695e3001afb5996a0,-0x332a6b745f10b0723020c8b460bf0d6d16ca58,-0x34dae65bf88977dacf71346a901c22de31f78,-0x2e00b33fecb0746ef728b46ac563e27f75c6,-0x21bdfa9aa6a81746d988f1472327906c188,-0x14d024fd3bf967f93e80132c3e20126771,-0xabf0226e4b08eea00e084e2ba28a4068,-0x49bdc9389009c21a0199def273e25f0,-0x19f870184df3934dc257030d024070,-0x762bcb0ecbf4ea5c9ada75a36cc6,-0x1a79f1cb87561eb795c63676148,-0x4804dd4319bf3432cb02b8d92,-0x8bc8fdff3a3daf51e3f81a8,-0xac97762efa6fa6ebb0209,-0x65f570553b7bda0b018]
def m17 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b10000000000000000000000000,0x6f59c4e7301f4902fa009c9c8448ed33e84e96ad917039822e500055c00,-0x64e3dc6d38c702e5258be4fa00fb921c427530b8e694a7f3e7331079ed00,0x3b0b5403ee3bd71553ffce66b57d13536815b9008ad503f302f108cda0300,-0x19160d2ffad9b081bf78ef119a8c67f7b67fe3478231473f51fbfa9cec2040,0x83ee24af1a3f4960fdca29b89a9888ed2e934c21432327a72403b4cd5a39c0,-0x22e9029cd7b3cacc1f450542db7da5edd9a05fed32992f04be0d22288d86a80,0x7a40c7d3cfbc3a6392bc066f6404b54c2eeda09446a10fa215682891282dd80,-0x16913d435897295eae3c05e34f36fdc188176eaf584905fffc298e2d49016650,0x3909a00d12a84ce31e07339f98dc9e7c6cddeb8b45e6a402e0592404dd465130,-0x7cbdc8046c9888de5789ae8cf0fc74e4087d093c36c9a8646595dea4fb53e2a0,0xee1da157c9969541ec0e14b33075d417b3a1c8a53ec1efa4822dc5fafe004760,-0x18f70e4d326d102c3b1e557c23b0dc982e77021e9f7d553ee6c616fb8569bf5f0,0x25006011d156281fc9a61c4f597c8c06caab9978664031afb7c92b0a738bd6190,-0x30a8af9d25001fc223e4df4442779116b599fe3fb6fbd896ce354286b26cdccc0,0x38f657a504ea2df7d8324aaa1e62b2a190570d585d660a021a233bf1f55761b40,-0x3b81cacacacb15533e9d4cdb661773a9107d5a9f2b36979d75fc9401ab48fd7b4,0x379313188309de6a7d1b40f6ca637f78a086df8d9d36a8d4e2ca4871491e7832c,-0x2e73d6aabf9ab59d7252aa0c524e8b600b8397ae26a11c9b128e6693986a9c188,0x22c560a43adca2d671414b95ad40eda480cd6e814a36adf473b354e9e8f7fbef8,-0x174ef5f8fda059ac1ed0111a7aa5504bae1de2b3b72d3ebaeea6119e5e1dc7d4c,0xdfc4fc04bdc891d73456923eada600a635628a809014259b95b234f32301cc14,-0x780f3128364b454eefa0721dec17d0310bc74724966760e143dc412ae2c3c630,0x39827f363bf4769d14b06b3560beb4e89110faf39a3d07f1e09d76fbd2b117d0,-0x188ad990c5ca2dd2d7b405f164cf2f5bc6ee7d50b409de1063bb48bef97fea74,0x94e35f185bd8095ddca72e202494ff426adde0c18d2d2844a4d2221f98264ec,-0x31fcee7e9f331eec21547b1aae8066dca1abf83950c5264799f9c353c6d9c18,0xecce0c787b824d1fe801ceab1313f423de2e95a5b24936a417cf7787c73268,-0x3d8669587509c6e341265458bdc56bd5690afdcfb1f50af9be97bf4330b72c,0xdf1df4a9ed4a34fb53e1cfe819e8e7a5b2f6ac3afc4342eff89d69de510b4,-0x2bcec3b2edba7b32c7b606a86af6a809bd1c2ed1293eb018e0364210671e0,0x763a975ad55ee4580afddb5185b538e2c258d129345e892e1dbc86a8d620,-0x10f66e62d862d4f21294c303d2f0d1085186d5034d605ed315350519a47c,0x20ba614cf316233fba5e0c0e2ef641a3912553718935d072447e804e424,-0x3450e33f1a81ce63c4ba02d4375816def7c2ad1094af0ec3689e235cb8,0x4414906add4a3d6b07e7e44d437bb16fe1cad31cc9a7620d2f58490c8,-0x46954ade701b2bba4fd582629f66c1b7e00acd28cca8527c53845904,0x38bf789148b73156dea3914d1fd8a3139abacd4c0f931c119d24d1c,-0x222fe7d7e85ce86cc07622e1e1ded86c7f0c617634f85216c909b0,0xec275fd49eeb081cbcb0261abe1054991425e453d02c90f22050,-0x44d7c907814e08175c0eee2f14f9426d65ac8bbd243d7662f0c,0xc7afaf6f0a137f95a1e28e7f1ba10572005e3e68bffc36294,-0x13f9d15091ad185fbe70299a18cdfeb01b13918221b77d08,0xea301bb5d74d6383f2b445ef3b5e0ca5c387d741bac78,-0x3875d59d66ce5cef9cfaf62d0fb26975fa57f5be054,0x21bdee104b1bd908034e8d7b50ff72bf88aadecc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 24 72 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 72 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 56 indices rho q17 m17 17 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 56 indices rho q17 m17 17 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r18 : List ℤ := raw_ints% [0x20ce644197656fbf808163d8e749c9163b6ac98000000,0x2b72ea4599367bf0e95faa839f5de118c38d2b7400000,0x1b5a60205d442b7c139402ef27223b7fb31f79d240000,0xae4900a956dfa9307dc0287ca923bbfdf1a5e5148000,0x31498ee0dbf5421e62503121ba1df1881fae71f20000,0xa887d1e882943ea6289e5c68815a5e8ef43c2013000,0x1c47139441d0a0ea25b60db5dc0a4b9f0ff90353c00,0x3d2079e519f62afca29d66253559187455223ebe80,0x6c4150243c41934aa786f945ae6a6951290381000,0x9ef7b6903d689c8ce51a15b7dd402dea3d71d2e0,0xc324a83b36d619c0924e17a963e4b0928d10340,0xc948cec80158ce14a17e96f6ca8d52a6e0b348,0xaee6e20a1af887a235d9fce68b17d57569320,0x800e6ae091697f08500ebefaccf6af4c757a,0x4ed51096103e666641d5cdd095b7b3505c8,0x289d088144b3e2409066a3615bd250f96f,0x11604f2d06f3afe8de0efb2c32f987f80,0x61a653157b2735d5ba865681ec8c110,0x1bafccb1c1321760b80fefcc0c5550,0x62ea6a1c148abc9d0d25a604f49a,0x10c089d3b6cdade83c9196a80a0,0x205f9d98c9115af2e4ae39aae,0x27c5aca27f91bf7db9de268,0x175c3db4d3e2602176c17]
def m18 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb6200000000000000000000000000,-0xdd0986f347168f577de56f44e052bac3e9c443f049c96f6c39bb00a62400,0xc6bb67e341adeef10238cbd08c2d27032410a73e9d037405a31d5aec3b300,-0x736226fe892c8f4e7263c36cb47870d84c5f4df5a704f68c2d83a9777f8500,0x309f7181284dfd15d841a4e9f2efcb36f9fbec96bb533a751180f6bd09435c0,-0xfd8f479759c6812584cff391cde192c8530939cc9804392d36201a5356e3840,0x428317205096a5a7a3d60780c410b0b2b147b260a9913a617af96b30f7b3f500,-0xe6d51813d5140c6e4d5e5d213f0348962517c25785ecd772d02970f20b45a700,0x2a3744b253cb2682c19e4c9e786bbb63ee53e264653ff81621d25d2307f57f630,-0x69ad2094192b447dc4eeeaecfe5569b9c8919720cc35f13160763771355a7f650,0xe4d2ee9cdecc21ccd49e83fa0b79186d8d922b6af981e021ec5769afc20fa81c0,-0x1b050694eaa9bee842f5071de5b683951519049ad69cd5d854cff372157a585540,0x2cd7f2edce6a1d37cb2355436562134da40cceebfd9aaefbaea425fbe3280d7130,-0x41bb0a949a561c1054fa963588737faf4708b0fd53642a59ed9a8445702e89fc50,0x5572f30437937fa7c3742ba37ed36c8984c1894696c2c31fb48c97b6f9e3cb7300,-0x62d6d6afdc4dad4e80f3d9fb14a678f31c6b5b840c7b62ea61f58e297923417f00,0x65f9b61fb7a57ecb692dd6add1e222dbcf425ce92c53dbba1e3953d3b71619fc0c,-0x5e01e26539c32b20e5f06620320c565138f569a0ef7ad075ca8f32431b3c902714,0x4d84f9bbba5413515c5c7d4a53e3f78ae4d80dbd0455da8a1bc64df2858b2486f0,-0x3935c78320aa391e7cbbf787bbbdb181504c91c3809323f751d587fecd65429bd0,0x25c96c93841fd19335918f1f907f5de9c35166206749b5c2f252885df4eb2c9a1c,-0x1652fc43de680de0829f7b896f9ce1c70c005a3eb822e273761896fa4d9184ccc4,0xbc8cf109f1f2f6e1edca59d411ece0c58fd10046fe05a809bc5f6287f97eaf140,-0x58c9a7cb2a0d2ed700b5580a997f5c75924f819b226cb7e700ddb096965b57340,0x253709247f5c86f5aa6612329a11c322048f554d7ed68f628e07c0c0ef35e38dc,-0xdd86bc2a8bd1ed51b93c576adcc3a864e0bb88b8da4d30bb905fc4bb87372044,0x48e671b4d61699e88b0d8694e97450462a92e9d523f49153a68438b23ce26fb0,-0x152182cdbe91179a66a14beeaa907f4f1ce3326b0291d73d342fe38ae9382490,0x55e2997ef32393061d7bea93ee5bdbfae4dc09554e1c7772ead2966ce55f9ac,-0x13014fdce2e4d6519b95e937606260f8e54d4cb8870378057dc41038bed3c34,0x3a3280d52bc2f13a04b33bfc7cf253aeb7f41600e224181fdc0742bc2eaf00,-0x98d2eb99050004a33709a9465554e5c6557dab19fc8e689eefb26624a3e00,0x154a9005ef02ff6ebd4598e392cf505f82924f64d3ced28bb73ac81772ca4,-0x27ccc9a43a5d335fbd688fd03d4974aba5932949fc79712f08c3eeeba7bc,0x3d7ad31103d0195d66e2ac9351851de12e60bcf30b0d2b5dcb46aeb4550,-0x4d16410b1c713f162bdabb32f0cafec532183d5f6613a715e86ac51df0,0x4cbf3a20020805394333073e60111c261d60b554acaf60d3738c97014,-0x3b0633c0a3c3272d656bb8dfe97bc8278e4e3dd9130b6918cdfcdd8c,0x21dccd84a0abbeffe377731269db918e61ecc0bc4ba549efd431bc0,-0xdd99cfd443c2ae5062ec760ee974e15d3d9ace4203e160abf3cc0,0x3cd4f2f70cf91552c074a3b0558254980e902c63c826a2336b44,-0xa4fdd08e1bbb884b252e371c9347c8507968cd03364e3cf39c,0xf4ed20adaba6bd74abb7cbd3cc937221c0f6de52dda3eb50,-0xa4e19944980ec649df5911d4a734d422130a265671b370,0x241fc4ac586dd3a538e812402205e2d003854b671234,-0x135cd0a5f616ae214c5e9100f29c46578468b67ec]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 24 74 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 74 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 56 indices rho q18 m18 18 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 56 indices rho q18 m18 18 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r19 : List ℤ := raw_ints% [-0x784335fba8e666646f75fa7f96ad5d064a8c7367000000,-0x9f2d9b61169780ac15603c6bf92cac5d8d762223880000,-0x6424954db2011f6d4f8a29d5c362e03ba6721690088000,-0x27d9f0226bfe47a3c3f3039b034b290208649f81e2b000,-0xb42d7524e2c60c14fbd1e6685d05162a98b157e524400,-0x26793009483acda2c332d1a3cdea9a843cfa203dad900,-0x6731872f0903f445d921ef7c35e5867612c235039440,-0xdeda12613ae1f7b235c461385b0b574f481584350c0,-0x18a402a3bca800a08a50f02804b3772e79f5e923310,-0x24246093739554477064f1d84c1f6dd8a36aa4e370,-0x2c4fb7df26800d5d83043e7346e1b6cb829b6edec,-0x2da4ccf6b954f48a682bf024b750734b2e629d24,-0x279a33771788c5fd6bca620204bc1415f3a25df,-0x1cf2bfbae8e5a6af49795071cbff35d07b13a8,-0x11c9fc2ab055f4e81577765f596ec4ca1ad88,-0x92590418c5fbf68c94263f552f494c4e464,-0x3e7a8ea2bf9bcc8e6f0bf1fd8d99c9907a,-0x15e461e601ba8646dbe916b601370dde0,-0x630c9b81de3de015e66d82cd7fb93c8,-0x160d1b26f65e40103940f2bc6caaac,-0x3b8d9bb758bc9780f34e6b19408f,-0x72a7371cf09561257acdff2b48,-0x8c40dfaa88bb1444a0b12e8c,-0x51f99f507a55142965d9cc]
def m19 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c4000000000000000000000000000,0x1b6d9a85e0d6f997cf6f50740b2ab283a444443a18ef647e1afda5141e5c00,-0x18799dc36111b64cd9ad082ec28ebf73261c54a9f00f520316ff868c9b2ad00,0xe19a2c0d9cdceec38f6f2b36debf1705f641596185290dc3bccd4e9844aa300,-0x5e4f64dbdac1f280ad6c9c18a7f90033054c4f9cfcb3b66da3abf46a7d875840,0x1e7c22f4ebe01a17448bb4bc584c8e5afe63c83f9f192c7b18e5fa3bc34a581c0,-0x7edb5c63722378b4c4430ff596f53dd5da253463f2c38cf271a1c174574f70480,0x1b463e8e681aa81c8f517b14a5bfaaab3847210bfd59e94b29c53a6dfd85187380,-0x4f157835bc91d3c47672be94ae84ee9d632f248b39512b749483c1d3391b75d650,0xc41a61658ff1cbeceab29209ec38ef07b945560c64daf3b6c4be38b4e43c7c4130,-0x1a47d99bae1b0f225c9487a45d87201d4d90836f410a635f4fffaa38d159f3ac120,0x31267bf438e6e4625d28cd3c35be52276ce609529c0df4d99e57dd2ffb86f4e44e0,-0x50b7f6592b75ca1449d230523b8b1ca08c53e5c5a5c4577394a6d659e7c8cd0c4f0,0x750751d35723e3730d9dcbbdc40ec8889176cf73f825874d342cf51c1ab55d2d290,-0x966a81e9c6a659ed5536e4c85b1dc4381206fa68d3521c5b19a86740498120c5fc0,0xabf0d85c384aaf429264017320076ec18d1b4397def54a5e8f6829c227f2165d840,-0xaf395963ac5a88a80fd9010a216e31b0bda158b178298739eec8c04aeb2a66750b4,0x9f784eff69e12b4e09e9f2b582c9c392ca0b3ef9666be7fcecf0e4ca4fa68169a2c,-0x81bf742b3431f6035789fda6b86b8f14a666c6248ba45e1680dbdca3d69c29c11a8,0x5e6bd746bf8b4026a9da8c3d4602fbf871aa5d7c736f6f362387a939248cf6279d8,-0x3d748f3e6ced17dc3416be5b68ce5c91721633412ff132d5ad9c7843708fff3f40c,0x23c0a97f93942c4c1e8d60e3291cae18ca3a7f6d42dafcc1a968d6eb82590402554,-0x1291feb88ccbda69e81d1e1d17bb26d04b5e301a9b7f827d07507cc4e99ea3722f0,0x898e4bb8fbd008ccde0e5dee5e7b29a2921fb8cc86f2bed7d578c7500c8a6d4710,-0x38a1d703f2774865d545f6ed8a4d09c8c6ed83e8296a481c8dd8e625a78df538f4,0x14acb432189e0f8b4fa6c39a9a7a1e96f21737c3102de7835f01fbcde65b33986c,-0x6ab3c5c2b82a085850eb480332ee4820b955a7cf1c20435fc1d111eaf5d467b78,0x1e47a66891f05927f4b5739f2d34f062d2d137d6731fdc1e9861c250cf9146a08,-0x785430d12154b81bed9f889af0eeab6cd1a0f03b3c57b2b83e01b9e20474596c,0x19fee14d31b1d9feac12b64b92f2d76d91bac016dfb2c3b78d97cdf996a3a474,-0x4d96ccc3cec817303ee4ca5cf72a3d71cc48b642dd39f70be03ec887d34fd60,0xc63a5587733be02a01cb3b3df4e2b26776d5b2b9070ef86b11151c9c156aa0,-0x1ad05edf8507529e99cfa642a472a0bfd8df2cf2a15690baaf9db36b63287c,0x308dd2369d2695227e44d247c1d140034146d6c758d3b01d7381e0168a424,-0x4876be7764fc62e43a4c2de3994b74e9a77e041f9f800056403014aaff98,0x5785ec48658b5d3d8d7629f3e9d8b1ef9949b59859ee1aae8adf370a6e8,-0x53a6ef4d07dd6c1b2ae304695017d1b88756c213dbb042545887459044,0x3d85366d982f5c5e6f1ab6ca7793e4c71df6382b434079bb58426f1dc,-0x2199346220c332932306cf18b21d96a72dbeff8bbec31d9821509070,0xd037391bd22c2395d203a3be223db087a6fa66bd6de7d53400ed90,-0x35cce1b9007a13f97577363a84d89140ac28d788970f38e3b738c,0x8863af815861deaf2e19805b280c6c949e3cc71e09416ab0814,-0xbbb710d58e517f4405f9e1db507bed662d61ab2853ccb7028,0x74122ca4421518bbbd32beae3c92da708d94c776e772258,-0x171b77582a554870c4803d58d7020a352a5a6ae828914,0xb1bdec0409235603fa3f9d5c8330018fff78af40c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 24 76 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 76 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 56 indices rho q19 m19 19 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 56 indices rho q19 m19 19 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r20 : List ℤ := raw_ints% [0x1a6053f4961c5485449f1d442d2e74cd275855ec0c000000,0x22e42a4df34a3a079423397a2884b35831254b7dffa00000,0x15eff86aa4622dbddb24330789a96fb45243daf59a220000,0x8b95b96c18204e46b98aca8cb3aa2e1dff2af99e0fd4000,0x276a52ebfc4c744824c6c0856c6610a0b1958b9bf84a000,0x868ed91754b2ce4538724d2321e3fc68c85ae90ec6b000,0x1689c8dd20f4fa7e4e4f3d817dfa5e885c504eea9a7c00,0x30a0f604065bf2f480a7dfaa69765b9476d6700a96ac0,0x55f2401fe92c6fb85c2b750b3375c3f6c68d94010e80,0x7dee36def22f20b782663ebd955a610016871f751b0,0x9a3807a521b4d40634cbab77a097be46020c8e4c80,0x9ea8bc21d12a63730cb5b5c3f81675fdd61adf9e4,0x897931f2c7775b659881ba3f0c1651d2ce6d41e8,0x6457710280a40451f1350654380bfe3a5efa1c1,0x3d8fd5a4e33714b6e9070415bf35cbd84d5880,0x1f9918eaac09b41656492f2669b453691bde8,0xd76b4bbfc6430e51af70ea8d3f8d14c79d0,0x4b51f224b2a69cd01deef8250a927abb06,0x153f96449dde1459bf17e58e250ac0300,0x4b7d31ee6fbe6fdc4107ad43c2d0be8,0xcb45fbc6de86bb4103f4b40ec1488,0x1860f0d04007867cde63da83ed91,0x1db61999b3ba6f6a24d5fd7d40,0x114ade8422606e7aef0d6584]
def m20 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad880000000000000000000000000000,-0x367741c03a17000e9048bbd63da415aae42f4430904fd2b4544b6fd6fad2400,0x303ec15f76a8d0efebda4fe2352eb0d38cf22bcecbd3fff4000526b32ca2f300,-0x1b9573238ba0bfe2400323fadb6e9d495e41b2b7dd74872361c66140094ae2500,0xb70e434d7c59701935eeb81c1c930f35e6526518bde95a4d751a338381b3fedc0,-0x3ab19d2cbdf67098af1014e5249e0e21e54ea605be223110b60d4f2e3457914040,0xf234d987d5c6d6971eee1a7da44074c085961dc7f77d6d0531e2a86f5390fcb700,-0x33a030d8c4e74b27f97ea0869d16f5df36184d2cb5154cc5b871ce7952985731500,0x945b4a4b2945b002ba326ff4f60b3176b1f7cf5e70d14d1a8d679767f7f31247a30,-0x16c7a68a1ddcfebd77b1f93755920460a57df8cdb8346d0e11a7ac80747d33f2f250,0x3060a646a406859411e5033055c43cc5a9786ad63de628bbdf1def46580acfeb7a40,-0x5993be41f08d701d7c9cc66ee776d85d8ec7e6d9805a006e24a98fc81524bac028c0,0x9197d32bdf044a2f4bedb1ec8549dd7d14c57220b3b278c82f2556d97f4546218330,-0xd0d29e5009d4551b0de231ff6ff76711128b93cb4be96688354e1ecd2c739cee1250,0x10967b4006a4cfcdee4fe14f7a812be2f1bce0a5f8edd248f7693ac78543f549a8900,-0x12bdc986d129ef56c2a7bb8cfb3d863e27276225c691348394007789f7b78c7aab100,0x12de3627430c36d59cec5509ab53e5192066b64d7bae33a5195a9bbc3a62ffe47640c,-0x10f4666ea3b9b3dfe86368b90148589b3bb1d08a4dcea14eaf77b2086630e987f3714,0xd9cd19bece142b4a9c41b4092652764317b7caafee324f447cb8b6830d7a7ebef190,-0x9c4fb3c0d8b7d37e3a0e9f47c3c02d9b45fc0369c2a7625ef140589ead6822888830,0x6443f526b825228e2f5706790e27347cf363b7990935503e74501f29b8552c32729c,-0x3972199a2a0c73eef3b11fcf4f20801e566440eb73f217541874cece021f1f25f644,0x1d5cb4e06a9cae2db06e1a4687131302f83a03d2df45ec882df07bd60bd9d901b3c0,-0xd5d829a2a5e46aeab73182d821db5d24e5c1c6ac90053dad98323cf51599f1c82c0,0x567b9cdd0c357b88413d08ae4ab62ae6e7e97bbafdd82327bca891faedf9f75f39c,-0x1efb73fc0a166af46356b40a8996ea86e7a26c83bddf51b76cd7914091791e36d84,0x9cbd031d79cf1293b46ed74248e29e405d7f31a4b5272fcd6989e20fcf47a046d0,-0x2b8be0816f816e4d4fb7d7fdabefb024ad9a4742fedcd96efd6b553b98e154ea70,0xa9310bff7b872f0aaccbe9232a0c40f48e943af3ebd012677543a4363752a4a6c,-0x23af0f14caca96371b2ca74f00e71ef40ac622baff12a285ecee6f06e3e156d74,0x67cdb325a1fdc7117d96cc1980b23f37630b74649657886b85caea964fef9b00,-0x101fe96b52c0bf1c47b8d75256ee2afed62809a13d7d1cd2acd080402358e600,0x21e12213f8fd0fb4d9f09c1b450010fb548470ae217afbddf913983f5ac9824,-0x3b6abd868f1a64b90f9c0c2a2781b2443e9d7acbaf06e713375a8bf831943c,0x55a8339d4aac86ab9a133f3b4d8d228447bfe24197956411d513879f37a30,-0x63a25c24b70f7dfcc88c41bb774bf3b67c396f221d566f6266235bf65a10,0x5b6452396481497beae46b195c4dcc5250f8c981e6ae0ff90c163f7a614,-0x40401cd253f76666ff62e5b2b6f0f27a32a4bfcf7a72c96a6cd79ead8c,0x216403489b63734c420e44ba88b039db8169bda9dd8ea35346b6ad540,-0xc3e0e91f9925a3abb7bd8e36db219ca05e5e7e0de419105989d8540,0x2f9ecca5050a27c6e03537efb64c32f40be634d8506aeb33ed4504,-0x70cb26c25ab01520ffd7ccdc9a8c74f0cc2dfc1bc8b0bcf841dc,0x8fe199c73e1bc739199d77f9a256e2c721c95fdf411199fc30,-0x51b2fb68e9909b9994ee935e80cedf2bbe203ee2a81eb190,0xec7086b76b3a0bbc45d37517cf1f20569397fd85ffcf4,-0x65f4b85aabd57994cfd9d031e26304154053e88b2c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 24 78 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 78 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 56 indices rho q20 m20 20 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 56 indices rho q20 m20 20 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r21 : List ℤ := raw_ints% [-0x59063609eabbb31b7d11e3b8f80f51b6b0222d4c244000000,-0x75b36759dec965b99407eba240fa9d3b9fd171ac91ee00000,-0x49f5cf76ea489b67641f33a7009c63a4a8f15cebf26ce0000,-0x1d64f2bf74494083c992af432ac095c3e9448dbf556094000,-0x84b7360e48b7437d24a79b4a0650215aa9a3e03117943000,-0x1c4bf7b4b7cb96d0802b10dba4c72c23a9145509e4001c00,-0x4bc6b3ce3c73b3e9d2f78f92925713431932e05940c0700,-0xa35c36427d8b5461ebeb79d46a0ebbf28b544c28bca900,-0x12076d0b14fefa611b3877b5e28135d9f153b1b276d100,-0x1a6418fba61378f74b58fa00b158c2916e78c14bcc1c0,-0x20491a114374dc67e617cffee94034e7586f0ff840a0,-0x212d6ff37158feccbd762a7d2196d11445ea49cb270,-0x1cb642ac3b2440d49800ee46298a44d9e2f8fea960,-0x14edc3502da164ed141944e7a6076cf608ac9e3f8,-0xcd25112cc9bd54b9b06e6a6ad3e7c0fa7e2fc77,-0x6920a2d21ecd41efdb466f110ab0d1f3a5a050,-0x2cb742411879a2f7e41b3b401f3394ae5c494,-0xf9acabbf2ce03c073db960f1bbc99609cb0,-0x464941c77dfd6c3f1392887078e4abc49a,-0xf91effb0c85036414dc9c03386a06890,-0x29d141503b312094618c7ffb1a17194,-0x5002a20e03773bafbd4d247e140d8,-0x6131eea06dab85394958720f6c7,-0x385ca0c3e56e4ea1e97c19c70]
def m21 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b1000000000000000000000000000000,0x6c2cdc1e1d79890d144f0bd9e770a192c5f1941e179aa83d635228b085f75c00,-0x5f223bd6497f13e6519944c1de7bdd767d553d730f0097e306875cc04e7bb6d00,0x35fd5dcfbfa78bf20142abe4c821652eeed7d91c351ebbc347765b19d5d6b64300,-0x1638ebf7b0e9d3edb19e762fa91e159fc66836b3a3e9ceea30ba13a897440b0d040,0x711a813541228a49199759be947cb865ce9ac72f85458510625233510335b7089c0,-0x1ceec274fba7bcb9ede3c4f0e0697d85ad51dd9673cb5bc652d2ea8e34038f25ee80,0x61d639436b6a0e640323cc6aed7204a047d212fda6501f926d5cd6995364031f3980,-0x116b104d15f3454df7d70ef3dd79defec4179720cbf27ab06151b8f4e481d95fa0650,0x2a677957b4435f932e603a1d7b2647c6650127ac6171fa22a6f554afafe19f56b7130,-0x5934a9811a8356a4ce31e50b41e7be94366a23c1790808dc7af25e065d8146aa793a0,0xa38f97139f82f97f407b0c5b2f7087e069da2f48757dd24ca5d46515d5afd97fd2e60,-0x10724123df4706c94b339a10a0c84e4bb9889099f3b64f705a9d95e6fff548da4d53f0,0x1756e9843a1969d27b75fd92f490dc3887230d42d05bb97da64841733926b769234390,-0x1d564faadc170f7bab7532c8571e863a1cb067cf58fa1939c6cbf834748a9d67593ac0,0x20c4091edb69c6bcbed1c61d08cab7a0395464e13466a69c62eea363c5fc16b6e3cd40,-0x2097ac0409f4d6861af20b47d2fcc793d47a074d47fd2972d05086087c55bf9dc399b4,0x1cebdae603c45b3329cd673164cd7430cac7c41e80cb5bd98fa77637e82e308dbea12c,-0x16eab099761fbf2324862864357e8491c2d2bbbea8a0c8a2e02021d6e922fc46c662c8,0x1038c197da10cc4f53f05f7fcfc6eb65981fbd0e20bb09e3a7c674af852e9887198bb8,-0xa4187bc2d586671160c0d3217b8750669094ee36a1f1e711cf0d664f4f7d432f3bacc,0x5c994dc57619f1cb5f9f80cdbd34f60e7551741067b872d7b42da70e9d2a0610f1e94,-0x2e94523b716fe0c48d0b83ad92432b531810daecfcf692380591780f824aaaf43e1b0,0x14d920adb482c0c7a29b742644d1e55937541082885ebfc28178c3792f9ea2384f450,-0x848633223f9d92662b4b711bf9f9693831e20c6202da4fb25c5c8f57959298ea5b74,0x2e976e5bbc97a59d37c14cfcff3beb087470d0e40d5521fa66d17edddeee1a10a7ec,-0xe70d266c9bcca7e92859d2d0dd16a8bf5d72e8655c924d811057ab927ced98a59d8,0x3ed8df78b01a3d9b6b2192f6ed4dcb9df9e5c78fa9fa3b576ac0e5109511096daa8,-0xeebc4b22fd1e7e12b43d105af6772d16bf10cf25c1b4a60e79837cc4d836a0bfac,0x31274d71bc7568a4c2aad44aed5a022b41cbacc268efa5401ff68791de71053434,-0x8b598b34963ec47fdb9716f6156e6214d96549fbe67aef102e726a3f80bd8ace0,0x150e55711e440b514a104e12da64a5ec36d16166707130eb4cd9df8034820db20,-0x2af16ab1eacf74deb251c8d12271fc5bdeb5c2e03a626d2459de117bb8aa247c,0x48edeee6e35ea224b754eaa45a726e5cb7387ee92122cd88880540c08fe0c24,-0x658932bec102be1f5e9a3ac000b54781ec6c3ba9b702cc4ca518def1368178,0x71b5c84c9d8f1bb90e50acd2d2199fe9135262edfcdd40afa4f45f75da608,-0x64128db5503e76d1d368422137e282a56294c62657d15f3f09d7546c7f84,0x433ae46257006f365cd6500c769b19e99acbeb8b0db39225e05b58f4e9c,-0x213c3f6dc6a33c37bede91ddb9eb0f8aeea7c411a772aa8463c73f9930,0xb87be34119bf2b33fdd948a90696688e025f219e86b47badf5e558d0,-0x2a2e8dd68494a9fea9edc7e8d2d2d43cdad630b84473d24aa98dc0c,0x5d50b4f4e1066ff23227985489727c3bfcca997c5ad58e237f994,-0x6e4a6c30c378e0d1391bd684290495836a1ac4db455d475f048,0x397f5c882e9b7bc3ace2ac3d1f6512d272375bc9ea074d338,-0x972c08ffc0672b2ec76989e62f72beccca8bb51dda65d4,0x3a78fe39c71248622aae77e1105f89b7651c39bf54c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 24 80 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 80 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 56 indices rho q21 m21 21 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 56 indices rho q21 m21 21 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r22 : List ℤ := raw_ints% [0x12228d21990a0938b4374923bf006ff566480bc722170000000,0x17f6f4e7e7ed4ab0692be7921d46ee0c98960051b75dc800000,0xf0cfe1404a107f56438a4436c36c59ae1f3ee8ea5b6c280000,0x5fa6f223f92808ad184e3a04736982b5b06ffe903b7f8d0000,0x1af9abad9ed0c22463a6cdf96d4c40c18aee73e98b4b970000,0x5bf6830a7e2dfd770b87100a498a294f05b6c20e3518e6000,0xf617e8e13f48b8a0275d55a9bbf039cefb6426234cf76800,0x21220ce2ac186a7cbca8d6bac93bf1b9c0b549962ebe8500,0x3a7563536170f4460eb541ead846a15b40cb4108c2bc000,0x557ef6a8ac940fdc7bff828ee3324f87688c7383301600,0x687dc8a9c536f7ddbfeec54763ad6e8e9c924b6db6700,0x6b44378e3c8ba74c3281b187927357ec509eda8c19a0,0x5cb9726340217b0576eac282a3da84d0f051d528b00,0x438198f5c143a855743d8bbfe22153c0289abe6b20,0x294d219beef12ecadfc06c82757c3a9b00ecb0628,0x1522699a2684b6df56c36ac1aa035ad76d5fa249,0x8f9acc1e52d4eda2da1965041dd3e417162340,0x32070a0dd31300fdc49bb324df5238b2bf16c,0xe0e784e9cbb903fce54bb9f861b5b9b28d0,0x31b7a36aac7a97cc8e6b3fbcb638ecc726,0x853826a84eee70fe54e27f812d6c4f00,0xfe3c8b9ae4e32d3d825b43c0a894ec,0x133f4df8b99674be9a782e8f464c8,0xb2016580f4479e5e3620f7b079]
def m22 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb620000000000000000000000000000000,-0xd6e283edb2f56b6b10dd66cbd06fa83bb7300efa4dbba5f6f06f2ed6038f42400,0xbba81d18629ed4041aa857ca000d7b93c0a6fb2168ba1b3d20d15b06430fb23300,-0x69ba6c2bbcafc13da355d08217e5191e32d1f4811ae7fa7c8963d28d469132bc500,0x2b3168b6e42b51c2076af1cd09e986611d61a34d0d9d4d1017eddfce364417f0e5c0,-0xda23385ba7682369ac8d7e6cb4bf9ed9ef8003db9580937e0831159ea74e59c30840,0x375acde45f7d28e0a04acd00dee8dcee03f9dd41520b0f3c6ffbe80421974a4890900,-0xb9a1feb243537e67853cc926358c4e9bf8cc3ed8a3cdde3021d6013d101d2e52a7300,0x20c3d1da8503948dfc1f2ceb24b2f45bc03be674250375f8d01e38bc29dc83d0ae5e30,-0x4f0dede70e53a5fd562cd32013dd650fcfaae5f5df0cd04d1a58c2c3627a46731e8e50,0xa4c486537822b96953b00546e626d2d2a23cf5c71ce0c69bbdc112da12105e6339b6c0,-0x12b3337c59e22992294268cf979f22054a3fe4cffcfe0b1f0b0001bcce5563a5a011840,0x1dc8b869236e75eac7eada16cb56067a18d7381f48037ec86bceea13fb9684d67873d30,-0x29d3c9fe7c7a9c81c24c68727d8cdcd4792bf7da08a63863ba972eab512bda2232e0050,0x34014f08468b0fde7d050637c41f1add7ef3a47af0e7066775209ead5232224d94e4f00,-0x396cd3e6676d4b78606e6796b0f8a50ce80ff2c38aa4354551e81eee68f0574f6f9f300,0x38721bc7650d8a72daf4d06bc129705862914b51cf945b5859b2fc10784da9a341b340c,-0x3177e1a068ba5cc86b1f3b049d6f7ba299be1ce03c40ef7fb8adf382ee55c601529df14,0x26b0b61154c96094374c55bdfd637a226846f5f1de375f8ade00d9f41f1f6aac48d3130,-0x1b03eaad92151f77940c9608fba9b4de2bb5bbc7c19fce3ed0ffa4bed7741503d415790,0x10d63415c5dd10b63478c420f355eecaec8dbe15787ff6846dedffb9befa8fb21da8d1c,-0x95bcec8cd14573918d94e50cb5027fb598d516e11c70c6d9015f02d3cad2ba45b4bdc4,0x4a2244690a5c3a2b845d445ee6d6d30933fe9d3267c44633ce71fdeec92794cba08a40,-0x20a1162fd1e672353ead78c7678c44cafe45943e140517937fd76c86c8d0fa4ac1ae40,0xcbc4aed157dcb02e2190aae5c34159640898a18f4a8dae9175dafd639e0d7a2e6c05c,-0x464e83afc449ff6fbe58a0c01702747cb5f9996035c14b36c7d58f5d0f5f8e387a8c4,0x155c822a83377a65778a832579237111e52732b141f259052c4b7ae496056027366f0,-0x5b04ae1b16f8d9c1d30fa3d39a3c41f3dc0bc4fa252fc7f13cb503951444b847af50,0x15208171d2fb7aaa746dcfe205b392a27a72262cef810ab5851ba6bfd98f82c51b2c,-0x43f077ad5a029fc2217d5dc0c8d907d665b495bf4eea592ab4b9e01a78ff016feb4,0xbbb1ea72d2f44b320a2a9fd67c4bc508cb3dbcc97970b7a9f900e18b75fed12700,-0x1b95aed654bbdbf6397da35c1f60018309fb65801430cb0b34218cfb9a39264e00,0x3699bc82292ed9fe8638938f626255130d021bb3fb70345df175d48a26cce0fa4,-0x59c6fe2a3913558715d910b74b8645040747ceaef5fecb98e2621399c72474bc,0x78af73182c71d3cdfba6a0e7fb63f708133f4714ba2b2c8b7e0d51b8a94b610,-0x8217ff7f6f727c5dce85cea86940b9d2d9300c51f4c2e85230546c06c0d730,0x6dd0833babcd32cd2041cec5aa5a5b5839d8c906117261c9d46cc565f7e14,-0x4679f17bdff2201e18e9fccc54ca1c59eef45fb0e591bf2b76177aa07b8c,0x2121089fc77d75ea017c7dfc4383b34d47759d66b44d563b0c2a6091ac0,-0xadf060bd74bd7276be074827ce4056d5aaeb9f3d6f02e6c73436071c0,0x2563ec4d053a248d6d63c93043d56fb5b5f128770264000d5cd9d8c4,-0x4d3a05958b842bb42cee1a1006a99e53b2b796553dc86b629ed61c,0x548bc5937d327f0d34d026f2fb1830825d133b61f4c53f792410,-0x28757f76339a10634e131ce7d0393c7ffb7dcbd131a0cff0b0,0x60a1f501d77c100e9fcdf5cc2d7e60a1b3f317cb1e3fbb4,-0x21873f54e6b391bc7bf49c1e38d676cc7f77e667ba6c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 24 82 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 82 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 56 indices rho q22 m22 22 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 56 indices rho q22 m22 22 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r23 : List ℤ := raw_ints% [-0x3946656f8ad1c13160f04aea2bb9baa96623824141d429000000,-0x4ba6ce8f74038cfd4a4739ffe90777ac8fdb89079e61abf80000,-0x2f7d0eb2c12a1a94125070796b7c1c3e630d9afa7a1c60af8000,-0x12da495c38f526695ad958126dd2663ca3f83da15834f0c65000,-0x5504d8f3765934316f79704c8a19f7db4cf20eb77dc6767fc00,-0x121aa2e011a5990f934051dd95849f7c0b43e095ab840d09700,-0x306a219b09bad4af1ec1aa810b6e9b4526d8c3b43b1b5d17c0,-0x68382f7bbb7903b049cd06135430fc6473f9d36df283cbf40,-0xb7bd86a73d8b96ce58280d5d0f7bc0f0014556a352d99070,-0x10c801e3becc12dacd95ec656cbb5a34ad11c5711289f590,-0x147dd68d56b9173a31599821a0b33afc9e1773e595e7474,-0x1504027c7fe7b04372826cf1738c30997f383dd69cfa5c,-0x1225d6134108bbf08fbf01036bdb5ffc79a32187878c9,-0xd3286df2135507e42bc981b0feb39f431ed433971b8,-0x810859ae11e57e057b5752f2aff3b9d28c1fe2e5be,-0x41f0ca5b45d3daac005374ce66dee8e02a3b084ec,-0x1bf692420c7c1d6f6fbbca307934a2fe7a23573e,-0x9b9ea550ecee5800a25718d8378c7c7fc36960,-0x2ba679d5d0e0a2b683c061736e62e8ddb9c3c,-0x9a1922deab4a0eb626decc6e65a0ae48f74,-0x19c0dd8d2ac9f99056bd1b6f9512125321,-0x3108fc914011e6e407418c33dadb9698,-0x3b3eb5fca24eeb027b8bef3299a23a,-0x2225cf883c12587368847312c3c4]
def m23 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c400000000000000000000000000000000,0x1aaee12833e6f63e2e3b576d623e3345262451d04f69b918e71d76abea6e5905c00,-0x17249b874eff5206025f1329f200727dbece07c3362c560124f666c15428e6942d00,0xcf26fae5533424ef7d4b38a3ed7c5720a0f2d36ebad841b90b1087f890a1bc34e300,-0x54027048d3334c79a1230a15195c7c11ae937607bebf00cd8059d9d68ae312f8a8840,0x1a5109e80db35cbfd6d5e6546d0d410c0aa4d9cc5939a539441b7dbdb2ba5fbc1951c0,-0x6a03360b291fb7461fd0e1bd504c4217b00f1383eca7d4e119333e579f8ab91dd7a880,0x160a076ff39572ef0cfc41d197e2e82e9423068d0de27eb4b5f8905997c8fc56120af80,-0x3db7282d2e9d7c349a163c92c8474c51e732e4e47d3247cd0241d41a74b04ba5c5ef650,0x939a3375a6dcccda70afc23e7a1c1a67fe0d13ec0e5574bc0218bd25d97c43024a2e130,-0x130d6d6545749fd0b98f3e679a40042fbfdafea00f09df3ac5871248bf90c4ada84bfa20,0x2245135c3b3e5cd9826f5badc691ef1ffbcd9d6ffdd4cfa7d24c899a2b0941f263a263e0,-0x360b7f6d769fe18c3ca5e77502fe047348812c91a36033a83391349f6c1de1c568a862f0,0x4b1e7088211e7eb7836345540cf88208e00a1b03d23d73c958bc6a6d7b9125101deff490,-0x5c65b6947cfefe3c6000eb79e79e98c1481d2dbee9f027eac0e311f0e4b754f6c069ddc0,0x64e2cea13a89436fd95579f100ebe91ea178c998708bf0c19a212c075fe9456817607a40,-0x6201841ddc47080e7eb803ba348aea8b07b218f0df6c68d70799378bcc5720f2ea29f2b4,0x54d706353aaae9ffb8689f7ca38bf5748a75441dbd698a8841741a6d6397d0a758ba582c,-0x4181156f052daf8f94346ffeba46dbe22c6b83d958e8230b4e81678c68f1bcd6259cbce8,0x2d1f59b8dc1b6ba5de679a1a207a0dc2466d7a3d62cc3e2b050381e973ceafea0477ac98,-0x1bb955479100de0af06b38d1053e8401e891b103d7d9e53efe61ee9543fe47abc5b1c18c,0xf2e4fc988b97733da58a760b298f194201761e6526db27b2688efafaa328bc2c0b6c7d4,-0x765e58ad0c838acc6e69e1a4d2299eb71aeb1fd63d16c2671611fe44193464c498fa270,0x333c69f8bcad49ca36ba30be6d31908fc428c42430616bc378cf78e975f634453bfff90,-0x13a5d13d5c70674926b36b17be180f930f7488c47b272c14e8cacfc572297e3fe5ee1f4,0x6a740a455160ec4f8a54be8fc792d62b67ac32383245cee322b9bec16edcbf39ce036c,-0x1fb4efa70f27bc2fc91570354a6df4363d25cf2c997c099c31d8ec731f1e0a0b67df38,0x8444ad7e07808a5d345e3aac9773baa7214e239d9525cd7e51cec7e4b3c0c8da71c48,-0x1e04181a265318fc16475827a06752a81a5566e8343ca2bdb144ddfef60c9073ec9ec,0x5e384c1395bdf3b3c756a069ac701f70254d850d4209882a2dfb0aa7400547fadff4,-0xfda45acc9f465242e57b7d2ff62c9145d18a2a98c966c55846e7342ebe57a0f8060,0x24409b86ca3ed9862854d8680e250cf26c51734da730e71c304e5bd7a573fd827a0,-0x45a20ccc40a7f29e038dd68a112343279b0e36c763e2d4aaa3f06530e8f549f87c,0x6ed51b55e4c78e091163a44195450f5dcb63fca5765d6ccaa043454036bb1bc24,-0x8fd2eea53fddb2047e7a0ee4a90d76dab6317815b1551195e1104c81dfdc3a58,0x9530fcb2da9f692035055f6a0508ff4f33c5f159e588dd222d6e0e1f7327628,-0x78c14f1fda395e9698ff3c04d54334a22198bdc0d95d89c022a7e9baa3d6c4,0x4a0215d022b5108d346957a8c7c383ed737018b362fb00eaee389fdc2b35c,-0x2111960381e42ffafd3ee6d071ff085d2229bcb45451e28b11da0ce683f0,0xa42963808c4d56b7e9f08d2131c377d3dd0e8b9857a416fd2560dc8210,-0x212a0410d6d76cbefdcd45fe3da2ac5b98db79ae69a4238d448da388c,0x3fee4d13ef54a7bb7be12555286fb2f4b138ba793d44b6b07926714,-0x40cfecd489fbf14ab1c1280659a736302aa85df671d26d8105568,0x1c770f7827e73749314419cb78628c63d857d62f1c0a0492718,-0x3dc184ff860a51bec2aaa8aad249b0d1f7d8bd026e943694,0x1338bf9e108dd9ac6ee75fc63e39f82a0a637911b228c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 24 84 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 84 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 56 indices rho q23 m23 23 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 56 indices rho q23 m23 23 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r24 : List ℤ := raw_ints% [0xafcc336721441c1d0037f049df602e54ffef258185f0c84000000,0xe819f1c080e56ce0e18c5828198be6d0a15adf261e20dffe00000,0x91a0e248ebd2b07fdd324842fa114dae05ed06f0425bd26560000,0x39c8f18496cf4c73fd6acf596c40f76d0fe57118acea14f0fc000,0x104735d25bef6f39a892fb38b60892f70de508a97a457b80a2000,0x376dd2bce7034327b2f10e3c5d810a78bc5cde5fdce370c28000,0x9423b81388398cc158650cc5618a805ddec3546107c1e101000,0x13eae9c0dec9375b26b0fb334b01101a81aff8ffeca7893dd40,0x231717d0937e9a3e806331ed2264e4f6ef7188463a7d94d880,0x333d0b0b40aa246b92db96ba3e7daa389a808db39fa65a3d0,0x3e840e7fc730b784bc5aa8e8c2e5f1c0ea62abf7904139c0,0x400ee82aeffcffc9e5cf1c7be61c162a8d02c0b440fe17c,0x374393c2a3e4bc18944bd438c14b26bc2f5e59f8998328,0x2825c2ebc6a2aca681edce4132e60c3ea771a9c93db17,0x1881749555b8c2a1edf0a4098b61e1016463d59ee400,0xc821ac011fc950644c90c63da1c77a1c103433d812,0x54c1f851ee0c62328fad0dc6138d16ea7c0ec1f50,0x1d704697dd13879ba332bebe8d6763ca19f4e742,0x83e94dd14b9fc5cbd535dd0278a02188288040,0x1d0e42b36e7f8e6e9e64ba889b369e87be054,0x4d8c7b88b50d12ca80912bdbffadb873fc8,0x9359cb7f4ee339dc1418cbfbce462683f,0xb1a05d7b5688fecc6f0a4cb52f29740,0x661f4dd312456fb51529df5769a76]
def m24 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad88000000000000000000000000000000000,-0x3505ba9abb05f990e7f409595659df21cfd15e8399dcd6a03fc915ed1635cc7b2400,0x2dae6a35c1a8009ee114c617d6a0dc389d8a04d348a1c6751bd7def644e1febf17300,-0x196128e23366b3027db7580ebea17009006d6aed20f9930e391283f98b334d49b06500,0xa38136acdfad8b3df2faf3d30b17a9a4b8ceda95e54da62573e771b22c1ec991811dc0,-0x32d70c05d9175bb9b52988af05dcdb0028a5fdd0905b4907d76cb6e7b08604f57f99040,0xcb3b0d3bd1843dc33b130496f0c192d0392fdd8e965e1210de09025e643b2cdbf6d6b00,-0x29e9e859ce395140269c2adefe56da7ef0922488c54a0f3c783b30a1a71d8a568b134100,0x746620e950e3385e7892e1a4c0e6ff80fab3050850a4dc983749dc687c7f5e8f34b9a230,-0x113fe8f430e28bddaf1f654dccaa0f47c853860f3ee6dbf3998743debd449728be09eca50,0x234e898a994a18b71fea48f8a8e014df30eb98514f6cb3228623a01ec6ae697c49af35740,-0x3eea64f41300eb425a4281f3d11c1d46c5b8f5ab012355b2a910c99a6028ace873a0003c0,0x6242145696a2f892a89de4d1306d6fd53cafabdcb47326e49d83884748ad67a39844e1f30,-0x8730cb828b5b5ad078bb0c21b89ba0c8fb84a9d95e0a1653bbb25a108933f81cd944c4650,0xa48791ded7f3d4180f1c021ac048ea92adcc484756854432ff0e5d9fc1a132c5a632f0500,-0xb1a93ff4b96a6bc63a07c5d150112355fa05da8c697808ca140b7748009a958bdfcfb0500,0xaa983bc9b7bfa106cd5e037cc4c0140738bfb9736cfd327d2bc9e46a94a8ca2da7a9dec0c,-0x91e3915f932cfc065127d2673ab5d516cf6453cbe7de0353c3184c4a9f57a98c8c9859f14,0x6f3571b35f811b69227213d61b0e2170f4d11319a0ee9b66df9e21e34c9693e9cd16d6dd0,-0x4b956cfccbf007f4c85da367a70316d6b0f6901d76572d1f8134fff73de5e4dff2784a1f0,0x2dc9b73c2ea9e979010bbc4b775e49b5575a11fa1427cb12dc3db8f887745437e2ed1499c,-0x18b396f2f144401a9d2a557dc904ca1cc333a422c734eb0a04b7b89ad7a346f888f5f4344,0xbd9905511cb61d1a452493433eb918a7281b685b029380302aafb3b432b921714bb904c0,-0x50b6e8718b524f794d63fa95fa8d919fd41fa32950d56b1cb51a43d1fd2b00f2b5de65c0,0x1e6964f8097bf239ba2e18ad3f68655c479f2d6d2530afc6a922626d7d88dbd5146f3f1c,-0xa1b90f259a3a088dec1833668e5441edfb49e4a72c78006d9af506beb1868b2f252b204,0x2f388f27e0c137821da132b89392f2d43044080c81d1ba6c23b9a773b351b8d92596810,-0xc0dc1eda631479b33a53815625885d7a23e9d1152cb520487d95da544d3f5f2c1b9b30,0x2ac9992959be197963221a90d039b40e12967352e3ae5f4bbdd1d6bca0a607a54a6bec,-0x8318b503b649c08b26702b27d89953f2967d3919066122372090dcd54f612ca76eff4,0x157dc4cf70ef7c6ed7bcc59edd3a78375e58b56fc0de2470de4d9c31f452cdf587300,-0x2fca94943af8a010ab434cb1d149ce7ec691169a16b318eeaa856db2571d713d5600,0x59110b41e5aaa885701b237c1e893a27715eb44bf4e677d7ed3cde906cea32c5324,-0x89347063cccd3e63a3448fccea13411c0012efda71dfb525f1cac0b640bc74893c,0xabd605d713d7b3bf2e9fae789f55f5776233b94a2500114366fc91d1c440750f0,-0xab7bfd54965935d9890bb6a465be832a4e8bce2845aa2eed624f99cf63337d50,0x850cdf939ca980282c09dea50daf7dfc5124896a0b7f66f6efc1d5647c45814,-0x4dd8978735f7be203a68057c94987f9a8afecea610821663fc67d0a2f3678c,0x210d3342d63cf06b2c0ae99667536eb3082146c04a37fce2d80299ad77c40,-0x9b1458d7329c01e64228ae89b77edceb0cb075a18f0fa562678c7637240,0x1d6ec71350f7768dc6e9e71e5c74ba44c2ce2fd32f870fec2c882d4684,-0x34f01af6d012050ecd312a729ed579bf141a99c6ee7680fbca10105c,0x31af420c73de05a23198cdfd0edba37224c4e04aa3b188d9d22af0,-0x140601ae535dfe103214544cf5425bfcfd238d8d01cc75e3e8d0,0x27754bb68deb5c71b9753e611e58ce36c10ca30948e25ce74,-0xb048afc4d711cff0a35eea3d78840f58877e2a08435ac]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 24 86 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 86 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 56 indices rho q24 m24 24 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 56 indices rho q24 m24 24 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r25 : List ℤ := raw_ints% [-0x20dbdcb69a67f16cb8e25812c6b4fef7760cf1a4bb98dfe96000000,-0x2b5d7700390b0f4bea9a8a92fb3261cbe1718d2ccd8c0833ed00000,-0x1b326afb7b49afe1796394a963c68bcdf335da43a00422fa6ed0000,-0xac961b8108369f9e349bec9c331f1b63ae916106d9c218eff1e000,-0x3098042ab29873977275ab45a4f0aea8c2c060fae033300d9ba800,-0xa56113bda9ccb551340336467717f23da0f6797ee8d2f21b5ca00,-0x1b9bd69c7b4c504a0cb51c78bde3278ec1b7bacec9a93ef6a2680,-0x3b5b39b216375ad144fa7174beb891675836acd8032255386380,-0x6880d704121c8305efdb170f5ba6e27528488a6d0006e434960,-0x987cb86e1d35b4b6d429ef7f89dd1cba4774724fe62109a2e0,-0xb9e86ecd766cbf19d916c7c27ee4dc5dccaa1b12e9c9f9368,-0xbe56d445c30b3bdde0b5bfc264780e7cd9ac279b0dac37e8,-0xa410651f90f1c700c31a26244543623c8ecac054fd07a9a,-0x771302c05b368865eba31e34f8399ed9736d16b9a0fc28,-0x489b81a26e5d2ca935f9158318e99fea4eb879b0ffcdd,-0x2504f1d058300c858899608a416b33e13083446c3af8,-0xfa8c2af0d441d23e54c9e3e3ecfe5b2d445ad7c978,-0x56e883ebaaf6b23fb6655ec5b619655f8580c9070,-0x184dfe6c0144cfd141e8e30e4efb711e9228d3ae,-0x55860aa1dd01ba959926918433807541ce2bd8,-0xe3df8ebcd7b757648f95f0ad6c31dcf5fdb6,-0x1b02dca4957c8b68e94c3e9248c92e6c0c8,-0x207e9978c5ac1a8b9c7a7f9c8c8462265,-0x12a3cc16509473e395a22c86cfe4388]
def m25 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b100000000000000000000000000000000000,0x6960e64577488c799e2af207e750d7e92e7ba71efa1bdfd67b959a7b5b083c2e95c00,-0x5a32c1a58112c9fab2b15b89d3a4167b4de29c325a1bb42e51dfe0c092e105923ced00,0x31c652fc476f579ff336dd3238c577af20cbfdc8fc2a16ac86aff0370ccf5ce579e8300,-0x13e6e0e5ec6f1b5436f4deaae93f2e5c067b0130366db6cbea349bb5119f540f26c68040,0x624bb26b2151a85daad9355381610dd953a1c4281472b50f55a706e36fc0c9c08dedd9c0,-0x185fb1d0668dc1ec7cf3a19342bbc8c618b4acf102f9d5ea386f9ab02950a99226e52b280,0x4fcd10c5d15131125664640de1429e3aac09ec5a477475e3c9035d3033dffff7454325580,-0xdbd1aa16dc2b4e54ae30dbdf29ae527550e8a8949951a580248b62cc83afbf9d29cc5a650,0x204d135c3c78d939fa62d82936988807bee6f3cc2e4547bd620ac7df7d771e0da0c6619130,-0x418891decb6845259152479019387c980d5f3c00d87b14944b58958318405a51c2505694a0,0x73b5a8955dd08d7b3dbf5b9928635fa35cdd42899c829855936aee59e63b401c4d080e4560,-0xb2fbb7ce63b1a16a9159190f9b1c22a7c089d0c636a8da1cf019a83d8d668066144b90b1f0,0xf3cd7cf107d5fa8863fa4dde31c13ffa0b3555a4096f106013a842b12d9d7fbe1281922590,-0x1259ec848648194052bfe098835a2956f7a40fadf771c82d38151be1a7cfac4c20e9eb1c8c0,0x13998e92494d317bdb4a39c16d1fe124ae2671eaebda3ad077f0bb2b00d135a98addf4e5f40,-0x129af13a83fc4eb3871b7bb24041e6ecf56362e65e71a49d3d7f574281176e8aa630d8f9bb4,0xfb85cca2db0d435c867c4be596e107937e9679fa847b2d96c357d87104ff45b97568b47f2c,-0xbd51ae9d034a32bcb42e7f3706d2b2ccc3fb83f9dd7a1730bec6d8709ff081fa8563eb6808,0x7ef82251c60f8324c3b4044db1ee1ca0b6052eb548cb9fb45884d96ac1f245d149b98d5478,-0x4bd85dd2f240a17ba4088b4ad26a5dc81000e3d12c1073dea3f1bb44c998341d9b1131f84c,0x2850c21442c6a55987c067249c84325e7fc1102ef4eae4b52a34c12d172e33f0fd14ed3114,-0x130a401d89fa0341eb1f10c3af6169aae0fbf2cf5869edf724c596690c0114462f9b278530,0x7f8f75e1285c212ff34a0dd39f091972977a623b22c4b8e2ac008989ac9b990ddb67ec8d0,-0x2f39d829503823eb51344830f1a5ab5eb063548858ad810714cdcbe2434ee403e321e5c74,0xf67f43c29681b3ffbe09b8c3ed2d6b74c60bbfefcb19dd2d700e4bd15d9d1066e6481aec,-0x468f1f9d4fca1e370b4d15d87cf97b0c17457237f35dcbfb84a8f208cfe2020007aa7398,0x11a237acbb3883a7b435b77afffd9be923ecd038c738bf5b348d576aac025b642f4706e8,-0x3d317b5aafb7a52a738478d96518be9bd75e98d479cc2b88718b4c81fd166248a07582c,0xb6feb673d6dcaa36546998ae1475cfde59991dcfaefbf35411e6e07f86d819b07dc7b4,-0x1d3a299a3cf125d9199c8fd4a42797586d01661082901c939dbb14b27fe386558277e0,0x3f31a7e7735b9be472b6de198694db0219751a0294b3f49871a6fbce22bb532ad5020,-0x72407d51edb710a003e0bcfa5e608fbaae6d1a8931fe69a668985a581891574e047c,0xaa4f636c6d1809a419d978995a4cb125c0071b7011aff7ac32fd38e94bbb2a85424,-0xcdcfa0f4df900a83265723daf5982668684daa608ee7297eee4fb1f33b165c4238,0xc58b325aff74a5f11f1141507696963424da3025e228dc1d9bea424cc06ce3f48,-0x92e0a133a47738c22217814837753534e61e9bca7e1c76a04dd3ea64355c4604,0x520339265a2bc59c1339546ee597e9710f9b4f049a98d7c8b1e783385fe701c,-0x21133e1a74ed83f08b31272bc0fee57632b82f942d3c8b6bfd6e83da8930b0,0x92a0c97f8da5edf9a8571bf7ea449b8dc10287987c602916799977a00950,-0x1a22927dba1658ab061b92a6142f64710cb73ac2352a36851684daf590c,0x2bd85804d2bd53f48f766dcdd43a041139488d0b62e3e46498cb28094,-0x2616590e84f90f4eaea5a8502ffd1c99095d9daf2ecd1d94b603788,0xe153b691f41d52eca9e0024da9bed80fd2ebb45a1ca4f34645f8,-0x1934aed6b441bf258e662918841c80a1a49f5df6c24b84bb54,0x6506edc454790efcfc51bd46fa2929333dda974e91bbcc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 24 88 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 88 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 56 indices rho q25 m25 25 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 56 indices rho q25 m25 25 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r26 : List ℤ := raw_ints% [0x5ff5f4421b2aa1a7d5e085f1030d4bfda822f9793c9f261508000000,0x7e984fc0116a5777e53af18ba20c18e2feba100116a34298dbc00000,0x4f5cfdc54c9484b411b3c10392b434ee40afdbaf15da5f4fd7cc0000,0x1f7676f981f9b14b8bd05cdf34e5d6df526e801548a9c1b121518000,0x8dac728663c01a8deca435ce18f10528ef4011b612c8ce08f3f0000,0x1e1ead6a61dd851a4b7902fd8acc6cbfda2e10c4281f22fe3bd5000,0x5068ccb8f4c0ad0a611a158f9c0612091eb10da981a0f05f448400,0xacc639645b88d3bac113b061ff5e8528760ad0f3287051322c380,0x1300073aed49244ec242b2336b87b33b5ea9b9f3677d9f98b0c00,0x1bb4bf2d7aad8edc33a82b73eedc8e53e9b759aa0a8d1dcedf20,0x21c12e2c8476d30b81ee8e9282545e81ffb2e5691d31a176bc0,0x22887469d37d8fa12fc917c060d1a828d7f6943a7e93152878,0x1dbde287596143f2ba2d4769c9548682fb8e5a9f7ded7bf20,0x1591284c7f1d8115385900840db415357dd6241931504d26,0xd236f3c2b2c19db6289da786066ce124ee7976b368f748,0x6b11df23bc0a53d94889fbbb3ce6ccd6aae5ef369aec3,0x2d3d9fce49d1e3a5e7055028eb83b64c7cff638c5180,0xfac8e58593f2a749c10168581411d79ecab76a3388,0x460b0e761127f4ec34f997e3d1b1981bad1b5a2d0,0xf61f03b0ad69fa4df93093a1906bc9ec8ab9572,0x28ec49efba9d4ddf9c0e88f1e5f1d1f2fdb6a0,0x4d7ba45a994f51456e533b3c00d88704190a,0x5d0a5073ecfc46603f9e943e957c5ac2e8,0x35432c21d31342dc7192df68b063a6fb]
def m26 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb62000000000000000000000000000000000000,-0xd1775799f0f6820d5bf774c4f032118321bb93cc049601af8f71db4f005ff49a422400,0xb22777e3ea0eeef835f5cd3582361350f57a51f869adebfb28ff50e389bce5cb560b300,-0x61aa5e7c573f808c39c965a67889fb18626f2127bf55e11f827f1d627a2db9c0c2b40500,0x26c8bcc6f23e3f42f54280368291fb45d9c64c353635fad95a9b6621c591a5ffd1e1a95c0,-0xbe330a8d5978729b06bef6c79b4fab823d2394569ce280cb6857cd587720fe1422fdad840,0x2ed0d8122b8746b7d5b84dfe949b8f9e081327c5c6e937dbac4643d949fe9659aaad625d00,-0x981afe8850b5d44881617ddae0967351009b2bcd87fe788340c768b747c8bfa52abb90ff00,0x19fa7cc0899ec228872d48c6145b544ccaa578f3b77f9f5313dfcf0a4165ad3db9e83824630,-0x3c927dc39236506c800c731331c47a455ab556176ed85092349906297633fdd092aae6fa650,0x79d48a55d9985a8664551bd20175e2dd85ee36aa8469b924fa90ffaa59fa3d2ab6e5bb77bc0,-0xd52c71f30870056bbb5ff37db810c284ad8d7cb90d7d22345c0e37ffbf66ccc2403daa8cb40,0x146a4d1252ed80029ccfa0f79ad139e1676722af10d0bdd611146d240f360325e2bc37e7a930,-0x1b891327510a4c767b972d8d88bc7a189f2c131a57917010dd7ef15aa87a0c59baada3096450,0x20d22cda930dbb746d5af8328ef2eef7a71edbc4024a04129431a901febffbeab0a8298ceb00,-0x22ad339a4aefac1e108c6afc4b9f800b4c6c4f8d31524edf78301e94242ae020f627e941a700,0x208b92c0ebe3fa65e00c503219783ddfeed2f2d1ec8aa8aff601fc659723c76962c4ff5e0c0c,-0x1b2c2684ccfd1daf9edf3eec3a378d79cce902078dd3233cd7884f41f4921f3b3de59b81f714,0x14329427455a4b6b0d127673a39ad5b20909185b03b481452c09091f3d1b81689a5af87b0f70,-0xd5e376f873a368740d5e2b5f1ce731643a8f9a2b933c896a8ed75cd5b9da6caba54141abf50,0x7dffd05534a0c1f0abe77c75681cb8ce2f86cb13a67865e168a3a1f670577ff9afcd5d1881c,-0x41ff3199a48aa56c7f0a0e1203ef4023f452661d63247999fd4a15e8c6c59a48dd1516d26c4,0x1eafffccf0ea0006fe8afbc5b2c04087a9c00db9b7616313cd8687c703484babc99218cb340,-0xca3b394d8c98911439536f0988cd4510d452fab0fc6f3b86e1da6a7dc769b2855fc5101940,0x4992664de310e5bbdd39956080e5ecb9335ee5ccaa9a12aa8d31c2e8aed0e76366047d8fdc,-0x178ed94c6682ef5c46efaece57b7f1190bdbce6c3d72ef863117ded38155764778a9dbe944,0x69c6799d4f79b58960c9efef4ff697e48b75351d0ae992f3f5384cc724c73e644ca332230,-0x19e16c3d0cd5470dca9939c865bc2428e61d5079ef72dac4a9131580569263cc54ae29610,0x57cc7780559b9b94e895deb32dc7450a656d551529458c800a07fecad2df0e482bad3cac,-0x1003f61c4a641537fa030e5b4926f8bcb0e567467fd6f42f43095b4bf0f97111e1db4134,0x27debd5f4c4e71c848251f0a4ecc2d830de08e7f26615238026835eaa3f3ec8c41c9f00,-0x53ceddc3014564ce25fa684fca4ae1374e35548e3b717197b3e03d7b696c3b451ede00,0x92f865b5d26202261c25b248b044aaa4d6bff9608374eca805af9cfc9188894e522a4,-0xd3f4dfe2291d406dd7843201a5cc3e37f2b1f632c6ea9b961f243da724d539b511bc,0xf717ceaed5f59e2ca12a168771b12f2eadf24569beb2ba3f3f8591b973d66ef62d0,-0xe40c2b0317f13466684ebd33609a95ca3e944a746393542a7c0b925f38dd737470,0xa270442c0303a11199a9706256076bde598a6ea8051fa6cde21074f0b90ce1414,-0x56884240dbbfed65fa6985f5b734a4c0749ef6f8430292e70b8c25736eac118c,0x2123243986b97d128cb39c681794d5ea95fac928cf3298f472bb0a3f8f189c0,-0x8ac015037034c866df1f417298fcac495c24e46b3a8cac4c7e2303c73f6c0,0x1737d4ec80d3bafc3be86b2918ba660b6a10569d00df37dcca088b592e44,-0x2452359da39bbdce61ee01937c2e8bcff85903d135ca6c8d9ac025d09c,0x1d32332081964cf657da0c928fcfb91d3b693e1055475924aea898d0,-0x9e7343d1a2214239de38cf84511eb8e811b048c4920594bd451f0,0x10191126f6594877d8c841c4a79328552c287f15a4b012c3534,-0x39e34c0c938a51c58687b6caf3f32ea5275961322253cec]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 24 90 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 90 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 56 indices rho q26 m26 26 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 56 indices rho q26 m26 26 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r27 : List ℤ := raw_ints% [-0x11233fce68918b12962c767632e295c14f28d6ca96646894ed0b000000,-0x1699c0a55f323f65a379a8abd2b7221144ba99163a2fed7cba1b680000,-0xe29be3034e29372c1dcaff0132284d3f5c37c78cdb5a94f140fc68000,-0x59ccd777cfb5d25106e44b8a8762c26b193a5b18b2e40775b3943f000,-0x1942f52ed5ae58e9935225a2ace2968a067caad9294b77f4c3ee53400,-0x55e3c4ac042fc2be851af0eae741204e3b9e0602afa07a0612c33500,-0xe52e5d9d6d67b5357c9312d0b2dfb3c0a21faa7eabfc730312d1340,-0x1ec2cda8e67664e922afb35c2c84142850a4aaecec5e68ace6be5c0,-0x36180dc731f91210eaebcd177bb78a0f852fc34f672a6d5153f3d0,-0x4ed4f2c1c05b647cd43fec10e45b918cd974a72aeaef503ae4db0,-0x5ffa965db502ee8b77a3f4d3d294e26e699ce2346aec65e27f7c,-0x621f8a5a06ff9e7408815f28d18bce68aa787ab3810c8ab1614,-0x5471ff1813f030647ee7ad7dd1234ad827d01b7439ea176353,-0x3d2f6c867a4ab1f63a1a78e6b0f76a30692b9a750f3be9288,-0x253dab40849a26a0f0a18edd7273e1865f42728d0809f754,-0x12f3442866ba1804e34a8b1957da8c1ce967b0ddcee3334,-0x7ffbf012cabf84822c1de76bb4674954f54f378f94842,-0x2c4ae32b77c07c76cb4b2d2bc16fce7f53986f8fde60,-0xc5b2397d36ca5c316d1488609bdff1090bc64dfff0,-0x2b5c715c1ebee9964b8e4583804854b43ef4e823c,-0x733196c8ecd18fd725d41920e7087a07e8c4fd3,-0xd9c5ae2ce471f37ef45face2ad3727a6923a8,-0x1050f55fbffefc5bf597e240c6ba17ceb2c8,-0x952c85d14acbe1f6aa7b11e9d832a277c]
def m27 : List ℤ := raw_ints% [0x0,-0xee58ded4b89b0e5e82275b02d1219d6c40000000000000000000000000000000000000,0x1a06e6ca0f6917fbd5537f1e8d16be04cc0b36e5b48e2a34425ec98e910b9e9eae025c00,-0x15ffd3c821c69ebacc54eff8697a5cb39c8a4a514278e6f1d46de15e7e78ab5d9f6b5ad00,0xbfb96f9fba880da1cff5872c8d65841d6c4d0eb837f2a62cd494a5f18862a83b3f08b2300,-0x4ba0ead77ecf12709514083e9dc8b2dfd897ff31c0b075ba031c8580dce49e02c9e326b840,0x1705189ad68f2c159ff3fda296744d57eb077017cbf05829737ec3289473d128890a9ac21c0,-0x5a016bf1020ec2b2f07bb4534dd07554619c1b15c0d5765d2e5cbeed6f02b8c17e252518c80,0x1223d534fbb3c5b0b3edcdcbecf23e751e08b4a84e66a0a0632444abb2026c7064441f55ab80,-0x312f217b5decfade2bbacccccfe45f3dbcf038456b33bb523e01e7420e83ff8125ba93df1650,0x71bf3d346b34b3d7333d6f5575afcfbe0a0d94c80a27a453898290a87f387fd94d704f968130,-0xe2d7809d778bbb3ed8c7442f6e78ba8b8293ff4c947cdb41fb84e23ab0cd46221ed79f1b0320,0x1896778bfab97d6ac32348a0ef2a8646943e980f2f0920dc9d73a6993e767107d5b5f8d6432e0,-0x2553b16ad06434f5896bc2e68a070e683c3b7272e3e9106963230ed528afd53719c8f8b7d00f0,0x31dba39acf2e146883f2624242bf3c79b695c75e3d22e2fb700dd57db6b64bfb628ed450b1690,-0x3ad3661a6c249696dbb7ef6cdd0184a9895bd5874a8f85dc53d8ad2359bca8bfcbd85fd427bc0,0x3d7d9fac3478d258a99b0e1358a25a17433c7a33e263ce4ffd7bcee59a512ad451e7a9dc1fc40,-0x39112cee3058d46a3c51a8be6fd62d4468a7cb0e64af48433e6437cb71f73e7ecb08984a9d4b4,0x2f1650f03acc6bdb1c9db962db466495b400ad02f50f5a9a1e18e7fb5165e6eb368c16727d62c,-0x2291793d0ff8aa062d3e068d7cdb53a925d8e76ae1d4dad6823ff0a860e02869a4aa229a8ec28,0x1694ef6c71bb777a39e036c9b750fd27706d5614d9b6a58931837c4acfa8624e15fd93ac6bb58,-0xd1eb8e933a8b2b9b840bb7b976682df53128dce7a31bf0ea86ac249ab5c6049ed8130e624f0c,0x6c5b9ea9225d55647d10077c72048ca680b72f4ff974a0c544ef12744326718ba31394ea6a54,-0x319c567649f40cfebfc149bc5ea4157928cedd896bb6d855a625cfc5dcd1bf7a54ce010829f0,0x1419c39fbc9928ddd2b2d1f9ceb816c9b9300ba3d0a60f2ea35d0d29f2a07d1cfa8681923010,-0x72fa490e1b6120e5fa0fe1204ce5ba00bd9ced74982edde2ba4647d5a9a75c2b08659645af4,0x242373db5021527e455e7e188e827b879be1d1d0926bbcd0c927cf1cf7131eb69f03c6f5e6c,-0x9f139952e51c73da94bcbacf5013151d5680e134fbb3336693e056f444b20e2c40a4d43ef8,0x261b18275bac472c87cd20e986743e61cf90dc21b7b1bbc08a5a8b7821564ce2aade17b288,-0x7e5ec513cf37efb1a9f95fca05d2eda911a94f1fb9741679cf0971060bc1029cb379b4a6c,0x167efdf85a751e244d6eb9172540ea690b6679da062171c7371d6d67e9c8e25897de70b74,-0x368d6b5353bec5f8b2170836966c7f1a132e21eb171db9778310340188e2947a77a59360,0x6f77cd57c87df7b3e612f7738f5cc9538b93318913020a8f58985f39ceb67cc0ff754a0,-0xbd934badeb4d16f39e40e6a3e0cb9ee1768e6e30b228d35d3dc6495af51d077bc9a87c,0x1087526d2cf62bccf20232d8918b0ad2d4cb685179e5b3a7fdbc51978331c5e1d67424,-0x129577fe649f6d3273316663a8135e2a0d372b7331c773c45f9f2c6f7e53289e67118,0x107cd1e55829bfa30d892278afc6d10f88a929263324eb4338cf670b18c191526968,-0xb3f69d76095b12dd9c9c669140d35fc69b527d3c9009eb5683688402aa57b87d44,0x5b6e88fd639a05e0b786e70e2e455636f2fb6a2abbd3d146d51c048779d89d4dc,-0x213c61678e423000167ae1a628197375c5a4d2fcb4348b9c485903c5fe16ff70,0x836536a16f76578c7033618d17cf32407df0a5a1a71631f235025eeb0e0e90,-0x14a2c2b7ce0ab30c5b07416df19499aadb891c2862c090bbebaac61d00d8c,0x1e17df64d1e417e120095e95cf66594781d6223b3dd70d0ecc7209c7614,-0x166122dbd7e7a476bf7ec74d85fa0eebcd24cc0d649cf446da53d6ea8,0x6f672b6d344792d6b506a0377e6ec6083ff93d218b1e08356617d8,-0xa4765ba54045887cbba402ab69ad070a9d032a560664254b414,0x2129ec6c55519c557397025cacf84d96404dbac01e15010c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 24 92 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 92 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 56 indices rho q27 m27 27 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 56 indices rho q27 m27 27 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r28 : List ℤ := raw_ints% [0x2fff87427e1bcecc1233fe306da7abb76a80307d4a55bc9fe3abc000000,0x3f46eccd901edaddc468e69b2448abaacb61e73030d7273f91422200000,0x27a3b314667a71116635f41c21e33890baf95ec218f877741ea53aa0000,0xfb3c5984ff10db462217e4a2f597447c940cb7e9bb50537bca1e9e4000,0x46a557c9cb5204b383ba18504fa8d8af582efee0bad3ba5818fc56a000,0xf017a18db960e3a4d819e03c1f7c42a5677bc74fe481ad9eb09591000,0x2805807ecff021b5e7f82acedca919a0c4bdd51503c2ad3315594d400,0x55e7a3265797d0f8876ad5b767a7259b9ec3b96e6b2bc300c9bc07c0,0x96fc44d456a53b4d3f6b0bd781b840d1d924954b6e66e65987c0e80,0xdbe852655d58dbacda7d52e76e8fbed531992c753522c7026d0bf0,0x10b93b3beaf0b39232646c6c26fa53b12b8ff51f639e85b52e2400,0x111604a3eb7002d57fbb8149a23bf8f4a2026d4a4bbd1e2808d94,0xeb1a8ced30053d40a1e58e4787989683b90e929d7ad567e83a8,0xaa379ba8f0e87e3e4c5ca3947f605238a064f6e56ce3cf8ecd,0x67852cdf09b5d7dc869a5d9aff73c65c147291bfc0357c540,0x34a18abaca8dd305c9da43304567f0aa02cab754698033dc,0x1631eb6e97b22c4f745d01760475bb73d5a06e63d94bd50,0x7ac65f344e6b539f42c9285b55d92b79c4be67606c13e,0x223657af55312301988856b44dba68d9af1867c16a00,0x77eb59af54cd96f0d7710aa8368beeb5a1f635a880,0x13e2b834d37c2e1fa353b8c44faf5316fe3853348,0x258a7e51369f396e194d4b44aff76019d2ad2cd,0x2cef4844ddfcf623877f2b7b5a4c9443bd600,0x19a23b323bd01086b6266260ffdfd352f88]
def m28 : List ℤ := raw_ints% [0x0,0x1dcb1bda971361cbd044eb605a2433ad8800000000000000000000000000000000000000,-0x33c0458454521af05bb2d640995d6bf52140ba5d0dd371c54097a68439068353712492400,0x2b7a862f6f1f80f1765b29a1f53431b225494679466e53459333f2fa988609a824dffff300,-0x1788ab25b43a493a0968266676d7a9776a39f548aadd51bd0b54a30b1dac3bcf678a26ea500,0x9390bffee1f77c722abe85fa43389a71bbc346bf42f1c397cba9de4867901f8bd9885b74dc0,-0x2c9cac9bee0afeea14019d9bd992dedc38e87ad155d742561e611f0243f207dd2c20fc3ce040,0xad331a2ee916f98d5c52a44666564f80758923f2d12775b2357d0156986525d4c19555e45f00,-0x22a6a8fe9f98ff99e2a4ceba4d503530bcd45c554df1bdc4b9ca7ec0b0e5322054c64f8a32d00,0x5d3bab6f86f28fdd2640697aaafd265fd847b02348b1aad8793a172203815ff7bbe9d8cbc4a30,-0xd5e5df040d8385aec60b7899f62d86978c4c9aba081d443867c1ffd11299af21f0e9d20952250,0x1a7040a2b67f7b28284aa59e6379875216e961be2370915270d92e2589e3de789a9bba9d3e4440,-0x2d73c121a12cd7563924e7c3b80ed805f9456bd587762e938c8a5a66480adeb77a9f7012264ec0,0x445f727285e486e7314ed56c57da4aef55fb11d6027a876f35d954c20367ad657b3e5a39475b30,-0x5a747ef75ae905aea6389123f2d938c4bbce12e9f41cfca82faaa6087b6f76213ad0fa28c3da50,0x69a850f73527b9cffd30b6902f029ff89256bdc9c3c7f1b09c273fb4ef7abe395659bacb504100,-0x6d48d5f9549c2c52a711e283b98c1aaae4a5c3885bde3f153476da8f0a6f5ddcab0c695e999900,0x644dbcd305405cd666d56ae1d4808374d96e7d08986b2885cebab3cd200c4530598e834590140c,-0x51cd4176ae066eaeb9a012f1f8750901c3c05dce1859832b73cf985bc673d912d109db1bc86714,0x3b51a6bd69e280fa74b7cccfa1f2921c81f01aaed713e67d82cc78645725a7bf7f1030c858be10,-0x26400fae5b8aa2e60b30d0cbc060f622e41c03a8df8bf127eb6afad83ca82cbc65d9cd4d22c7b0,0x15eba20735be63f0ea6b94073c0ffadf3a89771a92b9c28d75a7a0ad8ba8616cdb5b0e860ca89c,-0xb26de23f3964069e8b3c1f0894e2428bd31331bdb10f6cb3305b68e2b97a47829aa9004978844,0x50718aabc15e69da565737549813b69fbbb4352abfa2be2f64ca176df058c8e725c9ddd7125c0,-0x201072893916ce7c282c632a425977c30185f42dde7afc10a39501773aa5b9a59ea121e5438c0,0xb43f01a4e6c3f1c07b4499ade19d0f5517dec49d0196e99bc48faa80e4f51b9e6d12ac97529c,-0x379c91c43bcba699053433739f91a20d5a0e7af4bbd27ed61823e389e3f493195b99ed7b2e84,0xeffdf0b127333f9712de51c5a0b005dbd436094b53135fe1d4ab5da63427b06761f014aad50,-0x38484d8bd7ca57dcd8a095ad4a0aaf5574d4369787ebaf620cc8155ee24e1cb0948a9df47f0,0xb673bdacc81f5e1f9d00d53ffea37696a2e9fd9783bb06c7f271ccfb830c7a073187bf8d6c,-0x1fb1f76258e013e0bf4b99f9acfa6173d5c15e23e5391ca45aa8d100cd4dfc1a8b3f5af274,0x4adca0072038f19782f3b01438550721b01720167c1f5e41cf324f2af32bed8c8de4ecb00,-0x94acea910b40dfd000870264dfbb8a9b390f3dccad4497d2faaaba94c682837035b9c600,0xf52ec56e78d026fa933721cd7c56f3273736e37f9e48c5deb1b130c5a25ee8366933e24,-0x14ac71af627a3eeabdb773cd7034b5beb8735314cf4c054e79af606f102f479da0c4e3c,0x1669c298d549645e5336c65158b2f2681811e6e4974d618a0c7e66bc056dbb7672c3b0,-0x131c3400ba6637b5eed6edbd39e9713af7fed5fffb934a290cab75206d19efff62490,0xc7b6a83188ae4616378bdf3a93603bbee7b796d22595d8d8900e43f468a0bd11214,-0x60bd7c7b1288209493cac797bbbe2aab4efc3bbbb6f6c4db2e2156a5a1b5ba998c,0x215e7de6b0535df4d26d5d195e0c540a2ad6f69c17fe514db41a187c15d18d340,-0x7c849252ab46c13d51d8ca0b1fedd68e91b62d7196fe2f1d8520cdca5cd6f40,0x125915ee948dc1f203eedae987d40f1e154c983ec80653170354a7e8d4b004,-0x18efc9cf5df58f4f34a410c3bc10f1870f5478a1ef2e125705107d6c76dc,0x11273ec76ac7d10ba41e08b8ba70c33362b7b7f71659d9b95fe2c4b5b0,-0x4e4fad36e7a05b53ceaa2aa33b16d7e07eb2dd50db14f0011342410,0x68fdb05120b4bf3cacb008705aee1400bcff286bc290bef1eff4,-0x12ff0978213637ec9b044db9b039210bf6db8b6f87fde102c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 24 94 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 94 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 56 indices rho q28 m28 28 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 56 indices rho q28 m28 28 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [0x19a23b323bd01086b6266260ffdfd352f88,-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r29 : List ℤ := raw_ints% [-0x83f7630be2c3d730495480c300431ab4e86215bfddf55858854108000000,-0xadeb52d0f495135aa1997df6bc458bf603a72a728129c2fc755255c00000,-0x6ce9e8e7ed15d7255ab3f833501efd73b4f656e6be2fb28ef0238e7c0000,-0x2b20c9a175ce3f582301556ace9a703e8cf78d89f991b540146ca4548000,-0xc1f68135006a60f1231da6e6e49c8f7f5437129cc8ff7ee21e86f62a000,-0x292eb547715334750ae77c835b72580682e43d6ec52777c7cf092d65800,-0x6dc9e1f01659ce215b14bda79aaf8ac5c2f523dd26510239b39c6e3e00,-0xeb8c3145bfaa6dfbafcafa61d9dede7b1817ef142f955ccea205f1600,-0x19dca1bd6e1bc0d6bef70e30fc22325e117d8fc23fd12307b8d34a7c0,-0x25a5afff134d769c6324fda2781948e002ff9b43c1c0c04a9cacda00,-0x2dc82aa65ea11d14cf5c5309978681e58e3f1e05bc0a8f9114a72b0,-0x2ebede979951dcc9d14991372ed7a115dbda9b9ee9b31063e1e7e0,-0x282ccab0c9c05509b80ce1a3775b94d391161afea3761689d9574,-0x1d1110b8ec72ba347f62ae1db3d16b02699a468ac8a2d090e418,-0x11a9fef4571ba2d2176f762438f04ce7de82c6dfa2753864ca3,-0x8f92f4b870e6be656047fea6420989c10ddac00e68ac7d660,-0x3c7e72a100ab032aa17d62245bdf366186f94102a6b96c9c,-0x14e516a544e62becfedd6df17a04c9b4de73c59b94cbfb0,-0x5d110b5708ad2460689a10289d4913b348171e9015202,-0x145db70373096c3189bc12b46aaecfdba28d2f332f20,-0x35f8b4b215a32704f333aa6f150f3447c3a0d04df8,-0x65c26eed392921b8f81cabaea9d139ff9d260378,-0x79a1b5a9282838c837e71c00ee5f678ad7f8e3,-0x454817facf6e99f5e929997117595dfb8360]
def m29 : List ℤ := raw_ints% [0x0,-0x3b9637b52e26c397a089d6c0b448675b10000000000000000000000000000000000000000,0x66ea536a104c0d228e6c9f07f927b8c29c4369144ac9ac6e2d25d2a02e7c9e71ab36db5c00,-0x55f489f1e8b25e8cc61e8ae25a2ce782f3e5dcb32909667ebb7ee1a21e0ca646ef71ffe6d00,0x2e3da32ba7dab633e1771a0e58851f8e7027b7acf332b56ec70265c3a816037779f05952c300,-0x12019e9e974f7e4e9d13511e82a0297e1c1ce2e003a44696f35c9cc0a66a9882fd176a5fd3040,0x5685b16fc98eef7afa0fd4656ebf1c2f9c734434096549bd73dcdfc82adc1e4e313e5990229c0,-0x14d9810ad20f9b6bc4f011c3a35afdb3f45c691bca59dcba8e040ed8975e36cab447afdba2b680,0x4242b16b51b56e6cd239cce53280387372524cbda16c30f5d8397adc127e43807fa83daed83180,-0xb0f224011f63548ec665527cd3fe45e58ed2650c3b894dd81e70730499df801e423ac2fa2c4650,0x192c69b1ab8bddd22cdbde28af050e8029d02219c92e3a487f88b8dc8a7627755bfa911a5a0b130,-0x316084afa983ddaecf43ee0188a9bbac55c98fb24a775f84895cf9de13e6e9285681d586e39e5a0,0x54291dc2ac6d7b36d5599438a8071563015a6870a1103793f6042339e1c95d5f0b3379504b28c60,-0x7d7756101f291963a36edd6dd1012cba943a53181dcc33998227fa6f44879b1b04e5acffe9c0ff0,0xa46d702e1fe12538e43383550175d2e50087835baf93606bb97a02b2584fa4e24b1d50fed140790,-0xbe2adffb6d9c9b3e5b19db7cfd6f7ae695aa8e26edd2784d38c0ce216f4c1f98657089461ab76c0,0xc2a81f46afbb516fd42b0c20207ed3c530e104de5554e247d1e987a3a5e25b52ed41f94d111d140,-0xb0b63d9546cf2dfeac226af0bcbbe4c0c3420349875252093f8e1f6e10448a420167bbe96bdddb4,0x8e75e260a78f730e1690aee42a375cd7aa10b65788aaddbc53385417997be015656672dd8cf1d2c,-0x660deb0bff87461b5d76f709a45bf37f349f3c045337aff1a32ee48ed9d97e86e123f2046e81148,0x40f70a6edca55e37398f88ae2f70d8b97f57e967f56e8ae9029b47cd13c71929e7e3bb43129d938,-0x24b9ece14a01607dfa6d72fce2a6429c36a117d1b977e7120e354373d69ea345ce6280304a6b5cc,0x126a927cf9f0bce91049181f038fb4a110c4c4644f39d32bdbbd89b1bcf2935f37f8cb7441c8394,-0x82d3340af0941989f9bc3ada04cb5a76208b44115b5c84ca1e59deb3452f12175b20003f65b0b0,0x334d946ddc80697e2b8f5badb6cb51deb4178ed54de17bed53d9a05257e7727af4a44e6d539550,-0x11b6eacb3e292c58d849d4bb0103a648b2e199044306ed26f37249c686cd75f4bfeeffee606d74,0x55d7c58ae762d7ab98894f04bef0b2807bf375fb447eb8bcfccf3774e7584bf1946a593043dec,-0x16b30ad9693934ada6454a7a416afbda96549681842664578e4561c4d5e814ab056105e182958,0x5362e60f86ab9dcf9cc7dbf8e85dc6af0bfb856c2e31c4e88b634a788bb23d4ff845bdaf7728,-0x1083a048e837a00901f9fe68b31a5b8e17381b6f8c9eb48fb096153b2b74f308156c672b80ac,0x2cca0fbbb834e98863bcc7b5ef6505dcf4c3617a33ecf6773e13652c88e2c546cd06487cb34,-0x67076429a3f6cda482afc847b7a9d23a5eba06d4ad0be3c344ca772d494f8993bca077d2e0,0xc6d97bcc4635f6ae7076171ebc90a7c65dfeb7db6d6c348c906b6900e7a4e860d30f23520,-0x13dec835233c958a23736c07cd3aa8b3b2458798d49d34806c36b6464e726333904f0447c,0x19eb896434b0af3bd31f3e617ff2c383a0db8786b9fba509a55bce44e162d1a46da8bc24,-0x1b17048f33abedd842779fc57c54eeb38b810bd8ed0cd53ac332b500daca208a2c05ef8,0x16312567475f9c21a08476946bfd673d3f9a63a6dedaa85e50f9f47d8c47a0e74c9c88,-0xddfcabadfbc873da1feb64d48d22d459d49c11228c12defe4773e90138b5ad292c84,0x667d30234c33cc39b19ed287cc736ce4cf24cd00871b38663a62012a57690da319c,-0x21890d0a0e38773507a22f5528a1663c8159586c0b3b3251c4470bc689b4a2d030,0x7613c8b78f0c8178ff8efb0cb644b79d14ef68af15b96ab347c2bfd8151131d0,-0x1051d814638295ec31f0edcb1fd25ccd5272c25942ebf66f551a5d40c90260c,0x14aa7f9c3799ff36928d3687abfa9c20d51d8b5b7deed0b86dc7f8a8c7794,-0xd258b0d3dceffa4d912ec87197ed00711f94cd4b6f7b2e597bbdd812c8,0x370a15880943dead3cc7e1b72f0dac4fccf1b694d32c770cc5f444b8,-0x4302df61dac9d08c1081b4a3620fcb56e4bca7365b0a6a400e0d4,0xae118c8e0115527e0a07363e03bae1bd6598b64552a86324c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 24 96 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 96 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 56 indices rho q29 m29 29 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 56 indices rho q29 m29 29 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [-0x454817facf6e99f5e929997117595dfb8360,0x19a23b323bd01086b6266260ffdfd352f88,-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r30 : List ℤ := raw_ints% [0x164ac2b1af501afcec17c8cee01ea80688b11563098b23d5cd570560000000,0x1d5ebbe4cde18f15aa7744f7f18497576d23fec588e95c1194343d45000000,0x1262f9432d283a1d2400cb6ed933d6f4bbd73c9a94c2e21cf15e6679100000,0x7474143ee525498e13a1d48fd9cff467d43f9489ab586ea86bfd328c20000,0x20b8b8d9a6a4804847a75000644cb3e8b3b17cda841854f7c98680b720000,0x6f1df2fa84ba7940cbf95df43dda24f74f5e5aafa5639900cae056800000,0x1281b21786197d6d69012027ebc5e6a993f094b453689fc28054b3a51000,0x27b01be0d233e4df776edff293a355fb23f6bb321aa332cf20eac2bfa00,0x45b00c24860a444b7d21b148b64ca7b2bba66cecd4135e05538a419400,0x6564e267f12599658faa6e07014f6ee8a3be3744256a65b078b98ce40,0x7b3cba16fc903a98f8090d2fa9dfc4fe107618d9233a90f355c7c980,0x7dc2720c9db0d824337480af1ddf3e7108bd3a63880c51e746837d0,0x6c0447decbbbb9335a2f52eb686d5df31962ddd036844cf091f580,0x4e19697f9354973b71e09bc5d03277da739cf05c7e7e341597f8c,0x2f6da87ddd10beca3d53224ca107fcb2920838bc5130b8eda328,0x18135cc3149f9b7cad7e00558f6319025c396dd0f0aac6252dd,0xa22cc230c8c995450ab97702c901e88b4454577ba1e386640,0x37f7a5fe6da5ec6fc77a0d0d76a095b7d9de65db08b70f64,0xf90c5b297c00b33fb15fb6c3506ede0348d330163e4f50,0x3671fbb82b5235f5d4ccdf70903ac8bde2174abff5f7e,0x90207d678f7458b0d16aa5a5e93e3e1f84188fdd580,0x10f6bf8c0254f1f3953ef14dbdf3afb4a4a4435b08,0x1440357db320af5dff4f5cd065c361e910088ec8,0xb84d86cde80571c6434d6e46a80591488839d]
def m30 : List ℤ := raw_ints% [0x0,0x772c6f6a5c4d872f4113ad816890ceb6200000000000000000000000000000000000000000,-0xccb19b10d96d4b54ad76b3f512c26528666e9b9750e6be15777948165a1172fc3bba4902400,0xa9fac5e62cf335391dbc5c1b400c73ba9f41eb667a970c406a110387b4794ad99aecdfcf3300,-0x5ae59c86a44e71c1aaca969b7d9b374eebab2020f2481141d7ebddc8c77f629bd6f9284d84500,0x232cf966d976594f302f9bb93c9aa2ac702b99bff5059d01e38284643d2697460a85d154a145c0,-0xa7edcd0ff71b3ad204d093e555cd673965caeb69925a4eef162e07ac0d2ae2f286c908bea5a840,0x28318b9d799a1eb35bba18686dcfb747dbe8a25cdf16ad364b349b41096b0afd286afc6a053f100,-0x7ed6375c8e829b7e4ac71ca3059a27a05f92857fbd993f3ef5913810a502314a29348db74c54b00,0x15038feb79f6e89a800fd54ca2851383e66b6d1a3773d89acb2a836d13a498a4316dc5fd5f93ae30,-0x2f773dcdb66063a3bb47f34004b11fe74c5c936f61afd7b434be54151c5312a280c5d896131b3e50,0x5c5ab9bd89b178e3f5fcddd977274f29ac85c7e89806f326a388f358a87a22b48b94c15ff6a0d0c0,-0x9c16a1018442a2c09c88ccd4924d401080a7890acd1ad96dc21f841db08f56014f91c7ca075a6e40,0xe6a47619f3f7a078a3f6d04e845bab2ec4d70530decb3a535b4786ad355d3ebffcd619f82d02b530,-0x12b772391d7b9624dcb012050a2a510817ea757c209df2fa87c93ebd81ea1424eee54ed6343d82850,0x156f99785cd9c7ffe97c5f2eb7846b5f08328fcd609bd1177227ada99575abddcd336630e8e894700,-0x15b7a8b4017d801aef527fdc2a25954767a9e2ebf7f30577bdd872863d6643641d5fdea4ecc769b00,0x1380bb76221b38b993aa07bffe0ea4abb01fb8c42bbc918ede0a759d8df1d03f0f570c6f196ae840c,-0xf8b43a1d2e35bdb95a071e7d948be92c1525149f56b01a916545be2e45a82099d5f37dc1be1c6f14,0xb006a0aa1fd78b0d493a0e547a9bb3e975ec7f90f590a6273b500f354d88fb3d028fe1a0a9aa61b0,-0x6ea19fbb38f776f990361ddaf004108ebb8745cc2ad5542f3207b8a719079797369f60f54b889310,0x3db3c06aeac4069dedcd1481724ef20b19adcf6130eada3984dca6153fb73b455763deb3f9128b1c,-0x1e7fdde1e71c972d0a13820dc5ed14a392d041d2aa932d8158caa2e81468844d4498aa378cc107c4,0xd561a92d0cf6ecf77d3082ab7eae1259d02873c1ff0ccd316adc022c41102a09065f9c67b93ec40,-0x525476a14bfbae38ae0806cc214dbb644f7e5efe85b998da7ba632758596cdef88a8a130d043440,0x1bf09c6c34c5e1c9642760aa853e184e21c0ce97b9e270872ac179122e6f5ded15b789e88a1a75c,-0x84e99f0823e49558c8f24d516a4d8420a903fd0b21d39df08ed748d6d7a12d8126dc2ee8e0e1c4,0x2274fbce15a2af1e21c49c3927375976144924c74c4039fda3f692f266ab4cf3e4e45d96896170,-0x7beb0b52b7d7d16597dd00bb0b16b8ccd0b8c47a6d73f71919318dbb017353f98e3a035ff18d0,0x17fcc8f537492699f5cecf5098a885d9b5928e36b235f2ef7a424e8bd6e5cc29925ddf9e25e2c,-0x3f7a69d8c320b8194edfd69851a5eff99a14aee198fe83fbc6a981886d5782f847cfe10e03b4,0x8e31cf328a72ea9b8dabf1e6e79e8d0d49e7ab5ee1b3be592f6718c0f5a3b23af2e73c21700,-0x10aac19a48321b98a5fbf3418cbfff1e8bee511ceff9432e3ddcb93678a18d429e1e762ee00,0x19d49983d73bc2d34a78aed46d58154bd04b3480c6ecf790855b900e9a8c31d474683e65a4,-0x2092d1f2dbf37f4aad951fcfa0170a2ec36cabd88c312278e4a5bef916f41759c3e037ebc,0x20cfa079da20f97c1dde85338dbca27c3df0949ae7e595c939875cc93f72f6ad7ddf0b90,-0x19d15d1d54427043b42a6a83ad20ef091e9b899f377700914bbebbfce4e609b4f2b35b0,0xf71f8b5f863aafafd55d7dc3ec1598b70adf576b625d00873f7d313ef5e74b4563214,-0x6cb667f6a10c0455d8bdf388c567cd5634dd56cc0710ea48cc22ee2c0ff116829f8c,0x21bbabf91c7cee0dd61f4507a00e0bbe14d43f30d527c1854eff0f389838978e8c0,-0x700990e7a593963ac8b4b90bd7b5a0b737a42ccf97dc6a219ba4ee47b68954bc0,0xe85340956c4a01a5f28fd154ec1c9f20e8a9ef1709139217aa653267b446bc4,-0x1120d62be411885b012909aa05fd19ba540008f5ebbe43e1185fbbbb5ae31c,0xa13361cab83efc332f78171d3fcde5232a74f0c493310bd553cd8d58990,-0x26ad21ec2795d9e373ed27875f82b713017e113199279ca072fdd9730,0x2ac2fbf85e6ca5bfac47f65db87ea0899d6b3016a0e7062fa5beb4,-0x63ac9f9fa861f00a94c3d4ce6a76cbfac368b6b42fc62def6c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 24 98 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 98 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 56 indices rho q30 m30 30 331595889998247930393357545164294656000000 32=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 56 indices rho q30 m30 30 331595889998247930393357545164294656000000 32 23
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_30
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<31) : intPolyRF (mz e)=rfPoly (C (331595889998247930393357545164294656000000:ℚ))*rfX^32*(1-rfX)^23*momentRF (key size) (X^e) := by
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
#print axioms moment_source_30
end
end CatalanCore.Li2.NVMod.FamilySource.U8C32
