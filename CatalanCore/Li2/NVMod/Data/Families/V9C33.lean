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
namespace CatalanCore.Li2.NVMod.FamilySource.V9C33
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,9,33,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6,7,8]
def indices : List ℕ := [9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
def num : List ℤ := raw_ints% [0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def den : List ℤ := raw_ints% [0x525ed8503b2b88d03531000000,0x6e6dd3a7f05e51d06f2db80000,0x4673361b7678e664bdddcb8000,0x1c774a0ca154bb74c45eecd000,0x82de4cb2071ac0dd98475dc00,0x1c760e2df3f029f5c8a748f00,0x4de4d65105c039a128aac5c0,0xac0111054ad42e765101140,0x137e5eeb3fed0dff2f6c4f0,0x1d638014b4779a3ed09e10,0x2527a6f2de14210e48914,0x279db4c9ad3f68a3ed3c,0x23bdb4b04eef5f3d571,0x1b507e62431b126478,0x11aa76a4da1caec4e,0x9a3b14f8fcda6b4,0x469c2fd32979ff,0x1ae54fdcf09a0,0x86b9364a0e8,0x22110cd164,0x6c89f0bf,0x1061c58,0x1c2d6,0x1ec,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0xb,-0xb,0x2cb,-0x1b5f,0x1b5f,-0x478,0xa16f,-0x3272b,0xe3a587,-0x43425c4,0x337ecea1,-0x35a0d73,0xb4ed535f,-0x242f77130,0x388a2a0db,-0x28b1643f,0x7a142cbd,-0x52d9ecb9,0x22d6c5f95,-0x11c66501d,0x610e303fb7,-0x5defba8e0]
def rhoDenominators : List ℤ := raw_ints% [0x2db5afcca0,0x51672d8,0x2b0e60,0x626a,0x7920,0x27d8,0x220,0x7,0x1c,0x15,0x12c,0x16b,0x5ac,0x27,0x444,0x8e3,0xb60,0x88,0x220,0x286,0x2860,0x46a8,0x8595a0,0x60038b]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-9) 0:ℚ)/(rhoDenominators.getD (m-9) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 9
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 9 33
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x17,0xfd,-0x6eb,0x2297,-0x8371,0x18a53,-0x3bda5,0x77b4a,-0xc7826,0x117502,-0x14a18e,0x14a18e,-0x117502,0xc7826,-0x77b4a,0x3bda5,-0x18a53,0x8371,-0x2297,0x6eb,-0xfd,0x17,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 25 li0=padCoefficients 25 (liCoefficients 24 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 24 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x16,0xe7,-0x604,0x1c93,-0x66de,0x12375,-0x29a30,0x4e11a,-0x7970c,0x9ddf6,-0xac398,0x9ddf6,-0x7970c,0x4e11a,-0x29a30,0x12375,-0x66de,0x1c93,-0x604,0xe7,-0x16,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 25 li1=padCoefficients 25 (liCoefficients 24 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 24 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x14,0xbd,-0x460,0x122f,-0x381c,0x847b,-0xf240,0x154aa,-0x16148,0xe5a2,0x0,-0xe5a2,0x16148,-0x154aa,0xf240,-0x847b,0x381c,-0x122f,0x460,-0xbd,0x14,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 25 li2=padCoefficients 25 (liCoefficients 24 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 24 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x6f,-0x190,0x1db,0xab0,-0x47eb,0xf240,-0x237c6,0x3f160,-0x5829a,0x626a0,-0x5829a,0x3f160,-0x237c6,0xf240,-0x47eb,0xab0,0x1db,-0x190,0x6f,-0x10,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 25 li3=padCoefficients 25 (liCoefficients 24 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 24 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x8,-0x1b,0x2c0,-0x1339,0x5028,-0xe6e5,0x1e480,-0x2ed76,0x33bb0,-0x22dae,0x0,0x22dae,-0x33bb0,0x2ed76,-0x1e480,0xe6e5,-0x5028,0x1339,-0x2c0,0x1b,0x8,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 25 li4=padCoefficients 25 (liCoefficients 24 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 24 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x8,-0xf9,0x7d0,-0x214d,0x5268,-0x5b0b,-0x8c40,0x3629a,-0x83270,0xd1ab6,-0xf3720,0xd1ab6,-0x83270,0x3629a,-0x8c40,-0x5b0b,0x5268,-0x214d,0x7d0,-0xf9,0x8,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 25 li5=padCoefficients 25 (liCoefficients 24 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 24 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x28,-0x213,0x8c0,-0x181,-0x8bc8,0x2c23b,-0x7ab80,0xe07ea,-0x112970,0xc3a42,0x0,-0xc3a42,0x112970,-0xe07ea,0x7ab80,-0x2c23b,0x8bc8,0x181,-0x8c0,0x213,-0x28,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 25 li6=padCoefficients 25 (liCoefficients 24 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 24 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x68,-0x261,-0xaf0,0x9c8b,-0x2c6b8,0x6b4d5,-0x7c140,-0x43206,0x22a650,-0x471cfa,0x57d860,-0x471cfa,0x22a650,-0x43206,-0x7c140,0x6b4d5,-0x2c6b8,0x9c8b,-0xaf0,-0x261,0x68,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 25 li7=padCoefficients 25 (liCoefficients 24 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 24 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xe8,0x2b5,-0x5b00,0x1d8f7,-0x33108,-0x63825,0x2dc000,-0x741636,0xa77a90,-0x81abce,0x0,0x81abce,-0xa77a90,0x741636,-0x2dc000,0x63825,0x33108,-0x1d8f7,0x5b00,-0x2b5,-0xe8,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 25 li8=padCoefficients 25 (liCoefficients 24 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 24 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1e8,0x1df7,-0x11530,0x10ba3,0x10ffc8,-0x53fbcb,0xb049c0,-0x887e26,-0xcb01b0,0x2cb5056,-0x3ca6920,0x2cb5056,-0xcb01b0,-0x887e26,0xb049c0,-0x53fbcb,0x10ffc8,0x10ba3,-0x11530,0x1df7,0x1e8,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 25 li9=padCoefficients 25 (liCoefficients 24 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 24 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3e8,0x87bd,-0x157c0,-0x11c551,0x681678,-0xb1d005,-0xc33a80,0x574f22a,-0xa7882f0,0x929d922,0x0,-0x929d922,0xa7882f0,-0x574f22a,0xc33a80,0xb1d005,-0x681678,0x11c551,0x157c0,-0x87bd,-0x3e8,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 25 li10=padCoefficients 25 (liCoefficients 24 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 24 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7e8,0x1f50f,0x7b890,-0x6bfd05,0xb2e4c8,0x327c915,-0xec0db40,0x1628003a,-0xb2ecb0,-0x2e7dc15a,0x48a24560,-0x2e7dc15a,-0xb2ecb0,0x1628003a,-0xec0db40,0x327c915,0xb2e4c8,-0x6bfd05,0x7b890,0x1f50f,0x7e8,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 25 li11=padCoefficients 25 (liCoefficients 24 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 24 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfe8,0x69d05,0x4e9980,-0x132ec59,-0x5055708,0x1da53e9b,-0x22bd4100,-0x4762f2f6,0xfdf7d190,-0x10b386eee,0x0,0x10b386eee,-0xfdf7d190,0x4762f2f6,0x22bd4100,-0x1da53e9b,0x5055708,0x132ec59,-0x4e9980,-0x69d05,-0xfe8,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 25 li12=padCoefficients 25 (liCoefficients 24 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 24 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fe8,0x1554e7,0x1da9c50,0x1fffc93,-0x32e79838,0x423cff75,0x1244c1fc0,-0x38a027ae6,0x232df7850,0x49b0029f6,-0x8f6dd7820,0x49b0029f6,0x232df7850,-0x38a027ae6,0x1244c1fc0,0x423cff75,-0x32e79838,0x1fffc93,0x1da9c50,0x1554e7,0x1fe8,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 25 li13=padCoefficients 25 (liCoefficients 24 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 24 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fe8,0x42fc8d,0x96d64c0,0x388189df,-0xd2ec4888,-0x2978a0045,0xaf0e3f480,-0x2a4706196,-0x21bddae1f0,0x2fb35f8002,0x0,-0x2fb35f8002,0x21bddae1f0,0x2a4706196,-0xaf0e3f480,0x2978a0045,0xd2ec4888,-0x388189df,-0x96d64c0,-0x42fc8d,-0x3fe8,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 25 li14=padCoefficients 25 (liCoefficients 24 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 24 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fe8,0xcef37f,0x2c033e10,0x20316ce6b,0x1432a56c8,-0x1fb638c4ab,0xbc0bcdac0,0xa30708b47a,-0xd60619d6b0,-0xa1b2f7b1ba,0x1ca68e1ce60,-0xa1b2f7b1ba,-0xd60619d6b0,0xa30708b47a,0xbc0bcdac0,-0x1fb638c4ab,0x1432a56c8,0x20316ce6b,0x2c033e10,0xcef37f,0x7fe8,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 25 li15=padCoefficients 25 (liCoefficients 24 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 24 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffe8,0x278d855,0xc37fca00,0xe4332ab57,0x3c10e205f8,-0x8b31b140a5,-0x248458f7a00,0x42f058c8a4a,0x560320cba90,-0xd46d401a60e,0x0,0xd46d401a60e,-0x560320cba90,-0x42f058c8a4a,0x248458f7a00,0x8b31b140a5,-0x3c10e205f8,-0xe4332ab57,-0xc37fca00,-0x278d855,-0xffe8,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 25 li16=padCoefficients 25 (liCoefficients 24 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 24 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffe8,0x78286d7,0x3496b6dd0,0x59df648e83,0x2d1417369c8,0x33c157f10b5,-0x184463c20a40,-0x17218ac8cda6,0x5d61bcf29650,0x16995d92a796,-0x95ff6682c720,0x16995d92a796,0x5d61bcf29650,-0x17218ac8cda6,-0x184463c20a40,0x33c157f10b5,0x2d1417369c8,0x59df648e83,0x3496b6dd0,0x78286d7,0x1ffe8,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 25 li17=padCoefficients 25 (liCoefficients 24 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 24 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffe8,0x16b7925d,0xdda1a5940,0x210f375b60f,0x19a410a0c478,0x62ff4137a97b,-0x28266f688c80,-0x27c9a8c986b56,-0x31c04ce298f0,0x5e22f0daed2e2,0x0,-0x5e22f0daed2e2,0x31c04ce298f0,0x27c9a8c986b56,0x28266f688c80,-0x62ff4137a97b,-0x19a410a0c478,-0x210f375b60f,-0xdda1a5940,-0x16b7925d,-0x3ffe8,-0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 25 li18=padCoefficients 25 (liCoefficients 24 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 24 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffe8,0x4486b4ef,0x3989ff1b90,0xba3555aa2db,0xccbdcadbc0c8,0x54f41beaf3395,0xaa101981d10c0,-0xe42d44fc77d46,-0x3581658d8fc0b0,0x87e1bd48ef1e6,0x54fa7f866fa760,0x87e1bd48ef1e6,-0x3581658d8fc0b0,-0xe42d44fc77d46,0xaa101981d10c0,0x54f41beaf3395,0xccbdcadbc0c8,0xba3555aa2db,0x3989ff1b90,0x4486b4ef,0x7ffe8,0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 25 li19=padCoefficients 25 (liCoefficients 24 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 24 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffe8,0xce541ca5,0xec955d6280,0x3f9c0810b807,0x5e92e1ef152f8,0x397952992f4a1b,0xe8c4bd03ba3d00,0x1127b5fb787e18a,-0x1da7d087cc5fc70,-0x46a2564187e212e,0x0,0x46a2564187e212e,0x1da7d087cc5fc70,-0x1127b5fb787e18a,-0xe8c4bd03ba3d00,-0x397952992f4a1b,-0x5e92e1ef152f8,-0x3f9c0810b807,-0xec955d6280,-0xce541ca5,-0xfffe8,-0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 25 li20=padCoefficients 25 (liCoefficients 24 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 24 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffe8,0x26c7c53c7,0x3c5aed83750,0x1544d82778173,0x2983f6d55d1bc8,0x2263a77329ff7f5,0xd3d6edb7c95cbc0,0x257011092c00899a,0x22fc69500d3ae450,-0x27860873d30456ca,-0x60e9ee89116c0620,-0x27860873d30456ca,0x22fc69500d3ae450,0x257011092c00899a,0xd3d6edb7c95cbc0,0x2263a77329ff7f5,0x2983f6d55d1bc8,0x1544d82778173,0x3c5aed83750,0x26c7c53c7,0x1fffe8,0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 25 li21=padCoefficients 25 (liCoefficients 24 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 24 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw22 : List ℤ := raw_ints% [0x0,0x1,0x3fffe8,0x74874f92d,0xf50ea08b5c0,0x700461f428f3f,0x11959cfce4fd178,0x13103a6d313b8d3b,0xa185933372896280,0x2c64d1a3dc7eaf4ea,0x655ba36e7e03ff010,0x68cc59c4e8848b1c2,0x0,-0x68cc59c4e8848b1c2,-0x655ba36e7e03ff010,-0x2c64d1a3dc7eaf4ea,-0xa185933372896280,-0x13103a6d313b8d3b,-0x11959cfce4fd178,-0x700461f428f3f,-0xf50ea08b5c0,-0x74874f92d,-0x3fffe8,-0x1]
def li22 : List ℚ := liRaw22.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_22 : padCoefficients 25 li22=padCoefficients 25 (liCoefficients 24 22) := by decide +kernel
theorem li_spec_22 : coefficientsPoly li22=liNumerator 24 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_22
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw23 : List ℤ := raw_ints% [0x0,0x1,0x7fffe8,0x15df5ee95f,0x3df2791a3110,0x2471a35e15304b,0x74191b685e4bac8,0xa07b7b4f602251d5,0x6f0bbf62b3961c6c0,0x2a01cb158e693a8afa,0x92f995c43be27e4550,0x133b6427c4a011d0986,0x188dc4b6c46ecce1060,0x133b6427c4a011d0986,0x92f995c43be27e4550,0x2a01cb158e693a8afa,0x6f0bbf62b3961c6c0,0xa07b7b4f602251d5,0x74191b685e4bac8,0x2471a35e15304b,0x3df2791a3110,0x15df5ee95f,0x7fffe8,0x1]
def li23 : List ℚ := liRaw23.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_23 : padCoefficients 25 li23=padCoefficients 25 (liCoefficients 24 23) := by decide +kernel
theorem li_spec_23 : coefficientsPoly li23=liNumerator 24 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_23
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x18,0x114,-0x7e8,0x2982,-0xa608,0x20dc4,-0x547f8,0xb38ef,-0x13f370,0x1ded28,-0x261690,0x29431c,-0x261690,0x1ded28,-0x13f370,0xb38ef,-0x547f8,0x20dc4,-0xa608,0x2982,-0x7e8,0x114,-0x18,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 24 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^24 := by
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
  | 23=>li23
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
theorem cache_li (j : ℕ) (hj : j<24) : coefficientsPoly (cache.li j)=liNumerator 24 j := by
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
  · exact li_spec_23
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee40000,0x9ac66d9dffa73fcececea4df2c8f00,-0xa7cfe7900e713da2593071833e6f840,0x7607bf7213bbf5b1e8773f39e11fff00,-0x3c8aa6752d1c5d8231f8e477c8313e350,0x18236b7655bdb3e8bef9ff6f997f961b40,-0x7c955cd02e147d06c154ee4d0762377790,0x216a4b92c2611f36840ab6629f0c2227800,-0x799c5c42204bb4f89ddd83a00c58e63dc94,0x17cf130f45add4dcd92a94206db083af77d0,-0x40ee55edc3861f5f2ba05bd3c32fde618214,0x9b8fb99059d31cc12f6c9241a110ffc41980,-0x149c4ee66dadf80e1a1620dad408100560074,0x26e246e48c7a6b3989a9367c4c8648b8e7b10,-0x4197880d2e28195db2819905f8c1df69a6d34,0x634de84cb1f85197d33944c84f11f9da71f80,-0x87576d79abc4a954318f40a9ab36509e26e25,0xa6717728ebc95e82a448a59d0b2a932ffb1f4,-0xb9091a7385e36638bb0fe7012e41c5038a875,0xba3112a577d887b938b19e2fa2ce61b9dd7a0,-0xa9b93801dab6c2aa2a7dc08f313e9bbb0a6b9,0x8c352a0ec0ccdcd67861dc2550a7c8f7f8ff4,-0x68f6b4e9f28b4e6e0d25483b7da90f6097e59,0x472dec4e765da703b6b60ea6545814c388960,-0x2bafb901b79eb25f3048abff3f437f6fe2059,0x183c600ae545230db0a3fd83c8038189ac044,-0xc21ce3f2141ad658424e07f9a5e0a7b76ae9,0x577bd5a4d521576ec3fcb2695ca218515cc0,-0x236639d3d39c85f2e967b283dd84020472ed,0xcd1320621b1263c1058b82e979fb8955344,-0x422bff00f7e2aa10bfe1ebe58dc9690a54d,0x12ef8ff9ab06b58fc8890e3bfb17aa79440,-0x4c71367d861e340af93715d351b421f0df,0x10e31a2256306154585864088e068e941c,-0x33d3885d19a70ddc1f4833301713f250f,0x88b51f95777af8a1f2a6c558ab443420,-0x13220197bc01aeffbd80c15d064b37eb,0x23d12cec29d7e341b651c40d97002dc,-0x36fbaa2a1dbe65cae847c7d10ce88b,0x438596ef7113a214b3554d491b4e0,-0x4034b3198659598eff5446ccfecf,0x2d386ae68c047894f1a44240ddc,-0x1625391134d159057c59064fff,0x6dad3697f7716489353a9500,-0x125804d59e67274f9ffafeb,0x13c3062350b094d9fe89c,-0x4365e8b1ba5e87cc4b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 24 45 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 45 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 57 indices rho q0 m0 0 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 57 indices rho q0 m0 0 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc800000,-0x132531288cbe5f62a065231ac00c5100,0x1489a2c93a7539315290b07e90aad1bc0,-0xe49f724a13e0acab9eadbff7f2a159800,0x73f9d88a6f54dfd8568b871faf92833430,-0x2db88af37edd3a9c008cfb2764d16fb2600,0xe9455537c4e251edee0851efd69f79d75d0,-0x3dd5bdc8ea9ba8fad79791bc7d16e7e51d00,0xde5a4da7894ea5a5ae266811f9e10ba527ac,-0x2b003401f901ee18df7e060a130ec712bf740,0x73cec0122c69a90b3ebc258f8933510977224,-0x111e92d44cd4d2645d7125837409900b073940,0x23d1203d65b92c0feb7d69a6e1fefc5b31267c,-0x42ab141aa2f6671e678ad26de2cd7f4ca77ac0,0x6eeb36865c3b98bc3e5187bd8e72243e8df474,-0xa59127ba7eeef2e0022e30c258357235227780,0xde64fdbafa4ac80480650dafb716e68dc29a5b,-0x10d726bb6450f4c35b48033f25db10acc60c710,0x126fae4d5ef2d650c784b42f342c3fa4fd9ae89,-0x1242afa870c4369a025975028dcdcbe060b7c90,0x106060d545cd7b1dc9afdb19a8f35eb0ccf6d53,-0xd4d9a0d3dca4a29f5dd38769960177d8066db0,0x9c9af44c7609f7f8bb8c4c2d1d3e5b7293b009,-0x684fa8a743fd7a572170ccdf0b8a1513162be0,0x3ed7ccf61ed816ef739e408f91ccdfd165863f,-0x2232c438590331eddb33b23cf36ea6f8569490,0x10c7b54d2781aaa0ff96841be7c5da6136ff65,-0x7682506d2579c02e759a197180b91b1acc4b0,0x2eecb2a2ccff4f4048f9b722610161b5b2c87,-0x109c11f6629f865f63441e0f7145ddf508530,0x53bdf36c1714713bd5bb6cf78bd0b1b36335,-0x175fe89e21d8cd7eb6a7ca8fd8ab8ba1f6c0,0x5bec026d0b181df1660c58ef879ee6dff71,-0x13c0bb7565b8552118f9f609a3eb3d6a0b0,0x3aded511bcf17072cff2ecd64254fcfb5b,-0x96857b459c97f3d7b487b811b31a10ff0,0x146029dcc9bf07b8fe3327fe5072dd889,-0x24cd3c6f2eff705844569fc1ea7ba890,0x365931cbf051e684b469214a1b5e96b,-0x3ffc3e813193d47c5724f1c29f5ee0,0x3a164121f8c524d02bae2f5003409,-0x26dbbcc6746b9053b974d269cf70,0x11f5b1d08e99c4372b82705d913,-0x5342dd312f1bcc02c3d274790,0xce5af836987f03983b57731,-0xcb061ef779744145e2fd0,0x26d2dd557146001c8d3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 24 46 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 46 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 57 indices rho q1 m1 1 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 57 indices rho q1 m1 1 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb90000000,0x25e663036643162041782e4b4765dcf00,-0x283bd2c0152364010b74bdd7f2b8a5c440,0x1bb21d65712e896291cbcdd9c26b7c74000,-0xde5d29bbb17bc09597e1e4f87d400f61d50,0x56b21bd96627efd4264a8a43d142425d3d80,-0x1b559f9c9d4d76aceee1a1df1a8a2d9ee0a10,0x7299b6b0b4f18e781328d95dbed2d9855b200,-0x1974198a66a4dbffb188dd3a5c22c417ea3c14,0x4dd079e1b95eb3a87ba839751eb6a9885740a0,-0xcefe7f312a23226b9664ed13795cd292132834,0x1e370419b8badebffcb9394b0815dc9042aac80,-0x3e66e4a4e000561dd2f007d27e02b1beec7d114,0x729f2b8a3dd05c95e61afea53b10d61c9b31ba0,-0xbc1f9a01abf986fb4a3743f1ece7fba08b45f34,0x114ea07a6a514316c735ffaeadf6c14c769c3200,-0x16ea8fbb2d66156eb057601cbadd4a774bc5e2a5,0x1b5babc3e99ce8e868263e186b89568bd0ee6468,-0x1d7fd246a7555aae3cefe52e13d66f3d041e765d,0x1cc3c3d546d80632dd97ad81ca285dc0ceed07a0,-0x1962608269378c0ef0b48fa73e09a4785b904d01,0x1447b269df156da200d1a0153e8e3682451f5e08,-0xeaaa964dd4d829e54bea4e7bf1b7794a6173219,0x998c47c6ddbb226e0661105fba4d4fb79a8f580,-0x5ad0b38f98c3bdd9698442fd375e4a2cb167209,0x307bbda26da12cb91fe55623b1f5925b2f9bfc8,-0x17521761e62ed20f23a81042a597989d2496401,0xa152f0f4b34d03022dc677517567cea8c51d20,-0x3e82f01ad27f938bab059e709bd6453439c605,0x15a1e33f0912d1ec7b37e089a6f017d7ac34e8,-0x6a833b9500c0514ea6b0015ab43d7de58ce1d,0x1cfff761835ff32a4046f3cdff0e1765afa00,-0x6f1799fff62533dea5340cca4e9b195d877f,0x173844f48570cbc75175b2e464dee0568538,-0x4332ba4ed8e69fd1f429dfc7db32fcbbaa7,0xa6843bbbc66451ff7768bc1f67862749e0,-0x15cc435d87f5e5f896dac39eac43e39a63,0x25f9e1ab382e446ce0ccd25ec43350198,-0x35ef7497ef66b54870239de270313aab,0x3cda2552a5a0c89ce84fac2edf34c80,-0x34b7059cdfac8e5f112e99385c777f,0x2179e8e285b8c81b345803b28b8f8,-0xe97a80f3a0af758a19e2502ce47,0x3f4757762cc2b75f1a687b84e0,-0x9123a4c2ca031b1d53ba9473,0x82566f6979b3ac82a2a058,-0x165b8838419227264c1b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 24 47 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 47 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 57 indices rho q2 m2 2 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 57 indices rho q2 m2 2 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb39577200000000,-0x4b0b076041467580d4414e40c0f15c1100,0x4eda67464150f3a5c815ec1233485a0f3c0,-0x35b788465ab967c4162ef87f692ca6ec1e00,0x1aab72fa4239992fc3775d4fb3ba36a533230,-0xa49209f84f1fdf60a317c591a2b8e4238a180,0x3350a15fe745ddd6fff053e0c72874003f8050,-0xd4b679265a87e17dd9dcd39fd2413cd1143300,0x2eb33f31e353320c954d47f68db1e7b6d36242c,-0x8d158e28d82004733a8c163b84ab645cf1310a0,0x172c4c5671ca0a34c45269976126f98b23c54d44,-0x3573bd8b0708ea76d4c4becf07a462bcf47480c0,0x6cfeac8a54b8c324b5cb8f5cbf49f4a4d0dffddc,-0xc59ad5a00bb895a082271c71d15b6d77b576a5e0,0x13fff57c04eaa84503d508c48819924cb73902774,-0x1d0956277c6ab9b94865e4a54b74beec403250680,0x25e7fb09ed8bcdcd1de02f65a85e6254500e7d4db,-0x2c9944717fa4e3c1bf295b492106bde61bac13528,0x2f5f740e607106907d6a7d55a2e59c039b1e10eb1,-0x2d7be5ce690b15b530cb8dfae450a755b9361f670,0x2780c19ab65a8b47a096128720abdc9097f3b660b,-0x1f0b23dc6d8e071055953c4b9e1c02576ad56b9d8,0x161231f61682927f2631e6330d86cc0449b5efd09,-0xe3050ddee49a107cadcbf4d84114b339433ebba0,0x83d4f618766e9887331b0c2326ed5ba4b4e8274f,-0x450dd2541b93501c355ddf1771f370f676aca0a8,0x209061567beff73955ecb2a4874cb83d4839057d,-0xdcaa21fa7bb709fab1ca9f030e43f14c268f450,0x53aeab1d01405aff21077a3a2d0440fbdd7112f,-0x1c5013105c460f52ee8eb6dc130f706d90a3498,0x882553e2a9bc417fc08e42e8584371298d4b05,-0x242830617dbc778a4f09e295e5bc35eee78c40,0x86ebdd13139d83e9c6a892859a787736e9d51,-0x1b6d8c62b4505b2086cf4c378640e3973cb38,0x4d11b0d78ad328b151ee630e07e012fbdb33,-0xb90fe7c14c0e9f6a1996aa937131ff2dd10,0x176c32176d3556d63330d4cc2b521e39a91,-0x2759ff80a030a699c5be0b7f7ae57066c8,0x35bb5d4b38775236fc7debca0e0e44acb,-0x3a129f25f5da4ec85dc8cd9f1c5474a0,0x2ffb80d18504bb27c3fd05d517c4919,-0x1ce8b83662c29b21f47769ea25fd58,0xbe08e336d408de99f069b4efacdb,-0x302428472af4756d6b29d3fa370,0x661d9a9a34f5cac0768cc7769,-0x53a88a4657cc1b655f6a368,0xcdf2100f5dca300d2823]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 24 48 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 48 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 57 indices rho q3 m3 3 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 57 indices rho q3 m3 3 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee4000000000,0x949ead5dd4c178ee460f70bb430ba260f00,-0x9a9c006ffa69cfea33ea6d4842aaed272440,0x6840d72579f2d6d91cb1a9ac85aa5ba923c00,-0x33391e2439e4471812e8abfd0ee0ad6bb32350,0x138bb31c8638eacdecaebccad7d84452f551680,-0x6074fecc756a698aa8c132048bbd6e99c5aa290,0x18b68f6c76475ef7a40f5b062290348c05890a00,-0x55d3cd0aa7add9daa91f884d34d1a93df7af2d94,0x10048c18a8046af41f06f09449c83fecb7518abe0,-0x29984c749ad2deb42d3e61d1965722ce24ffdcbd4,0x5ec723a312c784f70af74ba39c6342b0851cae880,-0xbeda2b58eff378233b7dfa4bb9e1b83dd33830234,0x15594ff28743b2b7b099fe1ca4cce80c8593dfa7e0,-0x221e1d7494df8a094a46489ce004b36b9cae639634,0x30dd40959794ae8af1af46e715d8ab7fc93f758200,-0x3ee79c34fae972b741d4bb372a5e0b97df47008225,0x48f3e6606d7ba6da0148627512d98487b9da23f838,-0x4c595ed3b716fc6ed6e65f33aeb8805abed3f6ae25,0x4830efe0d690e0247e399bfc9ddba049ebf8f065a0,-0x3db6fb14a014265e8b8568b0eb1fa1b715425102e9,0x2fb6633d9e59e5452a6d3559dc06c5cfd39334e2d8,-0x215a642c9679452c53373b4dbe39cc432378a6cb19,0x15119c7881ac0cd309ac1a592a870aaf3bf5b18580,-0xc039abc21e4a0154fdf69f90620db41f6da92ea79,0x62ccf795ed27e27dfe6e5fc99205310d36f784e58,-0x2daeb84cade90552fbfbdf51f673781fcfdadbdb9,0x12f42c3d5335fc9b909172595a28db44729110720,-0x708f5dc3d6071586ab56b0627d5c9142fb9ff6fd,0x253c448b351b36e10111f1ad3ec6bee63f1cb178,-0xaede4fe4d58dbb13df2754a9065aec417b6c26d,0x2d4c96b470c2c5c91ebb1d30c7f5f69790ed200,-0xa4a6ba6c50f109087509ce3838fcea4acb459f,0x208d78e07a6f4be1f61aa6cc4aedf75558aca8,-0x58cd02a876ed42150090c304d8dce1b3d6f5f,0xce994857ab3bbfa6e2c76c205294b96c97e0,-0x1946da480db4df400412cb71a853956dec3b,0x28f11ee1aa59e15f361e5627f4597f69508,-0x35ba89b6ef9166eea5472acabfe9943a0b,0x379ad9f407bc2cf41ab45fd3041197c80,-0x2bcca2260037b1cda731ad008f1138ef,0x1905a52f511aecffa0dbde9d4b7d7e8,-0x9aed7a9d207c3b6c633837213156f,0x24a8c29fb1256b122d51bf2c76e0,-0x47dd58897f706739e338641b9b,0x35af9e88a5e1fc96dfc79248,-0x7688ce8bd9f9d4d1ddeeb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 24 49 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 49 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 57 indices rho q4 m4 4 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 57 indices rho q4 m4 4 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60e64000,0x20eb7b000,0x503896500,0x74a81a980,0x71a8aab10,0x4ee858100,0x287d563e8,0xfb3d6ca8,0x4a95a151,0x1109cf40,0x2fd89bc,0x664c50,0xa37a6,0xbd00,0x954,0x48,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc80000000000,-0x126660e0c78c8c4d6fd5fbca66c568a9bd100,0x12f46ab218dcad4288e7802e41db290f9e23c0,-0xca768873783a267b0fffea7711115bdb554e00,0x62770f0f900527900b3610c67c5b930efea6830,-0x252e8886fe0639cdf10f3703b243b1260dfaff80,0xb58a50fcf94a893b7cfe9d097a56c8b770c9ead0,-0x2e01b249fe523f38b935a9de5d25903cbd3dd9700,0x9e003f6329e08f52952c3a47820bea2065dd688ac,-0x1d26c2e300f07b0163af029992825d242469ded620,0x4ad10d3c2aa1ab41c2dfb0e31be5134cd4ba461064,-0xa86f98c95e9687e03f512818587a6366c2abe9a1c0,0x14f0292256b31e9a0b3d421c5f3091db5c0975ecf3c,-0x25007c08323bf640a4591b0fa5ebf0718ddc945d060,0x3a5dd0f3c9e3bd2adca93d6d43372b5aa7f54822c74,-0x527aef45e8bfa62e20bd8e66a1d8a6ad9dac3fd9480,0x68b938a3aacbf90ca60d6fbc45e88e446f91bc0cd5b,-0x77bc4d538aa88d3a83cb0ca87a7765bf5e05acd7f88,0x7b7c09ea346f625964f2219562ba516adfff721c2d9,-0x73010cb444961a8d548ed6a528055e42e31267a9fb0,0x60c9911bdd613f29e30b10d0bd1e6ae0be267fd7543,-0x49a003579aa67e117cac621241fd660717822601bf8,0x329c4c57954a8d4f5740d0a3ac360e62e628033e489,-0x1f6b174c79a7bf00123b54fbab9071918acf8bc3f20,0x1198349d12953ba57e8668de971b043b87b92e599df,-0x8dfec48130ba9d10a98057947d84b962e68a484108,0x40610568e56c82bc9e676f1753cbc12f5004078215,-0x1a2b60adf948123bea8cf264e16aa912a645acd610,0x981da6bad2a4ecf9fa83046df3a2504c34a0306d7,-0x3133cf35bf4896ab7de6f654ac4c3d7eb594f69b8,0xe1ac9142fec9e350a77f790dcaa80ec51c074cd5,-0x3905cf1232d843c999b8289bb4b10750bb174740,0xc9e132728623268c5347aa457903c6eeb329431,-0x26d074a111e733ecadec9c0b22ba2bd214d1358,0x66c8510a7406e84ab73cf05153f9869e45a40b,-0xe7a7204a14cf771b6f7c980fc83c2653031d0,0x1b64499c912fbefcf7d2c8c53b0ca8e65a519,-0x2ac37a3f13f1fed5157ea26065a22f18a028,0x35eb3651c85872940e5b6517801e82e02ab,-0x356990f4ddb9ef6c4257d54c233aed3c20,0x2816ffc2cc1470201825061319c2b85a9,-0x15b45b23843736f239a3640fd41a34f8,0x7e7fc8a6a64b07aafab2032f3fb523,-0x1bf082204e54f3a0ac8680ff57ab0,0x32961626f65e49abaf28e755da1,-0x2271d2f75eeaa9b8487d75a48,0x4434be359c87dd01b82273]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 24 50 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 50 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 57 indices rho q5 m5 5 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 57 indices rho q5 m5 5 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x525ed8503b2b88d03531000000,-0x6e6dd3a7f05e51d06f2db80000,-0x4673361b7678e664bdddcb8000,-0x1c774a0ca154bb74c45eecd000,-0x82de4cb2071ac0dd98475dc00,-0x1c760e2df3f029f5c8a748f00,-0x4de4d65105c039a128aac5c0,-0xac0111054ad42e765101140,-0x137e5eeb3fed0df921084f0,-0x1d638014b477983018ee10,-0x2527a6f2de13d0d5b2414,-0x279db4c9ad381e2243bc,-0x23bdb4b04e7db692a61,-0x1b507e623e2c8ce378,-0x11aa76a4b19f58866,-0x9a3b14e94903a0c,-0x469c2f8893d8ae,-0x1ae54ecc53a60,-0x86b9067172c,-0x2210a68514,-0x6c7fb919,-0x1055f58,-0x1b982,-0x1a4]
def m6 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb9000000000000,0x2474af7858328d273362d21f9a6c7ac8de4f00,-0x253255c20d99fe4c1a163b5baaaaf57307cd440,0x1896ff44c55809c64b383df4bb636f07df8f6400,-0xbd6f9d3185a40639a6255b5f916bffa23a40a950,0x46ce051b2fb98537e51dc532f6653efade6ba1a80,-0x15619ee86e19a2440cc46e9c424ef6d496412c4710,0x55c58819fa2ba675fee5dab37cf3f67ff4711a2600,-0x12358f92aa4b04cd41ad6a7b98d645b0903c3d19314,0x3526f4be75dac88c167953d4470c94ee46c115910e0,-0x86d916919a22655fe006c2dc674244cbda84cde0e74,0x12c026dbe21f72bc3a6ec847c82bc9e976554d946b80,-0x24d7c681f3c08ebf3a1e88d00b9f68d4dc1de35d5c54,0x404cb8a74ccdb667da22a9a358de20887824d66f20e0,-0x642139d50b0c9b1ed9341a29bb772b8c281c318df334,0x8ba31ecfa9b0e25eff621b6a910d5c239f469611e600,-0xaee4bb97169f86a77813a09271569d79dc37f2990fa5,0xc52c2bcfa2d53f2cac50ac7d9961c037216a198be378,-0xc86aa6e1c21840ecd729bec560982cd2a3e49491ccad,0xb7e0103dca79bf6d8bfd385fa6bff21456a209a9cb60,-0x985e3958b045f5c0ba6c175f6cce90bee27965a47c11,0x720eeacbb678f59acc9660a5de3c1e1777eae1047018,-0x4d1c2c5912bee00d22b89d8b0ed8b91327f34591b199,0x2f0c65d8d29dd0d18c4d4563aa50179e5889dfa5c480,-0x19e0cff7db011090c6a6c72a9d1723fc794c16346a69,0xccf955b01714d5a650b6e5f7616ac4add343d3ac718,-0x5b22ad6928cd66ca59d0d47a6f761b4b37118cfc7b1,0x244c128b7de21991b5058dbaaa87f4608c615c1abe0,-0xce85d5c3ed9d326f8692d234ee323bcf9f86efc9b5,0x4151760c236f087b5fd33b2ab32df869d967187938,-0x12499d24a33d618308422e33b9a5eea7731cd3c0bd,0x481d53c0ea2122dbaf554421b057a953b4fd53a00,-0xf8aaf917f18054106efc9dc7651f7a8a0df4bebf,0x2e7d9065068ffc979c2ae7e7bb20a2841d504f68,-0x777dfd9f096e680a111c79f71a6a2546268f357,0x104dab306218c39a343ad9eb30efa79d2871720,-0x1dcde81ab85951285795b4184c43d636bef4d3,0x2cd60c1993bb37b93fe93bfe724f3d2fd0fc8,-0x364c2dc4eab5d7447a04e196a1f08ef424eb,0x3376cd47523322e688ca57b437f88173580,-0x24ca3459a0ab2ef3f346f83d18e7f33ddf,0x12dd857c02596f94278252be75a090428,-0x676f1f74d95630d34430c49b568af57,0x154f6b2ded259c236410948d6b6220,-0x239d4935fc81ecdc438d815d7603,0x16183b1bdd8a82c65710256d88,-0x273c89e7745e6c1d08854bb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 24 52 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 52 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 57 indices rho q6 m6 6 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 57 indices rho q6 m6 6 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x1a4,0x1]
def r7 : List ℤ := raw_ints% [0x87239ae3a1136c75974464000000,0xb4d9d067361f92b12631d0e00000,0x732696f1666dfbab7710b4260000,0x2e6d42469d388aa52d6ddeb9c000,0xd4ed4133499298b4418f2702000,0x2e2ed0f6b22eea165f9a2c4c000,0x7e040eba0e305bed0a2db7e000,0x1155372879e6818a00a5b18740,0x1f4f52a8ef9616c8337cb0880,0x2eff58334415682f7c32cd50,0x3b1ed5e529118cb86d7f6c0,0x3eac422bb25aca9f96125c,0x38296124a6ad365e7e9a8,0x2a94340e31308ec3aa7f,0x1b46a2c051f445ecc80,0xeb5e77c3cd36ff6ea,0x6a348d27db7bec50,0x27b6740df17f1d2,0xc2228e452c240,0x2f7868a070e4,0x9001a87448,0x14186c747,0x1de47c0,0x16dae]
def m7 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb3957720000000000000,-0x483ebb82d6066c1e48f7ebac21ce2de52eb9100,0x49065081cca14c3d68763c1c1ee28c9bd140b3c0,-0x2fd0672f17d1962564696ce8f00b85844be10e600,0x16cc178ba4e96c19fa08ef2aeee1bb6a4b4f394e30,-0x86f8bfbce0ab5b9cab10ef3054b6bf11319697e780,0x28576b023ff803e30b7ee5662205c74f59ef33cd950,-0xa022cfdb272a2e3e6cc09ac126719b9f7c8cf34a300,0x21a1c31954546a9d12a76772084ddb6ced65ff6d912c,-0x611719f0e3749811bdcc705b0d0c45719df62a2a4c20,0xf389e883a1b0e67affc7a5114476616f1a3bed583884,-0x2178b2cdf141d3ecb7f8b20082e5ffd4a275d97d954c0,0x40fc0ad7ce70a133fe5eeec1ed461aa06b0b5c789d59c,-0x70066034fef8c8ca3984e10df435f9727cd81f9e19c60,0xac4049a2df2478456b6e98d6c3afb1cfc3e9f3ff41374,-0xed190d8668272862ed8dcefd4f7e38aa2d9fcc78a4680,0x124fd66a170e075572b895f124fbe4bca8c1ffa3eae3db,-0x145c1540005933f90939a1b566709b347972cacad92f08,0x146659c762b40c9b21f7f655bf1c3ec07e30e43c075141,-0x1270c082635009d0b15d0b1d51fd9e00e2523945188d70,0xf0c37ec39073726da5c0e885cc305f9d9b9deae89babb,-0xb161d6d146d433b843e36fda89672e4101a94986652f8,0x75f4b423b813961db7e0cb844bee2147515474b0d9089,-0x46bed0c7aab204e329c1b4974e9b48b5fd5894c9a9ba0,0x2639251eb204e3be802b399e01211016bf1d134a02fef,-0x1292b64776416946fecbc4836313a8fe71798b93fd488,0x81953021a2d079c9a815a4fcc6457e53f9643780236d,-0x329208f84382db0094dc48bd11064fcb593fdd15b550,0x119a9ace7f35bb7f20ffa4625531cd843b9a1745b93f,-0x571bee529266a30dd0d841729a333d1a5fcf420d4b8,0x17d1d058032e32d61aef1ec831c95ab1ec852087ea5,-0x5b9de997f8a07d313c041a8cbf9a90f9548cb9fc40,0x133aee4543fb0f7c17dd76bf4f5c398f66a17e1611,-0x37ee8d7f614df8be35c47d123fbfa079991cb81d8,0x8b84b2152399b4cfe97cfb5d1d9e4c9fbaf858a3,-0x126f54994feaa49ed0dfeeb19db84e2d577a5610,0x208eb227003bd79fbb38fcc846d8956f0268f61,-0x2f2ea0e60d5567b45b2b8d3521073af6286128,0x36dcbbc95920af39f1578142d5fb6a721fd0b,-0x31bbb19fc2857370a6f0e2df22b9400324a0,0x21d85b52281eaca4124ac894eec18fb59b9,-0x106ddd29008e58e3d543a5e6433f61ed78,0x54afb5d08de9deabe6faeab03ead85ab,-0x1043e4f0fa53f92e558fa6c70768670,0x1913b9a8d71f77fcc768a16fd8419,-0xe2b66e4342bb99704b3a5aa348,0x1690d16c74c5e698f6a807c3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 24 54 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 54 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 57 indices rho q7 m7 7 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 57 indices rho q7 m7 7 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x16dae,-0x1a4,0x1]
def r8 : List ℤ := raw_ints% [-0x75a936e16ae549a7d95b044e000000,-0x9d3681d16a3ac75554987c07100000,-0x63ed4ca3875ec7178a081614f10000,-0x28364711653508e139e1bf755f6000,-0xb809124d8b4e7080b5e46340dc800,-0x27d2bd33f4bfa6773fe3558ac1200,-0x6c614a0bc5220c308c8b7d406880,-0xedd22d127c665cb77546bcc1980,-0x1ac319c7666c07fbba054d283e0,-0x2805e2140467cec9e2eb5d3660,-0x3222d4788b744e4cdd693e248,-0x34e4da961a86107f51d1d408,-0x2f23016d753b44d33771d72,-0x2381bed5b60c6239d777e8,-0x1692c9c4cbf41bc142885,-0xc1086e4eefcb01725d8,-0x5626c6dc56d5b18768,-0x1fc7f1e7cd7f5be70,-0x98bb303c8b833de,-0x24874df8ef23b8,-0x6b92096183ee,-0xe666e84788,-0x14276c42d,-0xe082a8]
def m8 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee400000000000000,0x8f32da60d4f566bf583141bb4eb778ec0a868f00,-0x8f6be1b5d4ed45279c32f47592a888662b6efc440,0x5d07a959d9ff498bf938c0e2d19e899c69ee28fc00,-0x2bee793c78bea14ab4b458f23ca4bbb4776d210bf50,0x1018d42753c6323ecbcaee30418db21956ac248eca80,-0x4c3517cde8fd037a7bb5d46410bdbbdc6255713b6f90,0x12b65c6c778cbafb225f914631b23117c7ed4a56b7200,-0x3e3793743ea074190b196a46aaf43d752b7278cb83494,0xb1ab5eb63d39b786eabdd8806a4ed8671d9e9815a5ce0,-0x1b8b6c01066f85b4ae5f8cdf54e044d8194d7ee1b5de14,0x3be1453ce5f9522092307542f3cccad394f33c3e5f5280,-0x72e49a7abffd4dce5202b3ca253f252100d844dfd5c174,0xc3abb36d9f75175c839b1d866e94ab74167742942ac4e0,-0x12920bafd94eff6e3a9c9329512ae87dbe7ecd55aaf2234,0x193bfd87971f503179d8803e03c81b47d493948ba513a00,-0x1ec563c2574104b9c8b771f39ce6f37f9499c6bc9b3bf25,0x21bee3df7867f1e8a8324dbee69d52c6987baffacb33478,-0x2155eb124c9402b30e0d565e5897e293c748991ed71c775,0x1db1c58b3f105e7cf5c275ad6cc48a8bc44c2344e1cba20,-0x17dd81898f9902689bc35e9ae3373b06b1939d98702c6f9,0x114eae4d984609a599ba9d7118c8e159b701e601749b518,-0xb526a561446ab15e0f7a36c9190e8f7c64603225bf3899,0x6acf83e769c265eff3b03ff410bd36f1a7d0c2be17b780,-0x38b171da14631866e87af23160424b8bdbaed2764096d9,0x1b0ac5c72d2472671d55553491a75b3522147946d87098,-0xb90d21b7ee28626d90f3eecbc7341ce6c1ac52770f069,0x46c47be4e45749faa5375eb7e5da078a8dd11b36beda0,-0x181dae436f5bb13cc00af394e650efd14c99afdffcbad,0x74b0ea8f8b4d0a504f096264d504b08654f7092383b8,-0x1f2a18fa7b2e41966b83a174f9db6acd78dddf52df0d,0x74e9e10a691de47bfdea816fc302cb8914fe9ba4200,-0x17e6312a7aa370810ca425ea20c4304a17ea46d5cdf,0x4395136e39b704a9b678d98062bd21622cd7636768,-0xa3965281bd56317c5fdb36f2a7d970894f429490f,0x14edeef9715514a200d83d0e063cdc7617c73e960,-0x23b37d524f5b88ec2429c5a82e64122c711f6dab,0x31d3ec84e898491db649555fc4a406f020e29c8,-0x379ca2cd08e5b1a91fae37437ba9b50fc1ae4b,0x30324eec0bddfb68445ea4d03dfa894c07a80,-0x1f35a5483342e33bfdb24b8d06a09b61eb4f,0xe5566f45502bf350f811f0e23029d34da8,-0x456bf9e7877f46bb1ad07229f1706477f,0xc6c1d07ec011edc3851ebee59ec0060,-0x11a8bd11d65a1cd00e9ecf665aec2b,0x915c2cb2d2172915c1baf67c808,-0xcf98d9abc4442c82f7aa7d8b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 24 56 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 56 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 57 indices rho q8 m8 8 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 57 indices rho q8 m8 8 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0xe082a8,0x16dae,-0x1a4,0x1]
def r9 : List ℤ := raw_ints% [0x483d077e4a78caa63a0e85ca28000000,0x6062cc399f15e7f02af7e42922c00000,0x3d2b8d934bb3bdf5272800cedd7c0000,0x1892fac04ca4fc25e099603278178000,0x7041e96f84a0887350b9163d1b10000,0x183dc9f6948ade517935ac0f90e1000,0x41d2d106a7864f68f93fa117d13400,0x9012a3af3d0300bf54ab0160d6980,0x102ab3d7e733de373ecf0a8270400,0x1819de45fe1321a20c09225956a0,0x1e154a780eef47f5e0429b8e6c0,0x1f9c08fe3bee8a8f61a7f84518,0x1c09ee3b2384dba92ab75a020,0x15022f4c243a8b93d09fc14e,0xd46100b010b447c3933748,0x70af9fcc7d7ecef08a59b,0x31dc2c9a9debb2346780,0x1233f38c97b49100998,0x565ee0101c6c9a9d0,0x14549b372185fdc2,0x3aa8c9f4f7d7a0,0x7a4c8a05c5d2,0xa4fa7040e8,0x6d0456b3]
def m9 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc8000000000000000,-0x11be52542492d619c1081419682f37a495464b5100,0x119cbb0b18ec6214bd76ea37cd4c34537776a14c3c0,-0xb51d427a736bfeade680255b84f2c4243f446acde00,0x54ba0a9b7e657f2159d0bf01da005d98dd745ee54430,-0x1ebf398069edab431bdfe47296c0e972c6ec047c6f780,0x90220f0da04137aa30386e0fb73308e64ccbee994fbd0,-0x2308c6e0463c2d8b3c276600e773b2e20a21de9a632f00,0x7347ec4c748285193edcb898408f9eb095f2f79a160dac,-0x145b3f60bec2bc5ca2d1dcb6aae52a699472d3220ae0420,0x31f1895d01526e34990b08ea443a44b822985ae921721a4,-0x6b5add9a07ab6873e6b070efcf04fd36c91a953834d07c0,0xcb9b0d791015eae8d5c0da7a19f09cb79986232aceb54fc,-0x156a1b4eecf5d0f550991d261d96f7d2cbb47e634c611e60,0x201ea271436dc164d2a9c14d4765a7ab5fd674beabe80c74,-0x2b180e9c634088709961d453d35545ec049327785bf7b880,0x33dd238927847ff613cb2741e5a70b3d6aa5fbac17daa85b,-0x381c5fcdfc5d5a591c2fbd8585e711ce3c0af01371038308,0x36a8040b2ec66139ba67eb578ff1f9e3a72aeb5b67a0d4e9,-0x2ffbc948ef7286bef20674227b1ac5b2e39c5184b36d6330,0x25fcb448622e1129707920be15f81488d1efbdb2e304c373,-0x1b1ef2beeaf52e26627573ec498e4ba1be292048c1f55978,0x1174921f4b2522d3b8d3369a63c8e0b083713fdac0b16509,-0xa1e85a94c781ddba37fb1832692223a21baa886198f8820,0x546efef4b845607f7304c6e4631db35795c69c7372e357f,-0x2789c69dc90c91fe82a6095c3bb561871e0543e38a46c88,0x10964dde392ba59709271494552ed59c880e6af80650885,-0x6375f22b28594a15a852716b34cffacdd37b5ad092c490,0x212e817eef9a34c666e8f343c583da5321994ccd60b167,-0x9d01f9b2fd998baa2f704097f7d44c996ae990fa00b38,0x28f42a5779869771704fb5c78b56bf24b1526987a2075,-0x95d9426f26ac8eac10e394a19d5494350defcc55f140,0x1dd48b635aa72d0cf9a6a85f56e1fac4a852346952f1,-0x52016b80f484c193316eeec8baf43eb4ecff00da9d8,0xc098bb3df1b90aca8dccd85624b16da0279cf4d1fb,-0x17daeafd74fb05a79bba6b8f15511181f427f4c250,0x274b49edfa5871b936ce8a91b71ff0baf2d197869,-0x34cda3a000ca2f6b423bedb4311078bf82e624a8,0x388c13f203114b3bf7dd5880ba610ebc82165eb,-0x2ed58045260bc884370c4e2fd0d0ae9c553d20,0x1cd80010600bf3e55f266333b970eabe8e949,-0xc86d84e064a675397d3ccbd53d688bd4178,0x38f9255c2d235643fc7ee59db37f188f73,-0x97e1f66334e6b30a961bc5027bfb9230,0xc6faf4454b71fa8f3d24b4dc8111d1,-0x5d2d96cad48675f500b83b7030c8,0x7755e766c8164ec88d1b52813]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 24 58 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 58 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 57 indices rho q9 m9 9 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 57 indices rho q9 m9 9 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r10 : List ℤ := raw_ints% [-0x2313c77aff6ea9e8c94d4d37a743000000,-0x2ebe65346d92dab121cd5fa02e9fa80000,-0x1d9fdce646fc4d15022e5f71c94f8a8000,-0xbe21a7aefe0ea6cf580a0eca64ff97000,-0x3631aec72a379fa4f3c27a1e82e395400,-0xbae7d9be95fcb2a19fb8bd8961d8fd00,-0x1fa7e495c66f543b06066d75abc8b540,-0x45223173baefcbf924bafb67d365bc0,-0x7bd105a0be751a0754db3af666ea50,-0xb8131cd4c5003c2115392a110e130,-0xe50e564f1482ab5838c51bcf3a5c,-0xefd7d33defce943810b53882234,-0xd3ea070b8f6d06d404adfdeeeb,-0x9e11d6e41a0a6c6821a06efc8,-0x635be34e73a4cad762ddad3c,-0x3467b50b06dcfda1e08d094,-0x1706b8bab7640b20ef51b2,-0x85654e87f31a994b1360,-0x272b3116355dffa68a0,-0x91be841e54d14571c,-0x19e3f7342fc981cb,-0x34f5b8b93389e8,-0x45b0380159d0,-0x2c89e65f1c]
def m10 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb900000000000000000,0x232f1347dc6ebc2310b3e138ad297bcee13831ecf00,-0x229e550f6198c6aef12b87eee4807b8604d7b3ebb440,0x160cfa3429fec17a263c88d9aa5f0b50f0d2eaef41400,-0xa388d3e78bbe91beea8eb0e46b6ae964b4feaa9402550,0x3ac9c4acd6089d03d5d5dacd59cacd854069c09c0daa80,-0x110ece5826dc16d2a08d20be95a771ce444f69431829c10,0x41aef26e2391d4a6563630438f163ee81aa7538f46e5e00,-0xd5efc871ee1bbbd2e9f6286cc00dd1743e9798e90f15214,0x2562011d68e1e66f2723aa7fa49a5aa70c301bdbb5b584e0,-0x5abb882b2a51d926557b0dc5820f630cb7fbe1a4b03c3ab4,0xc0e0e1b0c9c9eeaf49885ad2feb14c2eb4477e142f8fa180,-0x169a5b98511677eabeb87daf8404f0975f13ae2e5d049e194,0x2597506d2b899749d69c932c66926cd2ed7a89612a21ca4e0,-0x37b3a6dac96b4ca58911af3ca3967d5f914e1f7b99b360334,0x49cd267f1d3c020e6795dac926e099b70751679310804ee00,-0x57ad1026038ba40adf5835d0756d3b475b03a9d0dbd4bd0a5,0x5d97879a87ed0f8a1430fdee57a3cdfc4a3b67e50c551ac78,-0x59e897c560a86394168269154f2ea41d4d36b7fcf6a810e7d,0x4dcdd37638694a8df26e82ffd90f56e884a3ab99c2c2f4ae0,-0x3cae9104c8c51235ba84e4e049fb675aae4134dc01aafafa1,0x2aa818db3430530401f21eadb97823e11bdcdaf47e6ee2d18,-0x1b03bd0bf10d1e7034928c083cc58af392a47a4645594f819,0xf664ee3969fed5fdaedbdd80c8edf5cb9bf0f21b0d945280,-0x7e41a9531e1c6877093a28c2159e6f9292c996ea1596dfc9,0x3a0c38cf25767277997e893a5f3c96e10bcafdfbb9166918,-0x17e3871096001c35a00efd679a7f9a1c014054b673c3bfe1,0x8c6259086436529a13ea07c415cd2a1fe28e62e44b4f960,-0x2dda1baa871958686601dfa64ac5e184e7983527f1438e5,0xd42adde6bb63e767d703967a32cf6917f56dbcb9cca138,-0x360cfa21ceecb2ea45bcfe334b1ebdc2681d134e4efd5d,0xc0e2d2694da7b0d3f8c46d70cde2f27b82797a026ca00,-0x25640cd591bb064ef8247ffc2ca4a028b07a3b5d71fff,0x63eb3957b07c2ee71e137c019db3257971515a253c68,-0xe3a8c5feb7934ff42f675c382d9cf1ee6ce7eb33087,0x1b4b4a911f881222c8ab90a69bf404ceba32e0931a0,-0x2b67a3c99f130a3a963662a922bcc15c3759365ac3,0x3824995682b95e12b5f8d12ef49530398445164c8,-0x39aba90fa520762a8cbe98d746fd447bd391ae2b,0x2da0ccda300bacf7c7d7998bb42696675389780,-0x1ab6ce7838b95f4162ec402c11f9858820513f,0xaf71a805c07526315e20d37b501217998828,-0x2ece5286014bdd7528af796c9dedcb8e5e7,0x741ee82e98ad4a1dd0719584dc567d4a0,-0x8c227588ba862b3d991c202ffe50213,0x3bb6f0bc560cbaaf543e0ad8e4f88,-0x4495443d3ee07c5bb36bc4295b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 24 60 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 60 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 57 indices rho q10 m10 10 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 57 indices rho q10 m10 10 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r11 : List ℤ := raw_ints% [0xe54ac0f5da7e067d91c7b3d89005c000000,0x131348bf5a2eda4d01a9fef961c905200000,0xc1301f527b3f5fe823b28770639271a0000,0x4d63651a61ec9feaebcf663f6fdd38c4000,0x160692424d3710a6a2664e633eb918ea000,0x4bd6d8b590410e1609208a7cd7b1975000,0xcd2628b68c07bc09b5998486fdab6e400,0x1bf257fe84cabe537d87e1f0517dfedc0,0x31f164a8e756b95cf1ba764b087c3e80,0x4a11dafc990b13f00d7b5b7e5724f70,0x5bec13caf24cc21137de0ae2c48900,0x5ff63c882e8a28425c58b6b0ffc34,0x54803ea79a0c7ffedc144bde2528,0x3eca259f1f720334148971d9635,0x274beaca6646513b33f1efdac0,0x149f7dce7f1d80823c2355a74,0x9026607c15ae61e70e02850,0x33d7b1a0eeb319bc081bce,0xf1a12c6bd2c095dc9e00,0x37a94ea6f7a62f89a50,0x9c6449d0644f2dec8,0x13b618f5c0763fd5,0x1979e9808f2f80,0xfe8cebd7000]
def m11 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb395772000000000000000000,-0x45c7dce4e63b072645c4f8ecb61c5fe0d45ce0bb1100,0x441299f54aa39952998670d6becff0d7ba7967fbad3c0,-0x2afae81a9624d6bec3fee365b57517e8b0a1f0eb0b1600,0x13be4499ff8e6613375a33ee9667090d5c02fb81dc24a30,-0x708337d423b8f99dbd63e3dfbbd4529d31edbeede7fa780,0x20567ca9ec442f34548804872b0e1baca1e3d5886e903250,-0x7b4ff9e825a08535503cdb4a51010608e06ce73e4a659b00,0x18da23b4d5302d21ea55241bd0bf08fde332f00b356679e2c,-0x44c4e46b50929ea98e9ca597e9fd2c5b5222d33b50e8a4420,0xa52648ff4f3d85369579f035024445d7cd22eb2b6b85963c4,-0x15b42591a45cae61c491dea700d5c6fd8a97977c3cbd13f2c0,0x283d27f3ddc39b497b389086dbe315fe0ff383eb93e4f0555c,-0x42261d5bc013f096feb0c31116356df57da8db2a2768291860,0x60d9b1d0ef4defbda461a0acef30dc3ae52c6e6572c4a7c774,-0x7ebdce5ff3f4d31ae749802ff0044ba6dd5e32eb23ef3b9a80,0x94a724333bff1bcb0eb984c8a09dadd0ffcf67045455a22adb,-0x9c97ee308711322a5d7c623f3203feeed31d529f1255c3a908,0x9460de03071f266e42d4981b5b735d71b2b4681352bf236bd1,-0x7e95cb8691635600552d6009d3f74b3faae68971bfabb4cef0,0x61470528cbf6e0eb018da3d502f15db98b697a73197d4ad96b,-0x435650574003dab37f4d8e37b76ccee7b10b21b33d68a465f8,0x29f78036f5bcdf65d78127a11835dc9273e763aa5a6452ee09,-0x1786ccafe2313ed144dcefa74349e5aa25b0ad38cdfacb70a0,0xbd8c4705ab8ee2493f01779814b735ef3610d69c7826b0e8f,-0x5591b85714fc38178019e015083e6db02d27dc49fc8085688,0x228c0bbdffa8720c99abd2417c48b5a289cb9a94ffd47035d,-0xc6fa102305023a91e6d77d50431d40ffbdc3da98e0c93dd0,0x3fa0e4d6e7b07b7d652631ad8e7c2373a095f60df5f9054f,-0x11fec5e223497e7def7a770ee3a817b8ce9dfd40bfa1f7b8,0x47a36c31d51fd8c1c7bb02ddf6b93038ad958a023f01a45,-0xf953f93e772dd4da10258fbbe53ed8e3942c9c2ec09e40,0x2f0fcea71ee994faba6947c34829cf5c0351c82d1252d1,-0x7a3ccc7c59a4642a7bacf3f04fe48b445dbed652a37d8,0x10e2834541a377e0ccb8f58b14af260d863791964d213,-0x1f58668b9cb64a9c14d02ae14d501b3304bace1cd890,0x301d14f6ad3c73d38091676e678af6ea219e26cd631,-0x3be2e1b3523dfe70929b3bd9a9bda4b3eddd5a4a28,0x3afc606f9b9070b1784a027f1e56b7d7f662a294b,-0x2c904ec2de80ee77e9df35f28dfd2c405a1791a0,0x18caacbeb3e10c502c2548faa6c6b5100c2d859,-0x99ce60001494ec3ddf7b98b1369a8618b8378,0x267d80b35e60c9b6a7011bede7631811c87b,-0x58d17b2964cad984064d11a8c48c013bf0,0x62b140c2236f2ea854294a95d07d68c9,-0x26428e8b52c41c22b2095ef3ef8848,0x2767fcbe6c4c073e700933ad363]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 24 62 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 62 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 57 indices rho q11 m11 11 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 57 indices rho q11 m11 11 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r12 : List ℤ := raw_ints% [-0x51e7726024cedf400ecabc7ca727000000000,-0x6ce8770afa02766c830b6df91ebd824000000,-0x44dbe30bce5b77e29e673e2ac2f7d82e00000,-0x1b8cd6cf1da7d5a8bccb7fac8078403e60000,-0x7d4a63e8e7637a082e0c848c350128b3c000,-0x1aec63b57a805773ba912d90e3c700016000,-0x48b68000baec2bbf5340fb9ec2783acb000,-0x9e355b6295e81d84d09367e08569151c00,-0x11a2f7beca0b28e2ecb2e9576f63791240,-0x1a19d0470d0f83ea3945772e5ce7ac180,-0x2050addf1626e2643c37f6d3624a7090,-0x21a586e15372d3c880d8c094251b700,-0x1d8a822a6504a16ad39e3cc4be73cc,-0x15e0e2a9f74f1f2e05df07cae5ad8,-0xda438dcd1ab958f2b2769da89cb,-0x720f9a69e0a3d9d9cef1e2e540,-0x3196581bd8973aa20a66d358c,-0x11bbed6439175d84fe75d7b0,-0x521e3ba3669267c5a56432,-0x12c598a649a4a14932200,-0x34434da3faa655df5b0,-0x683c1e77e246ba138,-0x84e6f1010c5602b,-0x51983d3841080]
def m12 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee40000000000000000000,0x8a6c8b0ed45b531ed1fe8b686e0ef9c39b73f36a70f00,-0x85e864473a32771155e55d4e3c47e579995740d13fa440,0x53d2c2d6d9e5a35858a53b016c51d95f5940861da6aec00,-0x262a9f9c40e53ee242738b437c66a74dd5c85e9bf4965b50,0xd78a7d13b45b5c32794010ab40e085263597e6002efeca80,-0x3d6037bdfb5e7ce3cfeb0fd255bf2c633b6fae40247276c90,0xe7d03cfdd40933525ab1fd0126169c4d0c73a1ac6b445aa00,-0x2e43026ae90cc497ab1db5d17265eab6f3fea8feea40a00b94,0x7eb90bf3c72d8d4da8e27fb12c5778297c47bfe7896d775ce0,-0x12d2b439e49ac157f8970dc06784ef67b54f893f6d9333eac54,0x2727f68e32b4a7031da5c43b909b77ea36d2f8389a635632880,-0x47cbb0dfbb8dc574fe7b45ac081174394d2e9e7d2d7f544e4b4,0x74aec22d023dc3d5740d6831a3c5850a149bfd5065c5a5164e0,-0xa8d4be1c167ac729a0782b673aa40dc4017274f342747fe0634,0xda410a627bb208a38e93bec9651b7e16a725801efb6864bc200,-0xfcc4ef81be46866142695138c49b97d370dfc4533ae257ff425,0x106ce23857337280be632c5e8d50a8186a1626b142065f017078,-0xf5a834f7e46f3fda205845f75392a7ec7b7951aa7d04a20cbc5,0xcea3c0dd37b9f3d6ce5f48507520db7ae479645c5290bac11a0,-0x9c7c341acd140cfaa4823877c151710b2febc69a29c08f0c809,0x6aae4204bbd8675f7578f9a37f74503d132a1c092cb30ecbd18,-0x416ffccdb05d1f4155208331be5a85649624943f73ec5c84c19,0x241475f93905aac1d32e0cab763992b58e55a290035e2ed2580,-0x11daef185f05c7b29908aaf76abe1d3128f99184faea9d0f139,0x7ea4f38107061d550b4939be31ebfca28f889316dab47e7998,-0x322a049d542143fbec9d5011f4a187822451510be0439ec419,0x11b30056aaf38c522d69223272585648205791248024a53320,-0x58a9f4b678736730b9f41e06b636f44bac01b468a3a90475d,0x1885b7d408e2c69ef37ed3c6bfaf6e20eda6034047d511ab8,-0x5f57ff30526774e6abb2edbea2bae82ebc9fd5f9745943ad,0x1439d263e8c0b6be45b0e6a1f22725cf4bbc783afa615200,-0x3b795afd7635b429c3d65dde5e170168d9e90fc8107c01f,0x9621d8f63b516a74718c93e99fe129e80cbd5a79dfed68,-0x141cf4a1b492107ad39c0b6bce3ff3889a4309ed2b6fbf,0x2420e13e5da287661cbbede0e69184b4a5a043d4e0be0,-0x3583adfd72a507025f53fb9407a43999f2b23a9e3a1b,0x4013f981ac9ee6c991f5a9b4f32b51559231093cfc8,-0x3c7f9a0e5bf18319ff326d372840704009e379008b,0x2ba09ddbbeee34359ad6fbe582a8abce306b7fc80,-0x170d3f5e91d22b898ed6e9b16d7ab489a58a7baf,0x87070eb3a156cc20f2be13ae9dbe313b2392a8,-0x1fae17d0d26103e0cbec5e3ac9e5ead20448f,0x43f62503bad77aa35ea5a09bd156ababae0,-0x45813615e5fbe58b3ce71d4c42b5889bb,0x18820537ff4767c72f843b9507c5308,-0x16a304ba6f0dae93e35d68e0282b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 24 64 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 64 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 57 indices rho q12 m12 12 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 57 indices rho q12 m12 12 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r13 : List ℤ := raw_ints% [0x1a40fe748592ffac8f1b876973bb1a880000000,0x22e08423de2268339648b56f74ef2e25c000000,0x160770e8b4ce6bcba2a9ab34843e86179c00000,0x8cdd02d98b5a0e35d679ca05570a2c00880000,0x27fd5c20a63eec9c9c21489f3d829f04c80000,0x894fcff6eff5add59265d9f2ae4e21683c000,0x1724f414302ef0904eab19b36a9a338bd8000,0x32473826c91e6f4ade53f1da6c1caa6ff000,0x5985e5ecd8891ceb37ae7fb7102da5c5c00,0x843c625d7846e6c82e569ae1a5bef6f5c0,0xa36073c248be0d6c41e637b3f16ab0880,0xa9b6a727ed161d698b9cf22df56fed70,0x949eeed0b1340352485e74a26341180,0x6dc0e2da9ec78e50fcf4b4a09b4834,0x44362cf7b7bb3dd4bda4d39c4ac28,0x238430bc624564f2fe29a8341035,0xf606f1a52f5a09a0ba4ef60a40,0x579275922cc4fe0cb08319a74,0x1934caf92e2480b52d891c50,0x5b9c39932fe50ef1698dce,0xfd29861cedff5eed2d80,0x1f4789b69f1a4d5b650,0x2775b2682d0fb29c8,0x17e9a4a710a55d5]
def m13 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc800000000000000000000,-0x112a4eb936802db950c7f0055efad03eafd30a79e3ad100,0x10783bfa65119938fef29f3a8e27671efe52f9b5d774e3c0,-0xa3928b0d4d203d101d81afb5dde6d352eb82639459b90e00,0x49d66047902102d414e22a8c0655fcc30ffeb5ea30d52e030,-0x19d4df032975c512789754e193aa5445eef32939b9fb47d780,0x749ef061c533cd2885fbf5000b5c593971bdeaaa7c6d9e1cd0,-0x1b45b8ff31da7e8269cfa1f4ad528c9bc3abaced8760b8c6700,0x563ea490b2e8636516f921b37799151beb665b34e8577c222ac,-0xe9e89686c0ad17b762d21014f33461673e3c73884d8619e2420,0x2263cc7e8548e081d932edafd8bcdc36540d8ef7cfeaacb1c6e4,-0x46c941d42c936d23ec0ab9733a27b6cf769c34f51dca7d64b5c0,0x80621d9aad70aabc962d47b687bbc2abd89cbc794206fdc22ebc,-0xce4f7d82a94325b1bd9330376cac92c1d505f5bc92df157cd260,0x1270ea7f9b029244adcea2b7dbd46f739f9b6642fa9f5f827f474,-0x178dbf09e9bf4493e393cfa1093d99e2d72c2057deb461ae4ac80,0x1af09db3fd81fe36fa213b8025d6048c88ed650dd8118b5a17b5b,-0x1ba62aa3d5cf3c58f734553a6095f3eeda4efb2006d0b154e9708,0x197ff536f48af2f024be6a2162bfd6af0d897505f659f28f14ff9,-0x1526f2dff0d0fe4b19d351cc2da1a723f8382cbc8a48893e438b0,0xfc97c4ed43a6002e44c29cd3ff2993097acf8d444e3ed93fcaa3,-0xa99cb7cb5be8ce8e0a766e14ef6bdd92b58a64df667b22a0a278,0x66689b86e42a25c246cab64036763c8b1e1668f6b24a9ab41789,-0x378a4a60be221bd273bd5cf9553e7d2d4959f4f828965fb68520,0x1b03d8c41b7bd4a6ae52bb73ddc28e045cfac859b3785107ff1f,-0xbc2ce7df2ea41c5b74c50b9f4170116d778ba24d2f29f584888,0x492201d89d2f95186152c3fbda62dc2b0867c4f7e1aae4c81f5,-0x194ac253df536e6fb9d5a67b05554ecb4ea846901abeb513910,0x7c0df1a7ec298cf2d802911abe6b28877cab77374dc1238ef7,-0x218dc277e6f34e9cb7131772cbde680eff6342294979155438,0x7f692c4e3f312b47488e95383b7057fe6ea4483cfa196f415,-0x1a5ba7480e4abd0997526ee97202e6b3e8ac47e757b986340,0x4b754114bb691f9b925ef15499ea882719381f8cb9d1fdb1,-0xb91aa693a7f7221ba64f368d7d3fa1b75707ed419e99dd8,0x180c31b98dcb64aa1ea78015b2624662a9a9f2266966eeb,-0x29c9d07719f3bc3efb6b94258cffb6c5a2596fd31330d0,0x3bb7a79bf68e9bd2963b03d167bb0a78a20afd68e2ab9,-0x44c4f42d35028b259142cd30df34bc927316f06ebfa8,0x3e3716326bd0077ec3c7eb007d1b360c125e6e8732b,-0x2acebdf89c87536ce1d1472fa46f2fb34f026c5220,0x15790a3f2c8ab513138449f85b889c62c12f7cae9,-0x76b2cd9f56141dd5d12d773c8efbba013867d78,0x1a1895f76a494c344165f9b3a5ac3476e06ac3,-0x34051c877ba7189252f3655934f63a6d4bb0,0x30f27ca87f51c414d88fcb7db42e87c701,-0xfb1f1763f1bad61c69575930126afc8,0xd003407011bbfdb5d73c306759b3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 24 66 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 66 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 57 indices rho q13 m13 13 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 57 indices rho q13 m13 13 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r14 : List ℤ := raw_ints% [-0x7b1b2bc9a2468d558f50cac96cabcf86c5000000,-0xa366601b2578701108e0f8402bc1a636a2180000,-0x671c5845b2c2775bd6415bcf65fa672ebfd18000,-0x292ab179e63e205950cb0dc3f89fcf9642591000,-0xbac8c60c3c90715390e3335b5ca7f80ef940c00,-0x28097ab1c09ce087093b6cc454d010577adfb00,-0x6bd56d1cef6e045aa06ec6f0f9322aecbb88c0,-0xe9ec4dfa34fe71814d4f7bf545c301fdb1a40,-0x19fdddd0d957a7bd1da50fb6f71d60da59bb0,-0x2653d126e157b91a2c7982e623b9ea527750,-0x2f43c9a0dc3a1a0271a44c3ab255f7abbe4,-0x30ff2ceca1c37fefb6e13ad5b827d6466c,-0x2acf33afe77067b2fc3d769b5dbb92e95,-0x1f88a406f05601af0fa58a4960255e58,-0x138af48ac5f623e5140636306bd3ab2,-0xa24af0b79db9095adf44aabb8cb9c,-0x46036d1dce43859f0eec21c61bf6,-0x18d1f3d5905cffbf9d89cbf17e0,-0x71c71c08044d818abb5054e94,-0x19b52e50f3a4ed21958f4fe4,-0x469b063471dd32e0c12c1d,-0x8a92be77f08876019fb8,-0xad52706afd04ae73be,-0x67f5608e6ee1cb94]
def m14 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb90000000000000000000000,0x22104c4baf2a95e837379b51db53f37974a8e44c291f4f00,-0x206c2b7a70c852f3f98987fb3240de2bedab686dc2da79440,0x13f5fd2e264394e0709230ea37ea85313aeca76197f3b48400,-0x8ef42b984abcd0c42206019e77527683bb1ea162ae28a9e150,0x3194296f196422afab964e21fc7456044662047c9af3cda6a80,-0xddd708c27e861df71ebb722f5ccd85d4990cdd6bcf85ff10110,0x33673a5cea3a0a64371c897fb2f140f4de6f4b47e9945fef5600,-0xa10593fc54338027cc74a0c15635cd8490f8b6628d0c08be0114,0x1b0787277dd00910124f29d2116b3ffd21bea998d7f9afcaf34e0,-0x3ef2138a5984d705cfef574d544f3469059a44923ec3f64031af4,0x80393a7571ef8bc66699584a66e209b048dba25e5cffc6dd9e780,-0xe61253fe4becc7e8c64b2c3e70ab4e84c9de591c7bfc8748592d4,0x16da3bd49e1582ec682d7a9bb6151318b2efde9390085c1e4f14e0,-0x204f303c04dcb44a9dfc0f0fde5066261ce00a80c49f3041af5b34,0x28c752ac37168b8e0414201444b38e15ed4af93e6745f002ae3600,-0x2e11bc0a0dcff7c4ea8813206f5a31795a2f710275e244565419a5,0x2eae37551b57009b0a2aec1de3b30710cf7f5f0844d1239fa39478,-0x2a7ba9cf5788fb3605a1224265763cae151fd3b801dd55b8c6e14d,0x22c16e131f4305eda72a1a23bcae4f418165fc1679e65673efce60,-0x1991acfb2c48dcb10383b753bd48ac402303809c9db9573bb4ea31,0x10e9c8c276c4436746ccccca69a17aa342547e128363f19bcb5918,-0xa0d8d92aae361653f42727e95c8cb7205de517c27c828bbc54099,0x55d074c2d232f82cc89625f7be9de33b7d03933d7e94cd2b2d080,-0x290785b9d5b16818fc026ced0da3885bb73278dde4109f8684729,0x118afdedd325c51fb977c10d5820c235ea624f8f4346aecbc0618,-0x6b09e4e114722f04403ae40856436a1f6fdd642132f913d95311,0x24494520dd7894fce795ed03523edfeeed6b77a8a02c71aebae0,-0xae44a42b9491c5bfb5ce031426605aa44ee3c347efdf59ce515,0x2e188d94f1f02efbdbd02559f66e1b6c8d2df381dbb92edb438,-0xaaf1bc28787a8de33fba01656ee89fbeab4bd02d5ab92a39fd,0x227c360477a172fe480fa4f10eac5802b89cdfaf9632ea9a00,-0x601bf18dab4cedfa2e55a6035d044eb0574af580c99d3953f,0xe5151e2bd6cb541d8aca87cd8949532fac8bb0515741f668,-0x1cdb1dcaf4ed57018244cde8be1fc4cd433594789e9a14b7,0x30802c1580755e40bf047a1d94a5c0b8d9df9a0ef907820,-0x42da22f59f5c25c8ea2f23f11787ae540b9c4aca0141b3,0x4a04b076efb0cf9203dab83dd3f405adcc887e43f46c8,-0x4024f5373230a5e1cffcb4113205eb8b0e3ef04e316b,0x2a180fdacba6c212e6abf85b923b35a6438f108c980,-0x14094ec16c41deee8f1e3292a970311e12f2b1469f,0x68790f27ca2ee50c4a7da4abfbbc901c842e2928,-0x1583252cff47e403315e8bff478ad6b09d4f577,0x27d453fa279ced86d9d7eccf36aafd73ed320,-0x2277ceb69c5510418b2e12a9c816141fd23,0xa0c84a7559474a10b882827058ffee88,-0x7770c3a7e9b1f15d9b251d0a449fb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 24 68 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 68 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 57 indices rho q14 m14 14 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 57 indices rho q14 m14 14 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r15 : List ℤ := raw_ints% [0x21731cdeb1fe9f36466af9af51b0009d9b54000000,0x2c5cedbef7ebaf36a4dd590c584e5518b891600000,0x1bf87b3a2083822874c8c654a362618749760e0000,0xb282b593f90e7d9d852aa6d6cc2b96120ba06c000,0x329235df9598edfff750161f008cbc652233e2000,0xad3fea61e0472bc5e0a1feeffd331bad3833a000,0x1d2123f1bfdb5560802e1df47b46eaf5c39b9800,0x3f1bf4ecb5aeb383ffd5267f9ad44c7e77c3040,0x7009b2dbfc9ecdfe74b9358743cb943be91080,0xa4f55fa84cad70e6236844599894b7c5c7590,0xcb1540f9a64a41f7dd6ed1e20eb82513a440,0xd2230024a624cca55df623744c86624fecc,0xb73a2ed18d9039a0da0032372989b2b9e8,0x86a9df4e072b84522887a08733e0c0ecb,0x533fa4931335cbec4402320b471b18c0,0x2b16a59c718026cee8deedd0b8be15e,0x1287d64e1c12516c8ef91f171df0d0,0x68bd3ea6b27690ec7f53fc2d548a,0x1de3b31399caac83b7e80ede640,0x6b911925c60dd224051520b3c,0x125e5a7f69f43dcf35f65388,0x23d59d303c62fa4898fec3,0x2c817c6125712298b600,0x1a792526c01544ccb2]
def m15 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb39577200000000000000000000000,-0x439c3b5c4e86fd144064317d7f8ea7bb52073a538faca9100,0x3fd9f10821e9adc813896971a6a11a68e2340efbde2a4af3c0,-0x26fec171b83b78d3337eeb21e55e42763f048a3875a5fd2c600,0x114f8b1974b826fd1a2100ffd8594a0f58012c151cb27b478630,-0x5f3e9d421fc37337212ac6972cbcf80e5a26691b65b6674b0780,0x1a6749d245431c1fd0fdc4048606b96b71690d2ff64629bc65b50,-0x610265ecdaabdd38737b5008be3c77d3c1ea9920092445cd49300,0x12d1241635bceab7661f3509c17ee307a7fe3e31cdf86e8bdf7b2c,-0x320e51f0e8071f6adea7b82b3ec29e0ea64abece28ccb1564c0420,0x736bc48e2308c35fdf5200bea8c43be567df34465488d0c7b11304,-0xe8b9e99912d8b98e3f2313a74b21b503018172555a3fe9242190c0,0x19d3056dec0138afdbbb772b62a8b892d467674461534ee3c08b91c,-0x2898337d94cb0efe879dd14597d2779126350f70fd99fbfb1eeec60,0x38bf32c25bc91784f08d35e54c11135312f1de89330fd9fefc2c374,-0x46c9290bbd143e71300fec69c0ba832c5a9f5bdab689b7bb4b2ee80,0x4f00478bd5e92bcddb94a88881f4d2327489cfd263d602c827029db,-0x4f0ae496e9771118b4e98dd5ae1d17931973470668200da6308a508,0x46fea0d040256c96ac128c77b51afea5bff66846b9bd575354fbb61,-0x394a6ee0ca1b35be23a3d4831fb10344a6776445ccec4e751be7070,0x298cd7c0dd4ce474536e55c94c89399685b2df6efa2c4208539051b,-0x1b13e45282ccd736176b567918226fa655ac10806c72cfba78696f8,0xfd884b52d9d5fc081018110a3b470fbda4abc0181d3716f19ead89,-0x8513580b156e2362a18cbfafc956bc17c81cd0e959e89362c645a0,0x3e8c1f4adc6af95b60253f7525edc2387d6965c868c0889a53ab2f,-0x1a44780e4007a248be19ea042200d163f58c2d4f6acd3aae4a7a88,0x9d458e96f3d4ee4c0f72850d1d8657ae78661b02990798d4c124d,-0x34437d8bbe73d02c511b4086f8d10f275b1085735d239a8770650,0xf5c5cb729ee80610e308757d156624840a4057ab164ce15a685f,-0x3f9380efaea2ad63f9c4b9695b17556265c43ecf195be91988b8,0xe640909f4aae19a7b7a7ae9c178e20b292e4ac40d1dfd8c75e5,-0x2d4b09f22bf6cc5624f869b2b69d33ab83009a5016bcae4c040,0x7ae065198f60937bfea614194ef72b2ebe6799d6e3c5017b91,-0x11c8d909cb491438e95f64a556cc2684bc52ee894f3978e3d8,0x22bf6dde4e51c00143fca6fc8547578d2010a60c6bce2fe83,-0x387a9187f54fcebf07de1a5ff94339f50c8c18d4afa73b10,0x4b120e1279627c09c95511b6f2336fd02a27a1407831801,-0x4fe414e877056bec8c19d23a00764c809cb03e1d461d28,0x424bb86fd905ea08a5cb2b8a8902080a4ace2d5dccf8b,-0x297a4473fbcdcc11ab24feebb6e362805545efe17ea0,0x12b9ef6b72c51582ad8fc938e690556fad86d6544f9,-0x5c0edd9e30cee99c112b82d4b2c480eeb314e3778,0x11bee6ad33e2c6ac1700d86fceeb4f1f7b7b504b,-0x1e80d4280698130d8f4f44678f53cc311af170,0x18452361d8a6cc785876e419ab0cbc7bea79,-0x66eaf0200492284f7befd12db8daeff48,0x44916c77dfc4cb9d7cf57eb58c0b03]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 24 70 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 70 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 57 indices rho q15 m15 15 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 57 indices rho q15 m15 15 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r16 : List ℤ := raw_ints% [-0x8849cc091141215dc51a7fddb6bb6312c0812000000,-0xb49f651d0d86e5db9ef2344cc912d43250115f00000,-0x71cad3eeed39e05f1c6133c7311bd64db97d01f0000,-0x2d59d8d9afefebe7de776ce65567170c8dc805aa000,-0xcd5ff24b12bbb1f78f9556d75f8aa37005bb3c3800,-0x2bee328ddd6bee475a6fe519a9999a5d0bffc14e00,-0x760da51026495d6e2b0d6b452e5b5025e6b1edf80,-0xff76ef2a9c99759e6df7f1e9241f9826244f6680,-0x1c4f33e0c1418b8255a922f8d75c883facc7fea0,-0x299f99a9c75e5ab5443299695e3001afb5996a0,-0x332a6b745f10b0723020c8b460bf0d6d16ca58,-0x34dae65bf88977dacf71346a901c22de31f78,-0x2e00b33fecb0746ef728b46ac563e27f75c6,-0x21bdfa9aa6a81746d988f1472327906c188,-0x14d024fd3bf967f93e80132c3e20126771,-0xabf0226e4b08eea00e084e2ba28a4068,-0x49bdc9389009c21a0199def273e25f0,-0x19f870184df3934dc257030d024070,-0x762bcb0ecbf4ea5c9ada75a36cc6,-0x1a79f1cb87561eb795c63676148,-0x4804dd4319bf3432cb02b8d92,-0x8bc8fdff3a3daf51e3f81a8,-0xac97762efa6fa6ebb0209,-0x65f570553b7bda0b018]
def m16 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee4000000000000000000000000,0x863802162e6e7f9be7930900f45c64faeeee0101e65e878f00,-0x7dca9b4e21c2e97e6eab34f01da06d9448fdc7c181239138440,0x4c38b6ff21e6c93811374be727c34ad367fbc77a83b3c1badc00,-0x21904cc441ed121d8a04a6a8fa206322f0a7d0b1f5ce24d313750,0xb723448cc9e2823ff7ccd86af2f54ce30f360a35634aab2618a80,-0x3255d4c812c16aabe89909fa42300dfd4a346149707a412c617990,0xb74f1e451cf64bcadd2f04e0e05bd8179cd92ea5a82ba1d5566200,-0x233bcdeff0bd54b50a4526eb38315d04170f3276aeecb36eeb1d294,0x5cd91c1189c64f4b20fbd5c256a861976d514778be6ba9912e24ce0,-0xd405137b562ec49c4ed1de949fd3851aa37bd5d07c316d6b8212e94,0x1a738e7c50abb2ee402bc062a0cb89608e40dd04d718cccfcdba9e80,-0x2e79f07c53bd9f25fd7019223c38405346ff254169173e237048f3f4,0x48467c2627e40c9e77ca45c8420fbc9a8f7aa2d343c42e2f98fdf4e0,-0x63e932cd06572ed3538a4fb7c73a0d0bb2f635fab35d3a2147acb234,0x7b3143940655f79293a03f71329058d1d66be7d0bd5831dc17f5ca00,-0x87d85f33118db30b1d5da3437515286656940ba6dfb70c621933b125,0x863a005f852ad02c4df33e8d62a292a75ad5910524c2988baaa66878,-0x770013de8348b904e1fd373d16b4110114ff68a98a8d711982846115,0x5ebc649f4e9d5b17081ed66f5e5066d81c30ba86f22871ee1ce37120,-0x43bdd90153a2b2cebfea889280774565cf9cd8d6032d0c091ef0c019,0x2b7f908db5999008d6e6852ac5d03d59b52cbc01f1aa396ad1a9d118,-0x1910749973de4b720d1cef2b469075885259eebccf4d091659d08199,0xcf1c118a5d1ae5110f52b76827cfcf363475fc22f059b1f5e0ab380,-0x5fb3d06516ea48d4e14b60749b380c2417b17c40f6637f824f03d99,0x277a965f16db09163efab867ca2b10f7ae4b73f99434a67cc039e98,-0xe7f61dec1267a1600978e8794d9ba3ed9d94ca8b115cadb526d2c9,0x4b9109fb0901ce5ae14096689fa1bf6b8e186b7e1b501e204ea0a0,-0x15bf5d8e80a43d20f430584e4688947452215c01f54a0aa9a6700d,0x58066c27ae56f0dab316225917233f4eb44a066c124ecc6947db8,-0x137549bfa035e2185b16352360523274e8471d11d50a466c9a84d,0x3bb6d294adb80cfc6b69089d7b09404581273cb7aedf2b936200,-0x9dae9bd180a53531ffada456321009457de9c8199de7169b75f,0x162b9ae9955ddc87dd671a673b1becc842fc063e48769814768,-0x29fc85f159ac8889b42e89c398ede744cd75c6e2809e7a7d6f,0x41fb70819e39bbbbca434358b2274d8b7cac202f313498660,-0x548d33b65490eb5f984bdec087d20408723d050b691a578b,0x5676551284df358f40fb90ef018778091011d2d535539c8,-0x44ae440d3a25a078724f8e2a1f9d6fecc9154800ad6ccb,0x28f35213ce2b650049fadfd5e1835adb739d8d7025e80,-0x118758329f802f0ae7a11492be2a15127cd110a66e0f,0x5134996e627b7203e03b322c3822dc0b5562873ba8,-0xea5cc8be7bbadbb3f022b9e7ae1bbe97a0313a9f,0x175da0de16a98373f7ccdc6c7bd5cfa0de24d60,-0x11167a50e0ab529094531f0b6074e40eba64b,0x41dcd8a43bf3678d29df89ae7a45309208,-0x275af179d8f034d595b8b19f0215ecb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 24 72 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 72 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 57 indices rho q16 m16 16 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 57 indices rho q16 m16 16 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r17 : List ℤ := raw_ints% [0x20ce644197656fbf808163d8e749c9163b6ac98000000,0x2b72ea4599367bf0e95faa839f5de118c38d2b7400000,0x1b5a60205d442b7c139402ef27223b7fb31f79d240000,0xae4900a956dfa9307dc0287ca923bbfdf1a5e5148000,0x31498ee0dbf5421e62503121ba1df1881fae71f20000,0xa887d1e882943ea6289e5c68815a5e8ef43c2013000,0x1c47139441d0a0ea25b60db5dc0a4b9f0ff90353c00,0x3d2079e519f62afca29d66253559187455223ebe80,0x6c4150243c41934aa786f945ae6a6951290381000,0x9ef7b6903d689c8ce51a15b7dd402dea3d71d2e0,0xc324a83b36d619c0924e17a963e4b0928d10340,0xc948cec80158ce14a17e96f6ca8d52a6e0b348,0xaee6e20a1af887a235d9fce68b17d57569320,0x800e6ae091697f08500ebefaccf6af4c757a,0x4ed51096103e666641d5cdd095b7b3505c8,0x289d088144b3e2409066a3615bd250f96f,0x11604f2d06f3afe8de0efb2c32f987f80,0x61a653157b2735d5ba865681ec8c110,0x1bafccb1c1321760b80fefcc0c5550,0x62ea6a1c148abc9d0d25a604f49a,0x10c089d3b6cdade83c9196a80a0,0x205f9d98c9115af2e4ae39aae,0x27c5aca27f91bf7db9de268,0x175c3db4d3e2602176c17]
def m17 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc80000000000000000000000000,-0x10a7f2231a68801c7664eb3ad73e303a62eed21f3ae5726a5100,0xf7e8071e31e3b17d185d6e9f4f721fd450866b22bf41f55d03c0,-0x9510d63f8370c1c17f60bdf30d252e3ac61fe26dde9c2901e3e00,0x411f7837fd8873a325c8c81b1519ae000c69fa4dfd7fbd615cbc30,-0x160742f8494481ae4b472286121a52df26ef5e4b3b1a08eb1bb3780,0x600f9adc5a76ae11e9ce3519f1d237f8e345cffa2cbcdf89cf98dd0,-0x15acf9a46a1d703051cb1e61a36010d088963af2ef24267c1eb51f00,0x4210eaa5fa91c929bb385a568bbd898b82e62a0344d08b67458287ac,-0xac7ee20ec4d4674edc1692fed914b088dd899df61891129f69a36420,0x18625e1933e4274d86113f6e03f8d0ed8daa68f2772c77d6be8575024,-0x3032023dba0da50edcb682ca4c1c2a5f7f3f427e102206621114943c0,0x53d182cb27b34a89e474e07c4b5bd0cc1aaf8065524604a1870810c7c,-0x80f82a44cb465cc067f35e808a48f2db36b1474c3ed35ac2651d46660,0xb0547c8b693c27d99f4c6b98580ed486e0be4f3f66495f8a21de7e474,-0xd6f25318e44685ed3f20331fc0c61f9115ca7714fc9301d1e02136080,0xea38eb7ed8e4c49690d665bd7ed62a58d75835a324ac44631e27d465b,-0xe4962f547e24afbbd0655c728d6d1cb700c58f6bf47596e3d04bcb308,0xc80fe85c9b41dd1550f9ea0332cf327dbe64d10df67ad66e5d4f2f809,-0x9d24aa7fe4d0c1be07befd6e13396a7c7fd57ee281299025908656630,0x6eccf77b6a5f38f294a3dbffdffef91950799d0050b291375a68f86d3,-0x461c7038701d9aac5bf9a0a2f1ff9ed64ae5f6ce19da13c44fffa8378,0x27c86c457d17c8a49d729bc1dea5a03d68d63b595ca952c3506f9dc09,-0x14379fbd00dc7d1d3c4622b772f0695ddabdb086f29d9053b31bb7220,0x92f6f10b3c763ed3e03b4a92cee8e4cbd07d7d73a5c9d196914896bf,-0x3b8e090531e4e217f4057ecc182a7ac2ddca824344e4c9e9de3cac88,0x157685334c3266f0c3cd5899414ceefe5be8d5a571e2ab53b6cf7265,-0x6dac95ff6e0ce7f404b9c76ca53d94c7bc847390aea188fa2695590,0x1ee83608fee37dea7f3932d6caed491ced8cb7d9466060988b7db87,-0x7a5704ad8e866e8c83e0393b67535ed5b0acd2363a076f84d07538,0x1a68c6181f6c868281863e07af5fd1e81e09d11640b329542f27b5,-0x4f04fefa25f13317922bb1a825853bf219a581fb430078de9b540,0xcb14c3e4764913147991f6eb90dfd10d9d93203849f43cc2b471,-0x1bbc0f7b9bb7b89e43e66e09287fd53eec6e9c45ae6e4e8969d8,0x32e71ff1d3f6fb2baca7563d9bf227041ea6458fa6e499946db,-0x4d53ba3abbc4ca974b4cf6c42d44faa62bbf6fd968b0484750,0x5f817efcdb3375496ffc7e4babb9f878e746e0b1a41593009,-0x5dd140cc70892159f35d01905dcb20150868d32c338f62a8,0x474fe1f73cf6d5d23f41a5777644f0c08e41fde7fe22a6b,-0x28816b2fe3954c9acee94b6e49bd3ded407b4d11465720,0x106e6a9436d222ad38f52ff142fda1b666387ba75aa89,-0x47b41e1df6982b215b9ccf5d9c8d9fb052012e73178,0xc18e34a62ca15d0eb434675576a6c3475ff106313,-0x11e6c73887aa9f24132b7c7c9cfa764035cd7d30,0xc079c1c8c94313f2a3c4a04b53c6b5986a131,-0x2a23a572fb964fff0449ef7e32bb79e56c8,0x16956f5a6735476727f76f71236d3753]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 24 74 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 74 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 57 indices rho q17 m17 17 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 57 indices rho q17 m17 17 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r18 : List ℤ := raw_ints% [-0x784335fba8e666646f75fa7f96ad5d064a8c7367000000,-0x9f2d9b61169780ac15603c6bf92cac5d8d762223880000,-0x6424954db2011f6d4f8a29d5c362e03ba6721690088000,-0x27d9f0226bfe47a3c3f3039b034b290208649f81e2b000,-0xb42d7524e2c60c14fbd1e6685d05162a98b157e524400,-0x26793009483acda2c332d1a3cdea9a843cfa203dad900,-0x6731872f0903f445d921ef7c35e5867612c235039440,-0xdeda12613ae1f7b235c461385b0b574f481584350c0,-0x18a402a3bca800a08a50f02804b3772e79f5e923310,-0x24246093739554477064f1d84c1f6dd8a36aa4e370,-0x2c4fb7df26800d5d83043e7346e1b6cb829b6edec,-0x2da4ccf6b954f48a682bf024b750734b2e629d24,-0x279a33771788c5fd6bca620204bc1415f3a25df,-0x1cf2bfbae8e5a6af49795071cbff35d07b13a8,-0x11c9fc2ab055f4e81577765f596ec4ca1ad88,-0x92590418c5fbf68c94263f552f494c4e464,-0x3e7a8ea2bf9bcc8e6f0bf1fd8d99c9907a,-0x15e461e601ba8646dbe916b601370dde0,-0x630c9b81de3de015e66d82cd7fb93c8,-0x160d1b26f65e40103940f2bc6caaac,-0x3b8d9bb758bc9780f34e6b19408f,-0x72a7371cf09561257acdff2b48,-0x8c40dfaa88bb1444a0b12e8c,-0x51f99f507a55142965d9cc]
def m18 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb9000000000000000000000000000,0x2113b8e8d8bcb5885017c20974567d711faeb71c821c8dadfcf00,-0x1e8bd3c39004d01a771ae0b248ee9cb44c1d688c7820841e437440,0x123ae2caa806e6514ef6929841629b21997d81e2d5b4d4e50e3f400,-0x7e720c17708453a93788b10927640a0e340fdf2b517960011e6dd50,0x2a6e6f035b03e9c4db12c6558c3fb7d2d71a28fa0a2435fc6ef82a80,-0xb7846dbf61207b5945ff394077ed1dad30b896a95c25ee662723f610,0x290f30d697e60a3e7737751e545aa99527785c7ad0ced93f8a131ce00,-0x7c0d56e5fa5c611d6178a8aad5bfba705b16cf6d3b2e054fa11512014,0x140f79d2ad5a115d3d0697625c7bdbace72052ba902b309067906da4e0,-0x2cf2bb45ec2af8ef3dedbed2a2f2619ec95bf9dbfae78d1a27e2f9cf34,0x57fad158b8874e66592cf1001d7e9e8800f823254813af6b85abdd0d80,-0x97795a7ba1edd4ccb1f172725204550968eeda56116870c29c526ed014,0xe6a503907ff6cc01ba76b373e00534b8c1cbc85db1c4cf9c1a60ad04e0,-0x137efdc2937a31af59eef8c5754784800a204b3c7bad8e587cb339a3b34,0x177fc01e2af601b4b16440d45c1af32a61946470a6176aaabfee7a7fe00,-0x194eb61663457bc424099e3d45765eda57748b513c6326349b48f62aaa5,0x1865fbb1650cab1662d34aab3b764dc6af96d731f6a9116ee8a06472c78,-0x15155147140a5b98dbf24f791738010a82770d328c54837c3e3e2a5ed1d,0x105764b2898c98c1da8c5acdaaf6e49a92003391abdfd3a76541e8829e0,-0xb5ceee26c9493faec27fb9b41fab91b0741e5279eacb7a8dc2566163c1,0x716125ee5eef0682143f8672c646f0a1ded9a05e154ad8bf4b0da4e518,-0x3f5c2e2b00d6cce3c72d488978629a13adb1b17723b19c85ac96df1b19,0x1fafe8dcf5ba2b70ff9946b9dc7fc2d0a42679cfbc2b1cf19978372e80,-0xe27e49e3c6134d3c73e48746d69b25bcf99edf3109d83f1e3e74c5089,0x5a2aea5763bfbe6c33970d6feac3ce446a6184b09ef2f3fb628028318,-0x1fe4749f363b84f20a1e12829435e7414a875fc052a980116c4ee5941,0x9fc544c354ab003529147ddfc22ef97dc3a7e9403bc07036265b3460,-0x2c16c56dd94317097b8173d99e10796e212cc55eafc9867e050a1645,0xaaaacb20c86498075056123c04515467bd2add60b86b142dfa83738,-0x23f9f0e9b27cc7646cd731dfb217ab5f97cb6b93535fbac8f42169d,0x68f279c2207a208f6fb4a8e347a2148ecda2929aff8c5978146a00,-0x1067adec8ce050e83a5b406f8923459ab9b6bce8b8123e427c7e7f,0x22d06fc7a5741bfb4316c9fc033d43a37a7a6ee041930c41fa068,-0x3de9f5e6523c71bc487305fb74388560712c4976977fca46f7e7,0x5ae632cc0c33221f3cb2c49695ddd697a3c8b1de3c8771106a0,-0x6c2e7cd45313d9bda7016dc17e9db8e67bfbdca0e9ec2671a3,0x660d9ed83aa2575e7f81dad631bc1ea05c0eb58002d91e8c8,-0x4a34458e9e51c97b0965ffeeb9c7c8e49a72c1f680dc3eab,0x2822f68438e3b18747306bf392231d6f5c29cb2dccf1b80,-0xf6c6cd3de235c34321e4c2de3140b91399a186f96cdff,0x3f5f3aaf0e73eb74d6bbb3f840448f1f8c08fc458a28,-0x9fef3b6a4900abf68c92b4402f6070800fb705e607,0xdb78ed84631ab5ac2c460460e8439bc2659619a0,-0x877c66a7e1f2c1ec2b74d17837b70e4187bf33,0x1af460c1be98e88e2e57813205c2633f7d88,-0xcf4fa8ffb015cd48de0acd22c8a3369b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 24 76 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 76 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 57 indices rho q18 m18 18 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 57 indices rho q18 m18 18 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r19 : List ℤ := raw_ints% [0x1a6053f4961c5485449f1d442d2e74cd275855ec0c000000,0x22e42a4df34a3a079423397a2884b35831254b7dffa00000,0x15eff86aa4622dbddb24330789a96fb45243daf59a220000,0x8b95b96c18204e46b98aca8cb3aa2e1dff2af99e0fd4000,0x276a52ebfc4c744824c6c0856c6610a0b1958b9bf84a000,0x868ed91754b2ce4538724d2321e3fc68c85ae90ec6b000,0x1689c8dd20f4fa7e4e4f3d817dfa5e885c504eea9a7c00,0x30a0f604065bf2f480a7dfaa69765b9476d6700a96ac0,0x55f2401fe92c6fb85c2b750b3375c3f6c68d94010e80,0x7dee36def22f20b782663ebd955a610016871f751b0,0x9a3807a521b4d40634cbab77a097be46020c8e4c80,0x9ea8bc21d12a63730cb5b5c3f81675fdd61adf9e4,0x897931f2c7775b659881ba3f0c1651d2ce6d41e8,0x6457710280a40451f1350654380bfe3a5efa1c1,0x3d8fd5a4e33714b6e9070415bf35cbd84d5880,0x1f9918eaac09b41656492f2669b453691bde8,0xd76b4bbfc6430e51af70ea8d3f8d14c79d0,0x4b51f224b2a69cd01deef8250a927abb06,0x153f96449dde1459bf17e58e250ac0300,0x4b7d31ee6fbe6fdc4107ad43c2d0be8,0xcb45fbc6de86bb4103f4b40ec1488,0x1860f0d04007867cde63da83ed91,0x1db61999b3ba6f6a24d5fd7d40,0x114ade8422606e7aef0d6584]
def m19 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb3957720000000000000000000000000000,-0x41b2ddcccf121a5a70967c813803930b2d6282c73c1752811a1100,0x3c3ddde4d11666df5948bb607998dbf54d679984464f1ddda2b13c0,-0x23b089d1c7adbd6e87a0b22b1435c4c228edab6d8d90aeeac1397600,0xf5ae81d19c55f4195fb9c44c76ba97b45ba3f4ec48fed39d21730230,-0x51cd6e9debc4a80e565839b90ef3ad97e1af42d44beaaedec29646780,0x15ef55118648159532e40b2558a59ef889b30f6a6e9dd71a25e1dd5450,-0x4dded96b97e9381089548258b443145902dfd7196500b9d25ff1850b00,0xe940678fa5ded6628ebbba916234f8127e968e59afad23781f344b282c,-0x256267fb3860df4249980b6ffb3d90af2d29bb3bfa8c06de084fac84420,0x52fec775fe35a7ceb87014f471df78d4dcf75d10fccd81dc4b18562c644,-0xa0e7a85ce8075e53ccb0d5f2bb1b15caf68a2493b958c09346193fa8ec0,0x1124b15a73851506922057fe1c92494e106d1f13b08409e816e4194680dc,-0x19d606fc36ccc042189cc0dcf9c04cd62e71505b89c796d7fd822fc7c060,0x2291eea179fe79898304b183c186c3f4e92f8617c2592c65e3d090108774,-0x2934e17edddd20fb64b6d56d02555f542528b27d751649664233e13b0280,0x2bddb8840685428009b8a2beb260bc57b4ecde32be0bfef4f165171b60db,-0x29c83e0c3b958c82acd0c34f7be651361081fa3b25e206c080978a2bc108,0x23a7076914c064caf98f59f8aff325a618211f3fe26a9acb03baa1db1ff1,-0x1b459a5ae113bdce486881368a22863435b9b69f04e5485b4bf20ddd09f0,0x12b42d95663ff2c40086c1fa9a6362f8a7576eeab5fe4511d8cb46991dcb,-0xb7f2b8521cf7274e5a58fc445d81479f4893c5092334446b753292a87f8,0x653fcfbb40eac01fdb839ea58840cd8330742ccfbf72e30d4ee75a52f09,-0x31d5e85edab3d1addd21125a162a3bf61d7a9b959a659c735225c28caa0,0x15e4a39abffd7ecd5ede9f0e02d30bfa3a6a6e3af703ba3c5145d2225cf,-0x8901b6b87c40b0ed27736f5ad338153bf93e9c6e27db5d07b93f56be88,0x2f8ff395799c6e8368b20df60bd5047190f8d2a30f494380763353503d,-0xe99ab0ba5b604a666d458e470c285df5297cb91992130756d70a4d6d0,0x3f1fdcc24e8b63cc509fb3dfe2b5e3c7d77b73fb588a5015e560ca26f,-0xeef56ac141ec7cefe93a51be1db59c4a27b9aafe47ecfcef61f0d9b8,0x312feec6e447e3d898a34223f58207ace5cab8e445d2e02d7b065185,-0x8be1285c16eb20298a357ca16c95352d1cc74af0b46805eaa1f4240,0x1546e286e4306f6aea64b9e66430f63ba239b645d704c2f22b85051,-0x2bd8d420c70fbdd4815ba5884117ead06289946da609d71f69efd8,0x4b8bb964f91b4c3e914498eca67ee496e191baccf40808219bdf3,-0x6b2b8c08a0deed1be6c83d0944c81c4f38a7028d0014a6e3a590,0x7adf27737686f5f6ac7b87910a4119f63df8cd391083cabb4d1,-0x6f47948304dcc27e14e086105c478a92b7a26ba303b26c3028,0x4d5f905006ca58ff509010030492b984c273ed981317acfcb,-0x27d6885525e6cc446daaea837c790596629aaa50e06c1ba0,0xe7efbd6512985b9cf22e932e65256d11c7e06e7b533f99,-0x380e6dd8540f00165fb4111c2839d2b9f1a2cb173cb78,0x8436a9d92f03656129fc3c3b4e4f3184470b914dd1b,-0xa8308f72e8c5a99e71eaf0c804f66b7ea0df23ef0,0x5f5ba6ec139c99c5db85516b3f688fd49cf8929,-0x113cd890f4127fefa0a824137c55e1109b648,0x76eadba6746fa4707f0f3f72357922ea3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 24 78 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 78 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 57 indices rho q19 m19 19 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 57 indices rho q19 m19 19 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r20 : List ℤ := raw_ints% [-0x59063609eabbb31b7d11e3b8f80f51b6b0222d4c244000000,-0x75b36759dec965b99407eba240fa9d3b9fd171ac91ee00000,-0x49f5cf76ea489b67641f33a7009c63a4a8f15cebf26ce0000,-0x1d64f2bf74494083c992af432ac095c3e9448dbf556094000,-0x84b7360e48b7437d24a79b4a0650215aa9a3e03117943000,-0x1c4bf7b4b7cb96d0802b10dba4c72c23a9145509e4001c00,-0x4bc6b3ce3c73b3e9d2f78f92925713431932e05940c0700,-0xa35c36427d8b5461ebeb79d46a0ebbf28b544c28bca900,-0x12076d0b14fefa611b3877b5e28135d9f153b1b276d100,-0x1a6418fba61378f74b58fa00b158c2916e78c14bcc1c0,-0x20491a114374dc67e617cffee94034e7586f0ff840a0,-0x212d6ff37158feccbd762a7d2196d11445ea49cb270,-0x1cb642ac3b2440d49800ee46298a44d9e2f8fea960,-0x14edc3502da164ed141944e7a6076cf608ac9e3f8,-0xcd25112cc9bd54b9b06e6a6ad3e7c0fa7e2fc77,-0x6920a2d21ecd41efdb466f110ab0d1f3a5a050,-0x2cb742411879a2f7e41b3b401f3394ae5c494,-0xf9acabbf2ce03c073db960f1bbc99609cb0,-0x464941c77dfd6c3f1392887078e4abc49a,-0xf91effb0c85036414dc9c03386a06890,-0x29d141503b312094618c7ffb1a17194,-0x5002a20e03773bafbd4d247e140d8,-0x6131eea06dab85394958720f6c7,-0x385ca0c3e56e4ea1e97c19c70]
def m20 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee400000000000000000000000000000,0x8283dcd0277c0853e4f47a5829beece5a7eedd62046d2fda2280f00,-0x76d890fdda23ac81546a9905818dd1503a982379ffa781e70b376440,0x45e8109074a16e3c3949dee70b4da7a644e766fa6422a715c2cf5cc00,-0x1ddae11e94afba7432c532cd158d88d53e789051f97462080449395350,0x9dd6bc771c901efa4c405af3a800d39d5b3606f14b13d4891b81ee4a80,-0x29fdaabbaf4b3d0b13e70dd352f6c8a0abea4edca6e648e2366a52c9690,0x93dbe3974aabed440dc8f71599c0fb090436b7099dea479f6e1e0a09a00,-0x1b72af89bc940f67f6c82a746d456da01ef4fe90cc5d7546ace4e9308994,0x45c646f0a34d78900bd22ec42e650c1bb7e2bf8cb32f6add21b2171d3ce0,-0x99813039a59dd6e4b4d9291652820f48327cf2e1f8674590829a3b7724d4,0x126d12bfdcdd65dfa2cf08a01d4b0862c4479606391815cce818bdae2f480,-0x1f1b032cb3cbb7ebe6a1e4441021d00bd01c725b5c6ed88ad665aa235af34,0x2e67945e221ce521b7d0117969c0abcdf6779e9a01b1e42af03f2101a44e0,-0x3d70a2f448ae7abefb6d93eddf88f2442dbf8db6aa269221b683835b5a634,0x486f359184a69cb13536ef073945fc45f143fefd838019ca83501450a5200,-0x4c3b3565c6b97ef63a876d33fe53ab91cff89e49f1d5c28b5aab7bb3d7625,0x47bf4c86048d9747582e92b8897328259506fdbdcaea95c2cdb59bddae078,-0x3c763e760d1c5710ec694d5e7d1c2a064b8b2422248b2cb2fbcfa071fb765,0x2da64a224d229e3a3f69bea63624cf16307041281d04aceb350c644f3a8a0,-0x1ee1ed8b09d558c5da66a8bf2d3cacb0e9a0a3713773a65fdaef173435f29,0x12b65fd0b6b397204f47eaab21237eb1faf8f05f9c08961b0f5bf390e1518,-0xa254ffe364ec8d27a77c9b50e326014fdbc50491e7e9dd9b80bf0b247919,0x4ea513fe8336c9ea034f0969c0c6f5f6bcee8b1632cc0081966efd26a180,-0x21fa275632b8297540c499e5c1867d43e8b9e9ccfffb4b635406c3d81bf9,0xd0e9e12f9480a6778a3e5537fca4deb36002a8294f42828d30d3ff9b398,-0x472f8453ed5bf9bc7f45db6f2f5856ce02c971d7d1549017e645f08ac79,0x156caaf25d54e41f1f23d36a8013358f7e4b102efe73ceca6b891b74620,-0x5ab4a8e0bff495091531045bbfb03de3278f7c7472ca6db47a892cd5bd,0x14fc852b96bcf25eaf01cff0c7110778b4424d88d57593b37b68ee60b8,-0x437d2f76e4b34c2f975f224a899ec6c60cf48cc326ff9f1cdbd74cced,0xbb174c862c5f237ea7efc29a53312981ac05d30999d886ca5b827200,-0x1bb077a8dd9c2ae1aeb603193cdd4d2bc1145ccf9d459cdc3629829f,0x376748887dd9a19d294f52de5950ff3ad244749b860b7666dcc0168,-0x5c76b839b08fc19826c99fdc04b4553807b0a1ad2d03a121f0c21f,0x7eb77b064d21ae35bbfcc04c48f3355b0877aa4e2ddddfcdc48e0,-0x8bec0a513e4345a91c8411e7ea590f9ffa6ff7afca685dd995fb,0x799f1c15546046f65ff426794cc1f1a02f53ac16a27174dd3c8,-0x50d65754b822ff6d26aa724cf05624bfa8fae41c84ceff930b,0x279adca5b01893c03a62f55f8337d31ec54b2f919fec96080,-0xda3ff27ce2274a72aeeaf11a04bdeb49070c07a106a626f,0x319fd993784855f7386f944180bf02876db4482dd814a8,-0x6d577db93c5d876c942397febd222df6e0dd88e859af,0x80e6967f88ef1b9ab5fd3ee7c425c983c4f842a7e0,-0x431b1b6093a49dc40b2f09dc36a7965561c171db,0xb05677dea60344c3dd6a88e68eeffdd2f3108,-0x44333f56a03e6bf66c7516b1e3ab80a16b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 24 80 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 80 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 57 indices rho q20 m20 20 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 57 indices rho q20 m20 20 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r21 : List ℤ := raw_ints% [0x12228d21990a0938b4374923bf006ff566480bc722170000000,0x17f6f4e7e7ed4ab0692be7921d46ee0c98960051b75dc800000,0xf0cfe1404a107f56438a4436c36c59ae1f3ee8ea5b6c280000,0x5fa6f223f92808ad184e3a04736982b5b06ffe903b7f8d0000,0x1af9abad9ed0c22463a6cdf96d4c40c18aee73e98b4b970000,0x5bf6830a7e2dfd770b87100a498a294f05b6c20e3518e6000,0xf617e8e13f48b8a0275d55a9bbf039cefb6426234cf76800,0x21220ce2ac186a7cbca8d6bac93bf1b9c0b549962ebe8500,0x3a7563536170f4460eb541ead846a15b40cb4108c2bc000,0x557ef6a8ac940fdc7bff828ee3324f87688c7383301600,0x687dc8a9c536f7ddbfeec54763ad6e8e9c924b6db6700,0x6b44378e3c8ba74c3281b187927357ec509eda8c19a0,0x5cb9726340217b0576eac282a3da84d0f051d528b00,0x438198f5c143a855743d8bbfe22153c0289abe6b20,0x294d219beef12ecadfc06c82757c3a9b00ecb0628,0x1522699a2684b6df56c36ac1aa035ad76d5fa249,0x8f9acc1e52d4eda2da1965041dd3e417162340,0x32070a0dd31300fdc49bb324df5238b2bf16c,0xe0e784e9cbb903fce54bb9f861b5b9b28d0,0x31b7a36aac7a97cc8e6b3fbcb638ecc726,0x853826a84eee70fe54e27f812d6c4f00,0xfe3c8b9ae4e32d3d825b43c0a894ec,0x133f4df8b99674be9a782e8f464c8,0xb2016580f4479e5e3620f7b079]
def m21 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc8000000000000000000000000000000,-0x1035219f9f9123aabe13b7f466b51eafcf55eccede8938cb6a2d9d100,0xea8a3d526c74209198e6148b42031ef0bc31ab8e974334c1b1bb523c0,-0x88ff38e2d5dc99c60f1ed1102d4eb11b5a5aeb3fa62356021a94d26e00,0x3a160142f6a3edda1e42d951ab67a918dd7e289e3e1d12c8b40128ed830,-0x130ce4641b06856790876d9c5710df6fa86b8ecf9cf56a5627551c3a9780,0x50771af798ed39ebf45fc54bc94082caae2e699b57b797902c5afa044ed0,-0x1191410bf42805ba0fbb55b5248fc658f2422b35f35510a62420927935700,0x33bf762f7a90bee245d97d80c4ce093ad424c84924e88370a8eca411e3cac,-0x826bf3ef2b0cdc6b10323afb09b3f26574ea12fa0a3f7007dfb687890a420,0x11c6270d959fb0794ac010abffb20ae344bd01b696f7fb14fde92e3725fd64,-0x21d276024555d42aef6ee31216ce0346d9e515f00a71d4ef8224a8fd3231c0,0x388cc77b2c632da88ab8ff17dfff231486787924d2c6bdf1ecefb5fbf4ae3c,-0x53865237923db829564b935456733e40a997e42c14f5959a99f75902917a60,0x6d714494f04f30dd15b1257d712e08608e1f9c4af0fa9a06a45702b01b5c74,-0x7fa29785e6d0e29cec12f5dfa611c4e504b30ef8e441020a477d997802d480,0x84d082ba25305829b3165336d54e943d4c770181a694bfa636ded42d24895b,-0x7b88b236df2c3979ebf5b11eb1aa6b023d3152811ed6982c8bf02a6c374f08,0x66d31f694413e5cdb3c2055f7f48df2a4ab0a65e8ab60d5849ca0b67879d19,-0x4ca2ebfaf3208a1a1adcd3d48b1970370bca5af14d0ed172daed5b9f02cbb0,0x3325b4fed57c05fd4eecfb8db9931f359db31f27a23b100b70a66bc9d2e803,-0x1e8da0ffe6c925e777a2ed0b61b55d1a0f3b6c2b156ab57ac129893d5a4478,0x1051d878d1b731b4ac7234b5ca80a5090c788b5b0c8c4fe64bae924c279289,-0x7c8638964cc5df2c22fec3d95386447a33c11a38fe78e045d1251081a0f20,0x34e96415c36670314a3dedd716b16083b6f61ccec96bc717c5b91b65d9c5f,-0x13fab9b2ab46464c9b49613249ad4a3ae14f4046830de963cfc763ac71088,0x6aeb0441f7c5458e0325165e1ad9f91954c91523e4657b63b0211f4fc9d5,-0x1f8cd11417a7eed6984d99e4e49909bddb742d6908d86864a60f2a3aba10,0x82cd452977be86a17d1fa8714cf11af03196d2b8ca30026abf8d1e56717,-0x1d9823356d336ff4bfe26e20e5a1da3dc194a84fa3ff8c0e3a50474f638,0x5cec9d472bb70563b18c386c6c31551b4c6aee7b5a85229361f5cffb55,-0xfb1802cdce8556d3c4300feb79706742ce776da084bdd5aa572776740,0x242769ccdc3c0ca340b7e7052093222972e09614c7285dfd9d857b731,-0x463a7d03b8c88f84c8871f37c6db48099de40f917d14988b92c2b5d8,0x7182aa6670cc39c9eda7905b89a8edd0effd831dcbdb9f7c55b09cb,-0x963f05cd815cc54d94176e6678ffda36f3f476c0b5f8fe695925d0,0x9fbdd00ca357654f0f5b6aa2f2e2ebcfed081f9783d2159b91859,-0x85388c2a4cf5803dd0b3864754c439c90af91f2a2fb67556a5a8,0x549da9b0156b014f0ef7027b857fceef7ba89e8c5f42dbf6bab,-0x276ed23c892c6a0e841913f127a307ae4d8e945a4cfc450c20,0xcd99ed1f791e91bce257f509272e09636632007259792829,-0x2bf663f16460f52db35fef4ca6096436c2705a44b83e578,0x5a75972a206b37046e8092b4afeb9e4ce024834fec863,-0x62cba341f932837e49874abd22d28df30c44cf806b0,0x2f379fd17e3d2d5f83ea15f3e82442b77f0219061,-0x70b7d422523f92967f897e1a945196e95e9dc8,0x271b29e72faa3e72566ee9354844f9540f3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 24 82 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 82 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 57 indices rho q21 m21 21 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 57 indices rho q21 m21 21 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r22 : List ℤ := raw_ints% [-0x3946656f8ad1c13160f04aea2bb9baa96623824141d429000000,-0x4ba6ce8f74038cfd4a4739ffe90777ac8fdb89079e61abf80000,-0x2f7d0eb2c12a1a94125070796b7c1c3e630d9afa7a1c60af8000,-0x12da495c38f526695ad958126dd2663ca3f83da15834f0c65000,-0x5504d8f3765934316f79704c8a19f7db4cf20eb77dc6767fc00,-0x121aa2e011a5990f934051dd95849f7c0b43e095ab840d09700,-0x306a219b09bad4af1ec1aa810b6e9b4526d8c3b43b1b5d17c0,-0x68382f7bbb7903b049cd06135430fc6473f9d36df283cbf40,-0xb7bd86a73d8b96ce58280d5d0f7bc0f0014556a352d99070,-0x10c801e3becc12dacd95ec656cbb5a34ad11c5711289f590,-0x147dd68d56b9173a31599821a0b33afc9e1773e595e7474,-0x1504027c7fe7b04372826cf1738c30997f383dd69cfa5c,-0x1225d6134108bbf08fbf01036bdb5ffc79a32187878c9,-0xd3286df2135507e42bc981b0feb39f431ed433971b8,-0x810859ae11e57e057b5752f2aff3b9d28c1fe2e5be,-0x41f0ca5b45d3daac005374ce66dee8e02a3b084ec,-0x1bf692420c7c1d6f6fbbca307934a2fe7a23573e,-0x9b9ea550ecee5800a25718d8378c7c7fc36960,-0x2ba679d5d0e0a2b683c061736e62e8ddb9c3c,-0x9a1922deab4a0eb626decc6e65a0ae48f74,-0x19c0dd8d2ac9f99056bd1b6f9512125321,-0x3108fc914011e6e407418c33dadb9698,-0x3b3eb5fca24eeb027b8bef3299a23a,-0x2225cf883c12587368847312c3c4]
def m22 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb900000000000000000000000000000000,0x203544ea1abb726bfafa6eb0fa4ceb74a1b67ad0cf29de0a1db8604f00,-0x1cf02f457c3c424b51515ba2266ae339058a0ad2e6df1b3391edaef5440,0x10c9b7d2f8e8bff6907516963ee2d34f4d489ae77620f35f5e52ce266400,-0x711618bab5842cb06fc29b853d5222855c8e1cc7c1c3e928474c752b1950,0x24d195bbdc68367b2f1ee4b32fbd2a0129303c5a61d89bc031f8f9323ea80,-0x9a57ee6e65644cbb7330291c4d27ad8085e04bf41a08a8f60d3a648607b10,0x216f061b385adf96cb848901a6ed65530e8cb563ba1a89b6e564a9bfd9c600,-0x61b028ea5bc4de8088d7d8efbc9576c910887aad9935e48b1a5027de6baf14,0xf423dd091d48a238beb72eb8451bb9c8f2cff4724c39acb0070b7f23c914e0,-0x20fb5ca203d1ba87f4b54f163f4177162027aae1d275300ec398720dd7e9774,0x3e316983db2682097dda88df76ff1887e4b3792b20f784d023fce8751cc1380,-0x6701c1393d30f2e17b1ef9326cc5c551e20b9a69571e78ac3f77d13ba44d954,0x96a6d08c5944d1571f07a3353710bf01800d3f69c9da282bf7e6acf412bb4e0,-0xc362658e6f3fb3513ec6a87b2d0230e0e224286b50fd326036a331691022334,0xe170243d75277b2bc17c9235cc9e9a5f91f0edf47ac37e8afca9cd8b9f24600,-0xe7face4a4ad250c6534c596ed588b7c3078c46bd85021bc1b9424468ea503a5,0xd543a6104d932d97ae0e04b3a1dc88080a81eafd90c293e679f5d97b1798478,-0xaf5b05acc65fead0febe00950ce8a5b64b180d56b33b7050ee454318adc01ed,0x8107d87865738bd146bcb5e024648d8d3d8af61b64303e5543b71827a9d1d60,-0x54f71828fcb3988d38f8561c18b9fcaf6500e1445bbba2e3b1452a4cb072c51,0x320ae4aaa4c24f62537b261b69280d66aa1a68b539c0e97dfabda9c0968e118,-0x1a55cf048253305a6ec93279057a236b6aad484ee9c3fe4700bb285ad2d6799,0xc5d1f1290ac02c39e1fb57a1a5da9a16497ef0bf46e0b72004fb62fabf6c80,-0x52ad0dbde529bbd270a602b70371fa42b40569e766220af38285ae1cc25be9,0x1ead306539553ca189367577c20d33885fca87a5913e2af0e0ccd143be3018,-0xa124fd3371015e288f0abf12e799b04c2dc7ecc239126b3cfe4284f37c271,0x2e9fa31581b80fac9aab37a015b3358a49dbd7adbdfa37e6dd7502bbb25e0,-0xbd4831fad6ff20416ac847e7283546ab28710ed7b39fa76ac57f6bd8fc75,0x29e0bcb85fe61e6a0aa18d859a36500582ab520bdbe7ea12d97fccb97a38,-0x8062614599eceadd06a0a49a37dba28dc1a15bce4a27f799ef73ee7d33d,0x1521f17e6dc0fef59ca0132c3fa1e3744942492b6dc5b38fcb91c1e3a00,-0x2f5c033decb1a486214422532dcd3bd8130c85c892383b9bb0a4279bbf,0x594befd1ce57797f6baedc49d2e5a97bd1e9a9ae773b2082777686a68,-0x8bc14a76d1a86f78a6fef81fd31a005dafae24215d0a63da44bd8a17,0xb2a0561193d758c881bd70c6ea428e084ca09adc3d57ac6f7cd1d20,-0xb6d04f2fb401ec8b038441178e0ba5d4af8116a4248f40530e5a93,0x923d325267593a3593d05e6445001bb046084a776ec54c7657ac8,-0x58bb17abf168aebdc0b76ca84a21921bc52afb8a260a635eb5eb,0x2751665857485913ea1fe4d1572670e80fc19524c31a15f8d80,-0xc1e3ab54e2695b745b69547c42a82b7dc2b72e4e24e57475f,0x26f8fd124a344fb3843c3e9216c1a496dbaed5aacb27db28,-0x4adc9b713800b1cedff3c3785966dc1da407a9738d0797,0x4bb95f53762020dc10f68cca03721e526d0f211ee820,-0x2137d80488cc0a3e60884207f5ebafc220d9c15843,0x4809017a7d2527032019435ce087178e4f72c88,-0x166b5e4eb66d279a4e852bb9d27cf8eb6f3b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 24 84 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 84 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 57 indices rho q22 m22 22 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 57 indices rho q22 m22 22 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r23 : List ℤ := raw_ints% [0xafcc336721441c1d0037f049df602e54ffef258185f0c84000000,0xe819f1c080e56ce0e18c5828198be6d0a15adf261e20dffe00000,0x91a0e248ebd2b07fdd324842fa114dae05ed06f0425bd26560000,0x39c8f18496cf4c73fd6acf596c40f76d0fe57118acea14f0fc000,0x104735d25bef6f39a892fb38b60892f70de508a97a457b80a2000,0x376dd2bce7034327b2f10e3c5d810a78bc5cde5fdce370c28000,0x9423b81388398cc158650cc5618a805ddec3546107c1e101000,0x13eae9c0dec9375b26b0fb334b01101a81aff8ffeca7893dd40,0x231717d0937e9a3e806331ed2264e4f6ef7188463a7d94d880,0x333d0b0b40aa246b92db96ba3e7daa389a808db39fa65a3d0,0x3e840e7fc730b784bc5aa8e8c2e5f1c0ea62abf7904139c0,0x400ee82aeffcffc9e5cf1c7be61c162a8d02c0b440fe17c,0x374393c2a3e4bc18944bd438c14b26bc2f5e59f8998328,0x2825c2ebc6a2aca681edce4132e60c3ea771a9c93db17,0x1881749555b8c2a1edf0a4098b61e1016463d59ee400,0xc821ac011fc950644c90c63da1c77a1c103433d812,0x54c1f851ee0c62328fad0dc6138d16ea7c0ec1f50,0x1d704697dd13879ba332bebe8d6763ca19f4e742,0x83e94dd14b9fc5cbd535dd0278a02188288040,0x1d0e42b36e7f8e6e9e64ba889b369e87be054,0x4d8c7b88b50d12ca80912bdbffadb873fc8,0x9359cb7f4ee339dc1418cbfbce462683f,0xb1a05d7b5688fecc6f0a4cb52f29740,0x661f4dd312456fb51529df5769a76]
def m23 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb395772000000000000000000000000000000000,-0x4003dd0f3eefa8538badab05cb910831f9518df491611e3399953a99100,0x3925663589ddbf0111896966c38f7ce2fc638230501a755a21df82fb33c0,-0x20ee86e3a84a59154e767e3a274f650cff55c1095ec95af29a3b612072600,0xdc4ea5d043f60bd80e25f60214328079932853c593d9cc1a987e7ca78be30,-0x473787956397d36490018140345185673e2f5f1db6d59fc87a319b6b91c780,0x128568ea4860cfe71a6e63d86e6d2814e3b46a28b5a5e2ed7fef23a51161d50,-0x3fb396c0a9eb9d3ba1a8a3de62ba535de097630deafd26e5af880001f470300,0xb8a65086a47fb4367e88005f51a2925119e0ceb33ee57c2964eb29cd01da52c,-0x1c9ac1513fd4fe99ba414aa6c151a7382abd508184d6c4ba859e8392bb7a8420,0x3d4cbd8f6d90832864a3355dc834a59231e2ea106823bc7c2557c3d5b9c9bd84,-0x7290104f4e7ab4e2f335152e3a050b9d5e3d02b44c49bdb639cb6efcbbb2ecc0,0xbbfc99e262cd89d67763b43586de60cd4d1c9a8f7fc0872ecf91ff9191fd6c9c,-0x1104913a4ef9684067fd35816aea364161a3f231903ba7a6b682403b5cd5a1460,0x15d94f5de1726a29397074ac955e1be6b0375cdadfc823db9196fc3a27a089374,-0x18f1e2a83d396846ed8beed5550b4b61381f5ab53b3c000fd4a45b32c6257d680,0x1963121dc414fe8cebe56e0a30341f9e179ae7690a6c6c3e7373fe77cbb7e4fdb,-0x1712252f7cbae93b792aa415100aae757abc9134ee4d9644435ba983cbd1add08,0x12bde62c2fca0dfe26c808f8f92b02c4360a112f1d9558d182d27987067e9a981,-0xd9de0eb8eb8848c479aa56fc89a174f857c1e952a15000db62bfd117bf379b70,0x8d9029b1e4c1a5c00228d847c59ec74dcb6e6087d5b1043e6a355cbb1a14d37b,-0x52375671e0c46fd58e62fa792ec2b56596b44fc8701b8edadf4a1da33ac558f8,0x2aa1d1414e2bebdb6c5675c4d1b1520cbab15a6f059a8f14447ff34fce7e5289,-0x13b481661466b3cf7f79dfcc3fda3dfe55e12c5fbc3c81d8b4c61e8c9b8fffa0,0x819cfc6cf1afcc80ec013495243a15c6cd872ab2f7d953bf47a063257ab1e6f,-0x2f429d77a64031af2a19226b8e3f5ee43011bc5c24e3198673495effd540288,0xf3b4324f0aad9d794fb43973ee7dfa7dfa66c0773eea0f9b7f9dd0e617ed2d,-0x4522ba992dcc605ce10117547d0d38082c466225968756370cf04e1016af50,0x112d98e709f371d744110c415b1f1cd2cabbbe9e61f8ff4f7bf2727c71437f,-0x3b765771d58c1dede807f94e24be65a58fb462d10a410cb5f2ac330790ab8,0xb1f8f1412f92ba8b41f9c6f30e90654078ab2827860a5bb4a2682126ed25,-0x1c8ceb2dee51dcffc956a54e8e4a924001d99776452eec2f32b7ea162440,0x3e3c1369efb7975c8ae3ded5083309fc9a31fe4fb2fc5243ec17ec31111,-0x71e2bb077fdd28c4f1e2374e73d1b0817936a8f808c4e8bc0db5f5fbd8,0xac8e8911173c14a36f61adfce505b5b0ddac1aa80449a242e105b8063,-0xd4ec712850954b88491af6c7dd0a491b0a98711c5f4eac7aa5f11810,0xd1b62eeb5f84048abd5a7eb46cc6d1d938488e902a85dd1fec37ca1,-0xa0dc03be5f2cb3991a03533d7c82e460adf76df2024c8f8934e328,0x5d34bae7f7472dbc54912459e066373cbf544aab075b9d2060a0b,-0x2741b0f90c71886606c1c74a3025274b24bf80b93c81822068a0,0xb706327b33c674a01ff3a13609aa052a3d8c773372449c6839,-0x229203aadbc8910a6651382b781bc508930da4c7a67335f78,0x3df8985f6d91089cffcc198fc018586c17d149e4def7eeb,-0x3a0a995ee2283983cb1935210ee63be03f30169a12470,0x175da6569aadf852be9ffe135f24c316b632a4a74d9,-0x2e068f1c4b62449f82a87ba4891060a805e48d48,0xcd9c5543c7eb5a4e823094608aea1773be43]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 24 86 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 86 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 57 indices rho q23 m23 23 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 57 indices rho q23 m23 23 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r24 : List ℤ := raw_ints% [-0x20dbdcb69a67f16cb8e25812c6b4fef7760cf1a4bb98dfe96000000,-0x2b5d7700390b0f4bea9a8a92fb3261cbe1718d2ccd8c0833ed00000,-0x1b326afb7b49afe1796394a963c68bcdf335da43a00422fa6ed0000,-0xac961b8108369f9e349bec9c331f1b63ae916106d9c218eff1e000,-0x3098042ab29873977275ab45a4f0aea8c2c060fae033300d9ba800,-0xa56113bda9ccb551340336467717f23da0f6797ee8d2f21b5ca00,-0x1b9bd69c7b4c504a0cb51c78bde3278ec1b7bacec9a93ef6a2680,-0x3b5b39b216375ad144fa7174beb891675836acd8032255386380,-0x6880d704121c8305efdb170f5ba6e27528488a6d0006e434960,-0x987cb86e1d35b4b6d429ef7f89dd1cba4774724fe62109a2e0,-0xb9e86ecd766cbf19d916c7c27ee4dc5dccaa1b12e9c9f9368,-0xbe56d445c30b3bdde0b5bfc264780e7cd9ac279b0dac37e8,-0xa410651f90f1c700c31a26244543623c8ecac054fd07a9a,-0x771302c05b368865eba31e34f8399ed9736d16b9a0fc28,-0x489b81a26e5d2ca935f9158318e99fea4eb879b0ffcdd,-0x2504f1d058300c858899608a416b33e13083446c3af8,-0xfa8c2af0d441d23e54c9e3e3ecfe5b2d445ad7c978,-0x56e883ebaaf6b23fb6655ec5b619655f8580c9070,-0x184dfe6c0144cfd141e8e30e4efb711e9228d3ae,-0x55860aa1dd01ba959926918433807541ce2bd8,-0xe3df8ebcd7b757648f95f0ad6c31dcf5fdb6,-0x1b02dca4957c8b68e94c3e9248c92e6c0c8,-0x207e9978c5ac1a8b9c7a7f9c8c8462265,-0x12a3cc16509473e395a22c86cfe4388]
def m24 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee40000000000000000000000000000000000,0x7f40cb60e0394b668971647907a0ffe0d30e0309d9ac2a83f99121888f00,-0x70e2b4439e7a3fac6a2745e218ec9eac3c1be50606ae5e964902adc6b4440,0x40a1685a018e6da8decb1fceb18552478422f3223a44206945bf6188dbbc00,-0x1ad759debc50c02b1e024dce852c3e76740d45ff738a3371b385088fdf2af50,0x89dc6aeba89a55f2ddd24feac67ee0c29f8c9b76e5888a758d264808f990a80,-0x23981b7d70c9159cfaaf4338ce7f7a304538c8e32b10c831afc8c43ed39dc390,0x798165c8713e9499a9a31a6242ef0b847f74818209c3ac605c8aa9ec1fac5200,-0x15d770f9a6033c51e1bb2bc1817fcb4643856ee3a461570c5bc8351d6b50d3094,0x35b2f03f56ba9701f1c28489a0298562182e827f32f9f93eadee732d621c92ce0,-0x721c429ba54f16ded1adb704e37a47752e3ee01b88aaa8e188e319850043acf14,0xd36513abcef32af66651e5f228f678aab42f39ff52456ec4d6105a3924bf62a80,-0x157b7de2308d39c89f7dc26ceaa51e9b63e2d23619731da56f414b0602b95e5674,0x1ed1ef946e11c8e9570c0328164acb7e2a2f8f61a42a863009d816c5dd7f3354e0,-0x272d43d94687850a79f662cd74dcceb104fd75464c0e2488cd894ab483f1646234,0x2c43c1a4df590ee9283ba5be3fae470af82f2c18eca592d1e8e4fe29fd0e655a00,-0x2c8f97621403010fb1b81982a782e7b0802d124a094b78d9d6e1a6881f4ffac325,0x28092b0fd5f9cff14ad4645f9117b3afdc2a890f8a60f033a54eec890520cb1878,-0x2022e36fbc9e32fee81a0898c0b6a8b4cf6d836350c881c06166ccc2bea0279eb5,0x170e805f2b0cd046719608448e68e98308a6841add58b6932b65d6cbb8b78d3820,-0xec8e09f8308a4512b718f96ac216207d4ac59eca10b3094e09e121387d707b539,0x877c37c33c51ab9f494bf313b302049655adba3343ac6b174cabc51aabb17c918,-0x453adcf0c90e6bc01027b2f2228451be8d4b1d23dd8362d8977f75209cb171299,0x1f81a35627d93eb9d6492ed409445ca028181241d191e2334131f982d0ae7ef80,-0xcbdd2bee320b5c8f0a790036b23f0f3db835b0a5912156f800cc4cec4eebec59,0x490d31d724cd6e7b5573fdeb7ae2b47389f45847f4647c4691870c5e2f89f898,-0x171cd4c12e754a5f1e01e69d4b337173714f0cb2b93435432984fa19e9104129,0x66dd539647e5608217cdc6dc716efd4ccb8ffbef05aab80f3911b7ab19ca3a0,-0x19072e8afed1ba81fcdd977fb3068523d7e6da8e1a23a6a8edc54da5a29a86d,0x54b69d8962adc3fd09cc8a3fc5b273a60fa4cd6103ee29a1db4238f4da03b8,-0xf78712a5c84cf4dd54da7bcd2cff182c3b34c809f0bf9af0f452bc34bf18d,0x26b23681b8b4389405412902be54d7a9b4355a8de8d20ee26bb118ac48200,-0x520920b0f3e48109685e427e6f64844e21fc7b95499f111457b89cfce1df,0x91ac94ea8f538cd4b12f0498bdf6decaa1bee70232f78b244def520db68,-0xd5a56b2fad343d1691a7459e1af18a4ef9d3e70d83987df303b066edcf,0xfe734dbf08cad505cf0156b1afbf06a060ffe8ac68c0c85720071d360,-0xf11d41f4ec498195f3f82c07eea37c9871f5b76bb9a966250553656b,0xb14a6713c6684f2f19d6b67e5cbaeeeecbee2698b5b81216e205dc8,-0x62113f62b992d30ff3c8eb5915712134899622ac792f2f31c2534b,0x273ee1a8526d03707eb4dfe74a6792efb6d22d6fa452f86fc0280,-0xaced2a438ad5b30211bc2f5b5b45b726e584b0b9fcbc678b8cf,0x1eaec2bc474c12cf95faeca2ac5d6a746997d43112192edda8,-0x33500f0609e7e193da6958f52d077e587528dd94bef7f1bf,0x2c7cd98b711b3a1fd533a2778e4c5635d5bdcf6c984a60,-0x106ed6c6bd38f46aa0e8313ac8fd4a02b572569bfc6b,0x1d669df6d642686a5179e70120e0d03f7676af008,-0x75d581ea457f2ac08b4d4865786d6d1c0700b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 24 88 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 88 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 57 indices rho q24 m24 24 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 57 indices rho q24 m24 24 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r25 : List ℤ := raw_ints% [0x5ff5f4421b2aa1a7d5e085f1030d4bfda822f9793c9f261508000000,0x7e984fc0116a5777e53af18ba20c18e2feba100116a34298dbc00000,0x4f5cfdc54c9484b411b3c10392b434ee40afdbaf15da5f4fd7cc0000,0x1f7676f981f9b14b8bd05cdf34e5d6df526e801548a9c1b121518000,0x8dac728663c01a8deca435ce18f10528ef4011b612c8ce08f3f0000,0x1e1ead6a61dd851a4b7902fd8acc6cbfda2e10c4281f22fe3bd5000,0x5068ccb8f4c0ad0a611a158f9c0612091eb10da981a0f05f448400,0xacc639645b88d3bac113b061ff5e8528760ad0f3287051322c380,0x1300073aed49244ec242b2336b87b33b5ea9b9f3677d9f98b0c00,0x1bb4bf2d7aad8edc33a82b73eedc8e53e9b759aa0a8d1dcedf20,0x21c12e2c8476d30b81ee8e9282545e81ffb2e5691d31a176bc0,0x22887469d37d8fa12fc917c060d1a828d7f6943a7e93152878,0x1dbde287596143f2ba2d4769c9548682fb8e5a9f7ded7bf20,0x1591284c7f1d8115385900840db415357dd6241931504d26,0xd236f3c2b2c19db6289da786066ce124ee7976b368f748,0x6b11df23bc0a53d94889fbbb3ce6ccd6aae5ef369aec3,0x2d3d9fce49d1e3a5e7055028eb83b64c7cff638c5180,0xfac8e58593f2a749c10168581411d79ecab76a3388,0x460b0e761127f4ec34f997e3d1b1981bad1b5a2d0,0xf61f03b0ad69fa4df93093a1906bc9ec8ab9572,0x28ec49efba9d4ddf9c0e88f1e5f1d1f2fdb6a0,0x4d7ba45a994f51456e533b3c00d88704190a,0x5d0a5073ecfc46603f9e943e957c5ac2e8,0x35432c21d31342dc7192df68b063a6fb]
def m25 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc800000000000000000000000000000000000,-0xfd0028325f00ec9fffed84e61937efc398eb25e315bd925fb38930f895100,0xdf0fc69729ba037b5c6a6f616a6a99400c48da337678aa4b874c3cb0fd43c0,-0x7ee67509f50fb4369f24799d8a3405d94886ae690a9b0aef3bb676444659e00,0x345b1a223f847962e377367317a62a0db480c30527e72a820ed7e4557edd3430,-0x10b13d08835143a6c978fbb45c6741b0e0c773785c613ac35e61d433c15fdf780,0x44781c4e12cc9ecc3408c79a679cea32ab6cd9cf459be54bb94c11bfd0df75fd0,-0xe8039233a2aa7146a4cbfd399d69d2901e8416dcaecc4a7c5e0bdc0d2505f0f00,0x29636ce6fae899c14aecc4d65eec8beecb4184d88f313b142ee50fc5478f2041ac,-0x64f308430bbdef148c7fe0c73d2ae06f8967e07ca707b165bad5146947b103e420,0xd4bf41afff0fa92f442a28a815dec370c2b4f2f871ab74e3dd0e5a3468ad0f0ea4,-0x186bc416c809ca65d85daf01ac0eddc55365f6642ef5986705cfcff0b80e7157fc0,0x2759f35c53f58196da5342f1b0ea28d73843603acc32dba039b82a5249ba11ed3fc,-0x37ed848e08e7fb54e47487828b7aed2cc9a4f83536a65f01f99bad5dd791e520e60,0x4665bba93a6b8115a6c99905bc3fc2791d9b09674a6939f7f5b06e5e6657f95dc74,-0x4eb9fd0f88f572e4d6aa472fa644a045c0d387405297e0fd07b72f519324c3b0880,0x4e67a4234c26477e17efdb0a12191259fccc7da381eaacdc3f007f80243b2fdc45b,-0x45a7009b2369bb8795d739f69c4c96912a0da342a6be989ad1f330862ba0071eb08,0x374024616c62791cc5b7091efc279f12f035edadcf243646776367aae24b096cf29,-0x27264cca0a06e54feb8d1d6b5e8ff9efe13a1992123afeec153ff39a8f3dd33e930,0x18c6e8c64ae1463bb8d9604d8856cdc248d88a5ce7c612eed9d9854e26971cd1e33,-0xdfefcf8c4ca63dc30d91da2c26eb73f6f924031d08ab457c17d598323475c16578,0x70c4d2869fa06c7cf132a85d6defa374f9ee03a0e7b826c0cf3521d7e9ac841b09,-0x3288ece86ccdfb8e2e2f5251fe18179eee28651f71d92612e3d93a73c88b605c20,0x141afa27b8584b9bc8892e23c8dbc0fd89c198450bdfe226fee63536a23e96afff,-0x7149da2a5880a976d2dee972a0c977fd05c710fc938e970bcc43b89f270b9f488,0x233019ba4ff862e6b9b06c2613100f3276f2c93d961b70abaaeb9a73790e13845,-0x998ee8250f4e039ba3b8d16ae1c6badc527424e2001bbe6d660cbf0f53b2e690,0x24961cf9027e224c8c62d08bb20e76e54785f46c57ed9dc99f56bd5dab7841a7,-0x7915b48a75a581d6d2109515005d09a71648387f7f32981bc6a4aa4c5355738,0x159614aca444bebd635845b30ca578f90b127758384166f2e886ef1de78aef5,-0x349cbfb3c36f4bad8cb4cd03e681fa19afde9307b2b0177a5f79661f317940,0x6c76d7aa5bcaca51cfbeff6c3a9ae5d7dd686799030aa9c40a84105f345f1,-0xbadf1bdc593c51bc9595b227be907e06a78e4a3f6bf8c6078290fdf201d8,0x1093af3fd432f90b6c57d909b93be0492959503be652799e3ef04e22a7bb,-0x130d2de4bfafe10cd9eb01915417d01f781c5f0e0d3d033d45ed1984c50,0x115d3bbbf77539813a56d0b9a0a8f6be80f0cdb8a654f04f69399933a9,-0xc3c51aff9e409956d509e8f115779db8545a8f0821027f5cb6bf08a8,0x6757ed75083dc90ed20697086c3d157c107eb1edff81832824116eb,-0x27483cae933d0027ca794ff2588eeea3213c432449a7c99aaa7120,0xa386861596b6a2d5e7b6f05fc9a4104b03e753e04a4e092ce3c9,-0x1b3f04228fcb485d51a6ccbb932c3771105ea74a78df51c1978,0x2a7f1edfbc0c33d3b836c5613f09cfdee17ace19495e62ab3,-0x22192a1f090825b0801842204bc023361f2a5063c2f6830,0xb8e22e118c19523b50d0c6a3d6e0d88b1361801a4491,-0x12c6ea392eede634d2e05b857af6e67dafc13304c8,0x4384a5da23ff0732cf1786d7bfc254b2ddf693]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 24 90 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 90 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 57 indices rho q25 m25 25 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 57 indices rho q25 m25 25 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r26 : List ℤ := raw_ints% [-0x11233fce68918b12962c767632e295c14f28d6ca96646894ed0b000000,-0x1699c0a55f323f65a379a8abd2b7221144ba99163a2fed7cba1b680000,-0xe29be3034e29372c1dcaff0132284d3f5c37c78cdb5a94f140fc68000,-0x59ccd777cfb5d25106e44b8a8762c26b193a5b18b2e40775b3943f000,-0x1942f52ed5ae58e9935225a2ace2968a067caad9294b77f4c3ee53400,-0x55e3c4ac042fc2be851af0eae741204e3b9e0602afa07a0612c33500,-0xe52e5d9d6d67b5357c9312d0b2dfb3c0a21faa7eabfc730312d1340,-0x1ec2cda8e67664e922afb35c2c84142850a4aaecec5e68ace6be5c0,-0x36180dc731f91210eaebcd177bb78a0f852fc34f672a6d5153f3d0,-0x4ed4f2c1c05b647cd43fec10e45b918cd974a72aeaef503ae4db0,-0x5ffa965db502ee8b77a3f4d3d294e26e699ce2346aec65e27f7c,-0x621f8a5a06ff9e7408815f28d18bce68aa787ab3810c8ab1614,-0x5471ff1813f030647ee7ad7dd1234ad827d01b7439ea176353,-0x3d2f6c867a4ab1f63a1a78e6b0f76a30692b9a750f3be9288,-0x253dab40849a26a0f0a18edd7273e1865f42728d0809f754,-0x12f3442866ba1804e34a8b1957da8c1ce967b0ddcee3334,-0x7ffbf012cabf84822c1de76bb4674954f54f378f94842,-0x2c4ae32b77c07c76cb4b2d2bc16fce7f53986f8fde60,-0xc5b2397d36ca5c316d1488609bdff1090bc64dfff0,-0x2b5c715c1ebee9964b8e4583804854b43ef4e823c,-0x733196c8ecd18fd725d41920e7087a07e8c4fd3,-0xd9c5ae2ce471f37ef45face2ad3727a6923a8,-0x1050f55fbffefc5bf597e240c6ba17ceb2c8,-0x952c85d14acbe1f6aa7b11e9d832a277c]
def m26 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb90000000000000000000000000000000000000,0x1f7158a2ef1359f88ab1fd5f505bc608af8479967fa1f4b996bd9cee1a0cf00,-0x1b8e73b8a621c132dc986e87982d24fd67c7869e44f6695a1fe96ec16eab3440,0xf947687683d7f995bf8103f3956de9bfee9820e0521a6d437652db596c2bd400,-0x662fbb85ed0602b9282730cc79c218e9366e34eb4e309fce583850b49f09a9550,0x205cd70e493d9f294b13b3f0e069e13f9d7d72b0fbbcfca82abf78f21df7adaa80,-0x83d416aeb88f5daa954d24365bbdef5cf14a0139b7b464798a2adbc1eccb839010,0x1bb80c4d0bc52fe454ceaa04b6e9a41062f5ef0902871987731e2047a07963f3e00,-0x4e862fcf12a06c5d48897f2fde723910a73087d5574575133406cf130a7b0b6ae14,0xbe09579f6b3511db08a2fc41147a0a4aa483328bf085f09c60e25b5e48c54c584e0,-0x18d3fddf219701e6f7877476110ad2729c059d95608950f89efd2f19e66eca55b3b4,0x2d36e3e722c78ae5d1f7d7e3127898eda1bd13856f8103163da223d9593aa64cf980,-0x4837018be198459c02d937a9f81b11a893b85edbe917ce7d79c2d3523efb45a0ee94,0x65b0652435f885a2ed827de473d7d0bf56daa62fe29472f82530e61d008c3a7f24e0,-0x7ec3b3b8ee0a0a228159819b0a1c783e58bb6a7dabf5848d4db0b6396208f55e9334,0x8c551b52488787b31ebd3066035ffc4d76c943283688c1cd4296fc54592f05f90e00,-0x8a47fbde2e33693dc1f27bcdbdf0adafa3f16cc8aad331a09ea502b4b1ae5ffca4a5,0x797b40b0ef1e10520d328cd697f0ea9388f0cb565262429b2c8c1e4b2b8767bb9c78,-0x5f3d5ca530ba59f81263790cb8ece2f2d01f63b2567bce9a7c7efa547d45e0ca6fbd,0x42a85605a4d34b5ccff4b45dd38d27578410e37573b39dc5755506a5976808fa28e0,-0x29a42382fe0baf9fecd760c3f0088f3fadddf3add19c92d85beaef16a901ab74d3e1,0x1733a1f171d776510429357e82ca980a534af49898fc2f955194341f6e2c87304d18,-0xb83f95424abe68771dd1041d307087350ed2ab71121dc12b71ec39ee714af2e0619,0x514efe97c15701c70fd0267e5ae98a0c03b2fb875e9c0e2a233bbace125a39e8a80,-0x1fd3815539661e972f2f6675225dc69373d11fa24ce1e1ac0c9915bd1b033fec949,0xb04187af2f63ed26b4463c71e6a473beacae4832bb27b407d0755885c26dc00d18,-0x35bf2ec83d0bfa729bb27819ba5d4fd98096baae859cf966f054d5ac2b64c6fea1,0xe5fc5f126b7eeef29ccbe15748739e985ce5a022cc859a816ed068690a4d30f60,-0x35a8408663c148094fa35e391b6c40fee41dbec736ac0651ab16c96a531d247a5,0xada1bbef97b015ce7075065019d39702dc8400d6a09e8c6bf3d73e0283827d38,-0x1e371b9577196c23e3a642c7ed479ab0bf43040dcbf8e3c15b630e655a92afdd,0x47c0e888ea5bd1e73a2e8cff04c372a7f65f88f252cdcc056ecc093689e0a00,-0x8fd4dae0216f8351b4318810934751510e745cf49b7d65c2b5bd094264acff,0xf064405458a671028ba62ec2fb3f6d6c3c44f639e004033cfb1ba92475468,-0x14a20e5d2a12a41f90e2c43789ca3821cde366391f9a26c7658d482adfb47,0x16e09cd923a417e6526ba615527c163ff0d5146bbd61858a8f9e90a93ba0,-0x140ce6b988b015d680526a00e57aaba50c3f722bf51f72ee1b6e164ec83,0xd8913d9e90faf7f9f3b0b5b76ed22dd0c5b8bfa5a4fad96d68e2cfcc8,-0x6d10b4ca2a7579c4807aa62e4b05f1f89a1169e7ad26b3c930fb772b,0x275d18a50f38c2196fe65ab71ca3a546e58a5a9ca9aa675789d1f80,-0x9ac23a9f25acbb80c803ec68b7b15ae851add4445493cc25e12bf,0x1834b469596ccd43d3195e889fec70df8807ec4b3343a4d41c28,-0x2333990fe6dd7faf1a8dfe7be3dd6c4d8ecb611f3f49392a27,0x1a225c71ce5252f8291208be2273d2012a1a87d2cc3ebea0,-0x81fba1b82a8c9d7dbb6f54a44b683052c893ecb345853,0xbfd4f59d27cabf931655e6eb73b8e079088fb5fb88,-0x26ae507b9d0b79d392491d3c31015a28c5773db]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 24 92 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 92 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 57 indices rho q26 m26 26 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 57 indices rho q26 m26 26 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r27 : List ℤ := raw_ints% [0x2fff87427e1bcecc1233fe306da7abb76a80307d4a55bc9fe3abc000000,0x3f46eccd901edaddc468e69b2448abaacb61e73030d7273f91422200000,0x27a3b314667a71116635f41c21e33890baf95ec218f877741ea53aa0000,0xfb3c5984ff10db462217e4a2f597447c940cb7e9bb50537bca1e9e4000,0x46a557c9cb5204b383ba18504fa8d8af582efee0bad3ba5818fc56a000,0xf017a18db960e3a4d819e03c1f7c42a5677bc74fe481ad9eb09591000,0x2805807ecff021b5e7f82acedca919a0c4bdd51503c2ad3315594d400,0x55e7a3265797d0f8876ad5b767a7259b9ec3b96e6b2bc300c9bc07c0,0x96fc44d456a53b4d3f6b0bd781b840d1d924954b6e66e65987c0e80,0xdbe852655d58dbacda7d52e76e8fbed531992c753522c7026d0bf0,0x10b93b3beaf0b39232646c6c26fa53b12b8ff51f639e85b52e2400,0x111604a3eb7002d57fbb8149a23bf8f4a2026d4a4bbd1e2808d94,0xeb1a8ced30053d40a1e58e4787989683b90e929d7ad567e83a8,0xaa379ba8f0e87e3e4c5ca3947f605238a064f6e56ce3cf8ecd,0x67852cdf09b5d7dc869a5d9aff73c65c147291bfc0357c540,0x34a18abaca8dd305c9da43304567f0aa02cab754698033dc,0x1631eb6e97b22c4f745d01760475bb73d5a06e63d94bd50,0x7ac65f344e6b539f42c9285b55d92b79c4be67606c13e,0x223657af55312301988856b44dba68d9af1867c16a00,0x77eb59af54cd96f0d7710aa8368beeb5a1f635a880,0x13e2b834d37c2e1fa353b8c44faf5316fe3853348,0x258a7e51369f396e194d4b44aff76019d2ad2cd,0x2cef4844ddfcf623877f2b7b5a4c9443bd600,0x19a23b323bd01086b6266260ffdfd352f88]
def m27 : List ℤ := raw_ints% [0x0,0x22bff60905c443909fb39577200000000000000000000000000000000000000,-0x3e8843455a59f8f3e2214f77924dcfb0d410ab939749ca27940f600d52791100,0x367bf961de1f34ae8103f451a55798fa70dea6b077a54bfd3391c6f9c66bb53c0,-0x1e9e53521ad0d2a25764b31fd6930be39f3e0684899eade3c68e5a58bf296bd600,0xc79042724cb5d399088e2583f269254b6cf54ec42cdb48dc45c97626efe16cba30,-0x3eca75bcb1cd8d985737e117a7546e4147979fa843cc4585ebedc52979bf3d32780,0xfe0c05262510527008a4f4ccba9ef79a8b7de62bdacee744f6627a1661d6e31b650,-0x350a9a4b28b96082c1a0e8f0c08e5020f99f82d74f84bcca0836c2d68656e7b27b00,0x9528b4bf008b46ba3b04ee8a5326eae3267324b4cea26db7f4592a82a844c669f22c,-0x16639c0963e4ff2b036cf3cec2c91f1d7d4161573d46cea45141e58faf2371c8ac420,0x2e6df082dbb3a882f77fd31a0180014ea58f6d93f684f39be5bc8cdea1fee946138c4,-0x53d9b68ac4d11777c467190aae102538a129bf37308dc2608f8243d20529e0ef8aac0,0x84c2d2dcbfe5e4a8f56407c74233295f2f2b528dde89edbbc6407416c69f513293c5c,-0xb9402a6024fd98910905e8ebcec1b7969c7c8d21961420027bed611154e325c71e860,0xe4bced60a61daf3f40730c51ae88ff05b7e211531beaae88a48edb3f7715ba13a6774,-0xfab32ed5acead8e0aed3643daa8d6ab973502a580a90eb8a2d5d29ea63f43b0016a80,0xf47497f8fb4905b87f32e4fcf40d98fbf2bdc0e0ffef67c560f0d8703dc90142b76db,-0xd4669186f86436e4ea02df560125cfe68c845f73bcdcecf8d63a063a75fff86aff908,0xa4990285c801f382e6feed8425b7c70fc4231a260e6b192b013929caa74e0b45f6811,-0x71cd06a609f56094031bfa15b26a787e30608c21c430946d1f7889e4d9ebfa5e3a4f0,0x462e44094fdc44d59f24ab9ed753b7d249763ffef70e87ac3ed3d50bb88a8349fd62b,-0x2692feafb1af27a6079e6e98886664927c3df821c24f033bf2c5b861fd5df836e09f8,0x12df06556352d92c25e6ac9f0e00a20039e6ec9f080699a90b6c260a2e4030aaff809,-0x833983298d587697d2bcb691ab42fb74282e549fff31bce9b266c665422d6025e4a0,0x3289b95211b43dd0ba951770ee1bc54bee1a14ca00f708de3ddb025de61ed129350f,-0x113185f84d5b20ca6de40ecf67943ed1297b283f48a09acba6c1eb1df49ac39b4688,0x525ba7121145ea6f2d3a554a7202b5bc8310d3b1b6ef08331370a2c89465277191d,-0x159901698b28e93a7d28f7be2f1c4c2d798af981094b6e751e3d6e0d95f6be40fd0,0x4ef2290f097847fb5d5a8d5d6372b4f99239c16412a33aa4e58edbed7a4a5ddb8f,-0xf9c5e49187c2ef9c18ceb30f3729d73abb8e324ad30589c8c0c599b0140561bb8,0x2a6cddee6df1758c1920ab3a2a940d8c7ecade4908e7caaa8d1c66d118f6b88c5,-0x62276a7f576458e8591c30225b38e4268d78ba5b856625f4afbfb4ea26916640,0xbf484e77fcaddd4faa2b9b223cf9e2060041d256a028520364054e42b11fdd1,-0x136159a9a2d14a99a73d9b7cf5e0be11c86460103c07d091875ac8afe4907d8,0x19bf2b1112a4c91b215c80457c5c0c439f25abb65d1c20055a72ec147eb5d3,-0x1b88edac5e77e94e6814fdb8542a3e3b50dd238da7b8fe92503828d541290,0x1733031f72182625671a6a0598f5980d7b4e7c4dd8f399fa464990993f71,-0xeffd79683ef08167849c825ea5314ebb1cf87c495f64b4cb491d9f3628,0x73443861859bd0147bb33151e56b292e573fab5a59e26ca074d765e4b,-0x277cdc57dc869ab081c143330d35ed8498f9947a3d31b3bc297c65a0,0x9291fdb42b2c072c5adcf9d71fe08d2bcdccbd2c921829b30e5ed9,-0x158394fc5a0474d1400ef4b59122d380a0ab8717762c65475f378,0x1d29cec45c0b7017b0fb4bb18ff5654de16c69d79bac25645bb,-0x14077c35f2025b06b6d5989b69ce798ce9677e4ef2a9821f0,0x5b5e7a8834d53c9e6a87b01fc46feea41e0d09f0a6dd89,-0x7a7677f2a8932c0a424313591213cc7164018498448,0x16280e51cad6bbcbb112fd8956ebcb7a518739e3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 24 94 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 94 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 57 indices rho q27 m27 27 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 57 indices rho q27 m27 27 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x19a23b323bd01086b6266260ffdfd352f88,-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r28 : List ℤ := raw_ints% [-0x83f7630be2c3d730495480c300431ab4e86215bfddf55858854108000000,-0xadeb52d0f495135aa1997df6bc458bf603a72a728129c2fc755255c00000,-0x6ce9e8e7ed15d7255ab3f833501efd73b4f656e6be2fb28ef0238e7c0000,-0x2b20c9a175ce3f582301556ace9a703e8cf78d89f991b540146ca4548000,-0xc1f68135006a60f1231da6e6e49c8f7f5437129cc8ff7ee21e86f62a000,-0x292eb547715334750ae77c835b72580682e43d6ec52777c7cf092d65800,-0x6dc9e1f01659ce215b14bda79aaf8ac5c2f523dd26510239b39c6e3e00,-0xeb8c3145bfaa6dfbafcafa61d9dede7b1817ef142f955ccea205f1600,-0x19dca1bd6e1bc0d6bef70e30fc22325e117d8fc23fd12307b8d34a7c0,-0x25a5afff134d769c6324fda2781948e002ff9b43c1c0c04a9cacda00,-0x2dc82aa65ea11d14cf5c5309978681e58e3f1e05bc0a8f9114a72b0,-0x2ebede979951dcc9d14991372ed7a115dbda9b9ee9b31063e1e7e0,-0x282ccab0c9c05509b80ce1a3775b94d391161afea3761689d9574,-0x1d1110b8ec72ba347f62ae1db3d16b02699a468ac8a2d090e418,-0x11a9fef4571ba2d2176f762438f04ce7de82c6dfa2753864ca3,-0x8f92f4b870e6be656047fea6420989c10ddac00e68ac7d660,-0x3c7e72a100ab032aa17d62245bdf366186f94102a6b96c9c,-0x14e516a544e62becfedd6df17a04c9b4de73c59b94cbfb0,-0x5d110b5708ad2460689a10289d4913b348171e9015202,-0x145db70373096c3189bc12b46aaecfdba28d2f332f20,-0x35f8b4b215a32704f333aa6f150f3447c3a0d04df8,-0x65c26eed392921b8f81cabaea9d139ff9d260378,-0x79a1b5a9282838c837e71c00ee5f678ad7f8e3,-0x454817facf6e99f5e929997117595dfb8360]
def m28 : List ℤ := raw_ints% [0x0,-0x457fec120b8887213f672aee4000000000000000000000000000000000000000,0x7c615169b557479d30f1731578aec2669ae04c6df51ef7acaeddca19cfca90f00,-0x6bc1d0b24180194c7b3244dc0e73d6da3b4e0475d19f06fbecadc23d9070af2440,0x3c3308a6258d46c8500e1f515fa921fee457c3621c4a1a3fd071d7f14bad75cac00,-0x185f6a24949e787edf98091529b2e2d4b724e93c6a59cba815697c6902e0e6a14b50,0x79eb03bdbf870f9d6df7b8092c240b703b2ec82309268bb9e261264810857421ca80,-0x1ea01d3b5cfc2708b5ccf7d3c677ed14f6de055b546bc1396ebf982671aef237a0090,0x659a13a6fd331ba86f2d99607ac7b6d931662f5b01ca5e9b267d45cf2b8aab2d18a00,-0x11baa993ffdefa729c48d23ada4a68cd16200c45d764695cef845510afcfb95c08c794,0x2a42a26ae86db6278f21902e1afddf6baad30c7870ffc17b97fd13c1474dc01bf61ce0,-0x56f3ea9d505f5ab2f70ae7c257709e7cead30fe9e05ec855a9ae14988576e91d026d54,0x9bc0c91f42eb906a8a4dc9c7f40ac09ad4296569f88705f77f150826dd77559aba4080,-0xf4801dba8087d42c4b052d888f8e208c937a6c3daddcc579da30a03a48613c007a29b4,0x1521edfd1ee304be38154e6133c868d621040a1e3324d64cd89a4bd70edaca57c9924e0,-0x19d95eff6ac2547d1abd1ba43be4bb361b389e831ea798f99b82631340e4b04de2c6634,0x1c0d8090bc6438feb8fd55d060f8adc9179c440f28a3636c75ec39c70b047932e32e200,-0x1b1265942ee69d36a9e1dd3c3d5651308bab6b28a516f6ac3eb34098c5c19f893c11825,0x1744528584d288227491691350be9d4b99f0cba3c30647fc747f75946b74fbc514b1078,-0x11d314b06b323938bd85d4fc7f12f7d195bbe2d17be56741733a7b394fa1328f4a3e705,0xc2ce0af1a3ba671942ed54da782f2cb1a5d78ef6e621442f244658ce4e8e4c43739fa0,-0x769bd512cb4331356308c617c8981ed1d2abeb12a6a6946626193d0adf0e717259d249,0x4050ee147c008eb32ae68aebaf46f60fd2309fa39f99a755fac2217d91f356884aed18,-0x1f0451b74ee96632c36c29d4b78f4e4d66077f95bc9f816b712015c2f22c2d97252e19,0xd46d5249e17abbe4a692c530bda3832271dae1a76813e3b4f3b2939bddd7500d19d80,-0x507fd7d2f47ea5f565ea69247205b1d200f22bc3dfc24d416f2266cea46f5e00d0eb9,0x1aeb546d5e237f63d545788f5c7d98026e30b0a71acb6e4fc67dceb51f1a8727c6d98,-0x7e9973b0894a49a0ec43b3dae287c066bf445055277959148d340a0aa153404a80d9,0x208de8b2dbf7c85b256e542cf818a1db129a2cd6c96beaeb7328dcd01c137acb3920,-0x74851fd5ffd24d52e54b470587551b0f1dd8f3893bcdcadbea695fd4d81c19a181d,0x1686c90f42adf347d322d4e9a882978fce934c5964724a8b322b31251681ad766b8,-0x3bc0444110aad762c85e82966428e9725d13c2eab1fcbb3381680d0ec3c9f4562d,0x86aa1bdcbb78e9b54e37a38e84fa918e7c6794048e4d67c71ce7dacc5b9cf9200,-0xff1b2fb232fd8b9525d4bcb27d49266d895856ee2ec244136f0f1de22c85951f,0x1910bce14a507933e4f13e7256f342985d5b94e6dced75e47b68f80cd5c3d568,-0x2034f9db9e520ec59709ea23f43b66b775d1e535e9a1ec85bdd3712080ab07f,0x2136dff8921a40fceddfe98ddb4a58d80f02ae4b251aa58795629591b6a5e0,-0x1ae52eeddc07702095d0888968ce1bd0f6da41ce4be78701c973e612a35db,0x10a635cf627bb09e72cdb385667c89dc32cb13e075dcb4f72e81d210d7c8,-0x79fbdba81f8a8259038ef8c9e783a1c241ce251470d0fd0947d7c28d8b,0x27a6fcecaf23fb605c0ebdb5617d4aa8d0a7810b048964c013bad4480,-0x8ae90ef1da308f06d10be555f7d52aa888d9c0b8ff5bd75a7e1d12f,0x1320fa4e4692e21668293a577b745f1faac4a258b70e3470db96a8,-0x1829f6c9fed33487131643e2372d58321a8b782d246fdeed52cf,0xf5973343dd0e7a48176cfc150df97d1dbc442538c9160b4e0,-0x403701e2f30f480537f9d6e97bdcdc747a7b1efcb1a55fb,0x4e299094e19e2947c9ceefd9e80d5bd9a934d84bcf08,-0xcb06d8953408bfbe1f04507663aa4fccbc534aab]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 24 96 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 96 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 57 indices rho q28 m28 28 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 57 indices rho q28 m28 28 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [-0x454817facf6e99f5e929997117595dfb8360,0x19a23b323bd01086b6266260ffdfd352f88,-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r29 : List ℤ := raw_ints% [0x164ac2b1af501afcec17c8cee01ea80688b11563098b23d5cd570560000000,0x1d5ebbe4cde18f15aa7744f7f18497576d23fec588e95c1194343d45000000,0x1262f9432d283a1d2400cb6ed933d6f4bbd73c9a94c2e21cf15e6679100000,0x7474143ee525498e13a1d48fd9cff467d43f9489ab586ea86bfd328c20000,0x20b8b8d9a6a4804847a75000644cb3e8b3b17cda841854f7c98680b720000,0x6f1df2fa84ba7940cbf95df43dda24f74f5e5aafa5639900cae056800000,0x1281b21786197d6d69012027ebc5e6a993f094b453689fc28054b3a51000,0x27b01be0d233e4df776edff293a355fb23f6bb321aa332cf20eac2bfa00,0x45b00c24860a444b7d21b148b64ca7b2bba66cecd4135e05538a419400,0x6564e267f12599658faa6e07014f6ee8a3be3744256a65b078b98ce40,0x7b3cba16fc903a98f8090d2fa9dfc4fe107618d9233a90f355c7c980,0x7dc2720c9db0d824337480af1ddf3e7108bd3a63880c51e746837d0,0x6c0447decbbbb9335a2f52eb686d5df31962ddd036844cf091f580,0x4e19697f9354973b71e09bc5d03277da739cf05c7e7e341597f8c,0x2f6da87ddd10beca3d53224ca107fcb2920838bc5130b8eda328,0x18135cc3149f9b7cad7e00558f6319025c396dd0f0aac6252dd,0xa22cc230c8c995450ab97702c901e88b4454577ba1e386640,0x37f7a5fe6da5ec6fc77a0d0d76a095b7d9de65db08b70f64,0xf90c5b297c00b33fb15fb6c3506ede0348d330163e4f50,0x3671fbb82b5235f5d4ccdf70903ac8bde2174abff5f7e,0x90207d678f7458b0d16aa5a5e93e3e1f84188fdd580,0x10f6bf8c0254f1f3953ef14dbdf3afb4a4a4435b08,0x1440357db320af5dff4f5cd065c361e910088ec8,0xb84d86cde80571c6434d6e46a80591488839d]
def m29 : List ℤ := raw_ints% [0x0,0x8affd82417110e427ece55dc80000000000000000000000000000000000000000,-0xf76f2be37beb0549e475a135344298a6cc1294150aebffde92cdb792029878d100,0xd52de055ed2a83ad8e692ed11a452962341097741c87cc92a0fedfb353da53563c0,-0x7668e2569fa7dc57da5a364c51098d2edae1034818be94719b6121406d140407ce00,0x2fa758da66c0f29c78d9a30dde2467b55c75d26f100fb54100dfa8aa5cbb16cfbd030,-0xece4ab8755206c7f55968eb34c8af2147ea5427f37cb39f7220bfd21deb3e3e255780,0x3b1f2c940e9628431f1115ecade0a27a66048f5731683c4179bbcfdfe17fe2389bc0d0,-0xc2d14fcdd56211a91a1600ee3c5aaf0a6f2d5f58dd3e36868badef995c0676eaf04700,0x21c1828fdbbaa30a1f41689f585b7e4dcd36961cf372103a11f1b643b21bdce08a396ac,-0x4fdf3e301388dd1314d5fcc46e461b1b9fd87ff6054323f5b05ade34e4194c0d64d2420,0xa314ae7c57dd3fbdbd989480ef7ee6b2ee716b128a1576f78ebdd0804febe93e8f7c3e4,-0x121c6212d471298907d957475905a68238c56da27fa3c3163d02cc64fa21204442312dc0,0x1c31153fd856d1231c6e0b38551536c734f036cc1b2ab3091eb07289c2bdbf3d75553dbc,-0x26a4c080bc2479973d22ca044742cae81bb7ae57582abc12c586ba97dcfecba1349a2260,0x2ed5138f86547c56195e3871db847d6cd503421ebf1db007f2f898558c6e4e079f82e474,-0x325516fa28c6adbf9fd5617148a204c34fee6db1711adf360fbd619417152c2b8693fc80,0x3013e5607e4b4e16471168dec41b763c7c76026288dd40e2dd041d179ddb5dd86fe7775b,-0x28e095db553362a19f14de5c8980ca02f4767164b20d7ff70940372501515be349608708,0x1ef63695a10c961f04f5dc89d007c6932839bbcf7a2919d8dc3676c680c73641c1f91e39,-0x14e588487b3f7a76142ad2232cebc76b3fcbd1d712595822a05b8df7dc1088cf1bc23eb0,0xc900c78cf1bb52a6c5599894f7cbb5a63cd062d6dd492937b5231dd7d32e5d80b3a5963,-0x6b8a5615e9b7b72ddfc5ea45dbc3ea049d9dfc0bdf8045f00fcadf67c35e386a25ce678,0x3320ddf645d94cabaf6afb5c9a8cd3419fb93ee80dd0acacb23e7cc0f6199fe536c5589,-0x158e7fe60141fbc44271704571ea25b3f7e7a6e7f1b20ced5af2434e80682785fb05920,0x809d4980ae754eeae117eacda485d62288055ab05e80b508b597d9373da6b9b041719f,-0x2a46e8f3937c5d607ec4bf0c6d11f05e8375f0472554b0d07aa8bafe8400bb13b85888,0xc3369a2cdb283af1115d2ceae812e7403815a88687d48fdee77eafeadc6ff458a6db5,-0x3138fb7184839d04b08251c8b23bc40a447bafec4cd0991997a4cea22112a07255b10,0xac82e34bb612aaf00c29e6de314b87bbdc78df783322e3ffaae5be310d162ebf7b37,-0x209afc8e95d8bbb5180d4be623237b14567e80cbc5d4e2c294ec62518d7a098b9838,0x546772e569a9c2bd62fb3d18fe125634cb05b8a8794e25527415eb7fb48a3b48295,-0xb94a38fc18be3672cdd8ea1fbd59ffcc75ec5dad628a66f40d72418f23b40feb40,0x15529ea984e03b9e6b90b39820363ec34b267037953647f600c20beb1cbb03a0b1,-0x20808e925f99e80822fba9776daa9cdfcf0ddb785d4617641b59e80c0d2614dd8,0x286262b1815e25adc7b631d8487093cc9f8378993b7425cdc6da5499a20e10ab,-0x2826cd657016547bf6da9787688e0d5404c9d376643efe0a42aa264fb363ad0,0x1f3d234e81dc87e3b5c4095a6ae6a1f332e54daad1e94f973ef97dd623d1f9,-0x12828e3c212dfe744a33fe00fb5f2e03c33a7c1e1866a8e6fca09bbb98ba8,0x8141d0ba4e274456a45531f3589afc4dccfe9bf8883129b130b630e0c2b,-0x27dafc44f704fe3ad76bbe1cef6ad4ba7050befd3821340bdd9d2c8620,0x83bc07d7e7b8a491bc60d4cdb59aaef1d1a0fc04b3c7a7e03dc97d69,-0x110393fd91cb012aafb07570426c1972b78b3ef55b55fcccfeecd78,0x14060d88f1c49370c1c1e91928e36866aeb08def1d3fda7321a03,-0xbc31c4e313f3e0d04ad50d40658f95081baa1b7446893821b0,0x2d1f691707ef53184365bbf7933079c3d36c446ee4436dc1,-0x31e096837984c7f4627ce7a36c3ff59b49e78cf6f8bc8,0x7441973191672d56be991172579f1e15e1e75d833]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 24 98 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 98 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 57 indices rho q29 m29 29 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 57 indices rho q29 m29 29 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<24 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [0xb84d86cde80571c6434d6e46a80591488839d,-0x454817facf6e99f5e929997117595dfb8360,0x19a23b323bd01086b6266260ffdfd352f88,-0x952c85d14acbe1f6aa7b11e9d832a277c,0x35432c21d31342dc7192df68b063a6fb,-0x12a3cc16509473e395a22c86cfe4388,0x661f4dd312456fb51529df5769a76,-0x2225cf883c12587368847312c3c4,0xb2016580f4479e5e3620f7b079,-0x385ca0c3e56e4ea1e97c19c70,0x114ade8422606e7aef0d6584,-0x51f99f507a55142965d9cc,0x175c3db4d3e2602176c17,-0x65f570553b7bda0b018,0x1a792526c01544ccb2,-0x67f5608e6ee1cb94,0x17e9a4a710a55d5,-0x51983d3841080,0xfe8cebd7000,-0x2c89e65f1c,0x6d0456b3,-0xe082a8,0x16dae,-0x1a4,0x1]
def r30 : List ℤ := raw_ints% [-0x3b4d1d60a07e02249003d2f12222034a3b8fb1330e291818288f0b20d000000,-0x4e1bb52492245bd2cbb79487b1aecf209b541bde2fecefc2fa30b4ed1d80000,-0x30e238e5aefa0b9dddf09b930e080e5690eba1333d1d1992f35f6cee34d8000,-0x13582c837d04883c9fdf1761179eeffc7143658e43d1229aed6f8a96c9b9000,-0x56f027a2b719e15c685c772ab28d8ba2627f78ffc2979d43f51d284319ec00,-0x1271ed22607db5aae2f78e00c5b0a5579f8a01ea15268030abde4a7b36b300,-0x312231b3793c4edd49ea2fa022ebcf6df628523552d8ee7e9b6b10b6c86c0,-0x695329094dee8c156682b4eea0923e22a82bfa8d8cb3e644e16daa094440,-0xb8db9c1691d740ddbd24443aef74338019e104be91030929288fb719d30,-0x10cd69b3d7eacdb0e3b3b15d2e6bcdff9c10846a118678be126f5118bd0,-0x14697255eb697489df070b1443121bf1a25225f589dd72153425547f04,-0x14d18d9b4f38c55441007802d8aa779d848a875bdf06c00f67106684c,-0x11df059f53cb65c8b43449662de1cfe648671c166378f3c96062817d,-0xce9dbf0d16c13d8a518bff47f9a8c79b60f52ac0a8d50bd2df1018,-0x7d64841a2c316abab4a14d32703ef08b674528e2af8e57075564a,-0x3f9b839161a33e6f687b5e4bdef447be666406448e0b541fb53c,-0x1ac247c59fcd6d1104dcffae997f607e14a3245888fc8f2fb86,-0x93a2a666fa571a9ccb11d1db1a465bc5016fd4ba418ad60e0,-0x290645ad6fe263a6193e2213bad66af6d99feb3a759656e4,-0x8f5cc95165813e8046e13d385a78e6d1c58b5cfae44704,-0x17b207f606f9de18e96b918a109effc40b8d64c4302a5,-0x2c93426490dd621a68421cd1145a1eee85327029478,-0x35265f047caa67524a1b49b6832f42bea7d34a436,-0x1e31a73887df80c9146302e96eb494a665462f4]
def m30 : List ℤ := raw_ints% [0x0,-0x115ffb0482e221c84fd9cabb9000000000000000000000000000000000000000000,0x1ec4ca156193b2f51d5e78cce4a2107c32b63fee8c5293fbf3c6e93aae5076a14f00,-0x1a5db7867befdbb55aa38300b434e5b419b0dd536a942048fd3fc793808f701771440,0xe90164b5c0c6b24b715f6480cc114779e32f31349b9631f927a52d000665ea7644400,-0x5d39b7973019f6aab5e394ce51c9ce8b09f894e32d12b7b7a3dfc460aa570ba2995150,0x1cc9f3f47c1d46e6693cbd72d70eef994c0f59e381e8ab33bcc93c6167cc7a8fe156a80,-0x723b031ce08fd4d3d83c282b3ee47601a2910e8427fe7e8828899e05034d1385efa3510,0x175ed53c1186d64c500c8a133cdaae6f49e48c1ea840698179c214c34d7ad6532b7a3600,-0x4057fb94c3d1d3fa57a3e0d035f6213aa8f862b432ddffbdd3154f9c5ab0630177cb1d14,0x9726e83551c4ccd7d2a9dbc2f6122147c5f09607dcefaee3d854996bd3adf9f38f22f4e0,-0x1324bab4e926078322e3b0c98c94845b88171fe82f9fa33e8b72eb2dcd6ca7ddfa1d763f4,0x21bf5f7b4d0ce18ad2d03a8d0834acf8f9dd9d70745edecc8d444fe013c5586db6215bf80,-0x341934113f5dd681ba8ddab9cd5b1aef9e8b21c8a219ef9353e99703e2821707dee484fd4,0x46cb906eb3373b2ec3d7585749b12110edf7f0169fa3db3938ed056d69b550a91784754e0,-0x55045acd25b3272d07e338a5a4541bca04f73189dc726e9e92cebb53c0260cfd9983f0b34,0x5a7f608f6d8fb1b71c3b35a42fc35116d0350f4fe5e22704582e3b26c603e291050e85600,-0x5592fb353057d29a19645c3b65a2959a2af1d7c83dff99dff6374366b93ab9ee4fed30da5,0x47fc9b83ec8917e90bd38ed74583da75c21a459f6a96aafd7187e6ba0ab84fec8fdcd7478,-0x35ea4a9a4a9d6a5966b5e71435bfe76a09db9b25c963ec70eb27ab93681c3c7c4c5cb868d,0x23f54d13cb701e052b6ce702b506f51d7a7e6a5c41d2b74f8f7d0f9f59b0f47c6f32ecc60,-0x1558ddefe8083f72b80ef4c3981af05abf5765365d4b7ad18173a80e23f99a508897fea71,0xb450f8b382ededcd1d7f2fff2455b7db85d9d196fa4b4e6976a0b14760863b8420832918,-0x5485da44cf7649bdfd7cd0692293a848562ad962ec469cde64d6fd274d652a554c64d699,0x231a82fecc9ac5713277a894383862c5480c7c9e4879e0cc91a0a5e37ea8df77ea378880,-0xce1b18426c04b0ccc51173ca70f54858ccc0f44b32962ea456aa4a0126ce46333b7f8a9,0x42994c8949c8f75cb49d5fe171764c1fa6039c99ff2561fd0cf56fa37d70071eb941a18,-0x12df03f0e0eef12a4132e36509571d530653ab6a37d43ce46cd6d36f427c13e05287dd1,0x4aa76653c2012fa869d8875ecbe61203102dfe6d72e8a675910b7dabff4255c7bb70e0,-0x10030043b3e145ed8211d77668c68b7b61642a2fc7aa22c7b0e8d558abfddc1ccba7d5,0x2f55f4a0a4a72b144789899aaebc114cf5dc48e6908018004dfaf9fb72c8edb2f4038,-0x77941d0c09a01b3ce30f0c8e700790330007c3bab0ef7ceaa7c8927c9f7feae5ec7d,0xffab258ac005f9101a48b6d6ced961156ddf423e628285220c2f694efb85529da00,-0x1c97af736e56b4cfd73dfa398975ca37d04ac493e6259234b1648d9af17a7f7723f,0x2a4072262317a017638d64ab19970d073edee74d3f21905ef53db64240a6545e68,-0x32c15d946edf935d59ef3299db8794d56191422e122badbb8d32b4ec6eb777b77,0x30a38181b614c2c809a72239310224f871f5863f611b8d11f77f1c5f3ab5e220,-0x245981beb58eeffeb5b2929e1e5f592bcd8b4101371f9625ca89f05a3771773,0x149c236d6e909af57dd5a29f0d106c853a1652487fdd407d2dbecff4a86ec8,-0x892127dfcf35426443afed135af90d2a7e188226f1fb367e93ca8b6e626b,0x281867934a1930868007f18fd1773a83840d060e742c5ff4b9fe8dad180,-0x7d00b24059674517e8605d5c5f92ffcfc77aa3d14b52fe0d4e948901f,0xf233d56967dcd94955951c8e6b049dfe3ed04e718f1aec16a664d28,-0x1098184878810db9d48227922531bcbfad454af5c403f2b1021db7,0x903329f929483c7e3f1f09ab187c01ff1773bf29e1957871d20,-0x1fb387902e4233295d6bfa4acfac4dfc3e77b1d66c3a54f63,0x1fd24fecd58c3fc54189237e59a63335c44934da27ea88,-0x428f4054ef974b47f570490cabc74f74e89d71c47b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 24 100 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 100 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 57 indices rho q30 m30 30 5628105466793884649407472640000 32=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 57 indices rho q30 m30 30 5628105466793884649407472640000 32 24
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<25 at hj;omega) moment_ok_30
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<31) : intPolyRF (mz e)=rfPoly (C (5628105466793884649407472640000:ℚ))*rfX^32*(1-rfX)^24*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V9C33
