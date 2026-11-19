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
namespace CatalanCore.Li2.NVMod.FamilySource.U5C23
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,5,23,size⟩
def bases : List ℕ := [1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def num : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0xbadbd721e35c30000,0x10f1fcdc34c8441000,0xb7baac2fd31263e00,0x4d48b8b91ed3f1e00,0x169e63c6339cab720,0x4e46efe187ea23d0,0xcf8813c4eac4420,0x1af193ecd8fdb58,0x2c771f20ce7d6a,0x3abf71e6f8fd5,0x3e4d00ab1949,0x34ea8f6690c,0x23bcfd15c8,0x12ef93efe,0x7b31d8e,0x2519f4,0x7cb6,0x105,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x1,-0x23,0x7,-0x4d,0x625,-0x4fe1,0x18f65,-0x4fe1,0x13a3c,-0x5377f,0x9625,-0x7f5ad,0x65e24,-0x19789,0x164c5]
def rhoDenominators : List ℤ := raw_ints% [0xf560a900,0x57fa80,0xc918,0x507,0x8f0,0x28,0x3c,0xf5,0x380,0x6c0,0xb4,0x1ef,0x7bc,0x11e,0x1b5f,0x3aa7,0x4100,0x22880]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 24
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤23))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤23 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 24 omega6=padCoefficients 24 (omegaCoefficients 23 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 23 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 24 omega7=padCoefficients 24 (omegaCoefficients 23 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 23 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 24 omega8=padCoefficients 24 (omegaCoefficients 23 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 23 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 24 omega9=padCoefficients 24 (omegaCoefficients 23 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 23 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 24 omega10=padCoefficients 24 (omegaCoefficients 23 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 23 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 24 omega11=padCoefficients 24 (omegaCoefficients 23 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 23 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 24 omega12=padCoefficients 24 (omegaCoefficients 23 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 23 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 24 omega13=padCoefficients 24 (omegaCoefficients 23 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 23 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 24 omega14=padCoefficients 24 (omegaCoefficients 23 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 23 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 24 omega15=padCoefficients 24 (omegaCoefficients 23 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 23 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 24 omega16=padCoefficients 24 (omegaCoefficients 23 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 23 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 24 omega17=padCoefficients 24 (omegaCoefficients 23 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 23 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 24 omega18=padCoefficients 24 (omegaCoefficients 23 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 23 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 24 omega19=padCoefficients 24 (omegaCoefficients 23 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 23 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 24 omega20=padCoefficients 24 (omegaCoefficients 23 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 23 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 24 omega21=padCoefficients 24 (omegaCoefficients 23 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 23 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 24 omega22=padCoefficients 24 (omegaCoefficients 23 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 23 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 24 omega23=padCoefficients 24 (omegaCoefficients 23 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 23 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 18 li0=padCoefficients 18 (liCoefficients 17 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 17 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 18 li1=padCoefficients 18 (liCoefficients 17 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 17 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4d,-0x111,0x27d,-0x3e9,0x3e9,-0x1ad,-0x1ad,0x3e9,-0x3e9,0x27d,-0x111,0x4d,-0xd,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 18 li2=padCoefficients 18 (liCoefficients 17 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 17 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x1b,0xd,-0x15f,0x507,-0xa9d,0xf15,-0xf15,0xa9d,-0x507,0x15f,-0xd,-0x1b,0x9,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 18 li3=padCoefficients 18 (liCoefficients 17 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 17 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x1,-0x37,0x177,-0x4bb,0x8fb,-0xa03,0x483,0x483,-0xa03,0x8fb,-0x4bb,0x177,-0x37,-0x1,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 18 li4=padCoefficients 18 (liCoefficients 17 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 17 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xf,-0xa5,0x235,-0x267,-0x549,0x176b,-0x289b,0x289b,-0x176b,0x549,0x267,-0x235,0xa5,-0xf,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 18 li5=padCoefficients 18 (liCoefficients 17 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 17 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2f,-0xdf,-0x111,0xf9d,-0x2ced,0x3cdd,-0x1dcd,-0x1dcd,0x3cdd,-0x2ced,0xf9d,-0x111,-0xdf,0x2f,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 18 li6=padCoefficients 18 (liCoefficients 17 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 17 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6f,0x93,-0xfe3,0x3051,-0x21e1,-0x6605,0x10c35,-0x10c35,0x6605,0x21e1,-0x3051,0xfe3,-0x93,-0x6f,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 18 li7=padCoefficients 18 (liCoefficients 17 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 17 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xef,0x929,-0x2e59,-0xb4b,0x16d3b,-0x2d193,0x193e3,0x193e3,-0x2d193,0x16d3b,-0xb4b,-0x2e59,0x929,0xef,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 18 li8=padCoefficients 18 (liCoefficients 17 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 17 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ef,0x2b6b,-0xdbb,-0x2a0b7,0x56727,0x15dab,-0xe32fb,0xe32fb,-0x15dab,-0x56727,0x2a0b7,0xdbb,-0x2b6b,-0x1ef,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 18 li9=padCoefficients 18 (liCoefficients 17 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 17 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ef,0xa331,0x2cc1f,-0xb09f3,-0xa279d,0x3ad6bd,-0x29186d,-0x29186d,0x3ad6bd,-0xa279d,-0xb09f3,0x2cc1f,0xa331,0x3ef,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 18 li10=padCoefficients 18 (liCoefficients 17 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 17 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ef,0x22c83,0x1649ad,0x37581,-0xbdef91,0x6e3bdb,0x171dbd5,-0x171dbd5,-0x6e3bdb,0xbdef91,-0x37581,-0x1649ad,-0x22c83,-0x7ef,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 18 li11=padCoefficients 18 (liCoefficients 17 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 17 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfef,0x70c79,0x7ea257,0x1b1aba5,-0x2986fb5,-0x7be17f3,0x81f1d43,0x81f1d43,-0x7be17f3,-0x2986fb5,0x1b1aba5,0x7ea257,0x70c79,0xfef,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 18 li12=padCoefficients 18 (liCoefficients 17 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 17 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fef,0x16345b,0x2736c55,0x115a04f9,0x161b7277,-0x3ca401f5,-0x4918075b,0x4918075b,0x3ca401f5,-0x161b7277,-0x115a04f9,-0x2736c55,-0x16345b,-0x1fef,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 18 li13=padCoefficients 18 (liCoefficients 17 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 17 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fef,0x44bc01,0xb494a4f,0x81e7e37d,0x1d6c4cdf3,0x12176ab5d,-0x385b1a30d,-0x385b1a30d,0x12176ab5d,0x1d6c4cdf3,0x81e7e37d,0xb494a4f,0x44bc01,0x3fef,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 18 li14=padCoefficients 18 (liCoefficients 17 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 17 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fef,0xd272f3,0x31b9e43d,0x34dfa1bb1,0x146d75993f,0x309229223b,0x1fb33ebb75,-0x1fb33ebb75,-0x309229223b,-0x146d75993f,-0x34dfa1bb1,-0x31b9e43d,-0xd272f3,-0x7fef,-0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 18 li15=padCoefficients 18 (liCoefficients 17 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 17 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffef,0x27fd7c9,0xd4e9b207,0x13e13cd395,0xb619b7b75b,0x2eacce53cad,0x5ce1c766ea3,0x5ce1c766ea3,0x2eacce53cad,0xb619b7b75b,0x13e13cd395,0xd4e9b207,0x27fd7c9,0xffef,0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 18 li16=padCoefficients 18 (liCoefficients 17 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 17 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x11,0x88,-0x2a8,0x94c,-0x182c,0x3058,-0x4bf8,0x5ef6,-0x5ef6,0x4bf8,-0x3058,0x182c,-0x94c,0x2a8,-0x88,0x11,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 17 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^17 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 6=>omega6
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 23 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 6 24 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_6
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
theorem cache_li (j : ℕ) (hj : j<17) : coefficientsPoly (cache.li j)=liNumerator 17 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x5c575c56544a41f79c3b29c00,-0x98b4d56536ff2a36b5f37bbb00,0x79c083bce45bf260c75a989e980,-0x3e5205a0314eed356007f3a466c0,0x1701f014b9e610733813c6f0d67e0,-0x68666ae50d30bb3f4867e42b7e6a0,0x17a78e563601324ec0fe6677668680,-0x4658612c73a50b55e235a3faf9cc10,0xaedb9d9b9c215a78c703e24a8766f8,-0x1705169477c00521feed1b8b02a7b68,0x2982c8ddf7b69e2941e38a942f7f440,-0x4092dfa2aa4fc9bce05fb1925f505c0,0x5724bd48bfab1222a80542fdacf6800,-0x666fb1cd0f0f8bba0e04d74b6427b80,0x692ad2832295532b9cdd5e22e80fec0,-0x5e71492a34303cbef6969a574aaca64,0x4a371039fe0e7f19338275d055c0e7e,-0x33001fbd36c34cc64d1e6cde6065c5a,0x1e98b5a23d5ead9423b5fe43b9c27b0,-0xffab2f07ae9c868bf0fa16f8991280,0x73c4a0de2ff0a9d63a617e4106dd68,-0x2d339d20c6fa8016a07dd0014416d8,0xf1c485ebc994a62733fe5c29dee10,-0x44908b015164c4c173465abc409d8,0x104d9c02a7718ab1d6a72b5ed642c,-0x33387a76f233a1047ee8624821a4,0x8248789458406905a5d064f9190,-0x1054823a64b69ec80dc8dc49c60,0x18e6174e9a2f6f55f3575b4488,-0x1b64915f8ce0eeb3eddf66978,0x14141681745de76b73b9bd30,-0x8950b3ce546b0af996a7d4,0x1a746c721b99adf3fbf8e,-0x131038db68f115dac2a,-0x4108acf8fdb2600,0x190356386193600,-0x72586594073400,0x16de7ab734a400,-0x2dbcf56e69480,0x2b0c3249cc80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 18 32 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 32 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 41 indices rho q0 m0 0 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 41 indices rho q0 m0 0 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x84bd94bc192abed3f0950c0400,0xd8035cb5d1a2b5dc2da7a91c700,-0xa9695107e26dd34f1d54ee2a9600,0x55433c815bd444717e98366d1cec0,-0x1eefb5b8f03434d30fd189a9d2bb80,0x89e68104242c6fd27ee99707d60cc0,-0x1ead9797af857186f085884bd7c8200,0x5987a2ebb544bdad8a6ede8169095f0,-0xda44addc1d5809861d14230cded66e0,0x1c2a5c1f83fa609b235e9954590d4a70,-0x31c03e625a51aeb910b580342012df00,0x4bc17ea7ed5fbeeed56383ed00ad2c80,-0x63ff3e5aad709d3246362300ced4d200,0x72e1148b49a53fba09d63288d2a2c580,-0x7329f1e965af2fd389f77807eedda100,0x64e2a61614bf91a2c53d2a36b11a08bc,-0x4d40b2fc096836df046703dd91b729b8,0x33abbed51d29923f70404c87925c24dc,-0x1e21c75fd68c17d9f6ab4597e2802240,0xf4640f83a0384e4ae956c6caafe86b0,-0x6b3c5f0196da52676c37bc2ced3ce20,0x287fcfb8b72edea429388b83a8a2770,-0xd1153fd616fa3f98e2b900830a2fc0,0x39182903239689ca091b6c1e24f578,-0xd08eea5faf9002510dcece2590fb0,0x27307314a894280b5e025f44f29f8,-0x5f013affe8347341c072d949e2c0,0xb4b28c38caf8b47e083bb6e6fb0,-0x103ab494537b850c939417f83a0,0x10b14affeae5d84184506e3bf0,-0xb5070a908a75ff1ac837e740,0x46719a35aaef74ddb50ba3c,-0xc10d370174068aeefc878,0x7727b5b48a481d02a1c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 18 33 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 33 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 41 indices rho q1 m1 1 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 41 indices rho q1 m1 1 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,0xbed085ce642d7250a9d64145c00,-0x131b406f54ee5460b1cc449105d00,0xebf0bc77083bb84eb3314eb34d700,-0x74cf14d537ef8379e137ff1df64040,0x29ac312856b7134db055ee7448ca4c0,-0xb68f6ee060ce4073bd5700a12256580,0x27e4ebef48c49bb827d2484bec7ac100,-0x724d8edef563d33ae3a8cb53863f0390,0x1116d0334fed2c75662a30094a031ef30,-0x22993d24eb9b5b3260cca10263e577a20,0x3be3a4c130dd24631bda96d4070f25480,-0x594d4812c4330bc3f29c2a4088d7cd100,0x7358102f023bdaec7c7d7d3e1f7c77c00,-0x818dcde1b21bbde7b59b7d4c219f7ca80,0x7edcbab42a4290c46d2ce3e578e896180,-0x6c729d29c452dbcd320294c7877b3f864,0x50f2d484dfa1fc89daf67f3ee631dcacc,-0x34b6a88d91cf129dbf53de9fd508f8e48,0x1de3776ecb93083837ff6b34e671d3760,-0xeb5a0040a1af05f9a1b28d547b051bf0,0x6417909006b900f6dcd01f6b79e40610,-0x24919cbe61bb5093186dcc61a72ca5c0,0xb63d8cf06c470fd6cbb61bd5ed77820,-0x2feae571ed7167e48b95c77a4326628,0xa80c5c742158387d806f007c3979f8,-0x1e362db57dff4e242ccc1c017ed370,0x45c816864daeba2b0699619807d20,-0x7dcede724029f068d95bde622c30,0xaa44bd17ddcd61460f6a4e22650,-0xa38f3ea45132940337a1f63200,0x665fd4e6787615c1976f3b760,-0x24345f2af21ac64c6f000a84,0x580bbb278e378c074ff0ec,-0x2e8176c4e5db0ee5f968]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 18 34 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 34 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 41 indices rho q2 m2 2 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 41 indices rho q2 m2 2 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x1124bc058b0015453f423fdd44400,0x1b0d3ae528d89398a0eaaa93bd0300,-0x148e3a8e5b97ce3bc8916e9e6ad4f00,0xa03dad53014e13e9b3b6ebc0572a3c0,-0x383c10e938a82313e66effb86e165ac0,0xf2380def1fb904e39678eee3b5a7a400,-0x34043477cef538b570d220b15e692f900,0x92614318af672a378627931bd187103f0,-0x157b87e0e314e12705f3a4fdbcda60f4b0,0x2aaade69dd2cb6d44ee65190ebc6ef8640,-0x4867b457add278031cd259be3c43f91480,0x69c455c2c3b5c6e25f33289c25de99d400,-0x85b9bd895d81e2157507007c2db21e7800,0x92e74a477275753085dba780b83f0a8d80,-0x8c9071ffb5619fca118d1ea1eb35866980,0x754be51bd7655f183c52b2f0ff7a4798fc,-0x555f1b48e6ceaa1d99338813654583202c,0x3624458d1dd0d447d5a6cba453d1994cd0,-0x1ddb125eac7ea4f535761fed666502e960,0xe44ad51735b83d564efd51da1880c8550,-0x5e1e8ef00e16282e08074e995cab64590,0x21450d486433d3e3dc1a831420401cb60,-0xa00e8dd840479ad70bb5acb608bb1c20,0x2885be03c5a6902491f2cb88cf4b6fd8,-0x886cf8688aa46d9a2c93351478eaeb8,0x1775f98c627a390ad6f9ced1fa31c80,-0x339c77cb4770662353340773806f20,0x58276cb0fccd1b5482c441820ea90,-0x70476c23b4b33248a72e84df31d0,0x64a06776085fa1233410d1d99a0,-0x3a155d6ff153f43be2ccfcc760,0x12a301701637b8bd81cd0599c,-0x28265f1693e59653befac4c,0x122302ad1caf9b13328f0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 18 35 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 35 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 41 indices rho q3 m3 3 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 41 indices rho q3 m3 3 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x18a4ce47f7d01e938aef3bce121c00,-0x2651584875020c5625264038de1b500,0x1cadbf3d385c1d79341ce00217d5ed00,-0xdc1c8554905db979d0aad758cd87ca40,0x4c049c346671b3abd0824d54408285040,-0x14212fa4af5fc100eba0952f4edf713500,0x43ffaf86cb451043165e7701f45cfe4b00,-0xbc069c9d54cbedaed8ffde279997f1e690,0x1b192cf6cacfcd87ec9cb4729491a78be10,-0x34d206921dab1a33ddb93d3c91cb2ce8600,0x57e86eb7c8544f6e94528ee4a747011c580,-0x7dd90254891f42aee4a6c87a97af2404e00,0x9bcffa72b3c490c46819d05011655b57c00,-0xa7786bf9c364a53f23c7bf05f00d4e3c680,0x9ca2c20dc79e0256800700395e846bda480,-0x7fa21dd3536dea33d861e5dc76ee1997ba4,0x5a9b6d8cdeb584b4e4f011756f8dcece384,-0x37fa06b9cd370bad40035e7dd1ca95ba440,0x1e071ba2cdcdb2d55d61ceacb21577dca20,-0xdf03041863160e0b0f1e0dfd02844b1ab0,0x5924e124dc0acc4ff0db6ac21410406ab0,-0x1e7daf661aa5de791f634b159d407c3260,0x8d9d6872034dab2b8e7e77b8a0e832a60,-0x228584fe9035cf8b8f36eefc4afb49be8,0x6f8ee1ef0f0361a0d7b812a318547428,-0x1258bb1830bf1a8b14d800875162e320,0x266d21e175b11494d4e2aaae421cf60,-0x3e259c5cfd1f1670685601b7e99470,0x4a6f40d41149ab7e1597d12af2770,-0x3e2cba3db93612bbf00abecd0520,0x210d4d496213a519c306d06a020,-0x99b3b0a7540e689c551731484,0x124dff0cc6522f31d88d69e4,-0x7115cfcb497f1b43730a0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 18 36 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 36 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 41 indices rho q4 m4 4 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 41 indices rho q4 m4 4 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x236ce887743b2bf417b7e5f83a08400,0x364ca1e2d659aef69a6bbf77ed14e300,-0x280bed666c1a4a7f4fd0b2b16941c8300,0x12ebe42a57db08106c5f3e3e03e4d2e3c0,-0x66f02e951da18a6f58d5110dd30656bbc0,0x1ad2cb05d3ced8c4f3278282a65c1f62900,-0x591e98ada9c003071c3251514692d610500,0xf23d04f86bec4cf9ac2dec8ae6179d57ef0,-0x224c33933ac5e2e56b5559526b6196afc4f0,0x41a2de4a5227aed50ec5e25b114120596380,-0x6b2caea4fd76123f402871adf5ff4899a280,0x966bc6df895bc314331ba6e11f122d6e2a00,-0xb67028fe906fade77a231876d96f57a6a800,0xbfebaea978717c2527e2a2d346ef4f879580,-0xaf8564a825ef1297e759a2b669ec9efaf380,0x8bb3973a2da7c7e3d0c4878f3c7ee5283cbc,-0x60c297c5b06ef09b92f1362992f1faf62e3c,0x3a3f813c2b8f13db0e40909ed848ac9b1820,-0x1e6733ed342268bfdd3da580c2946623d7e0,0xdb5b26f294f4dac1845569458c397729cd0,-0x5506eba15c514b9c78f9c7a09c89a7bfe50,0x1c24e27c8b80c6dba7216f588e999fb3720,-0x7e32c19d247136e4bc8f1269c0a54d23a0,0x1d9e97b0928f3cc72ba9fb1c12350d88d8,-0x5bdcf1b167b1493a6baabec18eaff5d58,0xe71ba6096fc539672ba5400b47d207a0,-0x1ccac07fca9164a25d93e28640d9c6a0,0x2c111cf8a8f08fa53bb4aec137d5710,-0x319810767dba77b2a16768b5a25990,0x2691d03c1ad94aae0e12434486860,-0x12dbb4b0a1826d591d8948d1b9e0,0x4f50c02ef8a832051a3f9c5fdc,-0x857bfade6ad842af023bd5dc,0x2c0973ea52fe7c7c5695c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 18 37 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 37 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 41 indices rho q5 m5 5 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 41 indices rho q5 m5 5 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x32ec8e42b7150f2ee2185a94d36bdc00,-0x4cfabecec3962fb34ce16f90e3c8c2500,0x37f7e1ff0ed78a24068f8088adfb7c9500,-0x1a0ed45246c84882ed375191e68c7284640,0x8ba0b769fcadf5110462b6be8aca8b86240,-0x23d18682c52cb7b960a99c90c076edce7300,0x7518350c661dc1d105ba8b3875d21991a300,-0x138fe50c8f9593989eef9b7bd6f5108a2d790,0x2b8dbe60460f73a3a82646408e528e21df290,-0x51dd22814929199f9d7b672e08b448fc9f180,0x83329a1336db431f1a3c4a5784d56c70e0180,-0xb497ee525a824708c7e03339f3b2506a2fa00,0xd6a43164182dc5cc1cecb7c942b4cfb16d400,-0xdd12e1d99eb2fe906af805ec6296ee2957e80,0xc5c2b3f8245bfd5dc68070754460bcb325880,-0x99cb8466bc2d96cda88c9edce292ff73097e4,0x67f51ea5ab402b0159611ad0ba1bbb2d522a4,-0x3cfe9c86ce9d3ea3794688fe7c5dc99065720,0x1efc0a89abcfbec201820137ebd34c9e7b720,-0xd93617aeb3a298736c544099a043b2fa84b0,0x51a82a8ae93f979005a03d685b75df4b8830,-0x1a288e429daf9645d5f4ac8cae8d0ba0f6e0,0x713e81305577d2d67677d27818e2863d960,-0x1996de841e0df6b3c136879099e40f8f368,0x4c28308102745d083e765277c1d1e06f68,-0xb7224fdeb8365d21d7463558c873841e0,0x15b469ad9aae9d125bfae8e2d6083ee60,-0x1f6b49eac9449216dc6654b024b82870,0x21331444045112691dccb98cce3aaf0,-0x1803c2ced7d87c581cfd42d71d0fa0,0xac91f3918025fad97c450238a520,-0x28f7b272523821fcbd6669a79c4,0x3cd117fbca65090039fff8004,-0x1122f8ffea90d7639f88e80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 18 38 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 38 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 41 indices rho q6 m6 6 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 41 indices rho q6 m6 6 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0xbadbd721e35c30000,-0x10f1fcdc34c8441000,-0xb7baac2fd31263e00,-0x4d48b8b91ed3f1e00,-0x169e63c6339cab720,-0x4e46efe187ea23d0,-0xcf8813c4eac4420,-0x1af193ecd8fdb58,-0x2c771f20ce452a,-0x3abf71e6e8ef5,-0x3e4d00a92115,-0x34ea8f437b8,-0x23bcfb8c03,-0x12ef88888,-0x7b2e4d3,-0x250e3c,-0x7b2b,-0xe7]
def m7 : List ℤ := raw_ints% [0x0,-0x49340c7fe72e45d365030235efeb0c400,0x6d2dc0ab2a692254db011154760959d300,-0x4e49276748560d8b0ffd7601ac2b61b4300,0x23ee575b02770ac3e8152f1a36a8736a2fc0,-0xbdb5b4a3a9ed12922d7066289b9a726a2bc0,0x2fedd5728f9d70fc074edbce847fb5cf72d00,-0x9a3b4eeab9f9c49c50e9b806681e55ecfc500,0x195935ae0c3630431a0cb7ec50d49a3156bdf0,-0x377ce3bf5b597781c0c2981cc4b1d871e360f0,0x6679959b3e702040948ba40370fd91ddf3f880,-0xa13fde04f2ff9d366a91ee92d7e63577964280,0xd9c3f8ac8475208f623ef7b6b5448a74d32a00,-0xfdb8584cede33f599b26d045d89543fa127000,0xfff0e8df3096c37e14ab4d8023b7596a764d80,-0xe0035d15d59de18ff32cbfdc4c7c1cdab41380,0xaa44b4b001a5b97d45e105aab0feaefc34ea7c,-0x705a453068073e7fcaf9679a930e18c23db73c,0x4043d39a51220a69a50b2e496ed998af848960,-0x1fc7586acc8f28c491aec85f4acf3979fef7e0,0xd87f87836a7f7bfe454e6f0519f838f9fabd0,-0x4ef1d4a93597f9e319e6265d650adcf4df250,0x187a28a7d719bc29d9a51fc3155d60c01b820,-0x664eb28d3157ead78c537637023b02d1b3a0,0x16416ca47092cc74e963b9b47dd5aea96058,-0x3f8c6d82bb3a0d41d0edd844d825a9ec758,0x920689532fadcf758bd1d6ee4e1eb79a20,-0x1075170168296a7801ae611fd09675a6a0,0x1684c7caa30df4452e2b7c63607214610,-0x1652c0c4abc8ed38c311f8118f796590,0xf00d6f942794bda09f07a666501960,-0x62e901e5134d267b5f9b37f9669e0,0x152d21ef1b219cf1577aafcb919c,-0x1bb290e86178eb359e55054edc,0x6aa01ae453fc9bbad83df00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 18 40 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 40 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 41 indices rho q7 m7 7 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 41 indices rho q7 m7 7 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0xe7,0x1]
def r8 : List ℤ := raw_ints% [0xa89c5f1f94282f50000,0xf3ead6d41827fa77000,0xa4ba5191642913de200,0x4504e402dafe2cdd400,0x141ba34f1f738ac1fe0,0x45381c381e6a7b9990,0xb65f5ad8975875510,0x17807466f2e22a848,0x267063d7ccc34f4e,0x323b4dd55dc8409,0x348b847bf541ea,0x2bdad75afa8bf,0x1cf0df6a6fc0,0xeda5ec4b2f,0x5c3a7229a,0x19c78659,0x4b79fe,0x7058]
def m8 : List ℤ := raw_ints% [0x0,0x693ad1f7dc52845fe134532d88e1e19c00,-0x9ae910bcb8b0d64641fd6a3929bf7c8f500,0x6d97b5d8b6750066f7b572d2b3424f5c4500,-0x319b209c2220b6c9e9df4dc4ec33bf9ab8a40,0x1022d4955988f61bf8d3b106f5366ccd5f7e40,-0x4043ccad7a16b63e894ccb40d1d543749f9b00,0xcba3f64f7def6d029e678dbd43ac2128d57300,-0x20f06149005a6d4847497b91e0cd8f877189090,0x46eb0d662d3f38494fb328be53989eb17669990,-0x80bbc1cb48b0c06e172ee0d0f2f76da2c27a780,0xc6f6e7a7bcea81516d40cc6fae33d23f6160980,-0x107b6cca40f36762bf6fbdf32b5c4f3300388200,0x12d4cf17d3155b186ce2454eba5165714e48ac00,-0x129c60f3b3fa0fabd3d1b8c53bc06c6d91f3c680,0xff157fc369658f34961d491b0fa5ac6ff82b080,-0xbd8cf2ffbbfebb4d121821be9fa381f48daac24,0x7a215189e7f44911fb59325b6224e39282bda64,-0x441e8b97a0fedcff224f52e60609774521db8a0,0x20cbe424d32f94bfd4ec15b3cd1184441d12520,-0xd92af749d77b7675597822d8af878a70ce63b0,0x4cd1ce1e70c2d0010578701f0c4e479bb7bd30,-0x170df68c3e2694c42be1000ecde0991a775ee0,0x5d08ab2c1aa99540512f96a1a1243858b0360,-0x137b48ca26d9f08392b98a1ef8799c957e1e8,0x355c9582eac2ebb364c45ae2f81de809e4e8,-0x7522aab0a9168371528e50f7df481a3eae0,0xc8c501236dacaf1928a302136e93ab4860,-0x103839f10d25d3623c969be4735a956370,0xf128decb34e0c2d92e7304e436e25bf0,-0x96719c79d0bf7e8164289d626076ba0,0x38cca43d16d9ede221ea1f01987320,-0xaf3e018a3a2d944c5ec70a84b804,0xc9bccc118765f56f067d2971c4,-0x2970074f25313a5aa777ea00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 18 42 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 42 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 41 indices rho q8 m8 8 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 41 indices rho q8 m8 8 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x7058,-0xe7,0x1]
def r9 : List ℤ := raw_ints% [-0x520069b0c71e7cb080000,-0x765280950d0801b708000,-0x4face8a948b07209de000,-0x2145a77eebbb299946e00,-0x9a80d34ffdb4aaff1f00,-0x211837202f05ef7b2fa0,-0x56bf5da9707fe89d170,-0xb1c94679fc23e29130,-0x120b5f4a9e6fb6d428,-0x1760ed66b788351ea,-0x183365e5c0041d0f,-0x13f017166b41a36,-0xcf14a3ad75401,-0x680451d25790,-0x2735c93fda1,-0xa84748946,-0x1cf2f837,-0x270fba]
def m9 : List ℤ := raw_ints% [0x0,-0x97448dd44cb69e49d3bb379174c4b450400,0xdbe31040759d8cc9e0b89e7fd41c12c80300,-0x998b1cf15803cc243fafe51c3cf1af265b300,0x44917a760b29437281d50b23010af80910ebc0,-0x15feb1741717e382d64e5ddb14e49e9609eb7c0,0x56572fe37611ed24d7f150df8a951f1f1b94d00,-0x10d84cc71d26a8dac0e0e604cbaacf19aa03d500,0x2aebb92ba80ced3872dd72e701cd409f7ba7bcf0,-0x5aec849d1a40a53093dc144a39dbaa9bca5063f0,0xa2497c139be6759319436bf400614f261f1e7480,-0xf672b2f0a22aea0231ad5581899f174d3c026a80,0x140b330b7e9fd0a92c4d3371172057ad704111200,-0x1676d103173b65bd18027e5a09ea29f1d206cd800,0x15c1fa94ec12ec67ebbf141b47b48c97628340580,-0x123f59b94a863a903c77e67f5fc1214c56f354b80,0xd429343e0265ccdfd145851828a3531306262c3c,-0x85831e171752a7f5713777b8c4ebc388ad34c9fc,0x48a1829d5b1d07db312d6c9b6c8155f20d4c4460,-0x220d8e86ed00b13f3b00ce14f6227e87ba768de0,0xdb32ffb9aa6360f8a133fe0b8b7988e7ce538d0,-0x4b39d8730c65fe72aef9f3ae072cd9dd89a3b50,0x15da789af9a22b8b4d0d9756f2ce38c72ddc620,-0x5523dd52415368e5359e1e1b9e514da6ecf5a0,0x11290c1611536c0f8ea29e58fbe2e4df5299d8,-0x2d147f29b9b62e0e19d2f4a6c00c8219e4ad8,0x5e80b2d028aa507172b200106ff28ccc5e20,-0x99e46277a276d3c4050b4f286660bfc38a0,0xbbcc98a7138e834e5ef4e255dfa95f3f10,-0xa3763d195dd31cb6610fc741baaf64a90,0x5e8e4d5790ac7501fc688939bd6f6b60,-0x20ac0ed260e4f18a76c47276f313fe0,0x5aadbc83d30620ebd9f198046cd5c,-0x5bcae9a8f75b5a93d939a55339c,0x1017fef8a45305af37c849c00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 18 44 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 44 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 41 indices rho q9 m9 9 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 41 indices rho q9 m9 9 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x270fba,0x7058,-0xe7,0x1]
def r10 : List ℤ := raw_ints% [0x1c82f86b7eedfce7cae0000,0x290c7fc939d268c235ba000,0x1b9267286c02e2a49fa8c00,0xb7b26a53378e8383ffec00,0x3523f42a00c2aa2a4f7f40,0xb571cbfa437ca41e81620,0x1d98f75303ba5b28c2fa0,0x3c5b5e69bf8f343db480,0x61717c0e502e6a3c3d4,0x7d6104c4b52038279a,0x80b800aa1e4675420,0x68fc5ab173ffe9a9,0x434fb270eec711a,0x21494b19a3528b,0xc4be45ae739c,0x335df1229a7,0x882eebcf6,0xae0106b]
def m10 : List ℤ := raw_ints% [0x0,0xd9728be12e46838a205d1fe117dac3335c00,-0x1383df2a045bd9470e99859d2880a789f44500,0xd74a7b09096ebeb04b8f890754222585d01500,-0x5ee43d548eb940eb11cea53fae6b291d4a62e40,0x1e073bffdfbac0af4dd649839f974d9c974ec240,-0x743a1ad7d8b7b8687f8ed5a9403ece126f262b00,0x1658b1c8e9d122e8b0d2c6051f6ca5d8623232300,-0x381447973e1ab3c17e801cc21d255de4cf597b990,0x74ee9e81fedaa13f3acdfea5970b2224033280a90,-0xcd4a1569ec0b358dc6d87265518b2c5d62015b780,0x1326b4e0319b5aee2a3cea30d120baeb35b6534180,-0x1879b7cad92cdb800275c1e754468143fa345f7a00,0x1aeabaee7b40e674fe967a7f487cdf278952188400,-0x198ebef19b6222da5a7100c0f400baed457e234e80,0x14fd9c584e6f9a279f736924bdc75280b97a339880,-0xeebac888051fe757fc4a45dad1ff462a0e71f1464,0x92c40815f9e8f7431e39ec857e301a493a46ef4a4,-0x4de35af587b9176ee76700703f55b18dc4b4a00a0,0x239167eb6d4ed2a0fa4aa91862a152fa59d2d1720,-0xde98dc9b742cf4a660165149b0413cbbebeee6b0,0x4a1ef236ddd4999051ecefbe41849ebfaad4d030,-0x14d7f97c35c3efe82129e420bd8ef6665dcfc4e0,0x4e65e7efbd4f238ca56e2ef539cb0a898d29960,-0xf351c399d64bd3f66188eecef1a5b030dfd468,0x264e957a744f3880814488adadede32cf7c368,-0x4caa3c66fc1e70adb5f384462d2d412da14e0,0x768ecbe4a609c88854448ccc5489bb4f0e60,-0x888161f2faf2bd426104cbad7ba390b0a70,0x6f32e9b5266c2c225ce85f362db55342f0,-0x3b95edb1c34e136615b6e6d530445fda0,0x12d247da4782d50b715eb862a0bce520,-0x2eefdd0d02c0e30cd97c77b3700e44,0x29befab0eb8b26d7cd174bbcd204,-0x63f2d2d5f9a73fd3a82006800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 18 46 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 46 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 41 indices rho q10 m10 10 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 41 indices rho q10 m10 10 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r11 : List ℤ := raw_ints% [-0x7f022bf67dd93e9ca8810000,-0xb6808488f8865af378c4b000,-0x7a50d5934a68ac3c0b804a00,-0x32ce9668db40550e1146fe00,-0xea80c9c0ade5f19cb2c9e60,-0x31e2481b149ab5dbcca78b0,-0x81b835a42522ba405a6340,-0x1076bebb8ebae49349fe28,-0x1a736ee22c2144aa756ce,-0x21d743f26a69f75aaa33,-0x22828615a37d2bff9e9,-0x1bec23b98483a753e4,-0x11bad305b3a24b0ef,-0x8a9eed43170c310,-0x327314b852e7cf,-0xcebe58f2a560,-0x216642d566b,-0x293820021]
def m11 : List ℤ := raw_ints% [0x0,-0x13894a913b2855d168e85ddd3924a7899d4400,0x1bb8f6c435babc9368acf9357755df6209a3300,-0x12e1af11a2d619430e213b62808e9652ad1fe300,0x83791ee74af2259dcfe3058279a6f3e2b23027c0,-0x290f1e4ce04d879a784cb683b55d6691f8f10f3c0,0x9cc25b72bab6e37987bac64c07f8c3fd14fed5d00,-0x1db67c46ac80343786a8dcc2eaffd1e55355c42500,0x49777723c22393825e59417b7374d9db5e68bfebf0,-0x96d5802d3567e65e7052de0acf10e28e26795752f0,0x1048fd1d7a1519b3a2adc4907d61359c4c2a2ba2c80,-0x17e65e5bcdc234c348ede5dbc7ea4ab27004e463280,0x1e02013f1e0f403e32bdcc80da3d9dd3275b1c21a00,-0x206493c9b229a87cee62d7f313bed12ca3d31174000,0x1e29344b7c1f1a1df2de0311bc9eb252101d69e3d80,-0x1843fc37fdf54b015ec9769ee0c53cf6209bee36380,0x10e05d0af0db8ef2c5206baf8c5e3788c230ef6a9fc,-0xa2365144c360309a8d69df807dfdac6de0511737bc,0x53ff47cd5ff9d18bb639a7039bd0150ef710400e60,-0x255dceb967247c7c51f36473743d95d83670109be0,0xe364320a2ee5cbc4eb70f5781339540e005bf0dd0,-0x4978dbf30644383cf9f848be7967baf71a496c850,0x1400356172612dea618d8a8eca90afa4a8f260820,-0x489f92f93e0ce3e53ff10915b2e7b4a4a442dfa0,0xd8e57152480f95d59513a56c070c67392e35358,-0x20bc457b5c30970e2db8910e2a357003bc3bc58,0x3e863a215369df5d8c564463809881d987d820,-0x5bc7040e400a45154a0332aa0d0a6693272a0,0x63a323719e671dcaa9ca31617ce5079ef010,-0x4be6b204b84e9bbfa8eb0bffb92e5dfc390,0x25a376a1445ee0dd37a92090f7b9b20160,-0xadb3dfb1193a44c709c9c9c7027f4de0,0x184d02711b0f7b58ff72c9ba49efd1c,-0x12f9d18a518d4d36e1ecebbcadb5c,0x26c5ba4d2b0d4aabe1e942f000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 18 48 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 48 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 41 indices rho q11 m11 11 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 41 indices rho q11 m11 11 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r12 : List ℤ := raw_ints% [0x1e162ce8791d27fbeaee230000,0x2b2886a37c66140bf148451000,0x1cdeacdd9ac2952eb559294e00,0xbf7465231a16845dac5a29400,0x37184de23e395a214c01a9d20,0xbb004ef56dad4c0f59a1ff70,0x1e4c265fd9e464415faa4f70,0x3d4e0b2107ad30f29e0e318,0x62167ae96ed5d235282c82,0x7ce53892d0caefae433a7,0x7ea897e8667ce0c59836,0x65d02833077311b90a3,0x402581c2adc0887ae4,0x1f0d84785aaf86dcf,0xb2c0f3658c20c3e,0x2d2191965d70a5,0x72897d896e16,0x89ff5ccb3a]
def m12 : List ℤ := raw_ints% [0x0,0x1c155b30c509fb5d06ce06ee0224b0d5d211c00,-0x27658eeeca7fa6e8238b0acdbd93391d0e4a9500,0x1a83fffa55d30aa6ff202f1f67c7fb32491216500,-0xb65d6b7cf032f0768e41e50fd412cd159f6db9240,0x383a1d55f6d7907ea0d51e46010b8e5c2a3d76e640,-0xd3d329d05b8d476358c55b55f5c5a35aa79aa45b00,0x2798abd8dca19768d15bb074c70b74e6b118f335300,-0x607f09f8ee185a59f28ccd6947cd26c96d7e962f290,0xc324276d6bd335e4dbd15b6762b9c37c1c96990b390,-0x14bcf2425d5e2540a53825979f52a8dfb25031396f80,0x1def422f5ba2a617127ae9dd06a428ed9545c6d4b980,-0x24efc0dacb631e464bab7e66a0f7a08b5a63f41db200,0x2726416eedb2e323a1aa62097b3133242bc23ccbdc00,-0x23c187fbba8c0241ec43ffc6f67c3485a52f10605680,0x1c2fed7f973cb643415f9d4a9a0d435b7ab8b1054080,-0x132f94b188abcd1ee62327aab895ec096608b27100a4,0xb43d0fc08746f0db08b16760157b58bd1ef5bf6bce4,-0x5b15e220d21f7b5f8a08d4e3fed3ed70ed3db23b2a0,0x277a97f44722476e35db401ba743e991fb1796a3920,-0xe9a305fd56325856212f67a3340c7018819bc2e9b0,0x4941babdace22bcba73dfc87d41983161e2b808b30,-0x134e14f9eb08f0ba6a6cf533b24cc857478df2c2e0,0x43aa7d37b019b1123bd349b9c1300eda3fa5d3f60,-0xc2711c9afd5164267a8cad232b72eb40c25c5ee8,0x1c2068675148ea4ccc04567148977ca7188b2de8,-0x33405a8dd3f5eabcb41fe1c172d0396157582e0,0x475f73f4bdff25e4147a674cca65068bace460,-0x49038f8dd940392b0ccef04a9b05063179170,0x33f8716746dbd2a697de36f9b9b7400b71f0,-0x17d3a839d631e1d465cd1feec15a1d4c7a0,0x644e2d2c6502dda7610f2bc9b54930720,-0xc9539737d157847541757c23679d884,0x89eff9c91cf4dd43c63c81a9b7044,-0xf083fc655c271dfea49e6ca000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 18 50 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 50 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 41 indices rho q12 m12 12 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 41 indices rho q12 m12 12 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r13 : List ℤ := raw_ints% [-0x64ba0ad7c56762d5e8dcf2e0000,-0x904515439b81ba0173e29f8a000,-0x6057a345d459ba4d6e5758efc00,-0x27db1780b4c873f570c3bed7e00,-0xb71def83186659c8d6c1014940,-0x26c0868a21b070c9ebc4177000,-0x642ed16a62f5520e16eeacfd0,-0xca1662a5041cae41c17c2a80,-0x142339bc9b6c6fddaa7294ec,-0x1989a643e971ea702b850c0,-0x19c7071b2f5408a62869e3,-0x149bc61281bed80aab882,-0xce6c721da2c5c60f6ad,-0x632c190b162e2b34a8,-0x235b0be642d13de5d,-0x8d3d6aa7aea510a,-0x16183ae80b2297,-0x1a27dc11c40c]
def m13 : List ℤ := raw_ints% [0x0,-0x285eb3161b3e5955b9c829f62314be335df98400,0x38020a3fc753ecb1871129cef74e5519f12536300,-0x25439626992c9188dceec29fffa2ef824e6de81300,0xfd3d2398f328936d8992e0e6509cad25a6477623c0,-0x4d1ccd81e1fdb1277b89337b3aa0f0198a17d94afc0,0x11ec325554da682b155f3c807932a8e42cb47df42d00,-0x34e245ffc9e6068359200a39e57a4c4e1ccb493e7500,0x7f11b0576c67a36ecdc0bca4b23ae3c1e18ee0b20af0,-0xfd325c067367d991977a00ad521a92b3ed4a1706a1f0,0x1a7e865a0531c59af86a7edbcd84706f8a6168f23d480,-0x25a07e73fbed3434a24758834ab1aaab26e9c7e0afa80,0x2da448a98475d8edf7c81f934d7d4cbbfad8337ec2200,-0x2f83743967bc5e714401e22b656beae7b6c85d1542800,0x2a94230352bf7610825a2ba7dfd4dbfaf1940bd0bf580,-0x20e5e416d5c8692f4eb6827efafc897f79a94ecec7b80,0x15eb9219ec1a6cc615f10522f9c0b31f3572400d6c3bc,-0xc94fce46cc7fe0ff3a346608687a489dfdb5b8879d7c,0x634e2e422cd311821604b901bbe51f2c439db77b1460,-0x29f1431dc615e1959807e657ecc3acb81659ca38e9e0,0xf169eaea0fe3a11c4adc343e3a00591ed0ad39212d0,-0x4975d2b1284c94b0bc191950fa0990b30398ff57550,0x12bd775b4724fd1247c6a4908cd8d79fd4750e93a20,-0x3f6750179814225164578456e0e56d67183d2089a0,0xaf4559293671b4222563a6e1eec4aad59c4adc4d8,-0x184b1e154981dafe37ab9bee92219aec4eeb1ddd8,0x2a373cb3805ee631ce7ac4e5f9ae8b4995ec0a20,-0x37bf57b15dc221facbe5c987fbfa5fe549d6ca0,0x35b40adef491f453c523a46915f723696c5110,-0x23b036d1a9589677a734f14892f2177885c90,0xf1cec48cd3ca381194930cc300f0ec20760,-0x39fa218ac7b674286a50a1dfdc96729be0,0x68402e8727e16db169df232f252d48dc,-0x3ea275b2037f4354fea00bf5e43b1c,0x5d32b44dafb76790da26bbdc000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 18 52 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 52 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 41 indices rho q13 m13 13 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 41 indices rho q13 m13 13 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r14 : List ℤ := raw_ints% [0x13176bf91bd47b92aa086d1240000,0x1b4eb7c57c523e1df9784c042c000,0x12354bc8ff2f955d77913894a4800,0x78513a3874386bfdfe8efa5e6c00,0x227c09d835046283a78f56e79780,0x748468654decfb7f3ce0233a480,0x12c819bbb8b11ee55ffd6444180,0x25c8c2ba688738c4e7889ad850,0x3c0ef25e2aaa13cf54c40de78,0x4be63a09f594437bc60c3d10,0x4c4eaf6bb711aae6e81c2ac,0x3cb9f57cfb407b379db2ad,0x25d05d680ef6f72276cde,0x120db5afc33a2266753b,0x6637cf57bc4f48e600,0x194b8e2a8a5bc2913,0x3ea104494acdf7e,0x492687611bda5]
def m14 : List ℤ := raw_ints% [0x0,0x3a08216fc729a06b3b0fbc51d26dd169d716adc00,-0x4fa7004f645bb9cc759f723b6ed7507587f93de500,0x346859caf3f4573d1c556debe70786ecbabc319b500,-0x1600a9459fd9a540613b8f551988ec89bc9c70c13640,0x69e8d743f01ef97654a5e8a0a676d324fc811047ca40,-0x184e99a1c3e16df9b1a7214357c0f581aad457bbc0b00,0x46c86cbe29226e3f767c32df3f8fb5691898704048300,-0xa7bf6afb219b9ec51280ecc82bf8a51cbb77bc775bb90,0x149757fd1f71d24ddb555486fb86c7c6e0808d5afd8c90,-0x21f4a6ab9962e3d399261ed202036e94ce233fa5f24780,0x2f7623102cb2332479025b6f42985322531fcb6584b180,-0x389d0b332a799310c57251a01b68c3f0d8dc4faa286a00,0x39e6bc7def9a417463793e7880022f2d2a5bc82366b400,-0x32ecf9115c1780c61dc600af8d8fcbc9c2b7a03459de80,0x26931bc8839903ea23bc80caad77eb56c4b5a955626880,-0x192aabef34887c0af0801a72963e0b6abdba35efa270e4,0xe1ff07e060ce225371f085c0b8f36a31063a499ecb124,-0x6cd6dc8ac19044a88b08a960194dbfac2e1457330eca0,0x2ccd3b214beb5779ada7ecf53b3b7b0cd6312acabbb20,-0xfad45a83bd8dfec992ad2381ecf4eb53e06095ed5cb0,0x4a135500e44e750bf0042b6b3078629c6889fb71d630,-0x124b07848a331bcdcb05ba8dc3b417e92948937780e0,0x3bbc5943760751054a03e605699f525a5804abb0560,-0x9ed4aa637a1d38dd19d6419a77172083bcfaadd168,0x1516b3c06bb71239989bd72f0d538dbffbc8d7d068,-0x22ef7c89e92055c689c1f4ffbad2bf2710509e0e0,0x2bb94297e3442253dd7179f9288c74f16228da60,-0x27a34e599c358f9b54e10c0c8aeb2822d854870,0x1892bfde9f03e7e3780842f614a41678cbf0f0,-0x99a5743edbaccbcab87b668f02bfd23191a0,0x2189c65d8372a65d609c495f9e86a138920,-0x35fb37a805e7b3ec8725ea907b7c946c4,0x1c6d1342728b42f7e23947de6525a84,-0x2418318dbf210adc8e958dfe8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 18 54 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 54 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 41 indices rho q14 m14 14 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 41 indices rho q14 m14 14 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r15 : List ℤ := raw_ints% [-0x3564cfcb68f0f5665c4f1c9daf0000,-0x4c47690648204f4df9713d928a5000,-0x32caf67bfd0a444b82171347293600,-0x14f2099a4fb23b0ef04126f78a0e00,-0x5fe40b236c66f82811aeed79c3ba0,-0x143641b681d0ba1b995b360420d90,-0x3404c30f3cdeaa776bfd273fe420,-0x6866fae60f6e4658ea5fd3c1638,-0xa581ce7029b8a3bff63f1d3f02,-0xd087fd1209dd0650669fc16d1,-0xd0ef1f0819108e504dbef3fd,-0xa59eeba91506b6ae5a9ce10,-0x66aa5c72f8572d12ddff3b,-0x30c24ec6165c81addb2d8,-0x11260bb452ae7b4b6d4b,-0x4367f177ec5dfdf844,-0xa571cccbe2bc963b,-0xbf343bcb6979bb]
def m15 : List ℤ := raw_ints% [0x0,-0x536bb010ae4bd69a24e69eb59e7ddd08253099c400,0x7151a89d3a4618b825d884a412ecbe1547c970f9300,-0x49c20ec9b60668fbd33e7a8b942a3592c38f665f4300,0x1e9ea52ba576b9147ff66d5e64b74be1567168d1fdfc0,-0x91aad59a698d05ea5643c961465d672f56293f72b2bc0,0x210626bd77b83e61b3e6337063240acb5864af05e6fd00,-0x5ef0c17e209abbcd601f9f6198f909e859445f1681c500,0xddfe171265bee10c0a4ccd4075bb5146bcdcab53e419f0,-0x1ade30422e97f9759ddd8ff3d54af0b15d6c2840454a0f0,0x2ba7698075c3ec6e1d91cebd50d7b01f60ec0149d27bc80,-0x3c1264244ed2937c76944909fcfcae019ac1213bb824280,0x467c2539c503bb2154debeefaf817c8fa407f06203aaa00,-0x46d8261884300faadecb8177f6d1049c20217d9d7e19000,0x3d2bc91cd27f775dcfa07c6086b0815f227b0cf19152d80,-0x2d6fdb91b12821bd10a937f121f0d9adf5981cb358d1380,0x1d084d71f05b5881c9996e52c2b03460fe77f4f6a36b97c,-0xfef9b533a77703b6589f91a62a06c0161f715ff17e8f3c,0x77e7d267f3390efceb956a722fd5b3deac5ba106bd6a60,-0x301c26834c080f5109df344be62241841c36e3bbb397e0,0x1060541a882c39fab17b02d5ebe94087f6b00d3fb5e7d0,-0x4b1a3e87c11c1ba2c0f307107463e021c2fc519cf3250,0x11f41af22b80345af9bebd8e3d906a7d22a91b0f0cc20,-0x3894720675fef77b2d988e50e8d0b1948bbac56153a0,0x90ac597bac782759cb6c09e58430de96831ec6f4e58,-0x12654fb0399eee8713b360854c39c718e06dba8f758,0x1d0a3678c905d257cf34d16e96e51616e38894bc20,-0x226dabea2f0d3086960a2e5ba9ba21ec7a43886a0,0x1d5a2f7dc4c03659ba50dba146c841bf581d4210,-0x10f6402084a8146bb32acba915896d9f9d5c590,0x61c86610efc045edf1c3f42186b9a6018ad60,-0x136a009c122bac30316283f313ab6dd049e0,0x1bf2f5f4d26dd82797410bb8779906109c,-0xce4e0db91fe6b4ca8a20c35c9f646dc,0xdf8c97e093fdc9bf20e4337f0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 18 56 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 56 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 41 indices rho q15 m15 15 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 41 indices rho q15 m15 15 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r16 : List ℤ := raw_ints% [0x8b9025cf1f696373749517570710000,0xc729bf518d8c4bff8d14ab46798b000,0x84754cbc461810ed8276fc9d5b2fa00,0x368c573d0ede78bc3041b55291fb400,0xf95a94bf9b2c06b219e9608c37d660,0x3478a4f8533a600765a26bbba93d50,0x86ca9d26b04ef146b6496d4e6d5d0,0x10df7089e3f53ba7f8443be99ed28,0x1aaf832034b6de51cd2b115aa036,0x2188b5b041580a907d69cb97e95,0x217fa9dfe9e2f51d9733e3e282,0x1a76db0e401d562232fd273c7,0x10575cd50b3e6c2f4d88a308,0x7b9f6af1833e9c4c27124f,0x2b4104ef77681e72f01e2,0xa8fe347b36b4a26dbf1,0x19bd4aa11d55f526ae,0x1d7e742a7fcc856c]
def m16 : List ℤ := raw_ints% [0x0,0x77eacd17fa8d047d950b842513d4edbbb575dd09c00,-0xa145939d4787d847c9f3cd43fc2441938b23e9663500,0x67e0fdf59c3f45a495f06a1effc504d58bfdb8cbf0500,-0x2aa7fbeb5b21e5fcb1d8861f7c6b660d5658ff80d11a40,0xc8a0e2f34f7b0ef558f1253329311019e8a011c1d8ee40,-0x2cf1e1a7e5e1bfa1be50f4ee41ca4882e3d0d2b2ee8bb00,0x7f9b40ef0f98283f306d594690c416dff4940f04ab0b300,-0x1267c276cf22e9dfa5f530ca9d65a1f0a90aa5ae48a31490,0x23275c7d57e4806dc6b29398bc5b6d27ad1c481091d87590,-0x384b22fbc159d3cb427593986d155c98155eb2657f371f80,0x4c49d4aaf3eadeaf607c345b09c0b36964fdf31a53bc2980,-0x58139b20654dc972c06a26364b0eba5230a6436d0c2ca200,0x5705d3daf317a2901eb711b434090c665d228e13bfb10c00,-0x49c997a4cab976220c3e87a9a190de89448a81ca82abe680,0x35c2570cc5543fc703209caf02928bf4e5378b3669261080,-0x21a633e7edd5d6cd3fb8d623fd6333f305bfc89c53f2a524,0x121142ffb7d78c76b0b1006953f706f8e94964794b9c4964,-0x84c40c44c0911251fc48e92bf23b35b5b4cecff464266a0,0x33ee49a99cb7bf244a242e5c1b4c5c0795b4796cc625d20,-0x11327c073c87cba88b271488be01c1806d22eab936affb0,0x4c8c448da85d7644447ab43748bba45cc279027ea65130,-0x11b69756263f659e6d9761795175f7a1d6f1bcb1839ee0,0x35de2275a6dfb80549c0c97b4ee43d1a717eaf2a82b60,-0x846eebd62c872788eeec97273f12606a84e2b50bebe8,0x101f2e34c1479ed9258eb3be2338fba7faaeaa635ae8,-0x183e098c15979ddad8db3beeae6f6550be88e025ee0,0x1b35e529f6ed99f6ac091aaa49fa5f7de625bf3060,-0x15cd6ae95d790f43c128a1687c4327740acde6f70,0xbbc200042f9997a483dea67d4a61d16ac2adff0,-0x3e518f208cc50a74984e8a716781c6e12c7ba0,0xb3e902bd81c83ae4023a5b38f15d19b52b20,-0xe77f7c8687f9b76b1beb22a030329a5904,0x5d87ce9a85c2f75101ab43ef4d7f48c4,-0x567da48168a139087a9fe9faa0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 18 58 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 58 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 41 indices rho q16 m16 16 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 41 indices rho q16 m16 16 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r17 : List ℤ := raw_ints% [-0x1587345d5c4457b0fd2f26b10fd440000,-0x1eb0f6d80278dd81c799efb072895c000,-0x1463bd01ef43bb7ced009d1e09abf7800,-0x862f47cef8c18dc039288c35f383ae00,-0x264912ed8d41b77af837153057092d80,-0x80b59070134862fcd9d0bda28ea5560,-0x14a16313a132e92928d0c371de82030,-0x293e2456c94319b5e4eb9712de6b50,-0x4117e4cc7231a7f1b1910e6230d90,-0x519bc97b6f1123e7d819042bb6a6,-0x514f3e3ee07d2f5e5dbecc41937,-0x400bb164623733b3d0c233aa8e,-0x276a236b5e54d986b9aa3a499,-0x12908775f874b44235bfe620,-0x67789520fff51800ec2b99,-0x19233f10be10a2963b50e,-0x3ce54e378b2a1e04ed7,-0x454a1ce36f58ee06e]
def m17 : List ℤ := raw_ints% [0x0,-0xac6186d2782ab67486408df54c8215bdd4d96dbe0400,0xe59847e393ff836ded2fbb22e7be08b8e770d722ec300,-0x926663b57beeeb0cfd4db4f45af9dd30e8f8493c597300,0x3b7c1df4eb26a870992351ca7547e19191fba8d860d5bc0,-0x114b3c9ae673ceb851c92e4cd7767c68c7dcb159997d67c0,0x3d45bddf8fb87a1695befabb43ecc7feae8f3b174792cd00,-0xabdc0079a6b826f495bc1901db0076daaae0e2aa747a1500,0x18791d67678d5652f641207a01bb06b277bac61c2925118f0,-0x2e1e30d3dbc05ac2f7d5488c1e50c8a5a6becceb5ef438ff0,0x48cf4c440ba1c89be574e765a7f6e287f0d8f2d4989d52480,-0x6133b181395cb817d4b35517998872095531fa3e87e2a0a80,0x6e742cd7c6bd527fc314b2d694432b354c48087bed7abb200,-0x6b4f3c1117227a262f351f4ddbed4023431d5a46111677800,0x595fc1070882ae5a648725834ef6c9d2b9f4580047e21e580,-0x3fe25b3f68b7c48ed095eb641dc11bb57c56ae4523d3f2b80,0x272dfe8371a7393a5b98a3de7cc667491f76858504b464b3c,-0x14950c3410ee2b1aa5d23147b84445ff883aba8129ffa9cfc,0x93bbecef740532085902e558506cf5eb04b299a7ffaee060,-0x3856fecaa27fafc0025bb73d12e1ac433206ebd8f7e325e0,0x122702362648e509ab9a445c714e386834482485eb2e0cd0,-0x4e6cce362d550db4f922bf3692522f47ad4a8370cdabf50,0x1190ddfbecfc6f60e4ba7b2562dd8d76b3352f240ce7e20,-0x338af2cabe2ad88faa1ae6b81f7c2581f64bb58da8bda0,0x79cfd53192cae450014e7a8dcd2ef4c9aea60035cefd8,-0xe314a910fc5ca2620e5943d785e97c644b1d6864a8d8,0x1451e8739fbe02f8e828da066d3ec1983ab9a68a0e20,-0x1594fb976e2b3c1d30d9341375ad788e4951a1740a0,0x103db11c75932eb76fb2310980a37e1e78e22a4310,-0x822b7d50f81293dde4057d0518e0b6a87cddbe90,0x27c44383b4002bc5cc7b4d79d7e18d93c22b360,-0x683fa6356aa32c536ad438f9484db361ed7e0,0x77d184791f8a1d7fa39c7aea718ce87945c,-0x2a617feb9cca16fcb0b2282c1328f0e9c,0x217272ce708a30370061d14f1c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 18 60 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 60 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 41 indices rho q17 m17 17 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 41 indices rho q17 m17 17 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r18 : List ℤ := raw_ints% [0x3293599e5fd145179be298e92fb9ca0000,0x48099cf9a1f1480d4d248dfbe97dfae000,0x2fcf71acced5178ab6aece4951d018e400,0x13a4bdb7c92b3a3673647f2b23349f6c00,0x5990df2df6e1313882d33a971759301c0,0x12cb36cf952e9ce427c5abaaadc4835e0,0x3020690e0b1565ee2c45e066ca76f060,0x600d38cbafc1aab698887e9f8a51fa0,0x9751891f2ee95adf3f1169b664383c,0xbd51d5e8881d3265f69366ccd1ff6,0xbc30de05dc8400697f13def706b8,0x93d9688d5523a53b58709af89f1,0x5ab8dca2cde84e3352628ab162,0x2a96c0cbbac51b64eb277ac8b,0xec7924dfecc83151dd70ce4,0x393332244d72eb6f127b3f,0x89de99df58f99ee52126,0x9bf413c555b8ca814f]
def m18 : List ℤ := raw_ints% [0x0,0xf7cc31ce8cbd664780fccc109dfaff40e1f88dc125c00,-0x146f8c46b30dc202745ea5a99cb66ceea69e861be338500,0xce76aa7a8bf64af4026b569b9d54fe3ebe1d7b20e795500,-0x53090f3d8b89c1d3bcd82faf1fa79816428d9e5b33473e40,0x17e20dc4c7ee860acf3f90f98f4562daa26e537a7866c5240,-0x53ab7ce251479f12be7105e3975429e67d0af2ac32b186b00,0xe7eaee6b8a521c97bf529b35a0f975d7ead5587cbdf4fe300,-0x209dc45bf9aee02511054eaf1e34a8859a00a26770597bfd90,0x3ca906cc5b60a2f0e5b32cd039114e965def32b0da9941ee90,-0x5e7297c1951a527ec6f726afcb1f80977352af2ae6663f7780,0x7c3fa187143f7e87d7d1db638df6393263248125e55bd72180,-0x8b00eff52acc62fc010257d0028e4c3778e16f35f7099e5a00,0x84d3dbe05b7f32c19af56a84b34120ab07b3a8848df02ae400,-0x6cb11fe8abcaf97e3507102cac87299029a6cfad8606ee6e80,0x4c3e0198067328091b7479d70afc200bd5f127fe654dc43880,-0x2dd3274b402d27f5cdcbe280077f9c09f602f198725f41dd64,0x178ea5615f2db7d551a9782b68c2fc115403af1d12be8ba5a4,-0xa5301446cd016fdb033847b13d6bf2ab39912f882d9fe00a0,0x3d6d47f1217210445e6e48e247a8d7af3b548397a84d31f20,-0x1341d1c8294b3d3951f517252fdb03e59021ad12e36a5d2b0,0x50c0f99d5a231d9d726249caaf40627ef26dd14bf3477c30,-0x1181bbb8b69653988be18dac11b13be290d67e8d66df9ce0,0x318ee0a348947b7a5bdb61aa4d667e31e097d9750fbb160,-0x70901aa4ffe0a3ff31e18935c2707299de37e291562e68,0xc8c588719ae50c86ad9247f024f4506364cef5fa70d68,-0x11193be571bbc3b79b10330a0f491031c4f44401bbce0,0x112cca47ab3e23abb85de436501377c2a3876056e660,-0xc216f6ce0f1c0211eca22a09b1dd397ce245af0670,0x5a6b09dc48dea0202a74ba7938665899a2e0fbef0,-0x196771c0482b62a53421a87a9254dde5380405a0,0x3c6d93962c31f16151c55880fe77585a54ed20,-0x3e004ba84954587dc47a253552195b664f44,0x13319e636d1216c4879c7f7ea8c23f5b04,-0xceda9c3fe455451e0ee9d7a7680000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 18 62 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 62 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 41 indices rho q18 m18 18 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 41 indices rho q18 m18 18 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r19 : List ℤ := raw_ints% [-0x71d54338ebab7622488bf310447da2d0000,-0xa2018b3bd20407b4f4af5e5e538ff46f000,-0x6b6c988df335e3a484541eaa0b9de104200,-0x2c17c00551bb367799acf4bd8a0e07f5e00,-0xc8d2b43ce73c1b54cd8c6b32ce467636e0,-0x2a1686f2eb6c9ff75151f37f3239d9db70,-0x6ba20ae28f52ca9ec4d95ae1afa74f000,-0xd67ee5537562ac49bfdfb4f275e517c8,-0x1515b144eb2cadbe8c4b6d7e59e9fe16,-0x1a54d466f46adf4eff164507b957f7f,-0x1a1ee83d700c39d205b14e6b577691,-0x14796a999c7b01b4fb441f37a6ffc,-0xc87e99726b7516a827ec033f6c7,-0x5dd8e977111d79fbfef989bd00,-0x2075e28a446fe344e51bf0047,-0x7d2840817b4a6ef7a37e968,-0x12c5e6f5565d880787b6eb,-0x15213e48d76bc790b465]
def m19 : List ℤ := raw_ints% [0x0,-0x164358798ea504306c96b6557e318ceed44d54bc5a64400,0x1d1ccaa55a6e410a72dd2c6ed8e0388b5d06889abea0f300,-0x1235bb6e8a7dc6b7783bda5ea949f5d39158debd6bd16a300,0x7405c8dc1e1ef5f12d436415b7c9c69cdd3fa90bd520a97c0,-0x210683351f730c9410579a972c0b3b4bca9f011f7a841b63c0,0x72707d9918f40bc979cc9cb0b0c8b00143bb716b1dff9b9d00,-0x139921cd2b31717ff1b34796ea3aacb8a34b3ffcfb400e76500,0x2b9126274d2688477265a083b0058990a83efab763a90d807f0,-0x4ffe2a6ea040730c3a79b55631bb107522f21e14d9a88976ef0,0x7ade0b1ada7bb7b454916a35941d6c4e85e5b859ff44e490c80,-0x9f52cd3202beb69b5ff1dbac9049c2ecadc27cdae8204625280,0xaf894716b10f113c7ea44ca5a600801d786ed7793ddfcb73a00,-0xa5067d8617868f17ae15022a35888330b170b4e635bf665e000,0x84b5eac809a37a81fd002ee6d317fd65ebb63f3d16aae0a1d80,-0x5b5fb59de626a27da27c40e0f74b6a034bb11cb36f3af82c380,0x35d581fe1285dabf87dde847df7cd2131389784801b512f38fc,-0x1b161bc173e54c3d5c5463c6d66f7149f07ae12981a5c42c6bc,0xb994dd7a4906a2f41db9ce3aaddcf643c3c708f106e842b660,-0x434c80944ca95d31e541c5bff757f01c8d0f38ed12acd793e0,0x1487945edda27f68df5fff5abc73a96ae9f69b1767a90181d0,-0x538fac243f3a5a9c1e48058865ab4434d131c9c44830c1c50,0x11885c8c07c125d05207a8f6e5e71a9bfc4957158b19b5020,-0x2fdff04960c0e6e80afced66be8ca6fd1101ad3995b6c7a0,0x687bae5228a394b4209be92500ed71209d71342824e2958,-0xb23fa78a358b2f422ccfb9b94ce9117eddae98f772f258,0xe70fc6c62654f9b8ce15f14671171cc8a994bc3928020,-0xdb6081466de7bf0883056da804819eef71a6d5699aa0,0x915486c2da053365aace7bcef77f8d24c2ae2d25410,-0x3eea77a9dfca2b6fcf288fed82ab608fc85e444790,0x103ea61e2769fb2a01371f13c211f28235be91960,-0x23096241fc0a655787e5e3d6f6fc54ff1fe45e0,0x20131b8301daa5219315e80457978c987941c,-0x8b02ffcc85de0ffbee181ca5181fad925c,0x4feb6ba39983306db5a9bb31cf00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 18 64 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 64 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 41 indices rho q19 m19 19 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 41 indices rho q19 m19 19 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r20 : List ℤ := raw_ints% [0xf6c4c72ec30e2a55a3a9aa45166851ef0000,0x15eefbae2b7511d5cb6fac7a7381403ed5000,0xe882a585f77d6f674db17e4158ef28678600,0x5f593bc0baa8c95cec54445b187bfcee9400,0x1b1d65ae53561eb8375c9d433fe8573d61a0,0x5ad2929a33c1c7e577a5b302237cf182a30,0xe7fb438869f7b3756b9241682522038530,0x1cdaec9c936a82d8323c757a6a0f0679b8,0x2d50cd4e12afc051edce296589d60eb0a,0x387fa3c675d93186521004fd940b84f3,0x37f1add10191802e71295f20dc2ce4e,0x2bc2e5bec5216c367c7dceea7c6b2b,0x1ab8e27bff450dc1f979c482fc7ec,0xc79e06b6054cc492554e94c7b6f,0x44d87990404226368202c8c406,0x108943aa7560c7cd31863ccfd,0x2789bc5786cb45a7e094266,0x2c4fd8aed435a6f00340e]
def m20 : List ℤ := raw_ints% [0x0,0x2000cf2ebd0d36059c18a61ae5673a97512f29cec1f01c00,-0x297c7ead506ce574890af98682360bb8404d0b2019075d500,0x19b6b99a64d436fff08591f940ad418705bb970effaef8a500,-0xa244b51883d6f591125b1e6c9fd8f31de3a8f62839b867a240,0x2db9b24f2029413bb578457295551d1b9f1176769869fddf640,-0x9cc59e76d6cdf4bc56098d3183128a522b92ea6c38c6ab31b00,0x1a8c67a0075e218d9e2c41128b6bd36143482309c4a5f1321300,-0x3a5297d5c09dcd8b6beed60f45c81ef29269760d01661b197690,0x69c062df973ae7194b94e70a6c79a86fa41bb47a54ff67f0f790,-0xa049a4320b1a7970919c832922c1d3c2410cb531b0c00df14f80,0xcceedaf1d0ea1d9bd0da584dad1d304c1fbe92dcef3bf9dd9980,-0xde6b59750a108f729f30b380af985d85d2e583cf3cad8bed9200,0xcdc68b7ebbd6c07dc208436eb53a72f4517e9b14e03708143c00,-0xa2ab1fa9f6ae01ed502fb19c0ed4fcc245d134a858ef9a497680,0x6df5f11525020db55087b4ecdb7a6f4484e08b0da733f8f4e080,-0x3f846647580d4e03669936fe5bdc1fda3eb6ad04e0170bc859a4,0x1f48e5cd5496af9388efcfd82fc92e04ed1fef9039e4a48285e4,-0xd176ad5abeff6bfea8f7a328f3cb176b1f1db0ab4b40f513aa0,0x4a153594656662facd39d5758aac5092cfa9f76cb415c6c0120,-0x15fdcf95d7ef9575da3e4f31738d08c7e98064fbd63c2a4d5b0,0x56e1addc2ca17fefafc38d16a92ef69adce1c9e9e240625730,-0x11a4424819699dfe45e9448d1b8414530c790c93c8a5437ae0,0x2e75d400900d099beea8de1ee04c8ee9a6ffea46246bf9760,-0x6167597e7485eaf3e2c971aef6bdbda58470b1404b3b18e8,0x9ee254debe1eae9405818163557d6140d93b945877067e8,-0xc3d82b5de92e2a753cd8a4c9a8b05df5fff83b4c96fae0,0xafa78b22f05c38faf40529b22ca794db59f0601c9fc60,-0x6d12a364380bbab4a53c5f9bb0b2c441c9017b220d70,0x2bd944c4ea2bd7dd31f728d89607e86835a104b8df0,-0xa65881438037e0cfc29fd921edf8f393831442fa0,0x145182c41db7c98754e8e44d08b9f43e5880cf20,-0x10969137ef8b7a437df4b4ec42570dba276984,0x3ee4a15172c3b2a7b4980700c8dcdec5144,-0x1edd300b475436012666d43828a00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 18 66 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 66 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 41 indices rho q20 m20 20 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 41 indices rho q20 m20 20 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r21 : List ℤ := raw_ints% [-0x205810fa505f0a16796ea10467ed928caa0000,-0x2df742e2dfa215e7779480d93cd0187509e000,-0x1e6e73fb72c8755f7dde04234640a270c21400,-0xc7817f56fcf9ecdadc14272a2d73ea3241e00,-0x38aedf030e526751ca676786103553959efc0,-0xbdac505344049d70a60e34863aafd6d6d3c0,-0x1e3ef4e2da15d63728d10ac833d95c2a0f90,-0x3c1f1840e50aff0c722bd0740167c6859a0,-0x5e4a8f5557d6cb3e8c1ff1b998a3bdea14,-0x7562d8c9ed48b3e9be87fb29910f0369c,-0x740b05fba536b2e8e43f35fbdd72b10b,-0x5a9b6f4ddb7eae7d1177c71710d605a,-0x37372b5c96505cf051834a8bc765c5,-0x19b873b34ed1fa381579b0c3d41f8,-0x8d91d833dc8b53813f8767ffa55,-0x21e80c08440fa3db8e54843752,-0x50cea0e45b41333beaf7fcf7,-0x5a3ab92b78f6d8ad2bcfe0]
def m21 : List ℤ := raw_ints% [0x0,-0x2e0129d32fc2fda810636ec6a9c4643984b3cc1936c928400,0x3b233bbc9d7458c91a65b3f7358cd132bef9c548699a962300,-0x245509d1879a02a0fdf826ce887cfbd7f7225c530862506d300,0xe3284c1c3eec349a271de108c573f68ff835dcb0357fbd393c0,-0x3f632379582e1086707a1671011485f062783490373278111fc0,0xd7186b01014ad1577baae30eb7417698791bdbfe85a816216d00,-0x2407b8af157b3bc94011e6b42c0d6fa8a1bacbf6741442f59b500,0x4e3e7fcff2a69ae8f6c44efcb088fb7cccea449adedeb2597e6f0,-0x8c25ea1c3333884bb7f38c933a383d96599b69576e7b324933df0,0xd1adfb577429c147eb2666ce0e5abb2f37f768271878e741f7480,-0x1086646e0161769c609003c4516f88d0fe226811707e1aef531a80,0x11ac1ea7cb640fe94bd33012507a8fd96bce1510089ea5c53d4200,-0x1018168b3da8156672cff1cb090e6998624924c4bef3acc23cc800,0xc82699b79199921e6bfe92fb38d5a2e57b26f2af321c053a5d580,-0x84dd30e6aa16ba846c772343d3eade6ebf58549b070798cafdb80,0x4b42b5774f797de9a00229d6aaaea795d95eafa8b08fc762f42bc,-0x244b313bfe11d21e6923ac3f37599bad34540a2a0bead8eedcc7c,0xed7f43919d7ede7d7446afd9e6178be09da3e316111dc41bec60,-0x51ee2c0c4182cf46bc9753c85c84f464bff1364665b57086e1e0,0x17ab08ba83db047f86ce094efef65be398e7d199200cb40546d0,-0x5ac1d063daa9cefa740345f34e119fcb40bc79b0edb21144950,0x11d53dc1c8618b55819c83703ba41a5240fd92df80bd1854220,-0x2d49a4b375fd39ef3f0c51e000d2f0cab446b5c633fdcd71a0,0x5b2f1507576e3742950a77e6e22fd06a4495d087a8cac7ad8,-0x8e2a721ad397e0bc11f300b19e5cd9540cc1e884ec1753d8,0xa68df3d0d7570210ce1a815aba325c5356cde7790221220,-0x8d0a7ec9f2e7081d376ebac828603a33cfd88b1ce194a0,0x5209969185060c25eb4ebfbe454516d069fa6f88e7510,-0x1e9aaafb988c4e6fc7098627c40428b7da9d058e6090,0x6a8a332c81fc956f059d594657fcb9525994bddf60,-0xbc8d2143443e3e17a7303cb112939b7df52493e0,0x893874c1248de026b1681db56af5586135cfdc,-0x1c70cf28087c40d7d70869382cfd5232921c,0xbea0be10a05e378185968a57e5c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 18 68 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 68 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 41 indices rho q21 m21 21 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 41 indices rho q21 m21 21 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x5a3ab92b78f6d8ad2bcfe0,0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r22 : List ℤ := raw_ints% [0x41dc2699414bc602305f63388fa16a8b7a00000,0x5d89de97a845ecc641a3db8b7e890ca67d40000,0x3de2518abeaa4d135250131926ef182e28e6000,0x19566411e4d461f8d7d898f9f9aaec339ba2c00,0x7315dd33f74d78cadecc405a62311c3aaefe00,0x180bf716003cf62530d9197adb64ef9a6a9640,0x3d4aacdf151a6b3dacb5ac58679ab5c5aa840,0x79b2cebc18637c7b1369f9b60bf623da0570,0xbea22942a39d62a6e391c06e18ce27c1920,0xed01ef3ff9a79a016cd2951ae64cf42b4c,0xe9f2f31e8adc65859e25b4cbd727af044,0xb65e9754fd50e8e16f4f59f7fa1ded75,0x6eeecafc60db1c5d1f5df9f619a66a6,0x3391f4668cc7bf3286007952e91a7b,0x11b354f2853d7b3cb6884723c6c48,0x43a84fc186f377f62cae9ef072b,0xa0c8b686f6fec965e015211ee,0xb2f3de4f71277aca2b2f269]
def m22 : List ℤ := raw_ints% [0x0,0x4221ac1f94a84ca1978eef3d940a5012aec275643ec129dc00,-0x5453059fe9dffc2d435e58f3693d39348a0632de378a37d2500,0x335dbf605ae402402624d395045a8b4e0960287ba6b5760cf500,-0x13e4809951b2b537e47328d39d963d3baf1a4a28cafce14d64640,0x57fa1f7e99fac0009221451a8565f8cddcd65a5ba20285071da40,-0x1278fb88423cb29b8c4cfad45e79beb2978a410b3fd3ce4dc8cb00,0x30fc94d559796dfd2f2ec2975005b3d3dbab6a61ac8a4ff0874300,-0x693105a8d13b5d44362a46f35db879d575cf69edee61336e047f90,0xba2db9933b687e0eab76d5c248dc6484a297c07da5bcc1d0769090,-0x113079a9d751ea80cdf2a964da14f2e30ee9bfa00d41bce849ca780,0x15622ca61ccc23e639703c0c6fc690a53816ed1a49cd3765c879180,-0x168a171446c1c2fdc87baf7c0be89b4b1f6097ef347d5f9f23a4a00,0x1435e6f280fa10d407b1098b6b48730490719515e363701116d1400,-0xf731484d759a77657841710a1091950a3ca4a69cd256899624fe80,0xa12ccd5bc1cc632ea5f43ea461739ea49a0fac5289f048de800880,-0x598bfa143bf071d155951552c9a9eb1a2f1bb8a6fd5517abd259e4,0x2a498688e79f4e2d09ff533f57f18b94e7c3e5ee8f47ec98ef2a24,-0x10e7c4ead61524f395e1b7d0a7e92b2139638052871593cd5414a0,0x5b05a16bd5fd7cb9f6403b91bb93536799ffd8dc4ea04dcbf0320,-0x1996efe803928eaa98494f9025538eab77fb84f6224df1c1308b0,0x5f3d21ea505a742fb68a8b4b1ab0452a0da8cf5eb11dfef1e230,-0x121b6a27098995af0b65473eaf9f60b40706cd12f5b7461538e0,0x2c55a86b150b1e9dcee5e854a1c3e675bdae18a68f1df49dd60,-0x55b4b7c9e3f142f04ab47e875863c29a0f1694afc9262d2b68,0x7fac87a9c35e3959350f1d578ecc7f99f7d56d406c9fdea68,-0x8e196ea1334663c81800def19b2308f0bc62d12811de18e0,0x718c2612d1845820453904b7da712c4a42602e4bd3e7260,-0x3dd38f09dfec8d347f5fe4e3830cf9ad5a84e1580e8470,0x1563590b9524fde57df275e6b3c5bb344d72e5eb54cf0,-0x4447777c7f59d7a89a30eed36f7e039dbd04f1ef9a0,0x6d5d4fd3854392276f45bec9a28bca74f430ad120,-0x46ebe10f98f9978bb6488104b65232ccdefe7c4,0xcdad4da61e3b4f49b841a7531df066126b84,-0x498e74589c7842c6845a7919d6e800000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 18 70 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 70 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 41 indices rho q22 m22 22 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 41 indices rho q22 m22 22 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0xb2f3de4f71277aca2b2f269,-0x5a3ab92b78f6d8ad2bcfe0,0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r23 : List ℤ := raw_ints% [-0x829edc87663f8b94bc1b62f7939f24cc62fb0000,-0xb968a14a3e978fb1af92d772947f31c0e36a9000,-0x7a96338e1cc61c77a49bf47c631ec95803776e00,-0x32280a7c6f078b16fce590c4c1b04e7bf2b0ee00,-0xe3a471bc61eb8bd461033660c0d42e6afc73020,-0x2f86864712a2f54ca4abcf7aee1d01660d45250,-0x7906590c16c84763c5612f609cfb8f20e39ae0,-0xf00f8c2021d8e9ae3ead60cb57d5d242f7ed8,-0x177a0268b3997b5f82e24c60640f9cb199f0a,-0x1d26f15bccf6a6b9f2ab3feaaa46db573f3d,-0x1cbcc4b4b644764d8a8a637e6547de235a5,-0x165e511d5a74047e823b9efc1d6c3b7da8,-0xd9589f10b7eb5401667ea7797d571193,-0x64db20812fb4561da32071708c88b88,-0x228c0fb184c06e576f9777903a40c3,-0x83c0e901bc2fe37207c7232be0cc,-0x1385094d005619950bf6eb42b7b,-0x15a9eb20075e76ca3df1f131f]
def m23 : List ℤ := raw_ints% [0x0,-0x5f10676d65b1ee2849dd77e884ced31adb3788c01a35ac2c400,0x7845dbbef28dfdc1cf4c5475f823db6576b7bf1fdb79303e5300,-0x48a9df068429a590d5b2e822d1428ecf38ac2cf5383513e5a0300,0x1be59e9e751ff4f4f5863705a979f78e9c73ff780b0b4944a44fc0,-0x7a3fcf5f32b03cf1f324424ea488567556b377bc1b49e4199a9bc0,0x196b9f1a57dc4aefb1fbef74cf15bee637872f17f61b412beb43d00,-0x42b849ace094e9ef87c2fb0f7dcfded400e778d8f650b62ada10500,0x8db5f07455802a23a907c7f4feed15768d6261460eea10120dfb5f0,-0xf7e88d199afc169a3dfc734ca6c062ceeea42f8aa1e943493c5fcf0,0x169b2829760063d3de11721d254db1ab0640fba73112ce9237905c80,-0x1bc043b58fe3d7aa265263bd31bc02e276d92496d3a1f9353ec46280,0x1cd69ab0147008929d491895ecc8fd4aa50cc65d718ebc4d1b7dca00,-0x197791a715856236d74c0a4b8cd18284065d98dfb15c149d988c3000,0x132697932a2e451de29d74b695c5ea5a43e349080c372d1ce74d0d80,-0xc4479558a1ee82dec9df63eb2ac2b296cc41018312f519b15fe7380,0x6afaf20bebd16c3955cee0b84dff1919dde60da1d20cb3c2e80287c,-0x317ad905ddc9aaefc054227154e04fca41ee0bdd29c02ddd5056e3c,0x13567938bc6c88cf18e92dce130d918574477ef0c69b5b2aac48260,-0x6592d1d1118ae2d7417f4f5d9980b3efba3e3f70f2290f001f0fe0,0x1bca93f01d2c56512358516a843d36194f28be77495c4e25365bd0,-0x64632d6c7bbf2c222363245d9c3cdfb54ff6d89c3bdffe1284650,0x12772a33a25281e45b20dd0f4331f2aac5163476aaa6ef20e5420,-0x2b9523c4fcc0d04810f3a80d30fc2b31d1215fb4fe13e416bba0,0x50dee84ebf36495d8af02e16e383cf19b03a4d6c882c8416458,-0x73101e66ca90d034ae43a520ba318e5625caa4e06a5c934d58,0x799ab62080c58aacf6c41b2fc57e75e706719cdfb96d2c420,-0x5ba3e2015143d3f4f60168ed3113e251c6fe17d0c9192ea0,0x2eae3b33e61a910af9722eb493a0d636d0fd8ff76efa610,-0xef703ef0f4265da234dddac629750b43535cf78950990,0x2bc845f671488e4f7df8d9b17c5abc10947cddd70560,-0x3f6f49bb4ffd3c79c0fe889cfeeecd6487413fc1e0,0x24a483469f552adb66d0974789b1b9e5e096079c,-0x5ceb49e2ff99ddb7171810905e04dd779cddc,0x1c5f133e308e9945a8f108ef5f1f000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 18 72 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 72 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 41 indices rho q23 m23 23 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 41 indices rho q23 m23 23 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x15a9eb20075e76ca3df1f131f,0xb2f3de4f71277aca2b2f269,-0x5a3ab92b78f6d8ad2bcfe0,0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r24 : List ℤ := raw_ints% [0xfd00f65fc5d9e0d9b175bf987bb0f6f42fb9d0000,0x166ef207717806dc0acfecbd4ecd452aa2da72f000,0xed2da79a65395039a9f9289719ba1f33168d0f200,0x60facf100827eb375cdd20e047b50c1b608673400,0x1b7d97addaefc7ba4dd9f46eb163c0d4325529ee0,0x5bc21f508f9d9d89516d4093e5ec7e7bac6b9610,0xe9780aba4386e929a4101d660efc6a20ef64d90,0x1cead032ad4bc25614757e64dabb9d2a8777cc8,0x2d3397c07356d739887ea16ce5a995adf68efe,0x3811288afdbbc2f4b51b02a8837a121e09ac1,0x3733c06383f81922f9e32d1f9d5293183b9a,0x2ae90eab9ac0ba7e0f214c664b86e3466cf,0x1a05446fc1bc3eef6c142546341a3ffd90,0xc0e010914e2f15439e0980ef9546692f,0x41f29d0a4c149043529a855774b92aa,0xfb003e72ffdf8566f3500e5bcffc9,0x251a6209094007b494cc8a2ebb3e,0x291336aa72d35872530bfa5320]
def m24 : List ℤ := raw_ints% [0x0,0x88a794ad422fc659ea2e5c5e3ee94f769b1fd49425ad277f9c00,-0xab9860eaf5eaa13f9fde31baabe1d5fb851488fe5f7da55997500,0x66d9785c6fe9dc45c02aa5fe8b5a965b1ea237c196147add064500,-0x2727d175081e94f6d799e56e399db0d1de72fbdd4113dd65bf72a40,0xaa11186ee89fd085a17ad38fe34cc9804b21668b35c4c4f7c4bfe40,-0x230811ad9d8a9ab42e3e2183c7af454a95cf23702959e5d6c9097b00,0x5b0774e7fc8f959aaa994b84545bb2e84492ad988ceb27abafff7300,-0xbf4acc234dfe151f8f35d84b35f0640aff5efa826b3872ebddd61890,0x14add0c5efee96a7fcad7b1aa779d4d83b47f1205c05b7eededdbb990,-0x1dce6becaa31de1defea53327cd400d1e4cb9d1305c854be7fa797f80,0x241e09dfaef4b9d81de1743c80b13261f10062d604d852babdecd0980,-0x25032bb826cd5bdf99103bc764c67f7042decfd42a60e29a52da48200,0x2032e1664a865ca0e780bb3506a1f9f7bde30e9bf9a7ef423a6756c00,-0x17d2fcae13fe97c9160b2a38130b89431f0bbb5ce17f9c0daec690680,0xeff15274c3eada132c37bbd349a453865409927292890979dfedb080,-0x8051ec6674aeef151469e492fb8987a091228008bdc557b98c701e24,0x3a2320f3e0d38e6f65d77eeb5f1e056e99721851210a22983ebdd264,-0x163710dbfcfb0da58c2ca0619ad8850d426aff7e73965fd9a4188ea0,0x71d7d4b33eeb5159075aa76e6df641c6d6d4bff68add3a1b20e2520,-0x1e50a0cbafc936b77b2d419637ee472ac9cacd521dbee7b967b6bb0,0x6a4649a845da60851348c4b172e48ea5e55b97d490b6700e391d30,-0x12e9270fc674cc77714e49bb267ee778ab6786db3b74aa8412d6e0,0x2b043439fbd2320405e607730d44838c8cb94111e192af6808360,-0x4c98435afa31c6a7f23ce51d4bba1148e8cb9bdc20638816e5e8,0x680c14d91664f8bb7d6e4880116172da37ef8dd1945051a14e8,-0x685dc61c549c850906750c45a2f8f47688c0ead6e5dc3f16e0,0x4a21b7b6412b66cf909a6e2a5572b23b820fb9dd5c26a4860,-0x234e19338c1db76cf48b3aea1eaf9278d0614ff1818b6b70,0xa7b55756c875bb57f120056293ba7ae98e6183720bfbf0,-0x1c164846cee6b38aae2d1861175063ddbe7e902be63a0,0x24caebbdc352bf0af8b4c4dfe8ee003bf5aaff4f320,-0x12ecdf14bdcea3c096c7ea9cbcdf9944e2ca60a04,0x29f56c5582f85ff001a132d8f8c096d46be9c4,-0xaf056967512a82ff2c46f4206f6a000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 18 74 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 74 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 41 indices rho q24 m24 24 708108630396700943615901696000 23=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 41 indices rho q24 m24 24 708108630396700943615901696000 23 17
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<25) : intPolyRF (mz e)=rfPoly (C (708108630396700943615901696000:ℚ))*rfX^23*(1-rfX)^17*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U5C23
