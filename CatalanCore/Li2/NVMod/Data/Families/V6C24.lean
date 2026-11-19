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
namespace CatalanCore.Li2.NVMod.FamilySource.V6C24
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,6,24,size⟩
def bases : List ℕ := [0,1,2,3,4,5]
def indices : List ℕ := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def num : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def den : List ℤ := raw_ints% [0xbadbd721e35c30000,0x10f1fcdc34c8441000,0xb7baac2fd31263e00,0x4d48b8b91ed3f1e00,0x169e63c6339cab720,0x4e46efe187ea23d0,0xcf8813c4eac4420,0x1af193ecd8fdb58,0x2c771f20ce7d6a,0x3abf71e6f8fd5,0x3e4d00ab1949,0x34ea8f6690c,0x23bcfd15c8,0x12ef93efe,0x7b31d8e,0x2519f4,0x7cb6,0x105,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0xaf,-0x4d,0x4d,-0x4fe1,0x4fe1,-0x7ccf9,0x13f84,-0x14ddfc,0x5377f,-0xb24bf,0x9f3184,-0x65e24,0x1182e3,-0x200db3]
def rhoDenominators : List ℤ := raw_ints% [0x28e57180,0xc9180,0x1923,0x8f,0x478,0x28,0x5,0xf5,0x40,0x240,0x2d,0x1ef,0x6e,0x11e,0x1b5f,0x2cb,0x2080,0x22880]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-6) 0:ℚ)/(rhoDenominators.getD (m-6) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 6 24
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 17 li0=padCoefficients 17 (liCoefficients 16 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 16 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 17 li1=padCoefficients 17 (liCoefficients 16 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 16 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x41,-0xd0,0x1ad,-0x23c,0x1ad,0x0,-0x1ad,0x23c,-0x1ad,0xd0,-0x41,0xc,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 17 li2=padCoefficients 17 (liCoefficients 16 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 16 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x8,0x13,0x20,-0x13f,0x3c8,-0x6d5,0x840,-0x6d5,0x3c8,-0x13f,0x20,0x13,-0x8,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 17 li3=padCoefficients 17 (liCoefficients 16 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 16 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x0,-0x37,0x140,-0x37b,0x580,-0x483,0x0,0x483,-0x580,0x37b,-0x140,0x37,0x0,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 17 li4=padCoefficients 17 (liCoefficients 16 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 16 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x10,-0x95,0x1a0,-0xc7,-0x610,0x115b,-0x1740,0x115b,-0x610,-0xc7,0x1a0,-0x95,0x10,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 17 li5=padCoefficients 17 (liCoefficients 16 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 16 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x30,-0xaf,-0x1c0,0xddd,-0x1f10,0x1dcd,0x0,-0x1dcd,0x1f10,-0xddd,0x1c0,0xaf,-0x30,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 17 li6=padCoefficients 17 (liCoefficients 16 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 16 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x70,0x103,-0xee0,0x2171,-0x70,-0x6675,0xa5c0,-0x6675,-0x70,0x2171,-0xee0,0x103,0x70,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 17 li7=padCoefficients 17 (liCoefficients 16 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 16 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf0,0xa19,-0x2440,-0x2f8b,0x13db0,-0x193e3,0x0,0x193e3,-0x13db0,0x2f8b,0x2440,-0xa19,-0xf0,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 17 li8=padCoefficients 17 (liCoefficients 16 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 16 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f0,0x2d5b,0x1fa0,-0x28117,0x2e610,0x443bb,-0x9ef40,0x443bb,0x2e610,-0x28117,0x1fa0,0x2d5b,0x1f0,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 17 li9=padCoefficients 17 (liCoefficients 16 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 16 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f0,0xa721,0x37340,-0x796b3,-0x11be50,0x29186d,0x0,-0x29186d,0x11be50,0x796b3,-0x37340,-0xa721,-0x3f0,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 17 li10=padCoefficients 17 (liCoefficients 16 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 16 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f0,0x23473,0x187e20,0x1bf3a1,-0xa1fbf0,-0x33c015,0x13e1bc0,-0x33c015,-0xa1fbf0,0x1bf3a1,0x187e20,0x23473,0x7f0,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 17 li11=padCoefficients 17 (liCoefficients 16 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 16 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff0,0x71c69,0x85bec0,0x2376a65,-0x610550,-0x81f1d43,0x0,0x81f1d43,0x610550,-0x2376a65,-0x85bec0,-0x71c69,-0xff0,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 17 li12=padCoefficients 17 (liCoefficients 16 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 16 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff0,0x16544b,0x289c0a0,0x13e3c599,0x29ff3810,-0x12a4c9e5,-0x5bbcd140,-0x12a4c9e5,0x29ff3810,0x13e3c599,0x289c0a0,0x16544b,0x1ff0,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 17 li13=padCoefficients 17 (liCoefficients 16 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 16 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3ff0,0x44fbf1,0xb8e4640,0x8d7629bd,0x2643af7b0,0x385b1a30d,0x0,-0x385b1a30d,-0x2643af7b0,-0x8d7629bd,-0xb8e4640,-0x44fbf1,-0x3ff0,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 17 li14=padCoefficients 17 (liCoefficients 16 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 16 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7ff0,0xd2f2e3,0x328cd720,0x38086f2d1,0x17edfc8c10,0x488025ae4b,0x68336469c0,0x488025ae4b,0x17edfc8c10,0x38086f2d1,0x328cd720,0xd2f2e3,0x7ff0,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 17 li15=padCoefficients 17 (liCoefficients 16 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 16 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x10,0x78,-0x230,0x71c,-0x1110,0x1f48,-0x2cb0,0x3246,-0x2cb0,0x1f48,-0x1110,0x71c,-0x230,0x78,-0x10,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 16 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^16 := by
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
theorem cache_li (j : ℕ) (hj : j<16) : coefficientsPoly (cache.li j)=liNumerator 16 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x143ef68f7bb0c88d94100,0x1fae794fd8c2dc11fe20c0,-0x17dbe6c5ec092a5ca8ee4c0,0xb8367d4fa4b79b23ff79af0,-0x3ffb90b68bab097c1fd80bf0,0x1108b6080874eb209be286340,-0x39d4e89a9f98091675629dd40,0xa0a755e8b8774bc1863994f3c,-0x1740012a66b58ab2879f38487c,0x2d7be4fcbe5c7737a254ae1920,-0x4bed2b769f16237db7e21f0ea0,0x6cf201cadd6859ae5d6babc480,-0x871573e4cf1a9d4648f7399000,0x914364b4eadba6ad19e1e1b960,-0x87c744e42d7c8a3a5d1cd53ee0,0x6e6b2457ba0544443133d5190f,-0x4e1b315fe203782a35c82340df,0x2ffd5077abd818d6331e5a1018,-0x198b1c25215a53d3f2e2707c78,0xbbb54a803e9d31991301d5834,-0x49fc7938de54cd635f4e82d54,0x18d8c14b0736b7ed15b5abb88,-0x70b0fbf4c1dae44346056c68,0x1aa3c27c66c561f830ffbc76,-0x52b91614bf8c4d934aeca76,0xce9bcc8672bbabde7cf388,-0x193cd820cf03209856d128,0x252a29e14ba8f8c830dc4,-0x270d3eabf2c17856fd24,0x1af24b4cae8d7eef8d8,-0xaa129097a797154f8,0x1d5faf27d94a0757,-0x122c823db38647]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 18 33 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 33 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 40 indices rho q0 m0 0 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 40 indices rho q0 m0 0 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1d1a826e41ce204b84d700,-0x2ccec6791de80eef7349040,0x212f8fa1398de5499dd49580,-0xfbded3ce34cda75f107a5e90,0x55f456f945ff5ddcf30e136a0,-0x1678f1b02f61e552003cb4bac0,0x4ae24c0db6a5aca284716b8580,-0xcc0e8a93946a80cdd0b1930c64,0x1cf339d059a4eaa5398b1d4ea68,-0x377ba8156f8a69e57d5fbbe4620,0x5aab2078638cd8cf900464c5700,-0x7f42b5d32318faf392fce8d6d40,0x9a387f5e4d9e18a757d4c4631c0,-0xa1f01ee2580c59d7fe1ec8628e0,0x93a6e77dc8fbab1dbb67b928780,-0x74fff72a35305a1310a6492e2d9,0x508b45dc4579fbe22db0e22de9a,-0x30189956747d56ad8957a55f578,0x18d7c2bd2059d9dc73861d75e60,-0xb0dbbb76bddc3ac5e2aa524f9c,0x4367146f2241c14da555eb6ae8,-0x15d6a838b4b89a86d6624dba88,0x5f511bb1c27c61d6252fa5580,-0x159e93e8a5cfa24686432028a,0x4030132e3cdad8e087514f74,-0x98a21d39cfd0bddfbeb8468,0x11a8c111624b2a039229ce0,-0x18786696a3a23a2594b92c,0x17fdf484a2e6b0207ed68,-0xf45c665c833414bbf18,0x5783c69147afff34c0,-0xd66ba56e59040c21,0x717da8e15850da]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 18 34 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 34 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 40 indices rho q1 m1 1 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 40 indices rho q1 m1 1 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x29d61b7e7e984e6c8ef5100,0x3f66b26cd1ab8305e3f09fc0,-0x2e33551751c056ca534922400,0x158d8789a6ff49bf06182d60f0,-0x73ae1ad0e8c32d4979abb501c0,0x1db6c1691ecd25b9fa8b4f52740,-0x6139a003898a88f100108e8a700,0x103fec18f8f6ee53962dae5680fc,-0x242cee93034808cc87a1b033cf30,0x43f2d6a4275679fcdd9b680ed660,-0x6cbf04aaa33e4c69ee9be84976c0,0x955d14dd742a627fae1ceec83e40,-0xb0f9b0677b2680d69d3addbadfc0,0xb585c4eda464f9d747c36d42dba0,-0xa1815b9575a2a01049f0559196c0,0x7cbd9f04f220a586d34d16e2893f,-0x5398c885341a738f6c0b9599738c,0x308751605401abe44e60292f24a8,-0x18548e34927f20bf7c9e5985bbb0,0xa7d4de08d2755bb4dee5061f2a4,-0x3dda9d0def1753942701f798fc0,0x135616cdf834341b38587242918,-0x5137618bd0f04f8324999d0ff0,0x11ac5228069a2d8f6fa82c6d86,-0x32287cfa7979a56ab7d059da8,0x71846041985610b7ed89b178,-0xc6ed93af93b695b83168c50,0x10332473ac92270f4456f54,-0xece1eeb6e8ac09b0e7220,0x8aed14f3e462782d7e48,-0x2d192e386435408b990,0x61ceb3c60a85b1097,-0x2c42a21d04d813c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 18 35 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 35 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 40 indices rho q2 m2 2 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 40 indices rho q2 m2 2 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x3c23c785d5faf0bc0d804700,-0x59c02186a895b2fb47366f640,0x406085f794f76a6ff7b8f4d500,-0x1d8c659b02761913ab3ecae2190,0x9bf690dfedee7d7249255a65680,-0x27603ca75539ccd3f50f95dcc6c0,0x7e90d80371c838e6d69261f3fc00,-0x14c491b22c331b1cace708f15fea4,0x2d5ca93f4518b486b7d98d70c69e0,-0x5389ff2e58bfced6b07bb439097a0,0x82fcffb836c32c3cf133f065671c0,-0xb02036db118874871baec028b81c0,0xcc1cf3c32f36bad5a5f2d4ba39d40,-0xcc93575878d21a75856bc8bcd7c60,0xb1ac34533c17f02ffbdb0459cf4c0,-0x85cc845b071aa9a45175c2747ea69,0x5750c23ce196ff9ca657a7f5d9cb8,-0x3149b6e0e6e5bb735db0e8886f058,0x17fd9f92025dc2cb24c7f3f72d430,-0xa060dbcf6ccd9998b938af25657c,0x392a61fa3fbe9579308565fd2830,-0x113e539133e4ba0b4995c7ec1a68,0x45b24550b0da118e255cec26630,-0xe8c7d43050470b8153e0a97b4a,0x277639ce5c02a6ccf1cb994040,-0x54f8134f73f9f35351de4da88,0x8ce1a732f567a1b083971f50,-0xac79495691529096741f4cc,0x92c7543412957c5cda3410,-0x4f3459fa09228f4bb8f38,0x1744d061a2bae1e6cad0,-0x2c9a4948013980d891,0x113f8105a3aa4628]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 18 36 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 36 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 40 indices rho q3 m3 3 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 40 indices rho q3 m3 3 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x56736ed06398ba0e536866100,0x7f1b619fa3b8066913bf7d87c0,-0x59c8b7ce3b8ea794b25e8b24900,0x28904f832e6b2c366e94ef494bf0,-0xd2a497ad411f0290e5b236f4bf00,0x344b2f2316d405011e9bb2e7cdb40,-0xa530b968f26ab44fe458f0d773600,0x1a9f595c44ac9e33a39a3e041d40bc,-0x391388bd5e0d98bfde3cdb17f32780,0x6719928c75e9359170f9a25204a960,-0x9e71e7cab8914cd521a53b4f31a740,0xd0a31158b9d877ba167ca5c0d38340,-0xec940f605255cd1b2ff2a1839ca6c0,0xe7c71aac3d8b54bdaa57e3d47cd6a0,-0xc48eb567933333a474de1d62d45e40,0x905d73f3eb71e742d41d1d039ac6af,-0x5bc3cc3de964848e3e9930351f32a0,0x3261b1bf608b3ec596759711c3c568,-0x17d0265a4ac49294c5af8cbf1ffe90,0x9a4c96342d30057e7a24978ebeda4,-0x35329c885b30b12e244808c58aef0,0xf7bed1e118f6be1adef59e5ec0d8,-0x3c3968bd59a03f16246d7538b210,0xc0edf797ed87d19cb7e365c61a6,-0x1f3fecc992d31d927a2fdbb2f30,0x3ffe026d6a679229703c71bcb8,-0x6454df7fc84950fdf26e38ef0,0x73524d07db708351a7c30fd4,-0x5b4b6086e5d4fedd7c2b790,0x2d4511c59988f7d525f888,-0xc049a465149ebe0263f0,0x14554962b8240232bc7,-0x6b77529fc3caa170]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 18 37 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 37 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 40 indices rho q4 m4 4 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 40 indices rho q4 m4 4 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3840,0x100e0,0x1f834,0x23154,0x189c5,0xb676,0x38bb,0xbb8,0x18b,0x1e,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x7c45ef4b8f2b8b7497e612b700,-0xb417404cd33dae42dcc8f8e2240,0x7d53c9ff8b4b34246000c43dd300,-0x37c2030140ab47d5fb00a73bf0290,0x11cfc16f8c8548c0e7fd8ae37d9a00,-0x459938377c38cb1dcf1d4ee5e5b2c0,0xd8279f596d973d5d8f1a5275296600,-0x223a9b6b305891f09f13c8e617960e4,0x480ed2048243d4c1f32b090695e5cc0,-0x7fb834db6c7a2292e5962bc912b77a0,0xc0734f95debd8b7769b519964c860c0,-0xf84367f3b14a3dc8bd4aea5be4efdc0,0x1138a2894d56c1da571a7df6c731f740,-0x107f5ed30076e0f432305020f2bb1060,0xdaa5a1bba875dcee4eb14ab3ab5cdc0,-0x9cab2e8d0722c3e5c1c1164666dfc79,0x61068113fe4dd57f9829b4ea1e6bc70,-0x33d2d2d9fbb475f9d7e17558c757b58,0x17ca3d78737d1235c6ab53c55c51470,-0x956f3c9e420a122a3a3570a01c9fbc,0x31d68704ea279080c2d28d8224cd50,-0xdff80b200f27e7a192444b1eaae68,0x34635375033f34b2d4c9479d96df0,-0xa0f2d15ab4b6143fcd31b472416a,0x18e6f8afde613c3be7ebbcf50cf0,-0x307a5715f46bf87540619a17188,0x47d53aba76c8d1aa4aaa8f8010,-0x4d751a1b067d71f0e2454790c,0x38fbd99689b2f2b1191848b0,-0x19eebe9fab6e2e947c3e538,0x63658a9cac09c4f56c610,-0x94406dae4ff0479eaa1,0x29d1ced6279cecba0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 18 38 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 38 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 40 indices rho q5 m5 5 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 40 indices rho q5 m5 5 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0xbadbd721e35c30000,-0x10f1fcdc34c8441000,-0xb7baac2fd31263e00,-0x4d48b8b91ed3f1e00,-0x169e63c6339cab720,-0x4e46efe187ea23d0,-0xcf8813c4eac4420,-0x1af193ecd8fdb58,-0x2c771f20ce452a,-0x3abf71e6e8ef5,-0x3e4d00a92115,-0x34ea8f437b8,-0x23bcfb8c03,-0x12ef88888,-0x7b2e4d3,-0x250e3c,-0x7b2b,-0xe7]
def m6 : List ℤ := raw_ints% [0x0,-0xb2a487fc9dce98779a5abae7100,0xff4545e28883bd705becbdddb3c0,-0xaf175efb1c59023df58bfcfddcd00,0x4cbdd5e611a7a1895bb679e39a5af0,-0x1823823d3bb8e84a03b3735aec78c00,0x5cd35885fa8d0b71141edd093d08f40,-0x11b8e47576e87d9c307b935b708b3200,0x2c2323583df20cd206bd730d85a8047c,-0x5b45f4c7a0209d81197bb46bb9890ac0,0x9ecd86976dff20fceb16de7d1ba23b60,-0xeab45b10b16eb9190496393d4c8d3d40,0x128b8f580ce57924ef7143f45e7212d40,-0x142725f7ba9a60a51ccf4273352f26ec0,0x12e2476af9bc27865936f71b7fe423ca0,-0xf487f314954da35244cfef00b3bf4040,0xaafc5656f5ac8cd4e6f4c853768d8c1f,-0x67320eaf4019e84b1c241a61bf985f70,0x35a26138300442a246bc834e94c6e8e8,-0x17ead1f794109d0b09ff1eaa89f5a310,0x91a86f6e731e4f3dba783c49594fce4,-0x2efee5e1d3d4a5cc989df50ba815cb0,0xcbcceaa7542f498ba96de24d154358,-0x2ddde7d534e035c1b7d5c6aa445390,0x871e184a70bf8c63e4426c8fe6e06,-0x13f6c8526d34ef2258f4fb99e9d50,0x24ee75190f73ff1c6a9388be9b38,-0x33b036971d2b62bc37f5d0ba870,0x343f2500eb1917862d67356214,-0x23aee1b6fbbe2a07f8d38e850,0xee29d643dc2b2156c2a4408,-0x336a016a83321ffbc24470,0x43874bb93fa83547d3b7,-0x104346b2480eb967c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 18 40 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 40 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 40 indices rho q6 m6 6 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 40 indices rho q6 m6 6 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0xe7,0x1]
def r7 : List ℤ := raw_ints% [0xa89c5f1f94282f50000,0xf3ead6d41827fa77000,0xa4ba5191642913de200,0x4504e402dafe2cdd400,0x141ba34f1f738ac1fe0,0x45381c381e6a7b9990,0xb65f5ad8975875510,0x17807466f2e22a848,0x267063d7ccc34f4e,0x323b4dd55dc8409,0x348b847bf541ea,0x2bdad75afa8bf,0x1cf0df6a6fc0,0xeda5ec4b2f,0x5c3a7229a,0x19c78659,0x4b79fe,0x7058]
def m7 : List ℤ := raw_ints% [0x0,0x100cc837b22d8fb2bede26cac2700,-0x169fcdf75466a9a5bda249a108e640,0xf4d253b64ead5d3409f8a004fdfb00,-0x69c1576f789f5a80cc5c36fa689eb90,0x20c4a4d721740b9ef7799e7460a83800,-0x7c0fba29eee6e08d5b44fefc4d5ddec0,0x174e535e766218e64cc84869db1b72e00,-0x3913bf2d311e26f3ef32abbcaa60e1724,0x73fd2e2accc3b56491c6ebacb118cc040,-0xc62ad8a53a4dd337da4a1d91b0378e1a0,0x11f60d6306b9ab17e677c484d77c6978c0,-0x1642e0dde72825e7321d569c0b9e57c7c0,0x17b1a5d957ecf2e46d4aa9531f79b72340,-0x15b92b08040a91c1273a8d6eb435fdf660,0x112ecb4a02a92af3099b792ae033f07dc0,-0xbba5cf399b679dfa8b1a3bb99c87a7589,0x6e64eec71b964c18a709d593361020d50,-0x37d774ebe6a759a663a1c2c7895f65ad8,0x183191d7fc99c76857b8d104d29527070,-0x8edecf87ced1cfce9e4091e45c5cab7c,0x2c98e70902fb14ba404328a4acd69ed0,-0xbaa08661d5a420e6f937b5ee710f6e8,0x2868cdd1cea97474eb8a19445b68ff0,-0x721fb914d1766c313e519e8173830a,0x10191155f6869bd1bca42e3823c0b0,-0x1c49489cc1a1ab7c3eed7a799b808,0x255ed5e5cedd20667af93d25b010,-0x2361b2706cc4c50e12d24ddc7cc,0x166940a96327d73a5550f73630,-0x88f2b7c332d8b6ad3c7f4eb8,0x1a9bbaf31a5f5a80dfd3010,-0x1ebeaf4899466aa745431,0x651f721a52d8c39a80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 18 42 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 42 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 40 indices rho q7 m7 7 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 40 indices rho q7 m7 7 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x7058,-0xe7,0x1]
def r8 : List ℤ := raw_ints% [-0x520069b0c71e7cb080000,-0x765280950d0801b708000,-0x4face8a948b07209de000,-0x2145a77eebbb299946e00,-0x9a80d34ffdb4aaff1f00,-0x211837202f05ef7b2fa0,-0x56bf5da9707fe89d170,-0xb1c94679fc23e29130,-0x120b5f4a9e6fb6d428,-0x1760ed66b788351ea,-0x183365e5c0041d0f,-0x13f017166b41a36,-0xcf14a3ad75401,-0x680451d25790,-0x2735c93fda1,-0xa84748946,-0x1cf2f837,-0x270fba]
def m8 : List ℤ := raw_ints% [0x0,-0x17125fd010217e90f25f57c3778100,0x20188485814376db23fd502065b2fc0,-0x1569b205ecc1b196657ef1e3a981ed00,0x91eb2c2bda122ecb649049c39215a9f0,-0x2c8e3d6651da9e8cb2e4ac93bca642000,0xa6259237fa6bd882d4a97e6d87b368340,-0x1eb93b2aecd33b539e2db03b30f08b4200,0x4a04cecf5f9454dceda744d4eda696a43c,-0x93de5b71ac79d31512067c6b6589a65bc0,0xf82bba309dab25ab15545d1563bf614960,-0x161408309b4ffb44d23fea98b401b07b940,0x1ad5f5b13cfa2822bad206bffe04050ab40,-0x1bfc1f7305ee5a0e75671bd12092dbc0ac0,0x191ca67442287189cb0b772c0e134b78ea0,-0x136b249ccef3eb45183d5834386cbb1bc40,0xcf0dac3325a1344f7d0b02d91d62691c8f,-0x76c3cc6095c6c743bca67c4ee71b56dfb0,0x3a7b2018044d326520a6102fc0568a8768,-0x189ee1c78ff3d80b9846aebef535a24a10,0x8cfee255ddabdf1ddee8c53b6f68a0924,-0x2a95425a72e43c576f1de825bc5e572b0,0xabf48afdeb54f45e93bb8105fe1610d8,-0x23d14a1584904ec400dbdf731e497690,0x60f57ba98fd3d3c09fec531cf3b7166,-0xd0d8622e1e82199e351801e914f2d0,0x15c6984c1daf59c80ee0c6bd0fb6b8,-0x1b23fb0ab5f8cbce4312f46085170,0x180cae4b41bfd87a4fac22314754,-0xe1d23e477bc24545ec7ec60c50,0x4edeed5b21f35636195fd1488,-0xdc6a19e06064beb7b3c8970,0xdfda9d4b6f3c4119cb9a7,-0x274649aee83ce04e700]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 18 44 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 44 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 40 indices rho q8 m8 8 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 40 indices rho q8 m8 8 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x270fba,0x7058,-0xe7,0x1]
def r9 : List ℤ := raw_ints% [0x1c82f86b7eedfce7cae0000,0x290c7fc939d268c235ba000,0x1b9267286c02e2a49fa8c00,0xb7b26a53378e8383ffec00,0x3523f42a00c2aa2a4f7f40,0xb571cbfa437ca41e81620,0x1d98f75303ba5b28c2fa0,0x3c5b5e69bf8f343db480,0x61717c0e502e6a3c3d4,0x7d6104c4b52038279a,0x80b800aa1e4675420,0x68fc5ab173ffe9a9,0x434fb270eec711a,0x21494b19a3528b,0xc4be45ae739c,0x335df1229a7,0x882eebcf6,0xae0106b]
def m9 : List ℤ := raw_ints% [0x0,0x212a69bb173025f05c690e28fbc9700,-0x2d8d179c9ebad2f6bc65abd2d2704a40,0x1dfd64653eae9927132d7f3677c688b00,-0xc99480afd7c1d5e57fd6e81e246ce4490,0x3cae5d6280e65873fea70bf0bbe289f000,-0xdef4777e05f8747d73c73ec5b1919ecac0,0x28994b79cf78524bd30cec713c34d2cae00,-0x60413efe82abde7b594ba796884893c7164,0xbd1a1b2486c1da5c95a59b6579322835240,-0x137e0f62d9d504e827684348bd47aeb6d3a0,0x1b3e5375e7567562084f9b8f88daf04254c0,-0x207c4da8fa9bfc580fb82f81a00d3ecc29c0,0x2133954823447124b85b7bdf324566d83740,-0x1d2b1858faf9e7c57d187af7f51f15cd4460,0x160e77e79d6174228bdcf03c289b3657e9c0,-0xe5aecaec2c332f66e46da02e8c30eb40799,0x807a9f37a74e2eafbed7e553c167d0745d0,-0x3d98a72c8f54d4f7c8f8eba3724ec0cb458,0x1933d8e8bfa1e7f61b29c14382adee53370,-0x8bfa3851e58a898c4688520ecccefab93c,0x28e78bca1e1ef56061d38c0380cf4985d0,-0x9f62be71801d8116d93bf81605c4b8968,0x1fef1f481216f4e2af30c99d097a042f0,-0x52d7b634288508cb6f0d65bb9518b4aa,0xaa3eaee9afb9f7636dbf42b9497aeb0,-0x10d877764d9343c443ff87f3c9cf488,0x13cb827388f79fd958f19c3e28c510,-0x1067487a638c88c0bd53bb5390c8c,0x8e915e00ba9746f9acefb8d1b30,-0x2d7c35f483c79b750988e52e38,0x722542405385c61f017a8d10,-0x65d0dea6552c89876d90c1,0xf3e9268171d76429a00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 18 46 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 46 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 40 indices rho q9 m9 9 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 40 indices rho q9 m9 9 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r10 : List ℤ := raw_ints% [-0x7f022bf67dd93e9ca8810000,-0xb6808488f8865af378c4b000,-0x7a50d5934a68ac3c0b804a00,-0x32ce9668db40550e1146fe00,-0xea80c9c0ade5f19cb2c9e60,-0x31e2481b149ab5dbcca78b0,-0x81b835a42522ba405a6340,-0x1076bebb8ebae49349fe28,-0x1a736ee22c2144aa756ce,-0x21d743f26a69f75aaa33,-0x22828615a37d2bff9e9,-0x1bec23b98483a753e4,-0x11bad305b3a24b0ef,-0x8a9eed43170c310,-0x327314b852e7cf,-0xcebe58f2a560,-0x216642d566b,-0x293820021]
def m10 : List ℤ := raw_ints% [0x0,-0x2facf7fcf155368984d7045ae9f19100,0x40ac5c789cee1868ccbb42e0e6d80abc0,-0x2a092c50c2d0162867db099d5b85b5fd00,0x116ce6f9738b63760d2d86e2424e92728f0,-0x52c60c20ee2d143a2a04165dd67b59cf000,0x12bc69c9ad37110155495421f2de6c23b740,-0x35c62d1ed883c4048ac9544bf28e174b2200,0x7d82e038baf2bf197f89108f833c16723ffc,-0xf2941a1871f75a91deb7494ae32424edebc0,0x18949771448595a54b4e9ded7d35269b02760,-0x21be73aafe25c0cafa4865c666921a3d24d40,0x277c6eb74668a83ce5b410dbb7383dd2ed940,-0x279078725720d535c67c5f44a35cddc6af6c0,0x220a131a553168da9eb110b3f42846afab0a0,-0x192d6d6af8bf86d9d5848ddf9d67ee63fa040,0x1001d47200eec4e56b6281549dabfd05ed3ff,-0x8bbe081d13791a6cd21049802f96cd703fb0,0x413dca07670d8382309d41466539af21b9e8,-0x19f24224183753945c49e06be91a4dff7b10,0x8bc6c88ece6511d71be6afebb50e8041d64,-0x2785ab878aecd564153211a68e642aad1b0,0x9497ffd3c2f52f8474f78be17f6eb1e258,-0x1ca233197b0683b32d58f3e63adec8bf90,0x472b11ed8f072f67613a1c612f9702ec6,-0x8b7d6a6032d62a652a5fec1b60f8e9d0,0xd1798c9ff1b6d336796a9137a113e38,-0xe7ed470c0a46caef552352b0d6f870,0xb396986dfc22b5654e829466b1c94,-0x5a35d4ad93dbcc9c1e60c6a7a550,0x1a433d2e31451c1946c53ae8108,-0x3b1f3d6021ae6bdee5f2c8070,0x2e48ede97e539fe19406a97,-0x5e9e623b365e4ba7bc00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 18 48 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 48 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 40 indices rho q10 m10 10 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 40 indices rho q10 m10 10 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r11 : List ℤ := raw_ints% [0x1e162ce8791d27fbeaee230000,0x2b2886a37c66140bf148451000,0x1cdeacdd9ac2952eb559294e00,0xbf7465231a16845dac5a29400,0x37184de23e395a214c01a9d20,0xbb004ef56dad4c0f59a1ff70,0x1e4c265fd9e464415faa4f70,0x3d4e0b2107ad30f29e0e318,0x62167ae96ed5d235282c82,0x7ce53892d0caefae433a7,0x7ea897e8667ce0c59836,0x65d02833077311b90a3,0x402581c2adc0887ae4,0x1f0d84785aaf86dcf,0xb2c0f3658c20c3e,0x2d2191965d70a5,0x72897d896e16,0x89ff5ccb3a]
def m11 : List ℤ := raw_ints% [0x0,0x4488a47b9aea7e65aef51642b04b40700,-0x5bdbe367a7a05fab0f6db679d54dab6e40,0x3af771b8e826ba2a7cc29ae41cc374ebb00,-0x18211f357554d89c079d54cd56367031ad90,0x7115bffff275302cb267e7da83f878b8d000,-0x193d83d823c9b7d9dce66c67ca9489d3a76c0,0x4763a5c9c5c35f67af0950fd74be7ffa00e00,-0xa418bf3f9f41ad6f2ac2c9aee86ebecd8efa4,0x1381e6d8d045cc7228ca6077133d59365d0e40,-0x1f19db6b36fb85462c67d0b17dddf3085585a0,0x29f34782a7a97a0dc43476e713022b916f80c0,-0x3030322d307eb3d556ef1eec519cac2a260bc0,0x2f59c032f9b0d9e0da6bf4f8dd5a133c44ab40,-0x27e831515fc8450e3484bd20f74f8aa9ec9260,0x1ce14b44d5c1b5d38fc0257f1c8b284da385c0,-0x11f0bfa38eae63c52d9360451ab267ff3b0aa9,0x98ccfc3069bc0b4f4508f20dcea5b043818d0,-0x457b20546985dffd8018e73820ed28d206dd8,0x1adca2c3de4b96e6941224f69c5d9c74de270,-0x8c5e773b325bcc38efe42bb8ab7dea67bafc,0x2667737f54c9e1c4c2d167b5fe34ee57a2d0,-0x8b506756974c3b6998dce109d7a538b0be8,0x19d0c43f2bdbc6da412461de6ea231ec9f0,-0x3d75fb397229acde4c7cabad5996b3b84a,0x72da19117de33390105df3eaedfd9edb0,-0xa38559ee7306154f7590ae094f357108,0xaa7a2b914119f57300dbb3ed9be1e10,-0x7b40851f6121357e581972bf25c54c,0x3932835b37e812e9b7990f9a3de30,-0xf2de16cef05a74a0eb50a55bdb8,0x1e9fedcaa4c08ec95b327ca610,-0x150795f6840266076c8eee51,0x24af206f9516941d52800]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 18 50 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 50 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 40 indices rho q11 m11 11 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 40 indices rho q11 m11 11 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r12 : List ℤ := raw_ints% [-0x64ba0ad7c56762d5e8dcf2e0000,-0x904515439b81ba0173e29f8a000,-0x6057a345d459ba4d6e5758efc00,-0x27db1780b4c873f570c3bed7e00,-0xb71def83186659c8d6c1014940,-0x26c0868a21b070c9ebc4177000,-0x642ed16a62f5520e16eeacfd0,-0xca1662a5041cae41c17c2a80,-0x142339bc9b6c6fddaa7294ec,-0x1989a643e971ea702b850c0,-0x19c7071b2f5408a62869e3,-0x149bc61281bed80aab882,-0xce6c721da2c5c60f6ad,-0x632c190b162e2b34a8,-0x235b0be642d13de5d,-0x8d3d6aa7aea510a,-0x16183ae80b2297,-0x1a27dc11c40c]
def m12 : List ℤ := raw_ints% [0x0,-0x62846c71aeb115b22b804fffdd6c2ca100,0x8285c0cd214470d1f6ba6f061fa36cee7c0,-0x52c7b30024ab0568bc9ca7133e614f24cd00,0x21736f734803eb0a7838c870ce162699397f0,-0x9abb4c9a2b77d6a152d6b1064b2d010d73000,0x2211294eea2847a1b16382c738a68f69502b40,-0x5efd25a32054b74911d330770fe7d99e5a4200,0xd71b1e4d766fcd068b55dea50cb73981fc17bc,-0x192c93d8b2ac8c91a0c976e196238c29ac757c0,0x277b3f9c72b3fa9e508ca2b5782ba206a27a560,-0x345789c862f092a32a7df118b28a49e6b648140,0x3b0a5c93007fe5b483be7241a9867b6c273a740,-0x38e8e339652b05ae6d9b8951fc0b4417d7fe2c0,0x2eff6889e0a4c5543940ed1e285cbfbb850b2a0,-0x21491127187119952fa483ad347d4868b816440,0x143534919c1a49515ffd7b9f4adcc87b1f8526f,-0xa7f2d05e2cd609fd2148c8f22b2210c0fcd6b0,0x4a648c49b5599602ca048256ad72fc46d54468,-0x1bf64654946883503077fde02e448a53a7e410,0x8dbebfa111b89cd0867f8fa051e85608c45a4,-0x25864baaf47d0620614f9c141e2f4b80ca4b0,0x835441427b324230bac148a07aebd8e6fbd8,-0x17660c7028e975ca368d20c3593063acb090,0x3558be1906460aceaa78eeadcea125e3226,-0x5f02a322625478cf7404a998e84da8c6d0,0x802f3248a0a4e855f3d58f2887b308db8,-0x7dc112bdbe4c860aa91d2bc7a4810770,0x54d25da0d4e36515ea5c8d437cff5d4,-0x245515b37da8484e686007f4300250,0x8c7e61d05ed9c84e6990bdab8588,-0xfdd011aaeb66a7a41caa2e2f70,0x98cbb20e81e48b5b931baa87,-0xe36fe94604a7a7e6b7000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 18 52 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 52 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 40 indices rho q12 m12 12 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 40 indices rho q12 m12 12 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r13 : List ℤ := raw_ints% [0x13176bf91bd47b92aa086d1240000,0x1b4eb7c57c523e1df9784c042c000,0x12354bc8ff2f955d77913894a4800,0x78513a3874386bfdfe8efa5e6c00,0x227c09d835046283a78f56e79780,0x748468654decfb7f3ce0233a480,0x12c819bbb8b11ee55ffd6444180,0x25c8c2ba688738c4e7889ad850,0x3c0ef25e2aaa13cf54c40de78,0x4be63a09f594437bc60c3d10,0x4c4eaf6bb711aae6e81c2ac,0x3cb9f57cfb407b379db2ad,0x25d05d680ef6f72276cde,0x120db5afc33a2266753b,0x6637cf57bc4f48e600,0x194b8e2a8a5bc2913,0x3ea104494acdf7e,0x492687611bda5]
def m13 : List ℤ := raw_ints% [0x0,0x8d9e5be36b1e8f301e8872ffce4b8027700,-0xb9878ec60c3d8036696d7d9469601d86d240,0x744c4ce48ed2089ccb504995cb57cf82e6b00,-0x2e6cf8dad7c0736f2c8cd682992726f9eba690,0xd408371ae4e1d1b6bbb9ddac12044608675000,-0x2e10e48d76af954b598340cb49d2295ca94e2c0,0x7eab87ceb16620eef7c18f3ac702949f414ee00,-0x11ab204eb9ba6a1a7e4262a014c5b8632216d1e4,0x2094de5bec6152a5c3f52f76ca4216fbf7a17240,-0x32485c1b2eb162554f283a55b7c510a170f0d7a0,0x418a64199b4c6c597ad6313e7ed07c8021d3acc0,-0x489de76c45e7ef780036264d9b54669205640dc0,0x44aef5eecb4050350ce6ab9196b6c680007edf40,-0x3797fe02c1d6ddb59660b8a7090b157934354060,0x268adcb9c823252717514d5a240928f84a20a1c0,-0x16df99354b75a1eed679044c9fa066adcb16aeb9,0xb989bae3465580cc9eccf522544af192ec495d0,-0x5011c7bdd78c6ec1c81486b0f9bc88c7509df58,0x1d434ffc254f4f5fe4f5f3e3d792f0018f7f170,-0x8fe87c2b1847e09cb430c303dcec9164f7f8bc,0x24dcf039d2eaf45213c085c7c9676a4004e7d0,-0x7c75b0659ad54c535c4764c755b67513fd668,0x15513357935b2656a5bc1d401da75703ed0f0,-0x2e87986c5fccf4b51f5fca60a9c64c2cf5ea,0x4ef3346b8a25d7dcb68112172838933c0b0,-0x64e2739dbe0c631992fbac1c3cd4ab9588,0x5d12bffed0809c248f6f7cebbb18f5710,-0x3a85d88abc9f392c9a62ac058a89ea0c,0x171de9dd38151583e37c0db7f024930,-0x5154f2cf630feaeb2f03123122538,0x837690baa70fa4a207c9a537f10,-0x4559341d5e72c97a1dc8d34e1,0x58156e5f8cc3c4f327a000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 18 54 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 54 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 40 indices rho q13 m13 13 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 40 indices rho q13 m13 13 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r14 : List ℤ := raw_ints% [-0x3564cfcb68f0f5665c4f1c9daf0000,-0x4c47690648204f4df9713d928a5000,-0x32caf67bfd0a444b82171347293600,-0x14f2099a4fb23b0ef04126f78a0e00,-0x5fe40b236c66f82811aeed79c3ba0,-0x143641b681d0ba1b995b360420d90,-0x3404c30f3cdeaa776bfd273fe420,-0x6866fae60f6e4658ea5fd3c1638,-0xa581ce7029b8a3bff63f1d3f02,-0xd087fd1209dd0650669fc16d1,-0xd0ef1f0819108e504dbef3fd,-0xa59eeba91506b6ae5a9ce10,-0x66aa5c72f8572d12ddff3b,-0x30c24ec6165c81addb2d8,-0x11260bb452ae7b4b6d4b,-0x4367f177ec5dfdf844,-0xa571cccbe2bc963b,-0xbf343bcb6979bb]
def m14 : List ℤ := raw_ints% [0x0,-0xcb93a416e9fbedd52be4254fb88c8838b100,0x107d0e2778eabb19a06d771bf4dd54dbbce3c0,-0xa3820782ce8e83939a87a2a2db573c184f9d00,0x4081044e269ca72e312eac2348fbbdcf538f6f0,-0x122fa2ca650062f48a1c18d436ca67ab9fe93000,0x3e679102ce132e1905a223908296130379dfdf40,-0xa948df6471259d24bfcddd018a28198e26886200,0x17475348686071d7ffd141541b8ed66063bddeb7c,-0x2a49f4731fa2ca41715647509be470886b9e373c0,0x403e1cec094ac320984166c533f61fd941fc70360,-0x525ac06828e6651b710acd3f5fd6c70e3ea237540,0x59a785b683ff1e2a33d27961d8981a7c90c1cd540,-0x533b45f8b1ec602edc11e4899863edf12cb8c8ec0,0x420c4bc070f1703bae5a35b9365e458428f0dd4a0,-0x2cd5aa4273403a7d850a9708bf1b20267c0b9e840,0x1a03dacfec027b3a88f056f29299eb827c1f2c7df,-0xcdfde603e1cb97c760d425ed91e91a8ba134d9b0,0x569f10a0e4d0269f37dd2901aaf48a2e638c36e8,-0x1ec8d1af0388d7dbe7a27d714f96408f26577d10,0x92dfc889bdfcfa8c507b049c29d3521fc2671e4,-0x24673dceac6c25bb084be341adc7694d18437b0,0x768ed145393046278d86af72882d70b4ed6d58,-0x13847e961a1cf3ae124d014b4d6163dffa1190,0x28c63e7aa35408b0c1ddb8bd6c14894560b86,-0x41e2ff426566031260d8b370428380348bd0,0x4fb2f3725fa5fdc781bc6435110790d1538,-0x4519c844ac059a50c57fda13d4c62be670,0x2878fd0e77018fbc7e2d0b9fafb3de314,-0xebae5e7bdefa25699f8442e879d7f50,0x2f1c878850182ad5c8ae0dc7af1208,-0x44153f4c774c0701e64d17b9ee70,0x1f753647cb0b1679a45cd13977,-0x2218a9201a308fb4f4fc000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 18 56 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 56 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 40 indices rho q14 m14 14 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 40 indices rho q14 m14 14 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r15 : List ℤ := raw_ints% [0x8b9025cf1f696373749517570710000,0xc729bf518d8c4bff8d14ab46798b000,0x84754cbc461810ed8276fc9d5b2fa00,0x368c573d0ede78bc3041b55291fb400,0xf95a94bf9b2c06b219e9608c37d660,0x3478a4f8533a600765a26bbba93d50,0x86ca9d26b04ef146b6496d4e6d5d0,0x10df7089e3f53ba7f8443be99ed28,0x1aaf832034b6de51cd2b115aa036,0x2188b5b041580a907d69cb97e95,0x217fa9dfe9e2f51d9733e3e282,0x1a76db0e401d562232fd273c7,0x10575cd50b3e6c2f4d88a308,0x7b9f6af1833e9c4c27124f,0x2b4104ef77681e72f01e2,0xa8fe347b36b4a26dbf1,0x19bd4aa11d55f526ae,0x1d7e742a7fcc856c]
def m15 : List ℤ := raw_ints% [0x0,0x124a43be0f05a25e26f17f5a2994a03d17e700,-0x177458cbccd115415a6db85b2b29ff043b87640,0xe60c3866ddab93587f5d52ba8d71542aaf31b00,-0x59b7f77f041b62322677bae9e7acffeeee4f2f90,0x18fe34423a04c6972b22d64a2ae173f46be805000,-0x54b0543dc696cb3e4c0c1f1d6c74f64fa4ada0ec0,0xe2b7a4fc3089d7110385df271fb3c4995ec45ce00,-0x1ebeedae8963a5002cadb64f60ef5006227b205824,0x370ac8cdd6270e2716efb4c1089a61d7797daeb640,-0x5255a0a61666a3ab96ca32f3bf9b78ea9c38a649a0,0x67d64233eda7a58377af6b8a185306aa6c70b798c0,-0x6f1a1897ab61027a25b5e67efa5b143afdf0f8afc0,0x6543e6b75b7f78590250a158781e7ccb69aa065340,-0x4ecd920ee45fdcd9e5057f77f696f71447480ece60,0x34638ab3b2804d5ad8381bf16bff0b84d8bb0e7dc0,-0x1dba3e84a82ec9c44ae49be17492d8e68cdc2b83c9,0xe5d135ef0e70385d1af3936819d2b862c08668ad0,-0x5e2dfb235e4c7e9dca0d49acada0c133dd042e8d8,0x208ce9e1a5ac53fbbba92e02ba21afead73f1b070,-0x96abfb556f9ba77bc4d0bc8f2f56b083aec8527c,0x242208f0eb0356ffaf2350359cdb4f9e6dfddcd0,-0x718040de40cd73c8372564ea1fb55398bd0c8e8,0x11f4b013fb93a867625be865f024f8685ec87f0,-0x23e4725e13e47cd9c1154e4fd15e59ff822d8a,0x3735fb79e5f05f79906133bba65cc1a6bd3b0,-0x3f3012c2d3b40fd80a1522666d941b8e8208,0x3373e38ed82e248c644ecba248497f06010,-0x1c0cc88e616c8007a17f756353b7381acc,0x965fa3efab3a8d6a678c82d8680d4430,-0x1b4d7ccd425d63fd3e06ee6855b84b8,0x2340c40a0abadd4cf146aad67a810,-0xe43266a965744449dc1f8ed471,0xd311a80ff52e1efa98a8000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 18 58 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 58 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 40 indices rho q15 m15 15 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 40 indices rho q15 m15 15 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r16 : List ℤ := raw_ints% [-0x1587345d5c4457b0fd2f26b10fd440000,-0x1eb0f6d80278dd81c799efb072895c000,-0x1463bd01ef43bb7ced009d1e09abf7800,-0x862f47cef8c18dc039288c35f383ae00,-0x264912ed8d41b77af837153057092d80,-0x80b59070134862fcd9d0bda28ea5560,-0x14a16313a132e92928d0c371de82030,-0x293e2456c94319b5e4eb9712de6b50,-0x4117e4cc7231a7f1b1910e6230d90,-0x519bc97b6f1123e7d819042bb6a6,-0x514f3e3ee07d2f5e5dbecc41937,-0x400bb164623733b3d0c233aa8e,-0x276a236b5e54d986b9aa3a499,-0x12908775f874b44235bfe620,-0x67789520fff51800ec2b99,-0x19233f10be10a2963b50e,-0x3ce54e378b2a1e04ed7,-0x454a1ce36f58ee06e]
def m16 : List ℤ := raw_ints% [0x0,-0x1a4ac1613598196757fb27119bc5a657d25c100,0x21600bc32b0c15f7273c39132768a38194129fc0,-0x143e4d91058a49c9f3373d756306136c7be236d00,0x7cebd686d5af7adb98522b73969ec9e092de245f0,-0x226553bb8f78fd45e939afeabcce26fb1f14823000,0x7321959f3d2f58dd1da6ded792d8ea3ecad866d340,-0x13044a71a044e96a1ad9fc168cbb62efde823bc8200,0x28b4dde9afcb7ea1c27f255e307be8fcab9785f7b3c,-0x47d687b6437cb4985eedb056ee6451adb2311ff0fc0,0x69d821d9477c410af7cb2b51d4afe9f44f9aae94160,-0x835d1ffa65a1c70dc8cb6401a8bec06dcdeea73a940,0x8a2f055df19c4cef274894c5322ed1d3b43efe56340,-0x7bb0c704edb5f695b4746244a1ff0f375246a7ffac0,0x5e6a23a496eae9b2e7dcbfd9885eb22a8f3a29d16a0,-0x3d7c6f71c4c3190745ca2f08cfb53b02253023cac40,0x2220657ca58f821dd487cfa95ca74c9e94341a2a44f,-0x1019fec50be1ca6e0044793fd64dfce738f48c47cb0,0x66e6715d96331615252b49ab3d16c9da8dd7795168,-0x2296e8900690a6a9f5d32a8b7d34d189de6c9c2610,0x9b57b5954e4d0ff89a6e73aa84970a89707fda224,-0x240afe7ebc9c859982fda578700d9a1f3d1203ab0,0x6d2ff0cc3bf9d6fefda3e54fe8ec9dbef3d6f6d8,-0x109887a7442e86df5d6df3c623dddecbec400290,0x1fbb68b9538286d78bf7202029af8f90be5dae6,-0x2e72470deedc318d616094e4f06747d72700d0,0x32444d715d31530fa66f3d3875d28159014b8,-0x266a9eff53bd040a57bb3be9194b58eb3570,0x137a888fc27cf9f2e3a192f3b4567876454,-0x600e47b570c0c4e9dc14f830c3b1f0c50,0xfd43919118cfca5dd7e011b3c116688,-0x123ff20b5cb33c3d59682a3d011d70,0x67679f2301ff474f9bd6d0b4767,-0x519f7c99e1d147019f870000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 18 60 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 60 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 40 indices rho q16 m16 16 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 40 indices rho q16 m16 16 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r17 : List ℤ := raw_ints% [0x3293599e5fd145179be298e92fb9ca0000,0x48099cf9a1f1480d4d248dfbe97dfae000,0x2fcf71acced5178ab6aece4951d018e400,0x13a4bdb7c92b3a3673647f2b23349f6c00,0x5990df2df6e1313882d33a971759301c0,0x12cb36cf952e9ce427c5abaaadc4835e0,0x3020690e0b1565ee2c45e066ca76f060,0x600d38cbafc1aab698887e9f8a51fa0,0x9751891f2ee95adf3f1169b664383c,0xbd51d5e8881d3265f69366ccd1ff6,0xbc30de05dc8400697f13def706b8,0x93d9688d5523a53b58709af89f1,0x5ab8dca2cde84e3352628ab162,0x2a96c0cbbac51b64eb277ac8b,0xec7924dfecc83151dd70ce4,0x393332244d72eb6f127b3f,0x89de99df58f99ee52126,0x9bf413c555b8ca814f]
def m17 : List ℤ := raw_ints% [0x0,0x25cb75fbbd0aa4848e7908294fec1f1e3e645700,-0x2f822992163cb9c3f19c8221ab8549ce12cac5a40,0x1c8566f709b570101659b0326e52558b092dcacb00,-0xae1d8cd06962a6cf3ad3b84689f6b02897bffd4890,0x2f66aab563bed9ad944ef187d3bfe38a6cb04935000,-0x9cc8ab65658511bf56b909956765dc3f07a7e15fac0,0x1992dfc0386db5f2dcf98fcce7ce1503179decacae00,-0x360597ba52039d108e711704246b6c139adb452fc264,0x5e02e0801c3336021a55496873256dcda0f05adaba40,-0x8879adaf7c40844c503dcfea5e14356e14f3a425dba0,0xa6bc80d6101787bc9147a74dfb28e2630173cbc244c0,-0xac7badd6ab7d35685f43f187f8ccd301cd851059f1c0,0x97aa18de2b30b807f69a093cd55aa2c108c2f5050740,-0x7195524e12d4fc95eb393944100358c0cec529b53c60,0x4879b562ca101bb089b2c470ad5b3cc2bfbe89ce19c0,-0x275a91fe8073560115ab853bd1e4fc19ec90447499d9,0x122265ed1778d99930ff0c602138fa9f425ab2966fd0,-0x70f7ea2ac42c7f0a373cff998754a5649d5e36a8a58,0x24ef7cb6e8a14f61d1eb353a1fafdaa4520ee7d5f70,-0xa0f1077583c31735e443fddf72db3321dbe7d1083c,0x24208b70b2aa37e12dc7715e677bf07302f6aca1d0,-0x698837eeb361638d5261b9d0655cf5012b7cde368,0xf685fd2bf745e6b4507cdc1a0d5cbbcc633daef0,-0x1c2bc79d075706a0d2d531b9a45dc5830ccd7f2a,0x27383013318074e36db3611aaf99cc99e7a56b0,-0x281daaed98183284515b48d9f5a5c5eac13688,0x1cc1939d5b052735326258c9d8921cd67f910,-0xd8d071da4a9e7d393204eba4b04288c978c,0x3d6be464fb74d5d03851983b45861a6f30,-0x92e0447b258b63ac152d1f851dd3dc38,0x971f56a9ff6ad1078072c7da1e6110,-0x2ed50b3bf0264f0d1e92d2c0dd01,0x1f8cc7f978b4f410c9c5a0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 18 62 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 62 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 40 indices rho q17 m17 17 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 40 indices rho q17 m17 17 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r18 : List ℤ := raw_ints% [-0x71d54338ebab7622488bf310447da2d0000,-0xa2018b3bd20407b4f4af5e5e538ff46f000,-0x6b6c988df335e3a484541eaa0b9de104200,-0x2c17c00551bb367799acf4bd8a0e07f5e00,-0xc8d2b43ce73c1b54cd8c6b32ce467636e0,-0x2a1686f2eb6c9ff75151f37f3239d9db70,-0x6ba20ae28f52ca9ec4d95ae1afa74f000,-0xd67ee5537562ac49bfdfb4f275e517c8,-0x1515b144eb2cadbe8c4b6d7e59e9fe16,-0x1a54d466f46adf4eff164507b957f7f,-0x1a1ee83d700c39d205b14e6b577691,-0x14796a999c7b01b4fb441f37a6ffc,-0xc87e99726b7516a827ec033f6c7,-0x5dd8e977111d79fbfef989bd00,-0x2075e28a446fe344e51bf0047,-0x7d2840817b4a6ef7a37e968,-0x12c5e6f5565d880787b6eb,-0x15213e48d76bc790b465]
def m18 : List ℤ := raw_ints% [0x0,-0x36547999dfbf4c7e8ccdfbbb62e36cbb79b03d100,0x43a63dab1b74e70c93fb252ed6820c65762d7c1bc0,-0x2835ee532b62a9c0b5fe7d1b92332acd376da443d00,0xf2ed385d37f2705631d9b50e756136af498209e84f0,-0x416941eed1164d0964bd8dd0a7ba34dfa475fa773000,0xd5dcd433b765a3bea8d92714876c192acf6e38790740,-0x2275d2f8866d7931e019150cb003145676ec205d2a200,0x47dbe9eb5d6c0f3f2f46e2c5f0372ce1e511a2d4c86fc,-0x7b5a412a8bf2c67b9e721daff0a99376df76b5bbf6bc0,0xb07d0b800ff584fc05153c35d52fca431aac032805f60,-0xd45193b3f0dc1c171192702644a18138b3c370afb1d40,0xd80db7264c95a57569271321d3ba8a4b56593f2455140,-0xbaab13e3884b21c6a030a797a5838534056903c0226c0,0x8931a13313c944c6037c604fb611faf5ac096434c78a0,-0x55caa4f106028800907403c14fc3e26fb0ee5629bb040,0x2d953e8ace40e0df0e2f1b494ecebe45e5a4c55fc57bf,-0x148480350500c836839985d9e542447f73db513b90fb0,0x7c9ae33b473fa139eaf23792a2deef6d05d60d2013e8,-0x27a0eba66970234820f79b12dedf4a4309a640765f10,0xa789aa425f71566ea352470269fdc22931645c31664,-0x2461caa535525a134e91f60bb5ef22a249b58ec6db0,0x66771295cf26990e7171540bf9094d282aaaee1858,-0xe5ddf696b1cb3e90ac9a79d3a81c5c6234f240390,0x191c19e2deabb565ccfa156aee912de7ee7560046,-0x213c34ca647f477dd2fb293bfe2eea2cd2bb45d0,0x201c897858e7764dca5b4be12eed9f0fd980c38,-0x1593746c32f1180165e2a414a7eae032ac7470,0x9714abf13e6778a7c665c01408f0bbfeb994,-0x274f6b125d1a0d0ad781ad22c0a470b6950,0x55325daed5d920650f0ccdc70c2ce0308,-0x4e30e33416030e280a48bc20cb03c70,0x153310645d5006eee4626bb0ec457,-0xc3086c493f537406abe3c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 18 64 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 64 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 40 indices rho q18 m18 18 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 40 indices rho q18 m18 18 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r19 : List ℤ := raw_ints% [0xf6c4c72ec30e2a55a3a9aa45166851ef0000,0x15eefbae2b7511d5cb6fac7a7381403ed5000,0xe882a585f77d6f674db17e4158ef28678600,0x5f593bc0baa8c95cec54445b187bfcee9400,0x1b1d65ae53561eb8375c9d433fe8573d61a0,0x5ad2929a33c1c7e577a5b302237cf182a30,0xe7fb438869f7b3756b9241682522038530,0x1cdaec9c936a82d8323c757a6a0f0679b8,0x2d50cd4e12afc051edce296589d60eb0a,0x387fa3c675d93186521004fd940b84f3,0x37f1add10191802e71295f20dc2ce4e,0x2bc2e5bec5216c367c7dceea7c6b2b,0x1ab8e27bff450dc1f979c482fc7ec,0xc79e06b6054cc492554e94c7b6f,0x44d87990404226368202c8c406,0x108943aa7560c7cd31863ccfd,0x2789bc5786cb45a7e094266,0x2c4fd8aed435a6f00340e]
def m19 : List ℤ := raw_ints% [0x0,0x4e196ecd31a2fdf5ea6819dd5e26ec4d7eed57c700,-0x605c47467d44c2a614a2ff5d2e484efc0b3b2267e40,0x38ba7976b76efabcc82118b40b4a88d7467ff39d7b00,-0x15343f3a70464bcde829a9d260b646a98b41dc25ef190,0x5a61e856fa6076e1eaf8d1573eeac3eb847df2f6e5000,-0x12432b622e8ee29b24aabb0e7514a021b06c4e3094a6c0,0x2e86875a5c61e29fa7b9f3c834bd2fa206cbb361d18e00,-0x5fcd8bb7708e5c49f14b3d688b51b8f7b46d35e71350a4,0xa244eae1e0c0bfe17ae9e399729e3f7b42ed27cff4fe40,-0xe4e41554cafbf01b9c6fed05491cb4879270b61eb98da0,0x10f385a987057736d7d9e1610117749d91b2dcf132bb0c0,-0x10f905b3ad873ceca5f4cf3b2e5f52958943d25fcabd3c0,0xe69a7126bcb2b23c593241df451ccf6db746387126fb40,-0xa65deacd39b6c626340a90a392387428537c9cee468a60,0x65fa2c576a2f9811ab1435ee261d448c9f7f986e2f75c0,-0x35071cc21802ae5d3fc83c4c88f48a5689218c6f9400e9,0x1751825c5853179a48cabc8a7baa98fc16e8df094024d0,-0x8a12ad3e95df9801869d2d8d8ed8b95ed12297be843d8,0x2ab753ee2a217943e40421cc176707bb3432f00aefe70,-0xaf37507986b4f11f8a079cdb0db41b7819368fafd9fc,0x24ce77b8c8536cc9da25f2ecd8984730df15fc86b6d0,-0x63ed88380edfca050d724782ec277276f3b3eafa5e8,0xd73bb631d5f70b8571806a4ef33a1f74f37e9c45f0,-0x16779af90689a433f06025be83c3ce77049f388aca,0x1c4277e63886ce870c733079cac1f411ab10109b0,-0x19c6fbf9711bd313e327af353c4defa39c823308,0x10396750c83655b8d9ccfa74d123b25404e2210,-0x696ee1886a246140f1231a2b50569402a204c,0x192dad9cd7e57c340ce32f2c9e8d068b4a30,-0x316d222b263b0347b9cd5cb79c007cabb8,0x28719386f2a0c124954f13688d79aa10,-0x9976aec717d2c965add907723de91,0x4b51c5204f0106ff8e04280000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 18 66 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 66 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 40 indices rho q19 m19 19 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 40 indices rho q19 m19 19 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r20 : List ℤ := raw_ints% [-0x205810fa505f0a16796ea10467ed928caa0000,-0x2df742e2dfa215e7779480d93cd0187509e000,-0x1e6e73fb72c8755f7dde04234640a270c21400,-0xc7817f56fcf9ecdadc14272a2d73ea3241e00,-0x38aedf030e526751ca676786103553959efc0,-0xbdac505344049d70a60e34863aafd6d6d3c0,-0x1e3ef4e2da15d63728d10ac833d95c2a0f90,-0x3c1f1840e50aff0c722bd0740167c6859a0,-0x5e4a8f5557d6cb3e8c1ff1b998a3bdea14,-0x7562d8c9ed48b3e9be87fb29910f0369c,-0x740b05fba536b2e8e43f35fbdd72b10b,-0x5a9b6f4ddb7eae7d1177c71710d605a,-0x37372b5c96505cf051834a8bc765c5,-0x19b873b34ed1fa381579b0c3d41f8,-0x8d91d833dc8b53813f8767ffa55,-0x21e80c08440fa3db8e54843752,-0x50cea0e45b41333beaf7fcf7,-0x5a3ab92b78f6d8ad2bcfe0]
def m20 : List ℤ := raw_ints% [0x0,-0x70448f46f75a4d1180f5a52e3757f3af66752e2e100,0x894cf2920c0c52c43d8c06b77e2e51a45400697557c0,-0x50151af5edd1637b2dfa83043d5ec90a2ad5469520d00,0x1da43a37dc733abcce7c35b6d32eabd06b003a493cb3f0,-0x7d0be3a9b052f53e62e7b7d344d7f0bbf0fd52d8fc3000,0x18fdd4e8064afff4d5c785303f37c6bcd0f1cd57eea7b40,-0x3eef66c594883cfc4b89e188e1c2c5b94529493d5dac200,0x80024c4354d9e9a78dda06ee2bb833a8d23d29f238ccebc,-0xd600daed6069117b0f2e1fe0cc8a3cf8d9fa30667fd87c0,0x129b0eeb94fd734bee65e0168a12fc974b740069fbda5d60,-0x15b8a2fea6aec11c6e177b7eec6b3c32025603709d35d140,0x1567dc2a138ad041a9a937bfffa4ef0e56714aeafd389f40,-0x11dea70b722577bb3a0470f3ecd439bd2e7d81e92aef12c0,0xca865ec5602351465405cdd14fe18679490e5c60275faa0,-0x79b62e0620804e6304fd154e4ad41283e95da483a12f440,0x3df397e3e4f32e368d70c93e5860173f690589f30cf522f,-0x1a9e4b16ef35574ca7df41120baed6a3d372e3b74f4d2b0,0x99af9c93486306829540017d82a515151884af5d36fe68,-0x2e40fe0ca5d8e4890208f13447ef8b343e46ffb70d2810,0xb8140d79c616c4ec9d3e226618b9041a6e0e05fd50ea4,-0x2566e62dca4b765bd0dc6d04ecd5997b4d6cf7046d0b0,0x61df2ef3f076f83a8a96623f1d8047fbedbd064051d8,-0xca5854dddcbb08a2dc950900c9534ed1273f3c91490,0x142d4631bbb9a792b21701e777c3f4a51374735dba6,-0x181b4a372e6906a2e12c036c72e94951bafaaadad0,0x14bf76e3e4c899acd855d5020b1d08ce55ac87bb8,-0xc398ae9f79639b2689b4cbe9dfd8baf5998a370,0x49ad3be42afc69f594ac6bfd1094f18b2922d4,-0x1023422a561920a385278d00b62f9b68e9650,0x1cad3a048f46a906556d286d6df7e2d6788,-0x14e98cdbc8255e9c25328a6fc3dcc4b70,0x456600fd0eea5f6713c11db33ea047,-0x1d1338cff002a0dad97f5700000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 18 68 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 68 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 40 indices rho q20 m20 20 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 40 indices rho q20 m20 20 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x5a3ab92b78f6d8ad2bcfe0,0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r21 : List ℤ := raw_ints% [0x41dc2699414bc602305f63388fa16a8b7a00000,0x5d89de97a845ecc641a3db8b7e890ca67d40000,0x3de2518abeaa4d135250131926ef182e28e6000,0x19566411e4d461f8d7d898f9f9aaec339ba2c00,0x7315dd33f74d78cadecc405a62311c3aaefe00,0x180bf716003cf62530d9197adb64ef9a6a9640,0x3d4aacdf151a6b3dacb5ac58679ab5c5aa840,0x79b2cebc18637c7b1369f9b60bf623da0570,0xbea22942a39d62a6e391c06e18ce27c1920,0xed01ef3ff9a79a016cd2951ae64cf42b4c,0xe9f2f31e8adc65859e25b4cbd727af044,0xb65e9754fd50e8e16f4f59f7fa1ded75,0x6eeecafc60db1c5d1f5df9f619a66a6,0x3391f4668cc7bf3286007952e91a7b,0x11b354f2853d7b3cb6884723c6c48,0x43a84fc186f377f62cae9ef072b,0xa0c8b686f6fec965e015211ee,0xb2f3de4f71277aca2b2f269]
def m21 : List ℤ := raw_ints% [0x0,0xa1628df60391cec929611d726f8e6e4c234872623700,-0xc3b205596e48c00ba84fa625e567597ffe0e4698ae240,0x711f09a8163b07d12b7899bc27ce85176583d91dfb2b00,-0x29799df30cbcebfe738b1f339f86ebfafcdbcd4254d2a90,0xad388ccffb72a03d5646a9c99fd6385f1e20bcbba095000,-0x2240e6ebee1f78fa000b6331f478affcdd60e188186212c0,0x554aacd141c3a2dd6ab4c7ef0329211ae76f0040fcb46e00,-0xab69ed7a7a7f928023d7fc428b74712a0d01a83f51fd42e4,0x11aee019bf7c2fcca85a4e4ca6766c25a31a888d616ff8240,-0x1843e24087763e15781b73408c5cf99ca933e2f230ef35fa0,0x1beb1775c0f10ab434fce6477f0103165d31e9b7b4b8fdcc0,-0x1b160699594c20189c3d69f562c3bfe9dbbd62df52b1a55c0,0x163c2d19491d0ab803339641e5980c868654aa169cbc02f40,-0xf77a836d6321920043da4459a0c648d417bc7a445148b860,0x91d8d7a4873b104b701b17c9d569851ac1aa5753d21e91c0,-0x48adfe8023dc4af3a90d448beca66679d2e7b8c05c54c8f9,0x1e84392700e501cbc36c75d2498db178988775d7b5b829d0,-0xabd1b558021d1590c3f3cfb92699c2a9d631fd41fad9558,0x324ebd89a1cce598469d8e6341f16efca000b2323198d70,-0xc23ed714baf070a827e412efbe5e0cfecb3e10ee2c87bc,0x262bfc5741a2e63573b8a4536e751556cd181e62331bd0,-0x6041c6d824d9b46b9618cacb83d4621166492db889068,0xbef839e4ed4c78d8f2f82c21442e0a0508dcce2b4cf0,-0x122f19e1ac5e98d01df31d9a25f97445ff87b664f06a,0x14a0843063f4a72728bb3fa78e6c9a205c95015ecb0,-0x10bde55b647f924f0b0e0463a8501f1f42d7f5f788,0x93a83b1bb242b5eecf92d8cd302161cd99a7db10,-0x338c40bfcd34e03e0000b22e81821a5b3b1750c,0xa5960a05aeec2f761ad0d8f981dd862a4d530,-0x10a36aa9e0436c66ef3464bcb98b6abd7338,0xacf393c06c916b2a78772295065e68310,-0x1f5e1fb0e387708911f6bb88f936921,0xb38127629856ca0bed603a00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 18 70 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 70 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 40 indices rho q21 m21 21 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 40 indices rho q21 m21 21 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0xb2f3de4f71277aca2b2f269,-0x5a3ab92b78f6d8ad2bcfe0,0x2c4fd8aed435a6f00340e,-0x15213e48d76bc790b465,0x9bf413c555b8ca814f,-0x454a1ce36f58ee06e,0x1d7e742a7fcc856c,-0xbf343bcb6979bb,0x492687611bda5,-0x1a27dc11c40c,0x89ff5ccb3a,-0x293820021,0xae0106b,-0x270fba,0x7058,-0xe7,0x1]
def r22 : List ℤ := raw_ints% [-0x829edc87663f8b94bc1b62f7939f24cc62fb0000,-0xb968a14a3e978fb1af92d772947f31c0e36a9000,-0x7a96338e1cc61c77a49bf47c631ec95803776e00,-0x32280a7c6f078b16fce590c4c1b04e7bf2b0ee00,-0xe3a471bc61eb8bd461033660c0d42e6afc73020,-0x2f86864712a2f54ca4abcf7aee1d01660d45250,-0x7906590c16c84763c5612f609cfb8f20e39ae0,-0xf00f8c2021d8e9ae3ead60cb57d5d242f7ed8,-0x177a0268b3997b5f82e24c60640f9cb199f0a,-0x1d26f15bccf6a6b9f2ab3feaaa46db573f3d,-0x1cbcc4b4b644764d8a8a637e6547de235a5,-0x165e511d5a74047e823b9efc1d6c3b7da8,-0xd9589f10b7eb5401667ea7797d571193,-0x64db20812fb4561da32071708c88b88,-0x228c0fb184c06e576f9777903a40c3,-0x83c0e901bc2fe37207c7232be0cc,-0x1385094d005619950bf6eb42b7b,-0x15a9eb20075e76ca3df1f131f]
def m22 : List ℤ := raw_ints% [0x0,-0xe7fdac11a52199412b7b9a54805cbe8d72b8246d2f100,0x117029796da5c4088e7b93e03e5cb1e592c7f561b7a53c0,-0x9fe32a608b60799ca46571c5302663c35bbdb86b55cdd00,0x3a15f332901f4c46115618b820be177097f49f926bbbd2f0,-0xf03f33e02b628bf96aea45846f0ae34a5e649ed862e13000,0x2f050306df6562734432eba891d97219e452e5a8f16cf2f40,-0x73cd19606cbc19eea1e7b56a75d6e30e7e763775ee934e200,0xe6064284c51dfd9daf715c966c3f6b3a47ad5c6a3c144127c,-0x176f65087778c3d93f6208aefa07d9eb2165b99b44f02963c0,0x1fbb5f2d0f05411b7e85fe2808e146b99c5d2d555e54153b60,-0x23fd9db1b3472582ed36cd681d3ab6e45d157f80f91c77c540,0x22629f39a33245f50eb2d23395f62ef08b2553584c53fb4d40,-0x1bc37f046460634a85b00371e3108147d91b4ca392a6f2bec0,0x12f89c532003298eac9910373a25707db7b9a61ba338039ca0,-0xaf74992a564b00282b0d6ba610f1a286c6ae9fbfe48867840,0x559d810205b92ea43de1585e1e36ee1d730af97f38482039f,-0x23223580e3a6e8f1d4aff8ed767a3371d4a1a8e317b8fc5b0,0xc0ebef3c220c5e9ba3bce03772b9e3c1a46397f10e2890e8,-0x36f465bc36dced8b7c45225f4703077ab210d203e9218110,0xcddc240b3cc0911f86fe80b4792d79f8694a4d0f301cae4,-0x271f31a1ae05e3874f35cd9f8007ea0f81311e36fbe63b0,0x5f0ce83dcea3c95504b6606fde3b6257bc7c4144bf2358,-0xb4e91c3584548cb26b5dc6070b51153cc3ab60c683590,0x1071827248c3155c3524f8ff0d5ec37a58e9e9b96cd06,-0x11b37bf7955da95fb1d3cb86e47c59c0247638ccbfd0,0xd8a8109c177c035e0d246caeba71a27738be90e338,-0x6fa93b3eea41c52d783bea88c1303be42ab06c270,0x241ad42248d75749261cc2dfe7e940e29323e014,-0x6a3dce6f33e5d8d1c26ce6f42984d744119350,0x9a746659bda13c8566567c7108bc2df41408,-0x595db099fc56f8a368f1a6c07e88dc4a70,0xe2bd4dbf387fa92bf9a3d5928b0cb37,-0x453c8b2699f8c36fcec437c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 18 72 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 72 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 40 indices rho q22 m22 22 102999356846850207744000 23=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 40 indices rho q22 m22 22 102999356846850207744000 23 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_22
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<23) : intPolyRF (mz e)=rfPoly (C (102999356846850207744000:ℚ))*rfX^23*(1-rfX)^16*momentRF (key size) (X^e) := by
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
#print axioms moment_source_22
end
end CatalanCore.Li2.NVMod.FamilySource.V6C24
