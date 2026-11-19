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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C28
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,28,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0xc8282c5954c2678a80000,0x120847e668552e94f28000,0xc4370cc642445b60ee000,0x53bfd478c7bc651711600,0x192c70185a1edec5cab00,0x5aadca885da6d4adb820,0xfe0164abfb4ded2d8b0,0x236f9b28d14be8af9e0,0x401172fc5ce6550508,0x5ed7d76b1bf9e276a,0x73b93e3f81c36ca3,0x74c2bb45228e46d,0x616e44768d4509,0x430abbad16809,0x25ccd7d7500e,0x11481084472,0x64df2c55a,0x1caa141c,0x61cecf,0xeb91,0x165,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x5,0x37,-0x21,0x8f,-0x8f,0x6ced,-0x489e,0x5a2d01,-0x17d92,0x10d0971,-0x1fd6b4,0x17e107,-0x460b8c,0x242f7713,-0x602919,0xfa6b067,-0x904903,0xa6377]
def rhoDenominators : List ℤ := raw_ints% [0x164cc8d400,0x475c1c4,0x5ef60,0x71f4,0x2700,0x145,0x78,0xf,0x200,0x51,0x1fa4,0x37,0x14a0,0x1ad,0x11e,0x3cf,0x30c00,0x1144,0x8bda0,0x198cc,0x14300]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 28
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤27))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤27 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 28 omega7=padCoefficients 28 (omegaCoefficients 27 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 27 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 28 omega8=padCoefficients 28 (omegaCoefficients 27 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 27 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 28 omega9=padCoefficients 28 (omegaCoefficients 27 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 27 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 28 omega10=padCoefficients 28 (omegaCoefficients 27 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 27 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 28 omega11=padCoefficients 28 (omegaCoefficients 27 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 27 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 28 omega12=padCoefficients 28 (omegaCoefficients 27 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 27 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 28 omega13=padCoefficients 28 (omegaCoefficients 27 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 27 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 28 omega14=padCoefficients 28 (omegaCoefficients 27 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 27 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 28 omega15=padCoefficients 28 (omegaCoefficients 27 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 27 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 28 omega16=padCoefficients 28 (omegaCoefficients 27 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 27 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 28 omega17=padCoefficients 28 (omegaCoefficients 27 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 27 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 28 omega18=padCoefficients 28 (omegaCoefficients 27 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 27 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 28 omega19=padCoefficients 28 (omegaCoefficients 27 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 27 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 28 omega20=padCoefficients 28 (omegaCoefficients 27 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 27 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 28 omega21=padCoefficients 28 (omegaCoefficients 27 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 27 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 28 omega22=padCoefficients 28 (omegaCoefficients 27 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 27 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 28 omega23=padCoefficients 28 (omegaCoefficients 27 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 27 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 28 omega24=padCoefficients 28 (omegaCoefficients 27 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 27 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 28 omega25=padCoefficients 28 (omegaCoefficients 27 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 27 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 28 omega26=padCoefficients 28 (omegaCoefficients 27 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 27 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 28 omega27=padCoefficients 28 (omegaCoefficients 27 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 27 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
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
  | 27=>omega27
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 27 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 28 at hb
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
def m0 : List ℤ := raw_ints% [0x0,0x8a165b9cdc47467b8d6f8400,-0x10087fce75cee38dec7b8feb00,0xe6c12a49a1c1f8aa572add7d00,-0x85df547cf843686f1ad2d0ab4c0,0x384b129a7f342aa3cf30199d5740,-0x1247ccbebc36d8e28ee4185d83000,0x4c50c5ebfbe1e9121e2429e279100,-0x106f6320406b671843cef347b7ebe0,0x2fa6855cc483ef5fc75f2270f263a0,-0x75eaf8236dae167b7e7f4e97694620,0xfbc77eed2ee6446572b2617397eb60,-0x1d3c07ed0e055ce4b59766984acfbec,0x2f8fae4a0062df1d9868d6a2a30f484,-0x4419224bc37ab14da693e5d7e54ac24,0x56229867d12bd060b787faa16da2acc,-0x608342a81dc5be14a4bd44351edce3c,0x5ff9c20b182b081820b02d5f25dbc74,-0x54cbcb42ac94d21552085e6cdd0b874,0x42959e8ef5d91e9e4f7cfc8014a8e3c,-0x2e7328d8cc728e81bf099743acbb90b,0x1cc191596435b0f66d7b0f8661857d1,-0xfc4e906f2ae84302ba666f9c28f5b9,0x7a3c0e089eeb6f3d67c4d038c8a0c3,-0x3422410fc196aa6509ffae95f463e4,0x137cb7445cf913e471c3b4b427012c,-0x6590ab4006692f14d796bfe8794dc,0x1ca113404d8fbc49924ba57ba9ef4,-0x6ec2f716241f657bb631bf44cd16,0x16b9ddce429b69712b337c69f062,-0x3e7335a6fbb33da82677937bdc2,0x8d2e575d8fe7ff27533f95c536,-0x100c30f7250a0aca40b6f23268,0x16cae2335b32ba8f45d1e4e78,-0x1846875d9c2c999521979f48,0x124b765f95b5f4a7715f8d8,-0x8eeb304b96416c9d0adcb,0x270e2401feae34014351,-0x4851305e53c9901da9,0x1c7957bf47e484d3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 21 38 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 38 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 47 indices rho q0 m0 0 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 47 indices rho q0 m0 0 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xe905ba98b3b846f07eac2ec00,0x1aafa1e2db42554d3912888c900,-0x17ab52e30023541f1972ce66af00,0xd891c1ca8f1d6c016a84cc728040,-0x59bc96b8a647760043f8689103fc0,0x1cb475de7433714d3ce1e5d4a5f500,-0x75ffa6cc8f8bfea566d501dd7dbe00,0x190346d0280059331f54c3d559634e0,-0x4759ffd526a310316589e404a318ea0,0xada628fcd1d6d9c324c185f88420f20,-0x16c79a6d75c7bc05cd1c35c2725c4e60,0x299479f7ac424b3f9b18009419047934,-0x426db02786103f6d95b84beb78e310dc,0x5d590ff12996796e273aa806143f673c,-0x73d00a580e26b5663a5201b684a74454,0x7f3320f47b45db9d386323e253e74cd4,-0x7be778501008d78270f4ef124d780ebc,0x6b26bf7bc0e93db63032442d9762d17c,-0x5249c9a810d0e40f05fe9dbd12a79514,0x3817c1a740760b80c7fe6d223a7be6bd,-0x21e6387ba9f01d15588d9facf24ff507,0x1220b995859be50429d43ccaddd0bc9f,-0x88ddf8c65a0c7e47fd3e2dfa6d9fb85,0x38c8d14b557282dc7b1cc6192bf495c,-0x149e155d24692cd7a30fba563cf8a94,0x683585e8a658cfe6239069281a60e4,-0x1c6f457c782471f94b8f3d7c4f144c,0x6a445d05f8e58968e43ef01bb8fba,-0x1502fb0c12005bbdc4a1ecac7df0e,0x377c54b6f87dd866d2b38cfee42e,-0x7824ffa714b41d3606d7de3771a,0xd075d73108cc2e53cd9a6f53c8,-0x1191cd1c4892d1c82fba87da18,0x11a92644e4029fc2c5e193d88,-0xc7730d47767cde631f4c618,0x5a49bd02388f55cdfb843d,-0x168fd1472ba57d272da47,0x2576abd3c3d6447a7ef,-0xcdec7a4991e13135]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 21 39 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 39 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 47 indices rho q1 m1 1 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 47 indices rho q1 m1 1 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x18939aae1af46f7b5d5c28ee400,-0x2c6e79c74f3e66909e928fab3300,0x26dee8693b223fe1f1d7645853500,-0x15eb1d17ab43857fffc45bc4fa36c0,0x8f3c405f1f1aadc102b016d8ac5d40,-0x2d25b552e7a305851e0d5e05934d200,0xb6cdd9e43ee8754edccde30a6266700,-0x26274a50981684fc7c5ab06f8f13ed60,0x6b1de53610a227ad88aaa78764985420,-0x100755f6d826a75d6a853ce36f1ec7aa0,0x2114c1aaf6cdb45248b2dd2a10a2020e0,-0x3b5865f5cabff5a56dc08db413ab72aac,0x5d2199f157634bf2f1ff93ef2702c48c4,-0x807b0c63f54fb8ca1264ea2192be5e264,0x9c6482a06e9a0286540432b66ccf9378c,-0xa86b0507d23e53c5f565ef3855ff3eddc,0xa0bd6a84aadc86da1a9e6254f04f12e54,-0x88180e1e25462f64cfe92c3a6c0f91d54,0x663d87cc6e7e883d89f81cee7d93598dc,-0x441d74d096ad227ac602a431bd729f0bb,0x28316480aa3dbaed75b35b7b03c48dce1,-0x14f69406f79e4cdaa5abb2bf569f02d49,0x9a2f8e208dd902610110a922f3eba5f3,-0x3e3c16c41576a3ce9f87a754772271e4,0x15f379469015c935378448d1f3ba152c,-0x6b9a14ce9735a78f7c78eaf3a5e7bdc,0x1c6bcf4bdca7a48f7b28e0de52c21f4,-0x66992c91b448fffa69ba2dc00ffef6,0x138c01719952b7409e9e286a313a02,-0x3197f8b20a1c3dec77fccf27ac362,0x66d37d52435d952a21f18d7c2f16,-0xaa2490db9561611b11e4a55c0c8,0xd9ba22a28770fec344952e1898,-0xce68d49a53e0f3a6245d63768,0x88549e36717b67542d491b38,-0x392867005937ef27c8745fb,0xd0b82c5d313c36e2e09e1,-0x136751e8a70dda2e37b9,0x5d0756c1700130583]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 21 40 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 40 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 47 indices rho q2 m2 2 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 47 indices rho q2 m2 2 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x29791505cd7c7c202d8b85120c00,0x4a005578213ecdd54ac4a975a6100,-0x3fe07216a1fe7c006a1dbd8399d700,0x2386fd878074dfc0af4a28c6a647640,-0xe4ec6a358e7ea66b86f50e8ee8511c0,0x471f4373bb08ffd616b4088f4f6b2b00,-0x11bbed85a8b62855f857daed2fe3b6000,0x3a53e6851492864548275399a9c2b4160,-0xa137de54d700927d29704e8732b572420,0x17bd5fa7fdd5a54a08fe800a519d55d8a0,-0x303128041094daa6fd2693f6e4b673bee0,0x54fe02a83bfe9a06b9f4ed77643bc92474,-0x830df082743d04ca130d919eeb69f0ae9c,0xb18b639eeba4d8f2a5f2409d93b467dafc,-0xd4184bec1a909984f2ddc5d1076c782994,0xe0015a6869c681f2603ae46879380662b4,-0xd18695f9bc639df178b6e9ccc65415c85c,0xadb94988f23008c1296a3e1feb3826be1c,-0x7fb2a14abda9afd621d108f5b3a6fc4df4,0x532a7d8fa40ac6185e599d29c9814eff8d,-0x2feca9aaaa5bcb0fe3386ff0c9292dbe77,0x1862176b321ebd94b903843bea2c7db98f,-0xaebb60f55e83d6d281c26f4f1ba8824d5,0x449f6bdd13936a3436db0f658622e485c,-0x1783ca8895564e8892dcbd4468180a794,0x6fcb38e2492f10d895607f5d65d5eee4,-0x1c9560f93c7429da6f9b5f0fc2ca524c,0x63a9d9efc6312aa78aab3a37d1d10da,-0x124b1c973e84f00ea1a0547040a4c6e,0x2c958f18bc5be3d0dc21709acec98e,-0x587ce2924d3a2560482f25299843a,0x8b9319e851c66d6291e2b79bace8,-0xa9662784dc6ebd62898d3d46578,0x975a7432d1eafb638ae8af78e8,-0x5d7628448ae1824961ead1138,0x2440b7c2aa8367c18e7f5e8d,-0x78c46932142d09982d8c37,0xa0c1320768de9ae3745f,-0x2a016c36ed906e2905]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 21 41 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 41 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 47 indices rho q3 m3 3 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 47 indices rho q3 m3 3 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x45fc5379cac211764cdb708e74400,-0x7b4a292d62d2ec91f4d58b5e403b00,0x690962b97db7cbbebf964c76695ed00,-0x39a41862ef81c68c6e121190a6b0a8c0,0x16e56d7bedae8844447e32c19cef3a340,-0x70380fa5c9fee6745df1e27ab2d905400,0x1b942b6148c45449036d07eb6961fced00,-0x595db132721e9082f6e0d90ac55fc53ae0,0xf340c5d2f60285e1083c87d7cdc338c4a0,-0x23425662307a717bb298145e69272b3c720,0x466c485b72dc06f4d7ceccf201f39911260,-0x7a2296b72bde4d355998db5e0607576956c,0xb918b7738b5894106e5bc3882899607e504,-0xf64fd76d915697f56b64bfa59559a0a28a4,0x120d8d00434c62bae827f21b71779ae7d04c,-0x12b44e91f1d20cdc498ec7bfab7cad3dbc7c,0x112677dd4f72cf302e3cef0ab811660d1834,-0xdeda8ad24bc119dff656bd601cc88882834,0xa0510c47773f442016de86de57de637be7c,-0x6616331fd83e107b22cd36872c539a08b6b,0x3975b7844c284d16357ddf9c56ee8d253f1,-0x1c85d37016b1c2327da5e86417cbfbcd0d9,0xc72be6605817ca0c89401905c6342db223,-0x4c1dad38cfe7fc06c2aaf6d691c41ff9e4,0x195763a006421b63d8c5997e3c16ea712c,-0x74d9d12556ccd8ec8b0ec9efc053eeedc,0x1ceb86ef21e5652f434c93687bc3386f4,-0x616391eddc5001be1863f25e2a79bad6,0x113848e478ebf80d320f4e075b9fb7a2,-0x284e2373a2b429628bf4adeee12d902,0x4c8d3f56b0f7ab8bbf45905804faf6,-0x730e50805083ae5e356df4716da28,0x845e00c650a949f8e2b8713552b8,-0x6f6222675795969a8f13c5d5588,0x403f880641c5a828faac264498,-0x17086cf71350822abbacac52b,0x45eb6bab619dd31864b7271,-0x5336ec3e2a82740e355c9,0x12f524b48da42d62133]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 21 42 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 42 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 47 indices rho q4 m4 4 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 47 indices rho q4 m4 4 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x7619ccdd86277d77a1b24df0642c00,0xcd78be06ec30773497fc14f79763900,-0xacd3effcf17460e1d6d8fb42308c3f00,0x5d9b90e96a5edb13ae9243a17f2347c40,-0x24afa880457f9e6f2106073fa1e685f3c0,0xb15722e044eacfba4a79425d42366cf100,-0x2af8049a951ab8e6748afdd5e7358757200,0x8937e96a41b9fa7cd0496f6c2b3cb14b1e0,-0x16ff015461d5030b7c48f597059ee812bda0,0x3483511b51023e817c6d5a8d61563aa9f620,-0x67392a8415b68c0c48b39ead714e1537db60,0xb018707ad69dcca473fc06a2699580399bb4,-0x1065e264e162dbc213bd656f1bf935f6cc85c,0x1570a4f500f4bb50684679268b4d6fef52abc,-0x18b007233dfb4eed833633e1ac5785cb062d4,0x191935d19a97cc7688c937ed1605482a32d94,-0x16908e305530d5e9feb24f0aa5b8fc15ceefc,0x11f43c74f7d0e36a7f4f089526544ad158bbc,-0xca495014d41cac8b9cc0a9519ff90b22b5d4,0x7df87f310fd9e01a8666ad4783971f6dd75d,-0x45443c305d46091f2df1a2ce458d37a6d2e7,0x218d28a0433d4563189e0903dfb486d1097f,-0xe45353ce3864eb8ccb9cd681402e0566725,0x54eae0a0091aed22d755d6074e987442d5c,-0x1b78551e1193dda8997d92191b89af66a94,0x7adb1d968070a008196d90b85f253f4ae4,-0x1d6e9c6a95b57ff24650ba8dda2fe1324c,0x5fb76f70aca5f9f6b418d87d48e57abfa,-0x104cf6f1d01b7d5b243eee983adeeebce,0x24a24bee55c30de249f31cce3d7ac0ee,-0x42901097c95c1897be1e290beeff75a,0x5f494f949990c5b3c9b69ee0c99708,-0x67daeab058e84872d819b8c6fc9d8,0x523f50269eb8c3e9e19a16ca4148,-0x2c472f92d1f28b82f72e6436f58,0xea8002e3cb4dde22c1409f3dd,-0x28803907f4c43ba26a2e4527,0x2b0ff48aaea70837439fcf,-0x88d3c5d424ea5cb8dd5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 21 43 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 43 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 47 indices rho q5 m5 5 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 47 indices rho q5 m5 5 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m6 : List ℤ := raw_ints% [0x0,0xc74b89b5d262a3b9e0dce385a90a400,-0x1568a988c79622625fa117147b1580300,0x11c8cae131c004f9be712e6d656210e500,-0x9828a2accf19a3642aedb75385f2584ac0,0x3adac0e55d1abbf71142889b3be99453940,-0x118af61252df8109a349c5f472146821e600,0x431216ea7b9b13e486e87265e0179027a300,-0xd3254ca839381a84171fec46cca65a75f460,0x22de375d0eb21e235996373c26472b7f5a920,-0x4e6c456cf095d12e2b9284172acb8d9c907a0,0x97c180a0b82aae2842aa6832de59cabbb9fe0,-0xfebae327db969aefc96fea17865386ef51c2c,0x175381b2d5d58467c07a414583cf4da2ae0544,-0x1df94173f7e6b00d278e0fe70a6695b2c752e4,0x21e5e70c79ce361eb920c01c2438f94594750c,-0x21d2e549c80011ed0135ba1b14420d5116221c,0x1dd2ca83d029797ec0c42163ffedec0f4c0314,-0x1740e9fa555d32b18cd67c4069971923495414,0x10083120e7f39d92f14cd62f4174a49ab7d71c,-0x9c3e77dee7937ebc458069f67a8228efcc11b,0x53f19bcea6ac1f6c16d3c93eb8abf7a04f801,-0x27aeb316ce2e844d67945894096ef343b1969,0x107359485153da4986da9aaf956bd64260553,-0x5f46436d6780864eedf3537a587e0725bbe4,0x1df2b891a364035bce324f37982891c8a32c,-0x81e9438c980117d314550d636dbf18af7dc,0x1e1fc4e38eba8c86ea3ea11879fefe76df4,-0x5e99dd8a0d0faa4766c1291f72d88b60b6,0xf83c31efa9b7df06cada422620d6bbb42,-0x21789126511a0585c89479e555d6984a2,0x3a290f52020c161b8c50be9cba46b8d6,-0x4f43f2e25933a12319429c9a6697688,0x51cd4cb17ae01f1491353157f701d8,-0x3ced361b85646f6a43d36d54888a8,0x1e9632cb4763b3dda93db9305cf8,-0x956bfbe6c1725e74ee142ab35b,0x1778294107df7eef02dda9401,-0x1646cf8b780aa11a704c4d9,0x3db19a69336bbc5687e3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 21 44 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 44 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 47 indices rho q6 m6 6 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 47 indices rho q6 m6 6 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0xc8282c5954c2678a80000,-0x120847e668552e94f28000,-0xc4370cc642445b60ee000,-0x53bfd478c7bc651711600,-0x192c70185a1edec5cab00,-0x5aadca885da6d4adb820,-0xfe0164abfb4ded2d8b0,-0x236f9b28d14be8af9e0,-0x401172fc5ce6550508,-0x5ed7d76b1bf963e6a,-0x73b93e3f819caa23,-0x74c2bb451d5ba5d,-0x616e447625b1e9,-0x430abba7dc031,-0x25ccd7a900e6,-0x11480f632d9,-0x64dedc040,-0x1ca91735,-0x61ac5b,-0xe87a,-0x13b]
def m7 : List ℤ := raw_ints% [0x0,-0x1504f7862d3067449ab74bff18d414c00,0x23b3a003a5668377b939485be8a5085100,-0x1d4c7ca45e135ea16c17732bda834cc6700,0xf78f9b4ba7fb9ae88eb2ba17bdf94239240,-0x5e88b71f1596c3e4d447c6575592800585c0,0x1bcee2f4d7c04b3d2824e90eb9fd30fd82700,-0x68e1d098752761ab301310d1ba48e92b25400,0x145968eaf73545eef8058afcd49b3c77cd0660,-0x34feefcda13fe4ea7d3f3063da32ffd864a320,0x756e6bc6447f77254e603ce67f1927fcc97fa0,-0xdfc49bde87726dcfbdab886cf08bf5c9241be0,0x171ab9d0ec2e48ac05f986567bc10ec7b1d26f4,-0x214c3808a1113e133a3c4645b633ef0b6fbbe1c,0x2a0fb1a3d2a3392642a72971cdc4f7207e5f67c,-0x2ebb2ba41f9f71d0026521d7f9086af456eb014,0x2dc69d31d7078ff34b1a071abb32ceed23ee574,-0x2797e2c33665f1a3e427e3deddb5bb81ed8649c,0x1e422334851b96ebb00d1cc9db0dace489b705c,-0x146dc49d86fd18eca443abf29ddd78053867ab4,0xc2c5e7392b7d7fdfbfb0fece166b526359102d,-0x664314c3103257df0dcf31e9cd01c32e28d257,0x2f2f69bc7ac018abcaf73af534b67232df2c6f,-0x13114ecb1254a37e8fc23667a8a0c0b51d2a75,0x6b7cdac5633c474eb8d1bf96a5206f2a0905c,-0x20d516a2aebb75bd715330ea0071d5f345794,0x8a23f7684463f22c423bd94e97954824a0e4,-0x1f00eb7bcc55d63a9ec151f6f4557923d04c,0x5e021cbf0660c33e4018f465e99712bc51a,-0xed83caa8f81f6a5724ef78b414b6f7752e,0x1ebc32d214197c04d07d8fbc1823c1f24e,-0x330ec020b0236058078c49e4c48fac87a,0x42380b6da20c3dcb5e4b55b0bef23228,-0x40ab671002b44ae06c6b1a03f456938,0x2d448fe6949b21cb8895ac214bcca8,-0x152cabaf8d4736dd1a046efeece78,0x5f53c33e38109cbdd05e9fb862d,-0xd9aaa041cf915069bd9fa9d17,0xb85141407dcb6efea57523f,-0x1bcdf43f2c11ccc1d2fa5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 21 46 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 46 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 47 indices rho q7 m7 7 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 47 indices rho q7 m7 7 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x13b,0x1]
def r8 : List ℤ := raw_ints% [0xf6496e91eb4b35676b80000,0x1623adf5bccb842acdbb8000,0xf04f38398d04c986f5b2000,0x6648d363d7828c080173200,0x1ea5ee197e1c3fb84955300,0x6e011134459a59c564e460,0x132e0da37185e758c2e870,0x2a9c52868d8d1962e9df0,0x4c9e7ec9f93aac1236f8,0x70b27ee1059e1457a66,0x8877722172ebe06e27,0x8870088a196b467fc,0x709682898dfe37b6,0x4c6750a6985512a,0x2a5261db71c109,0x12e6ded833760,0x6ad68c2a2e5,0x1cf758fe34,0x5bb06180,0xc02f10,0xcecd]
def m8 : List ℤ := raw_ints% [0x0,0x237861b26c41ae43c515503e79e5e30400,-0x3b8e01270095e132d3520266491db608b00,0x304c2a8a8423de37325ef5f28b1cc9091d00,-0x19325378b5c378484c02f787471d28bdc9cc0,0x9806e0251d5a597c3eb940ee5f7fd7dd5df40,-0x2c25823efe3cb9ab3a965b1d80082e93f0c800,0xa44dd4a36f4ada0d5808e67d74df677732c900,-0x1f71aa6b030c1c20f3da3447715833791f8f9e0,0x50bd21488cb3bea5e47771cb9c9febe265bf1a0,-0xb04ed13f4674b92ff9cea9278fde8b358a14c20,0x14aea18e21ebc5d5d552a13a55bcd41aefc21960,-0x21a2edd53867c64a0ce1df45ad4bd5246be30eec,0x2fb215e536a7154c8ed5c5155179f6666b6fe984,-0x3b3de6655dfdeae11dc188e7fbd50cf4bda0a124,0x40ad2381439c2fa31fc6028810aa9ab5e9a2e5cc,-0x3e35adc00c065b4f41c108b5f7e87598531b86bc,0x34cb6b8168ec9ec387497b481141d62b31b28af4,-0x278de5e65008afa50f7ec13f7bb839f8285104f4,0x1a27f542780c835dfabd7ca5c6876e33b07816bc,-0xf4023099d63f6f9fe11fdd24f0cb8548aa325cb,0x7d371dca9d3ebba167d50820e7d3878c5438911,-0x3866a989db90128fda49b01757b481d305766f9,0x163820c4bff27edad65fcbf3895c9cd89715f83,-0x79eca7047aadb02979f4f08e16d0a7dc3017e4,0x2430e4a73d64e07c32408a68059fdba5d1632c,-0x93b150f5e1571dbd415227cdaa635d13ddedc,0x2014c80db0b3ba5207c339d3df3dca223fef4,-0x5de9e45ca2bae5682d8953b6de639a527896,0xe46b8c19ac636702da184b71a9538cb54e2,-0x1c5c32c7f392f76f0c86df826b6c53c7642,0x2d06500b98896923146ab25e814d8858b6,-0x378b6de032b10a1c4b2c7081189040de8,0x334dd48669a525bf769e3dc1652fc1f8,-0x21ba486d1c160429c8d0f4a378734c8,0xeb00bfa9aae8766058a9056405858,-0x3ce1db3f9064daa244faf469048b,0x7e33336adf033dc535fafdbe91,-0x5f47cb8e481a58e47987d4e9,0xc8690c97527dfbc6fe993]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 21 48 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 48 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 47 indices rho q8 m8 8 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 47 indices rho q8 m8 8 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0xcecd,-0x13b,0x1]
def r9 : List ℤ := raw_ints% [-0xa1b09bdb65bd4efe5ce880000,-0xe81b5e6125762fed1f2788000,-0x9d1f317d68495a027f46de000,-0x42b71e5e1be4866bfc7e77e00,-0x13efa1f5f82d7f6f857b7bd00,-0x4756174352ad79c094b0dea0,-0xc650750cbd974ca53d04090,-0x1b6d4e5fe10250911996ff0,-0x31179357bdfeeb45f2d978,-0x47d3ba4311b4d094aa4ea,-0x5670937fe2ec49a3ae21,-0x55cabb7f80fc6ae3322,-0x462dbfdb9705f91e39,-0x2f1eea74f8d69557f,-0x19c2a5adb0510e0c,-0xb50ade1f40ca41,-0x3e957d8b33db2,-0x107a679dff87,-0x320b642f8f,-0x629aef9d,-0x6034d1]
def m9 : List ℤ := raw_ints% [0x0,-0x3bdb24dd16aed6125c93f7696db3ef16c00,0x635fd30732615d760e149386ca3dde2ea900,-0x4fa9e4bf71551a56848c73df24c3414864f00,0x29118e92d9a8b14236435be0e59b9088653840,-0xf4c693ae0c2b2acd6bbdeb41945a4cb800c7c0,0x4630201b37349d5a3b8dc1474737b7e87cacd00,-0x101d8c5c83f683262ac9e6ca4f945ecff6110600,0x30affaa9532d44b89f799074987f3ae8b4709ee0,-0x7b4aa10e7e864f55f5945f59da383a88a66c14a0,0x109648505ae714092e7379e57f2c05c08f299f520,-0x1eac57e425804309415aee18af12507be758d4060,0x311f7d0a77d51767083921d8561818f3689bba634,-0x448d03e0d76c8a8a8522bbdbec8554e0ca8594fdc,0x53be4ec07456c809da6bec56e6c52bd69d4edfe3c,-0x59dc08016bba9dcc7fa02ae95ed63f60aac165154,0x54e3e49e40cec00108a6700ccbba2e61f57e58254,-0x46b3926aaca570dad3ccf3749267dd5df54e2b93c,0x33f093f1794e925d5876bd195ff026267984b0bfc,-0x21a5883c8af3aad4f9e7216d4793ffeda445d0c94,0x1332de8bf2c9256c88d47898a22b66d263d1f41fd,-0x9a171162f8558cbf4001e7c30310b326669fecc7,0x43c37622f49e40c00e3cd05e1287bb9bc078925f,-0x1a0708e15f09d50c0e661596d88358af9e8ffec5,0x8b08a4f0cfe66073becada774961ca52f11415c,-0x281b1f10386434ea92d2c08fa101441b4544e94,0x9ebed17964da64ddb3198279894bd3532270e4,-0x215ee9b2a45ae456145721e57e29b573674c4c,0x5e4d1a7157fdb45634ee0733145fb905dac3a,-0xdcc2ed92926871e64f10832be1d6c8ff088e,0x1a4a95a970a50664975b9a7a84af16373dae,-0x27e06a41121d54107c8b90f36a52962579a,0x2ec58af4983c1dbc61861bc265525b5648,-0x28d5d9d5d54c0c9214a2c4964240a9398,0x1931f62a22f915788f3a2ef8c236fb08,-0xa34e3fa5f3f567aaf5b8ba66acde98,0x26ebab5b280919805389d6119cd7d,-0x492e221861827a6c32eee218407,0x313c3fddccdb9d2bebb63fbaf,-0x5a3ea2652b472a985bde75]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 21 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 47 indices rho q9 m9 9 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 47 indices rho q9 m9 9 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x6034d1,0xcecd,-0x13b,0x1]
def r10 : List ℤ := raw_ints% [0x4b385c334e230c83aeaa1280000,0x6bcb85406e9e21dec530d728000,0x48d504cb81677e10ca6b52c6000,0x1edc17d2927d89e3fb3c15d1600,0x933247ed025dedc341227c1d00,0x20d4e728c9a81222939f821520,0x5aff8bf3df31d553d6b75c910,0xc8ad953e3b5b63f72a673f50,0x165cee123ee9217a21d54b98,0x209308d8a73de6d11ecdc12,0x27001bce80463056722829,0x267a13e2f3b50c104f2dc,0x1f40c7e56ae3980cfd37,0x14ceff4d1160b7ea520,0xb42aec1826ae1ddef,0x4e26c95f0015fb06,0x1a97d26d5c89c39,0x6dc59a4bcdd2a,0x144753dde378,0x267b9595d2,0x238eb7d8]
def m10 : List ℤ := raw_ints% [0x0,0x6501ce351647093efc39b181e91fa3766400,-0xa5de03dee347860daf29461a016d76cebd300,0x837a3edb46cc1dfc9e59c910e59c460a809500,-0x42ff6d9fbc8ec92d44dd8730872820dc19e1ec0,0x18a91fc985ce0c20f993f2f4c674242a00801540,-0x6fc0ea75a3bd9c54a89539845d5d24d1f4017a00,0x1955999b0ee9cdc226754ca98da3bade7d6b9df00,-0x4b8a00a809205bae97f7b22454b255ff6fe67eb60,0xbcb406b63203a8a175fa4d22b7249052975ddbe20,-0x19083b1196f64c9869af90f77d96fc1e1de1f234a0,0x2d9e901fc5b04c9743628b17a8c9441abb5e6adee0,-0x47f60c7f1086ac9c4f9bd8a551eb4d58428e416dac,0x62da94e508b9f1a8dfbc4c92555b30cade631fd1c4,-0x76cd5b93340291cf9c7dc95a9eef72442a24785364,0x7d52ff61837a325f08648b075f797708a57f53e28c,-0x744e93b3a9a7f085d64c84f86577c32adb1d5b125c,0x5f15711970a31f9a877cb611e26b6fe818d564b7d4,-0x44819a29ad71718bb16bf2f212d9e5ac4224e422d4,0x2b7b7304548fc390da2a48d5b198d2f0c05bb5955c,-0x1848db13a80f4092d70a80afe5fe1fd6bc9ea0197b,0xbe8e99e696f8c19f1e074eff6558645e3138eb721,-0x51d350f3d14817f837f7799e669132208ecc9e989,0x1ea512ab0b1246dd5c4e3a57d673415cf73a450b3,-0x9f5dd2f63501efb211dccaa12be4f664b786dde4,0x2cad076719228b438b05325ba1c41abbebec812c,-0xab82a4416dd132860d1e3e810c755a45fabb3dc,0x22e3c6cf8d1628cf82e8f9aed9c7c80d9cf29f4,-0x5f299e4f792018ec9f092e7aa8d2db60162276,0xd661c4782606a0a291512f93fd866569ec482,-0x187bccabaf611c72865c6ea67d75db437ede2,0x2376c8d7891313a1733a6ce4b15a73121a96,-0x2787a0c8323f3b796a749015fa43c864848,0x209ab36edef1c71df0aac5b2fb2c8a5b18,-0x12ddfaf550002043a063ca039096e81e8,0x71abb4396337c60cd18becbd2cb0eb8,-0x18e6dc3c57e6584a37464da57a78bb,0x2a706c5cd5b289444918020e8221,-0x196ea0ca7f5b1a255ab13395f9,0x289ed52a887ae9ac660f643]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 21 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 47 indices rho q10 m10 10 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 47 indices rho q10 m10 10 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r11 : List ℤ := raw_ints% [-0x1bcd141669bcdef3da5e5e5c00000,-0x27c7bd9c13f016a57b6df64f40000,-0x1ad51eabd92dfcedd8883713a8000,-0xb5915945d89c1845c9a20cf83000,-0x3603ff5b0e1b502d3bc9c5103200,-0xc051dedcdd9c1b13c1300761e00,-0x213a7d801e4a6d455e55cea8f60,-0x49104055f775f239b8ecac2bf0,-0x81d6cd3925f1555ead65db770,-0xbc693684f696fd96f494bbd8,-0xe09a6d0bb4fbf2ba9095276,-0xdc7b5bb243aa99d2ce7ecf,-0xb20c34007d1fec884bbbc,-0x75bcb43aa9eea9ff3961,-0x3f32452ab6b4e2ae8b0,-0x1b251b83f8ea416041,-0x92052b5015bfdeea,-0x251be85e9a05f67,-0x6b9739c719a7e,-0xc70d2bb85e0,-0xb1a70ca66]
def m11 : List ℤ := raw_ints% [0x0,-0xaa730bf99597df9a49a15b8b396563d7c8c00,0x114eea82494b5edc3999c4baa8624f248df4100,-0xd91e14fb61b3696338643ac81f10c569e7bf700,0x6d647bd05cb8f6ca09aed7d6b81600b932baee40,-0x27cc4613ce67225ebfd621ea3c4a7ad9ab52e39c0,0xb2308f1e6768dcc1e7e7877cdbf12f16559df6300,-0x27e533f7df37693528ddb10092038be378c3110800,0x756ec4ecbcd1ce38484da907666d1639b3d12a5b60,-0x1217898031de32dee536e2f2dc36371dc78123c3220,0x25df522688260db489741df624f4eec239a395476a0,-0x44098b4671752db5d42eb0a961978ba2534ccaaa8e0,0x69bcbf3faed67ee89992918caf8be68fa1f4e48d974,-0x8f0538e4cda101de68f27d18a0d70d3e7a6e1a13d9c,0xa921b50b67f1039d5cd8959e57525b172e3d33101fc,-0xaf70ed8cf4aacda36142f8c10166ec2e4d08abc8694,0x9ffb9618bb9ac80128081d17770d13ff0dccd7e3c34,-0x80687b65187c29880fe3e3757293353341d5b72b4dc,0x5ac040ab920a6f221f4849712cde577ff020ff9a69c,-0x3872afe63951677be7beec0f75c3de6db30ace34374,0x1edca9c53d3614a7ee609e488d4ccb1725181bb3ccd,-0xeccad43c6a17c3ec479aa4cde5b0716d6e3a983237,0x634b27d515581e9e9a19b1457a7bf8c5abce554b4f,-0x244334b819fd59bcaa358a806a16d7d8a41e299415,0xb7997fc8bbc8d8b0e47d87bbdd80737370d42f05c,-0x32050e48efabe97a320301b0f656446e44a1d1f94,0xba3d24da409332980d42410633be6586d5ca0ae4,-0x24a8d2e92002f0a327ac1acffe838a234a0b964c,0x607f227e45d1063b3ca973f93c787ea26f7215a,-0xd126d8d4ceb08cc16ccbc3cf9f70e98d0ba5ee,0x16e63f0dd43c164e84cb2cb5683753e46c230e,-0x1faa52dd4b069ba5c9a7460745fa3669824ba,0x2186d6e632c2c6a050ce8465d7c3d04b7b68,-0x1a1be70d0beb944dc0d5c2f7b43ddde50f8,0xe29143a0ab21a63724b9d2320688fd468,-0x4f3dbdcad915bb362e641467e200b7b8,0xff1a8fe6d6e47ff32b5a510f5db9cd,-0x189cc6bb392dbbc9ba1e49e0ee9f7,0xd21b4173f7a03751fcc3d00c1f,-0x1246cc85a73fe20243256a45]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 21 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 47 indices rho q11 m11 11 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 47 indices rho q11 m11 11 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r12 : List ℤ := raw_ints% [0x8ae662c2a910b6efe08c08a2f00000,0xc67b0ed3a87bf297785748cbdf0000,0x85ad9d96c1c7b4cfce87d0e1b94000,0x3870f643cb120d57ab5479dd304400,0x10c2956321dc041ed2a2940ee1f200,0x3b8d14eccb04a0a1b5293d9706ac0,0xa43f9822ebf7ec2e13a0d3871820,0x1683a1fdb15fbe087586499fbfe0,0x27e4db07941f6b04016f2ac2540,0x39b3b29ac47795ccda501fa0cc,0x44880431192b235a408512b1a,0x42fd2d773e83dd47592fb2f8,0x35d51b59fa0786cffe41cc7,0x236567d3258c6850f1d1da,0x12df80772c4edad15b833,0x80af5f62c08270250bc,0x2adb04b52b2f92459b,0xac3f99012e223c3e,0x1ec3e77eb175d13,0x37e1be73cab48,0x30b0c8eba5e]
def m12 : List ℤ := raw_ints% [0x0,0x11fa224352c7049545c404a7af0db187c22c400,-0x1ce7fbe5bf95c81fe66828c698c7036c678bdb00,0x166bec693076ff38dec44fe7f86097e2631254d00,-0xb2c428304b0f520ed694b582efa48d3e7f10d50c0,0x404cbb191a2431568ebfa621cc877248c9aca15b40,-0x11c85b4d78bc5456d3c700e41933864aadf90097c00,0x3eee5d0a864564696e752150586cd286275df296500,-0xb6eae1900170097e0a4602e92fd82ee4495449268e0,0x1bd0941f95f9aada9a6095044a84e3921116a218eea0,-0x3970f543d852b067054fc38baaa66e85001905eea120,0x65bfe727a54695cddeb9265194c37bd61928c6959060,-0x9bd4d07e917ef1bc5d39714b21979aeedc4226c9f86c,0xcf96ae38bc733a5dfcc612b4ca3c9ebe924c9353fe04,-0xf19df6d316997bd389ec6114c76f681588adbff4a9a4,0xf6817091cebb399c4143904d8918a0840a75dc282b4c,-0xdceb1b03e04f7e813eaa4aae3ebdcd5fd0fae087acfc,0xae1f87445b2726897db08a1d27f36caee5b9029401b4,-0x78bbfc7c86df899c4c7762471538ff17c2b7c76a65b4,0x499b4ca5e1c37e59c99a2a534bf0f349a1f3d4bd3afc,-0x2766cbbe3bf84642a8294857ffe7da3660d3c6ffac2b,0x127a3d1051aa8efe3e415d778c5007a325c63221f231,-0x791306fcff354f45a2f0549a8c5239982ce46531119,0x2b1f02c0ead0cca82e624488308abd4f632bcaea8e3,-0xd4913b39fbccc13d0480890eef7cadf96617471de4,0x3847f3ee4bed006084c642861e01aa0146a031ad2c,-0xcb3ab8a6faa4d41640f4dab0715d4e35fb33d26dc,0x26b49ab3fbacef8d4c4e67139d46b9cf9989a7ef4,-0x624f13c6f9ee2c9811789c731a56a9516659de56,0xccf6c1b12528ab3d7349f11232d05da37760a22,-0x1581ec18b3b18a5c5c523c8ff0a07db17a56b82,0x1c61a5bf11b4a5510a4e2334e3404c81fc7e76,-0x1c87c6821680967a53fac9d2ddafeee094da8,0x14f73358356db9b7624ec075c734e0860538,-0xaa67c5e2630b52a4fe0dcd8090f91b6808,0x3750ca3e8de78ee1af76708374a052818,-0xa3703413bd312403e3862c5dc747feb,0xe460c2acc98b94eb67a118e076eb1,-0x6c71a7cfec79c6f4efd62681809,0x83856c157f50a161bb7b5df3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 21 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 47 indices rho q12 m12 12 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 47 indices rho q12 m12 12 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r13 : List ℤ := raw_ints% [-0x2611c106de864106385cb6fa5db00000,-0x36552ed874241db425100fcd3f1b0000,-0x248b572ec0b8ad599a1eef571c574000,-0xf681fd617152f7b4ea56def63c8d400,-0x491465d418644d58616cb091b148600,-0x10330b49dbb6ba4446c5d91e26ee9c0,-0x2c96d9e18f2e0550ff56679b0b05e0,-0x619260a00036a89395ddb374d6820,-0xac749b71f3217095c2ad39afe910,-0xf8ba987a382a7741d8726d557ac,-0x12676ab0465fca3ea3e38fab10e,-0x11eca45e4127556f56a91fe6ec,-0xe582245acec9d1fa89d63056,-0x962fd79f48130c8df94a087,-0x4fa2c7a64d956a700bbf4a,-0x21b7a2ceac30b04ea3da9,-0xb248af391b28b718a50,-0x2c5fee702f610574ad,-0x7d65831d70dc19c4,-0xe09f5136d47c2b,-0xc04c9bcd39ce]
def m13 : List ℤ := raw_ints% [0x0,-0x1e5619d19bafd7bbe5bac7daf7671b9517aaac00,0x304a0b57c5a378c9c5455d9a0055a650d9bc01900,-0x251173ffc1ca202db0349ae9f65427076e14b75f00,0x124615226b5cdbb4199f40a2082abb1215629d23440,-0x6800856520218ebdf163b7257c125589f1204b65bc0,0x1c6f042c4d04d5723751d9263e0bed686dcbf0ee6900,-0x636ebaca78374b446181529beb665aa50fd86c17da00,0x11d77b308687f4a1fc74d4cf399e23100f0f2e9901be0,-0x2adb3470a628a5ce6fb0a2401ef960a8f8b5859569ba0,0x5755a1898a736a897a04512ac729c60790c7495afa420,-0x98939f2e5ffe481922ba75733a96272338f7fa74b3560,0xe65557e015b9dcbad7633ef0fb69e749f979efb0800b4,-0x12e43cba57ecfd73113a64ae9018f6d39f2926464b475c,0x15a58283697b48bc58c88841c513b34583da83dfbec1bc,-0x15b9cc5ff62433cf996a0d3fae6988eae1ccbeb6828fd4,0x1323bf8ce1cb502218040c1a28e1bb6f7fe170056f8b14,-0xed10cc1fe8a8b93fa206ac7f84cb6630dbd56df65bf7c,0xa14d0416ac3c51d06a7db6c22ca9bc2ea7f999ca8e83c,-0x6066c05d1645b5a11b981ae1108cb83a743e5b418d754,0x32881c732345e23f623ae1c7edc5324aa481f14f5b09d,-0x172d40fb23761511d36853afa294dbbd6adf3891732a7,0x945573724ac2d1bbd9e9eec2829eff92033dd8b9e73f,-0x3386265593c485e9f05144bd69e82a25a6cd2acb1a65,0xf74cdb2709801292128828be69840bd866ec9be4d5c,-0x3fa22c810b12ca93160a312e0b7f58ee9be2874da94,0xded60ce52563a4024f1800e8b7360e6cadf5cf7ee4,-0x290ee707dad91545284e7869bdbc62a1af290a5e4c,0x649c8ba86a8adfff6f960ced5ce7a7ac7cd48a47a,-0xc9bafa569be3f99089f89c62c9efb891dc3bcd4e,0x1448203814fa4ab945012750c9bd2a11f24da26e,-0x1987f0a5fc9632202660edaf3d31022c9752fda,0x185b126fb3275b6119da0cc86c813909b1d988,-0x10e11f011d4dc9ed6816fe9b35cc922a44958,0x806a3c129e0878445da1fa83cf4d63cc0c8,-0x26a9684a527684aa9979a43147991c51d8,0x68c4277391d046162d2b7002d1a11b1d,-0x846fc87fee9b2f39497c3dabb5bee7,0x37f335fed71db09427e80e30f38f,-0x3b21766c435b967179e8ca315]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 21 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 47 indices rho q13 m13 13 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 47 indices rho q13 m13 13 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r14 : List ℤ := raw_ints% [0x965a0700f24e936cc53d42e5a7f300000,0xd65899a9804c551cbed094d5bfbf30000,0x8ffeae69966c19ff71510f15df0bd4000,0x3ca039d306c86d3c96fad0a41388e7400,0x11f25a983f843e0f41155fee35fdbc600,0x3f8c34511078120c3f86dda88854c3c0,0xae9a03377c3ec62a04597e0726aa3e0,0x17d4e1738f75847b3bcb7cb62ccec60,0x2a071c5f55a43a965bceafeea36c50,0x3c76f9a5e1455c5abbaffec3c683c,0x4761e69466d31a62da2077235e7e,0x454d92a2adc14fc848fe91263a8,0x37433702dabef040beec21a752,0x2403fa7919b3e9b282d0a87e8,0x1301f438efb64f2755b6e8bd,0x8010bd234600b81122b672,0x2a0dee16b290049739ac3,0xa6398115b757250e038,0x1d1871bbe4a57e0ce5,0x338dbb4c3271bdea,0x2b8b840e5d201b]
def m14 : List ℤ := raw_ints% [0x0,0x33314b91b6b8bc0d13ab3141817dfe8b97f002400,-0x50b120d2bb50c554e3a4263d8a29fb888d4d42a300,0x3d50f8dc575eff8a3f27f5b898771b6454803e54500,-0x1de9872ea27cc9526f7ddf4aecae0d83e2f2e496b2c0,0xa8673e8160e9efdd2d72f610e2bfa229c8537df73140,-0x2d86b7dac9ef1d2ec6c7fe48560ab2a5304775f364e00,0x9d5ca62426f21bd046805cb22575953e63d3a586ddb00,-0x1be5ac31fee86ad10dc51c4a7eaddc8f462ebaed9b1260,0x422c86b5200c8fbfb39633119df0dd780c362f5e136320,-0x851a9ff34a7bbd528cfd7e443e849c90c65cd5d64f71a0,0xe56679cfabc9e452c24811d532350a6008c6d19c41cde0,-0x1557098b6eec3664ebd63282a63b080bd746a31161d6f2c,0x1b97f58808fc1138e5c8fdc686845579cc1a8eb3ad6ae44,-0x1f2214a6d195ddcb95259643636202836965dfb201fe3e4,0x1ebf0567d67d9614b719c90b3052328985f92c4a53c800c,-0x1aa199fc04e6b69d0d7e15d9718703611a00f4fb617fe9c,0x1440a65ce3b5ebe8dad8147a1244377512e3d519cf7e094,-0xd863efea1e6e2c82d73d2c8183042d755c1b5974a50594,0x7ecc6ad9107fddab900ba7bd798a51f58ead5cd957ef9c,-0x4118058a11606a8d7f15530cfe81cee2abe01af66caddb,0x1d342dcca057aadda6fb9a492dfcd41ea2fa142981aa41,-0xb693a095ef6fb86ea0b03034c75dcadd176d1cf264da9,0x3ddada31653225eca33734263700c3385b34717d33813,-0x1211326dea6ff0b5b1ad51b552223c71a920a7a3467e4,0x484998e7a0bc16ca9c2d20f06cc9c35e334f6108972c,-0xf57ace11fe4ae436146a52ca6f435b9e287b0fde7dc,0x2bc0e793ffd1ab7c887cc757d914a6448d323cb8df4,-0x676c4cf94be78c84b9c0280913284b516f296fac36,0xc76124f29a20f4072a914a5e854fff0a10b9b25c2,-0x13333904d060a39dc4d9e4375651b686ed7626f22,0x170c0ebf2d09e12578cbcc0eb9ca48064c060456,-0x14dacaf015642a8e252ecf206fa88b768790608,0xd9f7154ee8dd6a32eeed2bd256b6b7cebf858,-0x60f23d66f42b1e9b207d6787378f23dc5f28,0x1b0d507e69fc3751c0750d9f4784ddb4c78,-0x432fc3c4c7f04ded1f841cdae000c4a1b,0x4ccaea07070006027e5d41254841441,-0x1cdaf12c471335d52863403fe6b19,0x1a932a64d363809ad950d3d0a3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 21 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 47 indices rho q14 m14 14 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 47 indices rho q14 m14 14 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r15 : List ℤ := raw_ints% [-0x220bd483079ddbc7975b376dc2bb9b80000,-0x307d23f95a7d19e49c57a6dff4606638000,-0x2089d5a6f840b25c14eb6a2b067739ea000,-0xdaede5dda0dc2c37f7ecfa0403c6f01200,-0x40b8eb774b8527c5602da5e26669979500,-0xe4d767f0eb9810a0865e9cff8691aa560,-0x273be66c73f2948acc125bb77aaee16d0,-0x55874ed6bd4aabb4181c2ac80bd9b6c0,-0x9688abf3136927a0b31c614ccb39b78,-0xd817f879ce2369478411472979fbde,-0xfe7bf211b85e7f0f21ee6922b6cf5,-0xf663901fa99bdc8858b641535901,-0xc3dc5773e035e43f236d2ba044b,-0x7f3237f17d5b2a321f3e3a71a1,-0x42dc25288fe8e0d3e59c2a992,-0x1c0668dc1880e2aa68208f49,-0x92769d5fbc02151dd55a0c,-0x23f51a18223ead52c0431,-0x63f7272292a450ccf9d,-0xaf94a8316f9b9eb66,-0x92bd3dbd56c07bd]
def m15 : List ℤ := raw_ints% [0x0,-0x56632f85e457bd561130e31e8a849d8b906503cc00,0x86dfb19f5c85486fe71b87ff8cc033229efe6073100,-0x657b36494a0b8dc2fd2da928702f3347659053128700,0x3100bb66414ed0b0b783d3b0ffaf1927b5773c15c8a40,-0x110fa4cec96bd97b2d03cb5a01170509885faa5f05adc0,0x48fde07d5d3c8733d3815d17a47f8ecad5e6609ea45f00,-0xf970be2134d897c0f4c4739ebf0de029b97484a756fc00,0x2bb373688197affccbd17dc731687723d48d22957bcc060,-0x66650e901d5262c41679310c7718b308efc06eddb81f120,0xcb57070be621fc38f12d958d3fb5f1ec1b2dee871bb1da0,-0x159ce33cb844bdda665bd603956f994696bd223827acc5e0,0x1fb950b480991261450db7bbe209b9ada5c34961877e5bf4,-0x286d9827a59af140d6d9820b2d01484f975bb90a5f3b2d1c,0x2ceccb958700fa06e819b1d6982cbc6f6f1af5e459e2fd7c,-0x2baa21625099992410f39b26535e8962d7ad145aa83dad14,0x25315995fbfe555bf6d214747212e76e5441a574819526f4,-0x1bca7005f67122f7b0610fe7ca0de83b898467e72aac811c,0x1237a1b32061d678d81413e370299ce4960bfce11c32b8dc,-0xa77c4e0acead43a4d7e5f9d813fd1010230fd99c0c74034,0x5437eaa19c73317c628a32a8ff2f92cd66750aeb524cd6d,-0x24f68475a5450dd04a52e1db7ae578be60539f69ec67e17,0xe1c01bccfdfc637ce2500c13ca0c6f8fc5061ff286f62f,-0x4a99b71057570007cb6786070b3f1b8a9f8c4b250dc1b5,0x15379e57731bc601d4972a1ff4b9bbde14e895b10c885c,-0x527fa8face76edd70f2e3f39e66d3ba18a0e270500f94,0x10fa8f27e945ff7369bb738e135fe18186ad2b14b5ce4,-0x2ed5666f56642a51d424b9d14b186878f62799b4d44c,0x6ac4c9e76e0af2cf4536b9239ef8197f61828b8b59a,-0xc5da7199d7af1c9fe9e623b7867e2e97250628feae,0x123e750d2d8950327085ab0353383ff6a6576bbbce,-0x14dfd20ad026827872da2d693cfc5b460769778fa,0x11e86b2c009eb659da95c1457986c285c410e8a8,-0xb05116d1e37e7a82924632a50333da5e1364b8,0x494f987c88c556250481e19ffeddd77506828,-0x12f28f6199e01d41e23164cb85fd75cf64f8,0x2b1a4800e5e8a3ca896a5cff98a186416d,-0x2c859d4e3d0f45d7f64f1fab60fff2d7,0xee0319ce860955f451d83073b21ff,-0xbf06ce1379e51ebb35c8e958e5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 21 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 47 indices rho q15 m15 15 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 47 indices rho q15 m15 15 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r16 : List ℤ := raw_ints% [0x72badf394c58778e87dec6a4f493ac080000,0xa3401a348ef50a5d6ca8be6c6818ded08000,0x6d709f0027afc999b99617bb7ed24ab7e000,0x2df8b2a4f632eb1c8770bfc462400c789e00,0xd9305e8fccbb24800076d5c247966272d00,0x2fee96f751a98c3489591abf871a8323aa0,0x834b19348ba93a527974bf8875b6bc2490,0x11dc1a07daa1106f5fa649653799018390,0x1f60dafbf07556f54efbd7f001b6e3828,0x2cf4aa5582a3fa064faf3a94d0db63ca,0x34d3b1a44ad15f461ce406e6f89ad79,0x33059f99562eb0307b030743403284,0x2872aff1833b05532f6cfbea7dda4,0x1a2fe8a92bf8617225483484095a,0xdb7a0f2d2414828a6e6ad40ab5,0x5ba1d780d391f2261dd4efc98,0x1dcb6f84407930bbeb789a29,0x746c61c8efe1387a1842a0,0x141b253b4ee829a0553a2,0x230fadba343c83e1170,0x1d0d3ee79a5ecdf2b]
def m16 : List ℤ := raw_ints% [0x0,0x91c76031f1540f813d027f4389bfc9db83aa7668400,-0xe17f445e04d202d3e54f11a1c15d89a23b30c2c22b00,0xa80bae11169e0c5ab2889749b6fed4d29bd52aa3e7d00,-0x50576d61136532feaf96aad3bc8dfd726a0cf3fd72c4c0,0x1baf580bc05a57df28e43fc138d1fb45697da156a131740,-0x752e5ff670c067f59445ef7a6cdbe66c09cb27fb0897000,0x18c055de6caa31eefd138b3dd305ca51b6b417fafdafc100,-0x449542bc286390d8af2cbdf3f1a703c851f50c7c33d387e0,0x9ec5655577fe2610b96efc6d660c5972231cf9d30eabfba0,-0x1375c5223f7737fc942e42d4d81a702141867cc2c98868620,0x20a9ddcc1f2090bb337562078f9d38e92eb0db6a3deea3760,-0x2f4ae97ba5f8090b5fbd21e7ce1b1778082fa15bc832491ec,0x3b69607c8480c8e65e041631de2549802f8462a9f1a262284,-0x41097814eb9af464e4c447f1e2f80c0683a1420bff5284224,0x3e3998a4785eb0f525ea7b4280e9ec26f3ca49ca390f9a0cc,-0x3421e8a3087cd07dbb6122ae00dcba5f8007f1fa271006f3c,0x2647f3bb9e60bf52e577149a4b74db6a76474e68132100c74,-0x18a30af6cb8d6ed265668b4a26d9d95492a350322b62d7a74,0xde25bffc6129b883e3412c8d257627cfabb783863a8b5b3c,-0x6d6dcad20699f5f990089c5fba5e6356e6b0b2933deeee8b,0x2efd3d97beb37fee6d67d8911d025fdc394bfb12fb244f51,-0x1186216a7773b1f3897b8ed028aae108db77232b34b50f39,0x5a6139fe0221a5b160864a1c6fe009d06ca32316b56ce43,-0x1907a42352a7dc64ee3a6d1cb1146017e033fc6d6c9cbe4,0x5e94018e68aed60ea1abc2cd0dc306151d6deb69096f2c,-0x12df8b7d01660db378d9d99576c7e1067ca178701e26dc,0x325905e2efa7a6023a6740cbbcee302250a1e70dd66f4,-0x6eae32d759fff28f62b6f0c8581afb9baa2dbc1c8c16,0xc51b229f177476d69a666be31c83203f740e37b1762,-0x1165cce30dcd20501b734ba17cdc52c9e70716b78c2,0x12f773c8ca68a79b695564598ca5e030cb1e6a2c36,-0xf6b4b206401ee2ca4ff92d05ba29bc29d1c31968,0x8eeed6b536870e019e08ca503ba2c8ba965ac78,-0x3785d55044c34b83629ac613700180757c1f48,0xd486afb61ac1fa71c9ba3c3a9bb10e82e3d8,-0x1ba903ff6f225ad3f443ecf58c5beed074b,0x19ceebcdae8976b11acab262be15102d1,-0x7aa7a2e448072447a653cc50589f29,0x55caaea6481a41591457ff1fe53]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 21 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 47 indices rho q16 m16 16 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 47 indices rho q16 m16 16 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r17 : List ℤ := raw_ints% [-0x16b6e83f2ed3453073ea9e740cd0709c380000,-0x204b3511eb2840c457025cb5a50a0c96338000,-0x15a1235ac01a797aa8197eb1e1b54a2acf2000,-0x9139fc4b2a92f37af7519fce769dd2d70d200,-0x2ad5d7157e8f9afa984635a308440040d1b00,-0x97130ae4c48d4c06bf2607a9b8c203eaa060,-0x19d4637445e76386e41e88682442a2397af0,-0x3822eda62e3b8551f32aab0d20d14c5f410,-0x62789071fe6d7a347c8669de6df2084cc8,-0x8cd4dfb67b4ae79a771db0913802fbca6,-0xa52ae3f91c551e61cd8d04576bddd897,-0x9f2deb0de39e52264c790ded1cba3d6,-0x7de2e522c77fac1bd57cb926e93cff,-0x51484484bb391eabd891fc17072df,-0x2a72a99962942c323fd96e4a9b00,-0x11a94b7bc14d9001e080846c271,-0x5b862ac35315aa51ea5598f86,-0x16408fd0d0447d3da26d2a8b,-0x3d2b6df86bb569db4fcb25,-0x6a07803ecfb4d2018cb9,-0x573cafec609b152587]
def m17 : List ℤ := raw_ints% [0x0,-0xf6007254473dda2a16f436c1f873a4a26e2fa7cfec00,0x1791c296470422cbb0bd86b790c8ecbb07413f8a7a8900,-0x1166aaa0617d429eab30bae197a17e7f9e810692ad76f00,0x83d3388b01a4040bde12506d319db3d9522e83e044f7040,-0x2cf88a9bcd966d73d799fda0f772c85e0ec808a4e4f4afc0,0xbc5de897d4ca7418fcfd6885e8df28cdcbc785582139c500,-0x275b63c406ffe3191edf2a8f6cc5e1dbb451ecb384603ee00,0x6bd37080fe67d06221120c04facf6cea0f7f7aa7e5a9028e0,-0xf6b0d0e962e8522a46d57aa116b4586a84e3bc6edcb7bd2a0,0x1dddb306593dcbe1705eab2dd765f37edbdab46545ac058320,-0x317d370c9f7e734c513b625f00bd4274870034ad23a7e23a60,0x46b232bcc1f68794aa60c32d86159ea06a6777e0a66a8d2b34,-0x5791b3ae7762a5cbce113db66e13c8449bc04b4e11cd40aedc,0x5e740fee8290e7467b4d0c77061438295ac0049e926525753c,-0x58f9e4262cd0f37fae46f1071cd6cc8501f61e499d38571e54,0x4955e77a65e4049428cc35a8205216bd9cb2b753b38a8e07d4,-0x34ee165c72a6963b26f1fc95d3d652084f1d1f47c8892361bc,0x217325b5903fdb3d69c5724b5dcfc9c4e3cecab1a2c0b6c07c,-0x127da38722582ddfda5d8555e7f8f42b7d295efa42338f3614,0x8ec8def4201c0f8d6c86cb9627d8e2456d5187d5aefd6c33d,-0x3bfe2a82124d2e0f1a7cefd15829733645416f6761c65a487,0x15dc4378398780cc8efcc485e31dae163c73a62c8903f081f,-0x6dfb8d6cdf503a3b170ee5cfc2bb8baef7e1643bf600ba05,0x1da8ac13f5a81897deefe8ba0e470dea6bcd84c786e5515c,-0x6ce7c7a14872ee32180d3b823979028cdd12199269ace94,0x1511f7a798699a527e995244ce9d04bb561ecf5ccbdb4e4,-0x365a8a1bcb95735a234287cf7460b5c8dd962d3f4ea84c,0x73328df0918b59ca65ef46d7be46e972f297dfc80d4ba,-0xc51a28b1f7694a066921f70b576298a881916069ba0e,0x10a5d384f072b633c306e12a8b2d5fdd66938b4f6f2e,-0x11492230c9f0261ec81f053cf6dc1e7e33123a0001a,0xd4f6a3480e1787c2ecddf0bd2d39b9600500e60c8,-0x741a5119ccf25735b8974bf4aa25197c91364b18,0x2a1c23c94d55e4cc23e7444021bd4e4bd6f3288,-0x951b5c81ebf63f3e0e95a2bdc14b7a374e918,0x11c129fac18e974e0561f32b05121dea7cbd,-0xef52af6aec4f063f7412f289c51be75c7,0x3f2ef3f7f714634b392bd36ca32076f,-0x26844ab226de366ee3fc6ca85bb5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 21 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 47 indices rho q17 m17 17 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 47 indices rho q17 m17 17 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r18 : List ℤ := raw_ints% [0x44351a0907a033885ad345f6ef25581e8980000,0x60e5fdc37dd64b80478f4483b38e20b7c298000,0x40d885c40ed10f6d440307bd76f1adef204a000,0x1b2ff982a2df4a8abbef6c9665ba0a8ee017a00,0x802d7d2e042f011787359c6cfcfce6e3245b00,0x1c39316effc2b416ea30d41f792832b9cb9de0,0x4d1d7f693b62520761b6c1359f6524d071470,0xa760e05fba6a60939627f7ce3be90e8daa30,0x1252ef5769b233acb0882b7d523fed71db28,0x1a2a4cf1e2bcd70eecca59b63965fc2ce1e,0x1ea2151d4045838f153276f119c6f11c4f,0x1d772d45bec5c9a4b05e5bc288ca75de4,0x1740b35fceca347360b3ec213a6b10e9,0xefa5c0be03bf5ace326c619d4aecc0,0x7cd0f0e659ed4ab67007a3ad2ca83,0x33c6bc775426d8e5a27b724ff71e,0x10b676356f402362ab6d7a75205,0x40c35b8c0b9780db5a78b173e,0xb13e83762cc24ae0005cf9e,0x131ab0e535dbaa651d6352,0xfa02115d303727bc88a]
def m18 : List ℤ := raw_ints% [0x0,0x19f20c0ee3838602706bc1c67534325d219f06b2ede400,-0x276d24ba2e2a3506a886e11a7695a834da232719aec7300,0x1cd83cdd5ab37218cdbc26f00aaed08993cb9ea010fef500,-0xd8773b9d7b1bd17f1320832dbf86e35b4693748f5a8606c0,0x491fd5c2fabedbcbe123cbbdfae8816242101d047dd8a8d40,-0x12f2e9682028bb75ec6209e69957079c40fc4c68312da86200,0x3ead3b1e862461d0eb373e1b60ecc16af7f27da3be22639700,-0xa9d2baf3ec03807bf1fa7f989de3f18974080a4c4b4ab46960,0x18011110aeb2dc7cc68030feeabf0ffeca5e0765f27de969820,-0x2df085803bd6ec0f7a01ff79fe404bff88ca99ec7b9dbc2bea0,0x4b2b035d8edd56ea69d9ffe4788782e44cec6346e123e186ce0,-0x69f7ac5994b2a3cb45cc2e6670a15c51eff61317fe98e7420ac,0x8173238724c36d22146477b4451005bc7d910d16ff24d349ac4,-0x899b0fad56315bc369723e1dee3ce2cde1640755d7161a00464,0x7fa733c5c1c6943c05775cd2150b0bd2f646529c4dabd944d8c,-0x6786d787e0be78dbb7fa45c24951878db3c43cafc3da50d26dc,0x4974c595e9bfc182aa716f54c0dbeef4857011a20f43ecb7d54,-0x2d974894aa6739b0803bf44c2bb98b9dddb9a03a3acb00e7c54,0x18b97c8cb3b90d422801053548e26bf9fc6ab069b869356e5dc,-0xbb1416dc053535288cc8a43441364737c6a55ee80328443e3b,0x4ceb60587b73dd75581f52d40369823c4e1358c2dc091e5161,-0x1b632dd18a217ee44930c9aaa78e2755e8c84e04dc6842c5c9,0x866b4acf5493079e620f802789e0e035158351d494e743b73,-0x234c05b89cfba0732c6f383d60261a2158e73a0e072e1d9e4,0x7df1bad48a5dadd5a86b205abc4586741ca672e931dae52c,-0x179f597416864069093cd2b076621e68042ce8a3783493dc,0x3aeb30cc0f402d1bbc598f7aae7c48cf801b164297a99f4,-0x785dd76308de95ebc508a078fe547d461e6337c5627df6,0xc5d0d265c5a2ab214d24f182875560b1f4a054421df02,-0xffb9ca2f4fbaaa7b7cad0bf1c8523799be69a9000862,0xfcca515a32d634496fde52ee51d79d0c4f7d8a57616,-0xb847da46de1bd63dbf4226bd076acdbda102c4efc8,0x5e7c593a169b7a60b1995959d13372d4aa853d998,-0x1ffa794d1b53e5650ec24d883afae05b4f0aa068,0x68af961c5bfa15ab01359a95d8b5d9ad771638,-0xb65f920e94c0bdb1da8c28662b9cd668e77b,0x8aad036c09fa640b811fca6f363efbca61,-0x20891005a5098229c841f1bb2371c439,0x114961a21921b3ae31ddca2809703]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 21 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 47 indices rho q18 m18 18 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 47 indices rho q18 m18 18 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r19 : List ℤ := raw_ints% [-0xc378d9331cb535ba91bf172dc027e3b84a900000,-0x11580666a5d63ba50962d772811e5077b56210000,-0xb990f85a93334827c6b80e706c76daa9e6db4000,-0x4dbc7a4f94a4b16bc163e0203b014ccae0213c00,-0x16e299ed9b58fd6ff905143dbfc85fed0a8ab400,-0x508b9b786cec7813472e0c27af8e90531b9e640,-0xdbd6381e4b0756e808f4abcd3a0b3e99b6b100,-0x1dc96ed5ce8541ff051cce31e44964cbba9e50,-0x341b80bfd8159de442f321c57904c820d4c20,-0x4a4c9d25ba0a51afc6a98ca3da0d108833fc,-0x56d989240bb483adf2f2961c63508c619c0,-0x53650735292efd3072ffa8b1efbfee2e73,-0x41af4b0e5a1124c8c6ac04a16e6c1e0f6,-0x2a385288ce86a6743e39207112110bf1,-0x15effce6707e9950e9b0ceea60b2acc,-0x91374cefc66fe9e9e0a2b6fe12af1,-0x2ebc056a2cc8c5c05b6522fabb66,-0xb47dcb3cb7d178bebd9d316513,-0x1ec164d9e8b48b91a82351c58,-0x34cefda63448a5d792d748c,-0x2af9d3e39682441814520]
def m19 : List ℤ := raw_ints% [0x0,-0x2bc874591fedf2241db5d6fee5c814fd28bc5b4df170c00,0x41f7d610a22e783b7f97123c49c8c40634af854756f02100,-0x2fd6906a4dbc84ad8735b60d77f7b5e432b015d21fdc01700,0x163b810d2f40e1d517b468bf1d18045d7f47cc9f4a85c46640,-0x7705a96498cd4404bbb57506ed307ca3fbd22c64fa9707e1c0,0x1e897053fb158cd55a86a512a829ad61f2012e9b27419f31b00,-0x63f67df4220ef1160dfbb0d5c2ed145b05c79c0dbbc3d183000,0x10bee8dcf8fe6fedbdbaf414ff5013147cb4a80b77574c873560,-0x25720256cfbf5baa855d8408c7a79a6ac396c4e40a82fc08e020,0x46d1e39a89c04a194c90821b2b01567c4cc0b9d8e3a1ba3c74a0,-0x72732a647332a44b311da85b170bed2392836234e6f7dec372e0,0x9f42738ecdd9a8852b2ec800078e478c437afb6cac0acfd9ae74,-0xbfe95792840e40e1cac45bb3a9d8b76d786b84f39cbe9f578c9c,0xc91799d322f5c6f98993962283576147bd669e55c1df7009e8fc,-0xb7beaa17459be087cea2cecb246676cd7fc1dfd4949a3a8c2394,0x92a7ab8b1e27bff843cff562062875645f1ac581191a14fa65b4,-0x665068f3a47a0c7f83addac13195cfb97d26687dfc39da76895c,0x3e601ba7b359ab14a7955025418ce8729dc2c448d2c0ab02671c,-0x2130bb27a67c7d3baedc8c358ea64937eb36cd8a97fdc904b0f4,0xf61be703000c14f1efde66c298c455f8440b4fb5236d173c20d,-0x63082abcff44fd933465f6ba5a5f5885e70d3b4cbe8800a35f7,0x2274f23fd1eb87ca4bc216b5b5b10f6827bc85e9397dd76ad0f,-0xa4fc25b69aaf85b86a1da69b52baebe8e60bccbbad67693355,0x2a2f8d1dd6f0b235dcc2ed19fe852e3ac586db166ed0d2d85c,-0x9243547d57addecc65b0c0c9555af443898a40d187140a794,0x1a97d920bce80ef1e32ad9792ea285fa3978afa03bc7e16e4,-0x401f192edc26dc4377b7d3590d4fc9d52f98de9fe0c60a4c,0x7e3e2aad42bdf6b43a410eae43d3e5a3b2f532242b981da,-0xc73a8ba999f317268f41280515b8d2341503f8d0c17f6e,0xf64a793f2f4b8d9606f70021df85a6cb810935c1abc8e,-0xe7b148b9fc1be5a89da599401597fac56f2a70c2c53a,0x9fd330d4017d45e9363d4d8e1dfea5d8009e05939e8,-0x4d071da4a704fc5e58f376cdb0850cd5b0b68f6478,0x18502778acdb788b027589a4bc93d421cdd1747e8,-0x498b3df2634c97909f2d18751f1a25fdc0f1638,0x75190524d317b1fe0622e8d185013e6501d0d,-0x5056820a96d13b9e1dd175bc6387c9937b7,0x10bf523dd0cca25baa30074a3745813df,-0x7c182408154556bda2d455d1b7b85]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 21 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 47 indices rho q19 m19 19 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 47 indices rho q19 m19 19 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r20 : List ℤ := raw_ints% [0x2199ec04d8a5adc62ee58dec004bd557fc5d000000,0x2fabd39043c5999855e16a372ae23cf0f230400000,0x1fdb03a5590c1dcd4d4df2b907f7d84fac4e1b0000,0xd55a2cab021f374d752366b3466e8eaa5d8358000,0x3ec1ef8b87c64b26dfa8e2d23f1bfbfc4d08b2400,0xdcad7b35fa3db795b3fef25319ed780a45ecf000,0x259b6264923f86172ddb08ebd7a097a95db89fc0,0x5170e1efc6da66211a6047508e19fae76e1eb00,0x8e4cbf038b59b7ab90d59db893e88b7a492ab0,0xcaa3fbc53f7e26da37285fa68802cd8c13320,0xec8895a2b0899637852ba4268cd7f5504f64,0xe2c4c338ada393b5a4683767a6909d4d4e0,0xb24dbad3866676293adec1838e37dedfad,0x7263b077e0963a64f8793acee99fe8d2a,0x3b4f9c82769dca9fe4ed3021d67abbcf,0x187b04d1ff935540c21aafc24e21d74,0x7db9906cdde9c51b5e5ba0a02c24f,0x1e4201d2eac9a3e7811787cf541a,0x523845df40267c754491153fcd,0x8ca4829065d48b9042776ac8,0x71f66d62c9b031e017f114]
def m20 : List ℤ := raw_ints% [0x0,0x49e2445665e1889cf222dace23c1a36b34bdda13876e4400,-0x6e67aa608ea230dcd4828f21233aa613a0590443e2b537b00,0x4f609a6d7b81c13525e379ec5ad17c6830203e6cabbac4ad00,-0x248fc5911eb8615c3d7d8c4069e7f1d10860dd9e92e7c80f8c0,0xc1eb32496b0c9d9d8b95d60677d7122c0dd85d9cab3e2971340,-0x31458ef2a234af854253e52a9fc4aded0f04cfd638467cfca400,0x9faa144527f914d8ef30e70c895b728ae23650991796a029dd00,-0x1a770aa2a0261df105b955861bb24d184c33c1630fd19c38556e0,0x3a86beef60da8ec7ba27096e5d41cf2290e242466fdfa35a418a0,-0x6d699125345739d52f63beec781f51fd798d0dc2c67a74d17fb20,0xaead94c58f01e398c82edf9dc66db6259721cc523b565013d0e60,-0xeffadfcf8fd67d028e3e8a2a48226115430ea5dd56d34819cdb6c,0x11d517f84026bcdb8d704c73c8dceb43723dfabdf4d7f892285704,-0x126c3207e10a565d761b174989e0be07ff694ea28ae967b6bd6aa4,0x10956c3231194e6478d102c244bd6849abb37e0bbdad76d0cd464c,-0xd075c8f7e8cfa28cd06b3c412e13396ca4076d10166a7eeec0d7c,0x8f0541d6b335bfc7006ce8f645092621132eac7cf3fa14bca6b34,-0x55a895825ada78b7f6ea2325b8335fec40f35e3ea67b2bebe0334,0x2cba49854e938cccdc9b4389db92d02fd3039d32d80a13639b77c,-0x1450f0c8cfbc7d5a6a3c85e058b1e51397ecd626429fc2a9c6ceb,0x800594c6ab667409001f7281fd850ef2e21dd19b34914c7a2071,-0x2b87de1470bcee2b2906b9cfa24eade07e08d7fe31cf1afce159,0xcb58c0c92d8e527bc146d1a04228abbd7c11e7da9b384c44fa3,-0x32a10e51b6ea859455e581b5713fa9b2c54d29eb3218afaa1e4,0xaa8f2eebfef8625db63cfedb3f1d5583bc4ea793937816292c,-0x1e0eccaecc779aa5d49cb43e6c208af2b48770827f3c725edc,0x460dbf608fc0f119752dc48f1925a25a57b72342c350936f4,-0x84e3f5623328958158ef6ad552c4e2d2ffa4bca2bd9081d6,0xc954aa71bea4d1f2cf2cb5e4b8e9b8c880265ad1ca27ca2,-0xedece0eb24557b5549cab6bcfb352825d3a3181a8a9e02,0xd4e9dc639c5e66a623e068495bb8d2967887fda4d61f6,-0x8ae9b386a49469a13f3a6fc8401130a074571b45b128,0x3ee5c1ff8d3893d550d6d46850501a3a05f0cb077b8,-0x12814874b8a294bbb331576543ee39ad5abd971a88,0x33b1a4d5c58c71f823fafe260b17f633027ecb98,-0x4b312136878c27580a2d31d9d5c044234d1aab,0x2e87ccdc4c74699fba95173ab4d0c862faf1,-0x89e0c66176de8c7a8c2c7475c19edea49,0x37a8be5e071919f70f0834e8fd4ab3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 21 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 47 indices rho q20 m20 20 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 47 indices rho q20 m20 20 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r21 : List ℤ := raw_ints% [-0x591a67b46435933c616b854c37d158a01af95200000,-0x7e5697a429ac005a6723b18032610703ba910720000,-0x545e7027eda113a34a33f201cbb9024c43a29c98000,-0x234a9aae258b5b191a611756433218088e67e70b800,-0xa5f7ec36ebe99f171f0744e3ba7676c4673902dc00,-0x2471e12d1518b2bd753e9549f49a1cfa52e23d5e80,-0x6348479be410b56ce67b1c0df9c1fc4171859adc0,-0xd6ca9ba062c737835d37460b89fd8256cd7ec5c0,-0x176e51c70e328e671acce458169418fc053701a0,-0x2153c6158fa26486e536bb51231b7b7abb2b398,-0x26d9ea320ced08a7009f5c7ffca8c2a66dbc9c,-0x2531d05345ecca6db4fbf427c70ffdab72620,-0x1d33299c1f8c5228501b8368405d4b0108d4,-0x12b36a1ff7b2145ad2190f5124cbc3cba07,-0x9ad933cc34cdefa09cc86db566672e1ee,-0x3fc78247553bae2fe8fb8064ecd7ef19,-0x146c974e591c7f8b379589bf8f50794,-0x4e711885b4a46b3beb3809eb92be1,-0xd486e11cb934bdc02a2481eb312,-0x16a57d1e63f27e1fb156c7a887,-0x124823fa5d6e29fd3eebc61c]
def m21 : List ℤ := raw_ints% [0x0,-0x7cadd351cbec9688d89ad13bdc56c3c4e9006000f48a12c00,0xb8d1c75e3bbdd4285810361c725dbc97fead8ea73e91cdf900,-0x83c60924f2947cd721a03539559ca709866604d317bde767f00,0x3c2b6da58b2eb17e41588ebc6e3ee7648deb07f484a89558ec40,-0x13c3fe8d8391ddaa5f43bc14f5beac0fb6800f71c689a930fc3c0,0x4f98a4b447d090ec4b8afe21429215b25cfd212a9c5831ac0e100,-0xff639650b4f811754c04d344d8d85d34e79f769f3f5c056314200,0x29e539555a129ecf1da891b8a4f87079bfb9fa7ce612c96233c5e0,-0x5ba66535bca9250eaba4b6f7884ee4290751aed2cee8817bfcb9a0,0xa9657490a550cca716415f86e4daee96a21c3ac22cdd6f1eb49220,-0x10b3ac3e82bebd6a041c747129d2214f1164f8638a40d5639854f60,0x16a8b81362dc2ddfd169daa966fd0806f9d3d7112621745f72d25b4,-0x1a95ec57c359d1b6ca6f37c6f615040d0647fb5953c3b39ffe7865c,0x1b15b18a8b0f8a87080c50e97462814a35ea95246e38551c1d018bc,-0x180628f6dfd9fe4e74ff411458f91b211a286e002d5c099f92dfcd4,0x1294ee7331bbda4d1e19bf29d26239ac880e01ed76447513789b894,-0xc8a0c09d3328d29b4e9390ce1f289d0d23fc909f6a9d765693dffc,0x7610c8b2c86a2bf03bb1d978d095dc2da27578904be281d422d4bc,-0x3c815e4e82689a5633ccd9910d9506efe8e9180f3806a6bfa4e8d4,0x1af050d50911a62e0c9ce942375119e97181614d8456f74fadf9dd,-0xa62961b3d6ce9c90eba3ef8e89f4b73d3e906ad78bfa26d17c267,0x3737c5b6a7d8f0f34a3418e07b6a3018995c31fb3372487ec74ff,-0xfba7572927a0329e6eb547b0589b84fd1efb54f96da9708a5da5,0x3d029f123b35876486b4ef1fa8d12500c085407472f9dc8dcd5c,-0xc7b10abe7fd97e317d34da00672ad8d2f7669671b30f670aa94,0x221b61b9ee455d4c2d238b36e8f628cce7be74551971e5f92e4,-0x4cd28e937605fe1603a17b89685ba7ce64a558dd4e3f1faa4c,0x8c623424bd8a6f4563014bb226afc96211e4627f5df423cfa,-0xcc1e46625a0dd215b3d01341398e7e8c0bc41dcd2a88cece,0xe6835ecd552679922238f54b181fe30416a48b7bd50a3ee,-0xc42533aa382e5ab4a15c8c792dd21c3ff56f859d1ec85a,0x78fb41c62e7513c5e8e51d80d36a01ab3faad7cb7ac08,-0x336fcd4f810f6a6db4f981d5c6c78aa338293e2ad8d8,0xe191e6c766bb5064530958c7bc29d8669835b29048,-0x245a415e3efc4cf5266a9729cb69291675cbd6458,0x3048ef4edc39936ba22c2d9f8f4d4358dd6725d,-0x1af168a95fdbfd8567562eddc10d45aff28a7,0x46eb643cf55de4aa047170c26ecf5eb74f,-0x18f4eefaf4c64903c40b02060498855]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 21 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 47 indices rho q21 m21 21 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 47 indices rho q21 m21 21 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r22 : List ℤ := raw_ints% [0xe4b3a8bff6dc1fc28224d4603f2573cb87bf22600000,0x1441844b55c8dcaaac250cd0b449353bf4c37c4660000,0xd84d35d505fc9cca7c804179e0cd7b3ac0adfa6e8000,0x5a6b8393a08869ff8df7d594b1dd9f030c976798e800,0x1a8ed5040f2bf09b9a429642b28f91f99b6a00f3fc00,0x5d3cdf0c784be5a4ec6e70657824875e8062bc60780,0xfdc8f18318c40905de7a13c5787609d3c419fa74c0,0x2248cffd071089c8ff94073898a4541a04dcbce6c0,0x3bc7d6380443f7839c3a15200c81a3a23b409f720,0x54f0211f10d8448f03d0a20d13ae7e251cdf49f8,0x62e665c20a7a744fd20d721d1822062df54403c,0x5e8f9b537733a8c937c0287f681e170cc68d50,0x4a2187fbf81d6b7997be8a98d4779ed645cdc,0x2f673093ae64a0b17ebd23105c3ac8a04e28,0x187d777d20d45819471233c22eb4814db81,0xa116a7e6f047c3fe6d47f78888c0ac68a,0x337a5eb31d2c126f0ce82e2e53f742bf,0xc53fd2039bce75b4e89a3df2e6d37c,0x21508eecaab176713e03d0bf28cc3,0x38a25d168ffc0153e90ca4836ca,0x2d91d0dc058226e7768039c85]
def m22 : List ℤ := raw_ints% [0x0,0xd265549a081f3e06ed85411503d26a5c4930a2019ca8ffa400,-0x135769f335ec40cc814f7aec15c3bad4da9eaced7d7960b94300,0xdadbfbd8b77a98c3f3a11f7e03a875b99ad040bd503fbb7da500,-0x631776cf34e42ee05faedce6874550e165fd8ede73f280e001ac0,0x2043cfea1750c3fed8ffe03509a3a16dd6b33b3b28ae9cb8762940,-0x80bc6039f3ea3da96104db6d11328696985f2d5c2d1e2d9013b600,0x19914c4bc9e7dc01e6b6432e89c73a8e886bd68af2b3da7d8ef1300,-0x426e7816e5603e6d0e35d99daf3b25382d45ac5e5c90e072b84f060,0x8fc9feacfc48f52b60d04ef40838460e3fdae658eba8d79dafa5d20,-0x106d0d6ad24c277aed92fd13e1a75921bd73b3d9c076065a22f71ba0,0x199c42318c124de9ab9378827019def7013294ff4e1497fd65d7bbe0,-0x2251837f76002ef3782c80384b97bad10e5d0ce2bf52d09519ab822c,0x27be7f06ec0fa5b1994f020d45ef6350bec271a55a066787b41b9744,-0x27efcd47d61b8cdf490afdff5cdb28121e8a6c4c00c9f49d8c9ab4e4,0x22e95aa35a79dca5de26c349b067f236c167dce23cc7178eb0b14b0c,-0x1a96d4c30aa5878af7823d3042c941bc299194cdb4d09071cfa6cb1c,0x11a6a8bc2351561b589cd33e4b4789acd89c221c4b0e8fbef9fc4e14,-0xa35278923f2f4102ef0f667eebe2f01e9293a6881a58a1cd0cb4714,0x5227c977ed3fb0f2c18bf11e5357d8f023d090c067dbb5619acb81c,-0x23db9a93b2963cb19148f53f9513accfa25abbfd08d582eaa814a9b,0xd88369b5a05b10c9537e973378476e2be7094a9670e46a4f002c81,-0x4652815d839a912387682559f2c97768c5bc7c43eeaf26f2e2d1e9,0x138af7395ddf54c988ef60f7762b1744429317ea2e5d9b3eb5dad3,-0x49d0377c5e70e0092c472f31f17292b9c6ca74f77dfa4e7c9b3e4,0xeab7df643792c47f20ab723f7f17531b559431c9dd12ac22eb2c,-0x26d96ccad6a898d78ad767abf1f60e8671b0d1097ac660ff37dc,0x548d8e5beaec3e0b10c4895b8b114d7c8f343a5d20dbc1ecdf4,-0x94cebac60f6d6e5e1ae06c635c61268b3eaa45d360c8ea97b6,0xcf9819bd22528e19d52ffb1297dbfd220a78dca747ceef042,-0xdff45638b60f705369223c0b30b4741a3c5110a50858b9a2,0xb5205ba6877beca3c3951d25334fa9e8f9c09a5f1786fd6,-0x6990b2acacbfbc18363f978d509a99ed444805db504588,0x2a1f7e0a73bbbdd099f2811a9bfdf3049e60b990cbed8,-0xac00c271071a9dd9832b4f6a6359486c99b54de05a8,0x19930838ecd5d7e5beabc6b32d7da27df7b4a6abf8,-0x1f01ac1464a544cf2f99f8e33bb27ad77421d0db,0xf98d71081baa62cddf329b7532628b3462481,-0x2477214d1abc25576c7db6e4035012a2159,0xb2fd9ddd078d45f94ff6435dc68c963]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 21 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 47 indices rho q22 m22 22 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 47 indices rho q22 m22 22 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r23 : List ℤ := raw_ints% [-0x23a111d97d5c6ba1fca4e6a9892a116c87ab7b0f480000,-0x3276ecfe7c4f6cdff6b5824958b54d3018df0f859c8000,-0x21a9583dbe7de43b8e565ece49b1186653541d81d46000,-0xe101f1e95c9503cb14ef617967b13af9c863e80b9ee00,-0x420bae5efd0b8f63c2725765c230c8e73f79addbfef00,-0xe7b45b4929cf81c9a3a022a7fd17956a1d9281e02ca0,-0x27631ec6e986b5bbaa26082d71900754870a1ddfcbf0,-0x5510474ae8dd315609fb187b286a0113463821ddca0,-0x943025deaa0d8fe4bbd74b175e3599a25ceb979668,-0xd25791c39e01be13ee05b5d805bde1e1cbf631af2,-0xf4a783572fce161860a6a4fd351eff1de1c47ab7,-0xe9a561daa98338ae6d4d3cdb9d30e4eb063d865,-0xb6ee745bb03c4ef8ee0d053fe5a09b17cacc5d,-0x74cfa4451a3b7bfa6e958f76e247c9ce72bd1,-0x3c416c4cb5929f279632e87a55462f2ed11e,-0x18bab5a311880a0d619047a9741e8422bb9,-0x7e34500c09673dc1d6ddc5518c3669938,-0x1e29355f1272c06fb228b285d0fa3fcd,-0x51513321d47c091f1137605e5cc20f,-0x89e1b649afc21fd44de02ec73192,-0x6e9fb2c43b27eecdf342c10eaf]
def m23 : List ℤ := raw_ints% [0x0,-0x1630afec3edb4b8abb0d0ddd37673137bbb821162b85d2f64c00,0x20649aea5c216de9023f7fe7e7fe8a2e87679dffc5c8d338a1100,-0x16baa6b04ca4784f47528fd1fec96333b50c19adf5887e8314a700,0xa34ded36d578f49bb91a3b6a7932639bf3662a102e8c390e8e8240,-0x34b79710791ce167afab2ef4e3da33339b3ceee892a7270ae48d5c0,0xd073f287d0c1889b3981b31b60bfc6002351b1c69666d8b735f9700,-0x2902c2281c201ea436e0834066cbc4f0169bbdb60005fac2a9f0a400,0x6981d695ec0b0dd1c9893b758923ed84989be20052a93d478774ba60,-0xe2011f63326851f526703874a89546c252c5463024fa0b4131e1ff20,0x198983c8b1fd9ccac4521cfbebecbb52aabc8db0ca5260eadd1517ba0,-0x275c2c9298d8462c59a9f59ee145137d24dcf9fc8a2cf4b0ba731afe0,0x341b46b9ed14879508e36755edce0990a88f052d8aff6adc3d6b4d0f4,-0x3b9351c8aa6085ba0aa300a388b9bc388f305c4e08e9e86853e045c1c,0x3b0eb057e2a4af8b16d4d1974fde7fb13169c9a7fb2ce52d43033c47c,-0x32e3a9188be029398a9ba065f4d1a9083ecfe50872d4b3187f261ea14,0x262bc8dcb144447a634b12930aaa9180a67196868e7ef31ea3ed8b874,-0x18ee772ccb326fbd53c1d2ef2cb67aa560163f781a8e65e936bc50d9c,0xe2bb13bd53a9fe905b168b7561412e223c21e40a551d6fad660ef15c,-0x6ff6ac18adb31b75d51e9987e786982390c6708efd1c4e67768455b4,0x2fe92c2e4f3ac7429fd2db8649ebc39828f853aac984d88711299aad,-0x11b36db20fe6d841a1681b4ce99d52cb5e1cb67ec88a752acdd7d9d7,0x59e8be215cea06699a59f90520d1037cde8a02a76d54eaec300efef,-0x1860bae8caee951a2c5bd78b59d568906b4c5e8fe46f309524d68f5,0x59a6e8ead9d53c208921c60142bc0f374ed9021327bb40be59605c,-0x114f281d0a2020ae0303f63b453a1a6996fdf492aa05e032b16794,0x2c6a66bf5b7212c0e1e8becb7ca35fad7382b24c8702b0704b8e4,-0x5d6430247787e5824addf5b688ab710829b68cface9d3b52b84c,0x9e4288add841b74d1bef6f06ce7f8216cfc1ea9d18121d9861a,-0xd3c46a2e68234c5b3b67bb409647e9024b9c21a2db06b5282e,0xda2993c381f009741653d96bf405b9fc24b9aed4331fd254e,-0xa7a24b8f35dba9436f9b54db6c693fef9b153163f676097a,0x5c4729fa4aeb725b1120ff54d2dfd357b85cda1d6452f28,-0x228a51aa457113a8ad7f68a9026d701c44507795d89038,0x8342da529183ce6658c0f2f661307d3cbe8d3d40b3a8,-0x11ff75be68d573ffeabd0f217a96ba5d26382ea8b78,0x13e9177d7a6437695cb99954f220f0a5b8629ccad,-0x906cbfc1cd50e015295115f7640275d0163897,0x12be3d6a887b81eecf24d54c3b1ec2d661bf,-0x5035a2a06c8e4ecea4f214b7f5be5225]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 21 78 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 78 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 47 indices rho q23 m23 23 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 47 indices rho q23 m23 23 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r24 : List ℤ := raw_ints% [0x567e1fc749bfb99d9a98ae404c7acb69ecd6f8daad80000,0x7a72d8f63f2041aab161272affc1bbd96a76b54857d8000,0x51a29fe2e6367e2657cea6afc08dfbf4d5473839ecea000,0x2216166894e410d9d0964925d1ea3baf3f290d5efadaa00,0x9ffca665e4494464696a8786efd6db9fcc95460ef8f700,0x230e8363cbf5354e0273df9345d1610295b3e21532aee0,0x5f47c7ca85f232f77a8de2b60f8cd8441cb2414cb93b0,0xcd9ddcf3d359d5d95fcc50a24ad3b9781761deab4430,0x165e72876a385e3d500311fc174169ed23b3734f03d8,0x1fb8e67badded7f9f7785511f7ea24bc1a2c297270e,0x24dc50803b2d048aef46dcd9d5ad88c4759208127b,0x232a0abd7815421da6cd01704168955d3d4daa1cc,0x1b7fd2d32647a9a87f6e9bf2dabb99d271bdd6c2,0x118987da0f5c6b61e5035e711b5d33dd1d4cfca,0x9089f19a92216abbaad6335515599ac3751c1,0x3b3a827a805af90222424af331e3772834d0,0x12dc1c76c166fc113d2358586a6a457a8cd,0x47fb149ffa014dc94f730a4888312adec,0xc1aab52436ba703cad5e00b134071b4,0x147a0e6c8ef720b63fbdafa9773410,0x1062fe01f6bc9030e65be8724879]
def m24 : List ℤ := raw_ints% [0x0,0x257228deaa120f7a1ba607654d7e230e0cc6b7d56971d3ffa0400,-0x36438c9f6350e2630cda649ccccc6f6671081d2c0116646f8fcb00,0x25c8e1b089434e8f6754e5dace316f1cf7c9b4051cb87b743e7dd00,-0x10d4f8375cadd22052420a2be91fbdfc03e45ca8950c046a0aabecc0,0x56363b307f0a39f86552b74c9840f42c7ea0931cb6bab8e162c94f40,-0x151ea5f078bc1cca1ae3d37380d9c8692f313a4a62c7c65ca3fff1800,0x41df0bcd8922798a5cd67d1d45ce4a7cb4add900a06e900aea90bb900,-0xa7d52ce9da0bfbad059a7cb17bf1c3e396df1590ce0a8b82ddad0d5e0,0x163de9e492831fb2c408bd648f73127db721eb0db6af62575af54c45a0,-0x27c84fc1110d748fb7dffdb923dfff4bb12a52aaff72b0a8a38e260020,0x3ca081d961851fc5673eb6edda6f280fe2437d504d37bf8b32f19f1560,-0x4f4eed36909fa0a6258a7eae0ff010291a4b44473a6fc566ab9c68d4ec,0x5989ea80c54fbf47e0fe6f44a625a66bed9d3e46404a1365ab35dc9b84,-0x5794b14d997b76aff18eef98909a8fe2f85749b3978ec47100fe762324,0x4a677543bfe1514eeed91ed23733a51b64f38eae9aae82afd04c591bcc,-0x36f921a59edb6a42b43ae5777b705e4e968bb296a730be796d830cc7bc,0x235552af2ed75694e241ad3163db2ffa2e3d3942ae9e5e3e6d4abdddf4,-0x13bdc114ae85a62128b93e3895bdbf65bc2e75a14ff89abf5c80ecbff4,0x9923d8e5ed48af0ca6e505f4a0935b166d883f08f6162088ae99c8fbc,-0x4040f4723251f961dc57f04c0f0de9a61830022618a4fc69f9daea74b,0x173df0b952feb4596640fd7f549af06c50b647f87247a4f11b5fee591,-0x7364b1c326683fd696f6a7f894478aaa074dabe05497fea5392e0779,0x1e86b6f6baf156bb147efa10a7bc68a3cefd2e54fc7bf5fbd705ad03,-0x6d4e2f9f5421174b5443d5704897fbf3e01c1c8d571106ac8701fe4,0x147ff929e0b189939557f4849d70da970d150c8570d413c90135b2c,-0x32f6a2edcecbce1896faaab44cb239965cd92e9747eaf2d6154edc,0x678242d9c407993cf6d94f977b11e01b735269f1aa059dff46ef4,-0xa8da2af0f186c51f6f9ada9c5d133f541c76b21e731ef471bf96,0xd8a6f85e1cce47878fe9d420e850a107d728589e0dba6b039e2,-0xd50fcaed682805fe94245105d5f4551d73c7df1b57cfd2db42,0x9b7a451290efeba67329a3f37293ddf0133010473f1261fb6,-0x50cc5bc5ac04c2d8f2f7fc15920f363a96bd02eb763d54e8,0x1c5b3a053726c54c7c3557215e42a63265da2461c0f26f8,-0x643dcb3ffc2371a5d147af17b57bf87cbc78d7d5719c8,0xcab6971c2f1f6ade6c380b5c513a3c3ba12d63b1f58,-0xcc8da9dce42598f1afd6ff2e6c33725151b9a3a0b,0x538f92f28f65127874a4405d3410ad8e3d5d711,-0x9a16eb3b9f9d1fdcb1b67d067d8e284c7969,0x23eeeffee11a54151b3e1238a9af6c313]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 21 80 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 80 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 47 indices rho q24 m24 24 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 47 indices rho q24 m24 24 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [0x1062fe01f6bc9030e65be8724879,-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r25 : List ℤ := raw_ints% [-0xccfe8bff4917031c0266518a80db8273fb2dcaee47680000,-0x12215ac4b04c848c68f9bc3fda81e149397658557efc68000,-0xc14ddb671cbb35dcb906e0808c13caa997738272768a6000,-0x50abd2ff919b6cfb116090bbb8441a108bf7666c79d4c600,-0x17a6ce84f0761b74c3ea5546e1d3d4826a7be854fe372900,-0x52df082c930e0aaa082ba4bf3d468de8d33f1fe512c1020,-0xe1166a46180362a8fd69371305a8fc19c53c1a87c73c50,-0x1e565cd29b85f3deef9c68a45bfb73caa1983756eb8730,-0x34c3f92a47e6834e88256bfab62e12334e992667e5c98,-0x4ac4309941a3007f79beb6aba0c94911db0836bb6d42,-0x56cc538c093762299b215fa44c832477a4ba1eb09fd,-0x52b8d121a07c2e38661316e0e028b760d844148d0a,-0x409f07dedf8af217971e01f2fb6617b8bd5578775,-0x2929b2ea124559a3c0dfa74fc04ebc9f3c80dd7f,-0x152d2ebfcdae70cf09f39d67fe6eeb117aff6d4,-0x8aa5d29ed662725f4c9941bdca59d6eb51821,-0x2c14c22ded672d5220a8e1fc52f71a2c62ba,-0xa7f506fedff8b9bdbc6847b561122bb86f,-0x1c30ddd2fd5800472428aa821dd8049eb,-0x2f97beb69303226c452f8647e01add5,-0x25ffdcc2e1dd45df1807b7de7dcad]
def m25 : List ℤ := raw_ints% [0x0,-0x3f30a4f7befe7a1e0ea82c7af2c4db27b58f563821f015bf5e6c00,0x5aebe1015058428326694c8978393217bf1cbd5e633d797c42a6900,-0x3ed73b51f14030f4276b1783e1ab2fe96783aefab73709462ba48f00,0x1bc6c84d0d051495ac727bf0f09e878d0b34115d4ac24bc78c92aa840,-0x8d1cec8b25c26bfebb2e656229bbc5909f14f7a52e04fa568c07b97c0,0x22463f7404614142888397b1160d469ee591717737122123770377bd00,-0x69f1651a60b75fe1426ebbb25f4e71075e370f0a05ff92e06fbd5bd600,0x10b63c919308c078c55bb13c2dacb7cb05e10ee1f5d4943bc7c41edf2e0,-0x2315971a6d0e47cd2883a220d054376fc7e268cddd889f551c754e250a0,0x3e18e673a621d69e840094000d05c2455e8244483d81c6bb68e8aadd120,-0x5d970d7a59d81bc0e7418daaeaf125e3258ae2fff0f79f7f302c3df7460,0x79003013964f4f7f3fe5e776546e92a2cb94f61032f2eaf8654a4c1f034,-0x86ec21ff63e3b37b404a0e59066b447cacb50660d892d98ddc0c6adcddc,0x823e6290272b2647bd32a0a551d20cb9da0a81927d0bfa563c6212cac3c,-0x6d1bd28960517c5bbcfdd96b6dd5d7b693fa7a725c339eda61bb1612b54,0x4f6bab7f98a806a12ef52c72e068c3e6f8e14ddbfa45f69f4782c9f5d54,-0x323d89108d7ad73a24753a68c6cf611e5f157fa2f525c3d8f4a83997a3c,0x1b98a96f1b3439316bb741848f864105e39fc806cb8269d7c0f746164fc,-0xd234e115e59ed9bdb13333b1253015e1320771adf1f6b3ac19dc6caf94,0x567ca7c57641bcb2bc9e800d70f3a3cd4c71d0d3298be878436044d47d,-0x1ea1a910e6aa58d86a92cc806a8112e651d9fe45058726678039520c47,0x94a8d35e31c2a2f157ec25b0bc5421bb3af792d4c73b1c3df5f6eaddf,-0x265ea09feaff814e8d510b7adf6bf6feb9c97b5423a4bfbb617298545,0x85c4029d2db435ae11cd9e669ec4aa9f15a73b0521e1cceb1c7f415c,-0x185e195fea112e3ec4af743d080a9d7f6485392b5e2395e58994ee94,0x3aaecb34deed62d3ea8357b5cdca8bd36ad1f67125767890b5398e4,-0x731b140fc6942fa4e6e63123c2659e75da582d16dabde23304e44c,0xb4b62dbde60e03a6128a07626a8038d1a8f9b88401b966b34dd3a,-0xde44f5639b64602e10bd3e42fb533a5c7f6d1fced8c02b210b8e,0xd09629272ada9386ae8e6a304b317d201d50c4268ea881d40ae,-0x907e7ec88c6a51817c09d89d12f56e56d44e07a3d70fa5889a,0x46db8c5bf265befd3dcd64b9137731903ac90b639db807b48,-0x174e1bb49c9767f9ce92ab0cce2689244a35e30c6f363298,0x4c99ed690d7925f550816aef3dd752cc6221c04c111a08,-0x8ebb9e9a920cb5402f3d510bb240a6ccca06a7ea8398,0x83554e3b46ea5c3cecc0f7af7f3ea4bea8c6537bfd,-0x305538ecf89da53109d53eaff65dc524e6ab5787,0x4f25bb63638ce036e5398c77a6103fc9e832f,-0x1017eb849b6ebba71baca548e6ea5aa8f5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 21 82 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 82 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 47 indices rho q25 m25 25 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 47 indices rho q25 m25 25 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [-0x25ffdcc2e1dd45df1807b7de7dcad,0x1062fe01f6bc9030e65be8724879,-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r26 : List ℤ := raw_ints% [0x1db5db07fb62376f821c88769b9912350a4bae6d47e9880000,0x2a06848039b06ac86233199cc56bd442864ece1cde46788000,0x1bfdfb36c3db258253edefbd6a4b6b56462565110500c6e000,0xbad20274deb4070b274be0286294e2aa564e7d7589bc97e00,0x36be95987ee502d6b99d19316a261483b7d9f2e9930bec900,0xbfb52ac8618cfcf8f208744cc22efb309d30f336ca49c4a0,0x20862177e91d918a695ae0dbb4b5cc0d76672b58ec579ed0,0x46175bd10fed10b1fd250b54f23e7192979c8b384002010,0x79d28729da62e2b6d8555db929a21cb7238d85d313bf38,0xac7bd591a9c8d31b1cbfc77b7ad95d3051e1a53e75e0a,0xc812c45e4e2e62f6a16769bae155d5efff1a09c610e5,0xbe8128102cdec7a1f48befd680b3d0e5ff95f5fffac,0x94ac3ae28d5d360bfd41fd5de79c6a98cef0d5d60b,0x5e99e234a42a9c2f628d54ead578f4c21a4b282a0,0x309c7a74cf8be2a2ff3d4bfe512a3465bb6e43f7,0x13ddd26ab3d09a2762e9e1d780cc5b4a2964236,0x64eb588303cbd65e194354ff47c4ce6299db1,0x17feee730831cb5a8655163e587c3f4f4432,0x40554d371e8a08dd15922d42a4ed6fed74,0x6c687bff2600d313a4307a644a668312,0x566102531f67003d7533d216550f6c]
def m26 : List ℤ := raw_ints% [0x0,0x6aa21662124d6e12b8bbcb0f79ac31d30261e17eb94524b2ef56400,-0x98601db747cc8f86d1fdeda164a4dc73bf1af349fdc03b01b0791300,0x688eab234ba4329977b4baa0500e3fb3a7021928fe2ac8c48d1115500,-0x2dde0955da4012c3c381a1f3af2fce9946a590d399a41b68aeb958eec0,0xe72d362f139422375ef92757f6108277cc4ad53352e9c61f60cdf60540,-0x37aedf99a094ba8521e41851fcca0be7474c2db50790d6d1f880eb44a00,0xaa9d277893dc5970d242b50d6e7ca2e2f879bd87dc36bab71d7f8644f00,-0x1aaa6d5b1592ee0588ed27a16e0329c4e87a458f6654bff7c9436b0da760,0x377030a0ee4d585d764586c2d45d979e48249e54a5bb83e69ba79551b220,-0x611e2dbaa237bd6871ccc0e678b3f188cbbb87d5ad445a30dd36ecf788a0,0x90c97f84be79479e7ffd1ed78ef740935c5fbc09f600cc1cc1c1ff68bae0,-0xb90c0ac9198e23789586ccb037fe964ad73db2f900ba4fe967acf09993ac,0xcbd4694ee4805de1fb9390c8bf2fb8101cdeac3d61094a93a0258cada3c4,-0xc238a880f0947d6794345cdbf60749d1eb8d81afedb986cd370feaf1f564,0xa078268a682810781b84b18e0cad2b5a534650c04939596af07cf0a9788c,-0x731879360bd7b6eb79f54b561e5eec4af01dfe742297520864fb6f8d2b5c,0x47ab4643318c1f627ce84457759096eaf984d7ddf668b79fd9ce580712d4,-0x26b52fbfd0bd0916752ccba9e793f3e79ba6bc19fb4f872f7db61c1e25d4,0x1218cdafdd6d6e9efc722619a8124da0c708590ab36cda18f22a7a13a65c,-0x74d51966b46250bc78e150338fdb3a6c890b84f8f1d28a6f3e4cb6a52fb,0x2884ba60a3781115f38702eae950d07ff296ac32364c406e92a5c52bba1,-0xc03987858dfcf836fa6b387c43d2a4fff7b17d1d2f554d6abeb8f9f209,0x306826a8e2b7627d5d4b30fb5d766d145c15227949e540d20974f69633,-0xa44c785c88837814af8960864fd53aeb5d3f66b1cbb9ecf520d8e75e4,0x1d11856fb8519e4fd87e904e3b4932549d79ba50da9ce0aab1aa0292c,-0x43cdb2546faa593cda11caa784c4ff9d09b3c92261822557493d53dc,0x806ac74fa43056e87b96de5e014a02205e18d2ea7b1245eae3aa9f4,-0xc1fb9f10649b9845318ef7b053e3d2ae598b9ec5e7ed3fa5ebf976,0xe4a4fd69fcc78bfa443b1cd05762a96a23c7e500327d7825e5982,-0xccadfa6c7c3e19724e81188fcffb68e3bedf285b10e509f482e2,0x868b0a898dd87207dd32e6bb540b2c80bbb00ba5111b566f196,-0x3e3b2509cf6da38f4c13d550ee067c01d89f67c151732d4748,0x132c4960d8a38286e32e475a260da75af3077b46dfc016818,-0x3a91d6a9ac4b30e4f0eec9d08ae086286e1e40f0c534ee8,0x6484d033d70486b0f568ae77103d4c813f4862bf24db8,-0x54503ae3765e404669e8158b610f4a3f107d8c4863b,0x1bf2d955bba8638702c74d17832c06f979943a2a1,-0x28a3e04a95a617338e7a185b7312e9a2540279,0x734af1cffd662bca39dfa154d47fbde7c3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 21 84 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 84 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 47 indices rho q26 m26 26 5190410855112579734077440000 27=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 47 indices rho q26 m26 26 5190410855112579734077440000 27 19
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_26
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<27) : intPolyRF (mz e)=rfPoly (C (5190410855112579734077440000:ℚ))*rfX^27*(1-rfX)^19*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V7C28
