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
namespace CatalanCore.Li2.NVMod.FamilySource.U6C27
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,6,27,size⟩
def bases : List ℕ := [1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
def num : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0xc8282c5954c2678a80000,0x120847e668552e94f28000,0xc4370cc642445b60ee000,0x53bfd478c7bc651711600,0x192c70185a1edec5cab00,0x5aadca885da6d4adb820,0xfe0164abfb4ded2d8b0,0x236f9b28d14be8af9e0,0x401172fc5ce6550508,0x5ed7d76b1bf9e276a,0x73b93e3f81c36ca3,0x74c2bb45228e46d,0x616e44768d4509,0x430abbad16809,0x25ccd7d7500e,0x11481084472,0x64df2c55a,0x1caa141c,0x61cecf,0xeb91,0x165,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x1,-0x5,0xb,-0xb,0x8f,-0x743,0x244f,-0x54df1,0xbec9,-0xe28eb,0x19789,-0x7f5ad,0x32f12,-0x192c265,0x200db3,-0xa0447f,0xb194f,-0x1277f]
def rhoDenominators : List ℤ := raw_ints% [0x9c197dcc00,0x23ae0e20,0x356a60,0xe3e8,0x2700,0x514,0x78,0xd2,0x200,0x288,0x1fa4,0x1ef,0x14a0,0x1ad,0x7d2,0x3cf,0x30c00,0x8a20,0x8bda0,0x33198,0x3c900]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 6
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 28
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
def r0 : List ℤ := raw_ints% [0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x5b072308e98ec02cbc492dfcdc00,0xb1327c41b3c7087c47a38f0c47900,-0xa73b455f9dc61724271bd70402b800,0x65edc4d299cb9a86359005f11934840,-0x2d18224f30841a534f8fc5574b479800,0xf6e1ed1dbb775b9c114fc349d71dcdc0,-0x43fc305a40ea98f6ae14b4a6c8bd45900,0xf7a904d8a5204ec709f6c8614084288e0,-0x2f88408444ba8ca23aaf9b293bb00d2d80,0x7cd3963d4d380aaffedf2f69a8cbffefc0,-0x11b70f1098be6db9d4103e03473e98b4a00,0x2313e1d99479565d073a979b01fd5d86b44,-0x3cf8df8512abf2f4023ba5be7d1afabdcd0,0x5d8469ea5aa3b5e5de9c66e0797000778b8,-0x7f11e967de7c0c29abae87264ef94dd21d0,0x996c0f8bbf8ae45c19319ec8152b6515e68,-0xa4f3e550f4c6ea8f7120728cc7d942cfc50,0x9e25a058c0610df968fd52f42e4d759ca98,-0x874c6aa0df11a4717760d3842faff404b70,0x674ae48ce9987901c5570c3915a17ee348d,-0x46539ee44a4e791aa78e202d6f2d95d4374,0x2aa5ad5c1a9f962928f3626f53aa257734e,-0x16fd4054eaf6f1073cb0e70620186beac34,0xafc7470d963201884edabf5d507929eabd,-0x4a34866d70cb9dc9042c9609341f8b0b30,0x1b8c81b8111b31dec9f2e6ae9c875df518,-0x8f1be3b59116b45a11498312762c571b0,0x285a82f720d8b61259daed377363220ee,-0x9cc6a1032c0beda3f5fdbd1ea7355a28,0x206f6d7e7fe0adfbc0f3b5289787fbcc,-0x5a4704a806ca3846ba8e69d9dcc1b68,0xcfc098ea08abeaefcec609e223bdfa,-0x182ce8f501027cedb15dc0334dbe60,0x2362d6870582aaed3b3d08347fd60,-0x2726b2e27578474c3e33cc87c9c0,0x1ef46b3a36cabced3fce447e601,-0x100f0999808680ff0423d6cf34,0x4be353762efb153810b8dc9e,-0x9b88f8e075464f190731b4,0x460ad68db79e60554d01,-0x6fa1877983a5c400,0x2ca702fd67dbe800,-0xdf430ef3074b880,0x34883fc0b66c200,-0x8c15ff573bcb00,0xebef274f8d200,-0xbcbf52a60a80]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 21 37 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 37 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 48 indices rho q0 m0 0 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 48 indices rho q0 m0 0 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x999c0b1f0a20e44b7dbb7d9ab3400,-0x126f7d6deb428311d67f06dc0364300,0x11287613022fa817e717eab0f3754800,-0xa4f6d138462477a9daf2ba51c3422ec0,0x47edbc047ec54e5c63f9623adcb1d1c00,-0x183fc98d57290083b76aaecb4088119640,0x693ab992cb708fe590c9ca78eef2b12d00,-0x1796a379baff60870a6ee17aaf8428aab60,0x474a12ee4f10e90c83814ed31b69f5dd980,-0xb82dfc477ece79f86ddcf8356dfe00c46c0,0x19b41187f854b2ec85f646fb2bcdec741380,-0x32069a94b9810d993666ace998d5f9b30b5c,0x556da219869d82e5a912777ced3747889fb0,-0x80a919f0a298f8b8b22a3bbf0f2ce8134788,0xab920aa2277f996d06a1630cdc381e28c430,-0xcb2dd7b3dd63bb02a4e18a3ce0dc811f6868,0xd6202e4e06446fe692aa7d0f41327c5e4cf0,-0xc9178c6e133a32490bb0630864989c58a6c8,0xa865a1bb8e4fec08c5b0d13f89479ca158f0,-0x7dbd85d877d08874f39293d0cc0211ffed3b,0x53a8e672881510131be73bccef9b5d267dac,-0x3187c3f2ca56a61158eaebc2ff6b25c1fbc2,0x1a0a4a754154e477704568406be92d03e2cc,-0xc1f80a5cd82ec779beadf717149f5470f1b,0x4fabfaa28cbb731b7cbe2fd3c261842c7d0,-0x1cbd33813b4820ede10764ef2e72a6c4168,0x90d44b981f315bdd07b9c39d74ec49cf90,-0x278c52217aaafd357c1302dfcf8182f842,0x947e272f779845829d6319a443d5a4c18,-0x1d9f5d3f49431663fcedab673fcffd554,0x4f492035ea491ca09454556a26566398,-0xaee70a42f9054940591237bc2b45646,0x136fa93000518079a83aeaf40995f60,-0x1b0ad7e7e248cf88bb4f98b6ab3ac0,0x1c46b73aa82768c104865714345a0,-0x14f8e874827db3fdff717fd1d767,0xa1b307e4253992e3146161f8ec,-0x2bc276d8c35b1069040c78272,0x5091e7f059de0c62a5ffecc,-0x1facba54a8fe88827b1d7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 21 38 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 38 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 48 indices rho q1 m1 1 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 48 indices rho q1 m1 1 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x1033752c46117813f642c63f50e7c00,0x1eb2c870589c9596c9bd9e9490781100,-0x1c2f6ac2fc5574a39d47e795def961800,0x10b3e556029f5a59d47a72c83e23601e40,-0x72e18635962c27d54facab1ca659abc000,0x262bac283d178e79974e38fceea995d75c0,-0xa331be4e3bb8394d4e3ead856fa2ed73700,0x24074374b5783c507fd451eae8efc5e8e960,-0x6b3250cfd07e6b33ccc772608f1433583d80,0x1108a7278a33807b94aa55046176e36af2ac0,-0x2569d3463fa5bdc81c76e0dedfcb21d6fcf80,0x47982222c88d9f7ac530e95475b57b812ea04,-0x78264828f22dd69274c78da1eeaf5ccaa88d0,0xb1bc92a57208debe35c4340e0b99a88f84238,-0xe8ac08e4f3d2798f8a880e5acb6764f7dcc50,0x10e543deef8d4ea8031be7b03d301d7407ae08,-0x1175484a03216bec59be468bd9ba15c720bc50,0x1010736a0d0c5c48bedd2241c5ef1bbf9617d8,-0xd2bbf7193dcbcdd422166076c7b1b7fb86b50,0x99efae6cfeb400aa7462e123bb1e757a743fd,-0x641ba50c8e46fe7cf13284f9885721df0c274,0x39e01c2feeb80f3fae142234f2b097781ebae,-0x1dae6a99ed9ecfe124a6c50242ca8c1d11754,0xd76b6c836c8d001688a79ee86bd93c169fcd,-0x561a445ce8e6d9d8358b0d6b16ecdea37d30,0x1e2e27a23e3f08152062b09284389d34e218,-0x938dd4df634ab2ba979c99a2ff8d2792570,0x2704ec26dde79c41857d9fabd1709a29e8e,-0x8d95fe4c199a20e0e96f7c0f932b858b28,0x1b3b303593a86822a08582b7b4ba30f08c,-0x46136ad7186310963f0b7d2c612e63da8,0x9424a3cd0f3207104a45720acdee7a3a,-0xfb7003d50f9125b652c6efc31ad0860,0x14c5ba70925f3107fc9a1896d0a8f20,-0x14833c293a5abec15565a0be7b0b20,0xe42586863082c48f817464306231,-0x66017d2e4ac0a2c621989136e34,0x1942be7a83bfd3878792c278fe,-0x29bb0ffc7cac9c55c7d12454,0xe51243e056186d49d2f91]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 21 39 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 39 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 48 indices rho q2 m2 2 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 48 indices rho q2 m2 2 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x1b56d5bab63d7aa1af90ae8ad8871400,-0x33227e00ba664c189213c87ccd40fcb00,0x2e544adbecc362aecc654041dc407c4800,-0x1b15b18ae3adcd309b84e0c394229dde0c0,0xb7b7ee520e518a244ca5e73627db1dd0400,-0x3c2e46471eb16d7509bf3f0b55f3d1c81e40,0xfd933a77d7c75b757e0b7d942bc834434500,-0x3726dd2c3f45d855f2be23122ed80bf726ce0,0xa19992445bf0c778355bf3cc56cc35e09e380,-0x19471bb74356aa1faba93973cf8dce660d07c0,0x36a14dd89bf09edc5f359be8b555a6b0c83580,-0x66d0df7bad4179635e186c10deea7ee42aba9c,0xa99dc223768f4fc66b5f01b734ad47ad4566b0,-0xf685e3be8e353a08ceea7525b56f84cbc84008,0x13ce53f07207023c1f9fd248156009f78994b30,-0x169527aea324adbbf269081615a5a1b96afcd48,0x16e287c76fc14b2f47b333ad34f860c67334070,-0x14a33581d5ed7c622f4eae58d712eeaff341688,0x109200a27b92b1dedf87b5a6f0446aef841d270,-0xbd813d07806e055dfdfdcb2cdd52765d58e94b,0x787b9612496ec805b4c0c6eb45b3036b15db6c,-0x4407d6512a657c52c975358af8f7c6e72ccbe2,0x220a1bf23b3d195e5bba85aa3761c429e8c08c,-0xf0bf7e06a3fc70a81605e18e7881765467a8b,0x5da624fbdcec7a0eac1cb0600f628339641d0,-0x1fe64eaace7bf666422e3e299c25dd5902068,0x97502c208e549bbf08842e7409dd5e96f190,-0x26bfc6267ef2d46f5ade6b90420f745e7ba2,0x87e01b0b760974c3b9ca6ab14b0bfa2e198,-0x193131809a9062c4b39bba56ebd56ca9394,0x3e51435db75ebaeaaea86c2b7b5f54dd18,-0x7e36c5599bc2c23ec98b6d2ab1d460986,0xcc67ec8dfe819d0b59512ff7abbc0de0,-0x1008d5ed4a12ca73872a81dc00961000,0xef1714a08970a0f401e38076cdae20,-0x9ba1131ad29bddb89a23ecf9106b7,0x407d645e204615aa0487b87250ac,-0xe987c4480d1bb31ee5aec8a692,0x159c28519dec202f1fb8ee28c,-0x677c6381a85b1d8e30bcc7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 21 40 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 40 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 48 indices rho q3 m3 3 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 48 indices rho q3 m3 3 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x2e2288ab1387bef0d844268a4d63f1c00,0x5533ffbe567579dde6ab8f4203be066900,-0x4c33b782f03dcfe2105ddc44525ce9bd800,0x2bf6422912abbafdf9771d7b97041c15e440,-0x1262d6735bd195558af64025b1352fbcee800,0x5f086bb6d02b70645f24d4e550681d872ddc0,-0x18ac1fef6ce415827dcf984cd492cb01ad2f00,0x549ca146c693c1b6557f1e62eb8e853dab35e0,-0xf4398edd91d472a460860f6f0dba8298e73780,0x259df8cdcecc5293d966378ba21813013d09dc0,-0x50047b719d4d1804df2fb7dcf175f49610f8180,0x9427c20878e2cdb4c44b47a2cd62c22c1a7bac4,-0xf0550a8b2419217ce9f6fb7d12df950a85f9dd0,0x15749c2a8ac89d896615c396792a122f9c6fb5b8,-0x1b1702fecff0b0d5ea3082430b2de51fd094b150,0x1e51f22b13f53a95e64ca956f7d7eb4232731aa8,-0x1e2437e0f418ffef7a8cf2c0d0739d93f65f15d0,0x1aa547ebfbe5900f9117751aa667935ddee4e118,-0x14f4dcee2259b8a0d8274dfd520b9fc8bc98e2d0,0xea911093ca5d33ca6c78396a122d1664f63cbed,-0x91d37defd5f1cc1043d172c647e82969ccc17b4,0x506f85dd9462397fdba9183127ea103160ce28e,-0x2745bad012a08261e524c75256d611dcf5b6094,0x10eb5b92da7c106d2a4d6f8605a258cd8f089dd,-0x667e9e71763686f437e54f1a2601b4479f6930,0x21ee3c0b224503ff390c18fa6895e27dbdb118,-0x9c282f75050ccdf29faeb99bc637e545e0170,0x26b9c798c7a66bcb21a55faa40b9c2e0d7f2e,-0x83375ccb7df55e4eb7be18b02e618de017a8,0x1773115747b6737b72b853da5b2e15af2c4c,-0x37bf7ee3128a6a8b8047b36973b5dac7e28,0x6c237d35b7825d6329b9a3505fff0f037a,-0xa70aa41318cab7f0c93f61c28e5bc52e0,0xc6f6c0ba7152d02cc144aa321dba2ee0,-0xaedd5e77b19529ac7fcc5130c984fa0,0x6a7ce9351a7dc4ffe31f47911192e1,-0x28da4b0d678869899ceccd9b82574,0x870a81e80a78f9f40b054aac7de,-0xb301e5bd2a8209cdeeecfb394,0x2eba3347c9f498f00ec7321]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 21 41 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 41 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 48 indices rho q4 m4 4 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 48 indices rho q4 m4 4 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x4dda46a0b0f512366cf301096298a7f400,-0x8e03a9a07f409f03ab860ac4718d4051300,0x7d6a5c732a68ed328be95467dc511f0f0800,-0x476c4e8fee3bf6c21485255086fc1d822c2c0,0x1d7a3a6f719cbedabc4125fee0e73c0f845c00,-0x964da5682583dc3560f7fe3a6668dc18774640,0x267b20a036679be89bd866b07c80a86fff0ad00,-0x821722c900ce49279957b92c610f233dd517a60,0x172021cdace67a309228d277c2930b66453fc980,-0x3822861cde9623a22fe0bf1768b24ea4bcd480c0,0x758fcb0708da573442709dfb1215df7fa8229b80,-0xd6340a6d45bc9a734bd37d092f819559c48501dc,0x155c4643607cd4b383cd4b9f102dd6235cfdb61b0,-0x1dfe707e532056ba0dddcbd589eafa988c2b9b088,0x25350b604c1d394408ba7fd8c448363a1e5563e30,-0x28e39b638869a47ec4c201e74a996c7fefd745128,0x27e28c7aa7af4467f954c7ad6b7f0e2d5f808cef0,-0x229276eb1e6a5c0cb0beed7781d88d586cbc74c48,0x1aa3deeaadd0629010f1159a3592a25b0653978f0,-0x123e65365899a756178c73fcca50e2f51d2528b5b,0xb17b202741fb148cc863ae5f8711c3470a026a2c,-0x5fa5d490f794ededa561511a3dacee2a47ada202,0x2d9393544960a03e9c5c3965320ce4736df6954c,-0x1323b6a51d8c120106c152b15b2e687b0a9ed2fb,0x70dca9aab2fc848a93ebb7792b3b1e3acd055d0,-0x245066ea7839de33740d81a471d061456ac4368,0xa22822c92d4bb8d3b4e58de250bfda666de990,-0x26f120db7e8025e427456a9015ef36a69bfb02,0x7f7de86b37075ac174c89d12139c6fa055d18,-0x15f5302bc520ca8772ba2731981a3472e45d4,0x32287ede8f8b0a8e26364c5fd2d0e886e098,-0x5d27f973b0b59b723785a4f1f2a13aba5c6,0x89312d2e0db091dcebb1bca98527119b60,-0x9afd8b060b500d07d5e85344cf1c4a340,0x805ee494d950db9d5e88cf781afa1fa0,-0x491253ff97e42ae3f65a5e38e5b8c07,0x19ed03958fbd54330f938c1c21fd6c,-0x4e2409e4daa305acbfa1625378b2,0x5ca6a4da090eb691edc784794c,-0x1516adb9de9a62694c03c6b7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 21 42 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 42 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 48 indices rho q5 m5 5 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 48 indices rho q5 m5 5 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x8360572f2a9d8ebbd7da11bfd6619b6bc00,0xecc78a97b46fea8da9a190d3b1e0cf790100,-0xce8a6ee6b899c0c6267ea01b8a7a952ad1800,0x74255c8cb30efccf195f0c104fd9ded086ba40,-0x2f51710b8ffbff5cc8deb9e8fda513748a1b000,0xee15c0c5eb7790fda0cc01746838053127465c0,-0x3c20ea1b59da9131439b4b8943261732d0482700,0xc8711b8667760e11b0e38d6e6656aa289847c660,-0x231f0adeb24c8170402e65770217e17981c247980,0x53ff37998fc5e083fc3527fe7f7d27c96195588c0,-0xad3e0b7597aff71814ea3c28cfacfed9cdf983380,0x136b77402fd477ba53214648d28e8a7a85f487a384,-0x1e7c0133fe09c318c7713fb5faa498f2ac76a55ad0,0x2a1760d2b497433e849f3aaf522b5899016203a138,-0x335011aa8c66ac27a574c1b83eacb766d058dc0650,0x3761e9b84729a421b2f1ece64921462ebe448f5c48,-0x35055979aec39c23b0e44159958b916a62f05ee950,0x2d12c87001edc78079b798a0232862b81066c0e058,-0x22094b6d604a3dd2bc81d299b19d1ca5d09ec2aa50,0x16d27ef8d515c9df169c5d10ed441dd9e6b05029dd,-0xd92eff7a5aa8f614543257addd0f9623cd9feaef4,0x726025558d575311eed3cf10c1787e6bb3f701f6e,-0x353283b0dc50a31268577e26f815ac4e8d471a5d4,0x15c7446c9688a127c50abf37e1c31907b27b906ed,-0x7d0557ab124d01d88f4916b2436a4c335af5f130,0x27197bb2d3f8f99ca30efea818883cd8b071e418,-0xa9680f1af88a4ef577d8967abd13d6772c78d70,0x27652e517b4f51547153ff62a931cc311fc6bce,-0x7c9be00005c3235e464134872a9349ff4a0028,0x14ae12b23a7cb3498ab352f1b69a7dea205c0c,-0x2d6137c5a39091b4255adec7f2facc111d6a8,0x50ab7930c5c27dff5019364bc7e153f9b7ba,-0x7137cca8e84f79d6402d7f2c0b9a980bf60,0x793f65da6a26ee177d3293d2c37db43ca0,-0x5e9232733f450924408746a176233b420,0x324637f04212d1a81a7ecf49d4867991,-0x107acfbf485f32d647d9f3c54a376b4,0x2d3d9a7dbbfb2dddf33ddb44884be,-0x2ff0a7f11a9bcc840263fb91ed4,0x9835326e6bc4ea1f37d61fb1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 21 43 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 43 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 48 indices rho q6 m6 6 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 48 indices rho q6 m6 6 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m7 : List ℤ := raw_ints% [0x0,0xddb2931f97e9e0dcfc3ffdf3b9c4b645d400,-0x18ae6eff068bf84e9318d9e368dd758e231b00,0x15459c98a0a3b95bc7db8f659220520448ac800,-0xbd0bd0586dc97fd1405413e4d2f4672ee9654c0,0x4c0c96f9ca23574ef6338be9c707fce6bb413400,-0x179b4ee7a4218fc7aa8155c6b94dd57ced90f4e40,0x5e1ff0a01b2517cb0005dba496cdb8375697b5500,-0x1357d835ac4f955bd89f083e7961c978498719f3e0,0x3577af55bec085f8094c72391379b41b800ed40f80,-0x7e069e1920d35e8bfb38698268952bb55abfca41c0,0x1000d8a2386b12b42c69b12d26364a8529eae755180,-0x1c42dad2cc21faca2416a197b90169673bdafe5a11c,0x2ba893e4cafb849180c7d7d9b05d0245ef8b98a7cb0,-0x3b4a8d2c5acf70eb2e73ad02f82df96c6afbfde6908,0x470d2b6d2264fda5ae355c867331a7e5be129576130,-0x4b559aa3e1bdd2f0565395de0cab085a33220be3c08,0x46cd3ce4aca8d26f21d0c45bc1061628c80b79c1570,-0x3b0b14998dd8ebac2f5acb85f24ec46237054b1fc08,0x2bb39c88951d355eba206542571a0c8d146b319a370,-0x1cb2742114bba33e1efa560dfedaa29bb06c6d7a36b,0x10b2fde2ad2079c3cca259cf30987fb6288801a20ec,-0x8985d9f5d3355dae0eba00c493d33b1c7c6731e222,0x3e715daac294495e861a2169502e85da5d5053e60c,-0x18ec7ca9ea76478085b6f0024b29d715d4e1e0186b,0x8b4c776024172e5592a1fe77d0c9860a1614f39d0,-0x2a58c18003c1b8022c2e9ba64e625761fd5ab6268,0xb2064e6048913eed698fdaa266b0cafee9a71990,-0x28166612c2847680089d61e2bd5b6a5a8edb7662,0x7a7e629dd9c7253a1a69cf31cfdf44faff88898,-0x1395f4f1e23c2b3ad41fb180c214f63a9d9e414,0x2946eaf8de8d141e6c2974c80410a89bfdcc18,-0x46358708b2db825c332ffb274f456b6011306,0x5ddce4ed7b9c8b26135bf44457fb2d5fc0e0,-0x5f3bafe4f5b98ee38edf5d7bba218ebf880,0x45e6df150a9603742a6ab1773040154520,-0x22ac99353640bca47308c6357164b1757,0xa7d98edceaa8ca4ce2004980e38b22c,-0x1a344fa0cb548a0765be3e84608cd2,0x18cc252bd452f266d2a027817c0c,-0x44a0f0ca6fdec40b32b33bfa7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 21 44 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 44 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 48 indices rho q7 m7 7 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 48 indices rho q7 m7 7 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0xc8282c5954c2678a80000,-0x120847e668552e94f28000,-0xc4370cc642445b60ee000,-0x53bfd478c7bc651711600,-0x192c70185a1edec5cab00,-0x5aadca885da6d4adb820,-0xfe0164abfb4ded2d8b0,-0x236f9b28d14be8af9e0,-0x401172fc5ce6550508,-0x5ed7d76b1bf963e6a,-0x73b93e3f819caa23,-0x74c2bb451d5ba5d,-0x616e447625b1e9,-0x430abba7dc031,-0x25ccd7a900e6,-0x11480f632d9,-0x64dedc040,-0x1ca91735,-0x61ac5b,-0xe87a,-0x13b]
def m8 : List ℤ := raw_ints% [0x0,-0x1761d5845505aab74e9abfc8b497bf395d5c00,0x292d1ccc05a2f8313fcfc10f03412dd7f73d900,-0x23130b3420c8f63e5e55270bef67c7627a325800,0x133fb2dbb9dd051563db05e5a44390adf560c2040,-0x7a5f4edb1e57fdc6e16655909366b6c5dec9f3800,0x2581adbe744b94d5c4d20b76fececdf89b5fcb8dc0,-0x939b13ab327d4d7dba0f1c2dbf9e11b64ab9fa5f00,0x1dedbd88f44f186471fd9ac5eefea9ca845f49dfae0,-0x5196f8592ffde2079519a25006f28c732e1f9b72b80,0xbd95aca5c1ac26ce34e92ffe8b5df5a52e6d715cbc0,-0x17b8d972c31ebfccb78eb79ccbeb75172c2df1953580,0x294255e1e7440c76ac9e316291338589a310811e6444,-0x3ebe01c00b767b6200a2bcc53e7955a998c1613247d0,0x53d47d8cb999cfda9de19d50c91d4d14fd24201b04b8,-0x62c60287ca31ca0f99fb232210c78d2fd86c7155ab50,0x66e7d258264be387b875b0be3cee4c7507b556190ae8,-0x5ef722679a64f95eeca6840e319909ab39bf20ff48d0,0x4db41e0096780208266c1624c000c513305b7e7f4d98,-0x386282693e3b68000dba99adfb038510ee241dd1d5d0,0x2444509b543c8219a2fc2b2438b1a83e824a38ca6dcd,-0x14a6ca5d6040a2dd768d82e29d61c5314bc27f92a234,0xa63f14505b920d420f509a60d2d8e1169949a93424e,-0x49b34099af4841695e4a4ee75f7b61c194ba0d2af14,0x1caf2213e37331c1579332eddb08dca9c47048816fd,-0x9c17e132be9149eeffc3759ebe96da54cfe76a0130,0x2e2097818207d16c03af7601e370ed0c54a6d96b18,-0xbc2847aa774c579a13fe769e522b27ac98a3a7170,0x29064ec2b5a6b1dc62831ed89471041ba1ab5e46e,-0x7916c483b2973d5c9710471477ce667a083930a8,0x12a6750a68cae8d7e6a8f7f198f607b4bea3dfcc,-0x25bd6729d39f2235a67445e1a9dbbf1187ae728,0x3d669da618c7a935e05eba7c060bc9dc61cefa,-0x4e289fcb2babef7ab006ce2e289c1dedda7e0,0x4b1612e9ea0102d8de5774a4a21d68a27060,-0x33d417764b7e70c3b3ae38acf1d56b18ca0,0x17f80b2cac17dd13ddc0020fef232e8641,-0x6afd172ab28bb9818ce3d760eb6b33f4,0xf2ef5de49569aba0411e64c6516f9e,-0xcd283710e0c793d85c8b2740fe14,0x1eee12d8543328b9da5459c541]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 21 46 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 46 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 48 indices rho q8 m8 8 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 48 indices rho q8 m8 8 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x13b,0x1]
def r9 : List ℤ := raw_ints% [0xf6496e91eb4b35676b80000,0x1623adf5bccb842acdbb8000,0xf04f38398d04c986f5b2000,0x6648d363d7828c080173200,0x1ea5ee197e1c3fb84955300,0x6e011134459a59c564e460,0x132e0da37185e758c2e870,0x2a9c52868d8d1962e9df0,0x4c9e7ec9f93aac1236f8,0x70b27ee1059e1457a66,0x8877722172ebe06e27,0x8870088a196b467fc,0x709682898dfe37b6,0x4c6750a6985512a,0x2a5261db71c109,0x12e6ded833760,0x6ad68c2a2e5,0x1cf758fe34,0x5bb06180,0xc02f10,0xcecd]
def m9 : List ℤ := raw_ints% [0x0,0x2775184f4f79901554a523a2b0c012b0cd8b400,-0x44b71b047eb8033bac020a0421389f7f9eb7e300,0x39ddfdf06ce69043e48aa2b51323623645adc8800,-0x1f630614e4182ae811eac51b75df4d0ccf8b9516c0,0xc525177f7c36994e825bccef1db4a17a2897cecc00,-0x3badc0771a8d60f2ed8f6c9dcfd327e5f1efa1c3640,0xe7e1d6f61b3b17bb2b700b160ad83c8e91fb6b0bd00,-0x2e66e39e50c6fb8fab2fdfc6c658f21254edb7cc7960,0x7ccb0952c5dbe9e3af877325ed2b8c0b6226cb524580,-0x11df0e125f85c91ced35d74b793564a156b55f8c84ac0,0x2343d0de06051db341739d5ff75575da9941dc4b43780,-0x3c6caa49638d4575a1751af40ec7f6ec3a2f94e7ab85c,0x5a7979f8c86ddb54fda688e3468e69ca29a364bbd07b0,-0x76f54862db929c96def073c6430b41a5ecca2dfb0e988,0x89d8fb747bb355e86c15678447d252e4b7c6efd37b430,-0x8d262aaa96e0fa906c8e2e293ca02ecce525cd09895e8,0x7fee884f0ae3305facbe6be873e46a35de1c2ee85c7f0,-0x66bace6c998d76fdfbdfbc87e26a95dae0504b89925c8,0x4918c72c8193678e0d273793271a21a06f0c6666109f0,-0x2e0fa31bc65f2e239b78167e84529cdd4e3e9e3cb597b,0x19aba5148a182e96864932709ca9ebd417168752bc3ac,-0xca0814ba134f7eda26fb3dd9d7a9c13b8edafaea2c42,0x57753720b1b0fea8eaa7583bb6e1e822035246e352cc,-0x213199675e918995004dfe9e2b9f645f10b1debceadb,0xafe3924488807c62c0b521b195cec8055b0b4c225d0,-0x32870f71729c5248ba0377373e4d27ca8533ca57d68,0xc7fb61084319e2bce072aa3a16f279f74cd83d3190,-0x2a377e9b8404b4bb7128fed5b7a60cb96615dcddc2,0x7859f3ce91475eb87519d550351bf4f2848641c18,-0x11da502e23b0e5b4b94ad7e2352b33a4ddc962e54,0x22adae344093817f98e6d502fb7ca6e69131bf98,-0x35f29551b708732f320c8fe1a2deed00c0b9946,0x415af3d76887276c2a03fbf6c4a21183960260,-0x3b6a7d44007c6e393fc08c89a76f9e9480fc0,0x268a452a8f775a6571cc22891549c18c96a0,-0x109a6f39b2c25c159420916530ceb3470a7,0x44463a30c76b0cc94adc33b6ec71762ec,-0x8cccccd2b17456d4c43a2fcd97f02f2,0x6a0b93c67e3c061bdc4000c82eacc,-0xdef02e0cf6c883c7daec8a9797]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 21 48 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 48 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 48 indices rho q9 m9 9 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 48 indices rho q9 m9 9 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0xcecd,-0x13b,0x1]
def r10 : List ℤ := raw_ints% [-0xa1b09bdb65bd4efe5ce880000,-0xe81b5e6125762fed1f2788000,-0x9d1f317d68495a027f46de000,-0x42b71e5e1be4866bfc7e77e00,-0x13efa1f5f82d7f6f857b7bd00,-0x4756174352ad79c094b0dea0,-0xc650750cbd974ca53d04090,-0x1b6d4e5fe10250911996ff0,-0x31179357bdfeeb45f2d978,-0x47d3ba4311b4d094aa4ea,-0x5670937fe2ec49a3ae21,-0x55cabb7f80fc6ae3322,-0x462dbfdb9705f91e39,-0x2f1eea74f8d69557f,-0x19c2a5adb0510e0c,-0xb50ade1f40ca41,-0x3e957d8b33db2,-0x107a679dff87,-0x320b642f8f,-0x629aef9d,-0x6034d1]
def m10 : List ℤ := raw_ints% [0x0,-0x42959905d61d2323fed6ac228a441f8a5adafc00,0x72b4d4876c4ca61e9ccb0dc6831ed4a085c64f100,-0x5f870f94c8964a5e452a7b0f8f2c0279f104ad9800,0x3339449bc85d47c99564482b3de92acc7667b4f9640,-0x13df9c36a18fd84b9ae9d6b884dc318b454bb36e0000,0x5f188c22eac2d988aec791486d73f2333ae544f755c0,-0x16ce8a071604c841da67611c181953884db4fc5bcd700,0x48165567e6e4d634d1184cced5005a41aee1bdb75b360,-0xbf4f944ffb54c38698ee97ebd3c7fd63a5e537a826d80,0x1b0602984246dcfa8c7fa469d3508c5d7f4b559d1726c0,-0x34929da849389cd9c30a6fda1e6371746c4d8124d3c780,0x58c418b5041a402dddf465fc0318dff77e7596199c1d04,-0x82e6c20ceaab4cd08d3981dc1774a1ba4414e95e1184d0,0xa969d5aa0bf0563d2bdcb892625f5e178d9f04592f6038,-0xc11e0aab9504207cb26d384f1bd279b487d0b3a6cca050,0xc264a0ee1729927e2c5cb93e4f85280e277cc96d0afe88,-0xad14dd9f090bcf001a4f26c03b55afd9a8766b15481c50,0x886d5929448aed23112af82f061668e1263b3d8e5d98d8,-0x5f34fee6cf362a94fa04ba63c2c9928f238c0a88b53550,0x3ac91c55be119d3b28e876301d07edf204fca76829ffbd,-0x2011ebf9f629589c10ba4974ae3a2ce89cb2d02caf1974,0xf6cab99ef2908d10423b885a1326b050e78729c466b2e,-0x68557bbb915ab027dd58b45deb05140e50363edb27c54,0x269e9d7ab6e407adc75ef8ff5e5a7e7f830ad4ef39a0d,-0xc746cca7cd3ffe20c2da9a31a154cb0fe9424fe18930,0x37a6ab9549f784b2a9cfc32b69add24429c9851b2618,-0xd5b62ebbc65a03e75ac7498413535eb3897db97cd70,0x2bada22179cd52c266a90637151fa74dd7411ce990e,-0x784000b1e2709ce8c73134a01ac65d82ededd05928,0x112d2dac50e6e1059134b03bb608702779f40fb78c,-0x2004e7f1dee9f4eb311bf412ec3841ec06121efa8,0x2f9c6567c9f0dd5bf079622dad729baa6255213a,-0x36de48352a473c6ded2eb74e0726be527a31460,0x2f2d6420b0b76ddfbdd08d36b69164c0313a20,-0x1cbca7d58c4e52a7c2d0555ee22ff6e0f2920,0xb85e5c90daf81704f2b83fef9c3ce1d00f1,-0x2b9d14021b0bdbd56f617248116afae534,0x519ec80a5b24ae3f66617b250ab2687e,-0x36cb59ad877fedf4b086d306e89154,0x646391ecba349f75ca5da27f3d1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 21 50 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 50 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 48 indices rho q10 m10 10 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 48 indices rho q10 m10 10 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x6034d1,0xcecd,-0x13b,0x1]
def r11 : List ℤ := raw_ints% [0x4b385c334e230c83aeaa1280000,0x6bcb85406e9e21dec530d728000,0x48d504cb81677e10ca6b52c6000,0x1edc17d2927d89e3fb3c15d1600,0x933247ed025dedc341227c1d00,0x20d4e728c9a81222939f821520,0x5aff8bf3df31d553d6b75c910,0xc8ad953e3b5b63f72a673f50,0x165cee123ee9217a21d54b98,0x209308d8a73de6d11ecdc12,0x27001bce80463056722829,0x267a13e2f3b50c104f2dc,0x1f40c7e56ae3980cfd37,0x14ceff4d1160b7ea520,0xb42aec1826ae1ddef,0x4e26c95f0015fb06,0x1a97d26d5c89c39,0x6dc59a4bcdd2a,0x144753dde378,0x267b9595d2,0x238eb7d8]
def m11 : List ℤ := raw_ints% [0x0,0x705c7239d9512b4cbe0a427a4952f539795189400,-0xbf88e3ea43414d67c5b3062a3f3cdaf3c5e4a56b00,0x9dc9eae79d90205479087b495ed329dace924084800,-0x53ab812d3aff5c9c69748296f6a306403e60500f88c0,0x20173c75489e8ff67d89d191f1163ee5d186f2c4c2400,-0x97bf9438274462a843c0acf03d904df0016b8dc90fe40,0x23f3b01428b90e686c39ea87dbb9e472543d1985b0e500,-0x703666096be6615d621fcdb2095bd12d2ca0f61d07aae0,0x125f206d8a27a42b168e44bb2e17f4957bea419463b2b80,-0x28f7367bfc6ff68919a8ba4bad32df36249b42937bb5bc0,0x4e97e7d3700e9612bb56afc13916c4def1299f8deab4d80,-0x82cc2e3a17bfb9069f6fced57b53c4b6c6d062827a8279c,0xbe041b3162908c13aaa09dee24dacc5dce33cd57b6542b0,-0xf21f5781d3c1cd0083d26a2f0618451b6f933c9710bb208,0x10f917c481ebb2938da6482a1de96c6aae550b7f0dde3730,-0x10ccae67687f3fbc8a06a9fa1fb4dbf2825cd23c650f26c8,0xeb27207083b4414f5e2e135691ac00cb20c960b9df75670,-0xb5fa9c3be46e9d5f60a12db0267bd5d91b34905246af988,0x7c93b354d684457bba15d1edeb0385262e362c07b69ac70,-0x4b626786824148d5ff8e9e5ef53b3f3fba327637a15c58b,0x2843521c1cf2e15902d4717639a317fe32447180687226c,-0x12f0029957f660840df3e1f7d3b430f4ccd55a5710de062,0x7d1ce7031a43c223b6bb8a06fe5c3324319b4ac3529b8c,-0x2d2b6ae9b84802c6e354bf3b4fdee666daa27ae28a2a4b,0xe2fa806d3846b81d37e99ae9bd3c06dcd27ced7f039d0,-0x3d9f48608c01ca73f1d2b4ad1485c99509a58ff98f468,0xe599e9b0dc78841f8a2aecf0761ed06ef4d01ce23190,-0x2d6d8a453d5bd4da049d66aa7972e5e020a172900122,0x78c3c25e9763c3077b48da9bcaf21e66a96498bf798,-0x109b74e7608634163ee360f0e523a7ac75d8c35a494,0x1db38fcb490424087169f543383cc391a2493d3b18,-0x2a32e4152047c8a32bcc62654e969d97cc3690086,0x2e3d7875dcc59786acf32b2dab2fefb3d7a60fe0,-0x2594bfca4284f257eb35262bec29dc3f8121900,0x157b5c2fb2f438218b2aff5263f4623e621420,-0x802dfa4a5e95464f13b307d3744d9c2d4ff7,0x1be2a8ca8145784bc5707a12fe225d61fac,-0x2f51f820bfcf5217ed1d655129812fb12,0x1c4d4d96e9ddd0f941bcbab99fb858c,-0x2d2fc0551b80792fda6c15f93e87]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 21 52 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 52 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 48 indices rho q11 m11 11 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 48 indices rho q11 m11 11 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r12 : List ℤ := raw_ints% [-0x1bcd141669bcdef3da5e5e5c00000,-0x27c7bd9c13f016a57b6df64f40000,-0x1ad51eabd92dfcedd8883713a8000,-0xb5915945d89c1845c9a20cf83000,-0x3603ff5b0e1b502d3bc9c5103200,-0xc051dedcdd9c1b13c1300761e00,-0x213a7d801e4a6d455e55cea8f60,-0x49104055f775f239b8ecac2bf0,-0x81d6cd3925f1555ead65db770,-0xbc693684f696fd96f494bbd8,-0xe09a6d0bb4fbf2ba9095276,-0xdc7b5bb243aa99d2ce7ecf,-0xb20c34007d1fec884bbbc,-0x75bcb43aa9eea9ff3961,-0x3f32452ab6b4e2ae8b0,-0x1b251b83f8ea416041,-0x92052b5015bfdeea,-0x251be85e9a05f67,-0x6b9739c719a7e,-0xc70d2bb85e0,-0xb1a70ca66]
def m12 : List ℤ := raw_ints% [0x0,-0xbd9c00c19eb8f91180b1502e5bbbfdd0fcb9979c00,0x13fe9942ca3ce20dfccec34a595eb0a3750af9724900,-0x104c6fa35947b0224463b7e8714042fdd7175ea76d800,0x88c8cdc3c75c01be413473540239531760f190c4e9c40,-0x33e08cf16e2608dc52bf42e4c4d626d7407d0332260800,0xf27dc72e05c129a08ca2ace97e42b25c2abeecaa74bdc0,-0x38c4c5692599d32fced879447f07c6892018d9902a18f00,0xaf0356e45824a765c53a8b5bb2ed94d143bca0c09d9cfe0,-0x1c4a4aca7f3a6d168e78035acd32ce03b48683b4f0ec3f80,0x3e4152136bc80e10f545173022401656db4ba09ca7d0d9c0,-0x75d095cd5b19cec8146b7539108785c059915eddf23a6980,0xc14eef3b8c1de844c08c021a36a082068b8126752d1d6dc4,-0x114b85f6bffea7c6b79594134d4f044519eff3e1c791c91d0,0x15b3d9bb2248a988c319cd488740689675e24171cc14a33b8,-0x17f4e45c1ecb047e644fe35b847d9a274be674f6b5885e550,0x17520e081ccaa270ccf272bdc0ccdbbc8b3fdf90453844f28,-0x140cefb1e6cd1ba05ae6a8e94809d00fea8bacf2370bf63d0,0xf3cb64350adec0043bffc44e77bcab75e057f02d28fe9218,-0xa3bed3e131d3a059ec65d4a3f162416d22a1e0c5ffa468d0,0x611fd5ca0af74acfda1fb7d843e05d700641d61aac0167ad,-0x32cb52a0e7f370992693eeab41f8d86fede190400b4174b4,0x175dd65b63bb6e76631df785a979d664eeab18f8630b3a0e,-0x96cb34ebe0e82415c828e318253272b4449cce9a1accd94,0x351a85e821e531037e0e10b02bc0c2a832a4920c23f701d,-0x103e1540e4f4e7f04d80d022774d6782f1348a5cf8a0930,0x44973bddf6cd81dce84801988196874845e5629d3cb518,-0xf7f439d5399201aeeb23793e520a0db5ab9fd7e97e170,0x2f7d4206ec21b6f2679afda76f0314f3de6f57a8679ae,-0x79e2936884c585588c779eb5757de72f99c517c439a8,0x10222bd2a8970ac4c12d541dc3ecea6821891ce5634c,-0x1baccf596efb7e3508f24a716a81da5525b1e4df028,0x258e4562ec068ec188169aac5702ea7bcd64c8467a,-0x271c53a1028712e460eed3a80214109d5090884e0,0x1e0744394f9e3aa5d5a1e7a8050006223e0e69e0,-0x1018b7c0192ef08a51b69099ad2340c3d5529a0,0x5941d04572e4ae21d5dd0f0958c5b918151a1,-0x11d7da61084769288e532844ad4449c5ea74,0x1b6fa54f502bcd7ff8d220f0c2af7e4f5e,-0xe9cdbd23eb90934df1fd36e6d7f1894,0x1454bc7ffb16d20737df476323b61]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 21 54 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 54 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 48 indices rho q12 m12 12 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 48 indices rho q12 m12 12 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r13 : List ℤ := raw_ints% [0x8ae662c2a910b6efe08c08a2f00000,0xc67b0ed3a87bf297785748cbdf0000,0x85ad9d96c1c7b4cfce87d0e1b94000,0x3870f643cb120d57ab5479dd304400,0x10c2956321dc041ed2a2940ee1f200,0x3b8d14eccb04a0a1b5293d9706ac0,0xa43f9822ebf7ec2e13a0d3871820,0x1683a1fdb15fbe087586499fbfe0,0x27e4db07941f6b04016f2ac2540,0x39b3b29ac47795ccda501fa0cc,0x44880431192b235a408512b1a,0x42fd2d773e83dd47592fb2f8,0x35d51b59fa0786cffe41cc7,0x236567d3258c6850f1d1da,0x12df80772c4edad15b833,0x80af5f62c08270250bc,0x2adb04b52b2f92459b,0xac3f99012e223c3e,0x1ec3e77eb175d13,0x37e1be73cab48,0x30b0c8eba5e]
def m13 : List ℤ := raw_ints% [0x0,0x13ff74146bbd8244d892b374e3acd3c50aa792fd7400,-0x2167c59d77a2dbaa2c6ad837ca731b16ec29ca70db300,0x1af3a0dafe4366c58a6a644aada541e0c420dbd74e0800,-0xdfcd9581447b406b8caf48351e7c05af6078a15f022ac0,0x53f4d63fa70328957d68886f5b8f8e43f5439e0c06f3c00,-0x184085a5c8722d920c157281a85a59ea26eda2bf4384a640,0x59c96368a8bca37b944a26457e6860dea65b245dd4f5cd00,-0x1117bef3a5cefca8334430f05e51ab1a93e7f5fb08ae52860,0x2ba8a847640c89052651a9ce1a4d508b99953c762902e4180,-0x5ed6ea5fd0e4cde96c0e76637b48a5c6479ae73b11d8534c0,0xb115d5a96d90847b82ed3b9d917c4f6e60e48c4c4b53b1380,-0x11e89060b44888ba4ad8bce8838b16be01f1877707483bcedc,0x194457cfeb333e1901c0e7b2f9ccfc5bd71a6c2b127c932db0,-0x1f3b342cb8b60f16e2fc463ea299548fc5b86e7ec67db14288,0x21efdeb976a7553212d4b2bf4b781142f8d001647a95e5ea30,-0x207f76c96355ee4c3d654c8d7f25b041ffef5ecd09d40076a8,0x1b772973a49b04d2bf55b2b5c08234ceb393cd38685bada0f0,-0x1480083843cfaf43b989d59607976099fd614d02e199a0e748,0xd82fc28ba81dbff19f487b7c456f1e4797f15fc22bc9baaf0,-0x7db6167fa23ca5802ef3eccf85cc5b491b0f996a331387f9b,0x406298d8cc0a03993d1541a524cd13b36711a8d51619dbd2c,-0x1cf8e77a1f5d444fb7f3b056088f8577ef10616f9c05b5e82,0xb6a706eae06c15da64d8c1d816cf6e43638786f101ad004c,-0x3ebf473f3a16ef87bc04a429df0797a37fd3e04c4d4336bb,0x12b11babb9f0a46bd7172b62455a9b448caf8cc3dc4f35d0,-0x4cbcb793b90f0990989a8e519050af14e476fa9ebaea768,0x10d216425d5572069302ac1c1035097a9abd7c725c35990,-0x31e42bf1b4ae712a95e67aedda7bcb23b69f537a4cb082,0x7b9c21be7654ef5a8fc3d10f7ce11c28dd2224ebd9b18,-0xfbedc22463e3cc6d62d4ce1a0fcc5967920f6053c6d4,0x19e5fbc8ea497847c2ec95cb2db4fc287b09f9da3e98,-0x218e2afc22c5338b538f28df004e30b2cc5df1dd0c6,0x2131f0bd31912c3175c7367e83095e102da9f0c960,-0x181014a6a9ba796925f30028933faac628e0a8440,0xc167ff9b3b23325898eea4a29aa47ec19d6dda0,-0x3e3e6532cf78edc8b36526f8f1d6867be1ed47,0xb6cd740db45648cd046c03fdc2cdf144e86c,-0xfe8556ab0e349fdac8954c7a5d31329532,0x78ab73114cde8a00ba96206bd19a0c4c,-0x924e27f5d9af62d6c0b345f87a477]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 21 56 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 56 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 48 indices rho q13 m13 13 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 48 indices rho q13 m13 13 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r14 : List ℤ := raw_ints% [-0x2611c106de864106385cb6fa5db00000,-0x36552ed874241db425100fcd3f1b0000,-0x248b572ec0b8ad599a1eef571c574000,-0xf681fd617152f7b4ea56def63c8d400,-0x491465d418644d58616cb091b148600,-0x10330b49dbb6ba4446c5d91e26ee9c0,-0x2c96d9e18f2e0550ff56679b0b05e0,-0x619260a00036a89395ddb374d6820,-0xac749b71f3217095c2ad39afe910,-0xf8ba987a382a7741d8726d557ac,-0x12676ab0465fca3ea3e38fab10e,-0x11eca45e4127556f56a91fe6ec,-0xe582245acec9d1fa89d63056,-0x962fd79f48130c8df94a087,-0x4fa2c7a64d956a700bbf4a,-0x21b7a2ceac30b04ea3da9,-0xb248af391b28b718a50,-0x2c5fee702f610574ad,-0x7d65831d70dc19c4,-0xe09f5136d47c2b,-0xc04c9bcd39ce]
def m14 : List ℤ := raw_ints% [0x0,-0x21bf13e275cfcbd42d778ed54033a55c81fac80bb3c00,0x37d3965475b883c157e2f0b2ed8ba15bb356568e71e100,-0x2c97a09f05f1a3ec0e467b3275b07ef72c479384e7e1800,0x16e7b2e452f6c380e90a2dec84a6debfe48de487092ab240,-0x88054963412443338ee8781f645621198d65088232e55000,0x26dc5326cf9cd1025f4d3d8dc4ef57214ad30aa31f4b0c5c0,-0x8e3d4d3fa0d3c10cb958d40ad1b497ff8c5c7a6870c0e8700,0x1ac2a8cca1b9fb187021e29fa82822d531cbd10efca4523060,-0x43855e5bd2ef703ba8688ced8ce3134c40c09056ad85f62180,0x90d348eebb4a0254f88aede1e1c3d91854803bd024fc3624c0,-0x10ae115219aeae498f0ccff3fe986a6f8d79afd143e4da09b80,0x1a9f3d160688314ed4358a250d3fb3fec58241cd8ec03d9f684,-0x25077829616f62ecac3660d46333f60244c916e9a92f6f26ed0,0x2d184ba257b571a79b4dc34040e2b273bc7d920ac6ccc1cff38,-0x303f6a78b209a1372a1f25c457b76f77ff1b7fd416c715e7a50,0x2d7583c8fa6d2912c8f9bf70baed02f849ce37ee2bebcee54c8,-0x25c5f1946be0d86bad766ad4704ceb275a70c084b3359cb7f50,0x1bb257337d0919a66754996ad365292e9b80739d239a31c0958,-0x11eab905c6ceebedd589a2662f67e62fee32f4e0e6d7fb55050,0xa3731917dc4c8d35ee9dc7b65220e22998f29dc8383684ed9d,-0x51fe71cff5acd538194287209a0eb280f6b23c1abaa81af3f4,0x241853d69a92a68591e6e65a1e890e4b16fd0e4adbfef14eee,-0xde52d4d51866a6b7adcacb3bd92ed2ffd696f695398d462d4,0x4a826b3d895088f4cde21b7869ee4b4f08bc1468480fff92d,-0x159e2a600990b67a3976dedeac7c2637f7aeba9898a8b4130,0x56477ccff9d33c7964ba7736cc534089b009f6b14b5db818,-0x1258ef0199bc21cb3ec4618dc921667f45c45eb36f356d70,0x34ab280ba3514e3724d20ff725ee22936ba467436b3f64e,-0x7df24f45e5e28c16fef44e4d45df9aef17920e4657d228,0xf6f7dc3f5c274f5f4a2f227383b9eb217bf74e10a630c,-0x18562e2f68556316b811e3f048242824b4603284ce8a8,0x1e1822059ae0c8b67e2bc27254e675ff15f3a29b16ba,-0x1c446051ce27f9402c195862626faa033f9d5575960,0x1355b3cf45fe64bd20e760791030215f27f802cfa0,-0x9189b4879aa1fabd4117ad747f667d60a0646e20,0x2b76811b5bccd9937a0878130e01052a1bfa051,-0x751e4b76970649f6505f57c544e1b0dfa03b4,0x939119c14aa444a7cd418ae4c85d746043e,-0x3e415fe8ca6c8a7db5bf4191aa1a7d3d4,0x41c70b4ce2adaa76a93ebd683b2bf1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 21 58 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 58 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 48 indices rho q14 m14 14 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 48 indices rho q14 m14 14 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r15 : List ℤ := raw_ints% [0x965a0700f24e936cc53d42e5a7f300000,0xd65899a9804c551cbed094d5bfbf30000,0x8ffeae69966c19ff71510f15df0bd4000,0x3ca039d306c86d3c96fad0a41388e7400,0x11f25a983f843e0f41155fee35fdbc600,0x3f8c34511078120c3f86dda88854c3c0,0xae9a03377c3ec62a04597e0726aa3e0,0x17d4e1738f75847b3bcb7cb62ccec60,0x2a071c5f55a43a965bceafeea36c50,0x3c76f9a5e1455c5abbaffec3c683c,0x4761e69466d31a62da2077235e7e,0x454d92a2adc14fc848fe91263a8,0x37433702dabef040beec21a752,0x2403fa7919b3e9b282d0a87e8,0x1301f438efb64f2755b6e8bd,0x8010bd234600b81122b672,0x2a0dee16b290049739ac3,0xa6398115b757250e038,0x1d1871bbe4a57e0ce5,0x338dbb4c3271bdea,0x2b8b840e5d201b]
def m15 : List ℤ := raw_ints% [0x0,0x38f2718e26cea7f60cb9c107dc57270c1b573193bf5400,-0x5d525211f7e29e13cd52c067b5b6e236e6736596602bb00,0x49d1a53646e3592d7965f316c10f215fa5e50425c2ddc800,-0x2589a40c7382bfbfd02eb1b52cca069062fbb829339f57cc0,0xdc9b9ee9ca8799a783653e7a8c7ab643a911a8eed2c1a1400,-0x3e5a2446bcc510ff2dcfa4969149cb63b61dcd8aa5e1062e40,0xe1b1ccfa42c74d24064fc5af08a959504cbb87c8e8ba917500,-0x29f945327f801ebb743f8f7d070de4a3eec4b3b11d5b25591e0,0x68a53efa8e7580996e0c75c3c1791064f837a0eb2a70c6a0780,-0xddadb1d48bda717a9a609f6e6910995d9f952293986305d95c0,0x19340bef71aee2146fd22cc1231cfd0611baf6ba393cbdf20980,-0x27b01eab4669da5a5af2dea8185183fa8d0b9289dc9ce4fe8e1c,0x366f239511543e8732ccf501dd785c1e1298c52213c6f3d5c8b0,-0x4153fee702fd039e680b64a3576e7fd01caf97468af0ec1c1b08,0x44d5c7494ef77c28423784b26012003dcca9174c6e0f4ae9cd30,-0x3fd3c02c902016ea05e6f8776d7be95078bfda5a4c0ea10fcd88,0x342768783b19ea71855e165f65313f8a3b428d9db2eed5cc4770,-0x2592e1b8875da923aa1075fff02bd041fe8eaaec3e4acfdddf08,0x17dc42aee04c4f588c2be61b5355898c4f0af203e9911046a570,-0xd576734681918f1d6398a605618acf5b22e1e9e81a29918dfab,0x68e5c481cbec1c8900814750ead8eaee6aee1919256608dd3ec,-0x2d2e29ef9b1c96dc29dd3773e0cc1454bef56d0d7382f9d06a2,0x10fe86441dbd0fca2be955f78921b916e8333501b3b104bc10c,-0x58e7ef8249d0d92d4a1f1238c0b1441eca07e5369ae01ef02b,0x191fb8817a6c02ee64bf0ab499954957814da73103e44959d0,-0x617af759b7aa73768e19d5418d5ba54fbb3f0e15e49867668,0x141bedcb327e117f87ef6db38040170f0786cf89df678e990,-0x37dcc31b09e5b86d85ff776c5748fd120218a4b4f15b3be2,0x80e920f201da70bd06554ccc8fa3aebb4c390e326650698,-0xf3265897b3dd2aff8e62171b5d6906f2aba77c9bc21514,0x16f5f0dfa3d53b903316e9074bf120e830d406fa74ca18,-0x1b16751e1af40bc2bbc83908e2c00c6bd090ac6985206,0x182562aee91569ea424eeb7c65302e77fd5d0b14cee0,-0xf934e23aaf141f9f978b8ed1d00205ca23ea874180,0x6db982b7bb705d79b35f3c5e3dcf43afc2d979320,-0x1e6284be07478dab2a42cf9e24135cc4b75b4097,0x4b1297757cbc75e8f31c99038abfdd50c57d2c,-0x558cd84200e432a1c2b69f9a5f262205f152,0x201b2553f22fb1508d8a1e543a9c993f0c,-0x1d8fe67236efcd6219579010f44b967]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 21 60 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 60 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 48 indices rho q15 m15 15 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 48 indices rho q15 m15 15 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r16 : List ℤ := raw_ints% [-0x220bd483079ddbc7975b376dc2bb9b80000,-0x307d23f95a7d19e49c57a6dff4606638000,-0x2089d5a6f840b25c14eb6a2b067739ea000,-0xdaede5dda0dc2c37f7ecfa0403c6f01200,-0x40b8eb774b8527c5602da5e26669979500,-0xe4d767f0eb9810a0865e9cff8691aa560,-0x273be66c73f2948acc125bb77aaee16d0,-0x55874ed6bd4aabb4181c2ac80bd9b6c0,-0x9688abf3136927a0b31c614ccb39b78,-0xd817f879ce2369478411472979fbde,-0xfe7bf211b85e7f0f21ee6922b6cf5,-0xf663901fa99bdc8858b641535901,-0xc3dc5773e035e43f236d2ba044b,-0x7f3237f17d5b2a321f3e3a71a1,-0x42dc25288fe8e0d3e59c2a992,-0x1c0668dc1880e2aa68208f49,-0x92769d5fbc02151dd55a0c,-0x23f51a18223ead52c0431,-0x63f7272292a450ccf9d,-0xaf94a8316f9b9eb66,-0x92bd3dbd56c07bd]
def m16 : List ℤ := raw_ints% [0x0,-0x60191f9fe17cbb6f357975bd43d311e46e2323a952ddc00,0x9c0a799fea4eb2556921cd4ce288e8dc65977f278249b900,-0x7a440e73c5b310c740398a0ddc10b807197a011ce06935800,0x3d911646903c01af536192541f3e90dc79efcf16655a495840,-0x1662c8b004e842cf13c65758c9343f586928c812027c671d800,0x642cef80901690e5ba7c50478c75750046f32af6d1c5c506dc0,-0x166ad1f807995415ea8a73c427d16175e0a566b20d142389bf00,0x41f4b101b84a0e06c540b19bcb7cb56715525dd8afa8d7e3b4e0,-0xa284a5d8403096f6ab769792b4af97993aaa40d952e090a39380,0x1541a17da9c0e8830b95e8587a30d875b53adfcd9c2d9858047c0,-0x262dfc640bc7d3523882f59014e749f37650ffbc0a5063605dd80,0x3b550da1d1dc0cc579802829cdcc90efaf6bb3da0e9e333665744,-0x5043330bf1da1f4ce949cf9b639794f16b496e54c561f30481bd0,0x5ef28fe872d72dda407dc8ce3184ff10fac5df1c90229afe142b8,-0x628c3b98db699bff171a4c0cef7a2e8e6fe383985b6b143635f50,0x59f247dee4ed8853f16d5806236c4f517a2ec4777f988e442a768,-0x4849cb33835fe0ae6ff405bdff95d89bb8234230f2da8d2f14ed0,0x332e06a4b8e016712f16ed2e50d9bdedb606b32173692e8b54e98,-0x1fe8dcc3d169ed790eef15ef5f64719b5dc1f0bb93b00d2f7cbd0,0x117ff68c58a3ef415d3b2a39cc14338c8003bca0ae77f380f198d,-0x86cd9f9d7328201fb8814234769168471803edad59e43f205734,0x38d036b2d20474e2e5ae800088ee35a1c65c93aeeb8a4f4849ce,-0x14e1ce76f9d2c5639ea31cf35ec16940c3f01a9c3f43c2fffc14,0x6a96a48148423cf519d81c667141b968f2324e726170758153d,-0x1d5688fe56821b2530ca58e4c5cbd20656e35e979e2146ff130,0x6ea8d7a13c4be8a7a6894954010d3bee175b3d8e395d94cf18,-0x1624b832760b677a4a6dd603e7275d6eb007ccb9595a773170,0x3b85706d2de05b50cf2b5948f0ee87e03d5b34f5b3accfeee,-0x8486bacc8b684c859f87684dcfb7d33f81270165ca8b22a8,0xf06372b7ea60569b5f6c7230c60296a3091a509bf2a36cc,-0x15befd2d4aaf4a25ea29984da216a234a26ec46c6b4d928,0x18773f0996ad447ead571fae87ac010997fbf3a340a9fa,-0x14afe217d62d8e5a3e8500ef8eda44d74c68c9a7d71e0,0xc93bb70f0d7feac77f4713b9fcd106904f1fda0bb60,-0x52de792bc7fcf25f249a3ac865ce7c8848ed1fd6a0,0x1543c0b17abb3174400d72a4f5dac08303cc55501,-0x302428081146b22d4c2fded65b7ace17d4e70f4,0x31975a4b8ca933453ab97a0f3f3bdd7f8671e,-0x108d1906808ce2f1fa1137c5ef9da9a0314,0xd47fe71685ba48579d6e97f65665581]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 21 62 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 62 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 48 indices rho q16 m16 16 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 48 indices rho q16 m16 16 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r17 : List ℤ := raw_ints% [0x72badf394c58778e87dec6a4f493ac080000,0xa3401a348ef50a5d6ca8be6c6818ded08000,0x6d709f0027afc999b99617bb7ed24ab7e000,0x2df8b2a4f632eb1c8770bfc462400c789e00,0xd9305e8fccbb24800076d5c247966272d00,0x2fee96f751a98c3489591abf871a8323aa0,0x834b19348ba93a527974bf8875b6bc2490,0x11dc1a07daa1106f5fa649653799018390,0x1f60dafbf07556f54efbd7f001b6e3828,0x2cf4aa5582a3fa064faf3a94d0db63ca,0x34d3b1a44ad15f461ce406e6f89ad79,0x33059f99562eb0307b030743403284,0x2872aff1833b05532f6cfbea7dda4,0x1a2fe8a92bf8617225483484095a,0xdb7a0f2d2414828a6e6ad40ab5,0x5ba1d780d391f2261dd4efc98,0x1dcb6f84407930bbeb789a29,0x746c61c8efe1387a1842a0,0x141b253b4ee829a0553a2,0x230fadba343c83e1170,0x1d0d3ee79a5ecdf2b]
def m17 : List ℤ := raw_ints% [0x0,0xa22a655dcc827c4baa3cf6af62742e3179db4c2dbbd63400,-0x104faf5d4726541409f370c724a1a0307849564a083dc68300,0xca9cfba4fd1687ea5488825a3a314de3937f9bc7dd17278800,-0x650e59a824b3efff5e99d79e0c0c864e66dc5ce907c049dfec0,0x2461fbed6f3c0dee92af86a87543b996fa00718abd635b4eac00,-0xa1267952e5ad6f661c41f4b8fa4f817ab284174d71160bac9640,0x23ae3f5a0514218e1af9f5f9e6ce5844421fca0e58ade0265dd00,-0x67d3715510e825d557c8c6e00e264218b1337e4fdcbec89d88760,0xfce9234b341cc4cdcd315034ac03e768b0d60a0f74334a894fd80,-0x20afa839a04a0f070714687a131820a836e3664b4a21710da63ec0,0x39fb939229af38ec72b345aafb7b0bd98be8abcd1ec06d4782af80,-0x58f1a55ca2140bc337d33b08a24d71dfc56078a2955628e6c0455c,0x76b2e033012884dcba0f87dadc878152ac9076f3b9da4f7c0813b0,-0x8a700e3228d1a68a701915ab4660f4796a69c365d1dbe0abbebb88,0x8d913bd317e2e7c09dd74c6717ee813ffd4a9d572fda832f34e030,-0x7f36531ba94b4613e9f77ac0685029d35bc80d02e514fd2cc73368,0x6493a7cf755fc27cb2a5c73ea3804748312884d928d735c744e9f0,-0x45fd8f6dda731f7a9564119f2b695643ac8064a86983f0df1b50c8,0x2ad9e8b38fea83969803b5e0ef8ec4e8bd82c0823bf207f9ab3bf0,-0x170d92f8237890b3b1eb2f3a422c55e9f1b502f92c54f8a512fdbb,0xae003734cf8679057e6344a100399c624fa0981002f88be18a6ac,-0x47c3d76cacfb29a71b30d32aa287209b18f0a554e9c0ade0d38c2,0x19c709dc6a4253acf3c5a3bbe5cb49abc4a4410fdc8c34ec81dcc,-0x8061f74dfc52350f1650d44dab9d0d4e34f6d3c7bf905f4fb69b,0x226b44a70f798398cef48b70ac8d19e9a6a3382a3cc86c10e5d0,-0x7e344c05a31c7f04769a7260ce4ca7823a08a7d8a2ff7f14168,0x187ec4bedbd498ed6f5950843aa62b2fb14e6973b3aaaed2190,-0x3fb3cf9ba06722efdf7d63ff19d734da2693c874df77c27342,0x88d367e878c9afdc2b5b0356ca23fc5af59f47c58a4cc3a18,-0xee9d9fb6629752af247da1bbefd0400ee7bfaf78736c0f54,0x14ac061f0723746bf7de00f0984b6ca78c8c402a71e4dd98,-0x162baf4d0f5c6846a82def9dfc75183895106aff63e8c46,0x11c600d24430e8359b735de5feb926eb87e11f11eac060,-0xa2dc308173742d376959171da8db887550c39c40c0c0,0x3eb001bc8d0a5a8a71e800a5472513227339f31d4a0,-0xee56c78177ed7355a0147ca0f8def66b9455a01e7,0x1ee1b13a64c7e83d1aada15d4e5c3cb156549dec,-0x1cbe1fae4ea3a8dfbbd9130d5e028413e72f72,0x887730fd1454c44b4f94fb98f859a7fddcc,-0x5f6f7a383a7fff62b28fbb9e34366d57]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 21 64 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 64 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 48 indices rho q17 m17 17 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 48 indices rho q17 m17 17 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r18 : List ℤ := raw_ints% [-0x16b6e83f2ed3453073ea9e740cd0709c380000,-0x204b3511eb2840c457025cb5a50a0c96338000,-0x15a1235ac01a797aa8197eb1e1b54a2acf2000,-0x9139fc4b2a92f37af7519fce769dd2d70d200,-0x2ad5d7157e8f9afa984635a308440040d1b00,-0x97130ae4c48d4c06bf2607a9b8c203eaa060,-0x19d4637445e76386e41e88682442a2397af0,-0x3822eda62e3b8551f32aab0d20d14c5f410,-0x62789071fe6d7a347c8669de6df2084cc8,-0x8cd4dfb67b4ae79a771db0913802fbca6,-0xa52ae3f91c551e61cd8d04576bddd897,-0x9f2deb0de39e52264c790ded1cba3d6,-0x7de2e522c77fac1bd57cb926e93cff,-0x51484484bb391eabd891fc17072df,-0x2a72a99962942c323fd96e4a9b00,-0x11a94b7bc14d9001e080846c271,-0x5b862ac35315aa51ea5598f86,-0x16408fd0d0447d3da26d2a8b,-0x3d2b6df86bb569db4fcb25,-0x6a07803ecfb4d2018cb9,-0x573cafec609b152587]
def m18 : List ℤ := raw_ints% [0x0,-0x111a78b0e491c31bfaf46e047f6240df37da2108d2cf977c00,0x1b49a94cb366b9b1fd91ba841c042bb7c88996ea55d83efd100,-0x14fee8f1692685d756a18954a3ca9aeb3ea42b2c3fc3fd869800,0xa6001c08de1ad6ace19719ec9f61c63ef4b528eb3a56e0b40e40,-0x3b30f1bd3626dd7a3ca2f122fea302d97927e020ee005bb81a000,0x103911e409fad05156606cf2725ebfd2fc255ee2127ebe6790b5c0,-0x38e09ad24c98382dcc56ee7f6edb97ae66611f13da3ada02e93700,0xa3ba414acbd94db5ce173110d60a5507a23271b97e508de6283d60,-0x18a5e0ae81162995f97ef4ade7d46a90f845d8e6a78002973041580,0x325fe026e5de5a2f320db9d77b959a3e37361d7c0e6c4bba42682c0,-0x58467c77f4cca1c8937fd17be5b8aab257bf10328e75818fa2daf80,0x85b1efadbfd2c5faacfaa0dbcec46658a8e2bdc0fe09f205d343004,-0xb00e3cba55c467e8931a030633e5fc8d4b90f4491916593477a98d0,0xca7bc15c1fa30df5482834d4684925cad2dc5830981f2db3fd87e38,-0xcc0c6edb10e102e28d2557763c42375601836eec90c430b20319450,0xb48e937e7664b260eb81b679e2d10b6ee6302478ead47e91ea11f08,-0x8c757cc7eaa3cee256971da21f9a01dd6fcfc46d584624dc538b250,0x6016f40771f48678bffd62769f57a5a81bc9d36758099048add31d8,-0x39c775ae9e941ccf0ba1451ed959b4acadd19cf48ecdbc921d4bb50,0x1e7f1947e1159410322f2bd1031b7cb9a2cd1f97d9e7fe2e378b37d,-0xe19249322907c6b4cee7be7ccc53b0a53d3ba90a60b5c53c6c5e74,0x5b0de3743511f617bbfa91e523c1a21e6c1f5f61ea683232b7caae,-0x1ff6dca58e6e235021e6bba52c86764136121db8b84223dc3e5954,0x9b56a244d4a0e0fbdb5c5813aa46843b1405c4c63494a4075244d,-0x289082c7c21bbc2427b3589c08c25210773a3018d66ee17f0d930,0x909600f9b73dc8b7dc990481c81a67afa08c83d545a8e06b9a18,-0x1b37b6388566322637ebedc2dd246441707512de90582bb5ed70,0x44790029d35d80f2f7d79c8ce6a00d0cddfc88908591c5f038e,-0x8dd9ada21f6d8bce73307fb69f8a23578397293f28f4ee2b28,0xedc6fbf5f89c00cb762abb5430b0bb23bf074eadba7ae5e8c,-0x13b88d586f45e219387b2ad95e74d71107dd8c20bac67c1a8,0x1427758aec2845a703280c3211a8bf5f79d6b0d1a575583a,-0xf4f976b929baf16d9d0acf6295b1f1be2d313e0d13ae60,0x8414db6398ff5d4566aa265f371b4ea114317b431fd20,-0x2f7dc9d4cc7a14558d73c175f671a41983f0dcc34320,0xa71a283642f7b86c4c83b79e4b94f898551de917b1,-0x13d0b7ff08df377c701726ab02f61de7846f47234,0x10a7fe029c74f6d3e1bbca1fcb7f01ed9c257fe,-0x464bd5d8b5cb8a420da2a38d1704f760e654,0x2ad8ac7ae59953d5aaea7703e83c84811]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 21 66 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 66 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 48 indices rho q18 m18 18 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 48 indices rho q18 m18 18 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r19 : List ℤ := raw_ints% [0x44351a0907a033885ad345f6ef25581e8980000,0x60e5fdc37dd64b80478f4483b38e20b7c298000,0x40d885c40ed10f6d440307bd76f1adef204a000,0x1b2ff982a2df4a8abbef6c9665ba0a8ee017a00,0x802d7d2e042f011787359c6cfcfce6e3245b00,0x1c39316effc2b416ea30d41f792832b9cb9de0,0x4d1d7f693b62520761b6c1359f6524d071470,0xa760e05fba6a60939627f7ce3be90e8daa30,0x1252ef5769b233acb0882b7d523fed71db28,0x1a2a4cf1e2bcd70eecca59b63965fc2ce1e,0x1ea2151d4045838f153276f119c6f11c4f,0x1d772d45bec5c9a4b05e5bc288ca75de4,0x1740b35fceca347360b3ec213a6b10e9,0xefa5c0be03bf5ace326c619d4aecc0,0x7cd0f0e659ed4ab67007a3ad2ca83,0x33c6bc775426d8e5a27b724ff71e,0x10b676356f402362ab6d7a75205,0x40c35b8c0b9780db5a78b173e,0xb13e83762cc24ae0005cf9e,0x131ab0e535dbaa651d6352,0xfa02115d303727bc88a]
def m19 : List ℤ := raw_ints% [0x0,0x1cdcabaa81b5f93f377c79a796f5cd78ae4017bee3be4fa1400,-0x2da97dec49292c8ea4a92a93865a9b8bde6ea94939c2ea4b0b00,0x22d405676f57efdf3b331810d9f3ef273906a60888427b21b4800,-0x110e2ac7006171b032bd81e17e9962d66a76c503eb18b377fc30c0,0x6064e1513bb517ae79c50066d6db6a5ca7a2b39fb48969e8ff0400,-0x1a29b3e83fe52b0bdbc1fec9594fc80b90e7a998f583ed83e96de40,0x5acd0cb3be4f933de3c25b9c6dac5ec89214cf1786e197a28850500,-0x102a284dcc0d786a6b4b4b6a4d208dafb223c0a4efc8f58a99e4a8e0,0x26826de8793942b263685ae751d29428eca45ed9ea0e82eb73a1a380,-0x4dce54b7829bff9ca6fc46e16761bcdec5b407f53aface8a4beaefc0,0x86b89988479ef66b7c7954970e5248911d676a117e5a440f8c7b8580,-0xc97f26ef41de08627315d499ee368aae04da63f0cdc3908b7eefd49c,0x105e15280de7502c85562932da12f0399f8565734cffce9db6ea50eb0,-0x1291326c55c994c18dc53fc044537c923d94dc15daa6f7ee17103a408,0x127138399b0691b7c719a7aade7295907718a78c49b2455c06b822330,-0x1012a9dfc4786617a9129e02cab883bc47125c54bccb432b362697048,0xc4e094b50156dae8699c4c2b223f06e7107813d1d92151318d442870,-0x846dd3c3fccc6d32b904ef4e75df8fd0a6d1e421d30cd354f9e92c88,0x4e38364b1c65b8264bf6eca62236660cae9e62c9c2213c4401990e70,-0x2882b2e782cefb01b59d99cdb82fabe06010b9f9dc303871e757b1cb,0x125ac6e540231bbf4ef30ab72b53d0ed46a734375b2fe3ee1ac3756c,-0x7408273866342882375076a3a6c9e69495b8e77b0698b542e9654e2,0x27cfc27d8b37ae96cdd3d28a48f497842ad785d9b8cb9cfb5e3568c,-0xbccb2b040a8d8b0d60370e59877ebd432cbdd34e28148f556f6a0b,0x30055f7beab18a45ea329fbd5f69c8129e53b1f2430caa3cae19d0,-0xa6611a3c23244f510326a9dedc5441b5ec9eb7b495d6fc690e868,0x1e5fca6c04dafa3888a2cf5fc07051f959a5cbd1766b97ae84190,-0x49e9053e619bce2cb2d989e66caa4e9af2ff626fe56b79bba6a2,0x93a669ed083ee1d23445a21c33f1d60b8cf3e5d085cb3e93598,-0xedd4d501a9ff154200a720f3de607ac4196adebb7259773594,0x12e0c0207c7355418438ce9b1a3989a20224853fd17a367918,-0x12604b1569b6b40f6a082ec91c11e9e6a53b5fbfef9384786,0xd39088b2ba585250f5f55c49df6a2c92cf22f54f9663de0,-0x6b547f32ea69581b7a6cbd4be7a28516357e0fb671f200,0x2407285e42bccb31e49449a0e72487f4df26401624220,-0x753ef70c5aba96ea09d57af6246154f326c7d6ca937,0xcb79ebc3140c21a761b875468c0168c9c29370aac,-0x9a67d39b4b6dbf896e2eb811a8d2a7cae826f92,0x243285e5564831213d559e848ba7477e0a88c,-0x133ad51cf69487d19a0a2652f9b049b047]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 21 68 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 68 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 48 indices rho q19 m19 19 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 48 indices rho q19 m19 19 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r20 : List ℤ := raw_ints% [-0xc378d9331cb535ba91bf172dc027e3b84a900000,-0x11580666a5d63ba50962d772811e5077b56210000,-0xb990f85a93334827c6b80e706c76daa9e6db4000,-0x4dbc7a4f94a4b16bc163e0203b014ccae0213c00,-0x16e299ed9b58fd6ff905143dbfc85fed0a8ab400,-0x508b9b786cec7813472e0c27af8e90531b9e640,-0xdbd6381e4b0756e808f4abcd3a0b3e99b6b100,-0x1dc96ed5ce8541ff051cce31e44964cbba9e50,-0x341b80bfd8159de442f321c57904c820d4c20,-0x4a4c9d25ba0a51afc6a98ca3da0d108833fc,-0x56d989240bb483adf2f2961c63508c619c0,-0x53650735292efd3072ffa8b1efbfee2e73,-0x41af4b0e5a1124c8c6ac04a16e6c1e0f6,-0x2a385288ce86a6743e39207112110bf1,-0x15effce6707e9950e9b0ceea60b2acc,-0x91374cefc66fe9e9e0a2b6fe12af1,-0x2ebc056a2cc8c5c05b6522fabb66,-0xb47dcb3cb7d178bebd9d316513,-0x1ec164d9e8b48b91a82351c58,-0x34cefda63448a5d792d748c,-0x2af9d3e39682441814520]
def m20 : List ℤ := raw_ints% [0x0,-0x30b461afbae3149aada20d4acebecabba60c2812205126601c00,0x4c6d72de5e64b2626c1abf926838b35d58e544ebf7eeab5ea2900,-0x39cd51d42bf70a39d81731493f215544346c3dbbbaf60933a7d800,0x1c0eba3148d5f73e4d59cf757369359c2eb84f4ca0faecde4785440,-0x9d21fe42006cdf7a6bc3f1af3ec54b8c54873a5c704cdf0d45aa800,0x2a3e9b29ca33910f0a11621cbf34a31e7a9183e5b36defd425069dc0,-0x912b45523db59d983252b1062e5ce989f873ef733f22d7b20a92ef00,0x1993fcf1e4c577affc748ecb405f73cfc147215cbba7f14925906a9e0,-0x3c485acb1bd9e3c2979ec0b1d15ad9b298b6cb6d3dcf30d5523fb2780,0x786f6792c2c8ed572907877a05fe4f13ec93718cb54a6c17b7bce15c0,-0xce187d77cf3451e13ed811ed8b3de2f27048233456384d25070ef9180,0x1307a0c1596a399948df57ac217b6c6951c34907a5621f53b8c60a20c4,-0x186a54e8ba7adb2d92c1f9d7e82cb78a9f0c5f35d6385fe4a47f16e5d0,0x1b52e41d83e0a3d88ab9700d61a46535337effb676c6224307054c31b8,-0x1ac1891beaa7ceb7163ffa9b5e7e770d6efd77af97330419b409761950,0x16f8a1e9987da206b29eda563158a2b2621b7ab26334dfed142f75d3a8,-0x114f490e60a9d061c7c15304c4630cf212d98ec658452dde0ad1a689d0,0xb733b972515304c461c05cb168d2ceb7959b53e2a3c38a00f2c160318,-0x6a4ee5f9da91895a4eca72c1b03f9bdb32355e181a6b9ec05a741fed0,0x360837a5802e34861e8a55618e8ff2f35ca3d5cc9d724e57d63fec36d,-0x17ff00e04082968b1e642120e785528b9eb2b12358b1231a38c89c9b4,0x947e77628b2909724cd986034169ad09cef8ae673be029b9982f718e,-0x31ccfcdfb8e92cfb5ac653bc8cc310815e78c49a1d35863ea0c63a94,0xe6755e837faa3c49c65d8f25dc634697df2a61020c2aed091a3065d,-0x3918c82533dd4b2f4cdb8e1dda4c8122061aabe156d4c8a2b30b930,0xc0496492bc2ab06ecb2a942d873554e7036e45768f851e1ff6b918,-0x220a60af0cfd1ce0ffbd1a780dfea6e03b207ebdc3108274a46170,0x501b3c36b69b0776397cd28895fc7c6b85c934cc83f6b0f82f42e,-0x9a48fcc136902ba39b909082827ddf3e0a1f9e4ef538662ceba8,0xeebf4a5b438e288726db3dfd0e70628adc241006e0e954e5a4c,-0x12215adf92bc3acc26a6bb71b410741fa038dd53dc65c03a228,0x10cd942a28773d34be31c3b46834cb1ff648f6ecc4c97cb97a,-0xb72564ce2337e98111e4aa4b726c3f57ddfb3626239feee0,0x576073d1f72b3106a4f680398ed87bbf52ac24221b3e4e0,-0x1b5d9d1fb31d2ea1d414d4400df0a91d52f831a87793a0,0x5251d8de251f8d8932508b35c1d4fe20628006f8d061,-0x829c108f9b74a2ab3b6bae2bb70244eed6ade94774,0x5970fdb36ecba33d8f57843bc0c753abe3eeb6de,-0x12a1cadcc9bd2f2978c1314c925fb5ca1bbd94,0x8a0b2778731ff123cdc993bb8dbef693a1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 21 70 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 70 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 48 indices rho q20 m20 20 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 48 indices rho q20 m20 20 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r21 : List ℤ := raw_ints% [0x2199ec04d8a5adc62ee58dec004bd557fc5d000000,0x2fabd39043c5999855e16a372ae23cf0f230400000,0x1fdb03a5590c1dcd4d4df2b907f7d84fac4e1b0000,0xd55a2cab021f374d752366b3466e8eaa5d8358000,0x3ec1ef8b87c64b26dfa8e2d23f1bfbfc4d08b2400,0xdcad7b35fa3db795b3fef25319ed780a45ecf000,0x259b6264923f86172ddb08ebd7a097a95db89fc0,0x5170e1efc6da66211a6047508e19fae76e1eb00,0x8e4cbf038b59b7ab90d59db893e88b7a492ab0,0xcaa3fbc53f7e26da37285fa68802cd8c13320,0xec8895a2b0899637852ba4268cd7f5504f64,0xe2c4c338ada393b5a4683767a6909d4d4e0,0xb24dbad3866676293adec1838e37dedfad,0x7263b077e0963a64f8793acee99fe8d2a,0x3b4f9c82769dca9fe4ed3021d67abbcf,0x187b04d1ff935540c21aafc24e21d74,0x7db9906cdde9c51b5e5ba0a02c24f,0x1e4201d2eac9a3e7811787cf541a,0x523845df40267c754491153fcd,0x8ca4829065d48b9042776ac8,0x71f66d62c9b031e017f114]
def m21 : List ℤ := raw_ints% [0x0,0x523064d88b5f32c50501766e3ce1f61ca834839e9688f0c22f400,-0x7ff3c532a80ea6b6de90b7d46ecf5b9baa840016d8e2192fb25300,0x5ff9dc75b51ff8447b02e2022d4ec197a10db0c8d83fe8ce0290800,-0x2e30b11d130ade642dcbb627a68d7a92a1a2a1eab8441d950a7c92c0,0x1006369560d3ea92a5f6df964651c19950da4500808e44bc272cd1c00,-0x444ae6be56c7725bd42ee80e79a5ed7f4a16b9056f0f12193932c0640,0xe86c1c2cd60e79838f56277f0a36444846c39fb69d0b823eea930ed00,-0x288a683b857b1fb595b91507476d0de5e36f196f0a2c3dfd2c80cf9660,0x5e8b8cf613d026f318176cc6f46afe6579bb3eb8c1bb1d5dce82fe7980,-0xbad10528067f5847af72155c7dc2973e1545975c907378a86fd99168c0,0x13c064eca9318b24b299d7c6f1d2128edc83d5eba0b7413604ebf470b80,-0x1cd44e88878470f96da847032a6d5a90c5472516c73b7d7c01ae3a31bdc,0x24858ada07e5891038dff42a5bd0479eb1c9612a2209c3db00ae897b9b0,-0x2854960c6d0c383ffda5b3566d4239babbfcc921b9fbbe2e757fc4d5488,0x26f0fb3a1d98c11588ea49a11382d8b4bc20a65f0da11e890f7fafc9630,-0x20f0ee0987c7b1cff1b21c137968e0ca711c3e2a7da976ecd2de0f40c28,0x186fd76bb89aa840368676a25ead38f7a2c7edd0c2f60360e156b8da2f0,-0xfe62732899733aa5ba7f07b9246bbf47a48faa98152bf7ea3c88f9e248,0x910af1d5551952e103df82f4972ad0b962f440310e6fe417681beebcf0,-0x485af836e16bb5cc753817e6edc6f0b2d00e3cd36e376e7c654b0693db,0x1f802c10e573e9f61738ca5cdfdd70c125bfbf2589ea78e5a1105b802c,-0xbed62634d6010b2c91c88e1fd872d51a9393002cc404c48660182bb02,0x3e8fceee9bbdcf3b23faac515cfa2d9b36156d5a2395529c03906ab4c,-0x11a865f52fc889ecb25b42b8f8b06233f62c33c5c6d335af1e6bb6a7b,0x442db26c9cba3238ca36bd51b3c63b70aeebd379dd498da12c0735d0,-0xdf2b1050afd75a989c59c7e1e157f201472903fd1164ae4b3104b68,0x264e9d6e054f552ab98047529a12eaa58ed49ae057aeea2bfd08990,-0x572ae9646ec8f58c7d36ee69334153d8f6c9e8ae678da5101ea602,0xa1d37d045ef3ac44b4d0eddefb9b05698f0df38cebb437075f918,-0xf0810127828377110197b2ca3ae950fd62ab28378def345307d4,0x117791cb1188546147c847c7e37466913b43c805e9275f699c98,-0xf6813ca97b3def4b7a5e9c51a0a60a4cb27d2841fc07d90bc6,0x9ee6a0887e346fb939fb414bbfad0f1070796a0bfe341e760,-0x474118bcc311408d2a9528e5eec6cde4a480940cdf444540,0x14cf4ca0d4f46d0cee5a46995565538128159e084d47ba0,-0x39d4dd28ea85d231b8693cd93b2a304872563ddc16e87,0x53d8a8ba34b647734ed3e4039e587b22c6a1a8d836c,-0x33cc60222cea4c55c3304383126c72ad40bf5d1b2,0x99644e9aff3a78e92c363b3048a0b0311a5f4c,-0x3dea6ceca745bbfc8edb774210301427237]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 21 72 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 72 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 48 indices rho q21 m21 21 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 48 indices rho q21 m21 21 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r22 : List ℤ := raw_ints% [-0x591a67b46435933c616b854c37d158a01af95200000,-0x7e5697a429ac005a6723b18032610703ba910720000,-0x545e7027eda113a34a33f201cbb9024c43a29c98000,-0x234a9aae258b5b191a611756433218088e67e70b800,-0xa5f7ec36ebe99f171f0744e3ba7676c4673902dc00,-0x2471e12d1518b2bd753e9549f49a1cfa52e23d5e80,-0x6348479be410b56ce67b1c0df9c1fc4171859adc0,-0xd6ca9ba062c737835d37460b89fd8256cd7ec5c0,-0x176e51c70e328e671acce458169418fc053701a0,-0x2153c6158fa26486e536bb51231b7b7abb2b398,-0x26d9ea320ced08a7009f5c7ffca8c2a66dbc9c,-0x2531d05345ecca6db4fbf427c70ffdab72620,-0x1d33299c1f8c5228501b8368405d4b0108d4,-0x12b36a1ff7b2145ad2190f5124cbc3cba07,-0x9ad933cc34cdefa09cc86db566672e1ee,-0x3fc78247553bae2fe8fb8064ecd7ef19,-0x146c974e591c7f8b379589bf8f50794,-0x4e711885b4a46b3beb3809eb92be1,-0xd486e11cb934bdc02a2481eb312,-0x16a57d1e63f27e1fb156c7a887,-0x124823fa5d6e29fd3eebc61c]
def m22 : List ℤ := raw_ints% [0x0,-0x8ab1aa2d6b30a5ac787277da06bd4f505bd89e1b9e071647afbc00,0xd6435c3a05d86713dcce079c35436399ab108d4c9c8c79807cec100,-0x9f6f8c7a6a10b43b6e74f648d9de0ef154840dab7bb14d6454c71800,0x4c1848a3ccf9da02462d6673d30d304e11db21c1ad98b4a94b807aa40,-0x1a2bb68cfa150ee2ac14f650b7e6e274487d7fb4dcd8bc38bf50d2f000,0x6e87ef7e8729f610a7dfdd4023b5332ac727a496ce2619d40035df25c0,-0x174a3f8bc1e3e24b4df8e10ae15864213ec58b140912fdcf9cc5dfce700,0x405c6203d1dab7a80d1411607d70b5e6d379381366f9ac8a0498b2ada60,-0x948e9a605d9ce4fc17ffa1f8758d4bd9ff7b2492d9fd8476927b7c04980,0x12263e0dc25123f11aa12e67499298cd79b6eb3cd3e535e9487d2d9a40c0,-0x1e5b4d553e373440ab381a70a2e4bf338de6e73450e8dd24142ca9d70380,0x2bc910bb8391fd65c328231fc77767bdbe959d34107c45294928b79bc984,-0x36c7bcdceeda845aa30bb8f949234cfa31673309788b02a681c019fa02d0,0x3bb4117e9c4d678788441233cd9e46df0497885059ddd03c37115e8ddd38,-0x38da9779343ceb4a6b050281e0bcad3c76ec37407d76ac42094085edee50,0x2f65248bca92047bdf81e91f78615df1ebe6ee126e43afa306292eaf1d48,-0x229e892199afdf2d8c0f0b1b1409f4f321f7feb4ad1fa5a6de2e39bcb550,0x1628474952e84a27b1c2353ef4b2e5e99ba1bbfa0b0d3e2914d5c8059258,-0xc6a4d16659b2bfc6bf4405345d916da347feb4d1a7384a86c4dadaa7650,0x6146074542866173f22a9a44fe223e69831aa673414ce4cd503a0b0915d,-0x2984f4a487ae26e0506c9c4185d96e553181840d5160bfaab0472bb58f4,0xf643b4bd90e65d7e42f8ba3136ada46743e53e6b56c794e33d5cb6de6e,-0x4eebd2a04ea8a25c976a9389a0aeab3fc4a00879883283cd9577565fd4,0x15bcf5ea86ba3cbf6cdae0c5b72fea7c9686bc8d1f19a2e591f0a01b6d,-0x51c081e2fae66cd72eadf192540c8a716b1620116b89dab4494dc5130,0x104145a67977140d63e81eb0f77e9886f6e8593e8f963239ae29dcc18,-0x2b48314528978aa583c43a09cb0ca18c5453122b09f3f39d441f4d70,0x5f37deeebee49ed007be5d1be42f64c40fb62665c6d8ab74fa140ce,-0xaa5af992636094d24097bc118134c8433195e9b7eac654c11f6428,0xf316e77942cdbae8c171d0a404d3e81ec49c2a546f4c89d7faa0c,-0x10e0fdba92aacb2b16b0b07c3b2901bed3f0698a557967c827aa8,0xe29ae48e93f95b83f4024e38e4f359ad5b1a827a7969f8fa5ba,-0x8a2831395d9a8e89a24299aac8fb7677ad42e62b64e7351360,0x3a32e711f9bb382013c2f0297d3229e1be5fd7266c02b42a0,-0xfd740fe206d15882b2b42d8575891c74323f9f1cf3aa820,0x28a6124591b6edf77cf6153e6eff66610ae28ef20fa711,-0x35d461dc8cbca8d17dc1b278cdbbf31de0f1a5be30b4,0x1dfdaafa6c885c004c4a10130ed3854997b7c663be,-0x4ee5f314162f74bad61387ff75a0b1d973dc8d4,0x1bc31ad63fd1313dc1b8e60b2f65a597c831]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 21 74 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 74 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 48 indices rho q22 m22 22 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 48 indices rho q22 m22 22 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r23 : List ℤ := raw_ints% [0xe4b3a8bff6dc1fc28224d4603f2573cb87bf22600000,0x1441844b55c8dcaaac250cd0b449353bf4c37c4660000,0xd84d35d505fc9cca7c804179e0cd7b3ac0adfa6e8000,0x5a6b8393a08869ff8df7d594b1dd9f030c976798e800,0x1a8ed5040f2bf09b9a429642b28f91f99b6a00f3fc00,0x5d3cdf0c784be5a4ec6e70657824875e8062bc60780,0xfdc8f18318c40905de7a13c5787609d3c419fa74c0,0x2248cffd071089c8ff94073898a4541a04dcbce6c0,0x3bc7d6380443f7839c3a15200c81a3a23b409f720,0x54f0211f10d8448f03d0a20d13ae7e251cdf49f8,0x62e665c20a7a744fd20d721d1822062df54403c,0x5e8f9b537733a8c937c0287f681e170cc68d50,0x4a2187fbf81d6b7997be8a98d4779ed645cdc,0x2f673093ae64a0b17ebd23105c3ac8a04e28,0x187d777d20d45819471233c22eb4814db81,0xa116a7e6f047c3fe6d47f78888c0ac68a,0x337a5eb31d2c126f0ce82e2e53f742bf,0xc53fd2039bce75b4e89a3df2e6d37c,0x21508eecaab176713e03d0bf28cc3,0x38a25d168ffc0153e90ca4836ca,0x2d91d0dc058226e7768039c85]
def m23 : List ℤ := raw_ints% [0x0,0xea0bcf2ca4e217930b412a3feb5f75d79afd8ace9aabf598f88d400,-0x166e0aabf4a84a8485519a11ce8929cb82910dbcf1fd55168d2ce5b00,0x108fa0238b9cd67cc183abc689fb9e4337fe9a2df6f6f3f9f22c40c800,-0x7d725cac9295076c84259244bcea94dcca8088a421843c251abb17a4c0,0x2ac7f91907115b4f583327b2f09fa0ad971f37bea5cf75238c9428af400,-0xb3193e5d5f736e99d9d2cef4cd9a0bd5df29ee83bd36828351693db0e40,0x25645b1be0f28f0ec6d7efb3d7e8e4850c96d0fd7dcb56f922bb475b9500,-0x6657306f2e57bd821f018590ac98a8687312e8264ec11ef2fcc59175efe0,0xe9d9e63b0a5765747cfc8dfa092e5354e0b1c29f4516cf8575915b75ff80,-0x1c44f8acecdb7767191924ef09f686a7121cc9dc58a493e8fbca890c969c0,0x2ec2f9ac9c50d3f72516daa0f47fb819d43808543f3362b034206634bc180,-0x42aa51e875d3ee80ec264b7582bdea772ef1ed52af3cc0e16bbb3ff1efb1c,0x5263475c0ac697d273d6a8404918fa2c962f0d64703129d9d8276f67b14b0,-0x58a33e3402521744f040a1932e68df8e0d38c379ddbf7d29e3788e0f64d08,0x5343090e3a3c6c18ba33b2c0f6420dd5b2293488c18619b6581baa83f3930,-0x4469f7b267e43b972c346ad6f87fc347a4c3d5f7ca780df7b74564fd14f08,0x313692ba1d52c02c839b8f5a9876561376e7b80c35758e2e4f9487eb3f970,-0x1efd7db289dd2b01244f818192c648735c2eceb93cfa064e29f6d497e6208,0x111124545b2d1b655d88a8cd66cf3e1e3971433089f71aefdb6bd66a1e770,-0x8347697f079864f5ea11c38755a558618ed71fa2b1e3af1622ea5fe7fbeb,0x36f117651656f69784f33e034e344b811c59595e366278b2458e4fe606ec,-0x13f14134adbb1dcd59399b97e315a74c03b31d5f2c07f0eef56cd56ccb22,0x63f77c1698d0368dde4c59fb5088a0b502f94cb06c4a16e795840235c0c,-0x1adf1ca8e461ae19cf5122b0413389ffc6451721a6615d9c176843097eb,0x626df4de05b6043dae623782008349c8a448f8b3b3f39076c11a9079d0,-0x13051a52b2e15190693243c500e939483db84206ab73673d261efb4a68,0x31184bada4dfe5c514449a4c2b50c329b0abf17fc99f2ac82b53a3990,-0x6867429d19c15a860056617e012581a57fb26f80118057b1e24dc162,0xb3f7c74dfb029e72c685495624337ebadd225d7f409caea1d708498,-0xf68004a6d1440da94337abe3f7902b9961f675292d79d523090614,0x105b8c595fe9d1da12aa78c8bdaeef88e4f1ee83e287e2cc124818,-0xd0d377fc60b77c4885e3836931ddf489d775590046aa2d3a2106,0x785c3c4ddd0cc1cf2c01c6c18e632bbff8ff1684055f5775ce0,-0x2f9afcd4b74790ac3d5d9618952b051589c2e99c416e0baa80,0xc11d9ba654e0060e5daa6570036e36656160470096ab2120,-0x1c95778e5c85e71789fbaa2de62e5732534ba046ad849d7,0x228f490e8c132ebf76e9e9c05f68ba6b44a5ee9e4c82c,-0x115c348080ce35bebe9da5b5ba566243d23eef175d2,0x289141d273116a42e357e4aa28cce0d30117c20c,-0xc71c5cb75d9827077c639c2c3987b8aba327]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 21 76 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 76 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 48 indices rho q23 m23 23 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 48 indices rho q23 m23 23 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r24 : List ℤ := raw_ints% [-0x23a111d97d5c6ba1fca4e6a9892a116c87ab7b0f480000,-0x3276ecfe7c4f6cdff6b5824958b54d3018df0f859c8000,-0x21a9583dbe7de43b8e565ece49b1186653541d81d46000,-0xe101f1e95c9503cb14ef617967b13af9c863e80b9ee00,-0x420bae5efd0b8f63c2725765c230c8e73f79addbfef00,-0xe7b45b4929cf81c9a3a022a7fd17956a1d9281e02ca0,-0x27631ec6e986b5bbaa26082d71900754870a1ddfcbf0,-0x5510474ae8dd315609fb187b286a0113463821ddca0,-0x943025deaa0d8fe4bbd74b175e3599a25ceb979668,-0xd25791c39e01be13ee05b5d805bde1e1cbf631af2,-0xf4a783572fce161860a6a4fd351eff1de1c47ab7,-0xe9a561daa98338ae6d4d3cdb9d30e4eb063d865,-0xb6ee745bb03c4ef8ee0d053fe5a09b17cacc5d,-0x74cfa4451a3b7bfa6e958f76e247c9ce72bd1,-0x3c416c4cb5929f279632e87a55462f2ed11e,-0x18bab5a311880a0d619047a9741e8422bb9,-0x7e34500c09673dc1d6ddc5518c3669938,-0x1e29355f1272c06fb228b285d0fa3fcd,-0x51513321d47c091f1137605e5cc20f,-0x89e1b649afc21fd44de02ec73192,-0x6e9fb2c43b27eecdf342c10eaf]
def m24 : List ℤ := raw_ints% [0x0,-0x18af3ed9b563d87c822fdf74bdd3116dbd58bda3ca5022e72236e5c00,0x2593b7eb28ad002c72267ecd16856dc02a4f074a60429687ce3bc39900,-0x1b89440001a6671cecd16368a4979c9e4c590ea9b00684afc0d74345800,0xcef1fdddc6c8d34edab9f5f4ab013ec6b503c4642c2160fc60cc4979040,-0x45ff30cc21b6965297c091e2aa8687115394bd2364951f193b0dd9d07800,0x122872084bd879ba5ef1080f55c5d17493fe5a7667b9399ea855bc41f4dc0,-0x3c1d111a8f5501dd8a76779324fe60c3ac8bf63acfdcc33769af2552d1f00,0xa2fce30cb0249d5a5fd981b141d9505039a00890fc8278df0436f13bdaee0,-0x170c6bd85044ff43a83e7fa82247a33a3967374f9cadd0df6724aa573efb80,0x2c1eef83618469bf47d125b72051b507c90631da0a04155d34b7bc897c43c0,-0x483136064ceb560578cd9df6ee7bbcacf711bbeff809721c4800b6ba038580,0x65bf8c9d1f70763a14142c8856984543502be781c95bcb8657a4fad7e1ca44,-0x7c3c6cf8b0f11a5b1fa2752a5eeafcbc842ceb75fcdfa7040bdfed60d0efd0,0x83f7dc0d63594bb41fe0fb173c9c38315923e5d387a859077c20a2d1f700b8,-0x7a4e3dfed03c3505bb4d5e987eb4553c59037597b46e338a7512ba98661350,0x63124cbac018f58e0e382046196dba9a13c52ffd6a78042bb09bbe7a8393e8,-0x4632209d6171a8dda497275072a04b886e86a3c4646078726afdf1861214d0,0x2b7f62d493ba140f429c2dfa7c5927f060121c713de746e24867e234e92f98,-0x178c4397c34e637fca369454ec6b1b59b1a66f0084a8a3a571346eff6601d0,0xb1d87cf5e7393503449c2fa076f0a4641fc9d226dc795937aaa3b570da54d,-0x48fcaf232a192e436a43526d1d118abd1d06af4d1271b8b3da189d93bcc34,0x19f10d39fd32dad965a997e71d20ec1a89bc8c091f9ec4d4a6174d33db14e,-0x7f2243f694675e6e76b875735144e03d87fbbba6be7bbea0168f68558914,0x2159ea9eadd3847c123bd5a52c4fa8555a7ad7ca245431ee55e15dd1437d,-0x76fc0c1ddad4ebf246a213e166976d0ab33ef8a161593657cd27fda6130,0x1657ca4f7197fd69bf2cb701115ef8191942e29804a288c09dcdc637318,-0x37e6c32aa66d8ec2928e854bd8d3fd15c6701954b77175b7f0719d7170,0x72e47841e2038d74a3a6ff27c1d920353eca8f0c8e6b48f1d1255d96e,-0xbec5dd68f486806ca4b7f371a2bbba7af8e1f1e76378ad088a6994a8,0xfabd549aa10822da6484effde39e4907948781b802335e35ee5cdcc,-0xfe57310fc84a1eee03749321610b9b4ce554459a83f10e1d9a4b28,0xc0e4a5568d349b8b9fe50c80693ce999517191299cd0c1f9a34fa,-0x690d60f03bdfd9d1c9a8620c44677c9871e2b0bb40f4728afbe0,0x26fe49beffdc2d8b5b2de778d8766422646333d41f385b86660,-0x9344709c0481a495963b6e7dcb0c1916853f4528379d760a0,0x141b86e061fe80bf7bc49af571d01fc31e99d2ecee5c03c1,-0x16301711a4e481eceac93d4f4b59f75e1a001d16f86df4,0xa0bda7ca2bb9b119100b2dc2bd9aefa5f0d59703e9e,-0x14d9f3ba0cc67733f3c4ee43801695b6308ce4814,0x5939cb1154a42db1d2d8083ccbbcabff375c1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 21 78 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 78 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 48 indices rho q24 m24 24 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 48 indices rho q24 m24 24 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r25 : List ℤ := raw_ints% [0x567e1fc749bfb99d9a98ae404c7acb69ecd6f8daad80000,0x7a72d8f63f2041aab161272affc1bbd96a76b54857d8000,0x51a29fe2e6367e2657cea6afc08dfbf4d5473839ecea000,0x2216166894e410d9d0964925d1ea3baf3f290d5efadaa00,0x9ffca665e4494464696a8786efd6db9fcc95460ef8f700,0x230e8363cbf5354e0273df9345d1610295b3e21532aee0,0x5f47c7ca85f232f77a8de2b60f8cd8441cb2414cb93b0,0xcd9ddcf3d359d5d95fcc50a24ad3b9781761deab4430,0x165e72876a385e3d500311fc174169ed23b3734f03d8,0x1fb8e67badded7f9f7785511f7ea24bc1a2c297270e,0x24dc50803b2d048aef46dcd9d5ad88c4759208127b,0x232a0abd7815421da6cd01704168955d3d4daa1cc,0x1b7fd2d32647a9a87f6e9bf2dabb99d271bdd6c2,0x118987da0f5c6b61e5035e711b5d33dd1d4cfca,0x9089f19a92216abbaad6335515599ac3751c1,0x3b3a827a805af90222424af331e3772834d0,0x12dc1c76c166fc113d2358586a6a457a8cd,0x47fb149ffa014dc94f730a4888312adec,0xc1aab52436ba703cad5e00b134071b4,0x147a0e6c8ef720b63fbdafa9773410,0x1062fe01f6bc9030e65be8724879]
def m25 : List ℤ := raw_ints% [0x0,0x29a7ba0f62187d521bb0c91500542d692f85c00465673ae609bca3b400,-0x3ef78ff76dd7943bd489bf8a863ddaf07c1c047a3f47e34e0404da12300,0x2dce03b705aba582f48d89cd121fa289dc252d9269a41df44fc0ebd28800,-0x1559d8e98932832563912f1c14c4f44ad3724bc4e7a6e5ba76c9c9f71e6c0,0x72a0736a13d8804a509b18d82fed3f8d4ce156dc557963478f92002ba8c00,-0x1d7cd8ce7f0a039e5ce3bfdd29465c43d45f16ba1c21b3b44ea41adcdaf640,0x60c500146372c272d44becc24dd1bc5e35f481156341b67ddc74e7b926fd00,-0x103f96e31bdf3408dd948787e5fd2e7e9fdf9050c5cdff5ff00309d63a35560,0x246922bfdd509eb984e6f4eb128db4816a345b3b5b828c92d2c7506a1ceb580,-0x44ff132966677b31e5580a42c3f0fbaeafeee42e9910bf6a5fc8ab3a8fcb2c0,0x6fb2432e9edcb70440e14b71ee102f82585c4172de668e96c537c3be18c2780,-0x9baa4c18213302a1ffb57d7bea27967211f00261d2fbe14541fc377571f525c,0xbbd3b0366a66fb62bf4a5b308d0e1f4a30632516d7a60bf75e82723549a1fb0,-0xc507826e515e6e0fc71b09a7a4e95165b4413cd1052c80894671a82e0510d88,0xb431876bf2e4243cd29416ce27f60e9eb749dbbd1b7e9f1f355b87d2e550c30,-0x8feba13e18364307fbf4aabd56a9ffc979bfcd2cb5ace47b8b6965a9bba40e8,0x64752b1bcc4e4d518e5fc151fd7dbbb62a3238eec4eab7c47444e9c1c00cbf0,-0x3d43ef6e131f8220f64ec4278422d0a3cebcb3c5b0dfa3d8ca7638c29e21bc8,0x209b822cd3d0dd0b25808858e9933198e1e3a0b88561198064b998c12a72df0,-0xf1d4a8667c0f9e2687eaecf7c0f34daf5601017853b334cd9e14ea325701fb,0x6154b978a1c1f973a9df5031cf13a77e47cb919251f6c6e61b19b547c049ac,-0x21e0990597bef32c1f52de8e81c287a640ad05d251f9c04bdebf7760aee542,0xa2527ad07adab56cd937780d25604dbbbd9e0614bc7a2ab2194ec1612a8cc,-0x298ea1fa80b4de815d7172627a5107d86bd75a1def0b8afd617965fc7525b,0x9065842a435c004ada46a05876b2b3bf3ce6de4e8ba806f6ff84a21c25d0,-0x1a58f71bc9b658a505fa6c006f5a70351773a17e77b7489f5e4a3156c568,0x3fe37f3a6bbcb1fcab2eee7aba0149932d0af9e9e29ef0e875ee0379190,-0x7ee2379c3c89fc78e0e6235fb2391e9c8e224d817f5bd7ae7cf3c1c8c2,0xcae5415d07d8ce8dab5394aa26c8e0a01a2f812d4693bc294b13ad818,-0xffd1ac7b5d0c53f109e0b681f9e3123691fd9db75e17430e520cb054,0xf7d242ab7de02fc791bd1e71311d0e97c875e9b874bb8103c787b98,-0xb2927adda249e7b98df0f6769cd50b95b614d6d11f079d04c48f46,0x5bda2923bcceae160edb630bbf7c1de17649fb8468dc477273e60,-0x1ffabc5d80c03fff4de824f37923e3ab9c4d2f03dd2018e291c0,0x7063e6b5f4d72c8dcbb10851d8abe77127830b8091e5e7d2a0,-0xe2638994b46228c90de0dcc2fc4bb656944be7e2eaa4f327,0xe3e8f8617d5bb83c224e748cc3e89f062c0654333598ec,-0x5cfee286e43f622f528488ea05e73dfeffd2dad77bf2,0xab6b9772583872358c58a40d719a44a9bbc0f90cc,-0x27f8fa3e83da6689d6dd145b62dfe392c73317]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 21 80 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 80 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 48 indices rho q25 m25 25 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 48 indices rho q25 m25 25 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x1062fe01f6bc9030e65be8724879,-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r26 : List ℤ := raw_ints% [-0xccfe8bff4917031c0266518a80db8273fb2dcaee47680000,-0x12215ac4b04c848c68f9bc3fda81e149397658557efc68000,-0xc14ddb671cbb35dcb906e0808c13caa997738272768a6000,-0x50abd2ff919b6cfb116090bbb8441a108bf7666c79d4c600,-0x17a6ce84f0761b74c3ea5546e1d3d4826a7be854fe372900,-0x52df082c930e0aaa082ba4bf3d468de8d33f1fe512c1020,-0xe1166a46180362a8fd69371305a8fc19c53c1a87c73c50,-0x1e565cd29b85f3deef9c68a45bfb73caa1983756eb8730,-0x34c3f92a47e6834e88256bfab62e12334e992667e5c98,-0x4ac4309941a3007f79beb6aba0c94911db0836bb6d42,-0x56cc538c093762299b215fa44c832477a4ba1eb09fd,-0x52b8d121a07c2e38661316e0e028b760d844148d0a,-0x409f07dedf8af217971e01f2fb6617b8bd5578775,-0x2929b2ea124559a3c0dfa74fc04ebc9f3c80dd7f,-0x152d2ebfcdae70cf09f39d67fe6eeb117aff6d4,-0x8aa5d29ed662725f4c9941bdca59d6eb51821,-0x2c14c22ded672d5220a8e1fc52f71a2c62ba,-0xa7f506fedff8b9bdbc6847b561122bb86f,-0x1c30ddd2fd5800472428aa821dd8049eb,-0x2f97beb69303226c452f8647e01add5,-0x25ffdcc2e1dd45df1807b7de7dcad]
def m26 : List ℤ := raw_ints% [0x0,-0x464b09f9f589537a8eba5353708e0ca18031b4076b1e3364306e543fc00,0x6988fa8cc24fb48c4f02bac478eb0247a71818d6fda7882a05c82ffeb100,-0x4c39d7f47b65d3ee2ab91c4a7593bd00ed3b19ebdfc5d206f865680bf9800,0x234491bb435bb577a5d178d74415162caeeba34462a89291559f2607818640,-0xbbdfc5f6ba7c42342e3734992e9614cdec82d4d70d387e0b878ac256c94000,0x2ff02769e940ca5b0f545461c2d7300cabe1bfc76c9de6b70f3da94f6e415c0,-0x9bfa9f8473fd35f459c0e0d3b8df54070301f2b5ac1de103f1458f576399700,0x19f4c6e78269306e6579b1e1e79aef2fac220c58235d93917418d3d0d55d0760,-0x399e588e231d5f10b0b28c7b17710c7f061fc52471b7bb065925f2c9a7f6bd80,0x6c1b0c347f2fa88e13619679bef5b8753396911431ba693db7a8d34949035ec0,-0xad301b31a83ea42e65b7d9a570ac9bfd1e75a50b254d4510b63534d8a3089780,0xeeb66f9df436cc9826322e458930383b1504a759aab1163252ce444fd6b1c304,-0x11cb0ebc48aed860ba65fe1f11ee268f44a92af02c55328d79fffd1276918acd0,0x126f9196450fea80ccef4ce86d0caed371fa50070b7a62179f9aeccb4ece91c38,-0x10a41f526af31cce86a231c3060c018ffd29df8d4598685a6177a245afebb8850,0xd1b8b9cb858ca8969fcd982e9d8298a2028ec6a667456a1f5d4c63e706480f88,-0x903c68880c814c133c6ec22daef8165c2dcc2c5448bfd2b7233ff218a48a8850,0x569612eeb6e666ac447a41074a089c4135ca29e9093f814c0548fe935269aad8,-0x2d50290cad5019c13cd4239f629fe730c4ff573660a0dc2ed24d63aafdb18150,0x14a0b5e3372c8713f8f04ecd2d6029b9c38221e53306912973a6cfda11f3c73d,-0x82489648f68ff1feda9c10e6a360794366fa78fe9931337d3a257b18d5de374,0x2c690d586eb1ccd6f456a01e3905d0cd22c66d54e66a926f1f3ca39faeb8a2e,-0xd00d8467acb015bca92f1a222077008d7f708fe333b74002a28d402cf27654,0x33fb9be1814b73a1d156fd30a0fbaeb19ba94601024ae10e135002add5de8d,-0xafe8a5ea22dd00d6685113af96c5efdc01b4928bc9f065ce45e85fbbba930,0x1f2fc87f59ecf26b42d798cd0e746ec7781d214bde026baa9ea2fb1ed4e18,-0x49483339679b872b6b63c470c98177409f8359ceb73dfc4a88385f9f8d70,0x8c9bd5e0a5e0e92d17879688e5e26da1a99cf4d1ffd94bd38473eb42e0e,-0xd87a845c966ead57e2bfeb13add7e6f1cdcd3f7599b2d3045eed5b7d28,0x105c1a75ca762cfcf9e1337e6afe5e8144a232b16fe002e3a70642458c,-0xf2145c037e63cb74ecce0ed2a7b49528ce4bb2f94c8cc74c341d13a8,0xa5a9b554c1068fb56733c760cc2dca32e745ec515c3721cac49bf3a,-0x50716318462fccc03ca92200b54cf2944946da825e3c98ee368860,0x1a41f655ed26ebdb52cb5631ced92088478ce1425a024a50b2020,-0x55d507a843ae9d67819a78d8fc01bbbb9af171321d7db5d9d20,0x9f5915aa1004ba92eca96c67ddb13c6153de950a950f58e71,-0x924e658dea3e58ec88f7be678318d8253c28159c4d13f34,0x35c9950b5f555030ca5a7352bdb9b9c27ec6f26d1277e,-0x580c71d0673b4e41a8b5a34178f57bdf9ed5a87b54,0x11e708dab45ace1c7e6ab560fcd9d173f822c51]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 21 82 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 82 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 48 indices rho q26 m26 26 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 48 indices rho q26 m26 26 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0x25ffdcc2e1dd45df1807b7de7dcad,0x1062fe01f6bc9030e65be8724879,-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r27 : List ℤ := raw_ints% [0x1db5db07fb62376f821c88769b9912350a4bae6d47e9880000,0x2a06848039b06ac86233199cc56bd442864ece1cde46788000,0x1bfdfb36c3db258253edefbd6a4b6b56462565110500c6e000,0xbad20274deb4070b274be0286294e2aa564e7d7589bc97e00,0x36be95987ee502d6b99d19316a261483b7d9f2e9930bec900,0xbfb52ac8618cfcf8f208744cc22efb309d30f336ca49c4a0,0x20862177e91d918a695ae0dbb4b5cc0d76672b58ec579ed0,0x46175bd10fed10b1fd250b54f23e7192979c8b384002010,0x79d28729da62e2b6d8555db929a21cb7238d85d313bf38,0xac7bd591a9c8d31b1cbfc77b7ad95d3051e1a53e75e0a,0xc812c45e4e2e62f6a16769bae155d5efff1a09c610e5,0xbe8128102cdec7a1f48befd680b3d0e5ff95f5fffac,0x94ac3ae28d5d360bfd41fd5de79c6a98cef0d5d60b,0x5e99e234a42a9c2f628d54ead578f4c21a4b282a0,0x309c7a74cf8be2a2ff3d4bfe512a3465bb6e43f7,0x13ddd26ab3d09a2762e9e1d780cc5b4a2964236,0x64eb588303cbd65e194354ff47c4ce6299db1,0x17feee730831cb5a8655163e587c3f4f4432,0x40554d371e8a08dd15922d42a4ed6fed74,0x6c687bff2600d313a4307a644a668312,0x566102531f67003d7533d216550f6c]
def m27 : List ℤ := raw_ints% [0x0,0x769ea0d5ce57bcded0da6c9ccdefb5508853dfcc84c2f6b911ba2e2b9400,-0xb0eae129c472dd94b4e74f6cf46cd92de52afe00eeb3d1bb4421d0fdcab00,0x7ee7889936bc2cb33919609f3ae8d899b3c5d33ae683d47912d4245ace4800,-0x3a4ae8ed551fd91d2c55d1283cef862e6f289192f208a5cfec8c0c11cfbd8c0,0x1342fa243bc435e23ff88ee4b5f629ff1e6153681eaadfc22a7b4aadbb0de400,-0x4e03d99c02868013d01d3a875ecbe874e53a57543dba113c446a004ceeeabe40,0xfbbc16837000cc362b4db83839ace9bcfd3137dc4ceb0ae0caaee42cc8652500,-0x2986744b78f17db633868358ff3acc5942dc2b051e89a46e7946b9879843a66e0,0x5b554a8f659490b27cde0a0348e0234e39c8773658eca9ac6d1b742b0156b1b80,-0xa9b46abe3bcfd0828636923218aa9e55adb5c9da97d26fb7b4b166d6cbabf03c0,0x10d18e1ee8b0ca90d6bb09acde346403b16fc24f8bf3eb2a1eb842bebdd646bd80,-0x16ee90c94d43c901076bbbecdfb1aee2a6fb31cdb1034d04689801fba53edf019c,0x1b097025ac6ba15244e1f0ffbe9b8d59320d22de905e0cc1b1ee72622ec5efdab0,-0x1bacba148f59ace882892c516f78301dee7b22d76ae3bdaf3a9c472eb048a81608,0x18a8f9aa0617107531538f3e51cb46bc2551f88555abb1d3d0d7c7ab4ba9b90f30,-0x1328a72fa9155d74682d9da59d5b4188f73cbae34ea81793219535b48d6448a9c8,0xcfc2338fa372bed75c4a1355b51b2901e57f2789255e150e25a11c7cc3cdcba70,-0x7ac8bb34fcbf5f56eafcdebd0163aff2ad26d10eea26ce944c7d1866be026ff88,0x3f30a2a147828f2861a5a175150c700112355f0d4d65ef98a92e8939e311a3070,-0x1c410451226c8dc78f7e9901f20b4aa961b1044febb9e7db25e0cbd3e881b7e0b,0xaf09da43edb62ece887e8cfadb8756a294efb271afd641780030d6ac8b7f886c,-0x3a7008078f14f62947260c577978eb120929e3e084a731d78e3fe14eb4536962,0x10bae3dcb9a78fbb0c27cbb5a7f25019de759a8bbbe88fb9504a72d047f5d18c,-0x414569a87f98ed2b4ac03deb2a53dd5d8b5cf07406bb6be6ae04ace65cf79cb,0xd71a715d421c7e53fadbb3d682660bc432654784e3671a66de37e7d2aa79d0,-0x250cd0d3acef1fbb0586975d6c1ed41b44a81f8bd0f3cbe78efa4e52789c68,0x545a7d054e4ee8ae35f6555fb7304f7a54daf5ebff03daea8d2a5d728d190,-0x9c56ccb43e27cf2496cb4c44d05a88e726bc7a9189f7cfba420978b60c22,0xe7af5457e1ac8ef314c702b14fc8c92b8874c99d67610701be6e43af398,-0x10c9399ee78a0511558207e0d885cfb1db2418f80f919d9b99a698b8694,0xed0aa27620ba1aa77eaecdf268041770d21d4d6cc098e0b9f16b83718,-0x99fe5ba211ac57b55101e56c6fb72b0c03990db98dbe8a662b2b1e86,0x468f31b95899c2fd2545d0256eb7a92d715ec5065b0113530012be0,-0x15952c82b39c6bd1d54cbacd215f2912c0f89996f71d8034e5eb00,0x419717ee1f3c53d4843fd20d5d69caa084cbe92cdcffd5133020,-0x702f31da56de888c8af5e47f87b648c16a23a8395dc5e0e277,0x5de99300b79bfffb87bef665c89f9e742d52c54cc4a4b5ac,-0x1f19f0fa4e897a292f005e8637cf49428281952ddc0412,0x2d35dcd80bd7423e6a46c368a724dfbf24b56448b8c,-0x8040ade6a874537d3a3128f6966efe21c7e1207]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 21 84 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 84 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 48 indices rho q27 m27 27 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 48 indices rho q27 m27 27 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x566102531f67003d7533d216550f6c,-0x25ffdcc2e1dd45df1807b7de7dcad,0x1062fe01f6bc9030e65be8724879,-0x6e9fb2c43b27eecdf342c10eaf,0x2d91d0dc058226e7768039c85,-0x124823fa5d6e29fd3eebc61c,0x71f66d62c9b031e017f114,-0x2af9d3e39682441814520,0xfa02115d303727bc88a,-0x573cafec609b152587,0x1d0d3ee79a5ecdf2b,-0x92bd3dbd56c07bd,0x2b8b840e5d201b,-0xc04c9bcd39ce,0x30b0c8eba5e,-0xb1a70ca66,0x238eb7d8,-0x6034d1,0xcecd,-0x13b,0x1]
def r28 : List ℤ := raw_ints% [-0x438957f01e3ee5ca78bb3d7a346b64c763d2366e114bee00000,-0x5f7e79988d42247e6f0e646cac04e87faf84d04889da2460000,-0x3f9470a691cb5999ef293b5316f510daa08812fc065c6ee0000,-0x1a824e1f59c007b55b0958e0ccb5f57d9e2cd1e93db49386800,-0x7c3a5b6b800db955d74837719554e7be0acb5a21575053a600,-0x1b2cd55cd24079f5f5f5ef48ecdb97a6c538e00fff98f4c480,-0x49b965fae1e2f01b0130fb600ccdadab420587126a3cbf5a0,-0x9ec89a462f35a6dd70c8dca76040cc36889c5fefd24debb0,-0x113cae15383fe757e763eeb16294e6f7ccdca135fed17750,-0x18634a9078a1578daa4c549fa5f0bd17a43998b7a261780,-0x1c4457cdd6c8f021578f4d9e20dc63d8765539f20703ba,-0x1ae47d7bb8d6ce555b4382531038ea08ee5683b0db017,-0x14f7e42940cf78fdebdacd56a699372e15139d41a720,-0xd543f0af37a5d1cad98618094137e52870759794c1,-0x6d78554b2f40c9117d1c61b22b24047c9d07a1548,-0x2cafa5b91a80669ef5707bb6be50dcf4b5eb4a21,-0xe2b5ff45b74ad1ce94579107572beabc4745c2,-0x35d49ed793020927b561df4ddba983e10821f,-0x9019b56c678b7033db98dd4129719cd1c22,-0xf26acdd805e4db277d3c6f1d9cde5f2b8,-0xc0ccc3ec4c9d0421040c994da37fe8a]
def m28 : List ℤ := raw_ints% [0x0,-0xc82baf68cc340eb8007097489b8481f7e60d89a9200900584dea2de989c00,0x128a46acc5de5ece3d694baf226141f278aea55458b223f5915d510ac460900,-0xd35ccd28ee31e7a463a7f5d5373da1f365213b23335265a93636fccf8b8d800,0x60688ee29ebf9643d86e2def3fffa149e020f95158caa1602fef71f418a30c40,-0x1f9f5b8aaba878af1e2695878fc882e73b38fdc2bedf80666f7fe0582ff434800,0x7f17ede9c2ee27aa3dbede574f09d975497368d45600bf9f610d797a53ca27dc0,-0x196c75082346e3ef43605770b316588366255e645896ea7ee61a0baab682c84f00,0x42877310f88315010a3f660f2c060c73711b657e09afb570dc271c5d34b653c3e0,-0x9103dcfb5a225cf506da441497bb85cbe615ffa52855ce194cd1d2ae4d86db0f80,0x10ae63250e33e2659d8e426d5e4ecee28f3aea8cfc3e0e2e944f462567811acd1c0,-0x1a2fbb4b519d10abbe1d4b3df93918eaaaa291b926557965ca6ef1649333acdb980,0x2353b7d5b335e67c98c960a67d319a0382b3b9d3ef60def4ade78109629419653c4,-0x292f0add884e33f3982048c28e5efbe58647d533a30de69c60b8321c2bee21e39d0,0x29a755c4bb9b2255d8a1d4adb342ee022b13a1942777afd171a4ce94917eecdafb8,-0x24a5892159c10b5b7615bf4fb9abb1a8d9d61bf7d737211b36cd9c7cb2390db4d50,0x1c16728924c3103aa18b3d08020961671dc79681ce6280b940c76424370ebd5a828,-0x12c343af592c1b472da5607e9a5d2e21ade6c9c905c323746bd2147c3da3f4eefd0,0xaeb0f6e90243427c974d6470b49ecc2b060a161639cf133bda179302d8d94f5418,-0x586c40df12334a21d3d056930ad39cc173686f8e635b8681ab1848ab42a5e6d4d0,0x26d64bd2c59af9f4b964d5b6a8ac80a5185fc1ba4e9654f651b7bea57a0edcff2d,-0xec06103907487989f880e17ca99efd41aece2e5ee28d1bf165bfa9b7cb82c5eb4,0x4d2e1855bec254baf234b4c06e709b67b59ce074fd917662579bd573c11f0090e,-0x159aeb86cf348521e48dd911964d9a2047406e45801a3a2cf6f69fd4a8343e794,0x5242f25025e1e2e6101bff77bc46370f36ca5512bc88929902afdb70ad7bcc9d,-0x107ff767209495027dce5be3263a204aa0c1c081e1c04bb81f8534f88caae930,0x2c2c70b7f7de3a5ff88d965e48ea26877939138795801dbabffbe61ea4bfd18,-0x616e7eb11f692247a05c4fe92bd5e621e66a7711284bb82c2bbff846a06170,0xae648a549d600388bc66236cbff6b8424b094da92b493f62fca2b1eeb2eae,-0xf8b32311051a111f93b7c764e04d18c5b3a3455aefbb912b83e6ead11da8,0x1144f8c58948cbe04608830a011f7552d9b31cc0f2892b5cadd2f7e4914c,-0xe8a49963b310d2e4c42baea46ec7208df5fb59b33a10810e158f58d428,0x8f6a98b59471d4b4505c9f1384ad284ea492266823c84bbae36eadc7a,-0x3dfaae5ec563b70048c501a8366750778c593610b19ac72e33a198e0,0x11c1edbe89c281b293aa10ecf383f7778445f156619b6ca01b6bfe0,-0x3226437662bb270b76ff1874aa3c8d8014a9eb914fec9f3da3da0,0x4efe679fdf37e727675a04e038d27ab831c472b2ef56dc32f21,-0x3c464e2ec85d42c06dc8abd78d6a5abeab7f1c6a39875e474,0x11fa85c9d8c0f5035f1ce9f26485f5a6faa1ef95c6bfe5e,-0x1734e724784e3f47afc58a2ea31ecaa96ea25cbba294,0x3968da2f26c0075141ce599f03da731c877d7be1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 21 86 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 86 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 48 indices rho q28 m28 28 6054328789891793067915959500800000 27=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 48 indices rho q28 m28 28 6054328789891793067915959500800000 27 20
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_28
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<29) : intPolyRF (mz e)=rfPoly (C (6054328789891793067915959500800000:ℚ))*rfX^27*(1-rfX)^20*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U6C27
