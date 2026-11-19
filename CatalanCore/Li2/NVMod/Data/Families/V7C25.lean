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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C25
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,25,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x2eb6f5c878d70c0000,0x3df114b7c4062ec000,0x266ed1bcb23a473000,0xed45259fede21a500,0x3fcf7cf2569afc600,0xcb437c65c257b770,0x1f0d42db30f42290,0x3b8ef60bb3372f8,0x5ae376db9eb1b8,0x6f3232ff0e147,0x6d575516d791,0x56395c7af24,0x3621d1761c,0x1ab16ebea,0xa1cd966,0x2d732c,0x8ea4,0x117,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x9,-0x64,0x785,-0x56a,0x32d5,-0x13f84,0x4634c1,-0x1f33e4,0x168b404,-0x2ef3770,0x75b4217,-0x8b4b538,0x598bda4,-0x1182e30,0x242f7713,-0x1207b4b]
def rhoDenominators : List ℤ := raw_ints% [0xd5a980,0x3246,0x2cb,0x8f,0x68,0x5,0x5,0x5,0x40,0x9,0x2d,0x37,0x6e,0x8f,0x8f,0x41,0x2080,0x8a2]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 25
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤24))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤24 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 25 omega7=padCoefficients 25 (omegaCoefficients 24 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 24 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 25 omega8=padCoefficients 25 (omegaCoefficients 24 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 24 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 25 omega9=padCoefficients 25 (omegaCoefficients 24 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 24 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 25 omega10=padCoefficients 25 (omegaCoefficients 24 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 24 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 25 omega11=padCoefficients 25 (omegaCoefficients 24 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 24 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 25 omega12=padCoefficients 25 (omegaCoefficients 24 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 24 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 25 omega13=padCoefficients 25 (omegaCoefficients 24 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 24 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 25 omega14=padCoefficients 25 (omegaCoefficients 24 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 24 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 25 omega15=padCoefficients 25 (omegaCoefficients 24 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 24 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 25 omega16=padCoefficients 25 (omegaCoefficients 24 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 24 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 25 omega17=padCoefficients 25 (omegaCoefficients 24 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 24 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 25 omega18=padCoefficients 25 (omegaCoefficients 24 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 24 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 25 omega19=padCoefficients 25 (omegaCoefficients 24 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 24 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 25 omega20=padCoefficients 25 (omegaCoefficients 24 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 24 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 25 omega21=padCoefficients 25 (omegaCoefficients 24 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 24 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 25 omega22=padCoefficients 25 (omegaCoefficients 24 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 24 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 25 omega23=padCoefficients 25 (omegaCoefficients 24 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 24 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 25 omega24=padCoefficients 25 (omegaCoefficients 24 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 24 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 24 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 25 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xedfe42ab8ea5f19a64000,0x186e5881d637d6413633100,-0x1359b43037a0d74c1ef1e1c0,0x9d786eb74bd74b2986eb3980,-0x39c84034ef44e821c11842fb0,0x104af34626f38dfdecc53ac4e0,-0x3abecec0153a97fa21894fd130,0xadd377f86ce20590a9bb8a1f80,-0x1ae1de5cc295822c9de96d7167c,0x38658f47c21cc86e846aa1ca338,-0x6559a0424a33cbfc56b26e8b21c,0x9d3a639234eac98a399b8b08bc0,-0xd3c584db4b5d732480d32afab20,0xf8aeb899aacb70545e31a03f280,-0xff53919c4067158ac2715b3e360,0xe5968ea266c1b5258475e599800,-0xb4ea91bf1f8bfc482d5637ee16f,0x7ce2f191c2a3b24150bc2b21c4e,-0x4b6a7dfb528da560c8a3e68d997,0x27be74d8f6eee1c8024b7325890,-0x1236bf982523c2bbe8f99ad2bac,0x7395270613d577fdf12ef3e808,-0x276d1cf0db59c9389d7b2f1c5c,0xb79609b9dbb8e2daf74a66270,-0x2d1f4c841b0c04891b46e02de,0x93ecdf250ea86709e01feaac,-0x18d9740555544b4009964e3e,0x3594ebb3e46d9a7766ecab0,-0x5a0abefb0c04e09dfb03ec,0x7151dcd19f0c5b09a7568,-0x64df759dbc53c616a57c,0x3a364041e95e7dd1a90,-0x12d67b410045fd7acf,0x2970c0897c82f2fe,-0x13749c86df0de7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 18 35 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 35 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 43 indices rho q0 m0 0 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 43 indices rho q0 m0 0 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x164fd640155f8ea67960000,-0x2426a54c9a428415c5305700,0x1c3c6887e41f580889ca7a840,-0xe28259506a56c626ce9873680,0x51e6757d9cebd6a9609e6ec0d0,-0x16bf095e2416696d9b429449c20,0x50beec65e85723349b4ce74eb50,-0xeb1ea9381f67fa659d480325b80,0x23c3ae092ec50de5862bcb459324,-0x49c24cab48fbf5640af9e62e0908,0x823af867342fb451817d5bea7c84,-0xc65ec32fd9514bcf8ff801adf640,0x1062b69f70fc35995998bf2f852e0,-0x12dddd1b3999b1077bd2ad987e780,0x12fa7a49438922f0dd62046cad8a0,-0x10b497fa71c1f705e0845d5f6f3c0,0xcdfd4f8688366de5d89fa0129739,-0x8aec77ea0c8cd1af6dde0401d242,0x51dec831c187c1f4464c66b9d151,-0x2a0d650a2fddf9289cfc53c553f0,0x12c1d632ed8846f29b6aaff48774,-0x73ab6fbec043181683d0b34fdb8,0x26460080e48128d167e06f4cd44,-0xac86455b16880e4d32818a6390,0x28f3c2a2f5b4da331116a3ff72,-0x814da1d053c6f60c8441ffdf4,0x14da28183b0e8184b9bbe3a12,-0x2afed310656e8f3847165cd0,0x44c2d9bb859787bf2eeca34,-0x51dd4be580bbffa4f73b58,0x446892c1602357d82f424,-0x24ae74a2a6a267d04ab0,0xadffc07733ce9a70d9,-0x157aa2e7f783c3812,0x8cc9e563114a81]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 18 36 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 36 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 43 indices rho q1 m1 1 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 43 indices rho q1 m1 1 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x2177c160200f55f9b6100000,0x358396b90f3afe03565fe5100,-0x293bdce4cbe8ef0b867c491dc0,0x1463216ca6fec827f8663d70580,-0x7443b6796b5fa6425fe547792b0,0x1fd125971fb250ebcfc0446826e0,-0x6f3d8fe0c1a68caef952c2c1a430,0x13edfb904b9c561340a4ecfb7e080,-0x2fb99f36efb7983bcf600c5f1983c,0x60cad6739822befdd04edbef2c7b8,-0xa7f6a0e8bdb9c9361acbb922a03dc,0xfb4b47d83062fd5991e36cfdb87c0,-0x145fc0de44ec1fd16b0be4db376f20,0x1702544de52bf348a1c454166b6e80,-0x16aef41833fdecceffd3ef23f13b60,0x138d167cb5f201d8d819f693003840,-0xebd617cf7995a431541b7a7bc235f,0x9b6e717bc635996c05a26513c6c6e,-0x5968c60bac82683c7442b5aa78987,0x2cc4fa988c1d6767653710356ae90,-0x137056464d1b7fb982c3dc2f0526c,0x74803fab1ef46cd0c4a9b22a9588,-0x256537edb7bce5c184afafc43c1c,0xa32e59a3bd7bd015ee8534969f0,-0x2567efb738ae05d09f6e68680be,0x71bbc503981a948a93f75713ec,-0x119a62f54d227a398b265c791e,0x22b1ec086834c06886c5dfab0,-0x34c72e948fadf4f255fb84ac,0x3b6697d543b8a43116074e8,-0x2e8dc7f66cda91278bbd3c,0x172b1878a356c5184b3d0,-0x648ceac7ffe8323eabf,0xb2178b12474555a1e,-0x3fa411d87a902d7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 18 37 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 37 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 43 indices rho q2 m2 2 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 43 indices rho q2 m2 2 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x3233a210301700f6911800000,-0x4f3f3652701ddd5adc89754700,0x3c42de3bc10035cf7e0eb49ac40,-0x1d64ad9137ca8f12b622e2e07e80,0xa54c73ee7b03303b7f36f7492dd0,-0x2c96d384a0693e22e509267177e20,0x999913a1ba67cb87d586f4862c050,-0x1b1986e92b6f6aba92dc2a164ceb80,0x3fe00a94065d9cea44edab15a15d64,-0x7f70aecd022cccd70de56b266be188,0xd96bf11f47cced6db88b7258e7e4c4,-0x13f9b56fee213a5f802252d7b068a40,0x19713d4c48313a6e441d47842753ee0,-0x1c30be834f4d7fd995eab026b6b4b80,0x1b3e983002d62212d0c1db47c7af0a0,-0x16fff9df9c42b0d7a5aff72a69c05c0,0x10f7913b785e2f650275865171f3849,-0xaee275eb7e29fc0505d81307dc7762,0x62370e145e3b2695679a0db20843e1,-0x2ff32fa102ad5fa3436e5636e412f0,0x14450a3eaec3ed54072997e025c0b4,-0x76131b64336baa4b46403c06ded38,0x24c4bf205ef847047f80044a80b84,-0x9b5174ac19f3dc4177bb144ea090,0x226140e2a058de393c6c8b290392,-0x64a5521257a42bed3a5e3730b34,0xef24e232f34c227b915d0c9832,-0x1c2612ae0705085efcaa4269d0,0x28b53c9baad262ce6e30a5174,-0x2b47ea6c38083cfcacf4a8d8,0x1fc8c8601de97bda81dc264,-0xeaa1deae372dfb9ddf3b0,0x3a280e493503c5dce7e9,-0x5c44acbee7deb0ea32,0x1cc0a66cf2cb1411]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 18 38 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 38 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 43 indices rho q3 m3 3 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 43 indices rho q3 m3 3 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x2eb6f5c878d70c0000,-0x3df114b7c4062ec000,-0x266ed1bcb23a473000,-0xed45259fede21a500,-0x3fcf7cf2569afc600,-0xcb437c65c257b770,-0x1f0d42db30ec3990,-0x3b8ef60bb0cb078,-0x5ae376db4b87a8,-0x6f3232f894e27,-0x6d5754c32fb9,-0x56395995ffc,-0x3621bf6483,-0x1ab11e6d0,-0xa1bdc7f,-0x2d50b8,-0x8b8d,-0xed]
def m4 : List ℤ := raw_ints% [0x0,-0x4b4d731848228171d9a4000000,0x7565f29320808683b5950296100,-0x582299cb1e60bd1ab8f8bf1e79c0,0x2a6cebbd1a8d2a124dd7a047f5d80,-0xeb5d3a4ce34a9b27192a0c9f41db0,0x3e9acb08e00e561e0cc64a195154e0,-0xd48e04007c8126a45f936deeeec730,0x24f1b8af28024c4d0e294f8be6a2880,-0x55bd7650f8306118baadb33379873fc,0xa856dcfb8b08ebe2b1d1ddea6df1338,-0x11a745085d8f11a0f433fefa1671e19c,0x19814bc41fc96b492360365b5321d3c0,-0x1fe7dad4edc46147516f5bca5653a320,0x22b1d65b1dff6e741101ee3566feaa80,-0x20e1478200636a1c0965e6fe8f6f6360,0x1b31bc79f780c8f40cbe41a956a8fc40,-0x13a2819197a9e02a23bf2ecb6d35ffcf,0xc5dcf56a4c987f8e7980a7a87cce84e,-0x6c81e5eb6d222f5ec80ce81373a6c77,0x33a8e61407f46984738f80bc7bbcf90,-0x154381ab6de7812f2c4cf5e2e83a72c,0x78671d9df94b8d1db35c2856463208,-0x246008bc525b5af0a93b96a44713dc,0x94be2be7007cb863126d45c09f0f0,-0x1fca3b9560b8abcde36a1ca16e79e,0x5996872b1d29bf1fa859d18b70ac,-0xcc31257df500a823e05278fddfe,0x16f4dfd10bb3497151c1d9cddb0,-0x1f8b7036054f886d5fdb3b1b6c,0x1fa8fb720917203b9113f2368,-0x15c4345afc041c63003c44fc,0x94cc9c42a1b221fee4c8d0,-0x21a945e0650ebf997212f,0x2fca64599be695420fe,-0xcfbcc552c0c6d6c7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 18 40 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 40 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 43 indices rho q4 m4 4 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 43 indices rho q4 m4 4 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0xed,0x1]
def r5 : List ℤ := raw_ints% [0x2b3f618a97df161c0000,0x392979385800e23bc000,0x2356a716f93bedb8b000,0xd94216b94416ade9100,0x3a25d186ba3f998a900,0xb830825b0f81850cb0,0x1bf40368868fac47e0,0x3532859b21db53608,0x506ba5a896ddd6e0,0x614341c86b50713,0x5e46b6969c4316,0x48fda5519f49b,0x2cb9b950f7f0,0x1554279031f,0x7b1a35c9e,0x1ff7c33d,0x56bd1c,0x76be]
def m5 : List ℤ := raw_ints% [0x0,0x70f42ca46c33c22ac6760000000,-0xadfb2b6e6db925d6f9dd52b7b700,0x80ff6e5819dd7edeee741a13cf040,-0x3d4db7527ba1a1796305c97c9d6680,0x14f9ef0d8711ed3ba516eb5b7b3aad0,-0x580f4290aedcc3db88c7a23760da020,0x126c85f95fc8ad47cc5ba2b12ed0e550,-0x327e04660c8aeef1defd4e69430ba380,0x736b71079d7a6a5d1a593b1ca29b1ba4,-0xdf1383aa90ce1359ba116a540dd56a08,0x1703bb7aa0d12a42c900dded51d095104,-0x20b0c9148e5ce013f037402e1de8bde40,0x282d4875b55893bba37f9b058b64c6ae0,-0x2ae3a038b988feeed379c9f0728aeaf80,0x27de46472946d03254980c363938688a0,-0x20504141054d2c901d2519140d97231c0,0x16d72655ab82aa183ebb03f48aafeee59,-0xe113929255f6e9b2867db6224a843882,0x788d575e21a908171585b242a1882f71,-0x37fa6fe54f73b91b9e2630ad1f31c9f0,0x1670285b82ee8aa0439627c8f6597df4,-0x7b82eba21e104e29d34a604b7b6fcb8,0x2433cabb979ee49443709f9cd2f8dc4,-0x8f4c5659c60efb30de2e39a2986190,0x1d916dc853911bd7c520dff15ef1b2,-0x50331146a39286429ed607bfe6074,0xaf4aad40e932aa0cd9a6f8fa1852,-0x12d0d4bf4c4dd5968cf4282d0ed0,0x188d859a53a1d66d84ba169fcb4,-0x173eecdf270383370c9d6d5658,0xef2b8aba18f1e365a9cf94a4,-0x5e87e933d58602be7c5e6b0,0x137ec05c09237a818873f9,-0x18beea76db3d7d356852,0x5dc29ddcb2925e6a1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 18 42 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 42 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 43 indices rho q5 m5 5 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 43 indices rho q5 m5 5 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x76be,-0xed,0x1]
def r6 : List ℤ := raw_ints% [-0x15ab0114d27ccf22e80000,-0x1c8fd9188a26770d168000,-0x119a71736bdb232eb9e000,-0x6bd88e3834c50714dc600,-0x1cbfbd7fb683a0ada6300,-0x5aa59a54cf76b20f1c20,-0xdaef8264c2f5b9afa30,-0x19e0d94d78e17815c30,-0x26d52541c007fd8088,-0x2e8cf068e05c015d2,-0x2ca333ed279bcc8b,-0x221a03c9e5251a2,-0x148be950cc9c2d,-0x995fd26ffbbc,-0x35b8b255a95,-0xd632e660a,-0x2231b27b,-0x2aabf6]
def m6 : List ℤ := raw_ints% [0x0,-0xa96e42f6a24da34029b100000000,0x101edfc87243abd1b7e70d56817100,-0xbcf16ff2b68f7f1c051d39e17995c0,0x58ad9c338d4109d3c27db4ab8203580,-0x1df461019dd57cf91b3ecce24f0d58b0,0x7c1633c36633b169f55ce6c8d9a262e0,-0x199b23da04cfa493c3e12ab4338ac1a30,0x452e0a9f87596b3f6023aeccb1666b080,-0x9bcf90e793e3766506a972c2cadef0bbc,0x1288a7295920905885684d7e33320456b8,-0x1e1b99ed36e9fc77163eba1bebd24a1b5c,0x2a0efa0a6a966b4d8e210b900a76835fc0,-0x32cc5966d227756e756924bdee27089720,0x35400099237bd46f64f6c133573240a680,-0x3090bdc9292cfae4c2cea3daf147808b60,0x26956c7fd9b68fb0340c01c8f58df37040,-0x1ab48a0abd0781168a55b73228dad7933f,0x101651bbf09730b3634617823512d6b22e,-0x86abc592f4e7116568ca1b8ca155f8e67,0x3d0037295503e39e5803fa3ac9fa5c090,-0x17d06450c5badc646b93ae6dc96d107ec,0x7f70c5e7fe5ada4c52c395d8fc9ad688,-0x243dd7f69d74824d7ecfd788ffc7a79c,0x8adb5e09c8c236cd99e049cf500c7f0,-0x1ba89b814fdc46da17fc9bd91e3dc7e,0x4830e5debc8092c0d676ccf5a6b96c,-0x974474432f3d790fce7e53862f0de,0xf7ef3883a482d7eabee774dc30b0,-0x133116bbdcc243d9abe1c8b25e2c,0x1120b8f8150cd74ca0971e2f9e8,-0xa4ae62cc1978606b842f208bc,0x3c2640247a72e3bb531e9dd0,-0xb4bdcac93ba8b9f72f2e9f,0xccf1d25ff12f6ce2e5de,-0x2a4c28df1efc0679b7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 18 44 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 44 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 43 indices rho q6 m6 6 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 43 indices rho q6 m6 6 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x2aabf6,0x76be,-0xed,0x1]
def r7 : List ℤ := raw_ints% [0x7c9656ce0eaa3bba9880000,0xa3d7df391ff0d5b88448000,0x64b6f847349c9686061a000,0x267312459a44fabd0d1ae00,0xa370edb61f161202dc7e00,0x20159ff7a7fcc36557b2a0,0x4d2631007e0eb17404a40,0x912869540e40c2512820,0xd88513229651be352a0,0x101b9b6c09ae59b66b2,0xf50f756f35dfaea84,0xb9521193e42b8c0d,0x6e448bc2b71e146,0x32a4bc1b3364af,0x11626d53c0e48,0x437e1adb5b3,0xa638a378e,0xc4fb69f]
def m7 : List ℤ := raw_ints% [0x0,0xfe256471f37474e03e89800000000,-0x17e858026ddd551e938a63885a12700,0x114f14f221a1d68d1ef2c3eb0fec7440,-0x8069d766c74cba42c7ec5c32e350ce80,0x2ad61c53658529b33a6fe67e125cff7d0,-0xaf29477b04085ad53b6a375ce3f05e220,0x23a9a40a25d7a8cc6d4963dd52a3df5a50,-0x5f03cbb1b30453cb5671753678725bdb80,0xd2eb1eac902f3fec888efd8dc6b8463de4,-0x18b6a7a0aef1c1bdd031a63625623b97a88,0x278569a62024af88db939e4d02e6d3c0144,-0x364fb2c72247c801472d202fe1040e57240,0x407bed6b031eacb5524786906f3a4e1d6e0,-0x4265756650852ba19c37587b84e6f895380,0x3b6da224336f86fc785a986bfbb938020a0,-0x2e4a7ecd78e9353150cdac8d6b7ad2d9dc0,0x1f616647e34807ef9466cb87c7e811df569,-0x127e393d52d587cbb92b52a521bec1f6ba2,0x974122356e172c59e45e596e97015bc401,-0x42d78d24485340ed6bda9207247ed2f0f0,0x196abb8cb7cd842bcd994ce395382fcf34,-0x843eb3f419dce258dd96248b17f508438,0x247d043baed2e7165d1da4c9d1484f404,-0x8750edd4c7d592eb06d0cddff0113290,0x1a041aeb894b4454fa663a44818361d2,-0x415452dbd8cbc7b6ae5fd81eab049b4,0x83315c8d8d47f09678030ab7e73a72,-0xcd2120103de6a98299729a95b03d0,0xf0fd430912d8da63ca5ff3ec9bf4,-0xca96cd4917e75991900b1515bd8,0x71aab90316fe185d1bae56cae4,-0x2653a9eba665f2ea7d88989b0,0x68c55b7ceb72105409f3109,-0x6a0c27ac620f0e5462872,0x131293c53c2562e5231]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 18 46 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 46 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 43 indices rho q7 m7 7 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 43 indices rho q7 m7 7 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r8 : List ℤ := raw_ints% [-0x23f1f4e54e68c58a418740000,-0x2f2cd28727b60f4d6aa014000,-0x1ceebf445f4272cfd16125000,-0xb0468645afe76ded6cd1db00,-0x2eb2555c9f09cc39e41e4c00,-0x92303baabbe9af6e9981090,-0x15e34c0a70beb22fd4c24d0,-0x29018f21a3bf83dbf86dc8,-0x3cdce30ceef01ef600928,-0x48075214f36fc3ca1279,-0x4406a3993488294925d,-0x3307a163375baa74d8,-0x1e11ecd42c988b757,-0xda5c71128b90110,-0x49db928dc025ab,-0x119663173c20c,-0x2a438af7a29,-0x30755cfbb]
def m8 : List ℤ := raw_ints% [0x0,-0x17d3816aaed2eaf505dce4000000000,0x2377effeec583f8d9cdc4f9e017a8100,-0x196362ddc964985b4b4b9f715223e71c0,0xba25e180a5c1b26e95e5cc874a59e8d80,-0x3d57c98c075ce0addf7e417f75d69043b0,0xf7af76ba242e6ffce4451542e6138850e0,-0x31c57c227887a21761e3560b65d0dc89d30,0x82cf5103e63b10fd01e38f54c0a71abb880,-0x11e4aa667dfc981e6f1a4cf302e5f8cd9f7c,0x210db31d575dca0ed6028e9da35c08f4d238,-0x340cfa60bded1de6d4af2b85bf0f4aa5711c,0x46637d8841d9cd99dd5aceb8800bd6a5abc0,-0x522d96f53b9729c7db517dbb7930dc3e4b20,0x5322ab17b7abfede7a4170cfa274b1ab6280,-0x490b6ed98902d55005b1745e29ce8068b360,0x37cc6dd799b028c973375ee82eafeb052440,-0x250e2deaaae35f2e11c471d9c40868b66daf,0x155e0da3d79e16f309d808e635e865fa3a0e,-0xaac6eb1afcdf3fe0d73b90069186164df57,0x49a3a91c906d2711b6d1c8f6c8d1c18c190,-0x1b47030b460e0cc942805a53e0613f9b4ac,0x89fecbd7142d20fc3798658f8f98d64308,-0x24f1113838fde855ad9d934a13a1d3b75c,0x8497e76eb0279af1d02b2a5231f1d0ef0,-0x189a540998c70f274b28e0826382e7f5e,0x3b6cf75559c3c7ed77ad35ba0ddf4e2c,-0x7255993ffe943d5836a7c7a0e6d91be,0xaa76aafa8b4b552f04e57adf02b3b0,-0xbddb312efdfce96b05035d92c8cec,0x963b2cb6fbd011cd5ebf3b25b868,-0x4ea1a0daa8689c0344cc44ac87c,0x1873cf9a77cd813e7634f9c2d0,-0x3cc05986eaf8282bb0bba30f,0x36da86e87306ddf7a618be,-0x898a292eb5a7bdcdba7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 18 48 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 48 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 43 indices rho q8 m8 8 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 43 indices rho q8 m8 8 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r9 : List ℤ := raw_ints% [0x8d7b8ab991c5c7e123c9c40000,0xb95a79b90d66faf951f8f24000,0x717391c51f4502da6c67ced000,0x2b1ad1e2082edd417b29ec3700,0xb63e1e89283fb5aa2a5adc700,0x238eb1a93c9f96db3f77842d0,0x54e88a447ffacd6caa7f9ea0,0x9e7e759ec7111064f975e58,0xea4384f801db98ecbf2ba0,0x113e95b3af446e994feeb5,0x10320b73bf0566658a372,0xc11dea621157fda78ef,0x70eae4e0c6b223759c,0x32c62c01a73a9d297,0x10faf2db87014672,0x3fcb53c52f8f79,0x969c1abf0bc0,0xa8c5d5eaa4]
def m9 : List ℤ := raw_ints% [0x0,0x23bd4220063c606f88cb560000000000,-0x34a35337995dfb260ea4c342222019700,0x2543a7c6e9d964f12c2cb83c218b9c3840,-0x10e1dd5526660ae9920f47b4aaf10cab680,0x57f6e5d82cc5503b2e07fdabf36076b14d0,-0x15ed4bf5ab5d47f7690d37e18da3d4464420,0x459a3458e0c11f31618ec4766c5644cb1f50,-0xb4832adbc867236e9311bce3b47132e79380,0x185a27d6155c80931df5e6d2668fcea550424,-0x2c56e6af1a0921293514fca18380c6c919308,0x44c6ec5492fa0caccde5cd80cbbbeb88a3584,-0x5b8cf2cf31463f8909a86c83192f39b5a4640,0x692153c71b8ccf88949cd99895e69f4db82e0,-0x6885e7289d794bc6325e271526155212f3780,0x5a2c53920cd493f4667daa8d636ec5e99b8a0,-0x439189aa6f168cdc566d1b68fd9cd9887c9c0,0x2bf7aa730453a3facb86c3e632d48bdaa5d79,-0x18cfeab0f99a0f4d8555415684e8a9250b0c2,0xc1d123c0c8008357ed455d57ff3ee3b79191,-0x518ee204b94ce999d39213a275afebd687f0,0x1d6e989f7fcc981145b56142b18b38fbf474,-0x90c796c1db6f6a85eaacd6fc796d39003b8,0x259aa2f165e67173ce0be3127269c847e44,-0x829f921d8bc5efbff6d1c6ed8fe6951390,0x17635bc400cc2afe09fa9d660fe68273f2,-0x36536c11a275577e4ad62579e17d806f4,0x641ba2c272bfe0f056b9a5f4c2921e92,-0x8e4135e6126d566c2c3f125401a48d0,0x961e26bee022ec4d98deb85ff56f34,-0x6fbaf1e4951cc84b06d2c44f03958,0x3681cac51b053f82c2dcf8d9a524,-0xf9e34c5da2a45bc18245a55cb0,0x233c07901bc5ad1354aab2f19,-0x1c5cd2c9b636c44d458ca92,0x3df6b32c28585931e6c1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 18 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 43 indices rho q9 m9 9 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 43 indices rho q9 m9 9 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r10 : List ℤ := raw_ints% [-0x1ecc2b1fbe3bc89a0af6bbb00000,-0x284898552cc4690024bca7af0000,-0x189d128ef08ab3b7974b5e888000,-0x9555840e97bce14c1dbef90e400,-0x275fccde2e4e30ac7b4f3aaa100,-0x7a9d7c8263bbbdeed6d8601cc0,-0x123fc7ec35a6e409b01e558170,-0x21f54f9b4629ac3afc9e4b840,-0x32039ba33abdc669e69cab88,-0x3aaaa7b3cef28230a8f0bdc,-0x36d739b5aa7256bb01b42f,-0x28a63b6ddc2e9809e779e,-0x179e2811520c7196c901,-0xa8a63375db37e1904c,-0x37e5c9166c566aec1,-0xcfbc19fd0feb9be,-0x1e3e87a001b997,-0x21538163acfc]
def m10 : List ℤ := raw_ints% [0x0,-0x359be330095a90a74d310100000000000,0x4e2526f5a4e5c8b670c8f1e5910e249100,-0x36bb8021a87f1e86dcc81b952dfdb090dc0,0x1885b12fc4abcb393d9815dcd2ddfab26580,-0x7e4eb5be6b84178f28aea6c3267e4837deb0,0x1f1c17b16f02384a18ed5c14330f1db191ee0,-0x61871c48d94438a150631173c11a9bf875030,0xf9ac49f7b9623dfb6fccc464b986783b94080,-0x213aac0c3ae428ac4d613ac0dccbef5963ef3c,0x3ba704fa2231bda2c1c9c2548127aedbd605b8,-0x5b2b9ed195081a5d3e5f42b73aa61c8659a2dc,0x777dd73e699bc51b0ddf334b89ba914d6eb7c0,-0x870029bc17e55818b9a71e7d308ec2f306bf20,0x83f1998bf60d13e687aebdb18e24427e22de80,-0x6fcb9e59d70c923cc9ca2a07d8f2ce634ddb60,0x5230d686a7c9dac05a98ee8a94f411045a1840,-0x346a582395fea7b37c8ff1b813144a2368ff1f,0x1cf42e5fae8048bf00f95dd73688dff3a15fee,-0xdd148bf6c1bb7cb4d6dc39387f96a56234f47,0x5acc30e5348a2de3573f77e7dc1f00cd3d290,-0x1feca9d88b81f74d4974767e3b096f1b06d6c,0x98b49541aa12e3012220e8551529f1a2f788,-0x267b3aeb60dc89e6d1b9162310fbe97d031c,0x815af67421d90fa4246bbc9f998be97c5f0,-0x1658a41c6f993f67a55b6f310771637b03e,0x31e7716f6d3511ee5977946ade85fdeeec,-0x580bcd4c244d4695fe8b4a75b6ac6a09e,0x7731a955f593c0b0d36c44ef74c366b0,-0x771b76220641a3e821af39fe5cc67ac,0x5352d6ed51e2fe2a3d11bdd15fdee8,-0x25db0793f46feaaddcae9d55e443c,0x9fc3691148058c6c664fc8137d0,-0x147035784661d037ad0992ee7f,0xea8d2b915af11c1cfe8999e,-0x1be75981663aba955ec97]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 18 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 43 indices rho q10 m10 10 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 43 indices rho q10 m10 10 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r11 : List ℤ := raw_ints% [0x614d29ce9bee0ec9ebd13bfd00000,0x7f17bf8e1a1ae5316c0fb03550000,0x4d889cbcc7e0372cc52941aa44000,0x1d597e081b82c387c96fdb471ec00,0x7b93a1d1775f9744edb9c47e0400,0x180003d8b6483e564fb4aa3d3140,0x390392031c96445de554cdaa900,0x69cdeacbf0e83a278b27764ab0,0x9b5a308268caf3d7377e1d8e0,0xb598452cd15c51200751ca5c,0xa914210dfcb26787ed592e0,0x7cc117df47bc78be26e341,0x481a09c6358b14dc09bf2,0x1ffb1ca32c2784f8a957,0xa85e49a5c09706f81c,0x26c4f6a98a6bc408f,0x595e9a45ccfdfb2,0x6137a639fcd0d]
def m11 : List ℤ := raw_ints% [0x0,0x5069d4c80e07d8faf3c981800000000000,-0x740cf701b1b0580ddbbb018bc0845490700,0x50711d4261f89ffe20af1f47c90b8dd03c40,-0x23a7952371d41c5a9d3772f892800f4331e80,0xb599d6ecd05058282eac80cf39c8ea29201d0,-0x2c35c47ad157e29c9119033283e5268640c620,0x88ec423e284661c9f2a7ea2dfd7f993f493450,-0x15a1c467286dca7c82a9ef14e6cbfe94716cb80,0x2d755171126316c25faf906cb6411e57911ae64,-0x507bc3c6d963304e9446ac70649c4de004a3388,0x793c6381837c3bf295dfb1e41f4d16159a42dc4,-0x9c7eea6aedf48524b35dc591ce443c67ffa5a40,0xae0025c4557cbdb7e98e13c361c94fcd6ff6ee0,-0xa737df0049ab9a0064d421bf2e44fbf2f785b80,0x8b2f76b4df506cb6b5964637954fb23ab1d50a0,-0x646ba54397c8630908426890e2e88cd734cb5c0,0x3ec6ba01cd4336aea08db58a854ddac48c83689,-0x21f3150339f05e0471f0357098ea9390f0527e2,0xfd6e66f26a79ee2cdad32f70a11ca8300d2821,-0x65990d7e979bc775c8bedc9dfa08ab2e738ef0,0x22ce8a9fbdf023348f7e11f458cd3bf7292db4,-0xa1e6e6e1e944ae16680d5024103d2f2b8fb38,0x2795396e2f47d5331e59d0969425252266c84,-0x80c05e0f492acaf025ce3f13a16057ed0490,0x1574bcce01926cbe233e6f3bb78665cc4812,-0x2e0e83229d52825826d4a80d0eb1692d834,0x4dc5d7fc8dad5492a04628fab6dd8ce4b2,-0x6441f14254cb5f9483cb8c24632d3ddd0,0x5ecfebc57d946c6b0307acdfc4afb674,-0x3e4c4a38998907ec6d31ac335ef6ed8,0x1a5628f6cca509e4e5fa6d230a6364,-0x663b3336bc04505ebe7ef6745fb0,0xbdb48ca2c75a17fefc83647e29,-0x792ea9ee4cdf65c4aea36eb2,0xc8f7e6a545895a14f3451]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 18 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 43 indices rho q11 m11 11 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 43 indices rho q11 m11 11 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r12 : List ℤ := raw_ints% [-0x11bd7ac4fc1a5e4b9f326cb879c0000,-0x172482b3a16e239c441fc1d404fc000,-0xe19407c9199c2e8f632683c3b87000,-0x55423d61771d72f5edf2f299322100,-0x1665e57a28656a3e8bdd4865092200,-0x45778780fe76ed02c3bdc966afcb0,-0xa4ac61a8137e803a953f7945e010,-0x130de47d4ad3b3251c16b7dac598,-0x1be7133f16bbd6bb3569d3113a8,-0x20848e472fa3f0d74a3bd872bb,-0x1e2c57ad881a658198b854501,-0x162d38494e4d416fb6ea25f4,-0xcc28349fd4fe78e474882b,-0x5a167cdbbe961c1a9c0f0,-0x1d76f592788b90ef0ed7,-0x6bca0531205cd61d20,-0xf662f311cf6051c5,-0x10950be36589979]
def m12 : List ℤ := raw_ints% [0x0,-0x789ebf2c150bc5786dae424000000000000,0xac65f9934e6689df52440af384be398fa100,-0x764dc4cc7ff0311f731c123da3890fdb569c0,0x33e40351da0c2b1b9a33c5e10e056a0233bd80,-0x1056f2bb736a88774469711664573827faf29b0,0x3eed4eccf5e17b711d7f1c3517255e86b62cce0,-0xc098e6738e647e2a0dfe93e668d214d584b3330,0x1e0dbac58c3d51a3781d0368482a55145ef74880,-0x3e581972892c1c01ffb7739b25b5168edbfdbafc,0x6ce4bfb1e6788477cac3ea45f8369ccd1e5b7138,-0xa1b6fbbc7c8c25580b8b72b5677f3cff2224709c,0xcda6724f7a951b07cef2df43d1e58422641283c0,-0xe11528ee7401e070bcc5375e1a3f0e3b6f53f320,0xd4bf628372ca4cc2628d2ffdbffabc691e4f1a80,-0xae005bc1866e14ed224667dc7bf8db47243e0360,0x7b3a219f3ebe17ca176a8a002c57b9babe064c40,-0x4b86f0aa041e198de883c3eec2f707fe34b4b78f,0x27fec609f6920ce736ad3f3af8390ff821f203ce,-0x123ee3d05695b47b08264ebdd6a5fb43ebf6ce37,0x723fbb1ce7d387468b666e36fd3901f522ff390,-0x26241eea704dd838afbab9b031c2878d90bf22c,0xac861a39bd18b4f0c554ee5bbedefc72a97408,-0x28ebe499cd744227b571c6f11b840738754adc,0x80c8f074601c6a775fe5dc6393c87afafecf0,-0x14b320c154d00d6248bd7aa6a77ed68864f1e,0x2ab2ba12e6264759856fcafdc98904cf5bac,-0x44fbf796180cd454fc5c1d007de86bafd7e,0x54a40f9ca0f25d536cdb44632e8a4149b0,-0x4bb4dc9a6f65fbfca243389f2c388ae6c,0x2eb0645c6530253c08fea9ce8c07ed68,-0x125a01de2dd29921b94457b29343bfc,0x41774c8b048da545737a6edc1fcd0,-0x6e0dd8d6a2af6bc1a1a817280ef,0x3e95a4bf1d360a49a73cf487e,-0x5a6d62743a171381049c87]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 18 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 43 indices rho q12 m12 12 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 43 indices rho q12 m12 12 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r13 : List ℤ := raw_ints% [0x306a204f08e9e68320ca6dc3d0ac0000,0x3f1640227740c62a120e591f553cc000,0x26628e210db690409c0b658d5705f000,0xe7ce295d6e4046ae352a0140dcb8d00,0x3ccdc4c15a85740237cae1678387500,0xbc4312694a7cefed0933ef918e81f0,0x1bd70cf4296e8a68c85815b7216960,0x336eff853e55a80d1675a9701af28,0x4b243c294eba9bbacef2d59e3260,0x5756f5d9bb77b0eecf66cb4d5e7,0x50cd5556140efe67c852a119ce,0x3b303b0b83a9b90ca63e90703,0x21ecdc5400eb6a0ef64d6948,0xee793a14cbdee220cfd36f,0x4d9a5c458e62882f6f646,0x11a398bc68228d81acf5,0x280abc0adf990d5264,0x2ac40c3b6b2ef11a]
def m13 : List ℤ := raw_ints% [0x0,0xb4ee1ec21f91a834a4856360000000000000,-0x1002f98850f28f7221fdca4d5fed172be77700,0xae1882506f566825128168a66110a64b4c8040,-0x4b975b51165752a03c89b4c8106abcc54720680,0x178d59097732bbedec5a2a98bfd58c6318a1bed0,-0x59b531b291ffb17c8b063ef2d07c6b936b176820,0x10f6a31c20eda1d62c2eb5314cb093400edfe9950,-0x29d834bc211eef84414f44036f02560503fa18380,0x55b68142ceedff5f6309b108d87b004b1982a7ca4,-0x93bcd317d35efd361cb8c380e51de583970fbdc08,0xd85d02446a66f59831cca7da35d7d53a13fc62a04,-0x10f232196d49bdc40180d06d47481f94c24749ae40,0x12433385a6a4fe0de3a0c88fbb86a2ae9391239ae0,-0x10fb4ed4d66588cfd4958b303cfc4a4928845cbf80,0xda68582f4e30825188196ef8dd9ae3d7afb64e8a0,-0x97dbcab8f34440186b7ec21e8fb208f8ab71861c0,0x5b45f69037524a8edf1fc9e8749a102f7060c9099,-0x2f55f1c60faa6bdcaab6111eb468ff4d69d5bf102,0x151e21fd64c34fba4b8a1a2fcd9f9cbf2471717b1,-0x811a2146a78b56f73d4049c0b9d86d5a9ed105f0,0x2a005bab68eb55eae03495cc7e61b72ed1aebaf4,-0xb8c12bde01c3d8cb030d7e77f253311b91eeab8,0x2a8375356fb5307ff938497974a7ef76a4efec4,-0x817067cc31dd6c89622813ded99ab5ddba0590,0x14100d923da0833ce1975cc7f6933df48afe32,-0x27c1ea7d7994081432742ad481701e1bdfd74,0x3d6f0064cc0746b2b3b72d16ebab7a7bacd2,-0x47b55383b7d99b970c3cf6b41aa5eccc2d0,0x3ca0ad66c5f2733cd4cbc325b033d2b1b4,-0x2311912dae3fcfcc9a4eff61aec847c58,0xcce525cd3036699bc4b3fa9042745a4,-0x29f31dd5a490933184c97cf45992b0,0x3fd8334cbb31f94ae1201e7c2e39,-0x204f0ee8f6f81ffed8c8ce34d2,0x28ac30b405491add705cae1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 18 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 43 indices rho q13 m13 13 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 43 indices rho q13 m13 13 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r14 : List ℤ := raw_ints% [-0x7cdcaa27c8ee1150e9e0cc6e023380000,-0xa2892cf6149b15c066de4ac9d52d38000,-0x62c86d784b55023ce8cece3b23a2e2000,-0x253ce3914aa864087472bae758ab9d200,-0x9c11a3e97b6104e1248ab98ebb748f00,-0x1e27df7e319fc31ea48ddc729e809c60,-0x473b18890bff708273b7ce9a1a690b0,-0x8359fdb9030491c7194b6d0be3bbd0,-0xbf7fc067655baf47af7abf37a9588,-0xde1205a782e8cca98d8ff4ae85d6,-0xccea0aec208958fb5a20f9a8fd3,-0x95a9be04c46e5f51b763ff93da,-0x557fd272d11b39300289553d5,-0x256bf8553664d1d43029d67c,-0xc20102cc5eed32c11b46ed,-0x2be0dcd49bc7460fb2832,-0x6308ba46362264d33b3,-0x690ed49e2371b70f2]
def m14 : List ℤ := raw_ints% [0x0,-0x10f652e232f5a7c4ef6c815100000000000000,0x17ccfede13b7b3caab4356c97864d14f1cbb100,-0x1005b427fbffeb3257b9160097881ea5c3df85c0,0x6e37d71c146be9f341c4f27c71e7426b7bfa9580,-0x21fd696bc003a37b06fb9b2b3ed814b5a945124b0,0x8014d626077d51f70de91ab3fc8a199ceecb35ae0,-0x17f2f9309a2f8a52547c42d0ce63a003de15674630,0x3a6291552ba8a4bf1f7016bc9928a01522fc2dd080,-0x76201c1bcf9b068d93c6b487a6aada6ee7eae2c2bc,0xc8fa85174ded78de0191d1570560207d2c8c4894b8,-0x1225729d2a8dfe04dc30d0f5a2d0684c58a8a0f9a5c,0x166a329b8bb3c0b5882a450e3f6622e60ef5dbd0fc0,-0x17ca8ccce366a85965bec8c2e60ec7e3eb1c627e720,0x15c4e29c262260431e6e74b12afbac1643a48081680,-0x1133c8d7a3e99c3e4da7e24bd026f4be6e017f72b60,0xbbed1bb66150a2e65767a88826bc7a08bfd00dc040,-0x6ec903a7383d9f0c60fc88f3cbba4fac96700606ff,0x38472a59ddcc55132dccdd895c0685beae950805ae,-0x188e61f38989ddb835d6cd20ce5240d943b3ba4c27,0x9295532c450de8feb30bee7428c51fd56fb0e2490,-0x2e79e432d26571662c747bd7fd119462e3f3702ec,0xc6cfbc5ee2b0da8db1a3f346bd386aedba923888,-0x2c61295abc4abe6e448c6885364a876132424e9c,0x82b4d974b51cce13ec43fd19768510a493c83f0,-0x138863071373a5755dd7e06a18fd10441573bfe,0x252cf0cd34348c9abf11c94646d4a1a00c546c,-0x36eb6a84664f1209bae35e02e9546e00d885e,0x3cf4a4bf5222caaee45c650a604ef67f5cb0,-0x30afa41af2c7d57bbbec903e3ca5ccc212c,0x1a650d44277eff161bc9053223dfd463e8,-0x8f2a03402978467791308e1529e86fbc,0x1ae542c90d9a8563e97aa25908111d0,-0x2508f9044e507ff9c9fdc3c76ca5f,0x10ac298d636684de41df5dd055e,-0x124972c40097638aaef2db77]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 18 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 43 indices rho q14 m14 14 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 43 indices rho q14 m14 14 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r15 : List ℤ := raw_ints% [0x132bbf9d0974493fc4edb96a29489580000,0x18ee9b764230c4bc5bb60f4e55068f98000,0xf2324d46abefa6df5077c77e2ef977e000,0x5b32946ef74af20d6ce2a70269e0cfda00,0x17dbfe5e64794b52d2e3003639260f5a00,0x49a95a4965601a9e8ea989c32c487d8e0,0xadbbef7d5d0365a37c8f6c790c970fc0,0x13fd64aadea2046f2c89217e3f709dc0,0x1d16efd1874ffcb032c595f4448c420,0x21aa0bfd32ff5ed218330cc4466f96,0x1efe07226afca71f18cf35c83b13c,0x1693e4ff7df9f30d88811894c035,0xcdc65d80b7e636626fb0a2529e,0x59c55247de560201bc1fa0f5f,0x1cfab9f896ac786dd5fa4bf0,0x686ceeb15e1442e5e2d8ab,0xea8aa9b51308253f6ed6,0xf766f72227e89ae40b]
def m15 : List ℤ := raw_ints% [0x0,0x19717c534c707ba76722c1f9800000000000000,-0x2363c29e6b609ad53dca92b8fad0ece1b94ce700,0x179b649eae986350036856de6d2327a7299150440,-0xa0d9f60fdf9e7325ef84c79bddb289ac2bbef6e80,0x311cb4baa7962dc8b54f531665821ffe6584c74bd0,-0xb7249646fb57ed44bd9d8f84306a836f197b4c2a20,0x21df3bfcef39f243d54308c1e96f7253d5759604e50,-0x51a20976a2fe7b6c48f500bbcd1b298bc0e2dffbb80,0xa32dfae8a6dc279977a5e5456589a25c1ccb9f1aee4,-0x11221125ad70245c1a144e6e471723b6036c92d70c88,0x186bf6edcf2bb4b6ef9cad480084a899b42e6c506a44,-0x1dbe25e17ba310e56dbb5d740ee92ca44d037b5c4240,0x1f19a178794b7926912a80510b90f2a12776458e06e0,-0x1c023c6ccc5e001f817218844191c16c72eba6746380,0x15c34a5a02545dcbc6795a1a061c27c27c7c543a80a0,-0xe98418a5a20a16e084eb2a69629d88aae992886cdc0,0x870bc4259870cb08ac930892b932d661dccd5cd7ba9,-0x43352eac0250a861dd48cb4ff0a6f3c84eed6662c22,0x1caf7ce36925c0fe3ac165b0127d5e046a94de8f041,-0xa735f1ec6083aa7cff2277975c770292442525ecf0,0x33abca6df21e47d1696fcb9a97ee62bbc0138fdc34,-0xd6f387745b788998f0a01d2a6581fb2d5327d5238,0x2e8b5d504dac02120f7ecbd122bf88798ea7e7504,-0x84968f5d21ce1e835602826010bc1d125b2d1690,0x131988d47be923a4f42ef7e5e709b93f3dc2b652,-0x22e722d6040212afc207a10c1da1b10964ab6b4,0x3146fd0e64d82cda3761e48bc43bf3225c96f2,-0x33fb1c250983240321b53152077edd9a9f7d0,0x2732be7a5fdbba11f246377156488ec1a0f4,-0x13e77b7134697007ce718c4d62d9a6ce1d8,0x642622acdd872cbf5d3b154cde08a8be4,-0x114073f13b086b197f9a858204e7f5b0,0x157b2bb72b2e63670b7a8fb46c4f49,-0x899a4c617dd7d0d06eb07733cf2,0x8380f987d5b06eafbec63a71]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 18 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 43 indices rho q15 m15 15 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 43 indices rho q15 m15 15 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r16 : List ℤ := raw_ints% [-0x2d2551231d3104fe4609398379efed840000,-0x3aa9c8dd9d6cdda4dd5b8c1d2e78ddaa4000,-0x239577e74a14ea44867edb5cd4925ed59000,-0xd62a011340f861c2e0d9e939e5fcaee3700,-0x37f7b28c5fb85c8d310b0d83f7f5215a800,-0xac93dfc4964171bbabdfd0fc4e2c7547d0,-0x1967b31f7956a64a78b17590f10f5de350,-0x2eb324e25e6e4d03122cfb454ba33c0e8,-0x43d8a161fb0b9a6da7cbf1c42f58e528,-0x4e5f38bb2619e28456752b7306a25ed,-0x4801317597d56a3cf743ac50ebf7a5,-0x3455ff2fe7059baeae70de6b4e550,-0x1dbc81d4c62051f5913f557442ff,-0xcef8878c269471d03f0e3a3870,-0x42991deb9e87ecdcf963e2003,-0xef1ad3f21293725cf04d6f4,-0x216cac59e5f05407d55861,-0x23168da126765b8f1927]
def m16 : List ℤ := raw_ints% [0x0,-0x262a3a7cf2a8b97b1ab422f64000000000000000,0x34a3062280e7ab256439dbdcf52c54847a5e8c100,-0x22cd7672615b401789d72723e07ad2f27fc0e361c0,0xeaf388d8f29662544130280b2316456645e35eed80,-0x470b9bcac7010da032945adb3ab2d790509fd28cfb0,0x10641f03b937b7aebba14c4b5e4c51b74e7411b8c8e0,-0x2ffd749177d82ad73b0545c690c337f30990635e8930,0x725eb6d47e402c3a98aff7d57a2b2d2b6ee5fe24d880,-0xe1f0947e1483bf7e5c952604651ea87337e1e216c67c,0x176df8eede52ed17d8b049c8f7c9de92705a82c78f038,-0x20f61e58ea730a0cdd0d45483249662e10fb52140e01c,0x2796e9f255ce6ec21decb7aa69a36d4efdcf1df3a5bc0,-0x28ca9a2281a0bcc74b0b641f1ddad008dbaa8d5549b20,0x242ab72ab090507601c06bb0c9fc32f60ede8fc45d280,-0x1ba34fed650874ea94959f0abdbd2a0c3a3689d875360,0x12356082def8009b43128379fa4a14b450449cef47440,-0xa55045c1476e266607810e48179486a04e41eae05d6f,0x509c6f1477ffc30a038cf2303debbe8589c9497d458e,-0x21a8ef7f43406ce5eb140381334a4cb68cdd2987b917,0xbf9da1751df2ab8c55207e98db566542332567f6590,-0x39b67a098ea39e401b6c33f6e853b3189d633305fac,0xe97a28dc69660fcddc7f55b17642098d85403dc508,-0x3109ab19302e7b292ba38d09a3218e33f69bedce5c,0x8717efe4705b2434ec164aefb3e35857c05e48af0,-0x12c159664372cf07b4e16e2f8aa1b0280d97d56de,0x20e5dd8b23270c80dcc2a5247b4d7aac5589992c,-0x2c5ef97cb59963c6d9a7b1866bddfa3ab37213e,0x2c765636dbb5e41e663a77dcab7e2049309fb0,-0x1fa2ee04add068edc9ec5d0d4bc98b3757fec,0xf0949fa8fa6c95a9c9b5d8fdb1e2bd3c268,-0x4621d3d7014df56cf048d6dcf5495a9f7c,0xb11f5d3755562f0bbc8415a1753376d0,-0xc75340b1b44eb2e9b8bbb1ca8b3acf,0x46f3881e5bad3b42a8887ad2b03e,-0x3b152e5ab61da1bb349919967]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 18 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 43 indices rho q16 m16 16 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 43 indices rho q16 m16 16 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r17 : List ℤ := raw_ints% [0x667212bb5348847ab5ab4b77ebb1ceed40000,0x85045808ad02acb1bc84365553be4d45b4000,0x509dfad2ff4e9abc8c9903179f432c6de1000,0x1e4c03dc167ec24e587fa8d4cdd64ec679300,0x7e8d3363e4f048edefd975486037132ef300,0x185ca719f3d47223d7662d9b8ed021c13a10,0x394f895cbc56d3799cd43cc09e69e8c0c20,0x6934fae024c78a14a7db6b02fedc3ad878,0x989e8c696d78a235b00f4dfdae81c4a20,0xb001eb7c684b10e3fcd350a2b8025ba9,0xa169f15ab455763f016661ef61cda2a,0x7515d2f47297c9d41d0084a1b63ad7,0x426048adb4ee3030d5c63a260d4f4,0x1ccd40acf780ca89ca3cedc987a7,0x93dd44560447e37127ff5fdc1a,0x2112e3019964911d0da81b7b1,0x49b4fc2fd691376389ae808,0x4d0e800bafaa9c11f1120]
def m17 : List ℤ := raw_ints% [0x0,0x393f57bb6bfd1638a80e347160000000000000000,-0x4e4fc65fc32038e2092d297a335fb97e6fe7e95700,0x33564290ba512f720f692ed8793274e99f2546dc840,-0x1577b2b337e6c6af5202a96c9a00bff221b57f935680,0x66e4296cbfa1e70e0a8c37b6b3dbb425a8ebfeffa8d0,-0x17815a250c497c2328930c99da0c76957d50c20810c20,0x441be04f39b27d778b3d91374007a8b7d62f2f8335350,-0xa08deca4184d0e38d73dee6cdff8c536c38de4e297380,0x1398c137baec3441fee728aa97747c3dd78231eb9d8524,-0x201f1525dc2cd81bd5c41dd528136753792846c8d44508,0x2c9ca3bedc64a7abd86cd6a5d8ec0bd143d11267672e84,-0x34db7d6b94d0c2001fa54f0f48d761ed08cc35f1c61640,0x35adf7a26f755a82be371697f9dfeee31c54a36df4b2e0,-0x2eddd4cb41e9eea2d584f5cc0ed3e707876e0ee4f74780,0x233b220066b1879f2c54a991f37d84c18ec74f2fd818a0,-0x16ce96b5bb0cee9393b20b37fb6fec163ab1c30573f9c0,0xcb33c90743284b2c3e6872854841b6cb616ad9cb207b9,-0x611a2997c4ef1e2ec241d6d76053f9ea89ca0a9a6f942,0x27abcf743edad31f3044f58e54dea331c09686dbf41d1,-0xdc91d6b9dc46edff01195bbfa1b576fb3b862e9943f0,0x40c0d870185d82f26deb65bca95550d973b64d9bd174,-0xfebf3e4a36d359fb148f52aabeefda5b147c5f7b1b8,0x33e5117381b5c68a71fa2b9b59ac5eb7465c0910f44,-0x8a3d728f9debbe3ac4340c9a57f8376189d2073790,0x127e10ad89d26d715542972b2d50cba5119ef19072,-0x1f20291a2f078921aa830c5eb598cb5ebcaee43f4,0x2816aa01610921aaf14f41631cf7df4b7707c312,-0x2624137d87ccc79e809b161ceaf8a5965a07cd0,0x19978d74cd3195d51ab51b7b4f62ec994bc434,-0xb609e83278a331d4813601f67f1bdf2e1f58,0x31288ebfef09ffa5d0becfc124c1cea7624,-0x71b1222d967cb986d12cdc3ba82e288b0,0x7393fd3b8b3cd42632c8268af87f159,-0x2491dc21aaf46a4c07e61373ea712,0x1a892652ac1d6b159ae4821301]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 18 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 43 indices rho q17 m17 17 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 43 indices rho q17 m17 17 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r18 : List ℤ := raw_ints% [-0xe0fad4c5a1e4a6564e2c6340b72bd6ad800000,-0x123e93530ae826cef86d682110f003631c40000,-0xb0c7e065b40fe8aed7cad977cd9a0ffebac000,-0x42615d1960f014b6113ad53d7768e1344b9000,-0x1150459aa012550e89b41d190989dbefb72d00,-0x3545fc903049d0ba98be672ac1143b1866b00,-0x7d2f4ec02c70ef2a0112c57bc784f27ea7f0,-0xe58670760ced0a3781cc07cd93f168ccae0,-0x14c840f86e03a4ed7d975048f1d5eb09688,-0x17ee7ced174c84a731fe10509ae38e95c0,-0x15e9575767e55b758392895efdab83777,-0xfdd83fefc304764ed4458425ed66e56,-0x8f9dfbe150c4b1b2e9f162eab464a9,-0x3e2dcd2788e03fbab014a417d324c,-0x13e6bfba4fcc0a8c502a799b6b19,-0x47062feb0de6b0d83c29487566,-0x9dc854ee9889ac0e18e500cf,-0xa45d15ce5e1b8b4040c1d8]
def m18 : List ℤ := raw_ints% [0x0,-0x55df039921fba154fc154eaa100000000000000000,0x748ad17ee73b1e0f5ad7e7c286419aa5c0dd5f6d100,-0x4bc4ce91fbfc97fc48990316bb83e3ddbf1595dcfdc0,0x1f6903a35f11edbe87b79ca7e5dac8f79c9a7f138c580,-0x952da32ff88fd22f5400d505aeab5bcf96f0b2ff12ab0,0x21c114dc2d1f8dfe9a48b7e11d4de4d2072ea8de0116e0,-0x60d2e239ebf4e18825043307ebbd343a996db285e3fc30,0xe1d3e7227635d203501ce90de4246e85245ad934246080,-0x1b416f84f3b8d7b9902f2d22929570fa600d1da9119863c,0x2c25b03330623077f94ea80fdca34018e94cbd6f98003b8,-0x3c8bd28f5a10a7ee43d325c21ac85ac8e29b2a297fa01dc,0x46c895aad559ce99b3ad12d85761b24268a8b84f89667c0,-0x46de6c85b8b6d1d429f5b25e586df78f9e3f584f4fc0f20,0x3cf14cbce264690fb31195a8a9cb169b80d78588be04e80,-0x2d13663d51313503d927711e5b4cd2d7e968c249d4c7b60,0x1cad854b7c23f926359e697d106fbf008934236a9fe6840,-0xfaca07e2872843926d2118bcb7681f685ad10c7cce2adf,0x757598c18642b0f407691bc1b7b1d9efa3cd613629a36e,-0x2ef548ffa9806967fa057572dc3bca1d5f614eace80507,0xff04590ca28b570a41cc8e2465b33f3fb31866fa4b690,-0x48f9a6118c847d7e1a5ef7f9c3c9257599219720ac86c,0x1172ef93e436e317d3c8dc148f6a4df313b4c2c649988,-0x37282338eeec38ca791f75be664fa813c92fcf858a1c,0x8e0da06d08e65939f2b6dc51aed7b6bde46673f01f0,-0x124e3e2bb5199e16524ebe04952fcf6ba5254c17fbe,0x1d8e6eb66cadb38b86e8a15907287815a76377e9ec,-0x24563c9c4c97fe5ebfcb04f15b0d47f21b2c6a81e,0x20ced5f8fad251413b1f762335ff0f9103b812b0,-0x14bf36e869b39951d7441758e3e9f0a39978aac,0x89f2f3b4d0151727312df412bc6632f0c88e8,-0x227c732bcdfe52c9baafddd4cdfcfb2e8b3c,0x48feb607d24bd7d97b31524004809e2bd0,-0x43013f2051fd2eefc695e06b83da423f,0x12d76929d90dd5f15fdc81fc8f291e,-0xbe9f593bb488ef2b3a1ba8c657]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 18 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 43 indices rho q18 m18 18 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 43 indices rho q18 m18 18 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r19 : List ℤ := raw_ints% [0x1dfe31e661cd17fed68dc59d070103157e200000,0x26e3fc4c302b3639ffcd4580837e25e7c8b20000,0x17890eaff58da66b194c46c2110201e6a57c8000,0x8d4a1468b53095d4a3a05c2b973031c0b0d7800,0x24d20a09832138450b6e550cae372cefc498000,0x7130deeb25a08f82938a8613d0111e07970980,0x109b6981d08a8f05179e162808d1724e854e80,0x1e6a48b59b664077302d6ab215d7d88975150,0x2c025d7d6bd6a59d25d0f3c7299f4954e060,0x329c56683f1deb25667ac8d20cec0240460,0x2e45379fc28bdc0462f1371a90447b9d98,0x2172c2162a667d815b3604c42d9cdb2e9,0x12e3d5162ef35fde03598c019af0554a,0x8297fef57609b4f48798c532fe12c7,0x29b4bca5e43f876ea904fe04021c4,0x9478f2bc2328b7a4503bb91ee07,0x148ebdcf6280e00a9cebb988fa,0x15591dd5500658b4edae4199]
def m19 : List ℤ := raw_ints% [0x0,0x80ce8565b2f971ff7a1ff5ff1800000000000000000,-0xad7bc3a64a802da5b710d75beb9a4e4e453e392cc700,0x6fe37c9e0b0be2851f471e24485a55c9e4dd076dacc40,-0x2dfec726c564bc8129b0da2332eed3c0a00e79c2c5be80,0xd8860b042be1620acecbe8ac15c0aa2c5557e22117d5d0,-0x3089bac495bce5888c9f28bd9312275d1888e51f2780e20,0x89deaec1e15f1b274e06db903901b7a9776ed9f4a8ca850,-0x13e3e33187fd2fa1b5d18c4d382f2cc0877099e27d96ab80,0x25fd7b06029e69bd1c539dacd3019f1cefca0a0b4d883f64,-0x3cd2b3d37066f3cd75f17f6802c932401e600008d3f40588,0x52649fa24cd5670b29c4b06f39ad35770cf9b595b7b2b6c4,-0x5f11697fd6c5c37aa0211f400dc9fff46d8add88215b2a40,0x5ddc30f72591d3da0c3023019994b5fcc8ca7a81b6fd9ee0,-0x4f84324e3915fd26b5660a6765eb647499e3d58202bd6b80,0x39e1608c5289c79d747a73467dd6824a603998a4c367b0a0,-0x24328b0d9a1f731537cf1ae3e7e5c97e53b6cbf29dfbe5c0,0x136c107b8cd78f07faedd602988517019b9bcb88c64244c9,-0x8eabd6dd1f96a412f65bc7ea4b484f665f67cef3a337862,0x37d1cb612b1f0a294831025c007070cfcf09e03900f9c61,-0x1281de8df28a0a70c0d205ace8f3576029313dbed420af0,0x529930782cb5e95776176f9fb97f5ffcc5c20d5d2ddab4,-0x1334937da928872426fc4f7348882b13e7053bcb198938,0x3adf405295262b0f03943ecb996c0d97e1a99717f0d84,-0x92911f647b644784f323fa9b237c0bda6b4bb0196890,0x1230b99c43c6e199b7aad2c743f53e4d27ebc8afac92,-0x1c2a3c6c6c561c6d3ee54fa4ce178cd96e6d4a1e534,0x2109d9fb0f99a9fa1b56a50330e0c11cc2e04f5132,-0x1c4b3f677db5188344a900697ab57256fdfb551d0,0x10da5ce0024aa442bf8b2823ebd55e88a8ec5b74,-0x68ae987f97d6b33abaedd4b4eecd70d815b4d8,0x18360cb025f186f019b77d59d344655994464,-0x2edfe9373fc582834ebebc89e8b08bc4bb0,0x26d6464e084b75d09d518b375fa0b2469,-0x9b4279e08dbba1ae6453b38f0e9332,0x558e762259a725c410aa03be491]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 18 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 43 indices rho q19 m19 19 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 43 indices rho q19 m19 19 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x15591dd5500658b4edae4199,-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r20 : List ℤ := raw_ints% [-0x3e545368b483184643fed27313673c4fa922c0000,-0x50c58894ce1c8955e0eb53ce09cde122a9290c000,-0x30d9439ad030a897e0f588fdecc6a253bbf09b000,-0x1250b3dbbdbb4ef8e0445f8377a4fa271cd841d00,-0x4c4f1bd956277767b1b603b0302d11dc5445de00,-0xea62aba03e7d798da08aab9ae78838bcdd691f0,-0x225b4d7ae62ca084619bc9f5d4da27f04f82e90,-0x3edbf3b352c5e0eb7fe804c8d5c3ad5ffb5fb8,-0x5ada7e07cca7786889e06e609281327709da8,-0x685adc02763ec64e3c58a3e179c86016ca0f,-0x5f474aef1295aa9e04fa628ca09a8cca249,-0x44c6519989caa5bc7d3af7972951cc32ec,-0x26c721e0f7ee59ae9db502513be66ffd3,-0x10b9b9017fb42c145ddfb3f272b51390,-0x554b0baecaaa471443ea695cc6c12f,-0x12ef927d8c0c1bbd3bd2fc90fdf88,-0x29d8c77acd83dcaeabb3072f5fd,-0x2b561b417b60aa2921d2ff4c5]
def m20 : List ℤ := raw_ints% [0x0,-0xc135c8188c762aff372ff0fea4000000000000000000,0x102503afed8410d45addfece29297d090838972305e100,-0xa55081003ce70ef048cf96bd71a310e387fcfaada859c0,0x4367fa7ac6e049fdb70f0cb4ff6598c7254f0195be01d80,-0x13a9aef999f5dc47ed03589389129f290bc5d7923c1535b0,0x45e3bf88871137d5a8e19184e23db3584a7a956905fa44e0,-0xc4a1414ebcf18e8e9860394d7dfedf87fc79b088e6da9f30,0x1c14ff5e1f9dbf7e02c872f8694e735f7f249c1b32bf46880,-0x3510a4f53d055ca197ee3a987b283cbe32d2b22f770a6c1fc,0x53ff68054e6b57fafd86ac1d64f1561e94f45d5d4c1a94f38,-0x706b2e6eb05a91c15a9209f2765795115867c6e263858bf9c,0x800d5ee359d0d94f9f6804cdabf403af1f8bc8f5e2b9d33c0,-0x7cb2b6605fd4c6637d762c9307d07a3feb7c97c5bec104320,0x68191a3e0c6deea137ab467fd4d95248da4b9e263238f8a80,-0x4a9624de64b9b3746285c395bf5b2cba1b4cfe1150174a360,0x2ddc2086cb4b068645d27cce0f071284aee12e176f42f9c40,-0x1829040a5fd5f9dafa387f43a93b77ad1421426ece450df4f,0xadff4a910c177445f362a8a6ea2f30c0b90a97725982ff4e,-0x42a1166ca1b6909cecb28a3549a0f266356847171b431ff7,0x1594b9d902a710b339eeed3ae5e5b6080a953241c32f1790,-0x5de3688d0dfc4a53ad2ba7051118495577e62ee432cfd2c,0x153a540f209ce5c5b4ae54fc4955781989625b54a973608,-0x3f18d9b90698ff7ee2e556dc6bb5b14174b6706c5b41dc,0x97d2c80de765d1ce198b0503c7f9c003b86393652e8f0,-0x122499c0b550d6e735fba52a0d22678277baa8642969e,0x1aee1423d731f554ef460d1ac24b51870705892406ac,-0x1e20eb232614c89b615ece247cc069b518dd1c0fcfe,0x1876032a0ce1579d0f2e039b165123a0c8cf28b5b0,-0xdb732bba63b7e81891f4f16fc517a0f84339016c,0x4f89adfb00bfa9c982f9cf1ff73e1600c7d3768,-0x11023a9bcf5d4ca2fcafc8ba2cfd35568bf2fc,0x1e1af111e784d1009a8162b83c608e5630d0,-0x16815fb92e671e7441ab1c9aec8c3d50af,0x4fee723f8f51218fc189357baef4ffe,-0x26633d28919c2ab576096d475247]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 18 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 43 indices rho q20 m20 20 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 43 indices rho q20 m20 20 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x2b561b417b60aa2921d2ff4c5,0x15591dd5500658b4edae4199,-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r21 : List ℤ := raw_ints% [0x7e871b87c88cfa7e2cb431d4a2c99a4928ec3c0000,0xa3dffbcb0343db3366215841e89b7e6917fecdc000,0x630c504174d76951f0ce9c36a290ae2609eff73000,0x251cd795cf8c164105ad50f4c3e54ab97b8d1e4900,0x9a8453e26b67d710453270dc5e434aac769774100,0x1da3c27768a90c5590f1c3b0f0d80c17031a10b30,0x4574951fdff26e59ab8a520117f954a6376946e0,0x7ef56da409991c5e6923ca9cbea794646bbaa48,0xb7507d2d95abedee08239dc5c3a7515b4ec2e0,0xd252d6438f8a6a2b1642b6ba6faeebaad69fb,0xbfcc48572561c29951f23970cfd4e0924c86,0x8a42e4ce1b457dc146ddc5d0f632867746b,0x4dd7e35058911e2c794c4c2e88341a60a0,0x21855eeb4036828f1fce214a9950d933f,0xaaa3b8b36960230ab49fdd14c6d6fee,0x25cf130a11f0719046cb3e390ccfad,0x535f3ca3c568c929749b836e34ac,0x56210398ff27cc42829ed0ccb6]
def m21 : List ℤ := raw_ints% [0x0,0x121d0ac24d2b1407ed2c7e97df60000000000000000000,-0x180b8cf6e0a9ab48f5c05777b5a993bcfbd159425873700,0xf46052b8b84eb5ac7976497c97c399eee01aa059a201040,-0x62dc4635de2e51cac93106590b21163e0bd827514f6ea680,0x1c996ebe3192330871af7200102a8817bc23ba35de3acd2d0,-0x64c3ab88ef45f77a567107bc62b4c14e5534ce6ec85133020,0x118deeab4fbff417717525cb2350e54cdc19b001855ed14d50,-0x27b848b9d2abc8b56988a3826864893ca0b3117037df3f6380,0x4a469b64854616c1fc6102a15ba7c63196bb22df88bf701da4,-0x7445e0c1cfaa47d61db91a7ccb2f9abf56c4e700e19abece08,0x99c8521276b86a7e774cb94d5b041baf23bf14a89bd69f4304,-0xacf7cb77d83900cbeb546471a9e96705e96d89f0939d2f7e40,0xa62cc636253247bf17f1f1d203668166642cc3942fc9becae0,-0x88b9e19be2b31f64f99f90980c079cf8f15e2a4c184d3ecf80,0x607326c4b2e6128c7f2131d13c6c4b0284b5da6efe1a8348a0,-0x3a50aef4f3824deea1f2a99768605be03f25d8c571587a91c0,0x1e2b6d486dcc5622a39de06ec22e5ea3404af325f55c7742d9,-0xd50bb5fae513e0106ede0d0451a9f8a2bc49f038848d2c982,0x4fdb6a8b81f2e10ec1d84fe9c575974ab33a1071285988ff1,-0x1944fb43e553fef30a05d839260e54623f4aab7a2292741f0,0x6b2a755054e150d034abca302763157c5dee8eabe8ed37f4,-0x178f645e92b55d0e4b6a641ddf30ecfd91ed3a16ac5658b8,0x43e5c24b3b05a686d1065fdce1852741ab9c1ae191cafc4,-0x9ddfc5f80b7a8df6578a3702f6d42384bd66187044a990,0x12292ceb9724e191bdf431b7d41d02ee2d2e717d4f2ab2,-0x19d543932197fd708f8f2b0a543a6d2211661a3e2da74,0x1b8d83e34d5402bbd3a3433e0fc4173b389ee09f6152,-0x153249aa0f2add3594b4ed5af4450cb4732b3bd76d0,0xb2e8ffacb6fe8cedd9971ac84ff40a018d00aa6b4,-0x3c80bb05cf2031123c5eecd33624b8d3a5b92258,0xbf4ad695c58d2d9501940e4e9bec625cc536a4,-0x135637f8fda6e59de03a4a2bc9b729f983eb0,0xd09cdd804073247e9a066190cdad2af879,-0x29229b89684c622961d8784094132152,0x1137ea78759034e5c408703973f21]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 18 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 43 indices rho q21 m21 21 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 43 indices rho q21 m21 21 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x56210398ff27cc42829ed0ccb6,-0x2b561b417b60aa2921d2ff4c5,0x15591dd5500658b4edae4199,-0xa45d15ce5e1b8b4040c1d8,0x4d0e800bafaa9c11f1120,-0x23168da126765b8f1927,0xf766f72227e89ae40b,-0x690ed49e2371b70f2,0x2ac40c3b6b2ef11a,-0x10950be36589979,0x6137a639fcd0d,-0x21538163acfc,0xa8c5d5eaa4,-0x30755cfbb,0xc4fb69f,-0x2aabf6,0x76be,-0xed,0x1]
def r22 : List ℤ := raw_ints% [-0xfb77ccf17829c2ae198bf86dacdb17cf30672880000,-0x145872ccb7e104b7e750f4bb856799e3f19cba008000,-0xc4a4f4ce6bf6429cfd175ddd52ad3496d852a0e6000,-0x49a30edf19362279d2028f7e2326361f756db701e00,-0x13262124b89f19414dcdfdfc65395e3425a87a07b00,-0x3aba9d1a56cfe78f92ab963d8fd09cedcad21268a0,-0x898397380c40f6b908ea3defc792492381c7a4730,-0xfb26b99ecd8609b1bb6a22e6d7c81bfe58481570,-0x16a4cbacd50f70c5de5ec2a6251c064c47354e88,-0x19f42c57737c7e28e122a55d51590b58925f99a,-0x17a442fcca38a072b7046ca0fa6e329b27631b,-0x11059f26faf98294ab63f397788f14034e712,-0x992292f8b6a1e951db547ca2d590b60d37d,-0x41d8e3e530a6ed04c72b96700bcc4fcfbc,-0x14ea8f5f7e42d6a64635eaad62f924345,-0x4a051b8f89ce7729ea808adc769815a,-0xa2e6a1b199b173b784487564348eb,-0xa7ebe47f8ab967307bf9220e5ae]
def m22 : List ℤ := raw_ints% [0x0,-0x1b2b902373c09e0be3c2bde3cf100000000000000000000,0x23d21e21dbcda2dc6df653831ce0ac5fa9fcf04f5f25f100,-0x1696e1c01b4443183d873e36536fb1d8e1b80db80d8e175c0,0x911a0f1bb78cd4ba9df08aa34807a658479e61d414f2cf580,-0x29a3af114bda98f8bfb03c185931b944c05d6d1c7bc5aff0b0,0x917654a751a362bdaa10bc00562268ca7cbd25f167e4f252e0,-0x191d02fdc930cd9bffad25fb0f1e3b54b9478b9847451557230,0x3847d60c2838e8020e1a8e720eda33b4ce0309343a4d1dcf080,-0x682d1a8b0afd307626d534b719237c997d8ba146c25447639bc,0xa1513bad7d82c1795b3df80fb8e391555293180a5e2607852b8,-0xd2e5f28274a9ecb0a50e2c6f3b71dd4afd5c69df99cf216d95c,0xea4919823934cb8845653f20325f9f3b3725a5f1061e9dabfc0,-0xde1cb4d2a43930179cbf50992dcca9f1fa39d850dd814d33720,0xb428bcad98ecc6c6073750253602cdbaf6afa02c35cbceb8680,-0x7d261bd50cc5a6449b3c0a8518903d6ee4970ae27b2687dcb60,0x4a6bbf9c2924eacfbd2779e30081a674808ec84cda6884c1040,-0x25d0dd5cc670504c68a88c9820d95b85670b8ddfa73eed0eabf,0x105e05c0a4e3885889a65a152a28b3c962fb091f1645e7d392e,-0x601830372b8cd7351a25d9153fc4c48939eae54649104ff9e7,0x1db56bd875a41f3b61e97e3ae1454e9444b3a39c3aae5f8890,-0x7ad1e16fb39ece43b55472692915fdb31a68798f38a91bdec,0x1a410d4c7b4bd80ea6a5aa3bed1dcffba7d8b258ebabe1a88,-0x49598ea6d432c38bde52d2cee75b4ec7d8a8507b8e44b59c,0xa4c7c28fd7eea39f173a88bdf7a750017d9d8ed48973ff0,-0x123df2fc04289cf5fbb59d2d3f103bc8071e47246d57b7e,0x18dbc362b8a04eb7019ebb53e67ea9c1a1a43266b6af6c,-0x1943ea4ce1794fc3434d006b023a449178c6aee00ffde,0x12686b689b974dce920dea1af356c5353aee374588b0,-0x9218fbc5db2ba615669c6de623ba63d0edfa14a42c,0x2e12599eb604f4ce11de7cfa69ce2a11bd59c4de8,-0x8687d73ab17e246d98a794fb022ae1bb6de96bc,0xc6bb3d71a00e20ef8d85a0067dec3d7c085d0,-0x78d3c511b4a9f75a5d32edd6df96dacd61f,0x15295fc98737895b36d1167807aae04de,-0x7b885a44f128820f9a8e63bb32d37]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 18 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 43 indices rho q22 m22 22 2102027690752045056000 24=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 43 indices rho q22 m22 22 2102027690752045056000 24 18
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_22
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<23) : intPolyRF (mz e)=rfPoly (C (2102027690752045056000:ℚ))*rfX^24*(1-rfX)^18*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V7C25
