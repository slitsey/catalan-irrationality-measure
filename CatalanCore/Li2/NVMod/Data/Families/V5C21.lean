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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C21
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,21,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0x168244fdac78000,0x22166ad85bc6800,0x17de865e2b02700,0xa4342056b29b80,0x3089ff42764290,0xa76ce8ba8b300,0x1b3d41745e368,0x369b14d7cce8,0x5539b8e2911,0x67f035a900,0x62c0cf6fc,0x48599690,0x2814a66,0x103c40,0x4894,0xc8,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x7,-0xe,0x15,-0x15,0x34f,-0x882,0x2cee9,-0x22f27,0x22f27,-0x24f8,0x5377f,-0x2f6a,0x4c69b,-0xcbc48]
def rhoDenominators : List ℤ := raw_ints% [0x569a960,0x290e8,0x35a0,0x37b,0x58,0xa,0x48,0x31,0x620,0x288,0x1e0,0x21,0x6f6,0x8f,0x36be,0x4cfb3]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 21
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤20))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤20 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 21 omega5=padCoefficients 21 (omegaCoefficients 20 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 20 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 21 omega6=padCoefficients 21 (omegaCoefficients 20 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 20 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 21 omega7=padCoefficients 21 (omegaCoefficients 20 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 20 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 21 omega8=padCoefficients 21 (omegaCoefficients 20 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 20 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 21 omega9=padCoefficients 21 (omegaCoefficients 20 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 20 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 21 omega10=padCoefficients 21 (omegaCoefficients 20 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 20 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 21 omega11=padCoefficients 21 (omegaCoefficients 20 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 20 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 21 omega12=padCoefficients 21 (omegaCoefficients 20 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 20 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 21 omega13=padCoefficients 21 (omegaCoefficients 20 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 20 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 21 omega14=padCoefficients 21 (omegaCoefficients 20 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 20 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 21 omega15=padCoefficients 21 (omegaCoefficients 20 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 20 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 21 omega16=padCoefficients 21 (omegaCoefficients 20 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 20 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 21 omega17=padCoefficients 21 (omegaCoefficients 20 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 20 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 21 omega18=padCoefficients 21 (omegaCoefficients 20 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 20 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 21 omega19=padCoefficients 21 (omegaCoefficients 20 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 20 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 21 omega20=padCoefficients 21 (omegaCoefficients 20 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 20 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 15 li0=padCoefficients 15 (liCoefficients 14 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 14 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x42,-0xdc,0x1ef,-0x318,0x39c,-0x318,0x1ef,-0xdc,0x42,-0xc,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 15 li1=padCoefficients 15 (liCoefficients 14 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 14 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xa,0x2c,-0x6e,0xa5,-0x84,0x0,0x84,-0xa5,0x6e,-0x2c,0xa,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 15 li2=padCoefficients 15 (liCoefficients 14 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 14 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x6,0x6,0x32,-0xe1,0x1d4,-0x24c,0x1d4,-0xe1,0x32,0x6,-0x6,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 15 li3=padCoefficients 15 (liCoefficients 14 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 14 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x2,-0x34,0xd6,-0x19b,0x174,0x0,-0x174,0x19b,-0xd6,0x34,-0x2,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 15 li4=padCoefficients 15 (liCoefficients 14 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 14 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x12,-0x72,0xaa,0xff,-0x4bc,0x6e4,-0x4bc,0xff,0xaa,-0x72,0x12,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 15 li5=padCoefficients 15 (liCoefficients 14 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 14 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x32,-0x4c,-0x28a,0x915,-0xa5c,0x0,0xa5c,-0x915,0x28a,0x4c,-0x32,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 15 li6=padCoefficients 15 (liCoefficients 14 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 14 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x72,0x1e6,-0xb86,0x87f,0x1c14,-0x36cc,0x1c14,0x87f,-0xb86,0x1e6,0x72,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 15 li7=padCoefficients 15 (liCoefficients 14 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 14 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf2,0xbfc,-0xd3a,-0x55fb,0x9ef4,0x0,-0x9ef4,0x55fb,0xd3a,-0xbfc,-0xf2,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 15 li8=padCoefficients 15 (liCoefficients 14 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 14 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f2,0x313e,0x802a,-0x1b201,-0xfe1c,0x3f984,-0xfe1c,-0x1b201,0x802a,0x313e,0x1f2,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 15 li9=padCoefficients 15 (liCoefficients 14 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 14 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f2,0xaf04,0x4cd56,0x154f5,-0x13e1bc,0x0,0x13e1bc,-0x154f5,-0x4cd56,-0xaf04,-0x3f2,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 15 li10=padCoefficients 15 (liCoefficients 14 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 14 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f2,0x24456,0x1cfeda,0x53acff,-0x17a0cc,-0xb6aeac,-0x17a0cc,0x53acff,0x1cfeda,0x24456,0x7f2,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 15 li11=padCoefficients 15 (liCoefficients 14 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 14 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff2,0x73c4c,0x942766,0x3587ce5,0x5bbcd14,0x0,-0x5bbcd14,-0x3587ce5,-0x942766,-0x73c4c,-0xff2,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 15 li12=padCoefficients 15 (liCoefficients 14 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 14 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff2,0x16942e,0x2b6c90a,0x193ac37f,0x59bdf604,0x879c5ea4,0x59bdf604,0x193ac37f,0x2b6c90a,0x16942e,0x1ff2,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 15 li13=padCoefficients 15 (liCoefficients 14 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 14 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 14 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^14 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 5=>omega5
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 20 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 21 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_5
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
theorem cache_li (j : ℕ) (hj : j<14) : coefficientsPoly (cache.li j)=liNumerator 14 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x1b13147031f724000,0x258b75579549b6ec00,-0x18ed4d4fc773523f900,0xa8b9cca116659102200,-0x3310e37486433de9b440,0xbc4c273e5e9c81264b40,-0x225691707fdadbef538d0,0x515571a00689191313f60,-0x9f3059d24f6d8ac902aa4,0x104b6099c07bf0db7c6f88,-0x16877feab2d5d16d6db120,0x1a7549038efa31daf658f8,-0x1a7e5389d8845eb331e955,0x16a9a4498b35eb8b067e9a,-0x10901b3db00bce30b9ee94,0xa53783857bace92403e1e,-0x5792e8a50fc0f598f0fec,0x274207dbe10cb3dd7a23a,-0xec5b9b995eae6b75a92c,0x49e5131b7f6ad23f828e,-0x12eed1947eec433a442e,0x3e724bdc8a4bfa283fe,-0xa1a17ac356f59b31dc,0x13d16f174d2a45772a,-0x1c066992bb5af68d8,0x1a72e40427fe8866,-0xea406da8ad1c74,0x3b3418761f9d2,-0x39786a231d5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 16 29 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 29 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 35 indices rho q0 m0 0 11792619219693312000 20=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 35 indices rho q0 m0 0 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x21d7d98c3e74ed0000,-0x2e09e1b107f68f67400,0x1df7c90614eec7c48b00,-0xc6c1336817cc9f3a1e00,0x3ae6f8d7dad65808c3ec0,-0xd48588c53c423fe0d9fc0,0x25e4bb0f9d90aa336932b0,-0x57afa70bdd89f04e71cd60,0xa784589dadc2cb31d9f03c,-0x10b87664bc3974dddce4e08,0x16850e7dc3e9120d90d9218,-0x19bb68305c80d3e6f6ba3c8,0x1909a7d8f563d0b4d805a23,-0x14c833652022cc786ef2eca,0xeb6e2f42b6e6d4cd58a172,-0x8df10dc735cc1a8d36fab2,0x489c24499df253dfee443e,-0x1f5721157342134f9fbed2,0xb5305f76cc29ec81b23ca,-0x363957f0dda0ac70f11fa,0xd3fbe9d398c142449d1c,-0x297c4a139357d8c9183e,0x655e8ac7a5aa9e5ca26,-0xba6a367c3b35768516,0xf4d20e624ecf4f9f6,-0xd3decd3b748a57de,0x6994b900ad51ed6,-0x1756f55ad99f96,0x12e407fd1d91]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 16 30 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 30 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 35 indices rho q1 m1 1 11792619219693312000 20=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 35 indices rho q1 m1 1 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x2a4dcfef4e122840000,0x387d13f181cf92055c00,-0x241283a4b2148a053b100,0xea8e638063c078c59fa00,-0x441b2f96bc9e3dbb44b640,0xf096a7b710887343dc3440,-0x29f7db96fd053aa44dea9d0,0x5eee7867637c28e3f536ba0,-0xb11f04c44cfe3486fc820a4,0x113fc7b1a928337a1bcf6098,-0x16a46433b5a3a6f8af613820,0x192f80262721b11cc625a7a8,-0x17d317b7d5e1dde6e3fde755,0x13327fa766b3c9276e1110ee,-0xd2c7416bf901545fbbae5f4,0x7af02ddc57f9dcba3c00a6a,-0x3cb6720c3a5c2c815c73df4,0x193ce5c2d13ce371f21f6ae,-0x8c220d4dacaed0e3a2e11c,0x2825706b5a5423ba92e6da,-0x95a9ef9522d4fdd3306e6,0x1bcc8f90992a81bbfc81a,-0x4018d313f455a89713dc,0x6e68e460ce41584db6e,-0x8684207ee26e2f50d0,0x6a93d001f27ac3572,-0x2fb5535d1dfe1624,0x9337cf6b887006,-0x633a6644681d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 16 31 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 31 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 35 indices rho q2 m2 2 11792619219693312000 20=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 35 indices rho q2 m2 2 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x34e143eb2196b2500000,-0x455a3599e497f70fcd400,0x2b78f3f1bf81073713e300,-0x1154e1484f3cb2daf402600,0x4eefca32f184758f753c4c0,-0x1112c2f292d49e2e24466dc0,0x2ea56bde3e53d9ec0f2cacb0,-0x6732e83721526602e6d6f8e0,0xbc26a98e273796f9a84a55bc,-0x11e31dd50dcc48acd70b668e8,0x16e54ee3e964837ff533ae378,-0x18cde60aa0a5077a3ce57c6a8,0x16d28006af0cc7073e9ebbba3,-0x11dc3073d5dbd7d9364de8e22,0xbe220cccfce116bd3265f2ea,-0x6b52481272f61432a3457f2a,0x332e870e0ca2e3dda3b9fe96,-0x147ecc04a5257b79e991818a,0x6d4fa8e6bbec7d6aab0c0a2,-0x1dfadc80401c38c62f0b9d2,0x6a9112e844e00fc9db0714,-0x12c82c328b6f6f884cb6c6,0x28d8389380ac01421720e,-0x41da0f447640e900da7e,0x4a57e6e39675e5426fe,-0x35d723a9f60c645866,0x159a9f588994f1f3e,-0x3a06c595311bd7e,0x2089a640cc539]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 16 32 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 32 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 35 indices rho q3 m3 3 11792619219693312000 20=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 35 indices rho q3 m3 3 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x421994e5e9fc5ee400000,0x5532390ca0824d768fbc00,-0x3473ecd8c98598f2d155900,0x1486cec017f0620c2a7aba00,-0x5bb45acd7405faa150bd1840,0x137138818267bfd4f3d5b4c40,-0x3406bdf96c5ec559629db39d0,0x70a3a6b590bde9d1680d1aaa0,-0xc8c8660569bb58735cee45324,0x12a4b908f7519b140196cd9bd8,-0x17482fe7c59242e689521e7340,0x1893dc61a591b24e2cc3bdfd28,-0x160156a39ccf7c9196d6987995,0x10bb5e44ce5d6b7a0814b6a3fe,-0xacc562cf7b9022ec6ff73c09c,0x5e68adda07848bcacbf1b560a,-0x2b7da9a6fd977eb65205a254c,0x10c7afc8049f258a00d671f1e,-0x55f9dfdf48e42ec8ec9fc084,0x1692f827075f443b8265249a,-0x4c803fefe45189e014d6e7e,0xcca2ed7ebd083a89ec440a,-0x1a382906b10d7763852314,0x2788c5157e9bb3ec2c80e,-0x294f60e6f85dcf861998,0x1b4d86005afc6f03cc2,-0x9ccec6d33c38285bc,0x16dd19a2b21db386,-0xaa847cd4c7da5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 16 33 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 33 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 35 indices rho q4 m4 4 11792619219693312000 20=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 35 indices rho q4 m4 4 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x529ffa1f647b769d000000,-0x68b8837e57ec0a1589af400,0x3f5caf8e11e5e4ddfbd49b00,-0x185a58e723bd69165cfa35600,0x6ac88fe872c9cf3f6c465eac0,-0x163416bed69925666b80bb31c0,0x3a39b94f07b28e70db97a330b0,-0x7b6e163205ded7c82710da38e0,0xd7393fdb8bf86902c1de24a63c,-0x13875c423923890bb48bc1bab68,0x17cdf985d64ab0fa7d0d97e3398,-0x187f74bf105722f55345e4805e8,0x155a5fbabc7aae502eba7c02da3,-0xfc80fa5aede74d07a689e543c2,0x9e1e6242ae1ff3d782a434e212,-0x53abc53362488b55eed1c496ba,0x253dd424a1f0b229ebd1a0948e,-0xdd8d7eaaddbeb5ad39b7cff0a,0x442a1cda2822bb6a35ff54dca,-0x11223bf721670ff66c73bcf82,0x37594df82017b02056e5808c,-0x8c65f27923a8f8e11fbd0e6,0x10f2ceacacb90daad82c446,-0x17e16b916c2acf66e20a6e,0x1711a8010c6ab0099a126,-0xde47fb99a0167563ea6,0x473ce9ec5aa3e1ac96,-0x90134bf00745570e,0x37ca7da7246b21]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 16 34 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 34 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 35 indices rho q5 m5 5 11792619219693312000 20=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 35 indices rho q5 m5 5 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x168244fdac78000,-0x22166ad85bc6800,-0x17de865e2b02700,-0xa4342056b29b80,-0x3089ff42764290,-0xa76ce8ba8b300,-0x1b3d41745e368,-0x369b14d7cce8,-0x5539b8e26d1,-0x67f0359fa0,-0x62c0ce6a8,-0x48598704,-0x2814185,-0x103920,-0x47ea,-0xb4]
def m6 : List ℤ := raw_ints% [0x0,-0x6747f8a73d9a54444000000,0x80cb33d5380ded9882401c00,-0x4ca0b5bc0f504e71021758100,0x1cf11de8e75823588bec0daa00,-0x7c9f9d7c80babf18e40556ea40,0x196d9d857f324ff3e18a9777040,-0x4161bca98328f98b777bd6175d0,0x87c78242bfdfab19aadcf3728a0,-0xe7b76cd7a23f1a166afb6af67a4,0x148e5c50cf1028a74c0ca99effd8,-0x18783070b062e4390b90ad820fe0,0x188f795cc35a8cbc7073426f0be8,-0x14d973c886cc4958dbff31bf1bd5,0xefbd47eee912cffdecf17c58efe,-0x91b7e4f490ae9e67c4bf8723fa4,0x4ab19470a30f8e49e44d7ca5f7a,-0x2021307506d69481bc089e1efa4,0xb83af86d6f0ee0b624b8ff8b7e,-0x36762730c2072b39922da3450c,0xd1acdda16226dccd1efa6e1aa,-0x2858ba63758f76e8194f24156,0x610427ac4ddf75625610484a,-0xb0728364484d8b24449f2ec,0xe8207bea1112bef783fd9e,-0xcf0fd236ce122352a7ce0,0x7171d96a776ab12f7b22,-0x2066a691b6676cce1b4,0x38b65a900093ab8b6,-0x123c3b67ff5c46d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 16 36 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 36 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 35 indices rho q6 m6 6 11792619219693312000 20=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 35 indices rho q6 m6 6 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0xb4,0x1]
def r7 : List ℤ := raw_ints% [0xfd398825d4460000,0x17e140db22db1a000,0x10a6600f5de1f0400,0x71f6be5712e52f00,0x217cd35a647431c0,0x72aff3af0279970,0x127fa51d17b3220,0x24b13690762fb8,0x3882e4b1d130c,0x43c14a2cad2f,0x3ef08e80990,0x2cb2f0f698,0x17a8ec8b4,0x8e91b7b,0x22cef0,0x44b6]
def m7 : List ℤ := raw_ints% [0x0,0x8119f6d10d00e95550000000,-0x9e7d6b282e1f942bc51c21400,0x5cc65f73836f0709d9a4f49300,-0x2274027101c4f21d22cce1ee600,0x91c46579035e7785162b478c0c0,-0x1d339b15fa4ee721aa4857652dc0,0x49a8ae42dd0cf5e57875e5576cb0,-0x95ee940dd9c14d63837d0c4beae0,0xfa8bdce20dfee1f3273f91ee52bc,-0x15bdb2b2e8b7eb836cfff25221468,0x1948f13439072e13b4b31dbbe2bb8,-0x18c35d3ca77c018cd6b33dcb844a8,0x147b529d4603a0c5385cbe12c84a3,-0xe51784dc6baacb164a56dfc3ec82,0x87340025175f14945046b90da43a,-0x4326bff6e6f33c43003afde7a42a,0x1bebee7cca7ae2181e57befd9fc6,-0x9a55963668fc6eadc97212fdcaa,0x2bd6c576587b144dfa6e7791c72,-0xa18f52ce3f33667265a937c312,0x1d9f75c324af2f2ec68df09cc4,-0x437f3ec6f75b931abe135d166,0x73868e0fefe38b410b5fca7e,-0x8dc73a76f93bbd76102cafe,0x74a4c29b8364b48117720e,-0x3a0d3a9efbe72ec78dcc6,0xec0057ff2831842096e,-0x164f57a153d9af6abe,0x5f44ff0c6147949]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 16 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 35 indices rho q7 m7 7 11792619219693312000 20=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 35 indices rho q7 m7 7 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x44b6,-0xb4,0x1]
def r8 : List ℤ := raw_ints% [-0x60a9af06e287d50000,-0x9165cb8ebd4b4bf000,-0x65032a3af3c5e61a00,-0x2b082fa50f36298900,-0xc95332ac996dc6360,-0x2ad828095b5071040,-0x6dcf2fbc2befb280,-0xd800978525e1ad0,-0x1494d8bc983865e,-0x185d84bbed12f4,-0x1645578a5d9f9,-0xf7c32c740d0,-0x7f6cbd05ec,-0x2e0fd0ccc,-0xa91cdbd,-0x12df40]
def m8 : List ℤ := raw_ints% [0x0,-0xa1607485504123aaa40000000,0xc324144171384c7c4f1d677c00,-0x7072bb186a65853a268e85ee900,0x2914d176c64c7629377d64d3da00,-0xaade8ad7fd684dc7f7f1672f8c40,0x21a026fd57f879791c1496cf92440,-0x5340438744471c654d6f98bfe91d0,0xa62d101b1beeec126bb75bbfad2a0,-0x1100c10eabb39eeceaa68e9a58fc24,0x171a14a0cd3b9bb8c37cb2a89666d8,-0x1a42f9934b91360f78b23ffc522380,0x191b31db333a3b93e4fc332b68bda8,-0x143d809b59439b6ff65651f4aadd15,0xdc4c5cde23f9a97857058690101be,-0x7e470f89c1e7d4a03bd119221db6c,0x3cc94eaa10d43690343e5188775aa,-0x186fc5b5b5a47ddb62fb30e9e15bc,0x8238b0172f1c203bfc9139d7de9e,-0x238b26a603c69652621e68931554,0x7d601549c15121e24b3e92e8a7a,-0x15e65a37008732a137111954eee,0x2f43e3793fa7cb7cc7c41ab7ca,-0x4c153cd09a8a225b198501504,0x5706ff19df83c3fd9448196e,-0x41f54f02f1b3fcee12af768,0x1dc655b01080de3ab65cc2,-0x6b820d94d5ab089efbec,0x8c545ff0054809c026,-0x1f1437febafade75]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 16 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 35 indices rho q8 m8 8 11792619219693312000 20=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 35 indices rho q8 m8 8 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x12df40,0x44b6,-0xb4,0x1]
def r9 : List ℤ := raw_ints% [0x1a8c9f4805917a600000,0x27d42f4f333d55dd0000,0x1b95fe493b9590b6d000,0xbb5d99111366b354600,0x369001ae1f719828b00,0xb8e56e465ddd3d5ca0,0x1d7379d79ffad961c0,0x398b7055d6dd19f80,0x57060fee4a23f870,0x6603a74e41db9a2,0x5c1d4ef02e300c,0x3f10f3e073a07,0x1fca488632b0,0xb2f84dca14,0x278b60434,0x42c9c43]
def m9 : List ℤ := raw_ints% [0x0,0xc9b891a6a4516c954d00000000,-0xf065c64fdf825a7e0841eae3400,0x8870aa944d1901dd3e7686fb4b00,-0x31103b2c0e3de5b36e0f088507600,0xc8b8a46075dc0bec2ccaa8cf086c0,-0x26d284f7138470c38e481419b229c0,0x5e638c6e09960c2e10bcb1dcea18b0,-0xb8d9ecc8ae199ecb2368226fab54e0,0x1289c4d814ab87bcbc14e50f35c7f3c,-0x18a90efab28506884b8d58d735ed768,0x1b69b5fcaa9fb8fb01aed8bd55f28d8,-0x1997a1c09aecb99f3a5848e05577768,0x141e2c19a8e5e828c02a616099ccaa3,-0xd52580246176f4c53759d053170dc2,0x76b3e78fdfacff8131e0b005a234a2,-0x3764baf707d83b6b640896e7e31c9a,0x1588a81c272dac16bea129370dccbe,-0x6ea4bee263353780d859fe42a99ca,0x1d04f4da2748a78c83b1bb00fcf5a,-0x61f6e697836ac30ac2350d8536a2,0x104c2791f45c73ae5e10f6ad66bc,-0x214d73ff45fe7c158f5ac849966,0x326262315773c0b4158e8dbd76,-0x35aad120c2db6586aefbc228e,0x256d01f1cd8a8c1b42dc5236,-0xf4d533bb1d0320c508d166,0x30ff421a5dcadd76b7206,-0x3720d2fb8f2801f806e,0xa2126c7f67b469b1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 16 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 35 indices rho q9 m9 9 11792619219693312000 20=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 35 indices rho q9 m9 9 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r10 : List ℤ := raw_ints% [-0x5df535186e281d4368000,-0x8ca18a5f18559354f3800,-0x6125a77506c730a013500,-0x291d7b35dced6b0c9e280,-0xbee77c23de75bb0de5b0,-0x284508b6b6fd04b84e00,-0x6625d6a1fe386808798,-0xc67cd5e7f4d25e9ef8,-0x12a35647623c557bf3,-0x15ad7818352e34290,-0x13635016ed187a52,-0xd1e49ab7c3f7a4,-0x683da94ad66ab,-0x23fafb709210,-0x7bfd6f64a8,-0xca241024]
def m10 : List ℤ := raw_ints% [0x0,-0xfc26b6104d65c7baa0400000000,0x1284e85518cbe2b0aaeb106eddc00,-0xa5b9b95086f3e9cd5a82d53869100,0x3ab0494207f535cea0f5221d288a00,-0xec47d07baced153336e446e3ccfe40,0x2cf0389faa0372793db83f556377840,-0x6b58d0e56c9cdd41d92d8a673dfddd0,0xce5bd3b9c69724b7f682f3d4b4b5ca0,-0x144b23b1b80b35c3ed2ac50b966dc8a4,0x1a7127ea2b61b2f30a847b4acb6729d8,-0x1cc1536295affdcb20771cc9302ccc20,0x1a39ef7a74bf2898aa8a7f7eb0ea3968,-0x141c195849d7561d24546ed776c4b155,0xcf7759179d506affa21fae188efd77e,-0x7048e601c074e03401b89b7b77dff74,0x32cef8e8410003a66d98a624150c45a,-0x131a50ea7320f7b13802dd8e0925094,0x5ea556ad45776b4b1c80219fa257be,-0x17da5473d5964cd01d5de12b1fc5dc,0x4d0db07436e1e46d3a2d08d79c8ca,-0xc348a413c1308b789d2c0f864b46,0x179a47e6455ef0b66b90ba55e24a,-0x218a2e930a49192026a92d33ddc,0x213cb17a667801572605aa50be,-0x154d5817579ae055becf0ce30,0x7e0ad42f5a0c29e5e1d8e62,-0x16564fb4e3bdfa7f89e1e4,0x15a42497553667442416,-0x34c72fc6704123dbd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 16 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 35 indices rho q10 m10 10 11792619219693312000 20=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 35 indices rho q10 m10 10 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r11 : List ℤ := raw_ints% [0x11c5f62d2c647f53c0e0000,0x1a8c8866d83decf60c82000,0x124c514817c66b129e64400,0x7b95e8bbfe0d552ed4a900,0x23c1e22e6c365d084079c0,0x78450dc0080479fdb4650,0x12fddb6f43f8ea9f22ca0,0x24bbb2487540c546c908,0x36e3c001deb2094376c,0x3f6ed86524a9c6480d,0x384c94ed141cf38e0,0x25bd91dfa529b1ee,0x1287a70a968deb4,0x64df96a5f1255,0x155405f2e2c0,0x21eebd3778]
def m11 : List ℤ := raw_ints% [0x0,0x13b30639460bf39a9485000000000,-0x16d685298374a0a96f58da83a75400,0xc9810aa75895c70513d421bebcc300,-0x464f63f9573e568d278eb8d08b68600,0x116b4faae5dcf80fc42c199e1ac9bcc0,-0x342654cef7696b6e3ad952aa498c45c0,0x7a73d202742a8af0dedc8016ca0c94b0,-0xe72c248a614cf0b6434855b0d17e8ee0,0x164d809d5539f98b512ac1595741ebbbc,-0x1c7a07387d6327d99158994460aff6268,0x1e4ed5e5f22ae8f6e4aba2c51cd3026f8,-0x1b03f8b97f1d261310bd18d9a16ed4028,0x143693da67c8c3aeebef3a1b62d803fa3,-0xcb1f42ad589c408ff59daf220437e502,0x6addab44fd9e6bc9c128c2c8f0158a4a,-0x2ee631fa0aa1180f5ec4022320c0388a,0x110e72bc69932357f3adf71148d31b76,-0x517e3969b34cfeff4a2e91845a713ea,0x13bbf8e34019b81afde9d009a82bb82,-0x3cfe11eed2fae57d329d9933b5deb2,0x9322eb96a6a5ef5455e54bef8a874,-0x10d24bc68d99f99790d7ed78ef566,0x166f9c52e8706abb8e272d5c4e2e,-0x14aa7a88ca84de03359bda6269e,0xc28a2d711e820582bc07c7d9e,-0x40fb7f349637a524b9912706,0xa2f48e03ed0dd82b7e2d5e,-0x87d37bec6e9f2f61db9e,0x112c36581727b54659]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 16 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 35 indices rho q11 m11 11 11792619219693312000 20=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 35 indices rho q11 m11 11 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r12 : List ℤ := raw_ints% [-0x2fbc8a3e48afabb8ea040000,-0x472e7d8fb7ab6de5b69ac000,-0x30f654f1d71c1bf5852b2800,-0x149f14eacc2f1505a6bb2000,-0x5f3782a8ae5115a65377a80,-0x13f50edd314df6bd4486e40,-0x32407773a8d48ee08aaa70,-0x60d0c829118576f83b820,-0x9003058a4daecfbc1df0,-0xa58a90f6b24c4e20094,-0x9200575ae36569a213,-0x6123bdd89efd84aa0,-0x2f4312700fbb17e2,-0xfe6dd2d6651f4c,-0x350c9d29ebf0b,-0x52e7de07300]
def m12 : List ℤ := raw_ints% [0x0,-0x189fc7c7978ef08139a64000000000,0x1c2d9bb6df9da31ec1b3a83c56b3c00,-0xf540e19077f1ed711be5ad6fb827900,0x545c09f88154dbaa7963ff93b114ba00,-0x14968360908951ecd46c42d2c3a99c040,0x3cab13e9672ec2f655a2ccac4a311ac40,-0x8c188494e3a52a29f7eba45aa4e0419d0,0x103da93e7361bc7ddc05cbbf4ca73a16a0,-0x189b0331539d0f86c3b7d5a986b89fed24,0x1ecca693d1db985067da3af181b4e8ecd8,-0x201834ee55ef8bf52ad484b62def90e9c0,0x1bf83d7a86c1a155215d1034f8cbe40b28,-0x146d644697b034eca74f5b539cc9f5a095,0xc80223ad742aac1449943156648d94d3e,-0x6651543e1018f74faf0f9c244870dcbbc,0x2b8f08a0e1e77cee9a17cc3826abc668a,-0xf535a1fdc372c9789f316daa87313a2c,0x469d78edcec850764b53fc5f5f833bde,-0x106e103d780fbffbfde56a58f40c9aa4,0x3093503f807dd33e0e91f2649d4379a,-0x6f80eaec7de5e99d7ff793be924c5e,0xc0d568ca36561653a18690eee06ca,-0xf13bdf9ac98b81620a6fe8cf0574,0xce57f3666710192e96e1b2dcc8e,-0x6f5114181aa7af66793b632738,0x218b18a9e725eb1767f2ceb02,-0x4a4d2a3f119486762c4b79c,0x353d6917a116ebbaba986,-0x59547e3162c55ea445]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 16 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 35 indices rho q12 m12 12 11792619219693312000 20=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 35 indices rho q12 m12 12 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r13 : List ℤ := raw_ints% [0x74a1d2b1bc15bb7579e800000,0xada5179de0074fafdb8b40000,0x773b70b7d1cfab61c8aea4000,0x321e067fa6410ee3246af5800,0xe6e3912fa52941b0072b9000,0x30450edc5b34746603318580,0x792f9ef65a4c8e953df49c0,0xe8b1a81b85cb5ea3818d90,0x158ca1b648b308a8ceeae0,0x18a8e4bd223b22b2ee210,0x15a28b0387de3691336c,0xe4e345b064e7390ded,0x6e8aed25f0bd38760,0x24dcfcb73355a81e,0x79a4750fb55cb4,0xbb8884bb18f5]
def m13 : List ℤ := raw_ints% [0x0,0x1ec7b9b97d72aca1880fd0000000000,-0x22c8bde421ef1f1f76de05b7a6f57400,0x12acb6181584123a5ea391e4d89aefb00,-0x655d64fa8891acbdb06d7cc0604bf1600,0x18616a713cd684aea37b61e97952d5e2c0,-0x46bfc981eabfc4f04c5dd5a97dc8d101c0,0xa0be5f93ae7c4d5c6c00f44e9d093ce0b0,-0x1251188109bb9e124119d861d517e5978e0,0x1b3f9f91d9ab86e62bdebd4399577bd483c,-0x21738b40f32f2c2489e0be3b7b156cbed68,0x22247d75107e9d96200aadff6af39f71e18,-0x1d19eb48af166d8da8ebec8b39f802f96e8,0x14c0ca2be1353d309334f77bbd541d33ba3,-0xc60b5a0195c9bf3928fa65740626e4e842,0x628917002aaabafeb08e6c9a0af384eb32,-0x28b341c5f9f896b58c7a19154b1fd225fa,0xddae5c36ed02db7ef78050642cfc2a9ee,-0x3d913bd1a398eba28e9bbb8d366e5190a,0xdc32bf3ed4f784a4bc006f8d541efeea,-0x26ea29f9d6904eb981c6eb2e09544142,0x54f82395391b0e4b654248d23c817ec,-0x8ada974bacaaa9eb4fd77532336766,0xa2ce9bc1d23e9c2057bbaa70c6ea6,-0x813331f38074fe1dabd41380e12e,0x3fd6912910cd81bbd82cc7b6e46,-0x115511d2d0cb6a07497337dfa6,0x21e027f36a175c4fbf8f6d76,-0x14da485d42a1fdf930664e,0x1d0539e544deb582941]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 16 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 35 indices rho q13 m13 13 11792619219693312000 20=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 35 indices rho q13 m13 13 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r14 : List ℤ := raw_ints% [-0x107d294592ac3b1eaa994ed8000,-0x1883ebce9509000e783008f8800,-0x10cea1a6bcba0351e8d3a895300,-0x70d5ed67e82bdabd9cc3189180,-0x206ccf87ce7480248849ebdbd0,-0x6c379d9771540e79a330fbf00,-0x10eff48c7f17358518cfadd08,-0x206d6cfd2f07d60027559048,-0x2fe382660cc4e4752d057b5,-0x369742fc7e594bb563d220,-0x2fae9c6b49d098e751d1c,-0x1f5d7b12b6c2a8796464,-0xf0e40ed6d78dfeb5b1,-0x4fbfc5a8f8c1c21e0,-0x104dd38a27d9ad86,-0x18de32a27622b4]
def m14 : List ℤ := raw_ints% [0x0,-0x2679a827dccf57c9ea13c40000000000,0x2af59bb89ec8ddbb0a368036164379c00,-0x16c5f4f4aa3e1a747fd1f7b440e5fca100,0x79f8ef711c8232eca91b6a921237f86a00,-0x1ced3946bd5e85ba76eb8b50ea595965240,0x52b3416721b09f8bedd7e61857e0b4bc040,-0xb8f45ec55ab95853ff9f198905237cfc5d0,0x14b9b5b089ab8845d394c5f14c8b74afc0a0,-0x1e496cb6ae72b122934f6d44a265b31729a4,0x247b0b08b7430abef21ca6335658595abfd8,-0x247bfb7c522a91a811643f20bbe93b7e2460,0x1e6cecccb92f7f0999d9d2bd186f561f92e8,-0x1531793ab8d35b712b9953d6dc18ed4cc2d5,0xc52be63b81295d5a70b61419ae6f306f6fe,-0x5f6f2bdda0f777e51d5f01942c7cd876244,0x2640bb5b8ecc75f8fc45d6df37b2f1f043a,-0xc99be07449fd6ae9f08d36d30407b4a084,0x360023ed023784cb728e30d6f82f40f6fe,-0xb9890e4ec6c954fb6deed37e0048905ac,0x1f5a31b93ce909cb2ae8a0d9d9ff346ea,-0x4117c0f1c19ece6176f86c9b40c7e036,0x6475cd4171d9750cd42bacd89f8914a,-0x6e51837c4124a76075a9b1a5cd21cc,0x51256914c8928efe39490f6b7f4de,-0x24aeb2d0ff8920dbefe924bbbc80,0x8f69489a4fa91b251dd74676a2,-0xf711c99b3acae4aca7c50b14,0x829494d3fd4865621c3076,-0x96bbbd77bef5af3a40d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 16 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 35 indices rho q14 m14 14 11792619219693312000 20=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 35 indices rho q14 m14 14 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x18de32a27622b4,0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r15 : List ℤ := raw_ints% [0x22fbfe356731d3443a2953460000,0x33f3309ad7058f0681c3695ba000,0x239105e272fb7e079c1bc279e400,0xee67e9c233585ac2f6e20b30300,0x4463b45f06552a389737b455bc0,0xe3cba68578c864ea46d2780030,0x2392b07546b8eb430c1437f620,0x43eeff477d03705f106e80618,0x6408b6f1b1a37047c9e991ac,0x71a83bee0357862995c7c4b,0x62e55fee91c4624caf4f10,0x40c4856c5bf77bce7e024,0x1eee1bd93e2d1d547754,0xa2d966bb46eaec274f,0x210e2586799f28e30,0x31fc404c4716f1a]
def m15 : List ℤ := raw_ints% [0x0,0x30181231d4032dbc6498b500000000000,-0x3514b1b360aaaa45347348073a70209400,0x1bcc1c909f91d134797e0c82ecb4dbff300,-0x92f96baaf433553a29b20954cc37a562600,0x2262558cb86d943d8db918fd686b3c4678c0,-0x60e4a4d72bd0411595fc45e693ff016b5dc0,0xd565e15382d17e136ee3036326eafab77cb0,-0x17868b385a71c95d34625693cd6d9eeb912e0,0x21c90bf1333654301e7431e8b52a92fcf24bc,-0x27f19e927a8cb69f4f0fcdc6f57237f9b5868,0x27286be6bb66819b0453c8537072be5783638,-0x1ff5fe0229dd69a49cba1e4571cde9d5bcba8,0x15c099a9447e380d750ee881a3840cf9c36a3,-0xc559cb5b6cc7f77d45fea7b683c3465bcf82,0x5cf1f1eb8f615552664ed1dfeadd415da95a,-0x24289d9674072291620699c1e9cf487ae8ea,0xb86bbc70f195fa8548962c92c1e6495be26,-0x2fa39fb0b727b641b468c2e7293f0b8d92a,0x9d386e8cfe0bb65555b2aee0e76c792b92,-0x1965bff0293de00a6891146fad861dea52,0x321e5452dd20ddcbb95de5a533af5cb24,-0x490265fbebe3f87d41f7d7dc2862e766,0x4b0826dfcc8d16575b24beff3d304de,-0x331bbc13924aa5cda9bcf95f21ae3e,0x151d70f2b2e565a814e64e521262e,-0x4a3643a9e21d8454740ea94bb46,0x709868b4d679fa7574103c04e,-0x33116b7a10c82c3224b647e,0x30e5c3dbad6cc0a8bc69]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 16 54 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 54 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 35 indices rho q15 m15 15 11792619219693312000 20=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 35 indices rho q15 m15 15 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x31fc404c4716f1a,-0x18de32a27622b4,0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r16 : List ℤ := raw_ints% [-0x4651d17bde4ca2030a00838c30000,-0x684e51623f938fb33583cdaf49000,-0x47529926e5f11e7abcf7d34715600,-0x1dd6b6603b804f83f26a920966700,-0x88bd5fa321ed37e5adb987bc2fa0,-0x1c6a9687f8e1d0b7b097dc79d240,-0x46dc5049d3957fb44efd9233060,-0x870525588a4989c680adf37170,-0xc6516a8b800d1ee748dd784a2,-0xe0ad96615d8e6c8178d09854,-0xc2db28f561160197447dd4d,-0x7f21a2ed0f7c159a426b90,-0x3c729e67b9b3e8281e838,-0x13ca5e55282586b1672c,-0x3fe417eeba8de763b9,-0x5feecb51deac3e20]
def m16 : List ℤ := raw_ints% [0x0,-0x3c1e16be4903f92b7dbee2400000000000,0x419dddff2fedd5e70cb01941556526afc00,-0x21f5e28658db09eb059dc1c438aefd3f0900,0xb1577c8680e7f760acf76264bd714eaf9a00,-0x28f1f1d2f7e3b13aa1c4ddcdd1daf9b3f3440,0x71c7044c88c0cc87fc3ae38f308a81f84b440,-0xf6e094f29eb957ae6a3586a436a9e99ea61d0,0x1ac98309bd3c5f3e6b5f53773c08709452daa0,-0x25d225486b518a09f903c7d17c50992a13be24,0x2be843d3f3bc7999cbaf3c6f00254da06e62d8,-0x2a3538292faec6079890e220a471283c778400,0x21bac5920dc97640c44f313c675a9d165800a8,-0x166fcb9c40357db86019bad4caa7e566ae3015,0xc68f99d67f9ab6d9b0817ab6ff61fc90604be,-0x5b03422271e26607996940e8d6c38d396bd0c,0x225eb908a6fc63080bd3e561183bffb62996a,-0xa9a728bebffec269b22b7598c18150a7919c,0x2a43a392531ec6560e5b492361f7256a911e,-0x85f5f4e75bbbdeea20fc63ddcba9e6d00f4,0x14ae7c351e9eedcfe2330fcef0cefa11aba,-0x26c6813eea1d44ba6b00299be093f164ce,0x3548ee0f4244ce7644ea32e71760ae1ca,-0x3335bc177460fd3838f3c33a78b2b0e4,0x20459ef0e453005d90e11781da10dae,-0xc2c3446237770ee14b9cc05bb6808,0x266c1abe3b650040db1257965942,-0x334bcbb85e03dbc8a53579424c,0x13f50b31e70e1145c84524e6,-0xfd9f460d044b8e8e1f15]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 16 56 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 56 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 35 indices rho q16 m16 16 11792619219693312000 20=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 35 indices rho q16 m16 16 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x5feecb51deac3e20,0x31fc404c4716f1a,-0x18de32a27622b4,0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r17 : List ℤ := raw_ints% [0x86f5696c657f8676cf6001a9f00000,0xc7fcbbed0cd6ea187e60d1fffa0000,0x889896191fa87fdc84c89258825000,0x3913594da7795923355fe65d8b1a00,0x1053112be9406c027460156b10cb00,0x3631c09c4c980a262f57d0cb43060,0x86e7a76d292222dad19ef335cac0,0x1008b743488930fe0f95e1569ca0,0x177f98a074d3c2c6820872fceb0,0x1a8e011f9a1368b05203cb9b5e,0x16f6d143b5b07e38fa5ef4f2c,0xeef09104179d1c75221d4b3,0x712f296ad9be2e76739530,0x24e56c1fc542d691d1fc8,0x76840e769cfa65b8354,0xb0e76e93b68a92547]
def m17 : List ℤ := raw_ints% [0x0,0x4b259c6ddb44f7765d2e9ad000000000000,-0x51261557c15664a475121ea485681df0b400,0x2986d8d1ec68ba4b05f6628f2fdb0bbadab00,-0xd64442eec37af8122ed90a0a3bab8b7ffb600,0x30d80784253b9c940a28b6a71483e063f8fec0,-0x85e5ab654dac08dfd55729e55e59abe4e459c0,0x11e5ba95451269d840897f196798977b826e8b0,-0x1e97fb15bc55154e348fecaa29409e2d372dce0,0x2a7bfd07a948719474de2ccae412a2b573e513c,-0x3072f3ced33064d8e641fdffc48f0d2037d2368,0x2dafbda35fbda0f507a2cb049ae9dc10f339758,-0x23c1f3fd36dc8c3877f09a087d09698bd600e68,0x17412d8bc2f686d20066cfb171d89c2c1a3e8a3,-0xc8cc1f2c155c849c53fdcd26bae98073cfdac2,0x5997e755c7a0dbdfe7e1a7dcb91a1fb51656c2,-0x20d90747b55d842c7d89b93bfd174fbf1e3d5a,0x9ced572f9c2eec6294296b12faf09cd7eee1e,-0x25b36d517339d588a0a30a4343e5e205b4c4a,0x72bff3ad5fbed6acfa503b4dfcda6a41b37a,-0x10ed1f78c7cb183d2dd5391c51adeb8e1de2,0x1e234449b206e82a9851f37fef88e32881c,-0x270b8691ff0bdfccc2ccf1c162cd3e4566,0x2310785cf04fad4eb60fe51a12a8776d6,-0x146cd859050d34755e37bd3bcdeed1ce,0x706da67bf62489e6ce91f10c1d5756,-0x13e6670327125634ea5062bd2b1e6,0x175c5f37fa8e59ee0244cdc13e6,-0x7cb252294cdffb3ffb4d622e,0x5229f719ef57051dbb9d1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 16 58 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 58 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 35 indices rho q17 m17 17 11792619219693312000 20=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 35 indices rho q17 m17 17 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0xb0e76e93b68a92547,-0x5feecb51deac3e20,0x31fc404c4716f1a,-0x18de32a27622b4,0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r18 : List ℤ := raw_ints% [-0xf8de8b39df88a30da34967802d48000,-0x170744ff09047dca7840fa135058d800,-0xfb693bf730662f6df7600551383d100,-0x68eebed05bf54dcd0d17a822b005080,-0x1df98b6579576713cec1ccc99f02bf0,-0x635f2a6bbdb00517816978dd97da00,-0xf6fa10055b5dbf890642fe133e978,-0x1d4d81637df8c4c1c8c938a699198,-0x2adc03be49fe6425e188d33f3c17,-0x305382e956c5b450d7f6a1f1050,-0x29afd4203c0680d6bb7fdb5086,-0x1b082e5663f9b127842bc42c4,-0xcc36543df1357ab9cd08b97,-0x42526ca54107c5ad026090,-0xd41f0c5b379aab286544,-0x13b0bfecc9a1dc99c24]
def m18 : List ℤ := raw_ints% [0x0,-0x5def038952163553f47a4184000000000000,0x64667e7f1c1d8bcde686c5340a6ba38dd5c00,-0x32d27eb3891f509b1062f80b6530c4cde3b100,0x103367b3d43b7e40ba95d29e0668fadbc664a00,-0x3a5dc53b882cc57e19a82538f5307ae2644e640,0x9de96d1ed974f34b5e55cbbf6e693534d9f8840,-0x14d0095378c4779f7628589cbdc6d2270bc36dd0,0x230b791facaa07658e0aa691da9e3c907c5ce4a0,-0x2fe227cf3ed13cdfb4687d953e0f1fbd85f1eaa4,0x35a92f83c143f1a82ddb8909d860f5e0121055d8,-0x31a7a2ce3ca775480ecb4516b8e4f96ad649d0a0,0x2613696ed71894970649f233769a041e87374468,-0x183765b6ac58a50bddcd59766129b05670a0c055,0xcc12352ac32d682c1ef135d2987ff14708e167e,-0x58a7338c8a3950715f24278e1f8badc125a0614,0x1f8f46528a0eb4839402b3d054197e154e9d21a,-0x91ef0572919d75121ce44d70257b146e490b74,0x21cf0cc1d7bbffa6ddf59d96503381b1b3423e,-0x62cc9c0c2e631d6bd4e61075fce84b27e767c,0xdeb7d2af3b927bafaa2820db603a3efe470a,-0x1786eabd8d045a84a8acd1744cfe3e65e826,0x1cb7f3c2e15289e86f99a87f43998c0a84a,-0x1814c9662cba6ffed959f410cea48a60bc,0xcf452c71e79cdbe07bc2f30a06516afe,-0x40f969f688bb451313807923495d3d0,0xa4f353799a3441dc1a3159c790ae2,-0xaa26b3258b4bb418662d58c5344,0x30a92e977ba1bdc86bd6102d6,-0x1a99dec4c3cd8c1aa0c75d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 16 60 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 60 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 35 indices rho q18 m18 18 11792619219693312000 20=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 35 indices rho q18 m18 18 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x13b0bfecc9a1dc99c24,0xb0e76e93b68a92547,-0x5feecb51deac3e20,0x31fc404c4716f1a,-0x18de32a27622b4,0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r19 : List ℤ := raw_ints% [0x1bb358e457edb868ecd4424afd60e0000,0x28fa4fd112beeb852d9aa8023430a2000,0x1bef7957916ab69afe8ca311d8730a400,0xba5d41b792f2e13122f6e1e58bdc0d00,0x352d27677013aae5811ad8e7d140cbc0,0xb0114f49ee6e2dedf0fe71561dd0010,0x1b4fb3a1d039be7f4ebfbbb537780a0,0x33c3c0a89bd3c86127bd88b82a4728,0x4b9483699f00eb483a37821f390cc,0x550d6d0e5e7fa4dedbbc584887e9,0x49345ce84f3133a27f726113b20,0x2f59cbff227ea99c6acb8d9bba,0x164b1b2967cf3955bd8de5b94,0x737803ba235ca70d86eed69,0x16ff15f39899b43f760440,0x220252b4a0cc9a5996dc]
def m19 : List ℤ := raw_ints% [0x0,0x756ac46ba69bc2a8f198d1e50000000000000,-0x7c454ca7918bc761c4219b32a35fd2386dd400,0x3e400ebfb0aeb2d74b0e282a94e225707e62300,-0x139fab343d77ce8bdece4b6ca5128754debfc600,0x45dc8cbf2eaba87a4aff0cf0917eccd0ae86f4c0,-0xba9f2168cfc43ce82b225f11d2b4a4e00284f5c0,0x18435c731a3b4a41ad08d437c19dd9c2774a1a4b0,-0x284284c262bd7058bb46f586f5c13c007041a56e0,0x3625639f8cf53a5910628709765788f573908cdbc,-0x3ba6a8d75853248898750864981051486516b4e68,0x362f3ce6285836397bb50032a058dd940ff5aa978,-0x28b86346224b3b77a4d552091f6451ad156438f28,0x1955aed210c253c793c1efbdde4c88bce4403c9a3,-0xd068ad7db91db80e9a6e4bdec73b2f14332b6a02,0x582aad05ae08453985a3d99a6981250359ed156a,-0x1e7aa8cbd62bf62aca415010160ac78287e19f4a,0x886b071515abd04a9c88596ae281ba810ec3fd6,-0x1e79803b33726265961c18df49e8025e2144a6a,0x557cfe4320a54421bca941023beac5164618a2,-0xb802b1a51f3b8b6ba2da79f801dc628391ff2,0x12716a6847a02f0f5410274619ff561e284d4,-0x1532b9764bf4932e1918bf8640f293013166,0x10958b7ce58f7557748d271533bd1e25a8e,-0x83b4f1af032407b7e9d3868799b474fde,0x25961f0f4ce35702b26cd0a9c5cc83be,-0x55779f63a8f474b68ef7be9aa55b86,0x4d6c4d3c9f78a96b957a097e463e,-0x12f9d449dbef218f9a07526b5e,0x89b61c72423c322f716b79]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 16 62 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 62 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 35 indices rho q19 m19 19 11792619219693312000 20=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 35 indices rho q19 m19 19 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x220252b4a0cc9a5996dc,-0x13b0bfecc9a1dc99c24,0xb0e76e93b68a92547,-0x5feecb51deac3e20,0x31fc404c4716f1a,-0x18de32a27622b4,0xbb8884bb18f5,-0x52e7de07300,0x21eebd3778,-0xca241024,0x42c9c43,-0x12df40,0x44b6,-0xb4,0x1]
def r20 : List ℤ := raw_ints% [-0x2fd8173d6b8750b785eb1f112c68720000,-0x46b9607e8eed58c7b9218379dba4cb6000,-0x302cafbdbdeb5a8859733dc4f252316400,-0x1411722ad975b3b97b7bc70d1cb0e9fe00,-0x5b867678deea0255acc6b9050a0d586c0,-0x12eb2963253980a10cda0f3c1479b0840,-0x2ee50a984a2e5640ab7341ca30995d50,-0x58c1c64e9e726ce50de28ead4b486c0,-0x816347f9ea2c84e887c622c2f9f974,-0x915905e8ac101bebf12eb7e2fab34,-0x7cdaa2500829a9ac3546912f60a7,-0x509484386d6bb2309237d3488a0,-0x25d7e74ff94c18140b569c17ee,-0xc37484aa92ae37912aa2eb6c,-0x26cd05efb70b74195ca29c7,-0x392baa98506245687d7a0]
def m20 : List ℤ := raw_ints% [0x0,-0x92c575869042b3532dff065e40000000000000,0x99e0c713c508da78abe1dd922ec1c9a3026bc00,-0x4c4f381aa228e587e095144da51fcfa916149900,0x17cc7569d5918ca786eb4b244fe84d3102de87a00,-0x53c1a260359352057b59e777d799bdc98220be840,0xdcff9a68daaeea23bf6208e8dfdb3230a87673c40,-0x1c5abb0fd6e1c3605ed359f586b752c2d806c669d0,0x2e61b00cb419a82b1dd23bae42de315b06913f5ea0,-0x3d6c9dc272c942325c3a1937eb866852295ba7ef24,0x428c0d2933dc7ac3ca1c354da79f4eb497a71418d8,-0x3b5c0945c7be108a9c33abaa145818d958f7771240,0x2bbbb2a4282a96aeb49abe64bf1e12f3a761c9ce28,-0x1a9fe83ccbc689a540f3054dac2e5bc7bea8730b95,0xd5da57514de2a95bf78f115fbd54b3ce9a4cb8c3e,-0x581dce8bee8afc9f65c1f4d635fdafe94831d775c,0x1d959685f7357d3f820aa8b5d57e212d778b17a4a,-0x802b8d58792103dd2e1247fe664d4159ce343c0c,0x1b9b400ea445277f6d0d55ff65c62eb3f165c25e,-0x4a53402c8f76d7c5c10835278a90c5730dd6044,0x98b52549713acfee410742b4522f41533ebfda,-0xe83d8d4d7d75ad9ad6d622f46f15a4416283e,0xfb2fdee33ed65bfcdcfd4f581ab0717654ca,-0xb7349da9e5c59f1ae5f8964b0f2fe308f54,0x53d545afb9a8fe1317d9e84a61852640ce,-0x15c2cf9b5b72f8de68e99c0331ebcb9d8,0x2c49657b8f687873e8505f5dec30382,-0x2336891ab408eb12efc03c0ae23fc,0x7651439ca8ee26dc4eb1d96646,-0x2c87f41872226bcf2d49ee5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 16 64 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 64 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 35 indices rho q20 m20 20 11792619219693312000 20=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 35 indices rho q20 m20 20 11792619219693312000 20 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_20
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<21) : intPolyRF (mz e)=rfPoly (C (11792619219693312000:ℚ))*rfX^20*(1-rfX)^14*momentRF (key size) (X^e) := by
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
#print axioms moment_source_20
end
end CatalanCore.Li2.NVMod.FamilySource.V5C21
