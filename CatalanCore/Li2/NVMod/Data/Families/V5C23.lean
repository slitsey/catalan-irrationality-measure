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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C23
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,23,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0x289f1881cd4090000,0x414c5669119863000,0x30e3dcb546b535a00,0x16a9d82270fa79600,0x74abb47e641c6560,0x1badcac08b02d3b0,0x5050772b7ecb940,0xb6374e11d9b028,0x147cc352136b0e,0x1d739b68fb0c3,0x21ec73f746d9,0x1f3e810dd34,0x16d86d8540,0xd15dd132,0x5be643e,0x1dd60c,0x6bfa,0xf3,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0x7,-0x7,0x4d,-0x79,0x4fe1,-0x4fe1,0x4fe1,-0x127c,0x5377f,-0x7e7,0x19789,-0x65e24,0x19789,-0xf83]
def rhoDenominators : List ℤ := raw_ints% [0x5c043f600,0x267d980,0x648c0,0x2d3f,0x11e0,0x1b8,0x2d0,0xf5,0x3100,0x1440,0xb40,0x1ef,0x8b38,0x11e,0x6d7c,0x4cfb3,0x59600,0x22880]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 23
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤22))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤22 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 23 omega5=padCoefficients 23 (omegaCoefficients 22 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 22 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 23 omega6=padCoefficients 23 (omegaCoefficients 22 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 22 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 23 omega7=padCoefficients 23 (omegaCoefficients 22 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 22 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 23 omega8=padCoefficients 23 (omegaCoefficients 22 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 22 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 23 omega9=padCoefficients 23 (omegaCoefficients 22 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 22 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 23 omega10=padCoefficients 23 (omegaCoefficients 22 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 22 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 23 omega11=padCoefficients 23 (omegaCoefficients 22 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 22 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 23 omega12=padCoefficients 23 (omegaCoefficients 22 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 22 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 23 omega13=padCoefficients 23 (omegaCoefficients 22 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 22 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 23 omega14=padCoefficients 23 (omegaCoefficients 22 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 22 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 23 omega15=padCoefficients 23 (omegaCoefficients 22 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 22 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 23 omega16=padCoefficients 23 (omegaCoefficients 22 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 22 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 23 omega17=padCoefficients 23 (omegaCoefficients 22 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 22 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 23 omega18=padCoefficients 23 (omegaCoefficients 22 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 22 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 23 omega19=padCoefficients 23 (omegaCoefficients 22 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 22 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 23 omega20=padCoefficients 23 (omegaCoefficients 22 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 22 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 23 omega21=padCoefficients 23 (omegaCoefficients 22 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 22 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 23 omega22=padCoefficients 23 (omegaCoefficients 22 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 22 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
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
  | 21=>omega21
  | 22=>omega22
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 22 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 23 at hb
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
  · exact omega_spec_21
  · exact omega_spec_22
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x160b74072e1edb56e400,0x23afa1a502fd965f6f800,-0x1bd33ff6d96f1a280787c0,0xdea210a48b538106ebb6c0,-0x5035c8be55871899b5cbaf0,0x162c3a8d5a21a544075a9500,-0x4e3f6b8ff6fa37ac985fcf40,0xe2340a5f71af4ac30a237f70,-0x221bdfc42b9e32087db152d7c,0x459dc3f9af1f4627e29c1c540,-0x796a0749679da1420283952e0,0xb64b55bcdc9dde2ee61aa5240,-0xece7bf4e6af80a3abe434bf40,0x10b7eb1360fd50c7cad7157540,-0x1070ba5da990724c7eea47a7c0,0xe1894893766aa0593be403f9c,-0xa89a15345c431905dde209e1f,0x6dc3d23fe3700914364cb1850,-0x3e16652bb90cf0cca947a7ba8,0x1e6732673677ca1cc4cd53b20,-0xcd2edb8ba17f384d524e63a4,0x4a0cd8dfd0638d871c331e10,-0x16aae161b7be6e9bcf91b858,0x5d1c1994135991bbdb60268,-0x13c1a7a2ff60efb42b69bc6,0x3661d97ff24f5a653ed1b0,-0x764c823a19bcf53e3a6f8,0xc44f234e7ef3c2e6f340,-0xec3649e74d775280654,0xbebcbac1717f445a70,-0x5acfa6f2fe29649e8,0x13d78ae07b695d2c,-0x10bc59c1c5d9f7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 18 31 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 31 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 39 indices rho q0 m0 0 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 39 indices rho q0 m0 0 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1e4fbf89df6a6d9779800,-0x3031b88c05033b5bdadf00,0x24e44b08980ffc5ed0636c0,-0x121a500fd4d8f4ac0fbdd780,0x665844c0a2c244cd3d1b55b0,-0x1bbb6085afc4d856a81831e00,0x5fdfd99f5d9181cb737f2d840,-0x10f59aa8fdd084ab97589d89a0,0x280841182d6e47c117e5c1e62c,-0x4fe2046fc44a6c03dbd56b97c0,0x881b3c122454f52e80fccff660,-0xc7797244d8e2452f149b790840,0xfcd0960eabab7626b30b0c8e40,-0x1161e8ad0395deccca7dcba74c0,0x10a2d202cabb94a06912f471300,-0xdddaa3a974bf12710acd65dc28,0xa1038c19822ab34ead9f7e580b,-0x659f61fb95d5c00f77998c1730,0x37a2f5cc0b317aeecbfa9b2608,-0x1a5279352ab66849a3c30f69b0,0xab47a0ce022bb18578eb95a34,-0x3b7643a115dabd0601cba67b0,0x117649e4b2a88f6b003a174f8,-0x44988fdabd022055d3c4b760,0xdde1b8c0b47a94dfcce5efe,-0x2434bd166753886c516bf50,0x4a49e515827debfb9c3018,-0x7376d18a1dde5460aa310,0x80eff12ae6cf52e8da24,-0x5f6a92358688c2a1450,0x28e1bd7f58e4ca1508,-0x7d01ef5903671a58,0x57f2d993883a03]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 18 32 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 32 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 39 indices rho q1 m1 1 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 39 indices rho q1 m1 1 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x29ada75d933256b0471000,0x411eaa4082130a26a0fe500,-0x30f66a9c493930aa7a0435c0,0x1796757c2e45fe037d86a6400,-0x82dac739e79305a5064ce4770,0x22c60146cfb4545945b34d2400,-0x75d4d0bc6b6cea016d159d9d40,0x146ab17ef43f9b1d17c463091c0,-0x2f2cde9c9d3f10e785abd51379c,0x5c14e4e6ba179f7689e13e293c0,-0x9958d04157ff9393cb9aa84cee0,0xdb7b0a6a1a31e34440b8b8b3f40,-0x10f694a41ae1b7b0f130c9ca6440,0x12308528bd332a45f6893333b2c0,-0x10f33ab55f648069db76c52709c0,0xdbd43407a07d8caaf41f0eb8e30,-0x9af4237f57e634dc1d707d7d127,0x5ed844fb90080fd6efdacc6fcb0,-0x32468a34ddec004e3c54e20b928,0x16fcc820fc40d626356f12c58d0,-0x9041edcaa857d8b69a00e547c4,0x302edd9bcdaf62a729831a71b0,-0xd936f507335f7bd7a01ee9c58,0x33004782fb887ed1f7eb70f70,-0x9d28201c68764cf42c411ed6,0x1850ef469b45a3c35a25eed0,-0x2f095d24e75d8ee21196278,0x446bb4e65801717371b630,-0x46d398939e0bed141de74,0x2ff51a6b167bc6027b50,-0x127394fe75767c57ee8,0x3139938080c317660,-0x1cda043c46893ff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 18 33 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 33 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 39 indices rho q2 m2 2 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 39 indices rho q2 m2 2 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x394ec620aa65373261b6000,-0x5808ae80ac8756280bad0500,0x410c65185a8ec3deed4be38c0,-0x1ec7f22f769cb5b73191d0e300,0xa7a4b22b344562e2405e921c30,-0x2bb66aa9e9c583846b3e39ee800,0x9140c077efb83464886720d9640,-0x18aa4730edba29ca2f5b121fec80,0x37d09dd6276c380df4993da26fcc,-0x6a9e4f5b692b2f25b22b811594c0,0xada079adf479836dae39c4849960,-0xf2cd361affb66959ce6a352c3440,0x125162069bd14de829a4757256840,-0x13277a2778a75343cea673bfdd3c0,0x1162ee0a0025c0374f31299091000,-0xdb6079de03ff9c697efc2b7367e0,0x963e02421c0b088824e228c433f3,-0x593711b04458c7cd6861fc5230f0,0x2dcd71f7e850c4e17f6f539b2c48,-0x143ea2f7bd7345672b238a0aaf50,0x7a8ce793eac2df4461e13f0bf14,-0x27632d59eecfe2c0201d73c90f0,0xaa5f57a258be9b96b9caf219b8,-0x264123f1bc71595d3261df0490,0x70473e50d03968dd1498a170e,-0x10779aea08e72c6feaa29c290,0x1e03ae78cd9e7e2a5ed9b0d8,-0x28d40b80ec6b335598e0b30,0x27222656a1bb8a67753284,-0x1834ddeea1916b8dcd610,0x85889c9cad3f79e6548,-0x13617a4280da5ea550,0x974360de6d31aab]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 18 34 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 34 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 39 indices rho q3 m3 3 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 39 indices rho q3 m3 3 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x4ecc506cea4b2be5465a4000,0x7711fdb964ed5b39e8d609100,-0x56814ac8b578ddbd4f595a87c0,0x283a592acc021599894c6bca900,-0xd73388d8ea5154f2979be8c0ff0,0x3715ef760604aeaf8659a2c80000,-0xb39634cfbb9dbe2e6af37ea44340,0x1de675b9101e24eab7ef629ed6100,-0x424bbff16c0804332494feebb4fbc,0x7bfe139e35f0773877b8aa70037c0,-0xc58b16f9de4b50c289a877dac47e0,0x10e06aa8521e182c610ae2aaa60140,-0x13e4fac0398c36f8a4cd8d068c8440,0x144b64d68230e4deaaac3cf03a1ac0,-0x11f388d90934bafc610df55e06c4c0,0xdc7335e93f15f5d9bd59bf0b0a800,-0x92bda049169475b3947f9db5a8aaf,0x548fcb727568078f3faea01b302b0,-0x2a0f15673a27cb08f69ecf4b648e8,0x11f9a6c508a04674e2c90257e6b10,-0x68fb7cd0904588bc5e048ac1bfa4,0x2078a7298aca192a7cbf02681cb0,-0x86c637fe2bd2b0f5c06849ea098,0x1cefeaf07d960950dba19b01810,-0x50e1a45608737f76ec2f2afea6,0xb3d8da1f074e635d9283882d0,-0x134b3c31d85722f20ead841b8,0x1885e6e31d480bdb63cfb670,-0x15bd1e3605f405e87dc9cd4,0xc43c776d90f83aef6da50,-0x3c81f507dd880e60eba8,0x7a0db4db1f71253330,-0x3182cb33053f87c7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 18 35 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 35 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 39 indices rho q4 m4 4 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 39 indices rho q4 m4 4 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x6c58ee95c2275c5b40bc18000,-0xa120aef607e1a7af5cacf95500,0x7326f5e616152ce4c5466ea62c0,-0x34a6bfddeb2a3a0c4169eadbb900,0x114ca6ec52594aad12dffe3fe8eb0,-0x459645ac8837c9f3d565871015000,0xdeaee4bc796b0b3386b10504c1440,-0x245e83e1fc704f900cdfe41518cc00,0x4f0c645266d36d62bc13676eb31e6c,-0x90d1c81a4215fd20342af716c6eac0,0xe1d2fbcea48c8f4b2a861001236260,-0x12ddd445bcbdb03d1548bd4142e3a40,0x15ba6c0c215d02e9eaa86c11d720440,-0x15a1e7b79a0f32fab0944dc7919f9c0,0x12a75311a681fac2878e84c6f648b00,-0xdf089c32f48057279c13b2f5b685c0,0x9057feaa02032b884ac05abeb4cb1b,-0x50bf7b111be0fb2b219f232af76a70,0x26eb63bdffb9b81d10196f59bd3a08,-0x101644ee056661618d8a5ff9819150,0x5aa9b5f86ac37d0346b77b5877d74,-0x1afd5cc994fb63f70ae3bddede870,0x6b7e230eab67b6067dde99bd1df8,-0x1611580aeff285a7c92d70fa7ed0,0x3aba1407ef17d1a962be9077e1e,-0x7bb0f6411a8873d8aa0146b110,0xc7d3332663f5e58cdad97c618,-0xed1dcce102e6a7176f1e2c30,0xc22c13497b7b1e41c854f64,-0x63c3b75897e8facebdf290,0x1b753cfe4ad0168204e08,-0x3005621d79852567eb0,0x10305530195f06813]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 18 36 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 36 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 39 indices rho q5 m5 5 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 39 indices rho q5 m5 5 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0x94fa480deaf61efd7902a10000,0xda255e50a10a1804c6de99b9900,-0x996f3217ee1a468c915097fd99c0,0x4502dd23088b3a5ac9110082e1500,-0x164b107557cbc5e060c4d7e2bd7470,0x581dceca7df6c791827218ff727000,-0x114e9a1a245ec6eaaf85d9a81fe5940,0x2c628931630f0460ca5b73efb73e600,-0x5e9c46407c93833ea63fe52a2f19adc,0xa9dc3234f02521f68cc559accbd71c0,-0x1035bcc720fb7f6828d5b37c51d1cce0,0x1532ce12a5491fa291ed82ab49d1b740,-0x17dc94cacbd152bfaf3f2f9fa6d78040,0x1731d52cdf5b2b82de035178443a8cc0,-0x13814d1fbe1c2e81b064aba73f2b8bc0,0xe324dc0e22be5822ed3415a93ae1b40,-0x8ef950cc6e564d9361b2b4ee5c83cf7,0x4daa5ad0ca405f14bac841f9015d730,-0x2448e6971a5f3a2896cef77df3a7ba8,0xe821967c49109022eb6b212c1b2190,-0x4ee99a9ef9c20f94e3a347130ccb84,0x169c9b9e8dc1bca1039296a5cc7530,-0x566a25a655031506fb0653eff4bd8,0x10f5fe81bb2c772c190e0b754c810,-0x2af6f1c8ffc2751c7895ee7950f6,0x55ae73b8cd0639bd13885c33a50,-0x823313b9790915430710ba3df8,0x901d011adb56a12eff9a42df0,-0x6ce39fe076959cddf7b3a534,0x32df18b1530c9560cc5b1d0,-0xc7994cc870b5dc3a14968,0x12e24d4f98671f9e5af0,-0x549bcb9eef48d574f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 18 37 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 37 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 39 indices rho q6 m6 6 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 39 indices rho q6 m6 6 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m7 : List ℤ := raw_ints% [0x0,0xccd8231323126a9c86639d60000,-0x1277b71b8ae91e3ee5d36132b4d00,0xcca34d9bd0de442aa7efb0c9a9cc0,-0x5a9543d80e5909284c1b6f7862a900,0x1cc86ca93e6f4184ada29728f71cd30,-0x6fd7b7f94dbadca29aa44696bba7000,0x159514555965580efeeab3ba875de240,-0x36581e2d24d273a423592363ab9dca00,0x71a80f547811d41783258a0e8c1b180c,-0xc80ea10dab974006c8d2b2a3d65974c0,0x12b3c50bf8ed10dc085b64a8dbc0d1b60,-0x17effda91a4c2a2e593e30d466871d840,0x1a5885071f7505628955fade47a4db840,-0x190364685f6d2976458c0322d36810bc0,0x148543396fe1a60ade7f988f03b89a600,-0xe8d3f2cac3dfb105d4d7fce23d71af40,0x8e93fe1499c6b865b592609f67a6ed03,-0x4b3a71382ea10d690bc5f18ccaf836f0,0x22134ea3001d3f0620b2aee6de0cffc8,-0xd2eb02e4f87e58fe0ef73156d049cd0,0x453566c11ef00c931550612e51ff2d4,-0x1316e97f5d3586c9c3081b3dfea3cf0,0x460070f84a0c792f99b620dabcb638,-0xd224d4ee62b477be6d6bf46871f50,0x1fa9466084bf9a8d45966a1128eae,-0x3bc1ee6c1be1853c76cbe626b890,0x555c2a4c82846044a584a10db58,-0x580de9ea40ac7656b0219350b0,0x3d50f785869549a1cce749b44,-0x1a02328c27c2b95003ff5610,0x5ac44b57aeabeecaec1ac8,-0x76bf7aec9da91c67b8b0,0x1b9c5ccb72f6deec3b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 18 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 39 indices rho q7 m7 7 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 39 indices rho q7 m7 7 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1]
def r8 : List ℤ := raw_ints% [-0x289f1881cd4090000,-0x414c5669119863000,-0x30e3dcb546b535a00,-0x16a9d82270fa79600,-0x74abb47e641c6560,-0x1badcac08b02d3b0,-0x5050772b7ecb940,-0xb6374e11d9b028,-0x147cc352136b0e,-0x1d739b68fb0c3,-0x21ec73f74499,-0x1f3e810d3d4,-0x16d86d74ec,-0xd15dc1a6,-0x5be5b5d,-0x1dd2ec,-0x6b50,-0xdf]
def m8 : List ℤ := raw_ints% [0x0,-0x119a9303a5039529738c8f8640000,0x1906c516ad287dd37fb9b9a177d100,-0x1112f2c9c7da840dc21dbf9d24cdbc0,0x7710793c81a0b2f90e756388bbf7d00,-0x253b198a621d4b410b2f9244170f94f0,0x8e492dc53fa396be5a2e27e0c55cb000,-0x1afcf678302c62b979125113d8716bf40,0x42c069049d0e154ff068369b066548a00,-0x8908b2bb0b31d0c3513a11e732c0a74fc,0xec94c3b5c8db257a9c3303d68e71a73c0,-0x15acac2f3cad5b86f517e238f1a166f9e0,0x1b2998c02556c6c261075aac73f4518d40,-0x1d3df38d26252f1c857af33599fdcfbc40,0x1b2072d2c8b9204f6b66e9efc9f337d6c0,-0x15b7e72b4dbb24cd031d863e64ff3b8ac0,0xf029c2dc9bd390abd2553e6af04a2a640,-0x8f1fea379a18d4903c76ee72e3f6762ff,0x495e7fdf7e8313eec15bb0556abd751b0,-0x203a59fb3d68a60198920d36841a72c68,0xc109b2c040eb1914b3e986bd006d5510,-0x3d25812651d0f3353460d91917567c64,0x103c5439c6aed76edd7a5aed12a18fb0,-0x391ff4ba8b4bc38b80e8b43cb5f3118,0xa3e7b03c13dd91ab3855d0a4abdd90,-0x177e5984417e1644ca0383069198c6,0x29f29d14041ae2870c0fc7e15b3d0,-0x384a1db2d553b690a7e3313e2438,0x36115647cf35265815264ce4670,-0x22a85573c7baf6ce8b5bf34694,0xd53ea18f929e8f02a6215f50,-0x294debe4043ed6067944528,0x2ea404fb0947281b30c70,-0x9008befa81080a1497]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 18 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 39 indices rho q8 m8 8 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 39 indices rho q8 m8 8 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0xdf,0x1]
def r9 : List ℤ := raw_ints% [0x2362965911cb3d70000,0x38b8e02d04867dad000,0x2a5530eb7f864153600,0x138d0f694b237a85000,0x6436f4b7f22514b8a0,0x17a7b7e93ab35a00f0,0x443b3b22dac328b10,0x99b5258ed4b3b998,0x112276d66d10910a,0x185fe82b5178ecf,0x1bb5bf4dd70644,0x1918ab2b96bb3,0x11f29f563eec,0x9f884bc5a2,0x42f7b905c,0x143f1917,0x403bda,0x685d]
def m9 : List ℤ := raw_ints% [0x0,0x18348a2502e4ed18fee14558980000,-0x21ee25393cac1d92e47fa9786fb2500,0x16d06c86285caf98497e5af993e206c0,-0x9cb742c82d54a46e06f121bf9f920100,0x303f09ffb8477e18b44a8ddfa3f7077b0,-0xb56d4658938f9a95f2d91af10c0237000,0x21d6e85b520c1a05f9e86cc6a3ac78c040,-0x523fef42487a96b755a00994c11ec4f200,0xa5cf67d477b4ce79ef647999aefc5dbcac,-0x118e3ab30b46254cacdc41d83b1d0d53ec0,0x193ac4321c429d3cb2c2f80d6cb9b98ec60,-0x1ef83671c3ae8355e02c1a31e60ed30a640,0x209fced1a488aed148ba3a2b0cd48261c40,-0x1d94d48959fb5c89c882284200da9cffdc0,0x171ef1814764a247270ea9be6869c056900,-0xf9426cc36e64ddf067e06f20216dc78340,0x9099f74a48dd4f4df886a3d3bca8a1a9ab,-0x480932925aa985edcfbb84f3fa5c735b70,0x1eb0fd32bfb7716cbcbf7dbeb79b64df88,-0xb1ec2bd4f5790e75b81f80ef18b86e250,0x36691e8ae3dc46ea0582cb93c5d579d34,-0xde85eb979093389f53549d7559fed170,0x2ef2d0fe6733995061fbe1f07a9ff478,-0x80ba510502a1e6877244a45f8df34d0,0x118c6b846e7528808e203ac5a34d6be,-0x1da08e45e67e4fa01cae8c9ea8f810,0x2552b12076fdf0b501965fc1d3e98,-0x2159dcfd3e92f8cd55f45863af30,0x13a7f71d02b9af8d909309c4824,-0x6d7e21134cf0ff98b1d68c990,0x12ce254979901c158039f988,-0x124e8c9480d9eddb96dd30,0x2eeb527dc8e8e4ba123]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 18 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 39 indices rho q9 m9 9 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 39 indices rho q9 m9 9 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x685d,-0xdf,0x1]
def r10 : List ℤ := raw_ints% [-0x108f63c0a289caf450000,-0x1a7b593fba3f815687000,-0x13b59b90a58fc71fce200,-0x912e65096e9460bc4800,-0x2e5752bd55e3afd783e0,-0xae4718c287980f1ae50,-0x1f43622662a48e74b50,-0x4604f61c6f3f72b378,-0x7c06b86bddfd7da7e,-0xaef82b4b44f1ddcd,-0xc4e637fe0855606,-0xb01622da2675a0,-0x7beae6b31fc8d,-0x43678cbb103e,-0x1b7e697d4e4,-0x7fa501200,-0x17c5b0bb,-0x22d46d]
def m10 : List ℤ := raw_ints% [0x0,-0x21483df2e3fac6025e75bf59d100000,0x2e05cc5ae68f7c671595ea7245f40900,-0x1e82f7c36cd95be4f8915a0a250428dc0,0xce8d595278ec6ae918c5c51175aa19500,-0x3ea1fbd6c97c4d7dcc0147a63fe8899170,0xe7d9cf26ad01286a4ca8020dc402d83000,-0x2a8b0752d56886451be89a6caaa48a47540,0x65a8b58834d65cf6c61c73b16d306aa4a00,-0xc95507bb2dae9719c55caa3aff59cf3f61c,0x14eccdb6066d9898eafded4007a1c97945c0,-0x1d7e846f7fb365f5b68868390863bfc2fee0,0x2379d3e040aab8e9632ae3ee0d998f707340,-0x2494efc1cff031479cec164e7faccdeb4840,0x206eb74001ed44ac700b0a7e4ee9a7aef0c0,-0x18c14b3967c21e1011a75ed254dc0561b1c0,0x10442ea2c122cb60d5c1f7d630d4fdf82840,-0x9303b85d4f73292612ab76dfa4fc80372c7,0x4730803cd2f78bcc29e0a548c1c49b18030,-0x1d6cbe78f311f491aa4501bbcd15b995728,0xa51e13b5931487923a92f6b7f57a057090,-0x30c0d09d523ff9e6700368198522298e44,0xbff10514a2e0f97f5c10b1aa15e1dce30,-0x26d98ef48ad1957c1ed499feef5e0cc58,0x65c631562c1a14b97001b69793658d10,-0xd30de0b3662c424095fbc62817a0616,0x150c28e30a7692cd28a854fa92cf950,-0x18dfe6b5258801c1cdb454f1215878,0x14a8c55ff4035307650de16108ef0,-0xb2eaaa45881ce02535d4bfe14f4,0x385104abe3537413e1eb6e08d0,-0x890826681f16c21a1674a2e8,0x72e397ef9ddc62dcfeb8f0,-0xf4566b1dfaf8653c19f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 18 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 39 indices rho q10 m10 10 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 39 indices rho q10 m10 10 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x22d46d,0x685d,-0xdf,0x1]
def r11 : List ℤ := raw_ints% [0x586d64d462fd0fbbd50000,0x8d1c31b4381020ae9d7000,0x68c597a9ec18ec979ce200,0x301a7664fe7eddec95fc00,0xf4e6f725461e93a0e61e0,0x395b54fbbe795f50a5e10,0xa3f0d8ff711f72c231f0,0x16d6559e2bc4fbf9d5b8,0x2838d05a946ff55797e,0x385c432719539de489,0x3ee957d424ad50098,0x37b53fc546bfe91e,0x26b9d5db15446a0,0x14bd8233a17dbd,0x84a5e094f628,0x25748f63e38,0x6b67cef72,0x949f2bc]
def m11 : List ℤ := raw_ints% [0x0,0x2dc3552df978d04341e1e71b7f600000,-0x3e73ce07002300f5f1a4823bc26c0bd00,0x28d79dd6e080a7f2309bec7c1a9945a0c0,-0x11098cb74c057ac25df2dedf9cd8ca33900,0x5173b9f47b8be5bd81eaa6ef7e356b42e30,-0x128efe31a16bedd20f4c38faa82766abf000,0x359ff83a8521dae95ab3a18f171533192e40,-0x7e0760fd34fde66df9c3549968a3b3280200,0xf54dcc172d0a078934226c79b7e730e3d44c,-0x190968ffaf506db937db68cd7fe291b3378c0,0x22a0119c17d4d7ead1fc7092375a0a61bb560,-0x28d3197dfd448f8597ccfab925e25abf30440,0x2938f6c4d7bfab3934e3972fa3b344ce19040,-0x23bf1baade739a37777898d04037304149fc0,0x1aa74189144eea5c532b83200666175ddb400,-0x11159eeb99732c5f4ff0eb508d677d377c140,0x96634e63f4f1d22611f2b8c434e2fc96f313,-0x46cd32e4edb12dba3813f1ac11b34469ebf0,0x1c653697d7cddba130b0ef25195a3142d148,-0x9a41e57d1bc87fa27afedcc539e66f7f3d0,0x2bfa78f2a607e82c70dfcd05932e1be2c94,-0xa6ad1319976a3f45c3a3fbead5e20cf1f0,0x205c6692dc68faf316c7c2ac601593b0b8,-0x50faa7d51ce2ddc9f3fc5274f1be6c250,0x9f9ac42cff76af0b0028be285683a24e,-0xf08fbb8b6ae730e8e5202afc3e66b90,0x10a87b77d6007eea927ce616b1777d8,-0xcd8e9abc2015226b31777473471b0,0x6610f3e784efd48f211bfa377604,-0x1d020d555038f18940cae9bb110,0x3e6b52875320a381f3ebf5248,-0x2d07fc74030bf2ea8a497b0,0x4f7636fece861bac30cb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 18 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 39 indices rho q11 m11 11 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 39 indices rho q11 m11 11 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r12 : List ℤ := raw_ints% [-0x17953bec73b7fd2d389c0000,-0x25904e2260cf7e938c164000,-0x1bd505481e37984197aca800,-0xcbf82b90378c39f19414600,-0x40ba2788349143fb8793680,-0xf1cc7ec0c1442515517360,-0x2b0abf492dc78af72c2cf0,-0x5f8a370fcb75a1508fb70,-0xa77788f32d8eaa7a0490,-0xe9598a90fdf29e3abb6,-0x102c0680b2c6bd444d3,-0xe34fa47d1fa7c9998,-0x9c7ffa8370e471e2,-0x52d294228949e18,-0x209cc0c2a0bbcb,-0x907edf1792a8,-0x193b1b56160,-0x21ab47902]
def m12 : List ℤ := raw_ints% [0x0,-0x3eec951f37061e5c7a969dc5cf2400000,0x54c8c2e6c4472012f07590e66043f78100,-0x36b7d6d787ed36db3d91e26a48ae6962fc0,0x16839d95417009c9aa440deed8dfc696ad00,-0x6a1bc82aa42c9fccb430bd3877d5b6bd89f0,0x17d1c2476f2af7c8fda084f6e1cc255fcb000,-0x43c42bc86bbcd20d6a67f6d21907ea4aefb40,0x9cb4464ed377eaff8550f969662df00e77a00,-0x12be2babaf5c528088cf1c5577c04a5634663c,0x1e11ab0693a8110c9e4a5ca726d13b969387c0,-0x28d12ce49f8fcd9d6099d9eb2cbce788eadbe0,0x2f30f1d0d14e83fcb2da011ef265118254a940,-0x2ead5d5f143edba245312a3f31da97e08d6440,0x279a6a9d52631d6e0b90a5d62fe8206ae93ac0,-0x1cdac5aa2f77fcec7fbd6ad78cc6e4c3f580c0,0x120c114db608b57d13fe9bdbae9a7916787640,-0x9ac36b79cb6d31dd9b24348a9465a631e9e4f,0x46da8ebf79bf0f8246699f474016c84ecfab0,-0x1b93aec980b50f326d9bde907d1a6bf99dbe8,0x910c22a64889f734008be7f4e18b7b932010,-0x27ee3f89abde5086e942ee46f032bf0c4924,0x91ad91df4808c81d7cc5847f5f1b39098b0,-0x1b20b8d870912972e257468c11643079d98,0x40d42562b96d56802292b19c7ff059f890,-0x7964a2316f6a1af34c76ab3740ffdbce6,0xacbe019292478f1329eed2579076d2d0,-0xb34bf40da6b98ed7a82b0eef9573ab8,0x8049c59e7abf2a611c17158ab60370,-0x3a5e8fbd86caee0cc296622d65854,0xef5c3bc36276675c93f042b6650,-0x1c6f0dcc11cd8c07c62eaa22a8,0x11a329e9cadd29f137825d70,-0x19d269748430abf7ad067]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 18 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 39 indices rho q12 m12 12 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 39 indices rho q12 m12 12 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r13 : List ℤ := raw_ints% [0x557afc9188718b0c5e9120000,0x87ef2264610f7583f27206000,0x64885046151afa08ef81a7400,0x2df39a064c3e5158435888400,0xe8c39679957073b22261e4c0,0x36331ce80c6d31d26b5aa0e0,0x99e4f10fcfed371ff173f20,0x15465efccca96c4fcea1b60,0x25240071f7189a6e8f78ac,0x33823f4091eb0c44d87f6,0x38cd3d572b8b791b72fc,0x31935b6de262d6b0995,0x21ddf6dbb1ab59b0e8,0x11c12c80db4dfd282,0x6e901fda7e17864,0x1e2c1d10369c4d,0x52b8a3ba6f4c,0x6ba7997b86]
def m13 : List ℤ := raw_ints% [0x0,0x56854d0aeba869bf288f18effcd1800000,-0x73268dfb8d3ffa770c25126349d7abd9500,0x495edac45de9f9839a251ce77f541f91eac0,-0x1dca11c1782a9aade0662d017aaca1d833100,0x8a764dcc9341ca00b7d33fc0e4c4f80c990b0,-0x1ea2bbee5b22ba860640cc6a62fb80bd7e7000,0x55da08644d78b63f8a61ec0d1e26867132ac40,-0xc3699c73b6a21d65ac9eaea13a50819e6e3200,0x16fd26ea2c12e0b9b05bd8af8a496ee072a86ec,-0x243ee5d174e8010043c06c9bcd2411fa34b62c0,0x304fa68b5c4e8a934205b1f2ce44a7e74083660,-0x36ca8722430002d566116f9f8745618bcf9f240,0x351ac9a0a5f77f0280f3673a6c4c2be4ba49440,-0x2c192c5b2db7ba1df92b037705c5010bcd6b1c0,0x1f67bb28ce03df59e9b4c206af3860ea28ac700,-0x132be6033e09957a949aa15f4c306f13e4f7740,0xa0337a8d42d2b73ec8a64792882ab710c6f33b,-0x4756128855d942e5cbf27742d16e1af9e45870,0x1af2d4b5087f70d0f9a8519f0fc98bfc08e508,-0x893fa0261dfa70f44b1ae2ac813eec3cdb950,0x247c47eea8f10649fb0e43d099a09051618f4,-0x802072d8cc9f2b3bdbc13c7dcac6e132ee70,0x16e17c766b0db23c395c20262c9b3f829af8,-0x34347efd0c2b6db18fad556a74b0baf53d0,0x5cd66e887019c7f48dba022bc47c23d55e,-0x7ca7fe7aaed9697d9e60a8c2605f9e310,0x791f6449568e647fb6ab464cdaa53718,-0x505411949299b223f081f6175922030,0x21741c89de7c4a64dc6b410bba7ce4,-0x7b917c06e1e7c29b1e72c6107c90,0xcf39e3dcd549640300b91db508,-0x6e72a4bfd13674ec3155c630,0x86283e56fa50bb3a57533]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 18 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 39 indices rho q13 m13 13 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 39 indices rho q13 m13 13 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r14 : List ℤ := raw_ints% [-0x11151761ecd0822b1584fb60000,-0x1b202d13d8dcff790f39c3b2000,-0x140750122068760c808dcbebc00,-0x9234b688f3f9e5a46b64b01000,-0x2e30ecc617f86ad8f80c69ac40,-0xabaff1f7d49e2973950fe7960,-0x1e6304a54284599ac0ed016a0,-0x430219e3603eefbb50662dd0,-0x749295f5f4507326b0da7f4,-0xa105a0070d0403041fbe66,-0xb0be61aa7797fa4dcd0a0,-0x996c09cf31bd3a14523c,-0x68234f1a4ed1e2e75eb,-0x362d514dc3a426d544,-0x14e43c2d022006ff2,-0x5a2fd8b7ec055e4,-0xf3c11c24d068f,-0x137772f5d0e6]
def m14 : List ℤ := raw_ints% [0x0,-0x76f749ef04079166d7c4c249fba01000000,0x9c754dd79563953dc2af75eb14b8f52d3900,-0x62768880694c840adba68490a00752a7841c0,0x2776e8baf0e36dd992a0d72236240a4fbc0500,-0xb4fab5406056a71001a8c384b681bf12149e70,0x277bd0effe815fa6aead311470b529d90513000,-0x6d07e73116ddd174b770c2b947fd11c1c33d140,0xf4606b94174a28e7d38999033ae495f901eea00,-0x1c49b73ba8033392dda33b8c43b5ff8e106b8d5c,0x2bd94925758bc5202b2750ebad2d7d1b06d639c0,-0x39687884a6feb853a9e1af1bcc1d9c29c5fed0e0,0x3fe3c372d5bfdd8916d3a314b91b64b8219eaf40,-0x3cb2b4009ad8297fee9739a62b2fdc48dd2c1040,0x3158ea3c37032a8a4749a1d51a8d92143b04b4c0,-0x225c57cac66b088c9a6510c2a220d8b52680b7c0,0x147a62286184eca39c9c3c7a9d0c1331d4b8c440,-0xa6c7eb275a399e5a5cdae68ec747c9ac64a3797,0x483f4cde896301fedd452e4a0e7f63ef6f84130,-0x1a7e7f96c2787f0f2ed1f84125224e443d92aa8,0x82aaaa1d1667154d7acb4aed1e34418db0f390,-0x218af359b87b89c76e9c107daf43fd42cce504,0x716058d403772218bb73ded89d0c28a3daf30,-0x1369bf364eae57493895f73d7d356769234d8,0x2a46edf8f3662792d951ff84627bfdb7c810,-0x475f0713ca292eea3d22d33a21fb30f1136,0x5a6042b2326a46adc254015d9acf1b4050,-0x5225278cbebddbb04bdd11f5972811af8,0x32731caf2c163a5bdbe1386d1c1ab3f0,-0x1335f50beb519e3bf7e0bbf6968e8b4,0x3fd81f70d458a9fd54c6400f037d0,-0x5e609a7e7ca3771b45f3eb77468,0x2b3236f0adc0bc12b1f84edf0,-0x2b8824f9c9df04f0caa2ef]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 18 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 39 indices rho q14 m14 14 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 39 indices rho q14 m14 14 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r15 : List ℤ := raw_ints% [0x316c303e0e4382c9a4cad0160000,0x4e60d21470ad9db8d88d95d92000,0x39c991462ea773c45ef1abc7bc00,0x1a526db598e3e74539f5ebb20800,0x84cf9e43d230548ea6b64110440,0x1ec9f56bbecb6a883c01b8f83e0,0x56fc25e9b6962a9c140e73f620,0xbf4f009e1ae4d6558402cad50,0x14bcf973a50fada33e46d60c4,0x1c8bfe9d55b292dc5a48973e,0x1f35b2119c4b7b885473890,0x1af79482f6be0168c82c18,0x1234cf44e09893ad56544,0x9697236201aaeee1d01,0x39a2343197c1af9a70,0xf68b06bb68339ed6,0x292f227839dccb8,0x33e505d0843c3]
def m15 : List ℤ := raw_ints% [0x0,0xa39405a8a58a67ed68ae8b25b9fc16000000,-0xd4abacf768922b13234ca5b8986ddac75ad00,0x843e9ae6c6c4a4a8ba409af8c189dd28dd64c0,-0x34587b00d34b794e21c73ffab06b7c5479f6900,0xecef4ffc5d430f68405ba3948359d09b1103f30,-0x32fd51ba8566d36d7a5e66ab9f1a48ddc614f000,0x8acd1fcf1d61f989409230390e5e352886c8ba40,-0x13276528b17d9ebb92b3f264bfaf3578142996200,0x22eb319759d27b1fefb74c6780e0650066aca3c8c,-0x353bf1b166eac806b03d89fe6b42858c7acce7cc0,0x447bb8181af62dd18210be5c2d0c39708a232af60,-0x4ad0759a280c862bf430a2760ac7420e91632f040,0x45b174afb5cacb29ee77665d6eab153ca3eec2840,-0x377d44d31b0085d75830f39ce83ae125d202bb3c0,0x25c998f0725867c640d454dc059e4a07a61bc6200,-0x15fdd5412b0a31807f9b04b3cc8ad1303cc7e9d40,0xae9aa2986b1955d7e8c8f28a8eadd7c6be692423,-0x4997c3a0239ce60e6011a001a77bf1293a8400f0,0x1a3382d892fc1db4da92486a5f7eeebac4110ac8,-0x7d24ca99a182b4d465ae4aa9780de918f23b2d0,0x1f058bc47ba5574e09ea04bfaa4dc43d3a43a54,-0x64ea4a5a9875d59f2042ff74edaa256701a6f0,0x1090a26ea4e1b2f6a0535dffa73da4c45d4338,-0x226c2c6468daf33b55bcfc4eea19baff17950,0x3724589bb6a5136147ef8df9c5d7773113ee,-0x41cfb7ef6d06a18c620401aa9030593fe90,0x37ea180ee19f63d4b9d73900066ffb4c58,-0x1fc5885585449297faf47dd37dd95fab0,0xb0cfdc3cc6f1083bbf324444862d4c4,-0x210220ea2a2ef3355b0d31ca134c10,0x2af8fef02be5b9a9e59003bed1c8,-0x10e1bf907b1f5ee79b313c40b0,0xe1d95e4967731bf95df85b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 18 54 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 54 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 39 indices rho q15 m15 15 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 39 indices rho q15 m15 15 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r16 : List ℤ := raw_ints% [-0x83c091ef9ba7f74581ebbdddb0000,-0xd0b33cba9e0ceedc9010b3fb09000,-0x99ac116bc81863508e323cb326e00,-0x45e52efb40f7e79e13ca2cd218600,-0x16016e58abc00cfa0b63acf775020,-0x51792dd669256fe4109dc9fd4ad0,-0xe5b4234856f501d5176fc3d57e0,-0x1f8045cb4881930535b8cb7b058,-0x367dffa93f340938c9c812885a,-0x4ac9173f3c8df902e23614cc5,-0x517b47969dc64ce0be652b0d,-0x4620c33c420b3f07715e20c,-0x2f214a82a4fede868413a8,-0x183c2f159496f80f109d2,-0x937a46091282d447839,-0x27232471e1306f94b4,-0x67ab6aa1e6310e98,-0x813420cb3a8561]
def m16 : List ℤ := raw_ints% [0x0,-0xe0eb87c7e39e4ee66fefff53dfba9e4000000,0x12131ae5dd96f1c6df9855691da417180273100,-0xb1c1df8788bc76d6ab4f3254d9654b3382943c0,0x45838591813b654a8b58765470e5d89af0ac9d00,-0x136ae73564cbfdff0bef0f33b3bc8a3670c66eef0,0x41fa62634ada2f743e63771b8c1afd1e5e2b1b000,-0xb11dc633b7550d1e57b26135aebe9b18abeec7740,0x1815ee9d8e1546955c494ccb50b57114e0d3edda00,-0x2b3cc864459239d029f1c82d55dc04a54fc517f37c,0x40da206441b24841559af571848bc6279b56cbdbc0,-0x52019b3466377737b1b3f36e596901a106e2e21de0,0x57f8483e65a822fa54fcd074f2c6e81d27b4200540,-0x5060d30fb0f52070224eec05e8732e811491944c40,0x3eb14b642d88e3f16e0914609b5d648c2c7469dec0,-0x29c3d343bee5e686638fee171e6e2893c4675016c0,0x17bdc74f22d36f65a9e49ff5a448337b3bae7ce240,-0xb7cb9557cee8cca210f89c45e14053674cdc6409f,0x4b62eb3b78fa667dd1e47e4b8ef63b053752373b0,-0x1a0f8b4dfc9666ad6ceba1ec6058644e6c9587368,0x788d0d16ade12430861c8a74b4cf45a214f98b10,-0x1cdb3da9b1687fcd27dd8903db6d717fa97899e4,0x5a55ee6d9582d88249d7de8eb15b41a0ae631b0,-0xe366725d810bc73fb0ec79a3a7694a4cb8e218,0x1c2c39f9b2d837acde2ebf05e754626ae9fb90,-0x2ace23e1c6a4242f1752805c565b5f915f706,0x301f53807a5c4d23e1934725c689ff2521d0,-0x26306427377cfe44303a37e5f5387ef8938,0x140f0ae4151fa75a86369bf048e18f8070,-0x65dc8cc6ae192409237a72ac702f1e14,0x111311ec1ec2d85de12f2d516b75d50,-0x138f9accb55a69d8b674b873b8828,0x697d0035265710ff750a6a5a70,-0x492f418266efee7c8ee0b37]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 18 56 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 56 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 39 indices rho q16 m16 16 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 39 indices rho q16 m16 16 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r17 : List ℤ := raw_ints% [0x148070de854d17dc806ba1f04690000,0x207102d7f0dcad5e76050f864ed3000,0x17dc1386be4965647328ef41ca68a00,0xad6873f0f060ce10f1e8b5303b6800,0x3683f4d6bb72c36b7d3015fa0bc360,0xc981f1e5ce84c34741772da755590,0x237153d18a3802830e5ef9b732670,0x4d9bb6b5e62746a7016580d32f48,0x85f06072ff4dff4a454fe6e25f6,0xb756096b8b5c725205b862c089,0xc727d5bb1e4fa6cfd65494874,0xaad2741623c451d54cb2a9a7,0x725a9dfd0b8bca26123db34,0x3a899dc7fa909a970b2a4a,0x16258fa9d1fee765327ac,0x5d74af84fe560f5de53,0xf5bd22b16bc763706,0x12f9107f025b8c7b]
def m17 : List ℤ := raw_ints% [0x0,0x13543dab2d8f9ac7cd9e9ff1353a09998000000,-0x18967b275b9a2d2ab04e20594d779a034a370500,0xef1e7927997cb57c6f3659f1c18d6cfaaf628ec0,-0x5c6b814321e296e30ccefa397f251dc777963e100,0x198030dfb3abdde33870651e5a7c65378a57c2d9b0,-0x55897bed34cb43a3c248e15deef259991e1f377000,0xe2874894c5427c894a44d989d498160e4bc992d840,-0x1e5e46fa88fe2a34c2b4022132f106cb0a2d6311200,0x35b35053e79fe3ff10a8194aca7fc39334817f81d2c,-0x4f45f17686a6a9b44a449fb7574f5cd8fb63ceb46c0,0x6290dfe4ad9966558de0799541098c2d2d2be1b6060,-0x67dbc3e1185198bdd8b98d651af6dc124e0e9297e40,0x5d1b392e6bd253bed36466afadb67f330c8a5ab4c40,-0x472924c4a358065a2c6f1c9d019ba26424c41f425c0,0x2e6362bcf69486815d35ea697353f4aa9e38f7a4500,-0x19c331289f613a68de24121e3d9f308032366f59340,0xc2818cf59defd5dec2bd0c7905197d0a89c8262fcb,-0x4da62cb6bc37fb6430b69f345724f7e92a049b0570,0x1a1104fa48027107b64958a45c171123aa74673288,-0x74c8a205a8d71293560604b6ecf5bbaeaaa81c050,0x1afe4d18303c6a4735a2fc16c74cc4db7119128b4,-0x514fa9b4b044a15d4de17e55b2e373ac8dad3b70,0xc423e4ef8405e7b82791547525a2f64b4e53978,-0x172c1b385d89aeb6b83568c632980518d7e52d0,0x2160dc284f6362cfded6a63becf177c18a61fe,-0x23533daa294f1a13c6129a33cd456094f9e10,0x1a2a34110a58f63233e0e46872ade9ba8798,-0xcb14f5d9baef0ed172a547f23e050c2130,0x3ac255f437b18f3b72e0030b6ef67b5a4,-0x8d5ec9e08af93bc299bac12f12dff90,0x8e6a92ba9b8a66c00eb6537c95888,-0x292b1c57793be97b69341f38730,0x17b318d8b6c41bcc4a5c7443]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 18 58 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 58 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 39 indices rho q17 m17 17 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 39 indices rho q17 m17 17 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r18 : List ℤ := raw_ints% [-0x302b5160f84382e2b9da9b01cc530000,-0x4c26517bbc8e8f457b41d6a0b1501000,-0x37f254a12a2bd3f6a954fe9dbf570e00,-0x19621c7faad0568fcb2da01e60e68800,-0x7f82cc41e927f5ed4c5084739f9cd20,-0x1d6a21f8076d5a0e93dfa6afba43230,-0x52a49dff2854fc39845a995356ac30,-0xb4a15c8f4060fb7674deff2b25cc8,-0x13718b1009696e26f1104b706e872,-0x1a8d7e4ee19d4792396ea8976bbb,-0x1cc4b4a5ed0c54b271c1b4df5ba,-0x189a30c2c8b36082a15d456f88,-0x1069f3aab64011c39728b5c19,-0x85ea093e974c60b461cffd2,-0x326ffcd41894c4684ae780,-0xd3bafb3d165d17554018,-0x2295626e21f3028bacb,-0x2a6987d78807021bb]
def m18 : List ℤ := raw_ints% [0x0,-0x1a93d4cb5ea574d2baba1beba92fcd3310000000,0x2175f06ef047f10dd24d0ccc4cb34c3b830836900,-0x141e80b299da2665c0567c5d5e810472ac1b15b5c0,0x7b037e5152ce4ba5e3c5190a9eb7728960d7d27500,-0x218a4cc0a6c817c5cd9181554f12c2dd4a9a2039b70,0x6f1a660eef0fd7857fe6bb7bdaf1cf55af74dae3000,-0x12260d4ae6194c360007418dc41d0a6f1d05ff866d40,0x2663c988ae866cbb6681e63201a7f3bd11cdf44d4a00,-0x42e4c17d06ce32375b016569ff7e37c3c427ff4de09c,0x6139055e88ef499ec91e8f689eaac449520e1e70edc0,-0x76e6fb7373ce4a31d24fe340c9bc5cc36455863202e0,0x7b1aa57d7873fd39e9228c317860166a20fead622b40,-0x6c4fb65b600f1ed37ac51e8d406d277bc8c5f9b31840,0x51241de8ebae6123e71b10d723c8fc44a23b29f738c0,-0x33c58283c02fa60e691bb0c931b2dd43e7afbe8e5dc0,0x1c18c12fabc69caf94f96d70c85af2a313b6b3a79040,-0xceeb20afa443d252c8449c590e6565a85e0b5d82b67,0x5068f9dafc2d42102b57df09f40b1af17e041e83230,-0x1a3707ce8ccb6c66d038fb598c52530ad3dc1b46628,0x71c1cccc895519be38712ca1045e4df879157ac690,-0x196377ca1a6f67d796c31c5d6a190951b7a56bdfc4,0x499420ec7682ffa6087712d42f449fa2a578bc030,-0xaa0a78b679ea9eaaba208d7281482fa6bd867558,0x1326693b6f634a5cd86645fb3a406f021406f310,-0x1a2392bdd6eeb63635b830da944454fa94cc256,0x1a06b20a19d1a0f90c49a342ca5b59716fd750,-0x11fa92ab018c91486750747f6bade96e19578,0x80c46a4eed5033659b600e796c7a37188f0,-0x21eefd3251b9e1387f370a814d63169074,0x492cdce9775350531b3ac5166c8136d0,-0x40c7c248a248c18097647236e8cde8,0x100e36702f2108e4b90bc78202f0,-0x7ab814a94a7c27b9408fcb3f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 18 60 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 60 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 39 indices rho q18 m18 18 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 39 indices rho q18 m18 18 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x2a6987d78807021bb,0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r19 : List ℤ := raw_ints% [0x6bad8d47209710fc0a5d368540b930000,0xaa145d188634648b24d24c7fb24e21000,0x7cd634b1af384fa527fb46356d32cae00,0x38942d15128caf98639371140ea698400,0x11be222a8ff8595a6f5ace738c2e8e520,0x416696f717439a231f3f49de4b608470,0xb77ad0c904689b750f62a47ee285f90,0x1905e64e93f43953499ddcbd7e22908,0x2b048ba0f444fbd2d2a4e75869a472,0x3aa02d9b95a7b82a16052ff0858ff,0x3f5ef1d74b52aead93906c1b4dc8,0x360d71918aa1c7ec1535c475342,0x23f49cff944e3ea87f24e82638,0x1245bf3b099d8fa711ad3e56d,0x6db08c47a6e333152023778,0x1ca6acaa9694f32b57ff44,0x4a7d721eceff3444d986,0x5acc983742ba4749b6]
def m19 : List ℤ := raw_ints% [0x0,0x248b4497a22380a1c0bfe66408a1ba26360000000,-0x2d8d63e91e711a521b021403e45404ee0036c79d00,0x1b1ad280d9d0697eb026d168a38a5c4968008c7e8c0,-0xa3ea86b94d543b3761781fe173ee811fd4d49b69900,0x2c2deb1c49557174e0841a77efdbbc15409407df0030,-0x909381f05fe0aedac49cdb8e795e9087de886625f000,0x1750b63861a9a08034e045e5fbdc1657a1cf0be6c8640,-0x30a77f4e2f35b461c1b8e90543ffa2265a0c5797f4200,0x5391fe6a1c89b65f9aa1cce3b09d2d5a3556de1ae10cc,-0x779fb0f432b11089d7c7f54acdb454d1a37fef80040c0,0x8ff294e99eafd691b46c5107afafe327586a790988960,-0x927be83725f1f2b23897d72b6f857b84203c8ce751c40,0x7e8707bea8ce9cf81be3a6cd53b4a22b3e02444510040,-0x5cef37b7717f35505bb82f79de927fb349484d5e887c0,0x3a0d56132fab33b4a0ca5664fdd5b7f5425c63d463000,-0x1ecb2f0ac2372bc147742bbebd3f1e6b0d727ce355940,0xdd3fe8a1eb23e9d972c6495d54079ef3d9866faff033,-0x53b4ef87cdb813fb241a6f680f3aa216625a74e985f0,0x1a814a350a37fa3c38cf23bb1f69d394ddefce79cc48,-0x6f670be2b18276fdc279b98c2e061fe70aa3ffe41d0,0x18017998d846cdd3df97c0f4ee4b04863711e00bc14,-0x42ecc6a349576a69e2dd899fbdd1dde8771c31cbf0,0x9423830c7ab4c3190ad0c459aab9ad0a040898db8,-0xfe5e34d81ddeb4ed272158f5ad061d4a85984050,0x148d8628bf50e0aa6a6e2605b13df9409285a38e,-0x133dad76f637076df4f6295d4419d5d367da190,0xc631668aa361782b934af84210dc5e3ab38d8,-0x51cc0ed54d36254c16ee0f65b6e598df33b0,0x139d972d2cb5290a5857b8c7181886e9784,-0x25e200612faac588d363379526df67710,0x1d743f8acf7dee75e2acff1f5147948,-0x641e27e7bec5fbfd9a2c702fb9b0,0x27b121e389604a62e1b9252eb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 18 62 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 62 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 39 indices rho q19 m19 19 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 39 indices rho q19 m19 19 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0x5acc983742ba4749b6,-0x2a6987d78807021bb,0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r20 : List ℤ := raw_ints% [-0xe68658c64ea2b0d45a3ce655744f660000,-0x16bd587bf083261e0283074d632ad832000,-0x10ad19e05b8837dc9702ffc6025e309ec00,-0x78cfc99623507df5cdcb070e5bb1bdf600,-0x25d858d61538f3aa512d37736e384eee40,-0x8b55617c33e133e93c9ce24447546ca00,-0x18661055ecc2ffce190bb3be2d87e6f10,-0x352964d0183614dc0cb189fcc0ee44e0,-0x5b3dde017199d8542aa023ee854f0ec,-0x7c1e58bb06ffbb9c4f52bd1f3aa130,-0x85e3a835619a4bec9e0d94626e647,-0x71f02a419c674de32dd08061c930,-0x4b98174757ff4fa86523154a83e,-0x264db1cb9979eb7bb0cd4fd554,-0xe52a6c45b9c41dd51e4f0ca7,-0x3ba0fc29d7545ba5a916110,-0x9a582c12846128a150e78,-0xbb2c25da5579d661e3c]
def m20 : List ℤ := raw_ints% [0x0,-0x323f7e507ef0d0de6907dcc98bde5ff48a40000000,0x3e09249a4c2e21b5b70e88b1c33639ac3a1a65fe100,-0x248acc25f870024fe5a84c1047cc92fe54e8986617c0,0xdaa79cc34466ed19afc7526d993bfc409689f0838d00,-0x3a46ee537f44df15ff0109137990a8cf63a36b738c3f0,0xbc78e02ba7cdf09e13242a2c11f878548f6c02526b000,-0x1e04696b69da7c4e90efad255545edb984a1e020633340,0x3dd1475766c29d03237180f6e390f1fa40320b164d3a00,-0x68b3969adb3c84186a188da5e8a53c0f3554ebf1ed5cbc,0x93a778202980b6cf843dfedc60a3fd8111a492d8d5efc0,-0xaee0f5f182bbec50e4746440c3f993af17e13cccd1bfe0,0xaef7fbd0e0df5d0b421b21126dd4e08561ba413252a140,-0x9469ed064c2ba68644f669542338dd9fded2aa2d597440,0x6ae85475359db2c52a1c0d8c410460bf3d9fb34a1f42c0,-0x41652f639f0c036392c78ef39dcd68d112ba1f23c04cc0,0x21e9a1a4b8c6ce06e7fece9cfa992395d54cfa917d4e40,-0xedc1f5be88646e7731477d957c4773994a903b3b459ef,0x579606c2a7c7331accaa4012f5b6e7f5ad94017351cb0,-0x1af0188fc59e34b2f86ec97649f6ac8597e50285432e8,0x6daa6ea3304ab3552a21adf811542ca1ead30b648610,-0x16d0ab52d19e17e28e397665e4be41f22bc153c16ea4,0x3d2d323213e677a0e424c4891630b835bee0900fab0,-0x81aaf14c3b4449d8e1082aab2e3c98f1bb76273e98,0xd41712453988b08ed25d00d0cbe7d0762fdeb8e90,-0x103902792b4e73452904979665b40ba2b1c742726,0xe453c002aa24a16a82427a7792da511bd81c0d0,-0x88e396e2a7c4e4b4b11825cf606de5f9edcfb8,0x340bbae0629de3efa65df7a0f56ab49a1ed70,-0xb5923d6d4d7c2faa331346180eef0c617d4,0x139d0b88f99d026707b01efa9e1c852450,-0xd62dc6ca0e4aff8a987b792dd0635a8,0x26fe5139acb68517f4dd546460770,-0xcd494d98935a7ac2e02971507]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 18 64 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 64 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 39 indices rho q20 m20 20 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 39 indices rho q20 m20 20 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0xbb2c25da5579d661e3c,0x5acc983742ba4749b6,-0x2a6987d78807021bb,0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r21 : List ℤ := raw_ints% [0x1db33840aad339d6133368244830c01c0000,0x2ed77f8c8ce6e549b47a37647c7285ad4000,0x22530b153c0965724ce511a52d921a91f800,0xf8727ce292a13e5d8e1e5fab29b2fd13c00,0x4dc08f0248e76cf2f7300fcb01b5d0b0c80,0x11df3383d6d9c295b64e29521bff9494f00,0x32034aa99e6a2214002dd9b6da736a2100,0x6cd3c223ee8a3d0258c8f23dd911b8a50,0xba814d9061786005c6929b8effbe7668,0xfd4a8df22115a39bf8bd099bcc156c8,0x110bacd1fa41da0e78f21fd587d67ac,0xe79d11e9fe5ef1e23a8901e7109e9,0x99505efd2a2cca4f74026666f1d0,0x4d7b8b9d41a0da0d912e3183b7a,0x1ce35af3599a729964d1c2ed34,0x77dd933165c3b46b0c8c8629,0x135140c5619d09f09cb3988,0x1752bbdbbac17ddd9a47c]
def m21 : List ℤ := raw_ints% [0x0,0x45174daeae8b1f31d06acf952051c3f03e180000000,-0x5483680ff7cbdd182f394f3eb6921a1957c415dd7500,0x314cd01b037c65f0e8014fa65edd0dbf0a801c05ff2c0,-0x123fae0953081177eed941a6c6489f8ede82ed4ef59100,0x4cfb388d580063ec9cbc51e178471d643c022a5c4d52b0,-0xf620765d04c34b7f543ae6f874ed674cdb445e42007000,0x26ba14f28caef9d17c4331d5be2ecc310ef229de5754440,-0x4ebbe675e748bbc84574eb651d995898b916bff80a7f200,0x838a740322d8cc323215721f5a7ee2187e92630bd0cbf6c,-0xb6d1d32390dfc01d9477b9e9b05b76b7fab9eb5bba7eac0,0xd52f5099e7bad7333539afedc4d13cc0b3bae673a0e6a60,-0xd1c5c4f553317f81513e9ab6ef9c7619d8704ea4cf14a40,0xaec922c527f696dc82d8f6f130e9db5f89615f3ba604440,-0x7b822dbbb039ef0b47629d0bc1c277a174e4bf59b4d59c0,0x4a0020d5a8855e486172cb9ed825b2e727d4eb59b93e300,-0x25862b834035c97223281a3e75ddd74fbc3f08953116f40,0x100bf9b517568ab5c15554b830a06a647c0de0aa0a9ef5b,-0x5c1ad5a0111354e7343609729bda4587e055ddb052a270,0x1b84511010cb97a77598ba5eadbb3c0c5628f5e297c808,-0x6c810f5c26f05eace4e9932221d0131731af8821a9750,0x15cab5ef9e9e937a8ca8d47460d15c58a9a87ed2e0c74,-0x38310f1847e36bae0c7bde5f40ea080ed6b02e367870,0x720413ab5ab3364af8bb2524780b6d9354164dccff8,-0xb192f600386fbc5edacb882b72d5574f343627a1d0,0xcd9fb4913bce3a9de8017ea48d38beef39d9a9c9e,-0xa9da6febfe4548dea4583cce7fcd884e6233e910,0x5ec31412349cf81bc4c4177f3c8ce02a3df3018,-0x212a16d34f68ea008a4ebc32ae43a932dad230,0x691dac364f55571dff8eb5419a9c86033264,-0xa2799c4bdd5ad7441bd183acfd94979290,0x614b51e741ecdb66c8389e7138c1e408,-0xf2d5c7e1f4dae449028815f0a7830,0x42524bfb1f9015cca499322e53]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 18 66 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 66 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 39 indices rho q21 m21 21 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 39 indices rho q21 m21 21 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0x1752bbdbbac17ddd9a47c,-0xbb2c25da5579d661e3c,0x5acc983742ba4749b6,-0x2a6987d78807021bb,0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r22 : List ℤ := raw_ints% [-0x3b36bf897a79f4f813276e87ae66d785c0000,-0x5d542e9aca0fda7860b98d48424a043a34000,-0x4456e31d7aec2dfcdb70fe2f7198c265a5800,-0x1ee4268c2a83df4304026187d4eecfcb2b000,-0x9a8af57d9c0a829db3c5b82aadf54d415e80,-0x237cea2f0d929b33954ac757692a28203cc0,-0x6333c328d5f2de87bd74220dffa0b4d6c00,-0xd79a6c6cea4a72e0733e8ed89680c8d260,-0x17100c9847479c0d3df19bc77575bf4878,-0x1f4664d5fb4ed9566b1d54e43a763140c,-0x219ea7f412d605b6bc1f067c3b58fe54,-0x1c7fbbdee4cd44277e725bf42770d84,-0x12d36dbd740abc4b3cfec513388117,-0x97e118be92f17ca1ec1f9a706a68,-0x387aa911e4166180f1c5be60a8e,-0xe9a9d9990aae98cd525fc709c,-0x258821d35470549d91bdeeef,-0x2d2478c30a8a088bcbe82c]
def m22 : List ℤ := raw_ints% [0x0,-0x5f000ad02fff4ae47e92dd6d0c706d6a556100000000,0x732ca79c7478a15b0e8dca47bc5cca0f4b0356b2a9900,-0x428eb30bf4230b6f43eda2388fac963a6efc8847dee9c0,0x1864b639381708c04701b65c5dd4dbe370b16720d55e500,-0x65d3f866e00a6c475bc9dc8cbc3a9b08a3fd99ada9b8870,0x141f7ee6cd9dbc8eaa4eefa1a37498b5392e533b2b3b3000,-0x3210f39e557e29c572eaaa26c74de83c834f581a52784940,0x6484efd6fa8d04e578d984ed72b855706a5a4b035119aa00,-0xa5b5b0147c521e887a6d79002a4fa9f0b41e90865aa42fdc,0xe30c8e8bfa3cc734cb55d04f96d620b030801b0b760761c0,-0x104c0fbd57dab20db51ba96ffa7b9ec85576a38df9faa94e0,0xfc6b324338028ba608058b5cf37da41272a46b718392e740,-0xcea775482d08e3d50a1635e7b4dab11035febedc518c6040,0x8f4946e1d9f90e05ad7eb8b3f19e606306032d960bc07cc0,-0x541bed5996ce70e47e913301c485fad1d82d93269524a3c0,0x29b6627e6192396f5ab5950fa0edfd6a3dad4a1867659c40,-0x1169599f206fa1ddb7af50e18ab2f50ae624cab1f4869e37,0x6154e1b438ee33bf51f01536baed4918a80b8721673d330,-0x1c3f638020593a1c5ffcd9192da4d27f37eafef8a8189a8,0x6be2aa5c112a4b0809653b5ce172e5982f21cd8203a990,-0x14ea559462960499d570f734915d2298a31f98e1743e84,0x33da806753340e33b6c67de1acb161f24d2fe0f638130,-0x64b10e7cabed1b85dfa9c31b6b3929d8b255c5e90dd8,0x9543d9133bdec5d2e3e0ce08788143fdb7b42fbae10,-0xa37463ac198ebd427b26e425a53f3e6f19e2343976,0x7eb58efa673ed317ab9afeb80b0051ebc3a9e3e50,-0x41bc653902b23ed644db1601b6d027db827a47f8,0x15291664c0826be13540c9b0d18c5da8bd4cdf0,-0x3ce35fc4885592e42b8de36c65a8ec2ffcc34,0x541d546821224ebde535ed13e79efff85d0,-0x2c2d2ced757e10af0da9380d460bf2f68,0x5e75395b64bfd397b0ffc2b00687f0,-0x156a2b0bd47f96cb0adae200a8f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 18 68 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 68 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 39 indices rho q22 m22 22 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 39 indices rho q22 m22 22 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x2d2478c30a8a088bcbe82c,0x1752bbdbbac17ddd9a47c,-0xbb2c25da5579d661e3c,0x5acc983742ba4749b6,-0x2a6987d78807021bb,0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r23 : List ℤ := raw_ints% [0x729c0d7c9add78d4b2c36ea9228b3f998c0000,0xb4881fa9dbb0bdc83e4a61ae62d31c96344000,0x841b0b85b2b165ddf54d8a7db57c1c16403800,0x3babeae36d7a053f6555d548a0c3b05c637000,0x12a48b8036ea2c90d23e10d675fa15772dbc80,0x446f32d6b766973aa660a0eaeeacb93a283c0,0xbf1c7835f041038e8e612ddd8088a2319a40,0x19ee724250a0a47a8bd27f3bcd22b5791ae0,0x2c53f1e8f796e41a5d333572053b1ac4408,0x3c083ae6b8ef46a6f65509f0eb2ec4d10c,0x406ff561562f39f5eb1cb38cd6064c140,0x36885b76d4aa6f99d8dd78d99440269c,0x23f50b8bfd2d3f2c38f52839addd97c,0x1217e3fd3e219a86bf32a6f722c381,0x6b6801df65027ae9956d144b0040,0x1bb35b7a2a430c1643ff2b99f82,0x46fb67de33512d1f1992eae5c,0x5517ccdce90b17f20cf72d5]
def m23 : List ℤ := raw_ints% [0x0,0x82a00ede41ff06fa2e09f075f11a96723565600000000,-0x9d02dca7a7d248a311e3a29d9cbdb3ef5d35198a7e8d00,0x59ea51db393a43cf49f4110449ce042245537bae5492cc0,-0x20a3be3555250a03aae94197a66c897a65a925d2bcaec900,0x86dfba2ebed02ce1a575845830ed82feaba515c44bc97130,-0x1a5e21633a7ef3b02c39b8d2673369af21996d9b07c66f000,0x40dafb0f2aebc4fd8047d7380b6d4eaeffcfba187dff09240,-0x80a1c7cb3151d1c075ddbebb319aa77109da83b5e0f172200,0xd14f332b34c39529ca13104e4494838767ff974a989d5910c,-0x11ad17f8d5a59b334d7095904aef9f000a53bcb507aa88c4c0,0x13ffc20ed625523b7e751f2e248a0650567fb6111d4e9f4360,-0x130d26ccc7ffd25d033d10350c291eb650d13d481df37d8840,0xf5467f1fec9cdec8f731b32ec62afa10b93e7986dd9101840,-0xa6ea1dcb34457d0030fb7fb33254f3ead18101f33aae31bc0,0x60036e0c671fe5e5b12125e1bf8bc91ce0863191780591e00,-0x2e94191c4a3a274f01f40019bd079acfc8f536b847cfb5540,0x12fb1bf88430d3af16e0d300e381b5155ad9a077c0a9fe743,-0x675906531d79e97765969cf91400b3a10f99cd2b1c787af0,0x1d2354c2c0212f7f6feb6b3e36c0aea3fe0b9777e31495c8,-0x6bc94c6e72360f0c9e411f8b6af68fab1291ff2665d20d0,0x142b28efcaa741849f43fc47cfa1d9870e1bc41f79971d4,-0x3010dd10902cb34b8094657a53fb35dc05ca7b42a160f0,0x594c481be8827090adcdca63309ffd344a11b69211038,-0x7df19c4c4d9ed287fbf9a2b358c3e091cbb688add750,0x825b2a3b6b6f7c64085956dfe67236bb89d3b53f12e,-0x5ec57a8989d658c17bfac2147d45bd81f660815490,0x2daff5cf4eb0e7562e5d402c96ab0a6527ffdbd58,-0xd845afc0756fb07fe19d2ea3853041bd56d9cb0,0x2349084ec4eca0d10ec6af7097da6ed2fd7e44,-0x2b8a9f2643d97d9c5273173da29800ed3210,0x140c70e4cce1c298c7e8cc3a178441c8c8,-0x24b83de1dbbbb0c55eec10a1c4262b0,0x6e938c6bcf799da786b95f2507b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 18 70 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 70 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 39 indices rho q23 m23 23 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 39 indices rho q23 m23 23 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x5517ccdce90b17f20cf72d5,-0x2d2478c30a8a088bcbe82c,0x1752bbdbbac17ddd9a47c,-0xbb2c25da5579d661e3c,0x5acc983742ba4749b6,-0x2a6987d78807021bb,0x12f9107f025b8c7b,-0x813420cb3a8561,0x33e505d0843c3,-0x137772f5d0e6,0x6ba7997b86,-0x21ab47902,0x949f2bc,-0x22d46d,0x685d,-0xdf,0x1]
def r24 : List ℤ := raw_ints% [-0xd8099f0220aefa9ab46d6d267daa9af6d7d0000,-0x1541cec057949b708ee984630a0ea2593479f000,-0xf8babc11f1b76b77f71124725d3cb919a39a200,-0x704651d3bbb602aec1194ea7db1389edafb9600,-0x230d1d0a7959f5d8367713e9180dc4f8d01a8e0,-0x808fe5d8223d796dc7dab93641ec149fc0c4f0,-0x166b3be427c55cd4b299c35716d3e0a9921e80,-0x309f8631e17b882bfdc7ead04f84198b7c708,-0x5306d50c14bf30b4524c9e1790f48aad33c6,-0x704e06fcc50e13794a420b4be027e45a437,-0x7862636ccacd8ebbbdae9670e9d4fcc381,-0x65ba921defe716a756ede768f95307304,-0x42f765fd5fe5fa76a029d28002f637a4,-0x21a291e2d63bd5cfa946a36c6c7791e,-0xc741bc7069fc93d9fda29670c4015,-0x33457f96e5b443a5b975e18d6fbc,-0x830b0643ae02bc149cccdb8b80,-0x9ca2f977de45a9ba8bbb51d3]
def m24 : List ℤ := raw_ints% [0x0,-0xb39c14719abea997ff4daaa22b848edd096b6400000000,0xd61d1a8638d37003ebcfe1fa1f4e5eebb11eae2dc619100,-0x798c812866f591ea91c6d0769ba99affa6049e72cf00abc0,0x2bb7452734e5ac30c6e49f202a95dac1fa847624e826f7d00,-0xb2e050a9781a7bbb36e6b159cd06b2b27ca194ce11f1008f0,0x229b40d51012a9fe73947c4d3243aa74f0475cc9e0660bb000,-0x542d682fe4cd4ca42d62ea754bae6116756a8fcc1f01af2f40,0xa4fb6d06a4536b825f2ee5b07131f181398969fb0c8e6e9a00,-0x1091149421ef56f99b66fe30d08f6671d033a41987f5ccfe1fc,0x1614fd22392f8c1365389311954be07a4b9da63ed946f4dc3c0,-0x189eec8218cd2b910ec3f983f4ff7fac73ca4b4b9d6c73bc1e0,0x17164f8972d3f7b758772302e6b6d4e0f1e5df43776d1987d40,-0x12436d096b91868c02e780287ead7dd71eee4784de8db84dc40,0xc338ee0883b03b09a9eec8c15b619a890a61499357cea566c0,-0x6e118a84cdcfd7df85ffbd49b5670e45095c6bfaabcaa422c0,0x343e415b971377eb2b7b13b7705d9348ba2d303164f6e7fa40,-0x14c9614a49d709f1fd2ecd7a820e824b9eb7050d82e6a2ba3f,0x6e3ff194bd5b88dcdd4dce4ef2e0cf60ffc9d6671ed68f5b0,-0x1e32c5f23467356f8428eada8c53becd2bf17e6488a249a68,0x6c31148502b920a89068ead2f2138963cd79a1a055e61110,-0x13898a4535860adc3c206881a1ebab6c08090c42a73d8764,0x2cbfb0a3afd79a4ba5c4fb0d953f96b535c49620b4bf3b0,-0x4f83566a141b70c13d6c8b26d6d3b3a5b69f0c7abf3318,0x6aa642b03b2c19e5b0259a35e9ea5ee7ce592ddec3190,-0x68475d949d9e1b13ad4c1f32085c012949ccdc496d46,0x470e6225f903c53361e6210696ceb67be2d5c85afd0,-0x1fceed1967b3d2d89d60914c48cbaa5ce4caf08e38,0x8a4aac70584b82251e0083934fdc29d1d9954a70,-0x147495763a2385d56228d286054a78f71e70594,0x16890492f67f9109dcefefc653f3ea2a1bb50,-0x9181bec5e96ba1a368ce55ced7c66fab28,0xe441537b1855562eeb651556096a470,-0x23aad8f73cd54b9a37ca93503dd7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 18 72 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 72 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 39 indices rho q24 m24 24 3707976846486607478784000 22=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 39 indices rho q24 m24 24 3707976846486607478784000 22 16
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_24
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<25) : intPolyRF (mz e)=rfPoly (C (3707976846486607478784000:ℚ))*rfX^22*(1-rfX)^16*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V5C23
