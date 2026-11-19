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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C22
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,22,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0x1d8afa8cf25d8000,0x2e25908bd33c0800,0x217577091e2f9b00,0xef62f0cff56e880,0x49f8610ca661150,0x10c48f0b74cf190,0x2e373474645a88,0x62e8cccf9b270,0xa676d7812b4d,0xdda4ff50611,0xe98d45ebac,0xc1b6650cc,0x7cf4b0ee,0x3d63ba6,0x163064,0x58fc,0xdd,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0xe,0x7,-0x15,0x34f,-0xf2,0x2cee9,-0x4fe1,0x22f27,-0x24f8,0x5377f,-0xfce,0x4c69b,-0xcbc48,0x19789]
def rhoDenominators : List ℤ := raw_ints% [0x569a9600,0x267d98,0x6b40,0x2d3f,0x160,0x6e,0x2d0,0x31,0x3100,0x288,0xb40,0xa5,0x1bd8,0x8f,0x6d7c,0x4cfb3,0x59600]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 22
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤21))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤21 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 22 omega5=padCoefficients 22 (omegaCoefficients 21 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 21 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 22 omega6=padCoefficients 22 (omegaCoefficients 21 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 21 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 22 omega7=padCoefficients 22 (omegaCoefficients 21 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 21 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 22 omega8=padCoefficients 22 (omegaCoefficients 21 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 21 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 22 omega9=padCoefficients 22 (omegaCoefficients 21 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 21 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 22 omega10=padCoefficients 22 (omegaCoefficients 21 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 21 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 22 omega11=padCoefficients 22 (omegaCoefficients 21 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 21 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 22 omega12=padCoefficients 22 (omegaCoefficients 21 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 21 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 22 omega13=padCoefficients 22 (omegaCoefficients 21 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 21 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 22 omega14=padCoefficients 22 (omegaCoefficients 21 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 21 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 22 omega15=padCoefficients 22 (omegaCoefficients 21 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 21 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 22 omega16=padCoefficients 22 (omegaCoefficients 21 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 21 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 22 omega17=padCoefficients 22 (omegaCoefficients 21 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 21 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 22 omega18=padCoefficients 22 (omegaCoefficients 21 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 21 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 22 omega19=padCoefficients 22 (omegaCoefficients 21 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 21 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 22 omega20=padCoefficients 22 (omegaCoefficients 21 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 21 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 22 omega21=padCoefficients 22 (omegaCoefficients 21 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 21 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x5b,-0x16c,0x3e9,-0x7d2,0xbbb,-0xd68,0xbbb,-0x7d2,0x3e9,-0x16c,0x5b,-0xe,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 16 li0=padCoefficients 16 (liCoefficients 15 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 15 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 16 li1=padCoefficients 16 (liCoefficients 15 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 15 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x36,-0x9a,0x113,-0x129,0x84,0x84,-0x129,0x113,-0x9a,0x36,-0xb,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 16 li2=padCoefficients 16 (liCoefficients 15 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 15 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x7,0xc,0x2c,-0x113,0x2b5,-0x420,0x420,-0x2b5,0x113,-0x2c,-0xc,0x7,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 16 li3=padCoefficients 16 (liCoefficients 15 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 15 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x1,-0x36,0x10a,-0x271,0x30f,-0x174,-0x174,0x30f,-0x271,0x10a,-0x36,0x1,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 16 li4=padCoefficients 16 (liCoefficients 15 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 15 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x11,-0x84,0x11c,0x55,-0x5bb,0xba0,-0xba0,0x5bb,-0x55,-0x11c,0x84,-0x11,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 16 li5=padCoefficients 16 (liCoefficients 15 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 15 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x31,-0x7e,-0x23e,0xb9f,-0x1371,0xa5c,0xa5c,-0x1371,0xb9f,-0x23e,-0x7e,0x31,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 16 li6=padCoefficients 16 (liCoefficients 15 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 15 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x71,0x174,-0xd6c,0x1405,0x1395,-0x52e0,0x52e0,-0x1395,-0x1405,0xd6c,-0x174,-0x71,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 16 li7=padCoefficients 16 (liCoefficients 15 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 15 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf1,0xb0a,-0x1936,-0x48c1,0xf4ef,-0x9ef4,-0x9ef4,0xf4ef,-0x48c1,-0x1936,0xb0a,0xf1,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 16 li8=padCoefficients 16 (liCoefficients 15 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 15 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f1,0x2f4c,0x4eec,-0x2322b,0xb3e5,0x4f7a0,-0x4f7a0,-0xb3e5,0x2322b,-0x4eec,-0x2f4c,-0x1f1,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 16 li9=padCoefficients 16 (liCoefficients 15 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 15 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f1,0xab12,0x41e52,-0x37861,-0x1536b1,0x13e1bc,0x13e1bc,-0x1536b1,-0x37861,0x41e52,0xab12,0x3f1,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 16 li10=padCoefficients 16 (liCoefficients 15 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 15 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f1,0x23c64,0x1aba84,0x36ae25,-0x6b4dcb,-0x9f0de0,0x9f0de0,0x6b4dcb,-0x36ae25,-0x1aba84,-0x23c64,-0x7f1,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 16 li11=padCoefficients 16 (liCoefficients 15 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 15 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff1,0x72c5a,0x8ceb1a,0x2c4557f,0x263502f,-0x5bbcd14,-0x5bbcd14,0x263502f,0x2c4557f,0x8ceb1a,0x72c5a,0xff1,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 16 li12=padCoefficients 16 (liCoefficients 15 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 15 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1ff1,0x16743c,0x2a034dc,0x1683fa75,0x40833285,0x2dde68a0,-0x2dde68a0,-0x40833285,-0x1683fa75,-0x2a034dc,-0x16743c,-0x1ff1,-0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 16 li13=padCoefficients 16 (liCoefficients 15 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 15 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3ff1,0x453be2,0xbd38222,0x9949abdf,0x2fd84a38f,0x68336469c,0x68336469c,0x2fd84a38f,0x9949abdf,0xbd38222,0x453be2,0x3ff1,0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 16 li14=padCoefficients 16 (liCoefficients 15 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 15 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xf,0x69,-0x1c7,0x555,-0xbbb,0x138d,-0x1923,0x1923,-0x138d,0xbbb,-0x555,0x1c7,-0x69,0xf,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 15 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^15 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 21 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 22 at hb
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
theorem cache_li (j : ℕ) (hj : j<15) : coefficientsPoly (cache.li j)=liNumerator 15 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,0xba8f78d5184af4100,-0x1184895253a41a8fec0,0xca427411fab3e2f6e40,-0x5d53c8c0b11885e5dfb0,0x1eecced8e5523f16ed050,-0x7d5c77e45b5f0f52f4af0,0x193eeb4bb0d5966c983f10,-0x425c8ba4073803af7cb42c,0x90ed22873f1a7115abf394,-0x10a6eb9f9e18e699182cb4c,0x1a046b06ad02b429cf501f4,-0x22c8effeb71e18db68c234c,0x27fcae067bd040c32c43774,-0x27a42fa2d529784efb9b80c,0x21f0aedd1539ab6a7d44734,-0x19190320b7c4739e394939b,0x1001ec8cf68b1a845539b15,-0x8c81c5c1edf9c842665bd3,0x42038578b32763c4359c3d,-0x1a6666e40960e86de456e7,0x8e9cfc71c21d888b165c9,-0x2836412e281115b79104f,0x955d1a20dc9f21664241,-0x1c042064362b5efa64a5,0x423ba7ccdd266a8aa2b,-0x7718a5c32f8580148d,0x9adc57a9d7805fae3,-0x86c9f12612767a71,0x4501b51bd33d7df,-0x102ccca083f189,0xe9a2d2e30e7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 17 30 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 30 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 37 indices rho q0 m0 0 754727630060371968000 21=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 37 indices rho q0 m0 0 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xf4dc4e97afe2605500,0x1691a7ea4cff864ce5c0,-0xffa80eaff2f1cf990b40,0x73ac7653983e345221970,-0x25903314e9848f41105690,0x95223d4c12025e5e6b95b0,-0x1d6520a88c84d67247d4c50,0x4b92a24e30085bd5e59c39c,-0xa14c3c8d6139b72bd7cef24,0x1218fe13b628d4197f602c3c,-0x1b9632eb09b6da14dcf29e04,0x23f302dd3383100dbef6bb3c,-0x283c722cf20d542e11160684,0x26ca97625de6c9c4202b85bc,-0x2041e78d52ed1e6c364fdb84,0x1722643922616950bb14d037,-0xe49a19b81a4eb9cf1508c39,0x7937b883e57c5f27e9205cf,-0x36ef630e2ef04893eb94781,0x152476a5ee914a6b0684773,-0x6d9ddfa8174073c9426afd,0x1d923c609500a7227ca77b,-0x68b25902034cd06316455,0x12a251a1572a17b1ccb09,-0x299191c6393a73abb407,0x460902ce4adf649af11,-0x548ad3c2f36d01451f,0x43747abab58ced4c5,-0x1f1551e8817b23cb,0x65f685a9c7e67d,-0x4cc40c3d8db3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 17 31 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 31 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 37 indices rho q1 m1 1 754727630060371968000 21=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 37 indices rho q1 m1 1 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x14161272716d91e6f900,-0x1d17ccfd54158c90ed8c0,0x14382bb747be5e8eb0ec40,-0x8f9c41856e76187d0c5630,0x2dba5f19b9cb0e696acd9d0,-0xb1e82d70408e535cd3c1770,0x225708d6c411f71657cfa290,-0x5665301fa2b5c4fc5fa86fcc,0xb44ef6f2b0d519c9147f99f4,-0x13c3fd7b38e8637375ff439ec,0x1d68f3d8d6fa95d7235d76554,-0x255f9289b39363572f34553ec,0x28bf382f759704ff5488110d4,-0x2638a2aec6c5bfaa768927dac,0x1ee20919f77590a2b58aac694,-0x157d5df4aa3b8bc8a46c10583,0xcdb2727f275a980927b477ad,-0x6975d5a8e843a14918aabdfb,0x2e1d60aad94e457641b21995,-0x111551f6911d852689d5356f,0x5504c7b2b411f1bb7e555c1,-0x15f1a99b3dc5ab37f4df797,0x4a0c07d8d94e8abe9fe479,-0xc807e73befa9e6da40ebd,0x1a4dc3c850c53a601f593,-0x297dfdd62a3c992b9965,0x2e7237225df9146368b,-0x21eadae22e7119c729,0xe09716b9336a54a7,-0x282c29e37b69e81,0x1931301c53b6f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 17 32 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 32 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 37 indices rho q2 m2 2 754727630060371968000 21=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 37 indices rho q2 m2 2 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x1a5cf83634dfcf7f26d00,0x258605ccc123ffdd37c7c0,-0x199d319ccc4f194922c6140,0xb29680c62e6e9f5abbfd1f0,-0x37ca19352f832edf30c31e10,0xd4cfb62fa4043c17ee41dc30,-0x283f743caa22f98956bcdb5d0,0x63247da4ea0b22151aa19a7bc,-0xca6e0f1eeff758f5da1f24504,0x15b106bd0bef1911df1825af5c,-0x1f85520d1eaadef9bb84cb00e4,0x2714655b63fe7bc5bb2889b45c,-0x298600a7d324e089c190de6f64,0x25e9af8de5a2a7ced10b208fdc,-0x1dc7461a45a4e411f9c2443964,0x141cce6195dd2fdbfd5ad7bb3f,-0xba8c5a74cf681b4586311b9b1,0x5c8100738c4341610a42f7e17,-0x2709b8ec7a50772e6294ef0b9,0xdec39edb374caa289d476f9b,-0x428466ac4a96d01e885e0b55,0x106d2ac295f313d37fe9df63,-0x34d22a832e373636669fded,0x8751ec7748cf8de8be3801,-0x10c638a069b46d172d528f,0x18c1138ee8557a38885c9,-0x19aa90fd5af173e0e8e7,0x112075faebddc8a70dd,-0x65a42120ed6176733,0xfd334861ec4f7d5,-0x841f59413d8db]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 17 33 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 33 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 37 indices rho q3 m3 3 754727630060371968000 21=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 37 indices rho q3 m3 3 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x229a05c72565c056e2f100,-0x306c628d10f8e50919362c0,0x207baff669cd0ba72a6efa40,-0xde71e331457e8f7d128e78b0,0x443624f3f38efcb156aff3750,-0xff3f743fb71544c4ce66c5ff0,0x2f52d8aa2ed2ae227af1534a10,-0x7231d9343ee47eb5261754266c,0xe43a5ed3430b14c6f0c7f64554,-0x17eaf2910a87a8f382932c3bb8c,0x21f59995bc305420a9ba47769b4,-0x2918a9d9b571cf6852956f8b38c,0x2a9313a0a29e03f64187d949b34,-0x25da9ce5e979089f137d8cb3a4c,0x1ce9dfe3da2e439f7a93d0643f4,-0x12f63a8feb47d47f7a2a292192b,0xaa7b21817442d90f4ab597b685,-0x51c91ccf883207cb4bb805e7e3,0x21516df1b4178496fe1099b72d,-0xb711a63375039212fd64b9cb7,0x347b256862e3c39bdc75850f9,-0xc664cb3b3b47b94e4b3f199f,0x25fd880578949752dcc25df1,-0x5c44c76d81a7abcfc106315,0xac6b3f098b8cb39e24a2bb,-0xedd863ee5061e94f29a7d,0xe428804f9e73d35341f3,-0x8ae677175e9aa7d5921,0x2e14d302bc77b4482f,-0x63b61212be87a6b9,0x2b428c226f7bb7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 17 34 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 34 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 37 indices rho q4 m4 4 754727630060371968000 21=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 37 indices rho q4 m4 4 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x2d6a279561158c7209dc500,0x3e85db058e9ebb20611719c0,-0x293d07a9fee096fdd472b8740,0x11583b6164652ace199c6aa670,-0x53938d1cc6897cc1ebe2eac990,0x132f47e303d4e5316f018ef4eb0,-0x37d19cd3c70a7cad7f245bbf350,0x84036f75d6da45022c61c45a2dc,-0x10262034988b75f7a695bbfa93e4,0x1a7eae2b71e828b6884d3c8ef17c,-0x24c609ba33841a4410eb114fecc4,0x2b7524b18eec68ba49a9e762f47c,-0x2bea06b07aa667e6087cd614a144,0x2609a12c71d68f98d8ae330e18fc,-0x1c43c8a0f3917ebe69272dbc2e44,0x12013fc07348ab7d1c924b62ea07,-0x9cf617cf87d2913643141ac4f69,0x48de5ff0217aa79a8be3b1d301f,-0x1ca989f17bd134f618bec4aec31,0x97a9f30ba4df0ddeae127bf283,-0x29be6b176dba13fb7599055ced,0x96f85a25a73cafd0b3f88540b,-0x1b8a26d53a3a833a94d8512c5,0x3f63801e5ea6a50550fe5939,-0x6f89ed5c634be13670690d7,0x8fb5169910fa3ea5ae42c1,-0x7f64434c87c1ab83ed26f,0x46a52931f3485f97b035,-0x14ec2ed83d869bb9b5b,0x273ff00e9c694626d,-0xe2638b8005bcc3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 17 35 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 35 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 37 indices rho q5 m5 5 754727630060371968000 21=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 37 indices rho q5 m5 5 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x3b9b53f40f6c4855acf12900,-0x50c52f8ecd9e67c00b6e51cc0,0x346890029d4df727296fd51840,-0x15ac2d10bbe73598844b8dbe730,0x669da03dc35d81e5766bf4648d0,-0x172182b6b6ad4fef8a8d09514470,0x420af5e69dcc530d1e4e7023d590,-0x99290e47326b8d9d087a3a1dc00c,0x125b6b070400c53c2699e4c33bdb4,-0x1d7ba740cf39586c6741a3802082c,0x280530b467249e925e0a1db7a0314,-0x2e346ab707babaf2f448a94a64e2c,0x2d8fcd366751f361f70ef9e22da94,-0x26762e6be23528273be48ae1b29ec,0x1bd05b7b24d8ad91bfbaa57137254,-0x1137263a20df4410b8db4a893bd93,0x91907562de2a3ecbdbace4c4509d,-0x416977952ae2ac9ae0f2001a208b,0x18d8da091e8f6e21d09f1ac07a05,-0x7ea1281e06ec65ee688a797afbf,0x2176d65a6da1c761e1bc1294c71,-0x73c6b2f6dddd7ae024addae167,0x141d67afefd83c514923962da9,-0x2bdc67de682236f3fc53806ad,0x48a171f23464ad125a5634a3,-0x57539562f282889b86094d5,0x4773d861da0317212f501b,-0x2409d38375ded0976a559,0x982be2dbe15e2a2d577,-0xf712577c1afbb8731,0x49f8b07b75db3bf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 17 36 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 36 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 37 indices rho q6 m6 6 754727630060371968000 21=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 37 indices rho q6 m6 6 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0x1d8afa8cf25d8000,-0x2e25908bd33c0800,-0x217577091e2f9b00,-0xef62f0cff56e880,-0x49f8610ca661150,-0x10c48f0b74cf190,-0x2e373474645a88,-0x62e8cccf9b270,-0xa676d7812b4d,-0xdda4ff503d1,-0xe98d45e24c,-0xc1b664078,-0x7cf4a162,-0x3d632c5,-0x162d44,-0x5852,-0xc9]
def m7 : List ℤ := raw_ints% [0x0,-0x4e3bde30543e1ef072fc85d00,0x6865ae88d0e97edafe00cb5bc0,-0x42ac3e35efc6b617f349c73fd40,0x1b1f4582111431a3037a3ca2b6f0,-0x7e4017ffe657706d446a4ff93910,0x1bf5b8a23a232d60a01956a858d30,-0x4e607ce75d4cae07dbd437f59e4d0,0xb2520c31b196577e44ded0e373cfc,-0x14f3577d8434e04c5e20991a16f3c4,0x20f44fc8a672c8f9872ec51e869a9c,-0x2bc45b253513098deebe2eed6861a4,0x316328dfda485226cab80869607b9c,-0x2f8ad2e40aac33333542abfc94fc24,0x2720e1a4465c0f2e2b7f593cb0811c,-0x1b8c25ffc30506391cf166c36dac24,0x10928d78bd3e039c5bd90dc62ae48f,-0x87f33bb876a7e73f260fab4f2d561,0x3b25bbba5dcff9d85f2819710e3e7,-0x15b3662d00aa5fe91a3bc796b39e9,0x6a873cbfdcd0c2ccfb7c16bd482b,-0x1b07bc13f9d9ef6edf3f85d997c5,0x597364e2cd451c58e211cabbd73,-0xecc58df5c30739b2052aaf56dd,0x1e8e745b4413d49b149709beb1,-0x2f96c2c52a6c7563275962edf,0x355955ce7ece5b00f44d95f9,-0x283e500d10c1dac226391b7,0x126ed4a7a60027c7a45acd,-0x453c260f7e2b9574e843,0x6125b7a5411e42ce45,-0x18257a020d3ea36b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 17 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 37 indices rho q7 m7 7 754727630060371968000 21=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 37 indices rho q7 m7 7 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0xc9,0x1]
def r8 : List ℤ := raw_ints% [0x17321eb8aa4b698000,0x241df3833be7c4c800,0x1a1714e59ce024ab00,0xb9dd57a2b5d0cf180,0x3924a1421eaccaf50,0xce05beef210398c0,0x233d0f3eab7e2338,0x4ac55587ba8bf68,0x7c84c267714d05,0xa39f1efe0980c,0xa9859bf1063b,0x897f60f8de0,0x5600b8aa66,0x2864033f4,0xd95cbbf,0x2fb098,0x5533]
def m8 : List ℤ := raw_ints% [0x0,0x66ae939f6e91889b96eb6fa100,-0x87010d384dfe72da18210ae86c0,0x54e7d57c75b910746ae864fec640,-0x21fe52621e513d24c23894baf41b0,0x9ba40565cfd3caebf9b1bca936e50,-0x21e1a0b544399de8493d61170ae4f0,0x5d4aab9447d370c3d19bc67ae42510,-0xd0549dab033e5b93f1b4e2fb6164ac,0x180105cb7aaa2d57179afd2bb0c1b14,-0x24febef39ad7a70a26c2703f27b47cc,0x30181b8093430621a17ca2bb5763974,-0x35107cac060f256d21a4c706cda1bcc,0x31e3212f15e1374b130dead9a9c96f4,-0x280b7c3120f8eb5815532628148448c,0x1b74bf24ecc704cd4ebc4bdcbe2d5b4,-0x100f2b9a72553d3e8e226bb0d2090bb,0x7fd88e5b1c27cb4d0dd4231a9967f5,-0x35dcdac7aec57055353ff22b11b5f3,0x13172423049cf3a133b2bdea6ca41d,-0x5a4668d0a1741eee191abb348a487,0x15fe383168d277943cd11cea19229,-0x459bc24554720fcc5da98ffe94ef,0xaf65a3943f65da37dd0b6c695a1,-0x156d0ecdcbc39417d753e65ab85,0x1f5d1f34efd0884c088cac794b,-0x20c0def6da125541b83ce0a6d,0x16c0637fc935a5436e173f03,-0x973285e4b1c5c231c1e5d1,0x1f859e96063d6c63a027f,-0x262c5143d2f8a81e9e9,0x7dff05f991051587]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 17 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 37 indices rho q8 m8 8 754727630060371968000 21=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 37 indices rho q8 m8 8 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x5533,-0xc9,0x1]
def r9 : List ℤ := raw_ints% [-0x9d507e0b68d54208000,-0xf44785b8053b8341800,-0xafe8cf93a9aea2e1900,-0x4e0a195cac1d95e2680,-0x17e4575ce60d9081170,-0x55b76060af25bc4060,-0xe9383ab2961099858,-0x1eb72f6dd127f9918,-0x32ba49e2567371ef,-0x41fba47e1628d5e,-0x43807d6c4d7738,-0x35dfcd244ce69,-0x20fe2d6eb78a,-0xf0e4c355ac,-0x4dc3ca3f8,-0x10079a75,-0x19dc6f]
def m9 : List ℤ := raw_ints% [0x0,-0x86c521c1411f034c36150283500,0xaeabdf87d11cf22f951b5e510dc0,-0x6c3b5fc53369f41df06b8ef074340,0x2aab382f55c4bc18373c41c3c72370,-0xc04047cb8d8946b6813fb451674c90,0x2928557cae7ccc311b62d43e30b37b0,-0x6f5e7d47e851c46b9c378930a8aea50,0xf436f44f4d31f2ba92dc5e0610fbe1c,-0x1b9ba24c877e83607016d07759a51ca4,0x29b5761ba3de67d1ce86b23d4f2932bc,-0x3518eeace30c2962b86ac54526d9f784,0x394e6014c1c0acad2d1c888fb3c1b1bc,-0x34a290b22d04bc29b196a773c0201804,0x2938e662d8273f22a52880cc9606f03c,-0x1b88a94627e468cb986578fa4ea3d304,0xfa99b8916785a69b841d2d94af494d7,-0x7908234aa0453809062293684414199,0x31639a0e23c4f654f0158d3bf11136f,-0x10e98b402be86fcbcb298821d6c5fe1,0x4d0b73e2872fbaf4e9472d1a388293,-0x12055fc2319d52d66e1de182d909dd,0x368ad31ace5f9f9b5a5aa1eebdd9b,-0x82cb04f8412ef10543e992489835,0xf1dd59c891c96f6ac4703a3de69,-0x14c8cdc4eca11b3d0e8641a56a7,0x14338fa17a904ef3247322a571,-0xce815803b67663410f9320bf,0x4daaf0c593f969d3f91aea5,-0xe5bc7a7b6c48a18932feb,0xefd4d9f03e59b80895d,-0x290dd7dca26b326d3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 17 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 37 indices rho q9 m9 9 754727630060371968000 21=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 37 indices rho q9 m9 9 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x19dc6f,0x5533,-0xc9,0x1]
def r10 : List ℤ := raw_ints% [0x2fc02b6576e86f08a8000,0x49f926048c077a1c6f800,0x352039bc2e5376aa41d00,0x177ee187946f330ceb680,0x72ae8e6f886d50941b30,0x199bdd0e960857fc6c00,0x455783a00e266dbe098,0x914aeb886c81830638,0xee57e637a9a3d594b,0x13385236a7da9cb70,0x13782c387a427236,0xf5994c466ae13c,0x94180eb1e70c9,0x423b6aedcd70,0x14cf03595b0,0x420fe814c,0x64bb15e]
def m10 : List ℤ := raw_ints% [0x0,0xb0e2bc4da578b45406fb934c5900,-0xe21ab31ba7e4b82c1e7febca620c0,0x8a19e8752a53f2a22e18e3f00b8440,-0x35a2dda23b65f241b4032bba4f62830,0xedee8cc5d5004f5b3926006da8907d0,-0x321dccb572f36439f5864fcc4fac6170,0x8554809f1a32c56ca8c3b46634b91890,-0x11f3a9c4ece0aef58790009ea4f39fc4c,0x1fdf4f1f96f74dc2ae4d5e4b7352ff574,-0x2f38521b1f309fd9037df022ebc6c226c,0x3ae4044e3833d2c0502393712810ba4d4,-0x3e322cdd6703b2c277e666d778f63846c,0x37d507fa89b31a502a13f360814f9e854,-0x2aad3aeb2abeda6b7a247e7c49181322c,0x1bc73d25189c73adf31d2f2f1467a3614,-0xf5f36851c7966d9a8317abbcf7bf9ca3,0x735485b038798ad0b2930fbd7806128d,-0x2d97616dc331096ef271d956f02c421b,0xf15c9c1a648d2d7c79cd0659bca3b75,-0x42349b2a2ecf2d9e1b2a7ce18086d0f,0xeddf4ddf93ea7ca2491f50568c5021,-0x2b057188d0ebb3cd9e85737cb1d637,0x62267b3e329c2e980d080337473d9,-0xaba41d4dd18181b8df0487db879d,0xdd84a419dab15fd02f0a3b11ab3,-0xc834433f8f0640d070cbba6145,0x758266eebcdd255544dc8c8ab,-0x27f7120c217f673f19e27889,0x68add50c98b73e21565147,-0x5e1b8d81f55bcc90bce1,0xd5d9031bb3f97c30f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 17 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 37 indices rho q10 m10 10 754727630060371968000 21=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 37 indices rho q10 m10 10 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r11 : List ℤ := raw_ints% [-0xb9fe0ea53ca5b823d50000,-0x11f8a5ad44e9ca379087000,-0xce05d036873854c6def200,-0x5adf942ff536028b85c200,-0x1ba32691753f76a513f4e0,-0x6265a55532fe655e127b0,-0x109598f2d67397d4cd9f0,-0x2295c04857df68031488,-0x386b647ec126c6a1d0e,-0x4850efcee457e7a1f3,-0x48ad8b406cd58a9b8,-0x38c0a409c6f044b2,-0x21d151c337ca428,-0xee650fa6b3c2b,-0x497679f91b48,-0xe3474552d8,-0x14e599cda]
def m11 : List ℤ := raw_ints% [0x0,-0xe8299725e92e6cae492a315434d00,0x124d2703c0b269a9afd86e579a0afc0,-0xb061bd56fd47dc56c31dd70f57ad940,0x4384c85e5776cec4442e71cdeb160bf0,-0x127061f8de3774b0cdd5a8cb3c176e410,0x3d2b3c47300bea600ae0e31824bc1ee30,-0xa011bb66f92e122b81373bd53d21163d0,0x152eaaac628c6463559169a945f9ec2e3c,-0x24ee4546f957c6079d86c9ca1792208684,0x35adb38843d2a7c8f9708e1b9d069581dc,-0x419c32bfb0e8ca6eab42e16eec20b7e664,0x43d53c0f66f06e6fb29f80f5cfde2c5edc,-0x3b88c9c1921f48f04479c85cb172beace4,0x2c6ddb1ff874deff9c982a6d9603de6e5c,-0x1c309c863f6240a10778b37f8adae43ae4,0xf2df6924fe841d0de318ff03037421cdf,-0x6e98f7bcc9c24d3b4e8cb440ca4ce9211,0x2a5c5d6b63281d8bb4ce8c5593adc30b7,-0xd8b6f38d8617921bb8b199b5ba6ccc19,0x394520df16ac7dd8b530433548298bbb,-0xc58858490e1217393bf6528f31ee935,0x22269656357820b4af0f351fa918e83,-0x4a19c6c320c91e1bceeb51c1821ccd,0x7a7bbb384aebf120ecc8bdaba1661,-0x944630b72c4668ead9974e238a2f,0x7c7e7c53fbf1779f8c40f823f29,-0x430d9b6b3c0e8f01579de15187,0x1498396541e5351f5b5b7d1bd,-0x2fb4583a9c23bdf08932c53,0x24e665914b92cf24709b5,-0x459014fa9b32e390fb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 17 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 37 indices rho q11 m11 11 754727630060371968000 21=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 37 indices rho q11 m11 11 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r12 : List ℤ := raw_ints% [0x2695aa4ed83d7f38dd9f0000,0x3b8b2bdd390a68611a29d000,0x2a936d4985cfea4c20f58e00,0x12bc6853dc70ece373510b00,0x5aedfa0797cb7b266c1bc20,0x142c1ed3a49aa2230b57fc0,0x3635d99cc32eb2d806d020,0x7098c1cd5133261015970,0xb6d39231470d5623b70a,0xe90f76c62a843d8696c,0xe8b722a0dde80bde85,0xb4523baf71ff07400,0x6a72586dc3fd6dfa,0x2e5c48aee014f34,0xe1495e8bae8fd,0x2ac174283b50,0x3d5c17155a]
def m12 : List ℤ := raw_ints% [0x0,0x130b69661c20ceea4c00760be855100,-0x17b6771c07d1fae04c79fcd2fa2e6ac0,0xe17bdb1ee678f93919eedfa3393ed240,-0x551ce8bc8f5bc5c2df70416d3afc93ab0,0x16e7e2c41475aa5c18453d9f0d01ee7550,-0x4ad4ada2d03b6c3fe89de8c4e756d7d9f0,0xc0b2dcd8afbadef999d72375c725ec9010,-0x1912d766fba9f3e8e3e803632789a292eec,0x2af23b12f3ed55fb6238558220819e224d4,-0x3d43eae95a30ca121a0be8d725022f1000c,0x496b20a6238a41580826f13a27ee78e5d34,-0x4a55a78c9b380cbe7cf04a404172dc1700c,0x3fced52633770bf8dc85a811f95624a66b4,-0x2e818c74fc5fea3efe5ca2f293d35df1acc,0x1cc5ab6ee3dc52e55efc265405786afab74,-0xf145fe83f87ebb0bcc5f32393775108b4b,0x6ab7cdd806bf24678f1d7b5a054f814665,-0x279c116f551797ed88b299e3376f3aff03,0xc3d6c65dacdf22a4c12599184ac60e60d,-0x31dc2e9190e8b765dbc93fd26e0f49b57,0xa5138bd72d5224afda64a5e863629459,-0x1b46952716d459d087c4fa3ce24ee73f,0x38448708cdf7fd4985e58cf3dc4e651,-0x57dd4f8af1d1ab6e0fddf7b672f0f5,0x63b3100295b987453792ea84d22db,-0x4db1f0554c1f6cde86b5bd061f5d,0x265b62a3a4d9bbbc81170128713,-0xaa02e643ff3a8f9eea43f1b81,0x15bd9b6cf68fcb74fc1063cf,-0xe753b4601831a1a0b4e19,0x169c42288f13f594e57]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 17 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 37 indices rho q12 m12 12 754727630060371968000 21=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 37 indices rho q12 m12 12 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r13 : List ℤ := raw_ints% [-0x714be4f93b37485d5605f0000,-0xae8f7702e079a3f880a23d000,-0x7c97b6c6e5707f1485749ae00,-0x36b779b15ac3c4414a82aaf00,-0x108f0489228349312622c9b20,-0x3a9f0422a3a65a00ce0c0080,-0x9d105942bf123cff8377c10,-0x1451afc870a66dcfb751b40,-0x20dca6f4f44bc68ae030a2,-0x29b2d2fb22f808706cff0,-0x2969b61112001f858d0c,-0x1fe2b2edd79b0e14533,-0x12ae1da1bc4dfb45ac,-0x80fb34212c222862,-0x26bbead34bfe7f4,-0x73f78ad550b9b,-0xa370bc53362]
def m13 : List ℤ := raw_ints% [0x0,-0x18fefa5604eb0f9383c09aefa0efa500,0x1ebcfd35abe55d845f7982d4e85cec1c0,-0x12084a98bb83922913cb60277257583f40,0x6b7037825eca354d85ccf088ad30149070,-0x1c81994114b71faed9ae577716602c2df90,0x5bc012e5ab26562a024ea0cf6ff341650b0,-0xe89a5c09e8b73f6ecf669aaad1eb18cb150,0x1dc5ac553123c06d29ea4aae08285fef555c,-0x321e2126efc07d11d208ceb98cecd000e964,0x4632f93654a056369a4039402bbae7440ffc,-0x5282b068c5474bcdbfce9875924d9c772644,0x51d7350801c6c7a89f4fb18a69fda2688afc,-0x44bb5b27ec5ff4640e63075ccd9232dd32c4,0x30f09fe943a16de23bae7afc3c9ff4e2437c,-0x1d880f612f5474e191b0cab4066958ad9bc4,0xf117001255156ca67e13fe8c6d8a0952ea7,-0x679926f3cc5ac2b8598cd7cf0b3130e34c9,0x25443e31f0274d063a67b13584fa46ebdbf,-0xb2151da00e5616fc82dffe6d6876d55c91,0x2bae1ad43c7b6c991e29ca161b901b1da3,-0x8acc9284ab1d5b675369f3c40aee19bcd,0x15e9cc07bbdfa96bb88e2d87c76d7fa2b,-0x2af660dd4602a9afd13949ccb1121aa5,0x3f582eb564a77d660447f14082ab499,-0x4352ad4f188460cd9bf952cf1f5b77,0x30a64a45f9ba99dad1312dd43a121,-0x15fd800e1a1742e16d7f8d80860f,0x57ce36e8a61ede091afcc49a15,-0x9e84214f94f53b11113fe77b,0x5a91e3400f0cc3e059f54d,-0x757f748e318daaa5be3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 17 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 37 indices rho q13 m13 13 754727630060371968000 21=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 37 indices rho q13 m13 13 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r14 : List ℤ := raw_ints% [0x12dc8011064951504b0e84b0000,0x1d04f185e186a9b84509a341000,0x14adf75502e84acb64446f68600,0x910bef4bce734fd5ee22ccd300,0x2bce4144e03cc36224eaeae1a0,0x9ab99201a8d1c301f31378e00,0x19d7904a74c80df99410fbf90,0x3554c370bb78e7cd5e1b22d0,0x55f549e2786b25de0decf3a,0x6ca502d8238631473684e0,0x6b68fa282c2ef3b0cabe8,0x5242ba932b20b0ba050c,0x2fe420b36a3452fdfe9,0x14836ad41ee0a7a1e0,0x61ae1e86d0f449e6,0x1213b8e2b085c84,0x1920c7be84fff]
def m14 : List ℤ := raw_ints% [0x0,0x20cea890e67484719ceccb5a833a88900,-0x27dced6f8ba7400b372f3c7770f9f5e4c0,0x17180d02773596ae43bd7228e776ce03040,-0x87ccf85d8680a4eaaa189f234e8c8941930,0x2389f0b920b802999d788e91b87a9e7816d0,-0x70be489d374a69388366a4a2e31960966e70,0x119824bd0378af0d9b4405d1b75bda6d16b90,-0x2375798b7a19fc46142206dc8a49b5b29648c,0x3ab04be48983cb6d61b51569d93cb2a7cc134,-0x50beb9129638a7e98f3625baddc9772e508ac,0x5d1ebcd4cfb6e6bb5e4f493a8aeaa3378ba94,-0x5a84736d0169739ea69dbdf6f19aa21d086ac,0x4a664d74f658adfa60a453072494fa277ea14,-0x33c5248504b0f5895f4cc86951bee95dae66c,0x1e7a343c8f7a631f05c6e29788fca1834cdd4,-0xf24913d79f8f000c8f180994cb7e91c7f6b3,0x6529ecee730e4b24e646b9d3e92bba66097d,-0x234607bf310163fccdab910f5b0c97e196ab,0xa2ebd0dfeeaa0c630a3efaf3404158fd9e5,-0x267f69452b27e58dc0ffe89b8141133715f,0x756545fff5b493200e09394276fbb1bcd1,-0x11b470bd5c0d0e75d433d7d36a78a13a07,0x20f9ebdfeeea107c3c0b40d35079c5b09,-0x2de1dd0c21a82faa9049a0ae5b8b4d8d,0x2da40fbf8d9c440d501901c5a3e8bc3,-0x1e8e1aba53647460d83ad427785ab5,0xca1bf80f2c7f9b0cc866aeb7843b,-0x2d62e02649327ddd8ea0a4d5cb9,0x483962c95619e44f83a490c17,-0x236f17808fe7918453d3b91,0x262261658d8f19ef395f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 17 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 37 indices rho q14 m14 14 754727630060371968000 21=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 37 indices rho q14 m14 14 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r15 : List ℤ := raw_ints% [-0x2e65ae41a8c24851a26c45a28000,-0x474b751334c75286c30546f8f800,-0x32bbc78754d596875cb2a00c5500,-0x1634713529c6aeb338f2165a9180,-0x6b1ae4e323cb664c9d218b61bb0,-0x179895e00c0c62316bd83c52cd0,-0x3ee95833972a497ddd19ee9778,-0x817ed41cc2e02ea2d7f398e00,-0xd019f91c5dd6e38d64b3c1e3,-0x106229e0d213a3880b797ab5,-0x10226389e0938b43d094f74,-0xc4d0e2d5024afdfacc34c,-0x71fb9b35d1d5fb4baa06,-0x3085785ab267a0dc471,-0xe55a735f3f5016dbc,-0x2a11f05b033a1d1e,-0x39d938cc84b29f]
def m15 : List ℤ := raw_ints% [0x0,-0x2b0f3d3e2e78edd51df6cae6cc3cd33d00,0x33b81101c7d846af90c5b04cc44812bc3c0,-0x1d9a1c3a5003fe77da4546e3d772e07cf540,0xabdfb24eb37e2e5ff322f8f06e85e716d0f0,-0x2c62106163d682341a0a859628d4782971f10,0x8ad68d3ee4c7ffdfdc1767974732188a7ff30,-0x15592e4d5d12292cc23639dd9b9fa676a932d0,0x2a5b91065e50733c7ab6cd02f00cadb383bb7c,-0x44f524b4bca7338ccb59fe3875e83f5c5a3d44,0x5d398a4e9722ce08723e04b7c75c227b0f251c,-0x698739e777329fdd8a6d0b3ed824731c6cef24,0x649015ddcf7f00a679cecfff188a8f8fe1fe1c,-0x50ec0b97407de02c34082881eaed63ec6861a4,0x370b266cb9a78ba59bb7fd653e28816fdf779c,-0x1f9f56a7e01725c702ebdc20c60b9be7666da4,0xf4d92584b8e37ac0984a4727d45b1d1d0ec2f,-0x635b0d2aab11c728e7d39dc948fd720c527c1,0x21954bd23b76c011e71d83d10d83ac0982c87,-0x95ee810d9631f454a4abcf74c5480766ff49,0x22210cf64cfb56c342f499c8639876b9224b,-0x63dc1bddf19069686c363e11459868157a5,0xe61e8867290654e55ee015c983b66ffa93,-0x19703e2473641c367dbffb3b26efb717bd,0x2161b8c19eb1ceaf267f10e8191009711,-0x1f0e5e280671a53d62d141ac45dbcc7f,0x133e6e041751107c1dbb4e05ff31959,-0x744c452d830453a472ead54811057,0x1779af9945594bb0589315782dad,-0x20e63a1c3d4ff063da4faf1b63,0xdda4eb4c7aed9ce6a10c225,-0xc5e30775a0e663b6b18b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 17 54 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 54 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 37 indices rho q15 m15 15 754727630060371968000 21=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 37 indices rho q15 m15 15 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r16 : List ℤ := raw_ints% [0x6ad0325c44f06434b18458b128000,0xa3f1f957c5f0053dade9fca367800,0x748400a483b2c3ec0eab17e5e4d00,0x32ec6b20dc3abc9db2c0046971280,0xf53ca7c2fa80435b04234453cf30,0x35ee34a4f31e03cb9ece8e4a0cc0,0x8f7f85c5fac6bb8bd679ba19da8,0x126b2d5e8da93abf58d14f91c18,0x1d85c8659f153fe66dd9cfe0d3,0x25142f50b51a2ba874f76d4ac,0x2464774268ec3b3be5817d1f,0x1ba3978c45d7ba224e0b740,0xfef745b020fb8c20a9c86,0x6bf91f3da52665d4ce14,0x1fb42af68c9a4efd1ab,0x5c5f62442fb050ec8,0x7de95ad8b541625]
def m16 : List ℤ := raw_ints% [0x0,0x388400619cfeb827b753ea4eec0fd540100,-0x432136098efbd00f7c711490c19e98970ec0,0x25f9ec412f0d9288ca8ff9bdaddd0621b1e40,-0xd9ce401c562e7de7bbec967ab8f8c7cbd63b0,0x37859f5ee4ba764aa7a10efdb6b32bb0df4c50,-0xab551e50b25a4d7184c9a991e026128ea03ef0,0x19f7f0dbfa96deb5725856774c4fe184f6b8b10,-0x32bf043fb10f1042bcfc6feeb424fc0b117c52c,0x514a85d9d2f3bb593011fbf79ac9bf837432294,-0x6c079fbcc2f3a707c13bc4121502e0c7630244c,0x7812d15ee101af1eea4e1ed69108a457a5054f4,-0x70369a14d2d9e2cbeb068b7836bc9ed88a6304c,0x586e34bc4b543b6a1c073b844bc7691af8f8a74,-0x3ad0fc83d814fedcd7ef3ae31c40ac2ef543d0c,0x20fb9424974bb3b3e179dc2bc0ff2c47d657534,-0xf8ca11ec73a03de8dcce1efeab0f7447c528db,0x6220dd677fad376cbe30642fbaa1833a07b1d5,-0x20281d2c8d43bb8911b2bddf9c41668851e313,0x8ac532596af2247d58e1c46ac825347cd1cfd,-0x1e6d975ce347c57685700e61b4caa70aea127,0x556958f4033b24c11e7640a2861b62d6b789,-0xbbe97e32099897d07bea517079db242308f,0x13b7b2e3307b9db2a1aca0f4e58d3d85001,-0x18638863a61e2ccd349c3d3d99d7915365,0x153462ec4708b8b38442828ccfddaff6b,-0xc268b9caf3c2698dc42fed6ce3bf94d,0x43057df248d7a116316ac4011dfa23,-0xc25ff74854833c3b9e05dcbcda31,0xefb4dbcfc563adaa4fb5940c1f,-0x56968d7b274bd1f5f657b349,0x4022ea5bad7b603cd7627]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 17 56 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 56 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 37 indices rho q16 m16 16 754727630060371968000 21=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 37 indices rho q16 m16 16 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x7de95ad8b541625,-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r17 : List ℤ := raw_ints% [-0xe87ca50bae401829261e6110838000,-0x164797f2be5217d9c5b2021c54aa800,-0xfd0e8ef11ea052221e9e1185fcef00,-0x6e75458bdd8491d3d49762ab2c4d80,-0x2132ee01640d00148dbdc5dde64e10,-0x74a060a527de9a6ab312049cd7aa0,-0x135c31f7cb7bade7be1c4709eb8e8,-0x27addca0fa7f7d63b210d68acc88,-0x3f7497185af19003d132eaec409,-0x4f7dd218a25fda222cfbb375a2,-0x4dcab0496085c2a81d6550330,-0x3ae22bd4e401b22c2229b85d,-0x21d1c9e4c5e825e39c94f26,-0xe423333867278e9844678,-0x42a48caf55fdb258c860,-0xc0ffdf95f06972b2c1,-0x10531128e4c920f29]
def m17 : List ℤ := raw_ints% [0x0,-0x4a2d40801e0e51b4209e238795d4c7e41500,0x572b1e919286712fa55d6f74fe202846435c0,-0x30c28717e16fd7fda2cac7ab5edc83717a7b40,0x1145ac40b9e268b6dc90c54aaff45325107ed70,-0x45922bb058cdaf3ccd390f1c5bf2a8286a88290,0xd3dddd631219f978d32399926ec574b377199b0,-0x1faa88483ae372571b9bf277201f420fd2d84850,0x3cf8172e9bc5dcc6be7191407ed3b9202b2da89c,-0x6023ec97ab15e8b6ba96efbc9b4c0790f932ba24,0x7da3179335bc50e81485aa858d7d8496184cc93c,-0x892a18856f8eb4efa259c7697f3dde00680eb904,0x7dc04b3c0be329c34b688f69deb1f304fc28403c,-0x6114a5c853807ee92d9179466082c89eb2e53184,0x3f27a721781bd183924fc245c894415e605cd2bc,-0x229401219c87919299277c595ea768d25c456884,0xfe2480881b630a094f53d9c64afae62bbfbe777,-0x6172a3cd115ba67ad05039ec2934190044bf8f9,0x1ef65b6554a9d2583d7cf206d400d162c2cdf0f,-0x81281f0117966db49486a21d1dd2b75f4ab241,0x1b4715f1b817921a63084f07ed9d8a486eb3b3,-0x4971287925a6ed0ef72f57ea20e5b981622bd,0x9a36e47d77953ed37f174140e48ebace19bb,-0xf5a56c23811da92005ee00ed8c6e1acea15,0x11e3908e9ba4e33ae2eeb49a2a2ff872bc9,-0xe863c547c91e71c1916d62c2b3e074f47,0x7b07eb0545c54cd848cc169613ce05d1,-0x26acb3ca78cfabb3ca88a7cc305325f,0x64a05a671fe02e9bb0897d7970285,-0x6d1e5d7273672c87dca758b320b,0x21cd766cef272d4d78060b63d,-0x14c60215129f0aac52ebf3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 17 58 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 58 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 37 indices rho q17 m17 17 754727630060371968000 21=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 37 indices rho q17 m17 17 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x10531128e4c920f29,0x7de95ad8b541625,-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r18 : List ℤ := raw_ints% [0x1e245b2fd99eb8031f235e194b798000,0x2e2ca842783ee0084ca6f400d891c800,0x20beb2c5c428d023fbe5cc43406a2b00,0xe46cd9df1087cc6205611900f8dcd80,0x449114804fed3370661d2e359d02850,0xf086dcd1d21c24009d8afd83b3d200,0x27dd1e5af43ba1be7faca43d22fd28,0x518e1c926a8d870dfb44c08b36b08,0x822935e5d93c2da79cd3cc98a5cd,0xa2af1dda442b0a7ac8b7c9c33b0,0x9ecbfb28c73a9dd7c135665cea,0x77d966b076e29b6883021e17c,0x449b407249171d51c7208fc1,0x1cd0a7a8e9409d33db0f870,0x861639f5a1005afe7558c,0x18256dffd867e2a43bfc,0x207b7d6ee7b0a463a4]
def m18 : List ℤ := raw_ints% [0x0,0x615b64a82772cb3c6acf8ea1f4a7465b5b900,-0x713c01ad58e360b0af95e7de4d8a34dc3868c0,0x3ea7ef92dd66a0ac763e91efa66bcc0d2df1c40,-0x15f10d2c565730edac48e4e0210fe6ea3e0eba30,0x5750ace871ce67365887a622d3006258207a75d0,-0x106841fa54365446949d927be435382e48e246b70,0x26b4dc13277ee77c84beaeba285d9083a1467ce90,-0x4974991a45f8672b4a7d5236b716566bc47ee38cc,0x720fb91c5032e1a6379fbfb6a79d7c8418ab7e0f4,-0x92a110e9dd1fc877f093e972065fedcc55200faec,0x9d4b83f9834d17df2e4dcb07ccd8c76b1da580454,-0x8d83b66242dea55cd78009f9dc6b54aa4031e94ec,0x6b0ead2ec7f21b46abea15e918aed5e9187e39fd4,-0x442342f9af2fbe3a11f2d48d1b8a145de269f86ac,0x246ec59c7c5edb49779a281454d9ec87434c0b994,-0x104f6e7122cb2a50d292630936568660f321d9bc3,0x614a3b55c788b27e180e73bfc88804f34d16656d,-0x1df960c65356c7572700e9adab0f7c6e78636e3b,0x78dc77912b1b3f8235bd9770a76ef0f5a920555,-0x189571aa2f517f05c5e8e43c5ef1e3549d4ccaf,0x3f79405577889b691a64c648b78b6e05dc8281,-0x7f2abcef2145c77639652453e9616e2be9cd7,0xc0192b235198555c75cd56c7b179a6fbd339,-0xd2b8a3538c43394de4dd105966104a7887d,0x9fa5db643575f2f5df120de84df90757d3,-0x4e054c78e78590decb72a0f191cdc3125,0x1657a8beb46b258972859e6e036ad2cb,-0x341b691ddda2aaf0f669d683b1c1e9,0x31a73131c2eacabb78899a0d95e7,-0xd2fce3cca43af499a3da7f341,0x6b964f52c9afcbabdee6af]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 17 60 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 60 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 37 indices rho q18 m18 18 754727630060371968000 21=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 37 indices rho q18 m18 18 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x207b7d6ee7b0a463a4,-0x10531128e4c920f29,0x7de95ad8b541625,-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r19 : List ℤ := raw_ints% [-0x3bf9f91a8cf686e4374370feb6c660000,-0x5bcd05f13387f3c7b013b1e1f5e13a000,-0x410a60dec8fe3aefe76c8c29232de8400,-0x1c53ecc25b16a9554a7b47dd3e12c4700,-0x87e4ddca9de95faa563623f129c739c0,-0x1dc1774e646135d037762a82952547f0,-0x4ecaadce8ce7f551bd2cadf5ab8c520,-0xa0efe05316e61f7941b686f294a298,-0x100645d0aec35a41f7ea2ca71f194c,-0x13fcf76bf055a5e91246dc09bd017,-0x1377602f92b0b2c95dba48824a80,-0xea77e7b93b47a553c4ec1449c6,-0x85d467d578b16ab41758380fc,-0x3806043b1f8dc936dd86d897,-0x103b624bb1fe7ed254cb3a0,-0x2e9090e3ec0c4b42b1fe4,-0x3e52d48e59b9b45c898]
def m19 : List ℤ := raw_ints% [0x0,-0x7fc7f41cb3c6aabf4c306b34911b8c57e82d00,0x932706255f62161296a2d74db5c565610a097c0,-0x509354b5e3d1b725ce9ae5e55943cd4314f65140,0x1be7fdafc366eb9292647ed4b0cd8117566f205f0,-0x6dc1bf09522b8aa4b94b098605c17f498178cea10,0x145e91e4d115ad8da7bdd8633f9773e5c6fe30c030,-0x2f6c440fba5008f0485a4d90736c66ec66b36851d0,0x58bd60e9223f15b3c6c10e91a321f80edb8dcd24bc,-0x87bdc2585fe72868e7f4ebd415e56fbf7e5900d804,0xabb7fdf7375ae60c1b25595be2329108af2660c45c,-0xb5104762bc4fe3b2f43518d27740805530e8a83be4,0x9fe8aacc78495f4dcbae598fccfb634cba2af8995c,-0x7694803e217dc154fc5deeef6485b95f98c566da64,0x49db941e55125b437e88e40ebe344d9dfb3514dcdc,-0x2693411b0d19a0ecc50b3965ccb19a96d008198464,0x10d55b51a0750ca79e67cc86947161e31e6266a27f,-0x61a3cf68d0d1690842c941141a493b89b81e04671,0x1d2bc159e097c2ad35bcf48a1ae80779f1370a757,-0x71b1d8616e3d662ca7d25c023e55f6ba6ee70379,0x16452f8eb7726a582cf0abe7d09cf8c602069bdb,-0x37211e22645c3ab03ec21f9e842c04a1be75315,0x6958689ea985e03e169f831a3701c1409711a3,-0x96d760b76eb1e37c9c03d1f514104e90437ad,0x9bad54f8979f7794c7a5067413e60efbf0c1,-0x6df975a90ba29b77cd70d63183ab6a745cf,0x3191c39a5bd52a17ffc7b49600a4405489,-0xceb7627cc3742ef2a68b5512040b9e27,0x1afc9b6c02f59cf836c507c4c3d5e9d,-0x1695997c472254a0828e4e7c7c573,0x52408a26f7d57684f10e546795,-0x22cdcd0999808ae7117151b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 17 62 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 62 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 37 indices rho q19 m19 19 754727630060371968000 21=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 37 indices rho q19 m19 19 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x3e52d48e59b9b45c898,0x207b7d6ee7b0a463a4,-0x10531128e4c920f29,0x7de95ad8b541625,-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r20 : List ℤ := raw_ints% [0x73137b9e8c6b93153f5f1b50bc73840000,0xb000d61d41bbe09b71c21a20270d7ec000,0x7c97936467d5abbea0b0b87d8d86486800,0x3636c4b89fb25622a988d90b5378df8800,0x103cd7aed2b8b4befdcc9b9fb223848080,0x38d22a8e6b4fdb1425a1a4a5f1470b3c0,0x9643b4d819231ee13eb631c5abd2b8d0,0x1327b76ec2acdbecdf9281045520ad60,0x1e77a6741928b64994a5c0d36b23b20,0x25ef66e67320f0fcb3a6ec2caec8cc,0x24ded0ae64eeee328d34a6a627e09,0x1bb1798ca4a457b3dbe136590ea0,0xfc4327eda92780e9523994b38a,0x694bd905461feb21dc6079994,0x1e685e0bf7586cae1c6802c9,0x56e704e78f9a9fb0590200,0x73cf09af769057130b54]
def m20 : List ℤ := raw_ints% [0x0,0xa7b67065abf4c01b13ff8cb4fe74283360bb100,-0xbf4d8cff5e964dedc1ef574e6a93150f5d2c72c0,0x67b2ef4b01d36a536dde611bc15b7e1f29cbfaa40,-0x23886b6887cff7732a86a56fb11158e4515cdcbcb0,0x8a2d5fb42db87789de52b10413f5cca5804514f350,-0x19562e9c84bbe5edd381f6a0ce9c82ccfef885113f0,0x3a3c2a9c048f4c25d51e001d8ded794f84074941610,-0x6b7d3b8f9324e8f7e8eea494ee6a4c8f624d82d676c,0xa20796c69ea13663165d8316aee55d3a9bf1e12d454,-0xc9c7833bfcbaa34370b6a6247ddc2d1decedd26f48c,0xd1325a93ddd6c322764fccb8b8eab1e05a078c5e0b4,-0xb56be6bcfdb57665964a5366eeefa69d97154e69c8c,0x83e90046794c31534318b50b4400377d2f2c9e1c234,-0x506cade1c2e4b3f8c7eddae19a386f44db4c8dfeb4c,0x290a3709061c9764a3448636a9f90bfa672de4af2f4,-0x1175ba7114fd08a6df67f3dabe11df29b9acc4b796b,0x627daac53105cb01c3aedaffc29d23034933b89a45,-0x1c891776ace582b779858b8b9243d1056664c5f223,0x6b804a2bce69096e8f9afc3066b6649ce58d0b8ed,-0x14467a637766fde9ce82366466645ad8013f205f7,0x301c2d35c712cdd134a90f579e77a344aa2babb9,-0x57a7024ce4c8c7b2bff6b3c2e13b5f7c57b40df,0x76e856f20fcb998ab63e3697b21b69e46b02b1,-0x736336cdddcb22e50482509a0964601c7c2d5,0x4bf268b38cfb06908bc82eb20f75b14e1efb,-0x1f8bbbd29a8b37f57a7788205353452083d,0x77a25688fe574fc0d6a7be062387c2833,-0xdfa49118a7d62adc93f4c09382051e1,0xa4487aee307e8ef6215c2cf36cb6f,-0x200b3d5343c29c5f4b87bf6c979,0xb40960008e9a9c36a89dcf7]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 17 64 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 64 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 37 indices rho q20 m20 20 754727630060371968000 21=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 37 indices rho q20 m20 20 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [0x73cf09af769057130b54,-0x3e52d48e59b9b45c898,0x207b7d6ee7b0a463a4,-0x10531128e4c920f29,0x7de95ad8b541625,-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r21 : List ℤ := raw_ints% [-0xd5d530c0b56ecafcc2f16ca081a0b2e0000,-0x146d1e9205896905da0a970cb3650886a000,-0xe72d2e24ba7c2dc9a3e14b6ee5866c91c00,-0x648193066ae34299762d45fc625bfb96200,-0x1e12f9f00c72faa74c0095dfd56cc4c9640,-0x6920e5949ba2e8832d0ec7a8f82dcbf2c0,-0x115b0a4a6a7946a5d903076e8e5c78d8e0,-0x235a56af572528f9ba4b132689f16a3f0,-0x38264bc4cb223cf5f71af6da4fd4d6e4,-0x45ccb90a2bdb56e48f104d3c7397d74,-0x43b7f193ffe6054c38c6d02126efa4,-0x32c2c88639942354cfea94bccc8e7,-0x1cd58083952a36afd1d051353978,-0xc0140308e35e473f65149900ee,-0x374f153707d2e2a3ac8c0933c,-0x9d8cd15e221e756263c03e7,-0xd12b674e9bffb7b17c584]
def m21 : List ℤ := raw_ints% [0x0,-0xdc1f738571b13c238a3f68ad8df874c36ef58500,0xf8cab33911e43b7ac1d2267d72e10ba42a4a569c0,-0x858ea598c1ad4776c8b8d83c8d7d0e625ad209f740,0x2d4b57e702c70efa6a236c59fd4694fa9db0f463a70,-0xae3733619c151624f28f613b0fa40a0e534ab733590,0x1f92e4ce460a0a4d71917ee89e8f63812492318e12b0,-0x47abf2f9a1bb0b0102cc70654769db78749f335caf50,0x8289b0fed7fd4544bb06d96273be4302b862304ff7dc,-0xc1fadb1d8d74bc7f2e3156a4d327a955750776194ee4,0xede248caf1fc3bb1256ca4d65997d4cbfafcea5e9e7c,-0xf293ec27298070dfb1b329110dea9bb4c5e939396fc4,0xcea3993c4e178891bbad95392a9cb0cb5a245420117c,-0x935be1620339d6eef3dcd31b1462bde10dd43f4cd444,0x57f7bd8012cfe4218904be5b7f96f65b8651eb27ddfc,-0x2bde04cf5fdc59a5562ef28ed515f5f77d58ec7ff944,0x1232a41cf69a64c317c32bf641aa2b57e428c7f00f47,-0x63d816de56e77bfa96e2580cac8f49aea024a683e29,0x1c0ddaf4e33b58317a4453d9c10045065148acf475f,-0x6626adffb7905189f5b3838013ca880a7d629f90f1,0x128c639e31680803ecc3710f4ec7e878b91211d4c3,-0x2a2d56b64ba60cf16bd7b9ce4c1017e80ee8d0ead,0x493cf37d5a02fb68a056a2b6e155c66d5de24c4b,-0x5e14cf4ec86274af660829ac9d93d0259a7f685,0x55c96dbebbcdf050f313d39af96ae23ba9f3f9,-0x3491acea70b16cdeb1993015c6f86b5b48217,0x141b09da0efeae09f122c227c83451fc0381,-0x4548ad9071c91351a67477ddcf423ff5af,0x73d58e5db3d712c59530be59be5cd7f5,-0x4aa7689ce85833cd95b45e5d9c1f9b,0xc79bd764e521afc5038ffbd3c2d,-0x3a2c7d9ef2a13dcb08276703]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 17 66 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 66 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 37 indices rho q21 m21 21 754727630060371968000 21=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 37 indices rho q21 m21 21 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [-0xd12b674e9bffb7b17c584,0x73cf09af769057130b54,-0x3e52d48e59b9b45c898,0x207b7d6ee7b0a463a4,-0x10531128e4c920f29,0x7de95ad8b541625,-0x39d938cc84b29f,0x1920c7be84fff,-0xa370bc53362,0x3d5c17155a,-0x14e599cda,0x64bb15e,-0x19dc6f,0x5533,-0xc9,0x1]
def r22 : List ℤ := raw_ints% [0x182378d124b2bfffb4ac84dc0da156bb60000,0x24dea8bff6f432765ba33f5b1c3c8c9ee2000,0x1a0fc080d8e6d3fc4728b51c34049174c4c00,0xb52589f03f8ec5f9f8ba5b757cdd86714600,0x3628389ce013ef54db04079b2930266a1b40,0xbd220f19c2b767336d8678693ffd133c800,0x1f30d965f2d6fc74df4c6e3138089d56360,0x3f75c9ef83ac4f73d10400d2c252a758e0,0x64a8e8643e41d80aae1ff6a9cc8c0f0c4,0x7cf2fcd428ab8f3fa4d9b7d72eb45ee0,0x7907360588a581c218edc77afa3633c,0x5a8eceba404414b3569b8b021bb58c,0x33562b729e487fb513817ade797d1,0x1553532b12bde6cbcdcfa3124620,0x6200488864a0a379f66f10e6a2,0x1165bd05af2e943a28e8b3ab4,0x1705a6d0ba8d4c31d497f0d]
def m22 : List ℤ := raw_ints% [0x0,0x120e9479f25389eeea5733963ca56194081a23e900,-0x143ac2fef46aa40907e7dd764cf875f47778191acc0,0xac22e785e65570919964e976a7a24a6350e82d44840,-0x39ccc42cdfc688aed2d2aeec9078e43847aaa6ef0b30,0xdbf8a58cc31bc73df5522480f42a8c377507000724d0,-0x276aec11530de8c6f12310040c58b441f0806889b5870,0x58667e68400c09f06290727989307ea053d7ef5974190,-0x9eee1fd6b431b2bb79f9a39dc973f611dc1e07e76b90c,0xe8e656806777bcb5fd049c4e39e843bfa1f26d9c714b4,-0x1195a3d7d6e7044003b4a0139b84c2a3179dc712dc392c,0x11a489bffd59439e4bc7530cca629d0b7783d422194214,-0xec44eb63e9fbc50ffdeb5c16754851a6afdf57e65ef2c,0xa54c48d69ff0dc72b8b379aa62108e0f772ca08c8c994,-0x60a3fecc03269aa41895da1afadd3f60dca34420152ec,0x2f1ae351af5c95401e86cc9f787b0ddbf04d018e3b954,-0x130ea78f5534d72bef088e9365687ce1b56578bc41bd3,0x65b549978235e57413a8e9c6d96fe75201ab325c965d,-0x1bb740e0aae34ad3d56d16f95204633da4aee6dbd8cb,0x61897c847a13dca839ad65572ddb0af1fa4a991adc5,-0x110c4e734902be0ad30df5d18761df43ce5acb04eff,0x25239f4ef74ca83d3923d8bab307f8556fa471d131,-0x3d70c96fe4a7824a6da2df2d330eb2159eb814ea7,0x4ab304080cf068592a963640305b85a76db68c69,-0x3ff64c24e00a9cf102d4d2cc16ece1fdbeca86d,0x2476dfa16f1b7e2981039947859c8b7a8e0ee3,-0xcd4ca83582db33c499b47b87523f8e99d495,0x2825a442d3af57bb49ff39c27362fdbc45b,-0x3bfdbc9f07ff934743c2f8e2afbc05819,0x21e86df99557559acf14224011a3eb7,-0x4da9d7d31c5b996520cd420013f1,0x12c973c289a3a1fd27c309aff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 17 68 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 68 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 37 indices rho q22 m22 22 754727630060371968000 21=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 37 indices rho q22 m22 22 754727630060371968000 21 15
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_22
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<23) : intPolyRF (mz e)=rfPoly (C (754727630060371968000:ℚ))*rfX^21*(1-rfX)^15*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V5C22
