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
namespace CatalanCore.Li2.NVMod.FamilySource.U4C18
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,4,18,size⟩
def bases : List ℕ := [1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18]
def num : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0xf29f331a2000,0x1568705e2de00,0xdd7e1e2c7ac0,0x56fce4308770,0x17307d8f6c90,0x470cbce9098,0xa15136bb94,0x113d3f1f6f,0x165068d3b,0x15c404bb,0xfc114f,0x8352d,0x2e91,0xa1,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x7,-0x23,0xbd,-0x4d,0x5ac,-0xa5e7,0x18f65,-0x22f27,0x93e,-0x4e8f,0xfce]
def rhoDenominators : List ℤ := raw_ints% [0x20fdf0,0x15a8,0x58,0x1b,0xc,0xa,0x1,0x7,0x70,0xd8,0x168,0xb,0x129,0x1ad]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 19
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤18))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤18 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 19 omega5=padCoefficients 19 (omegaCoefficients 18 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 18 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 19 omega6=padCoefficients 19 (omegaCoefficients 18 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 18 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 19 omega7=padCoefficients 19 (omegaCoefficients 18 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 18 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 19 omega8=padCoefficients 19 (omegaCoefficients 18 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 18 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 19 omega9=padCoefficients 19 (omegaCoefficients 18 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 18 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 19 omega10=padCoefficients 19 (omegaCoefficients 18 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 18 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 19 omega11=padCoefficients 19 (omegaCoefficients 18 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 18 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 19 omega12=padCoefficients 19 (omegaCoefficients 18 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 18 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 19 omega13=padCoefficients 19 (omegaCoefficients 18 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 18 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 19 omega14=padCoefficients 19 (omegaCoefficients 18 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 18 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 19 omega15=padCoefficients 19 (omegaCoefficients 18 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 18 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 19 omega16=padCoefficients 19 (omegaCoefficients 18 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 18 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 19 omega17=padCoefficients 19 (omegaCoefficients 18 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 18 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 19 omega18=padCoefficients 19 (omegaCoefficients 18 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 18 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x42,-0xdc,0x1ef,-0x318,0x39c,-0x318,0x1ef,-0xdc,0x42,-0xc,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 14 li0=padCoefficients 14 (liCoefficients 13 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 13 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x37,-0xa5,0x14a,-0x1ce,0x1ce,-0x14a,0xa5,-0x37,0xb,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 14 li1=padCoefficients 14 (liCoefficients 13 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 13 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x23,-0x4b,0x5a,-0x2a,-0x2a,0x5a,-0x4b,0x23,-0x9,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 14 li2=padCoefficients 14 (liCoefficients 13 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 13 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x5,0x1,0x33,-0xae,0x126,-0x126,0xae,-0x33,-0x1,0x5,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 14 li3=padCoefficients 14 (liCoefficients 13 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 13 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x3,-0x31,0xa5,-0xf6,0x7e,0x7e,-0xf6,0xa5,-0x31,0x3,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 14 li4=padCoefficients 14 (liCoefficients 13 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 13 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x13,-0x5f,0x4b,0x14a,-0x372,0x372,-0x14a,-0x4b,0x5f,-0x13,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 14 li5=padCoefficients 14 (liCoefficients 13 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 13 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x33,-0x19,-0x2a3,0x672,-0x3ea,-0x3ea,0x672,-0x2a3,-0x19,0x33,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 14 li6=padCoefficients 14 (liCoefficients 13 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 13 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x73,0x259,-0x92d,-0xae,0x1b66,-0x1b66,0xae,0x92d,-0x259,-0x73,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 14 li7=padCoefficients 14 (liCoefficients 13 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 13 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf3,0xcef,-0x4b,-0x5646,0x48ae,0x48ae,-0x5646,-0x4b,0xcef,0xf3,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 14 li8=padCoefficients 14 (liCoefficients 13 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 13 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f3,0x3331,0xb35b,-0xfea6,-0x1fcc2,0x1fcc2,0xfea6,-0xb35b,-0x3331,-0x1f3,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 14 li9=padCoefficients 14 (liCoefficients 13 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 13 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f3,0xb2f7,0x5804d,0x6d542,-0xd0c7a,-0xd0c7a,0x6d542,0x5804d,0xb2f7,0x3f3,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 14 li10=padCoefficients 14 (liCoefficients 13 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 13 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f3,0x24c49,0x1f4b23,0x72f822,0x5b5756,-0x5b5756,-0x72f822,-0x1f4b23,-0x24c49,-0x7f3,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 14 li11=padCoefficients 14 (liCoefficients 13 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 13 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff3,0x74c3f,0x9b73a5,0x3f3f08a,0x9afbd9e,0x9afbd9e,0x3f3f08a,0x9b73a5,0x74c3f,0xff3,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 14 li12=padCoefficients 14 (liCoefficients 13 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 13 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 13 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^13 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 18 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 19 at hb
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
theorem cache_li (j : ℕ) (hj : j<13) : coefficientsPoly (cache.li j)=liNumerator 13 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x19edda8a27af7349000,-0x204c2b03255a9ef25400,0x132a05b22c571d5178a00,-0x734b3a1a8b6b1aecce200,0x1ed3c2af9891b62c5df040,-0x63c12558b3a220dfaadb80,0xfd8e1a5ca11bf722c68ed0,-0x206eb6aa228ef6ccda1ca40,0x36592a75d61884765b9d6d8,-0x4b6db9c8038d4383c229568,0x575ba140daae8d30a652bfc,-0x54ce35eed346980d6c000c8,0x452311f2d115fda30a09426,-0x2f4ed70f086ba044212903a,0x1b178d325dca7a40aa44bb8,-0xcea1d85f2a946db4b50214,0x514fc42b381335533d298a,-0x1a1a05eed6c9f6d15bb45e,0x6b927932c987473c7b9ac,-0x15bb042cee05d9e8b4e80,0x3555a65fc0dfe60fddfa,-0x5ed57bb74f075c2a066,0x719e0f858d33571dd0,-0x512eb9d0082c90f04,0x1b454e6144aef35e,-0x25196a6c61f3ea,0x123ac8b1390,-0x74ab6ad4a0,0x1fd1a8c5a0,-0x54d9c20f0,0x686e78b0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 14 26 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 26 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 32 indices rho q0 m0 0 811444512974135040000 18=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 32 indices rho q0 m0 0 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x1d2b95db6ca561b22000,0x239b8655b92a45df5c000,-0x14b101d86b94324413d600,0x79d22cfeebea87f12d0b00,-0x1fd9e8377ef23f2f76246c0,0x64b35f66ba3bb78b5f2d5c0,-0xf9d9b60a033e14cec7fb830,0x1f2a12a4c34d5454425c9710,-0x32de7978d508b171764cd068,0x44af66e3a378e62bc3553ce8,-0x4d492ab843b62d811aaebb04,0x48c8a733fd0c2a6420415dbc,-0x3976c162a449feafac02cb6a,0x260196101eb589ebbcc610aa,-0x14fdc014a7ee84412e04c1c8,0x9a03b69e04fdd24bfc22780,-0x3a20bbd9a4dd6943c7d2906,0x11d54133c20967d45a2db46,-0x45f03a11474b182e2467c4,0xd5f8f8dea76d456d4d2ec,-0x1edc38f6b6f46b65f3056,0x3322c823d56a9f80dcd6,-0x38663d6771f5b306f00,0x247097b415c5a61588,-0xac14b01f52532252,0xc384c119ffb4d2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 14 27 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 27 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 32 indices rho q1 m1 1 811444512974135040000 18=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 32 indices rho q1 m1 1 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x20d10896da3a0de864000,-0x27492a71c26626daf0d800,0x165f97eb4291f8f7fe62e00,-0x81005d49a93e542c3b83b00,0x2101659c161fd2ceeac51440,-0x66066f834f6f66620995b9c0,0xf743efeb5a1e3a6de8527d10,-0x1e1880165182c9635c81aaa90,0x2fe1d486f0a6487638145e128,-0x3ef0360cfd94f0479169712c8,0x44d8b63a8afa668411f0b261c,-0x3eeea8965245bad1444d8b91c,0x302488571bf536f28725935ba,-0x1eca7f9f1f093166ee0926a42,0x106868b2293051ffb734389d0,-0x73d80df6184772d9e4a4def0,0x29f11f0a0daf3547ec4b7926,-0xc4c4eecf7ccc8c749d628ce,0x2de44225dd1775448a934ec,-0x84daac43d6278a8fd3ad6c,0x1200e00bc05bb349e1e026,-0x1bc5615d75c8a3bd4347e,0x1c26ed9c0b0c9d9db2d8,-0x1068d4c838975c81bb8,0x43e2e2d6adcc4d8d2,-0x4053cbf94642d2a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 14 28 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 28 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 32 indices rho q2 m2 2 811444512974135040000 18=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 32 indices rho q2 m2 2 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x24eb29a9b5814fa5708000,0x2b60264661eaed79f2e0800,-0x183a26cec146189791f07e00,0x88e67ea8160175a9fba19500,-0x224cae5f01fd9ff012a0152c0,0x67bc136cc9e5bf3e335a2cf40,-0xf5be3ad5c0f91024050e0e2b0,0x1d34b6a64ada11f7d1f1c52970,-0x2d51e5454c3229805ba5b4ef88,0x3a06cba856858d78362ca6a268,-0x3dbdb3b9b95a441aec39244144,0x36cf325656fb81d480b1b58c54,-0x28a578353217a2b24c6fb616b2,0x19266316fe20973114ccc1080a,-0xcef5c465afcbcf7b634ae8338,0x57e73b4814cc93113edb45828,-0x1e8909e8ba1e6d9b07845171e,0x88ebdc5ebfd4b32d19056656,-0x1e614124386bcb6a2172b3a4,0x53301b78f729bd7e71bec54,-0xa95b0352c04d1edb3f8fce,0xf2ece1b9e93b3ddd5fd96,-0xe1f92c78f93209d8d5f0,0x768fa29619b9e78d780,-0x1ac8704acf7cb4b15a,0x15231343598c93a2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 14 29 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 29 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 32 indices rho q3 m3 3 811444512974135040000 18=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 32 indices rho q3 m3 3 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x29888edeec31799a1e90000,-0x2fecdefdfbd3cd090f68e800,0x1a458ffde174c6419659e3e00,-0x9197319c38f305a985e2d4f00,0x23be8ca55c5d8d2da0ea3f6c40,-0x69d702ec3de827fa8c03cc6ac0,0xf53dbf87533762d3709bc2e510,-0x1c7a59d1a622f3e2716ae1736d0,0x2b205c31c4668748be89d1f69a8,-0x35d193f087d0eea42ba99936b88,0x37bb4c6f1715712ff15779fc59c,-0x30128f689e4089f2e929a1fdf6c,0x22938071393cbd8829419b5f41a,-0x14b4b06884ad7b28fdcb5322932,0xa48258c97448fe3d53f567fc10,-0x434594bb0156ffcd206dd1b740,0x166c89be9a69b5626f38af50c6,-0x601a7a8e28113c416b06ef83e,0x1448375ae10b0b3316a85e5ec,-0x34826ad868ff6d82000d19dc,0x644ce20475552a46e08f5c6,-0x85a303f0e98dce1470f3ce,0x71e2b49c1a85ad95dfc18,-0x35aa530c9e3dfb602068,0xa90ad1c404123a08b2,-0x6efd271b77beb5ba]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 14 30 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 30 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 32 indices rho q4 m4 4 811444512974135040000 18=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 32 indices rho q4 m4 4 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0xf29f331a2000,-0x1568705e2de00,-0xdd7e1e2c7ac0,-0x56fce4308770,-0x17307d8f6c90,-0x470cbce9098,-0xa15136b954,-0x113d3f160f,-0x165067ce7,-0x15c3f52f,-0xfc086e,-0x8320d,-0x2de7,-0x8d]
def m5 : List ℤ := raw_ints% [0x0,-0x2eb9a0bac9b7a8cd62620000,0x34fd3a0b75d480a80d6522800,-0x1c8747490a679458c1a12bde00,0x9b273ce36401c56d9125309d00,-0x255a2960a7140f3ffbe4fc62ac0,0x6c5af2d89bcdd3a8ba16d44d940,-0xf5bb041c2cb66277373ba65cfb0,0x1be5d524cd353ccd7f2e9a15a9f0,-0x294163c5b4c4b0ddcf5dc649de48,0x32352e1653dac5a8dbdf4fc4e9a8,-0x32a0e30de80f4b251c3154fe9944,0x2a744025f8ee0f4bbb1f0cb06db4,-0x1da0ddcbde755455584b106a2fa2,0x112dc3d2b74d3539e558b917e31a,-0x83d16d4b5513922f87d88f61f58,0x33e89cb67f3fd60ca644cfbba28,-0x109afb67daf98eb2f0c976f57ee,0x4404656eec27d9284460d091c6,-0xda6994ee90f31e258dff66e64,0x216635d76f37a4adaf9049534,-0x3bd0463d7b2aca09cb923a5e,0x49f07a267cd221f7cddb086,-0x39a1eead6a42dcac6f2810,0x1856c822c9a95b85c58c0,-0x42a997a79797f93184a,0x2461d4f6c3ce772f2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 14 32 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 32 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 32 indices rho q5 m5 5 811444512974135040000 18=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 32 indices rho q5 m5 5 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x8d,0x1]
def r6 : List ℤ := raw_ints% [0x85a1af2563a000,0xbbb5bf0ada2600,0x78a7ef989cbdc0,0x2f0bcb908e1df0,0xc6eb843ce43e0,0x25aefc3363728,0x5468ef56bfec,0x8dd6a8d96cf,0xb3675cb370,0xa97f01e18,0x75119354,0x389415b,0x1173d0,0x2ac6]
def m6 : List ℤ := raw_ints% [0x0,0x3490d4d222ee9de70eae40000,-0x3aa0cc6d7abdae5ac8e1d62800,0x1f0564831f82eb9637071d93e00,-0xa5adcddffd42e46b7d34408bf00,0x272315a38fe6e5c7f3e083bb8440,-0x6f4c9bd44d14efdf109b3d26d2c0,0xf731a7b7bfcdc85296278285f810,-0x1b743f596f1f11c34a190f652f6d0,0x27ab303be811deeedf4eff4d6f8e8,-0x2f1b30a1ae2fdfeb45e25a2ff06c8,0x2e4769d0bc4882231050f08f0059c,-0x25be6fa7be183f1e09952c93278ac,0x1991e6b5ce5739d3e254b4b13fb2a,-0xe5c0e95dc092c9f3529141f05342,0x6a72b49dd089405f22fad83fb0f0,-0x285ff88d6b7f1adeb3b3fe653760,0xc656bcce0ccc79246d3f40f8ef6,-0x30869f7fe4e9b41bf7b5be47f6e,0x94255e8962deb73db089898d2c,-0x15662723b3220dce6c395308dc,0x23e6cca6b809a88e715351136,-0x2920aa4c5be7d952b0dd2e3e,0x1d45e631d5c767e8d100ef8,-0xb0e746a96db4b82e4da08,0x1a46fc310d2161363ec2,-0xbe9ad9a2e365494ca]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 14 34 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 34 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 32 indices rho q6 m6 6 811444512974135040000 18=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 32 indices rho q6 m6 6 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x2ac6,-0x8d,0x1]
def r7 : List ℤ := raw_ints% [-0x2889c583cf74c000,-0x38b571b6a0801400,-0x24464abf97b04a80,-0xe101d18db2462e0,-0x3b0d84f142f7970,-0xb181f541ae81b0,-0x18992807e52550,-0x28cf8caa3c5ee,-0x32c9cbaf52d3,-0x2ef9705a332,-0x1f85dc3b02,-0xea00ef7a,-0x43e8ccb,-0x972b6]
def m7 : List ℤ := raw_ints% [0x0,-0x3b22ef6c674c71a3f084080000,0x40e90fcdc9a6eb9db76b213a800,-0x21c6b75a56bc8014f61aea441e00,0xb144c0e2ac11f7051a64c9461d00,-0x291d5541850a921f28b68310432c0,0x72b1c4bc3a8d5e67d73c31989a540,-0xf9a02fa2b2d1bcf61c1f152cf2eb0,0x1b23430d7179f90e89ec938b55a2f0,-0x2655a5dbe7616d8069ce8506c1bd88,0x2c713231885dcda19fd3773f57e9e8,-0x2a8f5845cbf4503dc72a101aaff444,0x21c68e76e3d25369c1082b24b59c34,-0x163885567c51696af9817669d5a5b2,0xc173a62e13e66d2a904478fd5776a,-0x569cbc935e35e0624c8489e0d6538,0x1fa5c090f20a3abbd079c1fab1688,-0x9538693e4a128d6c7400d430471e,0x22e33b01d99685065da789c63636,-0x653bd59e8a9789d7bb9b6669aa4,0xdce31a5f49709b8ba799d583f4,-0x15ae39db0c9edb7b64fa18dece,0x16fd26d834b16b6f6972e95b6,-0xeead9fd00f789cb81675df0,0x50778f3769a9cfbe07a820,-0xa5a421da45925a52855a,0x3e5831dc68cf44c6c2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 14 36 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 36 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 32 indices rho q7 m7 7 811444512974135040000 18=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 32 indices rho q7 m7 7 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x972b6,0x2ac6,-0x8d,0x1]
def r8 : List ℤ := raw_ints% [0x8f4502ddb16d2c000,0xc7bb1141334b11400,0x7f3f93ef2f288b080,0x31198305d020fdf20,0xcd086155183aeb80,0x2643b4e6e26702a0,0x542a1d172f6c188,0x8a4797b9e1a19a,0xaa03ce9fbe804,0x9adb225a501f,0x65df7aad8f8,0x2e063c9cfc,0xcdf5bd9c,0x1b297ab]
def m8 : List ℤ := raw_ints% [0x0,0x42874d59f435ffd86e948900000,-0x47e99e374c6669007d1c66b42800,0x24d2dda1b24fc6a2c1c25f1a3fe00,-0xbe08f24a793ed4afb4758c4ec9f00,0x2b4d6adc996dca9678e575d5519c40,-0x769150d11af37ebb2aa671bf9436c0,0xfd07e3b5c6fd1066895d70908e9f10,-0x1af10c0e1018632a2e35231cb9e9dd0,0x253a11124c65436009f754853842528,-0x2a2806e1f2f4dac2a34eb5e6ea3b608,0x275f1927b19ac498258e4daf7abf39c,-0x1e6ac4588414e438642e6fcb2219dac,0x1370e4e2b2b870b617b1453b650677a,-0xa40adfac25f04839426cc7709ffe52,0x46fdbb6af0fd78ad7a27083aec5f50,-0x18fe3328e50c0e52db8f98d029d1c0,0x711d16a632ccd0a57ae7c08a186e6,-0x1944d2bb7569f931d263f8f116f1e,0x45ab69d01550b28d926ac1e5736c,-0x8f70bef6b2ab97eefd7d4af241c,0xd2ae5277beb1c032c34cb52566,-0xce86b164cb42988125b491cae,0x79fb844a1c68d80dbdb62f58,-0x24a3a1b56884dec87134268,0x4137eb3253731a44f7812,-0x145f15f8673f7432e5a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 14 38 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 38 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 32 indices rho q8 m8 8 811444512974135040000 18=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 32 indices rho q8 m8 8 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r9 : List ℤ := raw_ints% [-0x19be1a299c5cb536000,-0x23c87863d6b04a98a00,-0x16b87576a5f48ec2a40,-0x8bb84ae0d7b5a4d750,-0x244c59c43c81e69510,-0x6bcd2a26b03b95208,-0xeb978c8ba6b4953c,-0x180169d5fbebb69d,-0x1d3d1090cd281cf,-0x1a52f843c38de5,-0x1110f8c28d8a6,-0x7910b783717,-0x21072c04df,-0x435ba4ef]
def m9 : List ℤ := raw_ints% [0x0,-0x4ad8370532bcbfd37c671a200000,0x4fb87534fc16800e8c7012f22a800,-0x28325c588a9f1d796edb0403ffde00,0xcc1a99923535b59efc90c2f06f7d00,-0x2db8658a32f35622b96679d3125fac0,0x7af351b50a3a31f2e9357341d3e5940,-0x1016cb86846a258643165100981bddb0,0x1adc38690c80c6e0d439b3c64de685f0,-0x2452ecadd894cefa5e170392b82308c8,0x28332674773b20a21dca4be51637b028,-0x24a1d2f51c7f41cf42f2d82df4639744,0x1b9000e6278e933b4a49931bf34b3334,-0x111efc5c39fa97b59bc7cc2ef242f4c2,0x8c109eb7d299e85ade8cc737a0d333a,-0x3a9a630649cd383194cac5844bf9d18,0x13e1a33e6533c577973373c0a562768,-0x565e6bbf93327614b4caa83ea0254e,0x126ecf04ab931a594ffdf6fe157a26,-0x3045fec8b441977a0b3fb7660eae4,0x5dba51f0cfbcdac5e9c2d0215034,-0x80a3d9fd5c576c2c836677d1a3e,0x747072d2ab0343da4ad619bd66,-0x3e804b9ae61e6026e52db45d0,0x10b22c1c29e008b271caf300,-0x19a9549811f9343f8a876a,0x6a667c196a74b162312]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 14 40 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 40 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 32 indices rho q9 m9 9 811444512974135040000 18=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 32 indices rho q9 m9 9 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r10 : List ℤ := raw_ints% [0x3fd685478006d1e3e000,0x5884139525ccf3b1e200,0x380ac4e7b49787c00f40,0x1577cc519e9b4bf60750,0x58e45bf0142abfdc320,0x106cff225e7469bc8d8,0x23b52e7dc348269d24,0x39d9bd97330d1df65,0x45ef1c7a2ca4ef78,0x3e646e777aeb4c6,0x27ffcbf6bc36dc,0x117cb6b90a05d,0x4af93132648,0x95576b570]
def m10 : List ℤ := raw_ints% [0x0,0x54333de5d91457cdebf3fd6400000,-0x586e4145ce1ece9d3da936ae652800,0x2beebbc73856a1198c12c31b5f5be00,-0xdb9daf840f38dcf5d7cf27c80ca3f00,0x3063f03c83c512a0efe5e7a10ae4b440,-0x7fe11d681e684b66f328ff6a7eb06ac0,0x106d54541cb983be2b760327732977e10,-0x1ae3cca116c17c519e273e9d17b4f28d0,0x239bb36931ffca425ba68de68142b4768,-0x268832305919f116b0b05968c8f176f48,0x22467585d216b5fc9d741220d161c459c,-0x1920821e836e0499676453ebb165d8dac,0xf2cb9f6853b4d24effdba9d550c8fb4a,-0x78654f0d1564ae7ae3d98c8ad8201de2,0x30b6602aa2d844da5aa64afb2732a2b0,-0xfed43bb15df2f826898115445ca1c20,0x42697e1e188731a8ec309fc3c19b556,-0xd89e1c56ac489f594007876ea5f64e,0x21aa6eb5cdd9f9bb58debc307bbbac,-0x3d9ae9d4e851726a965ce55a4e65c,0x4ef03b44607b062ba6ad603b2e16,-0x41e520c6c228fbc518d9f7bb69e,0x201867410b565f8f0f23622cb8,-0x79cc70a39917f4603a0894c8,0xa16fbf64cca1165867f8e2,-0x22b36db40f012a32866a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 14 42 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 42 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 32 indices rho q10 m10 10 811444512974135040000 18=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 32 indices rho q10 m10 10 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r11 : List ℤ := raw_ints% [-0x8d89829390f72940e0000,-0xc3d4259a6aa7d7c534000,-0x7badc911ceab8070d9200,-0x2f3e38ec935a93add61c0,-0xc2fa78331f99e4eb47b0,-0x23e467534cc0a8acf760,-0x4dae5bf62ce8e2debe8,-0x7d335e05847cda9e6c,-0x966cfd8935418a16b,-0x85393b7235a75958,-0x54a7b81643fb8ca,-0x249c3f4e31ddd4,-0x9ad951464413,-0x12f2c94f528]
def m11 : List ℤ := raw_ints% [0x0,-0x5eb9a5a29436e2c7a9727d10800000,0x6226b2af5d907ee6930430f8067a800,-0x3012a712c5c93b3b31153fff18c19e00,0xecba60f32f67faa31747552178245d00,-0x33566324f6d98e2a698f5ce2cfd45c2c0,0x8565687f55c4279329c18dca90feb0d40,-0x10d4ac6c8623b3d7cb4c37f516cae114b0,0x1b072a84f4f5608464382bbf39251078f0,-0x2310ba89146fbf8f4dea9cb3f4044dde08,0x251e9392b7062f1c6ec908f430de0b8068,-0x203efc5dea31a7d79aa58d9dd2dcc03644,0x170ab32597a17520538d5a8fe1f894c834,-0xd88a3d5a56ace820b170e0044181de852,0x682a59788ab95b7e16d0bb0f64ecf638a,-0x28c39335acaf32da70fab7fb8514a8ff8,0xcd897bff5adb4eb61d2e0caa56f60548,-0x3369fbe5c6fc8a7e0e62fb0009a248fe,0xa0271d6ac8d9be2d4e85e8448700396,-0x179fc9c201b368756c59d0061253924,0x28b794633c918b5468baaf24f8c074,-0x30aa1d5b6e05ee32ec66c3d6f652e,0x256b196bf381e4fcc290adfc5496,-0x108357412276b1da601d92e80b0,0x378dcb55dea5d8235f66e4ee0,-0x3f6d803c939ec7d33c375fa,0xb4e9e37a64ae35473be2]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 14 44 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 44 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 32 indices rho q11 m11 11 811444512974135040000 18=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 32 indices rho q11 m11 11 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r12 : List ℤ := raw_ints% [0x11f54ae05162d627cb50000,0x18cccde5162d598cddab000,0xfa1195eb340427c319ae00,0x5f499b990d44139ee5c780,0x18828ae1ca8e1829b164c0,0x47f4cb9c7fd405b9cc810,0x9b26d0478f3b4af4fbc0,0xf8f988595c6acf03870,0x1299d9001475b70e9cc,0x105ffc1bbc8b2b12cd,0xa54b26b3c3f7f600,0x46de2abf1f0a73e,0x12897bb63a2dd4,0x23d1b867ea15]
def m12 : List ℤ := raw_ints% [0x0,0x6a90da56e6bdbf209ea0ccb29000000,-0x6d00dcda2c4b42a06de4e7c219422800,0x34aa0fb5bf8e910f671e0ec74e2bb7e00,-0xff9d8f86e40d41fdafdcd8596558adf00,0x3696d74a948286dd2a4cd9472f9928cc40,-0x8b8c64e22ad1f04f72c0711e1d788cbec0,0x114d92b50c814bcb07bf4263f2a2da86510,-0x1b460a4460acecb31392cc5f9cf587f8bd0,0x22af13d241047d79b3e3ac367770d11d3a8,-0x23ef2e8181596cff37128701d1ce4669a88,0x1e7fd98c3cbe0ec141f7e3fd5294aedb39c,-0x15404d562aa15719bf866e723affc4895ac,0xc24cf190ecf409d1f9f7e5c9a9588a939a,-0x5ab25da7b6308e8aa4f9b9f3eada2073f2,0x2255fef23a1c63b4cc40efc6ddddb6e110,-0xa6e0db3f098ab99c6d4482c5d64a55580,0x281083385e7fd097e420af1b3fc452946,-0x7728734be1f861d4d3779c8ed33b0cfe,0x10ad080b5f265c91292eec1229c2e1ec,-0x1b0d8881258978a8abd2fb7aec07a9c,0x1e21608854d6aee7b0ab1a14de6646,-0x15503d8d437a596b764685d3a060e,0x8828870ddfcbf2d9e2b0fb0bd18,-0x19581a1c299e5d5ffa7772c628,0x18e6c72162c313c476c00632,-0x3ae63d9f2108d6c2e40fa]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 14 46 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 46 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 32 indices rho q12 m12 12 811444512974135040000 18=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 32 indices rho q12 m12 12 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r13 : List ℤ := raw_ints% [-0x21f286ba3355e247f264a000,-0x2ecdbc17e33d02e9afd33600,-0x1d70e4c4f3ab3033b73ee1c0,-0xb31c4bc163bda7a4ebdce30,-0x2df56d9c8d7e1f7f509c050,-0x868c9b9f8c3594cb9367b8,-0x1212f54366e7e32de1e314,-0x1ce583c920dc6db9d0e5b,-0x2264c85069fed46e4b67,-0x1e203cb258ee933678b,-0x12e4e16584b01d8eae,-0x80b353967a6a88b1,-0x21616402cfab4a7,-0x3fd6943200961]
def m13 : List ℤ := raw_ints% [0x0,-0x77e2f5a1c3957704b274e648e2000000,0x791fa187a30dea0f54a9b8701f824a800,-0x39c25559f2db4093661459d50f68335e00,0x11479625424471858e098827404e14b3d00,-0x3a2d3c970ecd558c3d179698544f6ac8ac0,0x9263e56ca8e434822dd70fd7ee747d92140,-0x11d8f2a59be1dc4c58facc6c123efa5af3b0,0x1ba07573a5e61e7e8b8efe5ff7725832d3f0,-0x2274757a45d8cd758bbd0010cbcfd8bc4548,0x22f422eb1409c89bba82675e8710b3d23aa8,-0x1cff7fde42d0747a2eae6dd798747fb98144,0x13b5ab7dbe8efda72d3c510d86c540e0b134,-0xaf616c467fa129c4ad69a7fd46ed311a262,0x4f757d4ce3546f770677046e69b6d51c05a,-0x1d1b0ad93f4354927b553be1a6acc1599d8,0x885c7d665afcd697027d449acad14eaa28,-0x1f6b21a35cce460f8d96e292633aec882e,0x5932860ab57daece1cd87d578765b3686,-0xbd67299f737ac5e8aefb3ad70c955d64,0x12102e5529049a56aeaa467cff57beb4,-0x12bac3651d09987deb599a2b4bbcd9e,0xc2c7ca12859da4de006f730946b46,-0x4643fde2a5bdead331c5d5214a90,0xb902273013d9454cf9ba8f69c0,-0x9c4c6897d4d7feb75ef2030a,0x1328f0b13eccd15582e532]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 14 48 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 48 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 32 indices rho q13 m13 13 811444512974135040000 18=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 32 indices rho q13 m13 13 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r14 : List ℤ := raw_ints% [0x3c808b1b92e80e0c248062000,0x534b2d2f13a14d08c025f7e00,0x344ed550d9c57db5ee7580cc0,0x13da179d942eb2017b1e75fb0,0x515429010557b5b6916b6460,0xed8596ab929d3f162506148,0x1fd16a0467561091541df5c,0x32b566210a7e713a03ecfb,0x3c225b1ff9348bf358800,0x3472f1a85c3dd7621274,0x20bb4e21eeb29caee64,0xdda9309e2097d2c5f,0x39181f184c6a3540,0x6c48f30a2b315a]
def m14 : List ℤ := raw_ints% [0x0,0x86df5455fc0825e548c38311fe4000000,-0x86aa295bebbc7a5dc5d7a66f42bbef2800,0x3f6a729e54851fec7b3896d7d643ae93e00,-0x12b85e8397cc81ff848156ce640c6ee37f00,0x3e2272a5b9e3432f5812c0bc769570ede440,-0x99fb86e65905734814eff64d7cc0f43572c0,0x1277e66578bbc8a3fcda55631079ddc28d410,-0x1c16c3c0f966631e0eab9e0bddc241773d6d0,0x225f2700ef8f3d80948abdaedf69bfdf869e8,-0x22289aa87887467b1c5708a6a19c4889d67c8,0x1bb6056c1e4db085aabf3ccd2565861937d9c,-0x12614342b92d138da4c323925bcced9f509ac,0x9f382389bed6fa24bea7c63325c9a26ca86a,-0x46089d9cc96537c7dcecdb680fc1c3527c82,0x18d322bf11a6b28e97d823642d9f58e0ca70,-0x701e720d939a4e7f9f2072ad1ab8f0891e0,0x18ca0de49e9211c252cbe6b37ed7db84ab6,-0x43292bb4d2110ece3d59cf226824bfef2e,0x872c7efcb8c5e80f4ca4eeda02fed062c,-0xc1df388e3fc8653b79602f968a40fcdc,0xbaf7e65877dbe6722f25704dc9c55f6,-0x6f87dcc435ab1541b4e9ddc7f89efe,0x244d977d018b01280346d8fec5078,-0x54677c6618ba2086e24c8b84288,0x3d4459b8181fe60069efa9802,-0x63a50d9b864fe554e6a20a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 14 50 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 50 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 32 indices rho q14 m14 14 811444512974135040000 18=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 32 indices rho q14 m14 14 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r15 : List ℤ := raw_ints% [-0x66a04cac25824ebf63574f4000,-0x8d1a88f369ef38f69d8039ec00,-0x587b9fa7d201b984153b026980,-0x21868ca51a553969f7bb7400a0,-0x8916f25ebde068d01c27c5af0,-0x18f85c2b4b049be93d8688910,-0x3563e1aa4d5fba51eeb0e4c0,-0x54da9988f6dc0f125986caa,-0x644f1a3ef8a701923b04c3,-0x572c01826d6868604ecbe,-0x362c2fd84cf3bed12252,-0x16d10d956421bd4606e,-0x5d7ddf39a7bd7f39b,-0xb01c1c118bfd45a]
def m15 : List ℤ := raw_ints% [0x0,-0x97bb3ee0bb892aa1f1dbf3743e08000000,0x95cc6b64f2c5a9e6cd94dd9d5c515e1a800,-0x45b32f65a4d70eb392b576977849807d1e00,0x14501ce2fb2ee4f4e0e0727ca1c08151e1d00,-0x428064a950e1ff4d0d9c6d30fb570201e52c0,0xa264ded21bf5e50b873b91101813e72851540,-0x132bb990be53b9bfdbe21fe3d97af1d7213ab0,0x1ca9992d2b1eb7c8a82a2ec57e13381cd536f0,-0x226df21acdc14f70f8366054013cd6376dee88,0x2188a12cc5ccc01c48e3af6cd5ad0479e2aee8,-0x1a9cd92802715e166d09e8fd534674d66b1844,0x113b3bbcde68c1a853155c275220483c4ca634,-0x915cf4ff8ce01720dcadc3938b55433e79ef2,0x3e16d4b6167da6c43e25866ba531c352b8daa,-0x154d080d3889221d16afda21c685889ea62b8,0x5cbe3da46eb763b39cc099305957e4b4f608,-0x13acae91304bb9275ce248145cccde9536de,0x32da4711175beadc91f95fa9219e9f1cef6,-0x60f6f7117f978547b8deb565e927d627a4,0x829ed5e12ecffd9155d9c1473b035e2f4,-0x750c17d43631eaa75f6348686d71b78e,0x4000e3e2c684e3906088ce166523d76,-0x12c6268982585ee933bcf3ae5b4b70,0x2680457f7668053d0812774df3a0,-0x17ff4b7d79d43e77bc5351ca9a,0x205d4099aaac229bec01302]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 14 52 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 52 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 32 indices rho q15 m15 15 811444512974135040000 18=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 32 indices rho q15 m15 15 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r16 : List ℤ := raw_ints% [0xa6e8172597b13a4d5c779af4000,0xe5386b941a0288384083c4acc00,0x8f8d5e43a46df41522786503b80,0x364fb019749d8a2d622bac5f3e0,0xddb7960e94fd7f6dceae4f6a00,0x284f1fe937834172b115485a80,0x5601300797d76c963db97f8f8,0x885c1e1c0501912fbb591446,0xa0c11b6c3bb58d1b2af1614,0x8b4357013594b8781e80fb,0x563b925562389e2df9508,0x242b2a9c821bf4add380,0x937bf61a8f60fb128c,0x1143ce6d614cc98ff]
def m16 : List ℤ := raw_ints% [0x0,0xaab2a6bcd2fa4ff6301771e2c5c90000000,-0xa6b7c57cf3491964cb39dfd73c2d59fc2800,0x4caf595de7cd3c0e9ad14f1d5903e264efe00,-0x161332c0763339b9117e85f07ee4b79e681f00,0x475228c82de9f7c3c01147f00156f53ad3fc40,-0xabb3b0b0558903b1e685e5d712558cf74e86c0,0x13f5ecaba2179ed709e7d46d4cc9871ebcd0b10,-0x1d59e5a587c2abbd52e385648ae2018c59389d0,0x22a017036a6401efab494676b973d1260c5da28,-0x2111031698413716d3aa5be097ab2c3c513a708,0x19ae875af3a3e2e3db0d8cfbd0bbcc49be8039c,-0x103d1a82d8a514b36261ff08daae0f5006b99ac,0x85717561882b3dbca48ebb8c6c235da26bfdba,-0x375c7128db72eb4722e62a92c3337d4fa43b92,0x12625b96b2dcdc7cb2779f692fafb07c2a76d0,-0x4d2a3d2942dbb07634c7c621cc8ba9bbfb940,0xfb44e2ba4770c23e34754642d81497db85a6,-0x26b6468e29f4f0101567117fe45b7b3f48de,0x45e4e37da4009496feadfe02a572d71586c,-0x585db07fa5f2e8fe6d242825529c778d1c,0x4980cf7d12e69a80f614ebb4e94efd926,-0x24cd2275c9883eb8f67e53907ff29d6e,0x9b763c2d74b28f68b566fec1db7ed8,-0x118ee76eda25e094f69d6c4fa51e8,0x9645f7f32080bc4a69bd1a5252,-0xa810f1a0b51fa790e998d9a]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 14 54 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 54 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 32 indices rho q16 m16 16 811444512974135040000 18=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 32 indices rho q16 m16 16 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0x1143ce6d614cc98ff,-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r17 : List ℤ := raw_ints% [-0x105cd5b2e11540871b63cea05e000,-0x1672c8d675f0600388456ff1be200,-0xe0ad23164dabab2ea00b0be57940,-0x54e481d586994094f41d43b12d10,-0x15a0d0a36c98fcda70dd424caf90,-0x3ecf295777b172bf286136cdd68,-0x85c2cf97b62efbba34598c5dec,-0xd3a0ef3a6dc1f41b159663e99,-0xf8e3e19f243159c2f10ca17f,-0xd7070f443f95314bf64a831,-0x84bb4983a658202431a4b6,-0x3778f3bd968cae8bc1acb,-0xe143d5cb4e296b2a6ef,-0x1a3e571213b3b125d3]
def m17 : List ℤ := raw_ints% [0x0,-0xc008fb946d5999f4f61a601f1e8220000000,0xb9a3a7a2a9ffa2769ad2a8c0bb49f25bea800,-0x54740386bc45cfdbc27af54f24f0a3a73ede00,0x180686a5a91d3cda5ea5499383d848c9684fd00,-0x4ca4235ab294040c07ec1eb0dee33a47d4b1ac0,0xb5fe2a6405bfcbd9ddcde3e4a6091f7d7e7e940,-0x14d8394b97c217701d04454bb2480ef56db429b0,0x1e28e5e6fe29157d1f93b2c662cf520d71b061f0,-0x22f543b286396c41b2b919666a03853cc92da9c8,0x20bf342379732a10485ec469f64cb2204803ed28,-0x18e689e963a9101b60d9e2e3abe21efbcee75b44,0xf6182154d1239f7ca5dd3e1017e6e4f446c6734,-0x7b2885b9e84b312d6eb4f507974a53f36fe6202,0x31a331f100c2308f96d6e7cdbd671a963c0df7a,-0xff50a5320d14332c90705467d4c88854058298,0x40916ef6ac68cb3daa08e196689ec7f6daa0e8,-0xc9ab8c8baee0a08629ec3c32316344bf5810e,0x1d9f44a81d65bfafdf30b5efa8b3e1a4dc8e6,-0x329d0ecadba57424ee7408b67ce5f6bfc7e4,0x3c02853f416c718a21478b1b6c9d3997d34,-0x2e4a457df7a2c301730cb590e7c2b73efe,0x153267349378c0260082b157d8b691726,-0x5081b0d4655db7ce93377eff7c39b50,0x801431b22998649fc7ed24613e480,-0x3ac4ff690762746f28f471bb0aa,0x36825b5b4a5bcdd76d56d952]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 14 56 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 56 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 32 indices rho q17 m17 17 811444512974135040000 18=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 32 indices rho q17 m17 17 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x1a3e571213b3b125d3,0x1143ce6d614cc98ff,-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r18 : List ℤ := raw_ints% [0x18df404443cf56b5d6f50a05286000,0x221752715c47663c154bfc380d1a00,0x154d9263ec094608fbd7cd6c0b0a40,0x80a30df313adeda4340f1001d5810,0x20bade04219c3df6172c2b3c61da0,0x5ee8b658d2e08e7349c3d4f275b8,0xc9c9582d4b49bcaa328f3202194,0x13ea84beb42776370b799c49591,0x175f8c68fb5cf302b7c434b008,0x1425179ab3684452b5a7d4ba2,0xc66b2fe8c7d724fb37d06ec,0x52aaf4090387134d5eb061,0x14e81b8b75ea7b3663bb8,0x26cf765a9816bb622c4]
def m18 : List ℤ := raw_ints% [0x0,0xd80a1b06fb04cd3394ddac230252640000000,-0xcece54a47911d308f7c1a39653c38c99a92800,0x5d18cd954d0350f5b98cc80c0c67c16132cbe00,-0x1a2f944d1a64581e49d05ff0b9de0c54d3e8bf00,0x52842e852f795b06552544575bde1e6d003b1440,-0xc15d2884e74b7f90a7f3e06161cd5e61c5a2fac0,0x15d4970185304fd1f7465244807e230a990664a10,-0x1f18259b6640f97c7016a0d25573906c211e9e4d0,0x236d8d8d07cc4311478514208ed73e936b9d23468,-0x20913a57f155ff5b27adf66756fa48bd62daa2848,0x184121f0abdfb753ffdc607ea77707e418481259c,-0xea3fdc975cdfc9327324c3284cf2db4ecf5a65ac,0x7242e0e92087802c3233880a7d3b789782e1278a,-0x2cbf61cec83fb5d2b62082891855ad2d3288f522,0xded5fdd51fa590e71cc3d0e3310b697aabf5e30,-0x365338108c76d7feba1035aaad5fbe40ebcc3a0,0xa2b90daa7b938cef89b2fa6e99c9d4fb8f3616,-0x16c76376a981ffa5e2ba1561f41a7a697be60e,0x24cfd794b81a6a1e5a1e36217e05dab36c8ac,-0x28e629e14bca797881b820cd621d0c47db5c,0x1d3a60327a7fc3899d211b8236618537bd6,-0xc3a3b2e9bb3b009a6a0e7897a99a91d5e,0x29b5ae508dbec971474601f077d54038,-0x3a5f0d636b6021df7c4b72ef4a6c48,0x16f775f27a056564cdb157732922,-0x11aac76688fbd7c8a44e387aa]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 14 58 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 58 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 32 indices rho q18 m18 18 811444512974135040000 18=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 32 indices rho q18 m18 18 811444512974135040000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_18
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<19) : intPolyRF (mz e)=rfPoly (C (811444512974135040000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^e) := by
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
#print axioms moment_source_18
end
end CatalanCore.Li2.NVMod.FamilySource.U4C18
