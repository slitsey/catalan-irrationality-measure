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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C19
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,19,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17,18]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0xf29f331a2000,0x1568705e2de00,0xdd7e1e2c7ac0,0x56fce4308770,0x17307d8f6c90,0x470cbce9098,0xa15136bb94,0x113d3f1f6f,0x165068d3b,0x15c404bb,0xfc114f,0x8352d,0x2e91,0xa1,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x7,-0x38,0x69,-0xbd,0x34f,-0x4410,0x86cbb,-0xaebc3,0x22f27,-0x93e0,0x5377f,-0x5ed4]
def rhoDenominators : List ℤ := raw_ints% [0x69930,0x39c,0x58,0x1b,0x4,0x1,0x1,0x7,0x70,0x6c,0x18,0xb,0x129,0x8f]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 19
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
def m0 : List ℤ := raw_ints% [0x0,-0x844c367c2ac19000,0xa9c2fada315537000,-0x67efbda18598712300,0x286587d6b63150cf480,-0xb2fcf895a047004afe0,0x2592bc09d7ba8abf8040,-0x635e06b71cccbe28eeb8,0xd42a0f0c494bbf88a4a0,-0x1740d1cb173b91871899c,0x21e38c4f13bcd89890be8,-0x296080948173a35bb27a6,0x2a89ec59384e0c8372f60,-0x24eb878df1b5b54260f2b,0x1b0fdd42ef73d6a52925a,-0x10b931e4efd8e5ef9b501,0x8adc190f6adf097ea1c4,-0x3c2248a0a065d402a05b,0x158829f78a0d7bb8bf56,-0x64b4397c84c476307ad,0x179d943fb1211b9b818,-0x45667d98b65f8260a9,0x9a75185beacb8c746,-0xf7e81e3aaf915b43,0x10a1ef2c2b9a1c64,-0xa8510174d72555,0x30fe9b16b0c22,-0x376bf6d0fb1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 14 27 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 27 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 33 indices rho q0 m0 0 56155329617587200 18=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 33 indices rho q0 m0 0 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x94d5bd4bb019c2000,-0xbb7a4274ffb66fec00,0x709b86032a8f8fd9b00,-0x2ae8a354e8cf4b79d880,0xba422d9415c026dd24a0,-0x26469adff9a3959d69f00,0x63028cee6fa0a6e7a46a8,-0xce95b8ba5c22f473fd250,0x161a86bf3240dc7d4fecbc,-0x1f69c71e10029d2d1db9b8,0x255b133f8a3d40ad600402,-0x255aa29546312579ce647c,0x1f7c3ec4105d3e1e0f38c3,-0x165fe3a4a63f65e58e2bee,0xd610601da0257a1ca6c51,-0x6b40b130a03d63d649760,0x2cb9dba579fbdd07b5263,-0xf5ff77c7b046d4a6ecca,0x44c8e2c1a1ca12d7afc5,-0xf5cb4ae7fc351cb128c,0x2ac31ae9199f0de1f11,-0x5986265dbfdf1320e2,0x85ee800a092ab9703,-0x8454ce5e70253188,0x4ba02f4015a266d,-0x135074f73876ee,0x123bf710453d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 14 28 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 28 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 33 indices rho q1 m1 1 56155329617587200 18=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 33 indices rho q1 m1 1 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0xa77074f5261cfa4000,0xcf30618720673916400,-0x7a2c986a6db680bf5b00,0x2dac59903362b203c5580,-0xc25ddda8420179c22d2e0,0x27209081c45eec3e949900,-0x6310233905e16740ba10b8,0xca1e28ab9dab15e6085690,-0x152006c7cb4a39e359a285c,0x1d4b6b4e0682aa47ce580b8,-0x21f307f06d6148205a40c86,0x210992d092ed678d092752c,-0x1b0ed28d870df7263f0939b,0x12a690272bc024d1716a64e,-0xacbaa5b4d4f917ee5644a9,0x5394fe5081fe5666033b30,-0x2192971145ac2ad9fceabb,0xb14ceb1b36cf271d6488a,-0x2f6c5993a3858b2b53ee5,0xa15d460bd50709b587dc,-0x1a94b01472b611c3e099,0x344f2cf1c13ff9f8042,-0x48dcf1cb0e4b936ddb,0x4227a8060d9f07c78,-0x2214f3859f9b91d5,0x79d84deadc926e,-0x5fdd31344a59]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 14 29 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 29 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 33 indices rho q2 m2 2 56155329617587200 18=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 33 indices rho q2 m2 2 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,0xbc5e8393cae09988000,-0xe521b1e7bd39bb189400,0x84bc9b27996c4cff62b00,-0x30b75464cca1a80888fa80,0xcb61f768ea1493f85e8aa0,-0x28222c97f6b916670444780,0x63847c244d472002d4b3728,-0xc6ac8469ca2f71fafa05d70,0x144c06f2d4ad3057a46e0a1c,-0x1b7ae5da747e20ee5dab6f58,0x1f0d9b43d10f1814b986a122,-0x1d6ca1ab6014f87dd097aea4,0x176d77f7bc1bb76dc142eddb,-0xfab953c206e9cbcaf9e2fd6,0x8c8a4ada67b636705fff9a9,-0x41b35fd994643375a8976e8,0x196cd8d709093c64eddda1b,-0x80f13fe032a5a1cb4f6c92,0x20fd9c447739f0c05461bd,-0x6adefa3b4e9b7179f8704,0x10a949f088b8becfaf859,-0x1ecc77450ff5cda8cf1a,0x27e5f95531347334d8b,-0x213b973471ed180040,0xf662f5f1a786a2f5,-0x300a2674e4324e6,0x1f75ff88cbbc5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 14 30 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 30 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 33 indices rho q3 m3 3 56155329617587200 18=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 33 indices rho q3 m3 3 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0xf29f331a2000,-0x1568705e2de00,-0xdd7e1e2c7ac0,-0x56fce4308770,-0x17307d8f6c90,-0x470cbce9098,-0xa15136b954,-0x113d3f160f,-0x165067ce7,-0x15c3f52f,-0xfc086e,-0x8320d,-0x2de7,-0x8d]
def m4 : List ℤ := raw_ints% [0x0,-0xd3ea5406443cacb90000,0xfd91e0976932e7092b400,-0x90683925fac56fd8ed1b00,0x34110321bf6ab7439732980,-0xd562b356de60a7143fc42e0,0x294d61658472e930ebd59200,-0x645e862297717abcfb186838,0xc42e710119342c72fd624350,-0x139a28b93e51afe64ac6bdcfc,0x19ed194b5fe13bec7d371f3b8,-0x1c9542c272fd5c757c47c1926,0x1a629cbd7574b565d2ce6575c,-0x146eb9702b7abe069ca88ca03,0xd449962c648816a9d25bf04e,-0x7346f28f95642384cc580d01,0x3414474ad210c4c9bba5d2c0,-0x136bc6ea97a4d65dc7ad9763,0x5e9778337a8fdc61754efaa,-0x17264d19497113d18b7fabd,0x4760eb7dc00e63840de82c,-0xa86ebb12285cff825c811,0x1243c32987bbaa03fa502,-0x15fadac793d9656014a3,0x10c489f4c1fd81313a8,-0x6f91329b010b5d6ad,0x12efbab0aeb68e8e,-0xa5019c8df0741]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 14 32 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 32 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 33 indices rho q4 m4 4 56155329617587200 18=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 33 indices rho q4 m4 4 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x8d,0x1]
def r5 : List ℤ := raw_ints% [0x85a1af2563a000,0xbbb5bf0ada2600,0x78a7ef989cbdc0,0x2f0bcb908e1df0,0xc6eb843ce43e0,0x25aefc3363728,0x5468ef56bfec,0x8dd6a8d96cf,0xb3675cb370,0xa97f01e18,0x75119354,0x389415b,0x1173d0,0x2ac6]
def m5 : List ℤ := raw_ints% [0x0,0xee679e870cc4425020000,-0x118ccd4a435f057c0adb400,0x9d4f7f7c51791df042b4b00,-0x37c1b1cdc9dd93ca7bddf280,0xe076d0711889d562f5306ea0,-0x2aa48855d984029826f898780,0x659e5a1533f274c50c3a2e0a8,-0xc2957ca1e92e235ea190612f0,0x1306d1ff2ce05780c5afde2ebc,-0x1898e46e4a69054ef30d082e98,0x1a78921bd37d021b3c9c693bc2,-0x17d12fb822f9056c2220d7c044,0x11f26b2e40d2beaea8fd188f43,-0xb5184b52d911162115c072ce6,0x5f4cbe9f40b20641ae2a0d4e1,-0x299e53bd4fc4930ae7248e568,0xef560040d8c62e935f8f8283,-0x45f9efdbb38696604691c4c2,0x10613712502cae0fe4ffa2b5,-0x300f2be144d8a3da792eb24,0x6b3aa3bc5edd514e421751,-0xae7c127c9cc19202b318a,0xc2d38b58c7ea742b7973,-0x87e5e0794e92d7f1880,0x329c5154dbf900098d,-0x776359ba0b42a3f6,0x360765fa5eb78d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 14 34 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 34 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 33 indices rho q5 m5 5 56155329617587200 18=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 33 indices rho q5 m5 5 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x2ac6,-0x8d,0x1]
def r6 : List ℤ := raw_ints% [-0x2889c583cf74c000,-0x38b571b6a0801400,-0x24464abf97b04a80,-0xe101d18db2462e0,-0x3b0d84f142f7970,-0xb181f541ae81b0,-0x18992807e52550,-0x28cf8caa3c5ee,-0x32c9cbaf52d3,-0x2ef9705a332,-0x1f85dc3b02,-0xea00ef7a,-0x43e8ccb,-0x972b6]
def m6 : List ℤ := raw_ints% [0x0,-0x10c349257ee5cca9a240000,0x13727b2b23a3ee7cc8647400,-0xab96467f1ec59f1b4680fb00,0x3bd2a3450fa44a6fea0810980,-0xecb7d8e07f3284dcdb7bc26e0,0x2c2a67f4dfad36658cb0164c00,-0x67452fd52d4822afa9142b29b8,0xc1d6a698cbeeefd76380f44f50,-0x128f0d0cad4b9eca2a16a216a1c,0x1776c2d2a9eefcabede56be6178,-0x18a9610a43333baaef2ab44f3c6,0x15a359f5a2bfbabcdd4bdb1421c,-0xfdf6c8b6d59526750b0c64be8b,0x9b9d7e20e8b7afbd25e881fefe,-0x4f631288665c48035ccec992d9,0x21859ce66678924c7ed8b7ece0,-0xb9d4afb077414b6931be6fb6b,0x342ff1e5e3e97c3f4d52b27fa,-0xbaec7ba7bdf41fac8ba055d5,0x209be941de3fbab65325e1ac,-0x44c21f2ca24c4fcd4648e69,0x68d87f6ce1f3c77dd03052,-0x6c7dcb34b3967b9749e6b,0x4514d3893ca576822b48,-0x16fe1baa541931e16a5,0x2f058e6ab084fd27e,-0x11ac1482eed5069]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 14 36 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 36 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 33 indices rho q6 m6 6 56155329617587200 18=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 33 indices rho q6 m6 6 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x972b6,0x2ac6,-0x8d,0x1]
def r7 : List ℤ := raw_ints% [0x8f4502ddb16d2c000,0xc7bb1141334b11400,0x7f3f93ef2f288b080,0x31198305d020fdf20,0xcd086155183aeb80,0x2643b4e6e26702a0,0x542a1d172f6c188,0x8a4797b9e1a19a,0xaa03ce9fbe804,0x9adb225a501f,0x65df7aad8f8,0x2e063c9cfc,0xcdf5bd9c,0x1b297ab]
def m7 : List ℤ := raw_ints% [0x0,0x12dbb24a2ec2863ed6880000,-0x1590200b996f0522b161ab400,0xbb64a7c20c3a33917a7e2ab00,-0x404e2e8950577a4c4f928fc280,0xfa426fa279d8f384a0860d4aa0,-0x2de23b5d5a1226da842d2f53580,0x69555820d91d0936df288991228,-0xc1ea00612a587164ff2abbf71f0,0x12306ede67f4d8932d947d0b255c,-0x1680813eadee879a6dfd3f700a58,0x171c222ae9f15d9b61a613833f62,-0x13c84309dfcf25f76fa4ef8495c4,0xe21fd718d12577fbaccc9b06d2b,-0x86abe604b249701a49c590ff616,0x429f67ceb40c42ba167c74d5759,-0x1b352a38dbb134b043f2ff56cc8,0x916a57dc256e92da88ce71e4eb,-0x2739d615ccd3427637b6817712,0x865a17e3c603d53eac094d56d,-0x164a2f321112cae686c9c71e4,0x2c6462892ceb0bc8a133dcc9,-0x3f60e7be88872f94858dd5a,0x3cb3f8f598e6c7587a0c1b,-0x2339ee2ef81504a2a3fe0,0xa753d3a6318a5399125,-0x128267304ec29fb8e6,0x5c644f17b0e7a95]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 14 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 33 indices rho q7 m7 7 56155329617587200 18=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 33 indices rho q7 m7 7 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r8 : List ℤ := raw_ints% [-0x19be1a299c5cb536000,-0x23c87863d6b04a98a00,-0x16b87576a5f48ec2a40,-0x8bb84ae0d7b5a4d750,-0x244c59c43c81e69510,-0x6bcd2a26b03b95208,-0xeb978c8ba6b4953c,-0x180169d5fbebb69d,-0x1d3d1090cd281cf,-0x1a52f843c38de5,-0x1110f8c28d8a6,-0x7910b783717,-0x21072c04df,-0x435ba4ef]
def m8 : List ℤ := raw_ints% [0x0,-0x15372893749ad706b15900000,0x17ec6edfcf08e82abc7d93f400,-0xcce782a31a43c5eea1add15b00,0x453fdfa9793cdbd9b5c82a81980,-0x10936a838cda09234d0c28f65ae0,0x2fcfbb306ee223ab48a1d5b77a00,-0x6bd23b7cfd3b80ae5b8421ac6738,0xc2ca63b30e8b2fa40146a17b6050,-0x11e9028a82e9620044afce7e37a3c,0x15b101b40cd81ec976fbdf1c0b038,-0x15c75f1c8b86ee04ff2e9016f8d66,0x1232560f73fc68c00f171d504c71c,-0xcaa7f8f4a74320395dd06fe059d3,0x755a5b9f9bbacdebd5598c9a8fee,-0x3850812f55789ce8b4f1ce3f8b71,0x163f4a18378f2e24af9a048a7440,-0x72a6c7cf7fffa922974c89fbf33,0x1db504dbe494d5b586b046a618a,-0x614882fae9a0c10d953da920ad,0xf5816eef554f90ff49f21e1ec,-0x1cd8dd4255f63d731ad09e101,0x2686f6ba742800f7c9e18e62,-0x221cf9756a841164cc47473,0x12032b5d9f5607ebe34fa8,-0x4c2d4eebf1b887e560dd,0x748075ea974b5b5b2e,-0x1e2906cbb6923fd1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 14 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 33 indices rho q8 m8 8 56155329617587200 18=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 33 indices rho q8 m8 8 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r9 : List ℤ := raw_ints% [0x3fd685478006d1e3e000,0x5884139525ccf3b1e200,0x380ac4e7b49787c00f40,0x1577cc519e9b4bf60750,0x58e45bf0142abfdc320,0x106cff225e7469bc8d8,0x23b52e7dc348269d24,0x39d9bd97330d1df65,0x45ef1c7a2ca4ef78,0x3e646e777aeb4c6,0x27ffcbf6bc36dc,0x117cb6b90a05d,0x4af93132648,0x95576b570]
def m9 : List ℤ := raw_ints% [0x0,0x17de0da5e32e31e78784200000,-0x1a8eec3bb77cc7ba044bf4f3400,0xe051112d69235ca51d416af0b00,-0x4ab49cb1f3551243c9668dc4f280,0x119b869881bee93312b626f0086a0,-0x31f7282f84762a50aee954bb60b80,0x6ec05dbae1d8f62001da48beae7a8,-0xc4753a4ecaf096837bb79b73bcef0,0x11b738bd2605405507fcd32e8cf0fc,-0x15040ba670597f5638935f39606618,0x14a3512a3f7a644ba0f07e4acab202,-0x10d691f38d342fa54c5030c4ddbec4,0xb6c868670cac3ba394bf2aff70e53,-0x66f342a308fe1f799bc8ed5cd7d46,0x2fef7848c512846641b11516c8491,-0x125298f7f2e168aa02440fd1eaaa8,0x5b0f1f721e1c7693089822975493,-0x16a9afada890c5bf4ce8528d4862,0x46f20431e1ebb08320bf2086ae5,-0xaa26261c11b32086f79cb12124,0x12dc70d3cbccdfbc57ab2b5e01,-0x178b166063f3d5e12a43f592a,0x133f4a5dfcea6359c2ed8503,-0x93b8c673b42a3a196de6c0,0x22b42cc12d011f46c777d,-0x2dcc9bb604848b2e8d6,0x9d61936f8f3416dd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 14 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 33 indices rho q9 m9 9 56155329617587200 18=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 33 indices rho q9 m9 9 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r10 : List ℤ := raw_ints% [-0x8d89829390f72940e0000,-0xc3d4259a6aa7d7c534000,-0x7badc911ceab8070d9200,-0x2f3e38ec935a93add61c0,-0xc2fa78331f99e4eb47b0,-0x23e467534cc0a8acf760,-0x4dae5bf62ce8e2debe8,-0x7d335e05847cda9e6c,-0x966cfd8935418a16b,-0x85393b7235a75958,-0x54a7b81643fb8ca,-0x249c3f4e31ddd4,-0x9ad951464413,-0x12f2c94f528]
def m10 : List ℤ := raw_ints% [0x0,-0x1ad9cf5a9f93f8247874a400000,0x1d80083b1be84f63d4180cfa7400,-0xf5d98f5af2e50560f2bd55afbb00,0x50bacf252820f0e7623715e5de980,-0x12befdd35498600b8292b5f81b4ee0,0x345d57980e106de8b4efeceaaba800,-0x722565f2ab237029591e4f2ff008b8,0xc6ea54fe5195b5740870996da99d50,-0x1199da87266a1ed91d7ba22914b3f5c,0x147625cd45f7d4d21c795cd79cc18f8,-0x13a98ff20168841447211562c12c206,0xfac01b4639628e154c68999844b11c,-0xa5e225d4150d35b8e5f6de4e69d05b,0x5ae84003158cc705ed26d41ef0915e,-0x2914eb52b9b61a87db601d355f59c9,0xf3241659f8388bd95b7ac9941dfa0,-0x48d5dc9bcc81ec6d9b0941a1ed63b,0x11693ff3a7dae8c1dae1187d18c9a,-0x3417ecc638a2bfba79c802111b45,0x76af96219dca3bedc4a42d13b2c,-0xc67619bda9151f235144325b59,0xe7515eadc87a649b100c2a7f2,-0xae62fa82233e41bc0cf135bb,0x4be07bcf40312ccbba5b608,-0xfd14ac06dc342334a9fd5,0x11fde3f7945c920adc5e,-0x334824fc3fd467f79]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 14 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 33 indices rho q10 m10 10 56155329617587200 18=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 33 indices rho q10 m10 10 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r11 : List ℤ := raw_ints% [0x11f54ae05162d627cb50000,0x18cccde5162d598cddab000,0xfa1195eb340427c319ae00,0x5f499b990d44139ee5c780,0x18828ae1ca8e1829b164c0,0x47f4cb9c7fd405b9cc810,0x9b26d0478f3b4af4fbc0,0xf8f988595c6acf03870,0x1299d9001475b70e9cc,0x105ffc1bbc8b2b12cd,0xa54b26b3c3f7f600,0x46de2abf1f0a73e,0x12897bb63a2dd4,0x23d1b867ea15]
def m11 : List ℤ := raw_ints% [0x0,0x1e350945f3867729078338800000,-0x20c93ba1ebb906ee06d1d1991b400,0x10dbff6fd3df56455b605f99cb6b00,-0x5762928b929d7bb59dfcecde01a280,0x14009ecfd9aa6cc649494830b0dc2a0,-0x3707c167a3af7cceacb67d30613f180,0x76082adbe1376e4d2723eb44da97128,-0xca2bcfd64809c9c133973d536fb9bf0,0x118ffee426e386051c4ccf3bde3d659c,-0x140477923b8f4cfcae757ae82a059fd8,0x12d4d1112ec2f1ef0e38508072a0a3a2,-0xeab52ea2e85b182ecc21eaa9653d1c4,0x977553257a49c3f5125a4be035aafbb,-0x50c90f9e1a7922a6367ab3da5278df6,0x237118cbca5e96f1232db7fece11089,-0xcb077cddff4f645ae7533ae9220588,0x3aa8f9dc540ec05097c3650e05307b,-0xd77bcf0d4c586aac4bf85cc3f5832,0x2680e5fb9b8c224516f7aed33ed1d,-0x534cb8bc3e7c0408b70bddbbe864,0x833c3eac9b5106e4f1e461de5f9,-0x8eb19834089daef9177baadb7a,0x63138f66ac070a35ca17dc42b,-0x270b622a5832b2230b9d0ea0,0x7362d6488c553013d2c195,-0x7100a119225ab682cc46,0x10b214cc450847ee65]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 14 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 33 indices rho q11 m11 11 56155329617587200 18=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 33 indices rho q11 m11 11 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r12 : List ℤ := raw_ints% [-0x21f286ba3355e247f264a000,-0x2ecdbc17e33d02e9afd33600,-0x1d70e4c4f3ab3033b73ee1c0,-0xb31c4bc163bda7a4ebdce30,-0x2df56d9c8d7e1f7f509c050,-0x868c9b9f8c3594cb9367b8,-0x1212f54366e7e32de1e314,-0x1ce583c920dc6db9d0e5b,-0x2264c85069fed46e4b67,-0x1e203cb258ee933678b,-0x12e4e16584b01d8eae,-0x80b353967a6a88b1,-0x21616402cfab4a7,-0x3fd6943200961]
def m12 : List ℤ := raw_ints% [0x0,-0x21fbaa6eb1f7460e28739f9000000,0x2475289b8c4910435b663afb8cf400,-0x1284ad2ddd37fb85c9c06c19ac21b00,0x5ebde8bc86d2c7bf2a76603eaacb980,-0x15638cfb6092c4f4247618608a80c2e0,0x39fc90b5e6c18b28d493711e5e658600,-0x7a70c386159db3e645f2b3cff94ece38,0xce3e023815f7c21d7d4925983672a250,-0x1199027ee59a00c42e257c630088ae97c,0x13acb090f29bff980c424d6fe1a28afb8,-0x1220b5120f7a4640641d92ffa528219a6,0xdce836a315b5d78f64daab8367d01b1c,-0x8b1a94378841c476c56930f4d31bbe23,0x483ca2ba45a619a5fceb09a68d21d84e,-0x1ec613abfe0ac6a5303cbb506a1fd7e1,0xaaa85a2250c552cdecbe58b60a73200,-0x2f8f13524cf8c49f528b6f57f586883,0xa7c733b255a487db23b01b59f52e2a,-0x1ca3b0abf7d6b73c5095278344d39d,0x3acef3d58334b94fb877c36ebd66c,-0x573b77267e96170167fe0499d971,0x586564b8621031f038961ef0402,-0x3875147f9c36fec5b31fdf3843,0x141f5288829fbbff25f29fb68,-0x349d97138035e3cf040838d,0x2c535b51adc03bf62310e,-0x56e5af971934fec961]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 14 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 33 indices rho q12 m12 12 56155329617587200 18=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 33 indices rho q12 m12 12 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r13 : List ℤ := raw_ints% [0x3c808b1b92e80e0c248062000,0x534b2d2f13a14d08c025f7e00,0x344ed550d9c57db5ee7580cc0,0x13da179d942eb2017b1e75fb0,0x515429010557b5b6916b6460,0xed8596ab929d3f162506148,0x1fd16a0467561091541df5c,0x32b566210a7e713a03ecfb,0x3c225b1ff9348bf358800,0x3472f1a85c3dd7621274,0x20bb4e21eeb29caee64,0xdda9309e2097d2c5f,0x39181f184c6a3540,0x6c48f30a2b315a]
def m13 : List ℤ := raw_ints% [0x0,0x263b1fbc88362ecfed821382000000,-0x288fbf8cb71ca94ad3c8d47d41c3400,0x145c92bf91ce4beab21bba325363cb00,-0x66e0f494e81903e721496289263e5280,0x16eb4a7d4f1a5504e2ca5885c078b7ea0,-0x3d42b65961bb88a75cbadc78e1bae0780,0x7f689c89df8bc751128e07039561d8ea8,-0xd3277978791372bb378ead3f00d12e0f0,0x11b48154b1938aae70190bcb0f88619b3c,-0x136cf4f49984c5244d359dce0a90c95f98,0x11899eb99ef026d5bca1ca7bbcf6b28c42,-0xd10a0a1cf97e75c3f7f6a70528af3e8c4,0x807df415354cb26fe86e43ea90f236763,-0x40fbed314bb710746415948720c9a7226,0x1ae37a2ab0d24db165f1e58290e284141,-0x905ed9c44fccd36f9bd5cf4c4610ef68,0x26cedae3094c09da369d7d80af0e26a3,-0x83773dd40eefecfe85e412aaaac0882,0x156ea46068c568ca72341e7d5e97a15,-0x29c0470353bad0f2ee19d99cd655a4,0x3a44721446847c7a33e4cb8e056b1,-0x36f957e0be4322b2064b3418e24a,0x2041f6ecc43ac0c67b204aa5b93,-0xa6249e7aa93892b34188f9580,0x17fe3aad123274d5d69ab16d,-0x115fa7920073bc1c21f136,0x1c3ecd2f4f35947332d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 14 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 33 indices rho q13 m13 13 56155329617587200 18=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 33 indices rho q13 m13 13 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r14 : List ℤ := raw_ints% [-0x66a04cac25824ebf63574f4000,-0x8d1a88f369ef38f69d8039ec00,-0x587b9fa7d201b984153b026980,-0x21868ca51a553969f7bb7400a0,-0x8916f25ebde068d01c27c5af0,-0x18f85c2b4b049be93d8688910,-0x3563e1aa4d5fba51eeb0e4c0,-0x54da9988f6dc0f125986caa,-0x644f1a3ef8a701923b04c3,-0x572c01826d6868604ecbe,-0x362c2fd84cf3bed12252,-0x16d10d956421bd4606e,-0x5d7ddf39a7bd7f39b,-0xb01c1c118bfd45a]
def m14 : List ℤ := raw_ints% [0x0,-0x2b0283b4193cf4a9eb3255f24000000,0x2d266879e2df5ce32c071e51515f7400,-0x1669394125ab26406a74a61766aa07b00,0x6fe23be793efce1ce0d9df70732cd8980,-0x189bc35a66d8096d5c5e7f8967741db6e0,0x40e1fe14e24c6eca0f311276274e875400,-0x84fa91df9db1b1fce34c050bec3b63d7b8,0xd8f0fd605dde5dc37b6abc075cb1c39f50,-0x11e251edc7a07b5e76aa05a066fc153609c,0x1343cdc3db72feea9085cf877be20dbb478,-0x110c9280465dedfc4dca19464edbe308c46,0xc6d949c02a6a38e1eb81cf419c4541111c,-0x775af03f56e4e0d37a11a6eea720da8d2b,0x3acdf1d0c5acf19ebb63785d0757a1c4be,-0x17a344fda4854e973fc44bfb7132812bb9,0x7ae5759776e2fca3b4f3b32023a0bcf60,-0x1fddaded414e3b45e6bd6364b9482e00b,0x67a55895fb472e54a5ffc0c4fc420e3a,-0x1021ef10cfdef1eaaf41e1992cce3fb5,0x1dccbbea7a3f49c57b31df7779987ac,-0x27196e55cd63593ff8028a33bbc949,0x224fe835aee3780bbbf27d044f292,-0x12799c849f5a02565ef6dafdfe0b,0x55d44151eaa5e04bb290092bc8,-0xaf0a9bbe2a0e4527c98de205,0x6cdf3f8ead3eea19d4e13e,-0x92c8a12d394bfa66789]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 14 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 33 indices rho q14 m14 14 56155329617587200 18=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 33 indices rho q14 m14 14 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r15 : List ℤ := raw_ints% [0xa6e8172597b13a4d5c779af4000,0xe5386b941a0288384083c4acc00,0x8f8d5e43a46df41522786503b80,0x364fb019749d8a2d622bac5f3e0,0xddb7960e94fd7f6dceae4f6a00,0x284f1fe937834172b115485a80,0x5601300797d76c963db97f8f8,0x885c1e1c0501912fbb591446,0xa0c11b6c3bb58d1b2af1614,0x8b4357013594b8781e80fb,0x563b925562389e2df9508,0x242b2a9c821bf4add380,0x937bf61a8f60fb128c,0x1143ce6d614cc98ff]
def m15 : List ℤ := raw_ints% [0x0,0x3062d42a9c64933f2898a0b088000000,-0x324831946d6858d57f29845429656b400,0x18b0d5146f4297c34ffa06c308e6a82b00,-0x79daf18ca4d5425450910a7e6e6cbd0280,0x1a7959f9063ba6fd6ed0a45f3e2de63baa0,-0x44e32693e630d22c9de9ba6b19500b64d80,0x8b330d9e201ae989df9e4174ff3c6946028,-0xdfa59e03a59de5c94e6692ef96c1d3e7df0,0x122281f0e3f1e0a817028761e7a586a9f9dc,-0x13301c5ff44711e68eebce59735dffe57558,0x10a71c81d683a00af706d0175bfd951243e2,-0xbe1fd9fa31b18b8e2532354d68e0b4bcbc4,0x6f79639e15c071a725a5454caa818fdbf4b,-0x3584bccbc6c641455986945ae6c30ceadd6,0x14e76375675fc8600bb9c8a6606a59294b9,-0x69409543b1cf97312d1b87055bd0266848,0x1a53232303f4296a015cf808c7da91b10b,-0x5232b6d757bcbbe10afae37ad73314552,0xc3629f5721daf6242a20d5bae22d6fcd,-0x1560b19813190de5ae0268f4e755d0e4,0x1a59b65c9c5d7ddd0f4708389649e29,-0x157cb96c5eacbb587b28f17cf4499a,0xa9a95827cee83f5c255750cef53b,-0x2c60d950025c999eb526538eb60,0x4fcc9e9115a5ccc70c031ed05,-0x2a9baeca86ba51ece7abba6,0x2fa3dc0969baf34c6735]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 14 54 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 54 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 33 indices rho q15 m15 15 56155329617587200 18=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 33 indices rho q15 m15 15 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x1143ce6d614cc98ff,-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r16 : List ℤ := raw_ints% [-0x105cd5b2e11540871b63cea05e000,-0x1672c8d675f0600388456ff1be200,-0xe0ad23164dabab2ea00b0be57940,-0x54e481d586994094f41d43b12d10,-0x15a0d0a36c98fcda70dd424caf90,-0x3ecf295777b172bf286136cdd68,-0x85c2cf97b62efbba34598c5dec,-0xd3a0ef3a6dc1f41b159663e99,-0xf8e3e19f243159c2f10ca17f,-0xd7070f443f95314bf64a831,-0x84bb4983a658202431a4b6,-0x3778f3bd968cae8bc1acb,-0xe143d5cb4e296b2a6ef,-0x1a3e571213b3b125d3]
def m16 : List ℤ := raw_ints% [0x0,-0x366f2eafeff125a70dabb4c6990000000,0x38060392fe25454b7b8a4f3ae749c1f400,-0x1b3a5aebbd7fe3172fb38042aac152adb00,0x84e7489137d5a7c65d8f20c883f05245980,-0x1c88f53187a7a1dce4c58ba4fa13ea9e2ae0,0x494ffc86b4ba52631c721878e6b700899200,-0x92202bf810b0ab74058c32c64ac61590c538,0xe752caa62444af456c3eedee4d96131d1450,-0x127553e5a49f4e7b5350e7eb88c146584acbc,0x133110a468144ac8547f60a48378fe1559738,-0x10573b9389afc638f34586d5fabca966091e6,0xb6b0e10b50e13ef2e95a821ec7a2fa23231c,-0x68ab1c8a1bd4b84bb4e737e73fde54cc6f73,0x30fb10ce9df917b378cd783f059e1db402ae,-0x1297ee37aa8eebd76dfaf297edc624625b51,0x5aac94272e60baa26aa4f67779c11701fc0,-0x15e01578b0f9ae5ec2b5cf6a34494533ed3,0x418fe918da0f0f1e60322837ccb82660ca,-0x94b1afcb79375cc3fa9d14b621d7b258d,0xf68fa0bc7f10acde19bba3e106c38eec,-0x11d49b140e4960d4a85debca6bac10e1,0xd7f374b3964f6c19fdbf74157ec7a2,-0x618fd624c6d06056706d015c84913,0x16f6551d9cb9e59fc03887400f28,-0x245ecea063635340ddf94b993d,0x10a99fb5f15b448a31a748ee,-0xf738140ad032b37db3f1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 14 56 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 56 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 33 indices rho q16 m16 16 56155329617587200 18=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 33 indices rho q16 m16 16 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x1a3e571213b3b125d3,0x1143ce6d614cc98ff,-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r17 : List ℤ := raw_ints% [0x18df404443cf56b5d6f50a05286000,0x221752715c47663c154bfc380d1a00,0x154d9263ec094608fbd7cd6c0b0a40,0x80a30df313adeda4340f1001d5810,0x20bade04219c3df6172c2b3c61da0,0x5ee8b658d2e08e7349c3d4f275b8,0xc9c9582d4b49bcaa328f3202194,0x13ea84beb42776370b799c49591,0x175f8c68fb5cf302b7c434b008,0x1425179ab3684452b5a7d4ba2,0xc66b2fe8c7d724fb37d06ec,0x52aaf4090387134d5eb061,0x14e81b8b75ea7b3663bb8,0x26cf765a9816bb622c4]
def m17 : List ℤ := raw_ints% [0x0,0x3d3d1485edef4a5bef612b5f6c20000000,-0x3e72dc8e212acd65ec3eed2440761e13400,0x1e0d97702aaef23032bfcc7cb4e32fd88b00,-0x9126d1a975ae6263cd909ba556ece8c5b280,0x1ed0101b4b41924544f9c4c4096bba0ee76a0,-0x4e337939d0cf2b014ecb5a3d1545b136e4380,0x99d1e4e41bb9fb4e28fcda06d9655178d05a8,-0xf008719cebb84ec60e7929c11b34f64deb2f0,0x12db3e04294213eda2fc2028810ea67625697c,-0x13462134ae3967439f413e315d2be8b439d118,0x101b507a0fdcc50e9b46dadf93d7facb05e282,-0xb0672cb7da8ae4cee8c4a9abf57af198d7ac4,0x62c9f66f0aebd9699847cc776b3c1485be173,-0x2d129ae6ec69eea308c626805c49086718d06,0x10a1c96970d8947fbe374637b669e978658f1,-0x4e90696b05070686ab3b6d7767e68856e828,0x124826870e42fc6fbd4b0d4e822cd13649b3,-0x349515670b1d3eea9ccdaafaf2d2e9542a2,0x71bebff900989ce4311be62294f0179c45,-0xb28c6c308eb4aa52749a7d305e3ea2a24,0xc1c6f3a45c97e4ceb4883f4f37eeca61,-0x880696af0a6f4d99e0188debe91856a,0x3831e77f3e237b8983116cbb6beb23,-0xbe33e5be5427b65b2e6c05df0840,0x10924555882013116f1bdacda5d,-0x682e7f9bf2374b79f67f4796,0x50207211188d4d13bdc7d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 14 58 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 58 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 33 indices rho q17 m17 17 56155329617587200 18=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 33 indices rho q17 m17 17 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x26cf765a9816bb622c4,-0x1a3e571213b3b125d3,0x1143ce6d614cc98ff,-0xb01c1c118bfd45a,0x6c48f30a2b315a,-0x3fd6943200961,0x23d1b867ea15,-0x12f2c94f528,0x95576b570,-0x435ba4ef,0x1b297ab,-0x972b6,0x2ac6,-0x8d,0x1]
def r18 : List ℤ := raw_ints% [-0x24c8407b7089f38c7c7469f58408000,-0x325fac649ed5c67be01193272059800,-0x1f72c2b46e40f3f4f77ae424ece6100,-0xbdb2f6cd25c079130c0aabd4b98780,-0x3035a836cb594aa297ebc38c7ce630,-0x8b9ca5019819e331c5e8d19a4c6c0,-0x12863dfa1214e2d11756bd516cf98,-0x1d34684dc780ad6cbf1f114aad68,-0x2235c9939e0ffa46d2faef3619b,-0x1d6c37d13855e23ccd7471c524,-0x1211c0a75bd82a93633f672da,-0x782048e4884826e06d9a988,-0x1e49385c06bc956f0a38a3,-0x3805de383bbd0a25a18c]
def m18 : List ℤ := raw_ints% [0x0,-0x44e4b716abad33a76d4d50cb59a40000000,0x45a4123134c5147abb1e540ae48c37f47400,-0x213349d67e009f2ca7ff00011b95e3d613b00,0x9ebce42ab71480de32b8d39c395956a812980,-0x2154cbcd0d41c1cfc794fb780bcf2319421ee0,0x5399e510b9a4f0dba4ab3a44b20fd98319c000,-0xa25a3bf1ea2ebaea2847499d7bb8ce426e36b8,0xf9d9294ae870ab40147f19afbb12f4b47ec150,-0x1354e9f940949b3c15f577315e1f9e1900795dc,0x136f059e291ea6a5cd735936250a834839907f8,-0xff2107368df453618ec527b9f84e4d91a66286,0xab23e9a007701a59fc5cfa4f655c482341f11c,-0x5db659323fb01941502bab0833acc52abb46fb,0x29b28cc5a53175d479dd4af5fd14e0d51b4e1e,-0xef599ce315063e08cb089bc245c5434561ca9,0x4473b09d7e473fa846d0672e6015bf9055b20,-0xf5d027d95a24ad12ae69619e2a76994b76db,0x2a65b8173ed096c8b535fdc73d8b9ce529da,-0x5770e83b03e9f1771400b6a1aa63bb43b25,0x81dc03e546afd33c368580d9e1cdc35c2c,-0x8416010e1c4c5b084c444c56fa13aa639,0x55e64761c7af8cf8b66125f4b4b70732,-0x206a3235a700fcb97b0ff068895eb5b,0x62827139780c6880c659e7a9b1d88,-0x78c30aadea2ae20fbf7a00d1735,0x28aea0d4ddd918c96f986741e,-0x19f3ff8174a5e678fc9899]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 14 60 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 60 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 33 indices rho q18 m18 18 56155329617587200 18=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 33 indices rho q18 m18 18 56155329617587200 18 14
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_18
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<19) : intPolyRF (mz e)=rfPoly (C (56155329617587200:ℚ))*rfX^18*(1-rfX)^14*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V5C19
