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
namespace CatalanCore.Li2.NVMod.FamilySource.U4C17
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,4,17,size⟩
def bases : List ℕ := [1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17]
def num : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0xd7a9f489000,0x1247cccfaf00,0xb4a20f6eee0,0x43499116c08,0x10dfe78c724,0x3027da196a,0x64968b3ad,0x9bc4cd19,0xb2e51c9,0x9689f1,0x5a3f7,0x2483,0x8f,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x1,0x46,-0x69,0x2f4,-0x21b,0x2208,-0x33d83,0x18f65,-0x22f27,0x127c,-0x4e8f]
def rhoDenominators : List ℤ := raw_ints% [0x289b0,0x1ce,0x8,0x1b,0x4,0x5,0x1,0x7,0x70,0x36,0x78,0xb,0x129]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 18
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤17))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤17 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 18 omega5=padCoefficients 18 (omegaCoefficients 17 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 17 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 18 omega6=padCoefficients 18 (omegaCoefficients 17 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 17 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 18 omega7=padCoefficients 18 (omegaCoefficients 17 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 17 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 18 omega8=padCoefficients 18 (omegaCoefficients 17 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 17 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 18 omega9=padCoefficients 18 (omegaCoefficients 17 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 17 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 18 omega10=padCoefficients 18 (omegaCoefficients 17 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 17 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 18 omega11=padCoefficients 18 (omegaCoefficients 17 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 17 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 18 omega12=padCoefficients 18 (omegaCoefficients 17 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 17 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 18 omega13=padCoefficients 18 (omegaCoefficients 17 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 17 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 18 omega14=padCoefficients 18 (omegaCoefficients 17 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 17 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 18 omega15=padCoefficients 18 (omegaCoefficients 17 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 17 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 18 omega16=padCoefficients 18 (omegaCoefficients 17 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 17 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 18 omega17=padCoefficients 18 (omegaCoefficients 17 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 17 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x37,-0xa5,0x14a,-0x1ce,0x1ce,-0x14a,0xa5,-0x37,0xb,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 13 li0=padCoefficients 13 (liCoefficients 12 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 12 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xa,0x2d,-0x78,0xd2,-0xfc,0xd2,-0x78,0x2d,-0xa,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 13 li1=padCoefficients 13 (liCoefficients 12 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 12 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x8,0x1b,-0x30,0x2a,0x0,-0x2a,0x30,-0x1b,0x8,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 13 li2=padCoefficients 13 (liCoefficients 12 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 12 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x4,-0x3,0x30,-0x7e,0xa8,-0x7e,0x30,-0x3,-0x4,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 13 li3=padCoefficients 13 (liCoefficients 12 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 12 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x4,-0x2d,0x78,-0x7e,0x0,0x7e,-0x78,0x2d,-0x4,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 13 li4=padCoefficients 13 (liCoefficients 12 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 12 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x14,-0x4b,0x0,0x14a,-0x228,0x14a,0x0,-0x4b,0x14,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 13 li5=padCoefficients 13 (liCoefficients 12 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 12 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x34,0x1b,-0x288,0x3ea,0x0,-0x3ea,0x288,-0x1b,-0x34,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 13 li6=padCoefficients 13 (liCoefficients 12 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 12 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x74,0x2cd,-0x660,-0x70e,0x1458,-0x70e,-0x660,0x2cd,0x74,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 13 li7=padCoefficients 13 (liCoefficients 12 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 12 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf4,0xde3,0xd98,-0x48ae,0x0,0x48ae,-0xd98,-0xde3,-0xf4,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 13 li8=padCoefficients 13 (liCoefficients 12 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 12 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f4,0x3525,0xe880,-0x1626,-0x212e8,-0x1626,0xe880,0x3525,0x1f4,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 13 li9=padCoefficients 13 (liCoefficients 12 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 12 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f4,0xb6eb,0x63738,0xd0c7a,0x0,-0xd0c7a,-0x63738,-0xb6eb,-0x3f4,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 13 li10=padCoefficients 13 (liCoefficients 12 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 12 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f4,0x2543d,0x219f60,0x949782,0xefeed8,0x949782,0x219f60,0x2543d,0x7f4,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 13 li11=padCoefficients 13 (liCoefficients 12 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 12 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xc,0x42,-0xdc,0x1ef,-0x318,0x39c,-0x318,0x1ef,-0xdc,0x42,-0xc,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 12 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^12 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 17 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 18 at hb
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
theorem cache_li (j : ℕ) (hj : j<12) : coefficientsPoly (cache.li j)=liNumerator 12 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x72900880872f596400,0x819eba8f89e4ddd8700,-0x458817fdd5750455f780,0x17834b593d2f5e97afae0,-0x59f2097623d74d1c0bc40,0x10299553d0398bee750bd8,-0x243d9a7766ade389a8a1c0,0x40e82d5e9795f0e9729c34,-0x5e5349ea0b1b831b220dd0,0x705d1f57e43527926c0972,-0x6e613de9faafcb4fc79ae0,0x59a5a2a50e7eec5ef63a05,-0x3c2a34c5341a175b366444,0x213f97b102deba2a628da0,-0xf06c8cd2b3a9a37a6fc24,0x57ec18fbd8584ffa5edcf,-0x199df583862f9ac26fcc8,0x5d126f776ffd6726ce8a,-0xff5c32c4e278d1dc228,0x1f916ccee2bd010f333,-0x29e3299f8067a210e4,0x210452e87872c132c,-0xc30b73ce94ee2b4,0x12297b609d30c5,-0x8bcbe1b610,0x3e21b9a640,-0x12a3b7b1e0,0x36395c340,-0x484c7af0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 13 25 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 25 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 30 indices rho q0 m0 0 31209404345159040000 17=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 30 indices rho q0 m0 0 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x79b909088fa24efa400,-0x86e0d6f370194a32c700,0x46cdd84d195c2418cb480,-0x1769464383fb0560afc0a0,0x577cb7e66916857f5ee9c0,-0xf57950b64383356058cc08,0x2189389c62b62a06d48bd60,-0x3a7b3ecfe25892a4bf39904,0x52a36f760d28251ce1a37d0,-0x5f93b6429c2c08eea8f8d1e,0x5b00bb217b84c495081aca8,-0x477fee67032cc1135df4a69,0x2e51a74081dd77a091a5a94,-0x18a517b667d3dee573ef50c,0xab1230bdb74ce7a4b7451c,-0x3bd73498e4280fe8616653,0x109b0aae96d5f062871c38,-0x3927ea8889e620964336e,0x938f54a5288440e21300,-0x110321e2be884460fbff,0x14cb69a1694d8f9e9a4,-0xed4259decaedca140,0x4cfb8aebdf49bb5c,-0x5fc5e0c75e67c1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 13 26 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 26 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 30 indices rho q1 m1 1 31209404345159040000 17=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 30 indices rho q1 m1 1 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x81549999189c73e9e400,0x8c77151d94b0fd52c3700,-0x4837b8f0ef805cc62f9380,0x175de64f5c587c61fa794e0,-0x555ecb3000de6f50274e3c0,0xe9f1f09eef79a05d6591b58,-0x1f2e2a4cde4df5ab03808a60,0x34fad3f33aa745965977a5d4,-0x48d84b0f7e09fdcf16ea8850,0x51d9e8f1da8dfa8ffc60b6f2,-0x4b954b7834f16b3e0510cda8,0x397ac01989ae64b3a8437e0d,-0x23f5bad2f43b77b5d7a44b34,0x126db67c8f36f75d89d28550,-0x7ad4263eaf2c29128dd9b7c,0x291a59dabfda8b76267ada7,-0xadcd78e47e16783c0ed6f8,0x236909d0713e2a576bbcea,-0x55f83ecb24d5e834345c0,0x93be70df2a39f6391eab,-0xa61897e9a01483405c4,0x6ae81028fbae620b5c,-0x1e64a9aa26bd5133c,0x1f86e3d1e5d7c0d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 13 27 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 27 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 30 indices rho q2 m2 2 31209404345159040000 17=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 30 indices rho q2 m2 2 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x8969e332aa263b2882400,-0x9266b72a5b922ba4bfa700,0x49c6ffa9a725957de736480,-0x1760c663293cae0f0e3c50a0,0x53912f146cb2ac3a16c03ac0,-0xdfd3d76d08419bf7f3ddcf88,0x1d1fd2e608ce5fa674a5b0620,-0x304065920430ae2ecbfdc1ba4,0x4098e113e3661bc80592546d0,-0x468fa660c84c2d62c361ee89e,0x3f3a8d06bda42277603e76618,-0x2e90c98939a927656be9982b1,0x1c2554ab6fd8a6b07c82f1ed4,-0xde5d5465fd64c7f3219e4fdc,0x58f6e64c16e1970f926a2b0c,-0x1c7b9dac2dc11966525c758b,0x72b11ef2ab3db1a7d192a38,-0x161f9195e2d83720244c94e,0x327a224fdcee149dba5950,-0x50bb75cd62697f5d3c5b7,0x53572d04cde67b94a564,-0x304e5164473bdf40290,0xbfffc0cba888d2eec,-0xa5d50c1433c72e9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 13 28 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 28 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 30 indices rho q3 m3 3 31209404345159040000 17=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 30 indices rho q3 m3 3 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0xd7a9f489000,-0x1247cccfaf00,-0xb4a20f6eee0,-0x43499116c08,-0x10dfe78c724,-0x3027da172a,-0x64968aa4d,-0x9bc4bcc5,-0xb2e423d,-0x968110,-0x5a0d7,-0x23d9,-0x7b]
def m4 : List ℤ := raw_ints% [0x0,-0x92008165d4c89edb0a6400,0x98b55357eee16cdbdba1700,-0x4b7d1657e421f2789f94a380,0x1771996d001852d20b0c0e0e0,-0x520dcd6360cd92c3030229bc0,0xd6f6a275e331af571ef9b7ad8,-0x1b53a8943c5792032faa6010e0,0x2c2c7e4727e9f13828d85060f4,-0x399e4a0a43ca0314f722a1ccd0,0x3d3897c5317939df784a743ff2,-0x3543c2ae3bdaec7e7fb373a548,0x2601e1c31242a61d6dca063cf5,-0x16345f943c1f66f86c84ea56d4,0xa914bdc91422a287a022ccca0,-0x40fbaaabee6795dbff81fa13c,0x13e8023253f49ee6f01e926ff,-0x4c527ebd3feca19e120ce1b8,0xdeeed3c23a951bbcc9ef44a,-0x1ddb1c16a6f1e95c76017e0,0x2c64177d4a4def5f6f4143,-0x2a029ea6d09143d9b56e4,0x15e106e3b7ac037a112c,-0x4bcb234d792376293c,0x36730e2c64400d15]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 13 30 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 30 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 30 indices rho q4 m4 4 31209404345159040000 17=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 30 indices rho q4 m4 4 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x7b,0x1]
def r5 : List ℤ := raw_ints% [0x679ea87dd3000,0x8bb04c8808500,0x55a5609d516a0,0x1f9fb6a67f8f8,0x7d84aaf64244,0x161527516eca,0x2d51d743cf5,0x448e25e0b6,0x4c37c8ece,0x3d26048e,0x21f469d,0xbea1a,0x20dc]
def m5 : List ℤ := raw_ints% [0x0,0x9b20897c321528c8bb0a400,-0x9f68d9485b65a226695b8700,0x4d5b8c425f2d18ef106635480,-0x179028d13d1d9e7158dd011ca0,0x50cf6e8b274aedd1249d85acc0,-0xcf37d57453c2db8cb3d4a7f708,0x19c0d5bc1aa489d0035a03c7520,-0x28a551bf197d007199f9ab35644,0x33afba3b5e22f04674851550650,-0x357390cd95e3ec4a231df52011e,0x2d2d608acc17d98634cbf43bc58,-0x1f3fa770bd036bdd864530edaf9,0x11a706fd7fd216ab95d5bc73534,-0x81986c1d84975b0edc35cd0aec,0x2fdaf3e1645bf313e24e537dac,-0xe06db31e5f28c93cf7d6f2603,0x3333042580f5fd951420e9c78,-0x8d7b2a1441592d51c9dba0ae,0x11c81f19aad39241a541e3d0,-0x188ceaa4ce1a594dd03c3ef,0x1543c33285e9aefc798344,-0x9ede3a8edd9626b54920,0x1de919de775fb46c48c,-0x11db4ffd300b0ac51]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 13 32 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 32 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 30 indices rho q5 m5 5 31209404345159040000 17=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 30 indices rho q5 m5 5 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x20dc,-0x7b,0x1]
def r6 : List ℤ := raw_ints% [-0x1bae949f45bc000,-0x2523563707d3400,-0x16a3cce6990c380,-0x84d5ffaea4c040,-0x20adda5e47a9f8,-0x5b0d8d7a4d4d4,-0xb87f051e99e2,-0x1129594f2487,-0x12ad7e18806,-0xe8f201c4e,-0x7c31c3b6,-0x29079f7,-0x670ca]
def m6 : List ℤ := raw_ints% [0x0,-0xa4d29213f5367b5546bae400,0xa6879797ceb21ac59ff13f700,-0x4f64177fc684053e34635bb380,0x17bc5316a97c1233de309a5f4e0,-0x4fd19edba6e83725cd98c0351c0,0xc879f54bec6442f5c425edb4e58,-0x185feca3154362799e300164aee0,0x2595a130854d2075d235ecc63b14,-0x2e9f7797ecdace949810c68e5450,0x2ef42d85ea6ca92d1134173874f2,-0x26928f02299cb549762af2a86c48,0x19dfd5882356a99ce39850f0e29d,-0xe23797506f75040242bf4b72134,0x641a33b145a3e8a276b387472f0,-0x2385743c8814d750fc676726d9c,0x9f6578e3f80fe2307d79205517,-0x229cb2b9dff40629166893c5f8,0x5a71ef4e7d2c1692b6fa01faa,-0xaa8ed16022f3654a45d612a0,0xda694cc43aa39aa7075181b,-0xacdce38cc42e5df07adac4,0x48374e0238aacec33abfc,-0xbcc5dad2426bfb93d1c,0x5d97644b9801a5f5d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 13 34 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 34 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 30 indices rho q6 m6 6 31209404345159040000 17=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 30 indices rho q6 m6 6 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x670ca,0x20dc,-0x7b,0x1]
def r7 : List ℤ := raw_ints% [0x56d00424ce41a000,0x7401b9d69e145600,0x4663e750341d48c0,0x19abae1285a1fad0,0x64615349ea02228,0x11578b1176ac3ac,0x22ccaf19a2a1ae,0x332becc7c2bd8,0x36d9a7bb5413,0x29eb6e6c024,0x15c4d95498,0x6ef65ba8,0x10886df]
def m7 : List ℤ := raw_ints% [0x0,0xaf1fbb353489e30a9b2692400,-0xae1841cc39335aeec9f0536700,0x5198968604a1c28c81fce854480,-0x17f60ac9f0de44531968b78458a0,0x4f1097c65344a2d0e190219052c0,-0xc2a3c98124b072a89743d7210288,0x172aa999c20bef39a75aa3c942d20,-0x22ebdb84b33285194f742c4e305e4,0x2a4882db8c5df6b752f9fd8dd63d0,-0x297e087b5e67cb073bd4f3015cf9e,0x212580a47c5a6c4d43f76313f3dd8,-0x15928a616775cda18ad13a4b40981,0xb681040ddbd3dced79163a8ad314,-0x4de751e6cb8620a74b259312e57c,0x1a91819105af8e21e5d45375a20c,-0x7212f82982e049bf7763f1bbb3b,0x17928e3f147be2265717362f9b8,-0x3a389738d1dd452f812ad1630e,0x66e058506b852d92f7c6ced10,-0x7a0bab8e600c7a49fc89a1e7,0x581e4536a8b7f24f27644a4,-0x20debb59f4757b1ae7d330,0x4a6bab8a86ee14b06d6c,-0x1ea014ffba410f7df9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 13 36 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 36 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 30 indices rho q7 m7 7 31209404345159040000 17=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 30 indices rho q7 m7 7 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r8 : List ℤ := raw_ints% [-0xded8e30053b957000,-0x128cdcb3c7c841d100,-0xb3662e7a3b10eff20,-0x412112497a8dc0238,-0xfd50fcdebaf0558c,-0x2b7c628476f97d2e,-0x5698b2ef33e4e07,-0x7e28551bef1d19,-0x85ae986f4483f,-0x64b3e822fadc,-0x335588e5e05,-0xff57b0b85,-0x24ccfae9]
def m8 : List ℤ := raw_ints% [0x0,-0xba11b6e887d2813b44d8fb6400,0xb621f6a3ea5caf1a868f589d700,-0x53fb11e056eda7c64856d850c380,0x183d5592f7307212f03c3748da8e0,-0x4e892c82baf458fd52730ac7defc0,0xbd9fbd7f78854521cc79d3b94f5d8,-0x161bc0b97ab93c3de0d6aed83c4ae0,0x20996bd7a665695c78fa600bbb6234,-0x268cc8395a8a2efaadb95884eee3d0,0x24e11d9ac608197a867a50ff9803f2,-0x1ca9ce9aa69e92fd1b29c92d7284c8,0x121b5045ede077c0639782a9e9f485,-0x94472c020f103e09035c7e4493994,0x3d120d4cea2a33df2a3892e2ba9c0,-0x1404f5c2f32283baac799618b837c,0x523d79cae112683c333fdd193aef,-0x102b1099c18c48f271278fde5238,0x25b9bdd40be4b9a9e84fba91c0a,-0x3e693f3c8940181c12caa779e0,0x44824f09a8f02ff5ea18c32b3,-0x2d0d16bb59e5ea215a56a8a4,0xefa02c538b0dd039817f4c,-0x1d52097fbecb8f83f1b7c,0xa02cf5c3989e7294e5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 13 38 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 38 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 30 indices rho q8 m8 8 31209404345159040000 17=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 30 indices rho q8 m8 8 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r9 : List ℤ := raw_ints% [0x1f00953263a95ab1000,0x292ce60fb727256d700,0x18ce9e8f53f384458e0,0x8f8d2cb6c9d9ac2428,0x22bde73fe6a63a658c,0x5eed8a33fafda4fee,0xbbdeff981aa4fd47,0x10fadb27f716c7ba,0x11d4f09bd439cd8,0xd4905d4d09e1a,0x6adf03f276f3,0x20a4f9ecb36,0x499051ca2]
def m9 : List ℤ := raw_ints% [0x0,0xc5b2d257104fa94ef9268b1a400,-0xbeac46c916989888fef84e274700,0x568dbe0dc3a5d2a8d5bec53593480,-0x18924b775a69e09ba0b1ab8955d4a0,0x4e38b997eb7a4e8ef4f708239378c0,-0xb95b5c1489624a986f667d88b51208,0x152eb4e6ff63d59e7ef2a83b253c920,-0x1e922c1cc22243e48306cf1914ca684,0x2353b711480acc187167ce2b3a7c550,-0x20f70bee066fd1ed03683c674afc81e,0x18f04b9fdcbb4bf860d7359641e3858,-0xf4c1644e823609efa5a72b36a5f149,0x794c48112a6c12cec1ead09f61f5f4,-0x3036c41a8899dd17e2ec140eb4708c,0xf31627a3c21c6c20488437f9cf86c,-0x3bb5f6e06fcbb33225c44d0d0e933,0xb2a4f4557a0224cda2085ad51cf8,-0x18993247f1ad4459482857b7fe6e,0x2611416d41982da734cbeec6b50,-0x269e23f743140d2e6fc9f1c29f,0x17179d180c14bc8037f38d704,-0x6d4403c754fc7dbfdb3cdc0,0xb8b33357ba1120013724c,-0x344eaff18f3c60d61e1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 13 40 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 40 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 30 indices rho q9 m9 9 31209404345159040000 17=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 30 indices rho q9 m9 9 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r10 : List ℤ := raw_ints% [-0x3df90b3bab7f8bab2000,-0x521c70c6214127e5ae00,-0x31553ce43a27f66cd2c0,-0x11c8ff578bcf70bae430,-0x449cf30bfd6cc3dd0a0,-0xbaaa48a90945a34788,-0x16f8c9e1e41f6f4f8c,-0x2104fefa3f0d0888b,-0x226d5404e717f578,-0x196d42cd3cb09aa,-0xca5f19f832834,-0x3d0001b1f7f3,-0x872a3c3348]
def m10 : List ℤ := raw_ints% [0x0,-0xd20dff7c8154a3e3e8b8f3cbe400,0xc7bf3bf09598408e5ee7d309bb700,-0x5952fd89a51c8f1963fb08f2b3d380,0x18f5164610eac8b24591d64d0055ce0,-0x4e1d16df55e5b9ca55fd9b707131dc0,0xb5c6e0933bf31daf42f5d55b1af9158,-0x145fb6483508a046cdd06e6a5d555ee0,0x1ccbf41304329a9f1685d5de269e3654,-0x2089285ff41252ce2473d7bc5b4a2f50,0x1da0fd7ee61404c17de50889842474f2,-0x15d3e74d438c9940ffc76c208ba06f48,0xd0188afad5ecbf54428baab97ae7aad,-0x63e3be7d0feaf9c10774734e73864f4,0x26535ed492b3960fc7540680967cb10,-0xb9c2f6b8a1ee54c0fc19df7255be5c,0x2ba657e5b2d22ef010f714195d3287,-0x7c2bd4fab5040809c459357d65078,0x10226de30ebf10799a733d9af256a,-0x1756286f6a99a39c8467f3e0d520,0x15d9fc2bbdf443afb0be9eb3d0b,-0xbdcfcca8c47b3d377f3f46584,0x31d9eba16ff97f57611c8d1c,-0x48aa24d375f39a64f8d6dc,0x1110c3330683f3c79fad]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 13 42 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 42 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 30 indices rho q10 m10 10 31209404345159040000 17=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 30 indices rho q10 m10 10 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r11 : List ℤ := raw_ints% [0x71de348d664da01188000,0x968e80a6122e2729b1800,0x5a3d7c27d055a0ba42100,0x207191994232830df2780,0x7cc4bd9702c8c55949f0,0x152326af6bd435017330,0x2971573bb9aba26b820,0x3b45b1314510a25a7c,0x3d6f56bde939d82fd,0x2d0e401a1f35d950,0x163914e415948ce,0x6a129748135a4,0xe8095eead45]
def m11 : List ℤ := raw_ints% [0x0,0xdf2edf744969ee2227448308a2400,-0xd163606a8c87e31414d6503a572700,0x5c4d630028be9542d5990b7509f2480,-0x1965f128a6c50d89d720ddbe9dc0d0a0,0x4e348ba6f37d434fdc4e74f05ec8cec0,-0xb2d4d9e94bd09a10bb60a87666fdc588,0x13ab86bbfdff43fb273a2525091b9f520,-0x1b3e3e7eb2f91ec4fddc2a649f0c03024,0x1e1c81a43ec7300787aa1b2e0a03022d0,-0x1ac60bcc2ad46e2c9fcf8f71c134bca9e,0x133758ab372e84b2160ee1283718e92d8,-0xb206488e92929a8411cddc117e320851,0x52cb37706c3206d6928bb299d75c4bd4,-0x1eab31911f376a6dd844458e75edd41c,0x8ee89aa19cff76133c523f7912c49cc,-0x201e7aae7065e49d3a6591f132db5eb,0x56d8dcf40d31412dc4b10fa0b14238,-0xaa47b00fa5365b41aeda12acd52ce,0xe5fa2f539561bc129b9fca88b790,-0xc684bb19b3bb0e97102c1a82817,0x61b3b859fa5420f449b3358864,-0x16c09d16fdafba9c99d9ef0d0,0x1c90d80cb0667be6ada3e2c,-0x59008b4193d5a0b96209]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 13 44 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 44 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 30 indices rho q11 m11 11 31209404345159040000 17=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 30 indices rho q11 m11 11 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r12 : List ℤ := raw_ints% [-0xc379ea8bfcd0f6d7ded000,-0x101fdeb4fe7d7d83e24ab00,-0x9a50929de50ef9c3a0aa60,-0x37594a42f78e57137f6528,-0xd446ede8904c61bb9d934,-0x23d9950f113aeae2831a2,-0x4608f61451e41178e371,-0x63beb64f4a97abc749d,-0x66e07d137645fc85b1,-0x4b032e544d33b87f8,-0x24be8b16e4bf4343,-0xadef9408271581,-0x178aa4bd193e7]
def m12 : List ℤ := raw_ints% [0x0,-0xed21cd6b8e008d0449b8cb392c6400,0xdba1c72c22e67fc22623b53dfc99700,-0x5f7fb3b0ca6d5be19b27090052c4e380,0x19e528571d6804964da4dca8a48da90e0,-0x4e7dc4a6b4219761d26944f462560fbc0,0xb079dc9f908b500a52bd0c80fb58640d8,-0x130f632ee80f219237fd170c98fa8152e0,0x19e1dffb110702ddba97e5bd0a100d9f74,-0x1c00066d73b24c088ebb330326d5ec66d0,0x1852022b38d13f03940e221e400a44b7f2,-0x11035b7e100c758433224c2680fa826dc8,0x9937f44bb9bc6590f349cc93ec4843715,-0x450ea9d9916cde51042b9d6c04e4a2f54,0x18b355d05bfb93df62beeb1e8e0e4d2e0,-0x6ea7ea623dc8ff4e75e80463ab80c43c,0x17c8c6b1f86d556fcf8cffc6597ea1df,-0x3d1accabe2c5b55ec2ce466aa57f8b8,0x70eade61b83f9950fd9f3b2d2933ca,-0x8e45529675e747e7ecddcb8277260,0x7112f6c17f0936e0d3ea27f52523,-0x325fb9ea408698bac6847f23d64,0xa62ebb432f43d041a3ab8116c,-0xb388eae04bc0a271aa5913c,0x1cfc5b773efe3b3e9c1b5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 13 46 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 46 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 30 indices rho q12 m12 12 31209404345159040000 17=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 30 indices rho q12 m12 12 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r13 : List ℤ := raw_ints% [0x13d5115e4f3f7f89f529f000,0x1a2223fe7f242c4118051900,0xf9a6511389ecb4df0b78120,0x595bc6b788f7f90e6a868d8,0x155e812144faf430639f854,0x39962230b8cc74e434f372,0x70267132392250dbb4679,0x9f27b5fac676434a891e,0xa378ccc4c0cdd1ec2c2,0x769e41143aebd055c6,0x39c607068a8a940e9,0x10fa26b7604be7f2,0x24778c51ea8888]
def m13 : List ℤ := raw_ints% [0x0,0xfbf3ea4246e095d48e5457ecbf2a400,-0xe6841459d2ab063b1885f091dc630700,0x62ecea0100ac84fbde169f9710a171480,-0x1a7318ebe3cb4216e61c755e42cd924ca0,0x4ef7cb8939901e4f33cfad4d6995da94c0,-0xaeac4149a0793b7a2e894cdc770527bd08,0x1288f0e2d49ada72c2d4f646dc30f9e6120,-0x18b0cbc0d2f58476300283b95da8681cac4,0x1a284e17b707d6282d5cb3cda5ab5a73c50,-0x1634675db3ec915f954aa28ee55017ae71e,0xf255a471cd64555e21ee3798f085838958,-0x84a50f7639edb2f5baf51eeed472abe099,0x39f425382bfc5cf6f9b2a1d7998c9364b4,-0x1404d57280841ef74a4ae7c2c7cc10742c,0x56389f363a4940f06bcc6167917f4722c,-0x11b84c9a268f3fa4fb80db907649e5f63,0x2b3cdea4bf857a5df052320cebe82978,-0x4b4176932696c260ae28b157d6c482e,0x585f1b0eeaac09d5ad2dbb41ba45d0,-0x409691aaac0c66a8c2597a910804f,0x1a0239aa31ed703938b2535688c4,-0x4bddcd2c2ccf2cacab09728060,0x46778ee5686570b1ab11150c,-0x96e9c437eed2f7cdb9871]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 13 48 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 48 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 30 indices rho q13 m13 13 31209404345159040000 17=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 30 indices rho q13 m13 13 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r14 : List ℤ := raw_ints% [-0x1eb89c99e3c4a9ba6cb0c8000,-0x286cd21284fdbfb9e24230800,-0x181902434b4a63a6ed2d0ce00,-0x89c1e2a546009b6fe93e2320,-0x20e021d83bfdf426de348248,-0x5862f8514689adbc807d7fc,-0xabac28e75f760bb4006876,-0xf2e03a12f3062a1a0f6cf,-0xf894733648a3a37db1aa,-0xb3a25ba564ec36c8d46,-0x5712ca35e51d0ffd72,-0x1971877ea3d8dbcaf,-0x364a0aa61b65c06]
def m14 : List ℤ := raw_ints% [0x0,-0x10bb328e66b4e9f31d7399d6b8b1ce400,0xf214865a5d6bd51b9a0e4f9afa2937700,-0x669838417c1dbf583d2d5d36ced0c3f380,0x1b1030d5c33aebbdc5bd9cc0a76caf344e0,-0x4fa1ffd1efdb1aa064d014c02028af189c0,0xad63ed5b4aeeb973a730061437522bd2458,-0x12162dee8106ea4cc8e47fec1921b14fc6e0,0x17a5e38a1a0b26eb2c4000b8991aad9ce594,-0x188bd5b86dc7e4b47b11024d8f9e7133aa50,0x145fbd6b3ffd5b4b057146ad2972ddcbdcf2,-0xd8e6947e68c0a83fd41a44c4454a315e848,0x737dd7a33301e4626516c9009eecb5da3bd,-0x30ed1a9acdc52f2d63b7626fdc77ebc40b4,0x1052dbec66a13acc001a5f5e2b71bf3e530,-0x439747cbb6c6f6c9771e085c3c481ec51c,0xd478796d403e9f4154f54c6ea1a0c4ef7,-0x1ec2fdbd66cde891dcb899a0e3b51baf8,0x3264bfa7bd4039b5cba610618bb66f2a,-0x371951c797bbf19f11685ee884d19a0,0x24fc8df5ed144e685c3386f88710fb,-0xd71c2dbde8f9313468f6355cf844,0x22a1feaae90bef1205ff656d03c,-0x1ba2d72df9d57491b41434a9c,0x31117f347dcd6215e70cfd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 13 50 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 50 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 30 indices rho q14 m14 14 31209404345159040000 17=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 30 indices rho q14 m14 14 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x364a0aa61b65c06,0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r15 : List ℤ := raw_ints% [0x2dbc39ae28708fbe442f736000,0x3c1b61b139293822980eb59a00,0x23c7a07c3cfa2a8cc812bf1140,0xcc36a87110c77ef70dc1a9a30,0x30a5a619b7679dd91acbf77b8,0x8285369b1788745fad662e34,0xfcea98cb849f511dafc8a12,0x164dce12db8e42cf5176220,0x16c20e1079430794bf2fe7,0x10635bc5566e6dbf225fc,0x7e955fd12dc6c3c0e84,0x24d04bf7088831f1a0,0x4e1d4742574faaab]
def m15 : List ℤ := raw_ints% [0x0,0x11c6e5b74d2038924f4ad374243ceb2400,-0xfe5dff7af0d8b0ea23af3494a9cbcae700,0x6a850ba88cf74a1fd2ae31762410b810480,-0x1bbceee5f7f8372c22c84d2e8451eaee48a0,0x507c10f3073f17683be03651d1ddbd4d4ac0,-0xac9a24b6d5699a5148294b8ba4c54e909888,0x11b5645ec16d354b50df3c43b1887f8dfcd20,-0x16bcd059bf66279b4c337408eb69f51299e64,0x1722a81a2f91450c05de245807f34de19f1d0,-0x12c8eb0dc7a661edcef68451151b1ff1d6d9e,0xc327e3d5b74e49bd944e46dc0ac55bd86bd8,-0x651e323d9a92ccbbcb42f8e498c9f3128c21,0x298b9411153671a3175b0d813275fd719894,-0xd63b57a7beb2ad3557fa39a7b5435e044bc,0x354c5b693e53773f68ac2ad44a66278198c,-0xa0209314a37c56205c279955bf457a739b,0x15ffc96bfd3984079835b69a4f268322b8,-0x21e55a193b8df434b0d16f9629ab4268e,0x2279247cd803fa70c604c491b1e2b610,-0x153a766a45597b3bd3317960a4f1947,0x6f4d390324d453d7f330a4b4cd024,-0xfcea5de86947d7641f712429070,0xad47093eafbf5dd174c739eec,-0xff1236e0cbae048d57af19]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 13 52 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 52 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 30 indices rho q15 m15 15 31209404345159040000 17=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 30 indices rho q15 m15 15 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x4e1d4742574faaab,-0x364a0aa61b65c06,0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r16 : List ℤ := raw_ints% [-0x41ce72ca77b5e9a5f0305183000,-0x5663b66733ce0770c438a7c8500,-0x335c533c3a2d6ac6ef1c7fcb5a0,-0x124ba23d7192d3f6a26cc196818,-0x459eff40d5aa7af61f02ec52dc,-0xba74bfd5fe6569b54a485e616,-0x16890c0fd14cb468c203db85b,-0x1fb91d98144a35a7ab620fa1,-0x2048766127c292fd12fb923,-0x172d30e5187bd43fc7fe14,-0xb264aa954c4170ed6601,-0x33ac103b85d758852fd,-0x6d20ed7063d4e63e5]
def m16 : List ℤ := raw_ints% [0x0,-0x12e35412c1f23c1b743f80ab6680b9d6400,0x10b6c102d8d7c5a7595ea27ddf4688795700,-0x6eb70f8473b4968cfaf83312b01f7cf10380,0x1c79e2f8fe6e0c22e30eba3c78a17a6f778e0,-0x5185f96cf2955955f0f89b32dbf368fa247c0,0xac496292302ca7c671d246cfaa9c0193d5bd8,-0x11651f808023d047333437104e86da61533ae0,0x15f1e2651821f3df7dc53dd3a3e339d9ef10b4,-0x15e6171083cc5a06e2437cbd2442e9fa80d9d0,0x1166c5200a543b164104f6a1963e947351f3f2,-0xb07d5defc1ce59b2488ffddf8bb60e2f45ec8,0x5903ccabf83ff7cba7e26437ee0989538eaa5,-0x237a40bff540f5c283a7c4109dc37a7ec7114,0xb0bc6440eb739fd79ddb2b2c820234a6e600,-0x2a4472d043dea7d2e585f56d3ded729a58fc,0x7955d821f82b6f1e9eb162bfe327d742fcf,-0xfcf7db4de83e36d6a0c10f38144d036738,0x16e51c2d0c7ed3329aed49e06dfa2fff8a,-0x15a3366dbab883c39b0f2774d4c757ae0,0xc355d66b34341ea11ee49b8ce3d3693,-0x39a254561f86f4bfc9f92667708e24,0x736881b7ceaea71df0ed0b64cd8c,-0x43d96b60be83de18647a47bafc,0x52cf33fc00dd6b7d4abe385]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 13 54 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 54 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 30 indices rho q16 m16 16 31209404345159040000 17=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 30 indices rho q16 m16 16 31209404345159040000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_16
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<17) : intPolyRF (mz e)=rfPoly (C (31209404345159040000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^e) := by
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
#print axioms moment_source_16
end
end CatalanCore.Li2.NVMod.FamilySource.U4C17
