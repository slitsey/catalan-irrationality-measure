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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C17
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,17,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0xcafa4f9000,0x10757ad2f00,0x9a844fa1e0,0x363d74cfa8,0xcb1003bbc,0x2160cd0ce,0x3f41a3ef,0x571208a,0x566c4f,0x3c582,0x1c25,0x7e,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x23,-0x230,0x762,-0x2958,0x8af6,-0x7f9e0,0x2a1fa7,-0xaebc3,0x22f27,-0x127c0]
def rhoDenominators : List ℤ := raw_ints% [0xad4,0x7,0x4,0x3,0x1,0x1,0x1,0x7,0x1c,0x9,0x4,0xb]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 17
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤16))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤16 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 17 omega5=padCoefficients 17 (omegaCoefficients 16 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 16 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 17 omega6=padCoefficients 17 (omegaCoefficients 16 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 16 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 17 omega7=padCoefficients 17 (omegaCoefficients 16 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 16 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 17 omega8=padCoefficients 17 (omegaCoefficients 16 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 16 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 17 omega9=padCoefficients 17 (omegaCoefficients 16 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 16 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 17 omega10=padCoefficients 17 (omegaCoefficients 16 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 16 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 17 omega11=padCoefficients 17 (omegaCoefficients 16 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 16 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 17 omega12=padCoefficients 17 (omegaCoefficients 16 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 16 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 17 omega13=padCoefficients 17 (omegaCoefficients 16 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 16 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 17 omega14=padCoefficients 17 (omegaCoefficients 16 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 16 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 17 omega15=padCoefficients 17 (omegaCoefficients 16 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 16 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 17 omega16=padCoefficients 17 (omegaCoefficients 16 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 16 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 16 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 17 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x3415bcac1c4000,0x372cc6cd922d0c0,-0x1b9ed37a7d4da7d0,0x8af501dc42b21d80,-0x1ec490009d72d7044,0x518e79e0ba948c8c0,-0xa7c1226504259ce74,0x1120b357549fed1260,-0x168e636d02c3da1061,0x182b1bfe87449fda20,-0x152b9836b8db5c4849,0xf2d17c00ae3f2d9b8,-0x8e1ab5b3164ebe895,0x437b293b887019548,-0x19bccf40c8eb96b5d,0x7c3a21bb89bd3c10,-0x1cfd519460f51f93,0x5115056de377470,-0xa1fac74a82ed3b,0xd6973c65000d8,-0xa63c694d2df3,0x3adae5a9c28,-0x506ac521b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 12 25 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 25 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 29 indices rho q0 m0 0 2130000364800 16=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 29 indices rho q0 m0 0 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x3415bcac1c40000,-0x361df9c99f562b40,0x1a8cbbf8b7117fe30,-0x82c91802dfa72e5c0,0x1c53ae23ade14e029c,-0x495e86afd8906ee030,0x934948c77a8335a174,-0xea8297049e781319e0,0x12c8f50c24a8bc26ebf,-0x138e1ffa23008d398ac,0x109c3246bcdb467e5b9,-0xb854ce6567abad14f8,0x681b4e5c84562af27f,-0x2f90c118a5de41b784,0x116449209c8da1ad41,-0x501f034d3330dd9b0,0x11bf7d55f9c278165,-0x2ecaccc293841c34,0x574d9076a6d28c3,-0x6aa4b9604ea4b8,0x4abfe78d9c641,-0x173c5bab852c,0x1a7cd4891f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 12 26 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 26 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 29 indices rho q1 m1 1 2130000364800 16=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 29 indices rho q1 m1 1 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0xcafa4f9000,-0x10757ad2f00,-0x9a844fa1e0,-0x363d74cfa8,-0xcb100397c,-0x2160cc76e,-0x3f41939b,-0x57110fe,-0x56636e,-0x3c262,-0x1b7b,-0x6a]
def m2 : List ℤ := raw_ints% [0x0,-0x3415bcac1c400000,0x35201995ebacb88c0,-0x1990797e3b378022d0,0x7b68a71a6221d99e40,-0x1a2ae5024bca54a8d44,0x42477ba86cef6df8bf0,-0x81f4772a1746268ee94,0xc9d2144afdb30ad0b40,-0xfbe85294efb24ac4541,0xfef15fe559a16c44d5c,-0xd21bc0f430974b21c71,0x8d12c23cb37b4406e70,-0x4cec9533ec1f87191f5,0x21d36c0bc4605295c0c,-0xbdbd639d4b76b42725,0x3424538978fe014900,-0xaf602842bb9fefdf3,0x1b395c75f1a75c2b4,-0x2f639cc4ce14e273,0x3549ce3e900e910,-0x21b764d7653b53,0x92cc54df3534,-0x8b67462ad3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 12 28 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 28 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 29 indices rho q2 m2 2 2130000364800 16=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 29 indices rho q2 m2 2 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x6a,0x1]
def r3 : List ℤ := raw_ints% [0x540ba4f1a000,0x6c3f5365e600,0x3ef3714bd7c0,0x15daee0e59b0,0x50b0ca3ec30,0xd0704e3bd0,0x181b211988,0x20195e589,0x1e57c7b8,0x1396466,0x7e4f0,0x18b1]
def m3 : List ℤ := raw_ints% [0x0,0x3415bcac1c4000000,-0x34321765733ddd0340,0x18a81848af59b956e30,-0x74bcc88142b0ac26640,0x18408f4c27a5e7aa069c,-0x3c1e10031b8a693ca6d0,0x7336f4c4d30cd0c36454,-0xaea604bd89881b1dfda0,0xd4712cdcb723d3c7481f,-0xd1276e0f72c89c2dadf4,0xa75756607933957985d1,-0x6cd24c9afca1673e52e8,0x394fe15f514c7e8f31ef,-0x18431c4d4bdcbb05771c,0x8281fba729df0f0e2c9,-0x223a70c66fbe45c2e10,0x6d37d6d00b6e1b2de5,-0xff638f92642da8cac,0x19e5079f363f698eb,-0x1ac2b1ddafc84f28,0xf3f9d094069ff1,-0x39f60b16e0034,0x2dcbcfc6d77]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 12 30 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 30 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 29 indices rho q3 m3 3 2130000364800 16=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 29 indices rho q3 m3 3 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x18b1,-0x6a,0x1]
def r4 : List ℤ := raw_ints% [-0x1393ce86829000,-0x1912403633df00,-0xe7afd9ed605e0,-0x4fc4fffef7b68,-0x1238378b4934c,-0x2e7765cbc23e,-0x5497372846f,-0x6e432355e2,-0x654526516,-0x3ec7f72a,-0x17d892f,-0x4422e]
def m4 : List ℤ := raw_ints% [0x0,-0x3415bcac1c40000000,0x3352f5580255ef330c0,-0x17d1d6a01b7094d0ecd0,0x6eb17e57e45524777b40,-0x168c7a4352c037e2bfe44,0x36be650f4113d81520eb0,-0x669fce5fd0798feb4c374,0x97f296721a3b37273cf40,-0xb43ddca19d2429ca994e1,0xacbb0725633352325864c,-0x863d4e7a8ca7596a90a09,0x5496861d87aefc374b7f0,-0x2b0b68919252f87b245c5,0x118c223c71c96d21a8cbc,-0x5a8635c8eba22c5bfc4d,0x16a81eb5d6828d325280,-0x448ff83c9055b5dfb73,0x96d5e22e55de545004,-0xe3cc541d2d2e68a5b,0xd7fe5ffd95804310,-0x6e9678ea04e5863,0x16e1239bbc0584,-0xf06c502d24b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 12 32 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 32 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 29 indices rho q4 m4 4 2130000364800 16=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 29 indices rho q4 m4 4 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x4422e,0x18b1,-0x6a,0x1]
def r5 : List ℤ := raw_ints% [0x360623fbd6be000,0x44dded29cb9e200,0x278f0de9f56f740,0xd8806cc8509a50,0x310f9acc71b860,0x7bebf0ea60db8,0xdee973ff50b4,0x11e3336ce85d,0x101c58c7e50,0x9bb4e9c46,0x3912a17c,0x9b0975]
def m5 : List ℤ := raw_ints% [0x0,0x3415bcac1c400000000,-0x3281c56b687c803fdb40,0x170c1f5c7c15efb167030,-0x69354bd3731465f335a40,0x1507a902a030f8d685069c,-0x320aa5031c5b6224686750,0x5bd34c340d16cb300c2eb4,-0x84e37f7ea8fc8d2c771b20,0x99d1e510788a207e83b5ff,-0x8f929b2a26ae8038df6914,0x6c7089ca4a7ada2b985449,-0x423dd7cc30988fac31cdc8,0x2094f0b540015260c5dbff,-0xccb1878bc7c5c03cb059c,0x3f4d541a8b6d1205ce551,-0xf1e1a83b37a0a85c6c50,0x2b5eac26f8a94c73d325,-0x59b3e3112d6e25d45cc,0x7df8a92273eb46a473,-0x6d67bd9907142a888,0x323859365efc3dc1,-0x9071fe48eb00f4,0x4ecb9a79298f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 12 34 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 34 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 29 indices rho q5 m5 5 2130000364800 16=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 29 indices rho q5 m5 5 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r6 : List ℤ := raw_ints% [-0x7aed0dbd626cd000,-0x9c1b6e0be0619b00,-0x5945f2a9aafbf960,-0x1e6045ce4d10d888,-0x6d722bd49b84e9c,-0x1125de2277af3c6,-0x1e90556ad24583,-0x26cc8b667685e,-0x227391b65ebe,-0x146f3d4581a,-0x750228da3,-0x133c061a]
def m6 : List ℤ := raw_ints% [0x0,-0x3415bcac1c4000000000,0x31bda87d9840a83bdd8c0,-0x1655850e3496e45e2872d0,0x6438dd07d69183080b9940,-0x13ac22704f5e608a14d8b44,0x2de9e81ddc8fa894e333bb0,-0x5286a0996f7332494a06254,0x74cf9d280b184fc2a6077c0,-0x84054e6069ccd03160c2981,0x78164a5f391a907330fd90c,-0x5831c1337dc8a61c8fb4e21,0x34400c9121a0ed850eeb190,-0x18d96e863c553ddaa227cd5,0x9666cff76eff0764c18d1c,-0x2c9d3beb24f49dc9e04e35,0xa2a3c86c9b8978fdc4840,-0x1ba2646e080421652c473,0x35b2226025dc82da8484,-0x4608de88965e2b3d443,0x379e70f958db6de530,-0x16d7387fac02b7db3,0x38f76c8619810e4,-0x19cba9c874683]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 12 36 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 36 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 29 indices rho q6 m6 6 2130000364800 16=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 29 indices rho q6 m6 6 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r7 : List ℤ := raw_ints% [0xf402b68d10974a000,0x134e53a0239843f600,0xafff12c6cfe0015c0,0x3ba016b13731f0db0,0xd5bc881ea26ba090,0x2149087d7ac1ba50,0x3ae562cf80b4c80,0x4a1bb9a7c64481,0x41184986d71a8,0x261775c4bc76,0xd6648361a8,0x227687329]
def m7 : List ℤ := raw_ints% [0x0,0x3415bcac1c40000000000,-0x3105cd5ea5088db81fb340,0x15acbdb5cbb8fb4b22cfa30,-0x5faebbb938e5a2e914f8c40,0x1274c7e028eb97c29318329c,-0x2a475148e8beb6ff8fcd3750,0x4a7c86a3978fcba7e85d3214,-0x672f81be98ccca008783e3a0,0x71f08f7297e0a6c34658dfdf,-0x650ea2908d1b7a1316815194,0x483408016b56ac9eee7cba01,-0x29810da6020f2bedf9174968,0x13176e5bd7f1efedcc8b840f,-0x6f586256c4f7b3738f91ebc,0x1fae99c38d292a2724ea219,-0x6e2b392dcf7a4597981810,0x11bb0bd5d52e613ce50e65,-0x20572a808fb0e8cedb58c,0x27210431fabf84cb07bb,-0x1c5e11d39c53de436a8,0xa669e87646d8c3791,-0x1673f91fe1a0f794,0x86f971ccea367]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 12 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 29 indices rho q7 m7 7 2130000364800 16=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 29 indices rho q7 m7 7 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r8 : List ℤ := raw_ints% [-0x1b533923e36546e1000,-0x227f8fc6c42e564e700,-0x139837f07ce413496e0,-0x69d4769c45473da428,-0x179c23b321e91ff76c,-0x3a892f2bedd1e5a6e,-0x66f70e79257de3f7,-0x80a5f43f6c0e79a,-0x700aa741d09126,-0x40e2024b6962a,-0x1687a8ec6477,-0x3900e54c86]
def m8 : List ℤ := raw_ints% [0x0,-0x3415bcac1c400000000000,0x30596ff1a103f4dc9db80c0,-0x15109ef9c44cfc22f1ea28d0,0x5b8b0f2c34e6cdee1e150b40,-0x115d32cbb5b05052d56c27444,0x271156adcb11d0b8caff981b0,-0x4382999c20aab5c618072e834,0x5b9635bcdf8bbc8dd91135640,-0x62dd85dc7461de7aee08afc21,0x558c5a036fdf1bb5fa76c530c,-0x3b7ddf9b5f31683c426a996f9,0x2131900999aee675dc43da0b0,-0xec5cd56b6ee203a65bba4a65,0x5308dc4bc9438fce65ecb93c,-0x16a9d2a786f5d2a640dba45d,0x4b284fa48b91ed9137aed00,-0xb73a64da707a37d5cc8a73,0x139766a9cf2502b5c667c4,-0x15f61b391d6cf4224cb6b,0xe829208e2d4a11380d0,-0x4bd9b0ad2d12952d83,0x8d803b5c742ad984,-0x2c189941a3357b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 12 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 29 indices rho q8 m8 8 2130000364800 16=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 29 indices rho q8 m8 8 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r9 : List ℤ := raw_ints% [0x2d327185a5ba74656000,0x38ee3ddd5e94052c8a00,0x204007252a01cdb85440,0xada5c1864ba58ddfb10,0x2699ff4d0fcdfc97040,0x5f4e9523d637d87c68,0xa6d43361860b368ac,0xcf3e101364d41c45,0xb340bbbc14e3dc0,0x66f2ab8c1568e6,0x2363610cc2134,0x586c7ef457d]
def m9 : List ℤ := raw_ints% [0x0,0x3415bcac1c4000000000000,-0x2fb7d85b6d3fa58ed3dc8b40,0x14801acb7cdf46dbb3ea16430,-0x57c36540d8c23d44589bd8640,0x106198566f48f0c4b21c5a2a9c,-0x24392d3c2890e0941f61902550,0x3d6f3b8d4749a423b538360c74,-0x51aba1bce6918ef9637e680c20,0x563c25d8f0d3ce5505418933bf,-0x48d67c7b22092f68e130b96b94,0x315312dd30ab15b70483da4879,-0x1ab93cd00dc43f7dfa9eae3108,0xb8296485a999a21c41ee84b9f,-0x3e5c87c6974413b364bc9a75c,0x1053a1967e10eae0aeae3b821,-0x339f8499c4ad58b2f1d7cfd0,0x7716ed50f5e70b1a3a2aca5,-0xbeed02f14b5f28b51dddcc,0xc60a2fd0ccd9ae8da8643,-0x770d253edd856e9454c8,0x2298aaafae90b33d0e1,-0x37b1bf33a61d846b4,0xe646d3d613b0ff]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 12 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 29 indices rho q9 m9 9 2130000364800 16=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 29 indices rho q9 m9 9 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r10 : List ℤ := raw_ints% [-0x461c119c001cb1aa95000,-0x582298055e9b4e9d59300,-0x31d013f401af54c76e060,-0x10b81c885b674262158c8,-0x3b4934a56b3c0cdcdbbc,-0x91dcbeb9e146b120a56,-0xfe47617c263184fa4b,-0x13a5d68a866c24acb6,-0x10e5fab3e9751114e,-0x9a3d25eb7233cba,-0x3497ad85194e2b,-0x822056f81252]
def m10 : List ℤ := raw_ints% [0x0,-0x3415bcac1c40000000000000,0x2f205a3e9cb79b35e69ec28c0,-0x13fa3c6dd97f05998ba632ded0,0x544e836b5934e5a1833924dd40,-0xf7eb19302d94e6c94386f61944,0x21b2500da3777ee20906017abb0,-0x381feafe3215ea7931b740ce114,0x49283a7fd2e05de991edbbbf0c0,-0x4b99ea56bd7e6da59acc45b20c1,0x3e5d3ef51cd9f2f406b8b041e0c,-0x2924beca2b21571a8bc47ad1b91,0x15a758881133a77806eb90faad0,-0x9074b7364a2560cc87b6b14775,0x2f283bb7e1e5c638d24214cd5c,-0xbd7923e91e585086bcdf5bec5,0x23b0d7d9d7f2c953377115bc0,-0x4dde0b04c29e30a5b6fc4b73,0x74e24ddd6addafd9b24b404,-0x700ae3e34caa23969c7ed3,0x3d2f064f38d5549cbbb70,-0xfc99f557eb0c1691cd3,0x15e7908f49e1147c24,-0x4b16e4c613c7d33]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 12 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 29 indices rho q10 m10 10 2130000364800 16=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 29 indices rho q10 m10 10 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r11 : List ℤ := raw_ints% [0x672cc0a5d9be11459c2000,0x817a094467d448b01dbe00,0x49088bf8000e9d220e06c0,0x18750e2e01d2a8344d7370,0x567fac599add996450170,0xd42cc46b1b4b657c8240,0x1709870596fb8f034638,0x1c5db21f00362b125e9,0x184814797b39af9298,0xdc665102afb75656,0x4aa85d0fcb86120,0xb743d48ffb631]
def m11 : List ℤ := raw_ints% [0x0,0x3415bcac1c400000000000000,-0x2e925403993811828834d66340,0x137e25d217f88e06138735f0e30,-0x51243e5819dffe9796156e37040,0xeb1a7b1522b3374a6be974c4e9c,-0x1f721e17758d7bfdab14dd684b50,0x3377ef79822a26f910c23adc2dd4,-0x41d1a257aebefd80265d07fc48a0,0x429b50d249a7616e3a32fa3c199f,-0x35b0341a627c8af2a5577a09ff94,0x2285bb9db11795e2837194775bb1,-0x11a7e6f2dd4c3fa525fe5da6c9a8,0x720d57fcd921357528bd08124af,-0x23e5b5b5997f41c98e13e49b2fc,0x8a55ba52e6864cd4f362c81d69,-0x18d4b6a3ca9bbfd4dab8cb3d90,0x3334511e67b98b327b11779e5,-0x47e5b95a8e9ebde578655e0c,0x3f9c082ef08023111d9f80b,-0x1f80f2e8b0fd5825f4c7e8,0x734e839e11fb87d743b1,-0x89bbbbbcc57b8648d4,0x1876b93f07779857]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 12 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 29 indices rho q11 m11 11 2130000364800 16=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 29 indices rho q11 m11 11 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0xb743d48ffb631,-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r12 : List ℤ := raw_ints% [-0x914eb6ec35b7a8ee99a9000,-0xb612a75d46aea6572f3df00,-0x6685e545c1966947e557de0,-0x2243c4dfe9c383fc5472868,-0x78e93249a701703779a38c,-0x127d0fdb3478cdabd369fe,-0x2005e29cfe629e3b0c87f,-0x274b6f28f29c223c1032,-0x2180a074f99398abf36,-0x12eae791cfc1f1a74a,-0x65f82fd4d52b5abf,-0xf8b058f1234afe]
def m12 : List ℤ := raw_ints% [0x0,-0x3415bcac1c4000000000000000,0x2e0d2e2c45f0806a5fb188fd0c0,-0x130b0d409939cad30ed6bc09d4d0,0x4e3d5739a0d05924bfa318e2bf40,-0xdf803656d997706c37abb5c35a44,0x1d6f89c5640f730fe9f4e173925b0,-0x2f5f4a1a14c9162c73640726d94f4,0x3b78066f4ebe61956f42cbe3c7f40,-0x3af6dd0256dd51960828eb005d761,0x2e76f88a9780c1a03f301f215510c,-0x1d2225064b6615b4b1d9c985875e9,0xe7bed783f32664802a4c0411cdf0,-0x5a9ea6a737b8c0fca3d5be3d5405,0x1b809b869e30b07e49e89a00327c,-0x65a43271221e033984f1a2acf6d,0x116131f0dc7dcbea421c4f5f080,-0x21da7460caa610ccdf5bb23773,0x2c6c0e7f3d8bf6962fa4ff244,-0x243a068517ccd22075f24c7b,0x103f69be10ab448930b3310,-0x34a489d31dce334e4dba3,0x3615d4fd2999d10a3c4,-0x7f6a1fc07ae6abab]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 12 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 29 indices rho q12 m12 12 2130000364800 16=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 29 indices rho q12 m12 12 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xf8b058f1234afe,0xb743d48ffb631,-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r13 : List ℤ := raw_ints% [0xc52e4faf6ffa15300a90e000,0xf6bd6c1c0654d7fe90d01200,0x8ab97354c31b0c6fda797d40,0x2e4887ed54e6bd35cb8f1ad0,0xa2ffa04d50ab36610ec7420,0x18de31a58ea1623d7c314d8,0x2af61a0f2db52f795d5324,0x348f9064268f792d3646d,0x2ca905dc006c5c9f3c30,0x191e501828b4410cbc6,0x86c53a56af45bf76c,0x146e9bf1da338e45]
def m13 : List ℤ := raw_ints% [0x0,0x3415bcac1c40000000000000000,-0x2d905ab267dd6863b9b6706d3b40,0x12a03b44a840571d8ee04a9237830,-0x4b935de7d91b601227fef3cd06a40,0xd4f9ef85a4c320a8e6788227dfe9c,-0x1ba2d7036647e81576373aa4f59150,0x2bc1dba04d24e75adba7947dc08e34,-0x35f40c9719e17013b3d1e8c8698920,0x3471433514e20ff1d067e7a847e17f,-0x286bafa3fc4cbfafddd59c63bb2f94,0x18b92033bb78d8fa56f18b64efc9a9,-0xbf3e52786c6aab5e9eec211f60f48,0x48723b7fec7ff64530a242631833f,-0x1533d741b828764348fc98c9db79c,0x4b23ba596c80908e0d3119ca33f1,-0xc3c15cb0d30f43c1e198ee9b950,0x167f1cfa1276285ee6baaeffe25,-0x1b8f5ab5155e9b49d923a6844c,0x14b0bbd4f893f5dd84262b713,-0x8641d281731674a39036c08,0x1808bf31ee8d170c0da401,-0x1538a65c53320579eff4,0x29712721b7e038f6f]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 12 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 29 indices rho q13 m13 13 2130000364800 16=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 29 indices rho q13 m13 13 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x146e9bf1da338e45,-0xf8b058f1234afe,0xb743d48ffb631,-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r14 : List ℤ := raw_ints% [-0x1033416ac0b31efc074951d000,-0x143f734f469d3674f3042ecb00,-0xb5e5bc6d781af36a14410cf60,-0x3c9831f8967090487efa9ab08,-0xd50745ff9c8cd64a091746dc,-0x206fc51f47290fb001641766,-0x37e927144bf95afcc79ac93,-0x443a5d56f4e8ffbdaafe0e,-0x39cd454e90c0a4e489ede,-0x20664c25dbe8c8d91bda,-0xad28097b46e8f25033,-0x1a21d1b9e71040e8a]
def m14 : List ℤ := raw_ints% [0x0,-0x3415bcac1c400000000000000000,0x2d1b547027ab81dd7e1b0966678c0,-0x123d08d35d74b18470ca60e8f40ad0,0x4920971a18613c22adfa4e7faff140,-0xcb69a8dbbe378544a35d45557a1744,0x1a0564f2222d52776ced4a37ac49fb0,-0x288eb4d39a229fc3c25d30dbb0bfbd4,0x312530c2add401cca7a4a88488481c0,-0x2eda717bf76f4763ae3dc4e939b9001,0x2356d7c1ee53b6d03b1518191cda80c,-0x15184091f581f6a337a716c9766bc01,0x9ebb770721b6723155d9639a4d8a10,-0x3a43d229f263fba9c173b0a0b50c15,0x1071e2109b312b5ca079e03de0f49c,-0x37e0803205666b7adfba000402055,0x8a9165b55f0fd19dce22e5e48b40,-0xf05a56b8cb263c05609ed8d8673,0x112a06ae9ad7083cb7a34f6f684,-0xbd8e176677822f558ec885e63,0x456a6e6496ed97f3e95647b0,-0xaf8c6eaf61829c98c905f3,0x851e3ae074194eb58464,-0xd77f5d5ff06067ee3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 12 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 29 indices rho q14 m14 14 2130000364800 16=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 29 indices rho q14 m14 14 2130000364800 16 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_14
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<15) : intPolyRF (mz e)=rfPoly (C (2130000364800:ℚ))*rfX^16*(1-rfX)^12*momentRF (key size) (X^e) := by
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
#print axioms moment_source_14
end
end CatalanCore.Li2.NVMod.FamilySource.V5C17
