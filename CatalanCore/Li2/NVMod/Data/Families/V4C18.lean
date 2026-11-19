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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C18
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,18,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14,15,16,17]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x35ea7d224000,0x5699d2874c00,0x3f7050ab6a80,0x1c1c853c9f00,0x86c92f48898,0x1ce9de12ccc,0x494d7ce81e,0x8b87be811,0xc87e143d,0xd88798d,0xad19cd,0x63603,0x26bf,0x93,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x7,0x23,-0xbd,0x7,-0x79,0xcc3,-0x18f65,0x22f27,-0x49f,0x49f,-0x7e7]
def rhoDenominators : List ℤ := raw_ints% [0xa4f5b0,0x81f0,0x268,0xd8,0x6c,0x64,0x1,0x7,0x70,0xbd0,0x1518,0x58,0x129,0xf15]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 18
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤17))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤17 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 18 omega4=padCoefficients 18 (omegaCoefficients 17 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 17 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
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
  | 4=>omega4
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
  change m∈Finset.Ico 4 18 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_4
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0xa3549bc26108400,0xc58c8c8098e06300,-0x719ff07d788709680,0x2955db2682c4602c60,-0xaaba8f8a1ca67dbda0,0x21422d9b01391d37018,-0x513635b04a4a7400278,0x9f32aa7bf40879ff2d4,-0xfeab668d8cf4d3979b4,0x1501f588737c9d50d822,-0x17091e689e9b7c30d01a,0x15108ed88438b3a458dd,-0x10144a5b2213d4ce4fe5,0xa3a8744881ecbb0cda4,-0x5662c61186793ab7fb4,0x258f2150a906929d26b,-0xd4e110b3a0f36fc1fb,0x3c7ed87509d041dac2,-0xd7e8f589d28b6b65a,0x24a78c47ed3492ba3,-0x486d03035269e74b,0x611575eb20edc40,-0x4e803d135f2040,0x1e7330d6f6a01,-0x31caf7a9c21]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 14 25 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 25 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 30 indices rho q0 m0 0 1403883240439680000 17=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 30 indices rho q0 m0 0 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,0xad89e57e8718c400,-0xcd0baea6c4d483f00,0x731e46da27d588ec80,-0x28d79ae18953451a1a0,0xa45c5ee1f212ca0c880,-0x1f29ee874d0d71ceff88,0x49fba7c599bc881c2050,-0x8cd303309e5a7cbf8b84,0xda72d4994f22a629c9e0,-0x11726f826a75f0a6af47e,0x127ddee9db8524debb384,-0x10501e9696dab39fb4369,0xbfc9cac067c4da719488,-0x7526eb91fd69f771a96c,0x3b35333a978000060798,-0x18907bfba2cc68e1a413,0x845217151f9e7d6d2ac,-0x23901b79bd9fc11388e,0x77506985edf63610f4,-0x12e4e66aa2e4f4137f,0x2277e60ca503e8fa0,-0x2a0dc7af431b26e0,0x1e4c90477fd7d20,-0xa1c6f2cf53401,0xd50dfc2f4cc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 14 26 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 26 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 30 indices rho q1 m1 1 1403883240439680000 17=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 30 indices rho q1 m1 1 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0xb86283d66f8a50400,0xd502c2ef5387e6ef00,-0x74d53fc166b0bf34b80,0x28759c312f2ea6fd2ae0,-0x9ec688a421c6093eee40,0x1d538d9856be3314502d8,-0x43be573104198841bec00,0x7d50121cf82f2155a3994,-0xbca52a2115e796102acd0,0xe995aff86ead430a2b092,-0xef78b200005c3671c0a70,0xcbf21cd17c34e84b6cbdd,-0x9059f74c35f8ed63e6994,0x54b7c822bdcd63b4ab9b0,-0x2903c4d186ac166fd8754,0x103e5e8035b83c727aaf7,-0x532d6fae48d9f245a048,0x15249d91e208dfcb8eca,-0x42aa71b6cfdddc62ab8,0x9d7688b94a8fefc71b,-0x108ebfada213a93384,0x125a7f15e6b84bdfc,-0xbbfbf03d3b3c504,0x35c08f88cd4cbd,-0x38da42a60290]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 14 27 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 27 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 30 indices rho q2 m2 2 1403883240439680000 17=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 30 indices rho q2 m2 2 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m3 : List ℤ := raw_ints% [0x0,0xc3e8ac13d682f54400,-0xdd79487c6b26801df00,0x76c6598991c7fac02c80,-0x282e9f2a1074d38def0a0,0x99e5eeeaa5d623d7f41c0,-0x1bb69bcefadb2fb0824608,0x3e576657cbbe02214920e0,-0x70286ea83c7416b159f9e4,0xa3fb14020df0c50e4f8050,-0xc4e36d982cdb354809637e,0xc36262e44b4574b503a688,-0xa0bf210fa67394be52bda1,0x6da8f06a206f3b5c3807b4,-0x3dddf89badc0c4d2c26b1c,0x1cb460359184d053a7515c,-0xadb058be53ace9629ab1b,0x34d9c6744f0d19f099db8,-0xcb49b46b1e0c8f68132e,0x25a3a1d60cef2b158060,-0x52d293bc06d381dfcc7,0x805becea0763a97dc4,-0x8106283e0dd479610,0x492dd2374417e85c,-0x11dcd86b49f2b19,0xf23d09e140c0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 14 28 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 28 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 30 indices rho q3 m3 3 1403883240439680000 17=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 30 indices rho q3 m3 3 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0xd02736d513eb2498400,0xe6773662543f02dfcf00,-0x78f34b2b905a16c525b80,0x28019857c1c06d274a68e0,-0x95aa11e23994a2269c41c0,0x1a4bf4e2c223443f548fe58,-0x39a6be11e432133cf9c2960,0x64f416f5c7d7106147c0b34,-0x8f74be51e83c556f887aed0,0xa72420dbe91f656976b0d12,-0xa0a8c359fc5898df7fd92e8,0x7fc48711db5dbeb35a2d0e5,-0x540e90dc007e2ee556f3bd4,0x2d9c131eebfd5f4ed77e260,-0x1449d963018a320644d765c,0x7542741e8151e53f134ecf,-0x21ed87ff35bf023dcf61b8,0x7b69c6f1e9d019ce3056a,-0x15760336d9001e527b1c0,0x2bf649c53b48e65769d3,-0x3eaf5d12a1b435eece4,0x3907a9b7f2f99543ac,-0x1c944375f2783181c,0x5ef54008ac31485,-0x40627e82bc100]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 14 29 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 29 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 30 indices rho q4 m4 4 1403883240439680000 17=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 30 indices rho q4 m4 4 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m5 : List ℤ := raw_ints% [0x0,0xdd29aa426529d6e1c400,-0xf00503269be90dcdcbf00,0x7b5e05c12a922a7f2f1c80,-0x27edac763848e80fae7f8a0,0x9204b6611894d38135914c0,-0x190d890d53af7f430cbd8588,0x3591c5d0aaf92f9693730220,-0x5b5f0b2c1b594503c3858984,0x7e490955fae09afa1ee68d50,-0x8edf9eb72f21162d06927afe,0x851bd8c03886da1544c83598,-0x6663024ad93d6c24eb632e29,0x40fe7f630978819e13f78574,-0x21eef6868d089e07489cbfec,0xe7a1a0c46f8109ebeb6302c,-0x4ff04fffaa11c654304bd93,0x15fec49a533dff7922625f8,-0x4ba6de67bb7a8b3eb6d70e,0xc59c39820dc5047ab8810,-0x1788c35e137262aee393f,0x1ed5b0089fd1a6894684,-0x19577cb9eb18c426f60,0xb30ba970bc56ce78c,-0x1f88e5180ecc6b01,0x1114fdb1518c00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 14 30 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 30 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 30 indices rho q5 m5 5 1403883240439680000 17=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 30 indices rho q5 m5 5 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0x35ea7d224000,-0x5699d2874c00,-0x3f7050ab6a80,-0x1c1c853c9f00,-0x86c92f48898,-0x1ce9de12ccc,-0x494d7ce81e,-0x8b87be811,-0xc87e1419,-0xd887909,-0xad190c,-0x63573,-0x2685,-0x87]
def m6 : List ℤ := raw_ints% [0x0,-0xeafc44e68b7c744fe0400,0xfa2bacb7280db96aa8af00,-0x7e08b63c026ec80a4da6b80,0x27f22cc07e8af837595044e0,-0x8ee99a110ad623a1938025c0,0x17f6307be0645bd28065299d8,-0x32025e59fee4cf7d529c41ee0,0x532521e808e498030db165d54,-0x6fd8efa88c1cc61402fe83150,0x7af46c4375e8f3b6f24c0e412,-0x6f18c08d13bca149110ff6148,0x52b3373af76ca19261afe848d,-0x32adf5024d0f19cf8f33792f4,0x19787db3f3042d198a7b79430,-0xa6cdd7a9ebd161b1b756ba5c,0x37023ec9326832608fcf9867,-0xe64d5fac3183b780a8c9678,0x2ecdab7abd8c6de4b1c11ca,-0x72b8f64d38b86fef9eaf20,0xcb2df01b88619b95cc1ab,-0xf4497dcc04d36fb44784,0xb50395fbb6fca57b7fc,-0x4640377680cd7ea6dc,0xa77162e21e664c4d,-0x4863ab3fee9000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 14 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 30 indices rho q6 m6 6 1403883240439680000 17=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 30 indices rho q6 m6 6 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x87,0x1]
def r7 : List ℤ := raw_ints% [0x1c6ea7fd0fc000,0x2d75338836d400,0x211da0b7dddd80,0xe9399f24c6e80,0x45524f9b76928,0xeb88aeca16fc,0x24d93efd3b06,0x44ffbda78d9,0x610200c41a,0x65a7a0542,0x4dc02212,0x2996289,0xe3946,0x2700]
def m7 : List ℤ := raw_ints% [0x0,0xf9ac0934f4343b94de4400,-0x104f4c0e0bcf4afc15339f00,0x80f5c756ad8a277a3b600c80,-0x280e93c4542f21650351324a0,0x8c4e330c76b470190d7909ec0,-0x17018695c95786fe0c73fc1908,0x2ee610c54795795d80d1cee320,-0x4c0ecac717f6bf436d343ff324,0x63a6034e96886f3bf0707cc4d0,-0x6a8255156118d939484527357e,0x5d63d98de0b2c04aefe91d2658,-0x43507471cf94b8a0fde3b2c131,0x27d76d01ca6371b926164dfdd4,-0x13485dcc0afa8db96f2ffe507c,0x792fd561514e463e061b8a94c,-0x2632160ee4b77727818162b4b,0x981288575f67ee1fe5105438,-0x1d35da5fa644323a383eed6e,0x432733316258c32059a3210,-0x6e7122dd075a56aa3b04b7,0x79afe60b5f75c944e1264,-0x512399a470fc8b326b70,0x1b9b7a9524b38195aac,-0x37854c296fc077829,0x132466fcad4c000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 14 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 30 indices rho q7 m7 7 1403883240439680000 17=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 30 indices rho q7 m7 7 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x2700,-0x87,0x1]
def r8 : List ℤ := raw_ints% [-0x836b91037c00000,-0xd15006a9f844000,-0x97ca7169502ac00,-0x4273aab845b2280,-0x139f6c94e82b980,-0x4224e8541baad8,-0xa3f4558927b04,-0x12f41a15d5bfa,-0x1a3b393ad227,-0x1aec883b6e6,-0x14047435be,-0xa47a52ee,-0x34db677,-0x82bba]
def m8 : List ℤ := raw_ints% [0x0,-0x10946c9c843777f4e2c28400,0x1106a664ceb2a157d686d8f00,-0x8427e3c1a6bc256c836707b80,0x284282ac7087618b2a3cec98e0,-0x8a2979282a9822a16e11501bc0,0x162bcba3b9e2699f8ed0622c958,-0x2c2d66a4de91c2f2f694d5a38e0,0x45ee86d6eed8878642791b45274,-0x594b3530a0c4f020f156108c4d0,0x5cda9d5bf90092c62c229dac312,-0x4f0da1558344979d05a70437748,0x37339cb7d5719b0e205f7c3abf5,-0x1f91f2d7645bec2e55ff9ae5c54,0xeb826f9fa29f6308128a459800,-0x58cc9326fcf8fd1d10e66240bc,0x1ac07054c9da83bd7f8d89a6bf,-0x6548556fdf72e29b43e0b5cb8,0x1261f5e1a3b2d89a49ba81c2a,-0x279d3b635a05019bff4a94e0,0x3c718f8a418f6dce928a2c3,-0x3cf22e3c507e723f618e64,0x247f82290d98093eb084c,-0xadc9d6c563a655feabc,0x12644bfbe75597df55,-0x50ddc8dd9a10000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 14 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 30 indices rho q8 m8 8 1403883240439680000 17=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 30 indices rho q8 m8 8 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x82bba,0x2700,-0x87,0x1]
def r9 : List ℤ := raw_ints% [0x1b8897875aba28000,0x2bb629d49d8513800,0x1f9437a181beaa100,0xdc34b9e85fbdda00,0x40adb88a9901a3f0,0xd89fce39ffe16b8,0x214cc45349204f4,0x3d01ecc1f6fc56,0x536edd98b9758,0x545854c02d4b,0x3d796fe770c,0x1ebb398970,0x981be8d8,0x1636557]
def m9 : List ℤ := raw_ints% [0x0,0x119db3664c7aef7430eeac400,-0x11c97660fdc42d1953ef467f00,0x87a1f88e08afdd4095a962fc80,-0x288dbef4f6d3a139070b45260a0,0x8873b76e32c1b8573e438e5f4c0,-0x1571cbab6fe5d668a6a6dabcf088,0x29cb62bf9e088f4d870c368ca320,-0x409eeca5fdfb1f77700272d011c4,0x507751d5c2ae4f6aff41f22d3650,-0x5174442c88574da9f7afab87ddfe,0x435f19b6faab08eb1c625f4245d8,-0x2d991fe313a47055778d224e6a79,0x19356cb145c1aaf4e566d5a23cb4,-0xb53885326e3eb7b2739f5d8b68c,0x419ae1580f3e812340ff9109cac,-0x12e499f57dd2fd22bf715eb4bc3,0x440331aabdaf599fc4cafc1778,-0xba909045625742ccebff1f2ce,0x178a24d6efb98c60dbb819f50,-0x214a1991d13f19a9e95fbbef,0x1eac88df1a548ca265708c4,-0x10778798e43c7d188d1900,0x446dfe0df32e44a3ea8c,-0x6160af105dd4086391,0x15520c80274c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 14 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 30 indices rho q9 m9 9 1403883240439680000 17=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 30 indices rho q9 m9 9 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r10 : List ℤ := raw_ints% [-0x4ad9835c8dc9e3c000,-0x76810d977ea5545400,-0x55567a1f69e2747980,-0x250d6a173a936a6800,-0xad5b0c211760889a8,-0x2418e583804151164,-0x58397bcddea2a17a,-0xa067b4d2fab8dd3,-0xd954472f74f565,-0xd92ae26515893,-0x9bf6f8887860,-0x4c7c49612f9,-0x170ef9fc79,-0x33f7481d]
def m10 : List ℤ := raw_ints% [0x0,-0x12b78e9cb1429e6b73fd970400,0x1298735cefc6d196e92e3ae6f00,-0x8b6737d83e5e80f4646f2548b80,0x28f0307f4aad348809c73e0a4ce0,-0x8726648c0ba3e03104f601bfc9c0,0x14d0c98e856360d2c452c972aacd8,-0x27b513a4018bf99e085a6f56c04e0,0x3c011805249e2303f1864e2737c94,-0x48e8c6063c39f3f8c4f6435bae850,0x47e33c585dfe5b1a6324705525c12,-0x39cb85093e0ed0a99ea7ae8efefc8,0x25ee90dd710584d870d83b656219d,-0x14479339fd6fd60d1797e1cdbe5b4,0x8c8836f74c26152c45027ae03450,-0x30db1a32e050f83fa99da9966f9c,0xd73318b9297a2d43fe96b0bfed7,-0x2e081a7a7f5f90b767ff551def8,0x773ae7ac28b40e680ad845578a,-0xe15706a6a241cac26f2585620,0x1270f8725156d5bdd06b22d9b,-0xf8187ae56f731a254a2d144,0x772c28460a739a50c4a91c,-0x1af529383c287068a461c,0x20303a9b55a60f4139d,-0x59d0d75bbe900000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 14 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 30 indices rho q10 m10 10 1403883240439680000 17=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 30 indices rho q10 m10 10 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r11 : List ℤ := raw_ints% [0xaf1cb5c9d8d8ee14000,0x1149723ccac370cfdc00,0xc6a26412a85f58abc80,0x55f7f80b674ab218980,0x190b6fde78ceb5bd138,0x53129fbeec9de6e974,0xc9faff3a2d34baa02,0x16cf3a7da2c127073,0x1eac4cdaaa28e516,0x1e5ee6d193b7794,0x1590aa58573ba6,0xa6cb7d417df7,0x315b59d08aa,0x6c8046c2e]
def m11 : List ℤ := raw_ints% [0x0,0x13e307867c56c8522b3d7074400,-0x13746028a0e9a05c57c11e955f00,0x8f7b1bb5142a043fc3ca90f7ec80,-0x2969dffbe0a7c41600f53930e5ca0,0x863c012a0c9191df4908f2c74aac0,-0x14466da8e64dc76318e61706672c08,0x25e13ad40801c1944eaec54e761f20,-0x37fb6d3aa89c80c13adc40c8061964,0x426a5ab0c89b7f900a6a2c7e797bd0,-0x3fd1d1f8922ca1403edd1840d4807e,0x31e5f261f178620b530a6fd0ecac58,-0x1fc584c23d87338f1063b67143a301,0x106ec295ba29cafc59068e86d77494,-0x6dccf9f5433157109a7ddd1a3611c,0x24a9c37569f3d9f62131c1fca6c0c,-0x9a624a758008e9ae29f76df056fb,0x1f63ccf6485cc5383e2b192868b8,-0x4cbdcd2a43c8bbb669561cf592e,0x87b00839c50cb8f4aea933a390,-0xa455055e5143055efb55aafe7,0x7de806d141f7ef2b17b1e424,-0x3604a9ac7a0bf5944e0ab10,0xa9f557371f2c042dba46c,-0xaa0c3b6f4ac20d40739,0x179dee3bbf8c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 14 42 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 42 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 30 indices rho q11 m11 11 1403883240439680000 17=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 30 indices rho q11 m11 11 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r12 : List ℤ := raw_ints% [-0x16d9f0f02d375ef278000,-0x24052cf489c64897e6800,-0x19ce9495daa5508eb4700,-0xb237bd9515fa0a6dd580,-0x33c0ea4b2525c8cf21d0,-0xab06f9f057a85304b70,-0x19e041b76ef10ef73f0,-0x2e837edb658123350c,-0x3e2a6c8150412ee83,-0x3d19674365d86e40,-0x2afeb869bf5a742,-0x148db5779bbce4,-0x5ff4661a0c5b,-0xcf24ed15c0]
def m12 : List ℤ := raw_ints% [0x0,-0x152137fee41c34d74df1477b8400,0x145e0bc10d1e9c0e1d3d307eb4f00,-0x93e16963d44815c6678a6bcc69b80,0x29faf5a1e9a2da48982a93b31300e0,-0x85affb4cd1ca46d4ce1b36667fc7c0,0x13d0b750ac228f64a7be0f4b5ce6458,-0x24480469b2fd9b92e095b591f0918e0,0x34789d27c43e421152dab598b208bb4,-0x3cd0ac454caa31e4a0b0884b0ec87d0,0x38fbab1d6aa67adf96bbc3b94888712,-0x2b5987a27b978a3f2177bca82af5e48,0x1aca24a6cfb6ff3575dd1878a7ff185,-0xd68c543da36a80b8d01752db62d214,0x566a8bc219cde8f68bb6763e732720,-0x1bb7cfc2d88dbe452fbb7966a5a77c,0x6f93b8cb4151ff88d9d13efc382af,-0x158f489108157cb00ed3895649338,0x31ba54b479a3ca755da894c137ea,-0x5231fb91028ec406c528043b760,0x5bf97ffbea45eb8a6dfc898233,-0x401e5a99ed9b1e8488a63f324,0x18872a673efab475c77cb06c,-0x42f8cb92bab55c9d6b7a7c,0x38152d50ee8a5bf34b25,-0x633cd6ba5c1000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 14 44 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 44 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 30 indices rho q12 m12 12 1403883240439680000 17=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 30 indices rho q12 m12 12 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xcf24ed15c0,0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r13 : List ℤ := raw_ints% [0x2ba06216f515d6e8f00000,0x44a54001c2201e6b8d8000,0x3114a4f70915a19f4df800,0x1522347e2e32781096f900,0x61eca280b060210e51480,0x14293796b357b419b3330,0x309fcb293263f34e4110,0x5706a1a23d4b1c4fdd0,0x73b75eea87858df9b4,0x710a73a84afc9cc3d,0x4ef76d7005e1bc80,0x256a63f57e819fe,0xacc524681fd5c,0x16fdce0970e5]
def m13 : List ℤ := raw_ints% [0x0,0x16734b7ed25df824c2d05bf33c400,-0x155652130016e77aff110386a03f00,0x989e34c85b8e810b9b0e1131dedc80,-0x2aa3b82dd3eeac676e5ec88849dd8a0,0x857e96053650dd8a9c6c29e804190c0,-0x136df0b6cd6f4169a280cb986b276b88,0x22e2cbf3c00ed441c9bafecc4a5b8b20,-0x3166dc35205079600e758c24a339a204,0x37f830ee500b0f6941ed29d3cc3c1d50,-0x3329f9f8ae025e1cefac3043d60fdcfe,0x25e3c7ab7710c0e5875c0328fb5bcad8,-0x16bc5ac0e6a12aa08f1605370f0428c9,0xb0458c8c7534910cbd430593d5a5774,-0x447e4a717a778e74baa6cf5c1fd102c,0x151b202f3aa3875463b340a0466666c,-0x513711b474e4dede167f8ff9aa32f3,0xee8f885343dc3eac4b7c577a84bf8,-0x206df3da3af6337f31016e0d8508e,0x32122916a7ea35c82b0d774d6dd0,-0x33b57ad302178bff07b2ccd2a9f,0x20c0bcd488e2ba898589297684,-0xb27325e8f3124f9f468911a0,0x1a62d634801865e90f2454c,-0x1279b40f2e893cb90dd21,0x1a080c2f760c000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 14 46 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 46 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 30 indices rho q13 m13 13 1403883240439680000 17=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 30 indices rho q13 m13 13 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x16fdce0970e5,-0xcf24ed15c0,0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r14 : List ℤ := raw_ints% [-0x4d79ae34a1007352ba34000,-0x79b736d924b0fc74756fc00,-0x56de6bd2aa3c8de7ae0c480,-0x2553d9de827243fac7c4300,-0xac8c816f02d5ad7d41b6f8,-0x236d6d8d728976684d3dfc,-0x552c1d60753d001bb8fa6,-0x97e03202a6051fa8c625,-0xc913199f3969c02ccc1,-0xc36dd7a56506a9716d,-0x87b2e3439848cf824,-0x3fd535380768e42f,-0x1242db2c7e51edd,-0x2676b08e9d623]
def m14 : List ℤ := raw_ints% [0x0,-0x17da8036bf83d7a70efd61b2700400,0x165e1cca123eb79eaf0213bf0a42f00,-0x9db5e43058bd6420e4f94103206ab80,0x2b648c20991728e9c5095067d17534e0,-0x85a4d4d15000e576cf1944818885f5c0,0x131ca4bfee4f3634387cef4e009940fd8,-0x21abebf842b11e2a0fcb233ebfbb04ce0,0x2eb7411e6eb413a8d614df85a7cb367d4,-0x33c3ac3d6555c47bce9435544cc06b350,0x2e309359b74e5e9675780befd5afcf412,-0x21504af0a2d8daa5dcb1944ffe9fb90c8,0x136ad97ec2a2d32769fa9bdc48f4f9dad,-0x91c948b70f326783f3c92a4c8f022574,0x36a8fe936f7b5fb9665949ca188ddc70,-0x102ecc5bb76187ba982c77b08f81a25c,0x3b855f88475294e460963a3d5220847,-0xa6113c0f7c759d80a6ff7246eba178,0x1546cd4f43706bfc6f3935dc00554a,-0x1ea95419a73cae85c51ba56d33aa0,0x1d30c50564bcd5d9744923d1ae8b,-0x10c692643fe323a72faa00f9804,0x513bb77bb5e8167bb63678a3c,-0xa6486fc034942745c52e5dc,0x6145c145ca7e6e3bd77ed,-0x6d21c6f97290000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 14 48 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 48 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 30 indices rho q14 m14 14 1403883240439680000 17=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 30 indices rho q14 m14 14 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x2676b08e9d623,0x16fdce0970e5,-0xcf24ed15c0,0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r15 : List ℤ := raw_ints% [0x819cdd80287f19d5fd2ec000,0xcb58232ea5160153e2642400,0x90e5e48567034adaf99f9380,0x3e265e3db94e848d2052f880,0x11eb1d180ea869cde77979c8,0x3ab92329c38aa2879a5f0ec,0x8cca5f74c34bcfcd1d921e,0xfa4153dfe95ba8aac60ad,0x14a1a84496d910203fc32,0x13f752eb35ad5c96af86,0xdcb383a535a827739a,0x6732bcb63ee2dec45,0x1d4fd6f654d711ee,0x3d34c35660d73c]
def m15 : List ℤ := raw_ints% [0x0,0x1958283a2b7c15217fed37cd9704400,-0x1776642c958904c499f234fafae71f00,0xa32d3467305c05718a7f7ee593d7cc80,-0x2c3df33aae193096a8049a77ab49bd4a0,0x86206a29de15366851695aa35d8cf66c0,-0x12db967fd9c673a8330c06c947e9114f08,0x209e96129deea27a69e1204189f950b720,-0x2c5d432f410b24106d56acfc7de69613a4,0x301af71c187819f982e502c0593a651ad0,-0x29ebb0cb7acf87ad4fa6e97e8edefc037e,0x1d7587c1e535893c966cc493307a418558,-0x10af759d90fc97eb54adbdbb9d979c9dd1,0x795a087416432c6cf7d37c944cd18c554,-0x2be9315914c2586856a63ca0ffae5e7bc,0xc7dc552e583ed3ca436fa562af7c3fcc,-0x2be8e46ceac87bae378b61420a48adab,0x74545b4b18aa00666586192bc2c2138,-0xe0a0264298e119f1ed5a6a4824c0ee,0x12de0547ba61766aba5dc39da2ca10,-0x108a37bd020ffba055af5cf3d0a17,0x89cc511a21717aef9cdcd553fe4,-0x2502a23ccaf41f73cca3c9d0b0,0x41777be730e357014cca192c,-0x1ff91db915943eee74ef49,0x1c90665b4acc0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 14 50 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 50 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 30 indices rho q15 m15 15 1403883240439680000 17=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 30 indices rho q15 m15 15 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x3d34c35660d73c,-0x2676b08e9d623,0x16fdce0970e5,-0xcf24ed15c0,0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r16 : List ℤ := raw_ints% [-0xce3fc9662b163c06517c70000,-0x1432e39fe43b37ac4b7b5b1000,-0xe5f7e4e01ba2c264dec3a5200,-0x627b11932808cb0dfca1eb080,-0x1c575216c1816d1aef8b4b320,-0x5cafda9fb59bf2188a6c5a08,-0xddb003cd3fae2c4b5d1a81c,-0x188f7477a15108b3c3318de,-0x204b482c566b616abf989f,-0x1f2347e85c439baedebda,-0x156b80407d9fb7868786,-0x9f72e93391d3c9ba1a,-0x2d053912be405917f,-0x5d5753444c48586]
def m16 : List ℤ := raw_ints% [0x0,-0x1aedaabdce33d67397ec0b4a70748400,0x18a030054107f6bce391584aaa9590f00,-0xa9093d1c4a6793e0a0eab6090a654bb80,0x2d308c2e31aa2e40e90b04d2bda45ae8e0,-0x86efa8cc895f47c899101f86a164cf53c0,0x12a9ba11b383409d7081f992252aaeacf58,-0x1fb6b20cc2fc4a411658b57b2ba70db00e0,0x2a4e51660e754cf6f0785f094c29fbd18f4,-0x2cea08efb2303c70bf6874cc278b3ec0ad0,0x263e347112516d42d5bc43703f444b53312,-0x1a326328723721fafff3e1bdb864e1e1f48,0xe6c746767f16f8b24a2adc515dd173d015,-0x65a57a772090b4f46282ed24cf78c4a7d4,0x2380cd9c6964a8e696c43562141cbe1840,-0x9b45354feab4e1875e07042afa9b6203c,0x20993e146c5baa6ff082ab016332ee59f,-0x51fa17a6582302b7d96f907d0a1ab9b8,0x95042982474355dacf58b1c841d17aa,-0xba98ba3dac6fed803e6243ff41f7e0,0x9674697c1341391b8bc1fd3b828a3,-0x46e2d2608a1ba72f11a1d2cea7e4,0x10df64dbfb96049a86205589a8c,-0x19c2fc5a7c535ad37048fb83c,0xa7f7fde75986d79613dbf5,-0x777fa81902100000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 14 52 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 52 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 30 indices rho q16 m16 16 1403883240439680000 17=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 30 indices rho q16 m16 16 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x5d5753444c48586,0x3d34c35660d73c,-0x2676b08e9d623,0x16fdce0970e5,-0xcf24ed15c0,0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r17 : List ℤ := raw_ints% [0x13a893af60cff18f2f94b2d8000,0x1ec52c234657ab00e459586c800,0x15de42e208924484fef56b32f00,0x959fb582c67db2ca7e0c1be800,0x2afd5f4a690892ceaf2137c710,0x8c55d6d6a69ed7e3a239ebba8,0x14ef29e3785a9a6e99884bbac,0x2504e87c0917ba9a6b9ea5ca,0x308abcf1c635352e9033010,0x2ea7d6d9e35a1815ca482f,0x1ffa23a2daa26c3091674,0xed057328519ac154d0c,0x4296bf00a2a6a7c8e0,0x893ebbd798d31a73]
def m17 : List ℤ := raw_ints% [0x0,0x1c9c8569ab1713dad16acbff177bcc400,-0x19dc989b773ed7d4b1ca6dcf553ee9ff00,0xaf4f759fddb7ae0f78e06cab6686a2bc80,-0x2e3d1284a4515dfbba76c7e3be484e450a0,0x88117764e606f09f3995f01a3aa99d8acc0,-0x12862e93844d35ed6c39adf159299a317688,0x1ef0c2a73921b3c710dac3ad03e8e59ce320,-0x28817d63b68fa6242571f5994291594f5644,0x2a20336cb7e025b591b782598f40fcb35450,-0x23104f7fc5214706ce2a4b6bb5760176c3fe,0x176c56bde9cb10d6ffaa327e1df5ad1acbd8,-0xc8a8afa41e343b58f21d073f057cc33c419,0x55a90b84735a627c800567628d2a1ba9634,-0x1ce285553cc445d27b1abde20bb1f8a3bcc,0x7962741715faa20d371a4ae270997f402c,-0x18594e1f60fb49a979c116d98e70f02523,0x3a195967b6ef153c2115d10cb0c9f3878,-0x635c15e011f54ef9baa02f2f6555b24e,0x73d279bdfb1ed2d9b1887ae2b943850,-0x55cc282de312e78c37da4ab3b0ec4f,0x248726e6bacced192a442e092b844,-0x7b2038d99b46c688fa6ce6e5c40,0xa21ae018ccfe0b27de3b1280c,-0x3717aa3737d183e626b57b1,0x1f36fcbf3dcc00000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 14 54 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 54 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 30 indices rho q17 m17 17 1403883240439680000 17=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 30 indices rho q17 m17 17 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0x893ebbd798d31a73,-0x5d5753444c48586,0x3d34c35660d73c,-0x2676b08e9d623,0x16fdce0970e5,-0xcf24ed15c0,0x6c8046c2e,-0x33f7481d,0x1636557,-0x82bba,0x2700,-0x87,0x1]
def r18 : List ℤ := raw_ints% [-0x1ce7b35154124ca7424670e2c000,-0x2d33013bba0ecbc74225a951a400,-0x20165429893cc7180f64d7cb0f80,-0xdb442a8174ba94b8ec7b8ae3e00,-0x3ee8b69591b63e01583a2e4e448,-0xcd067be6073be473afb5a01094,-0x1e8710f863ef3ff7897bca95d2,-0x35deac5166ec330ef3ab93df7,-0x4677b1fe750a04465959a39d,-0x438ae38df3ef225eedabc47,-0x2e25631e636622c88e20e8,-0x154cb043b988f2db67ae5,-0x5f55e7da170af5880c1,-0xc3846dc2a1a906729]
def m18 : List ℤ := raw_ints% [0x0,-0x1e664dc045c885187e8178bf08f3890400,0x1b2cc7bb10d926fdfce714ac4a92d89ef00,-0xb605b9fa9f665f8c81770e03cbb25f0cb80,0x2f645eb51336438edb513f919974307c1ce0,-0x89854644ea604bd26ceaee772658662961c0,0x12703915f7e608b3a19a95a0087ad025ec2d8,-0x1e49cf05645860620b7f6e5bcd13275f2b4e0,0x26ef36298c8312baed70469ade0080fe76714,-0x27af86012f0b7e545fccb73f4e5b0a1b06e50,0x204e741397c2469b2c2e4508ab03e429ed412,-0x150e05d24577b4fa39bee2b9f90aae17a49c8,0xaf75ec44999df3533a7098019378d2f022bd,-0x489ddf0dad8fe7b935e002aa88990327f134,0x17a49938416be3f0c72f840db5ee151e1e90,-0x5f7808ad39635fea5b4238ee3de17be391c,0x124b2164634e663f884d6c011fd0611a0b7,-0x296682c4ddae1b0d5a8cfdeddfe29c2bf8,0x429129ae2071a04a5ff57d02baae8670a,-0x482b6cd6a6f85215f46edd451f965f20,0x310f3e0f726ac7d528364ced04eb67b,-0x12d9b786542c6c35ba3dcdca97dac4,0x382ba27b5171b6cd98d258a9455c,-0x3fb664c50ed1a12738d43ba99c,0x120d210b21f66fe83b91893d,-0x82567a190a9000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 14 56 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 56 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 30 indices rho q18 m18 18 1403883240439680000 17=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 30 indices rho q18 m18 18 1403883240439680000 17 12
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_18
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<19) : intPolyRF (mz e)=rfPoly (C (1403883240439680000:ℚ))*rfX^17*(1-rfX)^12*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V4C18
