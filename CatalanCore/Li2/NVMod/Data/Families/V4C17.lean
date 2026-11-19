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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C17
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,17,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14,15,16]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x32be93e4000,0x4e859044c00,0x37168ebb680,0x1737a22e080,0x690175be98,0x1509337ef4,0x31313608a,0x55062617,0x6cad1c6,0x658257,0x43616,0x1e1d,0x82,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x23,0x23,-0x17a,0x31,-0x2d6,0x3fcf,-0x18f65,0x22f27,-0x49f,0x49f]
def rhoDenominators : List ℤ := raw_ints% [0xcb070,0xad4,0x38,0x6c,0xc,0x19,0x1,0x7,0x70,0x2f4,0x708,0x2c,0x129]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 17
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
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 17 omega4=padCoefficients 17 (omegaCoefficients 16 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 16 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
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
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xa,0x2d,-0x78,0xd2,-0xfc,0xd2,-0x78,0x2d,-0xa,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 12 li0=padCoefficients 12 (liCoefficients 11 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 11 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x24,-0x54,0x7e,-0x7e,0x54,-0x24,0x9,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 12 li1=padCoefficients 12 (liCoefficients 11 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 11 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x7,0x14,-0x1c,0xe,0xe,-0x1c,0x14,-0x7,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 12 li2=padCoefficients 12 (liCoefficients 11 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 11 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x3,-0x6,0x2a,-0x54,0x54,-0x2a,0x6,0x3,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 12 li3=padCoefficients 12 (liCoefficients 11 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 11 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x5,-0x28,0x50,-0x2e,-0x2e,0x50,-0x28,0x5,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 12 li4=padCoefficients 12 (liCoefficients 11 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 11 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x15,-0x36,-0x36,0x114,-0x114,0x36,0x36,-0x15,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 12 li5=padCoefficients 12 (liCoefficients 11 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 11 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x35,0x50,-0x238,0x1b2,0x1b2,-0x238,0x50,0x35,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 12 li6=padCoefficients 12 (liCoefficients 11 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 11 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x75,0x342,-0x31e,-0xa2c,0xa2c,0x31e,-0x342,-0x75,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 12 li7=padCoefficients 12 (liCoefficients 11 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 11 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf5,0xed8,0x1c70,-0x2c3e,-0x2c3e,0x1c70,0xed8,0xf5,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 12 li8=padCoefficients 12 (liCoefficients 11 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 11 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f5,0x371a,0x11f9a,0x10974,-0x10974,-0x11f9a,-0x371a,-0x1f5,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 12 li9=padCoefficients 12 (liCoefficients 11 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 11 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f5,0xbae0,0x6f218,0x13fe92,0x13fe92,0x6f218,0xbae0,0x3f5,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 12 li10=padCoefficients 12 (liCoefficients 11 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 11 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xb,0x37,-0xa5,0x14a,-0x1ce,0x1ce,-0x14a,0xa5,-0x37,0xb,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 11 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^11 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 16 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 4 17 at hb
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
theorem cache_li (j : ℕ) (hj : j<11) : coefficientsPoly (cache.li j)=liNumerator 11 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x90ae2888c0400,-0x9e3e7c55924600,0x51e28751cb7d7c0,-0x1aa5e72990a752e0,0x61d7b328ba8802f0,-0x10d325a52ceea6e18,0x23fafed9498f76038,-0x3d3926a6783a3358c,0x5427d6bc40dd47428,-0x5e55ef635302745b6,0x56add0b1d7007cb7e,-0x4160706b244f6233b,0x2865a6269a72dab5d,-0x1456a54c39a0d378f,0x843ccf7b69a09f59,-0x2ac1fc452a62f0ea,0xac64e52c1ab8b1a,-0x20da9367315a454,0x48768e19574bb0,-0x6be17a56cc97f,0x607067ec9261,-0x292dc74103f,0x49cee1991]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 13 24 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 24 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 28 indices rho q0 m0 0 639000109440000 16=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 28 indices rho q0 m0 0 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x90ae2888c04000,0x9a6de4c3f734500,-0x4de950215e2f18c0,0x18b1fe98a6fb3f080,-0x58370835f4ef873f0,0xebd6d7813ec667c20,-0x1e96982c382c536950,0x326e1f7adc508bd180,-0x430d36c05b16fbfc1c,0x4890a43fe70f7106e8,-0x403b5ab0e4beb9bbc4,0x2e8e1d3658f49068e0,-0x1b908c0a15e182d8ac,0xd40bd3abce0eb1508,-0x51f50407ab5a68d14,0x1914f3fd49cc87e80,-0x5f226ec64c212c94,0x10ec7875ec3507f8,-0x227c6f822c8520c,0x2ec1ea5c5f78a0,-0x25424ef5ef5b4,0xdb037ae38f8,-0x13c0ae780c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 13 25 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 25 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 28 indices rho q1 m1 1 639000109440000 16=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 28 indices rho q1 m1 1 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x90ae2888c040000,-0x96da56ab75d3bb00,0x4a463d79a14783c40,-0x16f3b03a1867c97240,0x4fd7228c60e20a2ad0,-0xcf9a0b0b859ccfcbd0,0x1a26ea5e64a60f13d60,-0x29d00f3b04b9ea2f620,0x35d20114bf201cf1644,-0x38471f65c17d767c704,0x300676acfc79b24f5d8,-0x2178f11445e4b16b0c8,0x13005451a7882d1e97c,-0x8ba767f050d7e4eedc,0x335ae87ffe80811440,-0xee08511107d384290,0x351350d1a389729bc,-0x8cf059cf0c56e6bc,0x1090daceaafd7038,-0x146b064745845c8,0xe763c823fbc34,-0x48d83c973b14,0x54645efb90]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 13 26 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 26 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 28 indices rho q2 m2 2 639000109440000 16=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 28 indices rho q2 m2 2 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x90ae2888c0400000,0x938001747c892f500,-0x46f11aef548e1325c0,0x156463d2a9c2af48640,-0x4888582575a7fb90530,0xb7990f236650e990a50,-0x167bb42130fded49e2e0,0x22e3c762e065344479a0,-0x2b830527223cc9132c7c,0x2bfeb60b76a61b50b724,-0x24386015e6e5b72ca578,0x184a78192fffd5cb1d28,-0xd3a49605226fae80864,0x5cec7722f5355a1355c,-0x2084fc30870c09815b0,0x8eaf4a2d4e19ec43d0,-0x1deb0cbf8362dcbd44,0x4a130c03ae16a7cdc,-0x806ba53553b2b7f8,0x8f9f3d463a218a8,-0x5a29a7b492202c,0x183b355605dd4,-0x167cf43acc0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 13 27 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 27 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 28 indices rho q3 m3 3 639000109440000 16=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 28 indices rho q3 m3 3 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x90ae2888c04000000,-0x905b5190f2d34c5b00,0x43e291a24273ef3da40,-0x13fe6814627f187f0ac0,0x4222d18d8886c27a3650,-0xa31c00b18fd43a2b01f0,0x136f07dbcc867f198f340,-0x1d4b6968afaf1a37ac140,0x236cb9730564dd10be424,-0x22a8e1c1173501c90f46c,0x1b8c1d9b13d5b3b5dd970,-0x11c97d118b336366dc3b0,0x94bd1a8c251f757fa1f4,-0x3e714379fdec5f252e3c,0x14cced0095bfb6495040,-0x5665070b7b765289a00,0x1107b966cdd96158c0c,-0x2749aa0763a4fc46e4,0x3eb6f0c80efd42ad0,-0x3f85483a6e2f2f50,0x233ed710693048c,-0x80ef4d8c84084,0x5fb10faf100]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 13 28 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 28 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 28 indices rho q4 m4 4 639000109440000 16=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 28 indices rho q4 m4 4 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x32be93e4000,-0x4e859044c00,-0x37168ebb680,-0x1737a22e080,-0x690175be98,-0x1509337ef4,-0x31313608a,-0x550625f3,-0x6cad142,-0x658196,-0x43586,-0x1de3,-0x76]
def m5 : List ℤ := raw_ints% [0x0,-0x90ae2888c040000000,0x8d68ecaba1b8c795500,-0x41140f1c0494ac8ac1c0,0x12bcd0764c5b376d8cd40,-0x3c85272e68bb6f490ea30,0x918d3cc2ff8cb38407610,-0x10e2ef13ea6fda5d9c70a0,0x18befd9993301f4474bc60,-0x1d09a27efbbe31c7d0203c,0x1b82d116935db384915254,-0x151f590278e70e87078228,0xd236fcf2143792a7a7098,-0x697dff8f5ba46624ce4f4,0x2a5c09cfaf7bd35df3d5c,-0xd6efd3a1e7d4d52f4490,0x34d0a87d0380932e2e70,-0x9c8b106ba1f38b81224,0x1503f562306fc47340c,-0x1ed98ca4b55d935468,0x1c3e54a1d8d2c65d8,-0xdd0451172c564fc,0x2adb46535a62b4,-0x196706d1cc00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 13 30 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 30 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 28 indices rho q5 m5 5 639000109440000 16=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 28 indices rho q5 m5 5 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x76,0x1]
def r6 : List ℤ := raw_ints% [0x1763d82b18000,0x23fed1ebcc800,0x1915e03a1d300,0xa7c8e327c480,0x2ef33222f990,0x9493c46c5e0,0x155c1bb00a8,0x241dc22e10,0x2cc768b51,0x27ff42d8,0x18b6c8e,0x9abd8,0x1e09]
def m6 : List ℤ := raw_ints% [0x0,0x90ae2888c0400000000,-0x8aa5ae14a5afeb1bfb00,0x3e7faf29ed49751aeea40,-0x119b58682f8638cf2bacc0,0x379341621b2dc151af5450,-0x82728287e62d6050bdfe70,0xebfa0060275ade1e93b740,-0x150703063690851b144e440,0x17f5d3be5522e108c287ba4,-0x15ff20147ce0ee299810a0c,0x105311891a9757d3ea24a70,-0x9c96a90d193421f8417070,0x4b7bf49f25f020e12b6a74,-0x1cffca26311b11aeb62d1c,0x8c19d05f9f19eb9dcb940,-0x20954cc10aef342451980,0x5ab92a3c5a5f6af8d88c,-0xb54b82c1f9767924644,0xf46b29c7a753df35d0,-0xc9dec3951e06d8a10,0x56cc8c2fbf4fe20c,-0xe3c0e612984424,0x6bb4f3b39000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 13 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 28 indices rho q6 m6 6 639000109440000 16=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 28 indices rho q6 m6 6 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1e09,-0x76,0x1]
def r7 : List ℤ := raw_ints% [-0x5f41e07eb04000,-0x91f05c1f5d2c00,-0x65295b30efa280,-0x2a04015de71180,-0xbaa13f651bed8,-0x248de298d1504,-0x530eb4b7cafa,-0x8a3f3f30827,-0xa7e3f465e6,-0x91c613bbe,-0x567d37ee,-0x1fd0877,-0x594ba]
def m7 : List ℤ := raw_ints% [0x0,-0x90ae2888c04000000000,0x880ea36719679c6a3b500,-0x3c20285541d24556fd99c0,0x10964b00ee5bf5229545940,-0x33356e15545c201d6fb8a30,0x75678bd3c5bf5fc14599110,-0xcf22058bf6dc43a76e20a20,0x11f86bd9d1258fe448b0cee0,-0x13e5ffa941eb037103ea233c,0x11b66abb9e3906b704f22b14,-0xcb6a412cb8db60779d92d08,0x7599016b4d679535024e6b8,-0x3679b7b6c7d4f027bd87d94,0x140727325541a631ac5267c,-0x5c2220f55f9f9110d092d0,0x1446f0f6be860782b2fc30,-0x350343c63136842b46e64,0x6279444489eefb365b0c,-0x79c36aaf5e54f686fc8,0x5a8c2dfa3fd362c178,-0x222433504b884d31c,0x4b946be4f8f40d4,-0x1c7ee63d0c000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 13 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 28 indices rho q7 m7 7 639000109440000 16=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 28 indices rho q7 m7 7 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x594ba,0x1e09,-0x76,0x1]
def r8 : List ℤ := raw_ints% [0x11b33ef6b43a8000,0x1b045f7c265ef800,0x12a52d4cf1e76d00,0x7b409d618b17a80,0x220046e7ccd48f0,0x69bc87f9418e70,0xedfc5c908d740,0x187755e382dbc,0x1d44558dd9b5,0x18ea0d99950,0xe6460c83e,0x51926d24,0xd87dfd]
def m8 : List ℤ := raw_ints% [0x0,0x90ae2888c040000000000,-0x85a1096465e3d2a3979b00,0x39f0baa86225f23d93e4240,-0xfaa6e6c81e7bd706aae54c0,0x2f57a17be8ae51cfae51bc50,-0x6a19c82675816f56c3dd2870,0xb6b39a5adb5a9f04a91c73c0,-0xf71a23730deaad4df90799c0,0x10a1082d9a4bf7a9d6d4a32a4,-0xe5c8892330010941ab6c2f8c,0x9f99ffb0514025e1bc33ff10,-0x5904290b9e6faecf9bdbba50,0x27a3c2441267e519c94f2054,-0xdf319f8bc252ee8c8bb4c3c,0x3d1afa55523490a573b6800,-0xcb946a8768645cb04375c0,0x1f37fdce53dbb8a643bb4c,-0x35db2beaa03754bc74604,0x3cfe035aeda93bcdcbf0,-0x28c204ecf5a01609870,0xd71c6b705e6012c6c,-0x190e4df61abfa3c4,0x78700b0910000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 13 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 28 indices rho q8 m8 8 639000109440000 16=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 28 indices rho q8 m8 8 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r9 : List ℤ := raw_ints% [-0x2ae9c5fcee7c54000,-0x414c229c07e209c00,-0x2ce5deeb59eb0e480,-0x12780b1e3362ef180,-0x5118deffa6fc19b8,-0xfaa194cddf45234,-0x22fdf2bcb783bf2,-0x390742620c087b,-0x437035fb6d0f2,-0x389398d07146,-0x2011448986e,-0xb12e9236b,-0x1c5d8d56]
def m9 : List ℤ := raw_ints% [0x0,-0x90ae2888c0400000000000,0x835a4901dd9845795e21500,-0x37ed2079816560ce400561c0,0xed4f27e3fab1e35283f17940,-0x2be8d97ea9f052493d6b42630,0x6044f9f20e4c1caeda2e81910,-0xa1eabaec69ccdf59b5dfec6a0,0xd584e3c44eaf27bf5ef5c6060,-0xdfb543f61d0799b41b1046b3c,0xbb8fa1f52d88bfceb0f2d4614,-0x7e21f30df35921793958911a8,0x43e63cc30db16cd033c36b798,-0x1d1348fe52a55ea50fde9bc74,0x9cba91a078d8ec0fa83bd81c,-0x28dba205eeebaa9062d71990,0x80c16be9905dfc3ed09d670,-0x1284f8477d8fe6496633424,0x1da472e76ad38520f6154c,-0x1eb3e45e3552fc35c7de8,0x1266cf48f26eccaf86d8,-0x54c6153776f2cc2c7c,0x84c2480e6ab72ff4,-0x1fc4927c8c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 13 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 28 indices rho q9 m9 9 639000109440000 16=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 28 indices rho q9 m9 9 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r10 : List ℤ := raw_ints% [0x59f636cad4e4298000,0x88863e0e25f9884800,0x5d94d15ab9e1133300,0x265abe57942d2d0680,0xa7b07afcffe90cd90,0x20398b7ba9be0f040,0x478ba5d660dc1e28,0x73bdf2b81ee3ac8,0x87a31d788e7e09,0x7085688c7e348,0x3ee0c861d81e,0x15518e07e50,0x35498a241]
def m10 : List ℤ := raw_ints% [0x0,0x90ae2888c04000000000000,-0x8137f4a57dd17121c83f3b00,0x361180fc5983b55f50b89ba40,-0xe1361e634abac9439c56154c0,0x28da9d3aef8bbb1b923eb31c50,-0x57b084b43e20905a4165989870,0x9028d4879157db316d528a1640,-0xb97a9dfe5c7cfd92329a3e3540,0xbd36839a218b944a6f51d7e3a4,-0x9a18b7b18be1cbb635a4e9308c,0x64623b7e68c6a5e2f5d29a2f30,-0x342d89c4059320446de63f73b0,0x157ddea63aea03d7e08e14d2b4,-0x6eeca5021633932484512d15c,0x1b88936218019b30b1b22ffc0,-0x520b9b983bb4f549c2be9f00,0xb0fd727d9aa2680e34c310c,-0x1069513425762b2f4161d44,0xf862622d71d9099752f90,-0x8544afe489afe8a49450,0x216ca8eb5ed09092d4c,-0x2bea13731a29f3c64,0x85e255af900000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 13 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 28 indices rho q10 m10 10 639000109440000 16=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 28 indices rho q10 m10 10 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x35498a241,-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r11 : List ℤ := raw_ints% [-0xa90085841b59d4e4000,-0xffe3f1ca3fb8e05cc00,-0xaeef8775d612fce0e80,-0x4779b26aec17fd8cd80,-0x1375cb8f23cbe948e18,-0x3b94227e715eb8d664,-0x839b90bec1911e6ca,-0xd39f827843761baf,-0xf632fb615e0547e,-0xca6f31cd5aa80e,-0x6fe2d7793c44e,-0x2569afec273f,-0x5bdca1e6b2]
def m11 : List ℤ := raw_ints% [0x0,-0x90ae2888c040000000000000,0x7f37c58ee4070a0fabbb47500,-0x345a6463f598a5f391ca2fe9c0,0xd63959dfce52dcb8977e5aa940,-0x26209341cd0c313eaef9f714230,0x502d45c6a61b52285300aec8510,-0x80ed0cc97a85cc7c66e3078e320,0xa1f3d94a62df6ae9220f37fc9e0,-0xa0f65bec92a2178e6d0c2b5c33c,0x7f68031c0be15632465258fce14,-0x506ff384b7058fa649cc930ce48,0x2862e4e41b637fae6008933be78,-0x10014ca6300c8154f2ecdafa354,0x4f1a641847bc707f1fe52468bc,-0x12b191c77df0c6da6288e5c050,0x34a7a41a1bb7a99ed9745dcb0,-0x6a677b1186104abdba4869e4,0x922b1c42b81f28784d76a8c,-0x7e16630428713bb6977408,0x3c736f12f0a0b6ed0e238,-0xd2e6afc9f079d651ddc,0xe826164bf38497414,-0x23380b904c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 13 42 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 42 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 28 indices rho q11 m11 11 639000109440000 16=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 28 indices rho q11 m11 11 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x5bdca1e6b2,0x35498a241,-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r12 : List ℤ := raw_ints% [0x12357a70b973c5ac88000,0x1b842633a98d5eff69800,0x12c49b04511b6f2561900,0x7a5d99d2fb0242a50a80,0x2136695dcc70cada4830,0x65509cb2de072bcef90,0xdeda173e099c464590,0x1648bd8c7943e43f34,0x19c53a6dcc38da3fd,0x1509a16c20857600,0xb86bc4ea00b73e,0x3d0157fcc39dc,0x93c5a4aff25]
def m12 : List ℤ := raw_ints% [0x0,0x90ae2888c0400000000000000,-0x7d579969b3d9496eb0ff92db00,0x32c4a9646b35b8a14807072b240,-0xcc3aa335ece32e7de5631c974c0,0x23b02a537fec58d7500e53022c50,-0x4993da66404bb4794ee3972cd070,0x73ce3b67aab13ea20662c421d4c0,-0x8e1eabb23fd745ee1741feb014c0,0x89b32ae3848f5163a5c72ca968a4,-0x69fd2ebcbadbc3e1b4e6981c038c,0x40e1dd121afdd82b97fde1ac3a50,-0x1f7a8443224642cd4c15b64f9a10,0xc016b8479e3a2fd4a4f4ce16a14,-0x38d2db549311ffd7583d755a77c,0xcc87cab6de0d6959c54ea54180,-0x2205bbf91f466f10d9fa3bde40,0x405bacdb604a20b7b544d64cc,-0x51c5be83a337182d54142884,0x403b3db7e98a710dfba0230,-0x1b78016f0f442e1529d930,0x532bc5493dd22c6f772c,-0x4c9cc36381b2758604,0x940bd3a71000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 13 44 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 44 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 28 indices rho q12 m12 12 639000109440000 16=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 28 indices rho q12 m12 12 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x93c5a4aff25,-0x5bdca1e6b2,0x35498a241,-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r13 : List ℤ := raw_ints% [-0x1d4a9c38b1812c37bf4000,-0x2c2ff97bfb9cf9c28a7c00,-0x1e14395e88565cc5e44880,-0xc3a952f8fd9a45753d980,-0x34f70eabf8149c428e978,-0xa111f99043784f941d14,-0x161032bfb074081d7a62,-0x23268ad9042e63424c3,-0x287290df13fd9c4c6a,-0x20d2fc216ab18db96,-0x11db4dfb7052452e,-0x5db2a61a6485f3,-0xe0905a4956ee]
def m13 : List ℤ := raw_ints% [0x0,-0x90ae2888c04000000000000000,0x7b957006d6ae64d7c5ef99ad500,-0x314d7bea42593d2284f4e1b071c0,0xc31f6a5c16183ec866d8511cd940,-0x2180512a3bb4a896eeaab7fb46e30,0x43c33c073724b2a0f20d537947110,-0x6876319f04ea5e68e00a5f4db33a0,0x7d5302e8944f4c10f206120ac4f60,-0x7671973178fda7bb74dabddcbb73c,0x58b37ce9855f21da67fa267825e14,-0x34ac491520d67bf077238697773e8,0x18b3d22ba38ad4c399be258410058,-0x911926d065fc8cb23aa0b03a3134,0x291b7f66b5305185351db4e20a5c,-0x8cd38c23a27218aed08da690510,0x162004ff2c87c3d30ef88b63cf0,-0x2725ff973427ad37cccd6819a4,0x2df4cd62cff33e546e8c939cc,-0x20d29057500dcfa0424edf28,0xc7fd90cfbd8a0f35ffdc98,-0x20cb1b13938c0a5ae123c,0x1940f20d4246a6e5534,-0x26d951784c000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 13 46 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 46 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 28 indices rho q13 m13 13 639000109440000 16=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 28 indices rho q13 m13 13 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xe0905a4956ee,0x93c5a4aff25,-0x5bdca1e6b2,0x35498a241,-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r14 : List ℤ := raw_ints% [0x2c835e8039d186e015f8000,0x430c7b4b370c1afa7c76800,0x2d8fcd6a3b0211502682f00,0x127c81cdce22ce582736e80,0x4fe1e7b208d38d5b8267d0,0xf2478bc9046ed11f11560,0x2115acb6515e2fa37ff38,0x34852006618006f4a900,0x3c2e35aef00fa496551,0x3098b85ec33b5b1a78,0x1a4836681eb42d0de,0x88f0cf3622c77c8,0x1456a7bed99ee9]
def m14 : List ℤ := raw_ints% [0x0,0x90ae2888c040000000000000000,-0x79ef693a27562e8a4990a0127b00,0x2ff24ce277cec3fa43e6152e6aa40,-0xbad0497da763da0468f62989dd4c0,0x1f893a922509cf5754d9130b6a4c50,-0x3e9fa117bc9d1dee5667f7b0dad870,0x5e9e02faf96aab6a59b7c91901a740,-0x6f09a6ecedc46185c15e75bbcd1040,0x666c1ff5d188452b42c898dcdd09a4,-0x4aaa94db6f3d3e937e667a92e3828c,0x2b07852413e569befece860f4d4670,-0x13834b12c285cc8c3e4478deb7db70,0x6e58e623db73d37359e68fe0d2074,-0x1df0b882ecb2bd756628ea853229c,0x619a858d81a5ba04475c3532a140,-0xe79e715d36f87f3a6c35f21e780,0x17f0bbf83534d7f0f69dba2128c,-0x19ef7bbdf692ed781bfb22a9c4,0x10d1741a2d52ea9601a7cd1d0,-0x5b1aef81e252421736aad10,0xced0564faf516c9c0cc0c,-0x85094618f0e59a668a4,0xa2ec84ef90000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 13 48 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 48 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 28 indices rho q14 m14 14 639000109440000 16=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 28 indices rho q14 m14 14 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x1456a7bed99ee9,-0xe0905a4956ee,0x93c5a4aff25,-0x5bdca1e6b2,0x35498a241,-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r15 : List ℤ := raw_ints% [-0x40810d3a5a68a62ff5284000,-0x610803900dc8ff081671ac00,-0x41d5c58148c64e0b03e4b280,-0x1aaa4c543aea5415fa652580,-0x72fe061d12d06fedc30d9d8,-0x15bf4fe34fb0951818abc44,-0x2f63770d0f84be8140f43a,-0x4afe7f59854608f61ddb7,-0x559fd949487e19f27836,-0x44da7bdfec7164aedde,-0x250ded714f8e81b38e,-0xbff212dc34037d87,-0x1c4f43b88563a8a]
def m15 : List ℤ := raw_ints% [0x0,-0x90ae2888c0400000000000000000,0x7863c2da42f37ba1a4f7961153500,-0x2eb0caf28e38a5af4a00254163f9c0,0xb3389a124a6c95a738b759fb15c940,-0x1dc42b94536fd9b184dbbccc1e46a30,0x3a119438088792342a1948f7666cd10,-0x560b15749cc30b65072867e97142820,0x62d54b46bbd6aac5949e0befc9360e0,-0x5906bf5786015a81f3b9301921c573c,0x3f3581294569f1bde3394f38e9c4214,-0x235d9cc9397906c9e677aadd68f6e88,0xf832612018943150ad5a3bc2eac938,-0x547889cfc8df66c73ea784bb573a14,0x15f32a932a4b5bcf9b01c1a1e04cfc,-0x4412f9bc5b18f83c8dd020b374fd0,0x986c928a040da3d3ad4b5b607f30,-0xeb67e9f5083019064965748bb64,0xeb14061ce82fe8ec24fec3af0c,-0x8a356e13a2d0cc7eb1badbb48,0x2989c06a67461e0a867fb1f8,-0x517b64dc85e3f18972ad9c,0x2bc09fa103d4e2cf9b54,-0x2aa864348c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 13 50 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 50 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 28 indices rho q15 m15 15 639000109440000 16=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 28 indices rho q15 m15 15 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x1c4f43b88563a8a,0x1456a7bed99ee9,-0xe0905a4956ee,0x93c5a4aff25,-0x5bdca1e6b2,0x35498a241,-0x1c5d8d56,0xd87dfd,-0x594ba,0x1e09,-0x76,0x1]
def r16 : List ℤ := raw_ints% [0x59c8e69077bbbd56d560e8000,0x86e6ab75d887c570c8860b800,0x5b67e21976d1c15832ef7b500,0x24f7046df533ff05c24c55280,0x9f20755fc56686b043520870,0x1e087033bd7b0d680a4cddb0,0x414a81dbf532642e9229220,0x670c81d58d164cbc6aca2c,0x754ad504cc562b5fe1305,0x5dfb2028bcfe1d8780b0,0x325dba1ae71bb9f35fe,0x103a013368fe1f1a14,0x2611f35f07c63c8d]
def m16 : List ℤ := raw_ints% [0x0,0x90ae2888c04000000000000000000,-0x76f0d6e05cd6f3e78aa81cb03e1b00,0x2d86dc041afe262a6a6d862671ba240,-0xac4619324d72233ba9c0c803d50f4c0,0x1c2b51e75f1778fd3f4377be7cdb7c50,-0x360536eecd3a74d7f9e3b377fbb25070,0x4e8ccca59ff386fceab85dd946490dc0,-0x585d2f9e97e00537030a8bd1fc5c67c0,0x4dc590383251bdfc0444d530e63946a4,-0x35ce2465c1bd16488821dd7de134b58c,0x1d3d3e04cf21194a61087402fb26b390,-0xc689e0ca9eed93eb6e54941101487d0,0x4112f9ea5d129cd8eb5c48a56e695d4,-0x1031927a740257fc4b26c1ce5893abc,0x2fc3fc63b84ac30d7c2833ba361f00,-0x64db937e2f5e417d8718d86c39ac0,0x9157014015ac12e3d1cdad3fba4c,-0x85a14cc5ad4c0b45d4569e9d904,0x47219b1c4cbc38ff705734be70,-0x12f34ff5fb8aeb6a18b361ff0,0x2015f7da01ab19cc7778bec,-0xe5f87b141c9c1a490c44,0xb2846989100000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 13 52 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 52 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 28 indices rho q16 m16 16 639000109440000 16=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 28 indices rho q16 m16 16 639000109440000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<17) : intPolyRF (mz e)=rfPoly (C (639000109440000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V4C17
