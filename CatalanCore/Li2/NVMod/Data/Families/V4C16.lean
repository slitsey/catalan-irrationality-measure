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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C16
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,16,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14,15]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x32be93e400,0x4b59a70680,0x3260f44b00,0x141192e958,0x54efe2d54,0xfba3551a,0x217700b7,0x338f256,0x391df7,0x2c646,0x16fd,0x72,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x5,-0x23,0x46,-0xa56,0x126,-0xe2e,0x3fcf,-0x18f65,0x22f27,-0x49f]
def rhoDenominators : List ℤ := raw_ints% [0x10eb4,0xfc,0x1c,0xc,0x3,0x19,0x1,0x7,0x1c,0xfc,0x384,0x2c]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 16
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤15))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤15 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 16 omega4=padCoefficients 16 (omegaCoefficients 15 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 15 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 16 omega5=padCoefficients 16 (omegaCoefficients 15 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 15 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 16 omega6=padCoefficients 16 (omegaCoefficients 15 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 15 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 16 omega7=padCoefficients 16 (omegaCoefficients 15 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 15 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 16 omega8=padCoefficients 16 (omegaCoefficients 15 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 15 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 16 omega9=padCoefficients 16 (omegaCoefficients 15 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 15 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 16 omega10=padCoefficients 16 (omegaCoefficients 15 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 15 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 16 omega11=padCoefficients 16 (omegaCoefficients 15 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 15 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 16 omega12=padCoefficients 16 (omegaCoefficients 15 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 15 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 16 omega13=padCoefficients 16 (omegaCoefficients 15 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 15 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 16 omega14=padCoefficients 16 (omegaCoefficients 15 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 15 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 16 omega15=padCoefficients 16 (omegaCoefficients 15 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 15 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x24,-0x54,0x7e,-0x7e,0x54,-0x24,0x9,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 11 li0=padCoefficients 11 (liCoefficients 10 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 10 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x8,0x1c,-0x38,0x46,-0x38,0x1c,-0x8,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 11 li1=padCoefficients 11 (liCoefficients 10 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 10 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x6,0xe,-0xe,0x0,0xe,-0xe,0x6,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 11 li2=padCoefficients 11 (liCoefficients 10 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 10 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x2,-0x8,0x22,-0x32,0x22,-0x8,-0x2,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 11 li3=padCoefficients 11 (liCoefficients 10 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 10 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x6,-0x22,0x2e,0x0,-0x2e,0x22,-0x6,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 11 li4=padCoefficients 11 (liCoefficients 10 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 10 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x16,-0x20,-0x56,0xbe,-0x56,-0x20,0x16,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 11 li5=padCoefficients 11 (liCoefficients 10 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 10 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x36,0x86,-0x1b2,0x0,0x1b2,-0x86,-0x36,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 11 li6=padCoefficients 11 (liCoefficients 10 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 10 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x76,0x3b8,0x9a,-0x992,0x9a,0x3b8,0x76,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 11 li7=padCoefficients 11 (liCoefficients 10 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 10 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf6,0xfce,0x2c3e,0x0,-0x2c3e,-0xfce,-0xf6,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 11 li8=padCoefficients 11 (liCoefficients 10 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 10 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f6,0x3910,0x158aa,0x2621e,0x158aa,0x3910,0x1f6,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 11 li9=padCoefficients 11 (liCoefficients 10 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 10 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xa,0x2d,-0x78,0xd2,-0xfc,0xd2,-0x78,0x2d,-0xa,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 10 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^10 := by
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 15 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 4 16 at hb
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
theorem cache_li (j : ℕ) (hj : j<10) : coefficientsPoly (cache.li j)=liNumerator 10 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x5161f6ccec240,0x4fae79f1a270b0,-0x24adcf1f0985470,0xa8b5c51c188507c,-0x21eea77053fd0d4c,0x5119e6fbc99b2a38,-0x9526b1fbdf32cbb8,0xd7bbf85746a8cf7b,-0xf8b4f5470d97778f,0xe62a3577cd38c81e,-0xab5cb99925035e1e,0x66657371e71949a5,-0x30c338add38f6959,0x12472bec7f78df5c,-0x54a347356a501fc,0x1260015253cf3c5,-0x2dd77ef5db7c01,0x4cb547e5d8cbe,-0x4ca22bd635de,0x245f572a37f,-0x4812eed6b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 12 23 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 23 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 26 indices rho q0 m0 0 53250009120000 15=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 26 indices rho q0 m0 0 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x4c4bd7601d61c0,-0x48d225d9bc20f90,0x20a4102e45dd1240,-0x9204689e109804c4,0x1c861f686b2df4fc0,-0x421db1be8aad12238,0x75b8fe3e1735bb5f0,-0xa48b7ab992b230305,0xb6ea421ee422b0af0,-0xa2d368df219dedaee,0x744599f7ca5f5222c,-0x4269b566bd127d5ef,0x1e1c2f933f3693234,-0xab14a76fc96a1d8c,0x2e9f4194fd31dae8,-0x974e65be3987263,0x15d081ac0fc5a58,-0x21444989cef45e,0x1da3be7a8fbfc,-0xc1af7505145,0x134de0b5c4]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 12 24 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 24 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 26 indices rho q1 m1 1 53250009120000 15=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 26 indices rho q1 m1 1 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x478719ea1b8ba40,0x429fc4926dbb52f0,-0x1d1c61aabc3bce4e0,0x7ec9d193889abe91c,-0x1814b2c6f130dc65c8,0x362fd252b22749c3d0,-0x5d80d505aa3d347a38,0x7e697ec768b4735fc3,-0x879f48bed3e87aefaa,0x7437ee82f86c729fac,-0x4fa77bbedaa5dab446,0x2b84185d981e548257,-0x12ca7e098cba64a25c,0x652bd0b128b902180,-0x19f58dd3cee91dc44,0x4eaccef069faa0f1,-0xa7a437413b05da2,0xe89285b3fd5354,-0xb8459342adcfe,0x407ed51df099,-0x5289e3abb0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 12 25 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 25 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 26 indices rho q2 m2 2 53250009120000 15=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 26 indices rho q2 m2 2 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x430ea84b79d2e9c0,-0x3d05313cca907a110,0x1a04a77223a3892660,-0x6e713a8c49cbe35c04,0x146a54ef040980fc6e8,-0x2ca4062eb095030a8a8,0x4ab9240009427e06968,-0x61cd2b025e112cd7ee5,0x6559db3040b0f3cb642,-0x53abaf0c00a4ab6feea,0x3713e6ec65ba3240252,-0x1ccb685f96b0c46bb5f,0xbd8dc81b305df7c7ec,-0x3c737be395fe4ce3a4,0xe9a32f42d8680149c,-0x294e6d76f30cf1c13,0x5136a841adff2f2a,-0x664f2faad9d6d3a,0x47e170f8b6c50a,-0x157a5377fd025,0x16028455240]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 12 26 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 26 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 26 indices rho q3 m3 3 53250009120000 15=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 26 indices rho q3 m3 3 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x32be93e400,-0x4b59a70680,-0x3260f44b00,-0x141192e958,-0x54efe2d54,-0xfba3551a,-0x21770093,-0x338f1d2,-0x391d36,-0x2c5b6,-0x16c3,-0x66]
def m4 : List ℤ := raw_ints% [0x0,-0x3eddbdc6c235bb240,0x37f259fe11223335f0,-0x174d7ce1f7409e41ca0,0x6080b5b6045ba5d6d9c,-0x1160f9e2b56ef92be078,0x24f66c1acc74167dafd0,-0x3c128fd23e20d31c4228,0x4c2f59d93a6d72f79603,-0x4c5209b1c22e6812e906,0x3cbe585b270a067eee0c,-0x266d6d2dacf42933e2d2,0x133c0c235fafeb45375f,-0x78aeb6a5e3b79c46bd4,0x247a99e40c7bcd96420,-0x84b3984937686e3aac,0x15e26fb86d7049d3e1,-0x27a8123d6d6ab464e,0x2d473470a14e0114,-0x1c2105ad0828ada,0x7267a6eb10821,-0x5db80bd1b00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 12 28 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 28 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 26 indices rho q4 m4 4 53250009120000 15=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 26 indices rho q4 m4 4 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x66,0x1]
def r5 : List ℤ := raw_ints% [0x1437eeecd800,0x1dd2f9f8b300,0x13c747aedb80,0x7cc9f94ae10,0x20967b32620,0x5ef415bb08,0xc59c6f3d0,0x127398db1,0x1388fe98,0xe1e2ae,0x66318,0x16a9]
def m5 : List ℤ := raw_ints% [0x0,0x3aefe1ea56125f71c0,-0x335900b8a0e378afd10,0x14e9c676dd07005270e0,-0x54940a8f997229a02b04,0xeda62507d92a1aa5f288,-0x1ec18982d74668a48ff08,0x3093581a36067023793c8,-0x3bbde29e56eaf51da8ce5,0x39e632e388d027cc7200a,-0x2c751739a87f11cb55ca2,0x1b0b58a250dad9c931aca,-0xcf7609df6c02d3ba7847,0x4d8f44407162a58aab1c,-0x1638c017ef9691e1f634,0x4c10f8d5bd5ecd5daec,-0xbb18f694cbc08ad5e3,0x138178974647329452,-0x14254c90843e9ed12,0xb093fada59d79e2,-0x2610baf8cdb9ed,0x18e4f4c8c400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 12 30 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 30 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 26 indices rho q5 m5 5 53250009120000 15=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 26 indices rho q5 m5 5 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x16a9,-0x66,0x1]
def r6 : List ℤ := raw_ints% [-0x47de085398400,-0x6973a9ae57280,-0x457c405bed000,-0x1b2faf25abf98,-0x707e5e1c7664,-0x143cc070440a,-0x2975d8977c7,-0x3caba46af6,-0x3e70e745e,-0x2b55e99e,-0x1270857,-0x3b42a]
def m6 : List ℤ := raw_ints% [0x0,-0x3740e3cbb0b1397aa40,0x2f2c837c398e3cbc6bf0,-0x12ce55b855421540c1da0,0x4a589b583c36046f35c9c,-0xcbe69e55224a07857d538,0x19b6e48aee842d7bda48f0,-0x27805f282fbaec6a72d628,0x2f26a2996a4235901a4bc3,-0x2c3dcf7923bbbea6d2e8b6,0x20cb4fb81d11bd0d336174,-0x13318fca47fefea1cb7692,0x8d16c16357a97aac70ce7,-0x324c28444fca2514616b4,0xda8c19eaf83a8fced410,-0x2bfb8c4610892853b8ec,0x64c51acd102b613b3f1,-0x9a88dda2f33f15777e,0x901767d6e14cb719c,-0x456b4f79c4d3b65a,0xca7c5ad58bbac9,-0x699d6748b000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 12 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 26 indices rho q6 m6 6 53250009120000 15=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 26 indices rho q6 m6 6 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x3b42a,0x16a9,-0x66,0x1]
def r7 : List ℤ := raw_ints% [0xbbf20eec936800,0x112967ab43f8d00,0xb40011f2eadb80,0x45fc9ae4755870,0x11f6694333c030,0x33383c1d3c7e0,0x67b56bbb85fc,0x9580b34c255,0x96e0b12b90,0x65fa14b1e,0x29cebfe4,0x7f325d]
def m7 : List ℤ := raw_ints% [0x0,0x33ccd58ef5a625e2f9c0,-0x2b61abb9b45735154a310,0x10f19c4d6e69db878d4ce0,-0x418a1b263567559de5f104,0xaf9b88a07a6cb3423f0d08,-0x1599810cc7b0bafa3814c28,0x204ca1d5e8e25ba3dff2588,-0x2572a8780f094a4a8c82fe5,0x220adafb8b0b389e4dc5aea,-0x186026ffa9c3c029896368a,0xdbba42a94dc1db2ff3583a,-0x60c4dc3b25ff10a466b72f,0x20e6e8919c60356e908b1c,-0x877f599202e75cb409aa4,0x19a42cf3fd13729a86bcc,-0x36adb012a10476c28273,0x4cfc5ba969b11e00672,-0x40ad8c72c89304bd9a,0x1b554f44506b6e252,-0x4341880c6cf7375,0x1bf53210a4000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 12 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 26 indices rho q7 m7 7 53250009120000 15=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 26 indices rho q7 m7 7 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r8 : List ℤ := raw_ints% [-0x193687063a41d400,-0x24b45aaf7ddef480,-0x17f56bf37025b200,-0x944aa88e3af1978,-0x25d3ed8ef678714,-0x6b111f45a73e42,-0xd6d1aff54389b,-0x1322d17f34f42,-0x13090eee5e66,-0xca07c487de,-0x50c6778cb,-0xed5ad86]
def m8 : List ℤ := raw_ints% [0x0,-0x30900836064bc384ca240,0x27ee8364afa7626405edf0,-0xf4b6ba48f68241f48e63a0,0x39efe976006d2714ca4e99c,-0x97cbf03d440466e95994a38,0x1239c03a187cb920040cbf90,-0x1a8d3f599127f8f3740b0568,0x1dec69d5ce77dd98f9978a83,-0x1a5f751234d32f00545f99b6,0x12409bc64860d6e05a1a4e3c,-0x9e749efcdf22bc986061ae2,0x42ead17dc66877cc68feb2f,-0x15b3ebbbf0e4e0da1ba2874,0x54b34ade8d1a741fadcac0,-0xf10b3493d98b72240ab0c,0x1ddfebfe021b6aee6b501,-0x2690ab0efbeff363d13e,0x1d228eca4830c118984,-0xac6365bc10f60a12a,0x1650d3a78f0febb1,-0x7639f610b0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 12 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 26 indices rho q8 m8 8 53250009120000 15=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 26 indices rho q8 m8 8 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r9 : List ℤ := raw_ints% [0x2f0c70cde667d5800,0x444954653fb101300,0x2c6a5d290bfaf4d80,0x111c0d66d00a8ea10,0x457b8e9688e26480,0xc37b945633b9688,0x1855f9d4461cc88,0x2260b681ccbe69,0x21d230fb54b08,0x161f9ec0b83e,0x8afe517990,0x18ebfcce1]
def m9 : List ℤ := raw_ints% [0x0,0x2d8707b2a5e7074c7d81c0,-0x24ca2f48286fd8c9d3e3110,0xdd4bf0c6817cfdc9790fee0,-0x335af143204a1e9c56d04704,0x83aed3e38e01931b0f432308,-0xf7245f2e7bbec595a72fb948,0x15f0c1bfb086f68d8b5c642c8,-0x180d94104973bb54aef6da3e5,0x1490f99f38c034cbf5710a02a,-0xdc3fb202aadc551b9ec3f372,0x73248de8acff6134de550d0a,-0x2ea44ec3f7f2da8f130b8757,0xe6e420f363ef1551cd8075c,-0x355d175e84e787fcf593014,0x8eaa90debf9d69f1ceb5ec,-0x106d87199387e6c3c48b83,0x136a5d5739f3bd3d70e72,-0xd2a04d43a8d23da8022,0x4400e4a7e299ac7ca2,-0x7656683d93f8503d,0x1f333c2cc40000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 12 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 26 indices rho q9 m9 9 53250009120000 15=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 26 indices rho q9 m9 9 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r10 : List ℤ := raw_ints% [-0x4f0a4eb94675ab6400,-0x726d0ed08557fd5e80,-0x4a33e52e13dc69d800,-0x1c7bb5c076ad09e8d8,-0x73308834c6287dcc4,-0x14278e7f7b3e21f5a,-0x27e85c68e576de4f,-0x37f933573f1b90e,-0x3696aa91906bae,-0x23531eaf4c07e,-0xdaef068181f,-0x269317c2a2]
def m10 : List ℤ := raw_ints% [0x0,-0x2aae97377b8896d7b5a9a40,0x21eccdea31336a37c32e5ff0,-0xc878e7b582204c08a4212da0,0x2da3f0f2327ecda7bb784329c,-0x72a14d852346612c2245e3838,0xd25a025218e5833f11afa7d30,-0x1238bb7580991602cf9e6323a8,0x1372241c9348e5a288be82e643,-0x10242200176261b80baf92b3f6,0xa743df78049bbee2f032179c4,-0x5449dddb7f5c4d9e379c425f2,0x20c24cd013193d4aeb288fab7,-0x9ab5f1255859b919abcd13b4,0x21df86677e62a36cecf91bf0,-0x5506e40ac446c219f69e5ac,0x91665daac7c0fa6acafd91,-0x9d19654b743be3a408b3e,0x5f6999642f92edcf152c,-0x1ad67b3472bff259dba,0x272cb48cf6a7386d9,-0x838db829b00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 12 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 26 indices rho q10 m10 10 53250009120000 15=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 26 indices rho q10 m10 10 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r11 : List ℤ := raw_ints% [0x7a5721877be285e4800,0xb0b8ff57e15ee73b900,0x724e98d9bd8e0701780,0x2bbefdda731164a81b0,0xb04adf10173cb46e50,0x1eb7cc436b34a7b1b0,0x3c86ba3bdcd680274,0x54659c1373f1a81d,0x51bb0f67f196b40,0x346fd58cbc189e,0x141917e40859c,0x37e902c9405]
def m11 : List ℤ := raw_ints% [0x0,0x2803adc403d00d6a3a4f09c0,-0x1f4f5a6f480170af81f3c9f10,0xb5ea890e2bf7bedf55a6b78e0,-0x28aa15f58a928caf48f340b104,0x641edcbd9c0fec910eceb6ef08,-0xb3c7eb690afbe5a1a68c3cc368,0xf3513699e05c849f3fe3344808,-0xfcf2df7ca133fef15b320548e5,0xcbf42874c9ed87c56dc8b81eea,-0x7fe30bc2e161c2740e1b65449a,0x3e2501a73663504d9b7703c1da,-0x172dc127f7af370071aa28f9bf,0x686f5324e895f34988ac06e9c,-0x15a7c48718be1271a65397704,0x3301ba4e28390f658f9eb20c,-0x50e034f5f79d34d21bb6813,0x4fc4808ceed8b91db777f2,-0x2b506836505aa6dc2f7ea,0xa97f4edc20ba43ab8f2,-0xcf3f24cd7a9ed7a45,0x229f131d2400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 12 42 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 42 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 26 indices rho q11 m11 11 53250009120000 15=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 26 indices rho q11 m11 11 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r12 : List ℤ := raw_ints% [-0xb1521c7f80d668b37400,-0xffa812bd28ec45a6d880,-0xa4ff6477a12015adbe00,-0x3efbc2de888601755738,-0xfd0e920431b7150f0f4,-0x2bf073bd2255b274332,-0x5638a0ffdb4e891de3,-0x77a433c8d3596713a,-0x7331334ba8f2b9b6,-0x49647808f9cec1e,-0x1be4a2c40a9e53,-0x4ccab599649e]
def m12 : List ℤ := raw_ints% [0x0,-0x258372e7c3930c9396aa19240,0x1ceb92ff96266f1c5d6dd351f0,-0xa55929d250183558d8cdcc37a0,0x2451db7ddfa28207e56ab924f9c,-0x57bb571838f2faaa81c595d1238,0x9a4579a0424a5f6e05982686fd0,-0xcc08972e090a72ffbf663c94fe8,0xcec3b7a8431905aefef85479703,-0xa20b19f18749d04214bbce83b36,0x626be5cdfbfddf55fd76733738c,-0x2e22f17c93a0a178df2af314482,0x10847b226206e2b503efdf66f7f,-0x46fff701b2605b8803a768eef4,0xdf05c6d47c4100698049552a0,-0x1ec978aa68f7ef676a855fb4c,0x2d36e5b2735ffedcb6f333a1,-0x28a5bcea64fce447b16e83e,0x13b2a411253f2f545a8814,-0x42e71c49fae22e07f1ca,0x447152e825ff68d641,-0x9198ad93b000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 12 44 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 44 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 26 indices rho q12 m12 12 53250009120000 15=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 26 indices rho q12 m12 12 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x4ccab599649e,0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r13 : List ℤ := raw_ints% [0xf38c24788505aa856b800,0x15e8f5aac2ea1b8d6c8f00,0xe1d04b1067d12d16b7180,0x5601c532de158d3bca650,0x158abcb2e2dd9845372a0,0x3baad585de18e945bd18,0x74acc9e430898f1a9c0,0xa13c88f1a490ac0b31,0x9a7dc40c1c8fd8938,0x61ddffc96c0cfd7e,0x24f087017a11808,0x64da21a443009]
def m13 : List ℤ := raw_ints% [0x0,0x232b3bb94759dbca5d3f7791c0,-0x1abbe23ff7147af370bd135cd10,0x9686daf3ed49400c621b8e382e0,-0x20841efd4f68314c0b56b06edf04,0x4d1e1fa23be432eb97c64aef7b08,-0x84e5c35eb96ab79f99c63974a688,0xabe1e6ef277e294f1edc22755748,-0xa9e808b4224a0d5fb7fc483286e5,0x8180a3230b338dde69a7603dabaa,-0x4c3a5b9e08e34b964818ab1b2902,0x227b911f6232b906acb5b801852a,-0xbda1a715683934d2997c875a467,0x30999690a23dcc7ea59455b7bdc,-0x907c78cded2b1ba1158416fd74,0x12b0aff97f848c52443f992b2c,-0x19654da7f14900c2eaaa42023,0x14c7489308cc062d8c254972,-0x8f87be7ad7d5e01f6423f2,0x1a66decf71f315efd73c2,-0x16936eaed62ed1a938d,0x2638b6e1c4000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 12 46 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 46 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 26 indices rho q13 m13 13 53250009120000 15=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 26 indices rho q13 m13 13 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x64da21a443009,-0x4ccab599649e,0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r14 : List ℤ := raw_ints% [-0x13fdaeba20971f4fdf30400,-0x1cbbad5934b372189c08280,-0x127a3d417a79059953a1400,-0x70626b2551ff5643df4298,-0x1c15f7b8b4dced2e02b1a4,-0x4d977ab341bd933476b4a,-0x97452ab8a0ab5aa79957,-0xd050ca799bb4c56fb46,-0xc6c96f2beb3290527e,-0x7d52c8e6a82e08f3e,-0x2f08a7ac65774167,-0x7f89bf9abc4bfa]
def m14 : List ℤ := raw_ints% [0x0,-0x20f887fdb2e43e0db76b8018a40,0x18bb4b7e46a997b3f7b29bbf03f0,-0x893dfd742346c56562deb026f1a0,0x1d2d5ffa354ab6d05443ef993c09c,-0x43fe5d54cc80ee08b24a9fdb22438,0x72eac332ec21bd138452cec63b770,-0x917235513d02d2f03660ace4c1628,0x8c55d7dfb8e610810ae80e15844c3,-0x681676f918b5abf68e30e414a0e76,0x3b6790991afd3dcb790c0abe65b94,-0x19f0da21a4b8e178d03062cd08d92,0x88fa0f91eb7af6ca9790164f0387,-0x217c6f139d2281b10108a74d2434,0x5e2f60340ee80aea107740716d0,-0xb68739034fbc44998c1888bdec,0xe53390fbf1598c7f485094b31,-0xaa6b6b20ffa5c48309e9f33e,0x417044898d761fed718aa3c,-0xa6a4eb169a1023795985a,0x770182f281d5f4c93e9,-0xa05ad64eb0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 12 48 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 48 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 26 indices rho q14 m14 14 53250009120000 15=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 26 indices rho q14 m14 14 53250009120000 15 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<15) : intPolyRF (mz e)=rfPoly (C (53250009120000:ℚ))*rfX^15*(1-rfX)^10*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V4C16
