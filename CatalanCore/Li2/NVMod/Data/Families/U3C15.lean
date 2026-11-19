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
namespace CatalanCore.Li2.NVMod.FamilySource.U3C15
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,3,15,size⟩
def bases : List ℕ := [1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14,15]
def num : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x32be93e400,0x4b59a70680,0x3260f44b00,0x141192e958,0x54efe2d54,0xfba3551a,0x217700b7,0x338f256,0x391df7,0x2c646,0x16fd,0x72,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x5,0x5,-0x23,0x126,-0x93,0x14a,-0x1545,0x1eb9,-0x4fe1,0x49f]
def rhoDenominators : List ℤ := raw_ints% [0x43ad0,0x4ec,0xa8,0xc,0xc,0x19,0x5,0x7,0x70,0xfc,0x708,0x294]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 16
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
def r0 : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x394e95415dbfc00,-0x3d34451eb00c5f00,0x1edf16895c831e280,-0x9c61cd3be47203bc0,0x22d5b2e55477b729e0,-0x5ccc45dbc5eb0b2660,0xbf974cf71b465dd8f0,-0x139acf9019b2b0863a0,0x19d3ad569a9043e61b8,-0x1b9e188fa0e04df3dd8,0x181296dbe373e56ed8c,-0x111b9c4f2b2adbf4814,0x9e0b8c4fb09d61b63c,-0x49931254e0cd0951a4,0x1b460de6688fa14058,-0x7e6ba18b262e22a38,0x1bd8305298ddd1200,-0x47981707280d9690,0x7df59d38777b67c,-0x88074eef749744,0x48eaa2214e75c,-0xb1191bb2524,-0xe9e86090,0x4df82030,-0xf980670,0x16ae950]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 12 22 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 22 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 27 indices rho q0 m0 0 143988024660480000 15=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 27 indices rho q0 m0 0 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x35b9abed47e3c400,0x37f5c93f58baa0700,-0x1b8060a3858cc22200,0x8796bcdb0978cdfcc0,-0x1d5c8c7b20350ae9080,0x4bf0a6055f897ca6240,-0x9800a4fb7e6ff75b700,0xf0e1a270e3fdf974ab0,-0x1329a8cdd859e6ee59a0,0x13c215337fe737a09350,-0x1091213d22fe9b53d9c0,0xb4b92fbc4afeeabfbb0,-0x63c9d9a0f2395e29ae0,0x2c41dc69e0d077ff7d0,-0xf8ef89f4459b9c3180,0x44012ae19c82b3c690,-0xe05950c5e321c9b60,0x216d7d97b9a6c6170,-0x35cd1d65c2b78fc0,0x34173df9177e650,-0x1832850a8aa7a0,0x2f947fabba30]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 12 23 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 23 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 27 indices rho q1 m1 1 143988024660480000 15=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 27 indices rho q1 m1 1 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x325e112e736587c00,-0x33389c0fa4681cdd00,0x188d7a5e57f20d52500,-0x75f137bee5134c31a40,0x18dad94cf4509c6cb240,-0x3e7a2512b84d97b3cb80,0x795cba2dc6deb9ab2680,-0xba5733db7f2a1a819bd0,0xe560b9aae67288736bd0,-0xe43e35e1b1cc288bf8e0,0xb83f82dfe1ca2f2162a0,-0x7899bb65676a21fc9d30,0x3fb86429078c3be5f1b0,-0x1aefa590c17a77fa5c00,0x8fb7c4d4271cf704940,-0x25054e5e04658d06830,0x724966c52a63b27730,-0xfc606e356036f6260,0x172f2617e82dab6a0,-0x1410f593293ffe90,0x80a8bad5da4f10,-0xcbe6957fe640]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 12 24 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 24 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 27 indices rho q2 m2 2 143988024660480000 15=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 27 indices rho q2 m2 2 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x2f38301b8c2f2f4400,0x2eeefbc663339cb4b00,-0x15f7740600ea85cd8500,0x66eaf7d41b71a2ffb5c0,-0x1520ddbafb8c23fc14840,0x33ab3bddecd5313175580,-0x617f9e7954fe5756f3480,0x912db152618187cee6b30,-0xacfbcbb79e0399526ef50,0xa641137a6fe410d39fc60,-0x814e7d257457150c6ac20,0x514fc4c6c7c3832b0da50,-0x2921e14a175312393a2b0,0x10944c009d252e954c3c0,-0x53ed0765c77a07086640,0x14621bea9ef74bea7fd0,-0x3adacb2456f5e20f0b0,0x7843f41e4d1a9d2660,-0xa12319274287e6220,0x7c4f29e210fb8af0,-0x2aca37b8102c310,0x367d074c57300]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 12 25 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 25 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 27 indices rho q3 m3 3 143988024660480000 15=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 27 indices rho q3 m3 3 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x2c44ad19d36c3c4fc00,-0x2b0cb852bef0245a3500,0x13b199626ba28b93a8f00,-0x5a15d230f63e8ea214040,0x1208be0c3375bfb820dcc0,-0x2af27a269c3ca5289a6100,0x4ecc80d8d8af44344ec900,-0x71e4aa2896363bcce5ad50,0x8378c3176ace278bd16bf0,-0x7a24a841c721861e29a0c0,0x5b987a00fb94a0593d09c0,-0x375e6b5929a29cd7739d90,0x1ad47178b9a992344ac830,-0xa50ad5e330f2e95542100,0x318c086c7012ab4fe2400,-0xb5818076a75034723870,0x1e9e9794bc3162fab450,-0x39d5b97ad87a633e040,0x468183b10cd952ee40,-0x3056afa5d4087c070,0xe3c48c3923b4ad0,-0xe87a95c34c400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 12 26 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 26 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 27 indices rho q4 m4 4 143988024660480000 15=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 27 indices rho q4 m4 4 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0x32be93e400,-0x4b59a70680,-0x3260f44b00,-0x141192e958,-0x54efe2d54,-0xfba3551a,-0x21770093,-0x338f1d2,-0x391d36,-0x2c5b6,-0x16c3,-0x66]
def m5 : List ℤ := raw_ints% [0x0,-0x298062483635788ac400,0x2787038d3cb2eb5747b00,-0x11b11747b7cea1b6581100,0x4f171f66551a28f44419c0,-0xf745475fc544a85a48b340,0x23dfb2545abee556f03f880,-0x400eee4f7bfc4e36a0bcb80,0x59f383423295ec4319b4630,-0x64ad6ab6c0c2e399eddcf10,0x5a7bd0ba85f640fe46fae20,-0x4177e56753f2cd7d0be28e0,0x2610e11681585183f24a590,-0x11ad596c926065b35cbcab0,0x67c0462b0f91f0e2e48140,-0x1d8e98901196f9c47d4ac0,0x660d0b4915d311819b150,-0x10155b016912d7ce49070,0x1c0c342472e33901fb20,-0x1f0d1e6a4e22ac601e0,0x12dd532c6b90c07b30,-0x4bc44bb0fb530c90,0x3dde7fcd6d3000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 12 28 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 28 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 27 indices rho q5 m5 5 143988024660480000 15=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 27 indices rho q5 m5 5 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x66,0x1]
def r6 : List ℤ := raw_ints% [0x1437eeecd800,0x1dd2f9f8b300,0x13c747aedb80,0x7cc9f94ae10,0x20967b32620,0x5ef415bb08,0xc59c6f3d0,0x127398db1,0x1388fe98,0xe1e2ae,0x66318,0x16a9]
def m6 : List ℤ := raw_ints% [0x0,0x26e85c23b2d2210217c00,-0x2454473c1d634cbc327500,0xfecb01c160d01e12d93700,-0x45a40efd4435fcb128e9840,0xd4b8696afaa9291249816c0,-0x1e1beeae830347ce1bd78100,0x345f08f0adc7bb1c0e0eb500,-0x47819fc3d50b5bd7ff792350,0x4da95232bcb286168bb29c70,-0x439243ed458d4d0532e4d8c0,0x2f33c9d8379c5c850d6d64c0,-0x1a69cc4b6f4557a233616390,0xbc2880930927fd0ea45c5b0,-0x41df0ade58048596b67dd00,0x11ceea141eca9fa7590e200,-0x39ef6bf19dabb74d4b8a70,0x8863f36417e71c0b1cfd0,-0xdb5429493d9d5d16b040,0xdc1313c0172a62f7140,-0x7623c151094c533a70,0x19317a93d85921750,-0x106f25988964000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 12 30 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 30 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 27 indices rho q6 m6 6 143988024660480000 15=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 27 indices rho q6 m6 6 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x16a9,-0x66,0x1]
def r7 : List ℤ := raw_ints% [-0x47de085398400,-0x6973a9ae57280,-0x457c405bed000,-0x1b2faf25abf98,-0x707e5e1c7664,-0x143cc070440a,-0x2975d8977c7,-0x3caba46af6,-0x3e70e745e,-0x2b55e99e,-0x1270857,-0x3b42a]
def m7 : List ℤ := raw_ints% [0x0,-0x2479d66177a4fef1f64400,0x216c00331979360782a5b00,-0xe5c7cc380688e69462d0100,0x3d7eb523f00848f52a7b19c0,-0xb7afbd13736287e48a3e4f40,0x196370c81aaf6ff63515e8680,-0x2b0d7bb13ef7a81908e986d80,0x39344028cea81b6e672b64230,-0x3c554f4e3fbca6384297a3e10,0x32db059783c7a6a9d826f5ba0,-0x2251ef8d14b80be6863c9bf60,0x127df84732d544388cb8cae10,-0x7e584c3fad8b54764ac81530,0x2a38ae66da8a5d096cefb640,-0xad4f8cb65ec9348ecf125c0,0x2131718556e555d246dde50,-0x48e6645668d5ed82dac470,0x6bf6518960405f79e22a0,-0x61fcb10450eaa1161660,0x2e59838f59e901b01b0,-0x85f1d0e0283a7eb10,0x45b8e92efc30000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 12 32 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 32 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 27 indices rho q7 m7 7 143988024660480000 15=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 27 indices rho q7 m7 7 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x3b42a,0x16a9,-0x66,0x1]
def r8 : List ℤ := raw_ints% [0xbbf20eec936800,0x112967ab43f8d00,0xb40011f2eadb80,0x45fc9ae4755870,0x11f6694333c030,0x33383c1d3c7e0,0x67b56bbb85fc,0x9580b34c255,0x96e0b12b90,0x65fa14b1e,0x29cebfe4,0x7f325d]
def m8 : List ℤ := raw_ints% [0x0,0x223238fb602aaf02d6dfc00,-0x1ec69ded4e103cfb3b685500,0xcf9b7d4f764bb0d2d2765700,-0x3673ac1b57251971b913db840,0x9f31d91e2a12f9dbf86bb5ec0,-0x158131048ee0c7949abfae0b00,0x2394ed07a69119ee5ddcb0d300,-0x2e0b480d78aa908a6599764f50,0x2f31dbc750b78a6bb819fa2a70,-0x2690a44ed5dca23bed0a205940,0x1928591ee3578976962cf3f640,-0xd0efeb64d06a5baf2f742c510,0x559a64eb2c50e542853ac3830,-0x1b4fa0aa367a2f092b11ebc00,0x6a6073ce75fc92dadd53ff00,-0x132eec40d6d695ce69747970,0x2745d2c479b851334c5f2d0,-0x357dc19e532c7db056bec0,0x2bd346cd07fa7cdc92cc0,-0x1237b796e94adaea05f0,0x2c78b7ae40eb7783d0,-0x1274de0cfc440000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 12 34 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 34 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 27 indices rho q8 m8 8 143988024660480000 15=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 27 indices rho q8 m8 8 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r9 : List ℤ := raw_ints% [-0x193687063a41d400,-0x24b45aaf7ddef480,-0x17f56bf37025b200,-0x944aa88e3af1978,-0x25d3ed8ef678714,-0x6b111f45a73e42,-0xd6d1aff54389b,-0x1322d17f34f42,-0x13090eee5e66,-0xca07c487de,-0x50c6778cb,-0xed5ad86]
def m9 : List ℤ := raw_ints% [0x0,-0x200f156baa280412a971c400,0x1c5d66143298003532812fb00,-0xbbe915b7a2b17d7e79e9d8100,0x30582b2e88f3cea560addfc9c0,-0x8a7502b7582ef6bcc5b1036f40,0x124b79ffe148c4b5236e9c75080,-0x1d8f5eb87afdb98eda47b107b80,0x254850b0462084a2b4605102230,-0x252a16272a2c8b51347826e9a10,0x1d75ab1eeaa757e1532e7a1ec20,-0x129656a534bcccc224f56564ce0,0x94c80140f748e59688f0a01390,-0x3a80caeb1a020f85ed8e6f69b0,0x11d26c65e0b97fda8ad9f8d540,-0x41dc62c844d0478e866bc3ac0,0xb2d938804a0127f12fe68950,-0x15502ad97da930123329f970,0x1aa93df11cebeaa478ea120,-0x13ad9de1b2cf61e5e2cde0,0x72b953e4c10984cfc930,-0xec03c7dd481c597d90,0x4e0c437104300000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 12 36 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 36 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 27 indices rho q9 m9 9 143988024660480000 15=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 27 indices rho q9 m9 9 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r10 : List ℤ := raw_ints% [0x2f0c70cde667d5800,0x444954653fb101300,0x2c6a5d290bfaf4d80,0x111c0d66d00a8ea10,0x457b8e9688e26480,0xc37b945633b9688,0x1855f9d4461cc88,0x2260b681ccbe69,0x21d230fb54b08,0x161f9ec0b83e,0x8afe517990,0x18ebfcce1]
def m10 : List ℤ := raw_ints% [0x0,0x1e0e2414ef8583d17edaa7c00,-0x1a2a5b77f1aa2e5a54ce90b500,0xaa609b29ae2d59a73dcc6a5700,-0x2b087b648108a66dd55e3723840,0x78d57326890ff8521262d101ec0,-0xfa156cb6e86ffa8ca871d370d00,0x18ae6014e68427ca6db5e6366900,-0x1e5ce6a64c067f6e5880f4348350,0x1d74ab88dcf449858c8895aede70,-0x16aa159258a39a1d98c495571fc0,0xdd692e325d000b5b22958151dc0,-0x6acd99adf8e3e9745a58c1f4090,0x2851419b697edf99a39d39342b0,-0xbba70e2e12b5add8fec7d98f00,0x291d5e079684c77508356d6000,-0x6906e7d2eee3a247de3632470,0xba561a9cbb8d5d615b8a2bd0,-0xd5c437196ec5ab84371fb40,0x8dda1c70d7bc41e1cdd640,-0x2d32b5fda53e21cb3f370,0x4e33a3a3603c50f8450,-0x1498d2b98d6400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 12 38 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 38 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 27 indices rho q10 m10 10 143988024660480000 15=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 27 indices rho q10 m10 10 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r11 : List ℤ := raw_ints% [-0x4f0a4eb94675ab6400,-0x726d0ed08557fd5e80,-0x4a33e52e13dc69d800,-0x1c7bb5c076ad09e8d8,-0x73308834c6287dcc4,-0x14278e7f7b3e21f5a,-0x27e85c68e576de4f,-0x37f933573f1b90e,-0x3696aa91906bae,-0x23531eaf4c07e,-0xdaef068181f,-0x269317c2a2]
def m11 : List ℤ := raw_ints% [0x0,-0x1c2d41d3a08d2b9466ecfd4400,0x1828280cd483c3d816486d29b00,-0x9abd24e66d62435084338474100,0x2666b71f50842ae6d60802c879c0,-0x69cdb63cc79f2be9dd6287885f40,0xd689e7b516b8f9cac54d18fc1a80,-0x14b54a79150c07c2253a5ecf2e980,0x18ddcd976f202f20275553dc8c230,-0x177e3448ecab121acbfcac42cfa10,0x118e975a73209f92bcbff8f22fca0,-0xa61091fc221ec04143473966f260,0x4d45082b43af98b3e7f3eea8f910,-0x1c0266787710dd2994646cf84a30,0x7c7eabebf9c25914dadad573440,-0x19dea883042849451aad5c0ffc0,0x3e2155c877709c782bcea03450,-0x6677f013aada1de4f49d50a70,0x6ba58f4301f20937250e5fa0,-0x40182fb87d640a6d8a19d60,0x11d173d8d0cf8b619250b0,-0x19e1f0b9f80cb7405410,0x56d88e93853000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 12 40 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 40 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 27 indices rho q11 m11 11 143988024660480000 15=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 27 indices rho q11 m11 11 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r12 : List ℤ := raw_ints% [0x7a5721877be285e4800,0xb0b8ff57e15ee73b900,0x724e98d9bd8e0701780,0x2bbefdda731164a81b0,0xb04adf10173cb46e50,0x1eb7cc436b34a7b1b0,0x3c86ba3bdcd680274,0x54659c1373f1a81d,0x51bb0f67f196b40,0x346fd58cbc189e,0x141917e40859c,0x37e902c9405]
def m12 : List ℤ := raw_ints% [0x0,0x1a6a6db6668458db207e2d6fc00,-0x1652098edcf138f18ed1d3271500,0x8cc3372dd18f80654c54ff7cd700,-0x2259c5c6be2b27afce2146a7a7840,0x5cf0a8384481420b79ef0c78a7ec0,-0xb8c75a218446cdc379b90ae0cbf00,0x1174f9773ed5d5e24d81f91a08cf00,-0x1479cf294db8866da76610300ac750,0x12da0843e5fb921eeaaad870987a70,-0xdb111178c01757fff2c99766b2240,0x7d7350db09b11961d8f1a75542940,-0x3853a29ac56a3b5286aae687d8010,0x139c4c61985b5b2903bcee15e4130,-0x533d3ea08ce077c89206bf896a00,0x106682fd08de54dfa78a2b31b900,-0x2502642cfe9517a7f7147b3e770,0x38ae8e8431119901fe2d5e34d0,-0x36723a29c75dcfb713d3d83c0,0x1d07f9d6ea5d731e079c13c0,-0x706ddbbe9d40e9889cf4f0,0x88e78a4f442fa05b78d0,-0x16db039e3cc4000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 12 42 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 42 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 27 indices rho q12 m12 12 143988024660480000 15=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 27 indices rho q12 m12 12 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r13 : List ℤ := raw_ints% [-0xb1521c7f80d668b37400,-0xffa812bd28ec45a6d880,-0xa4ff6477a12015adbe00,-0x3efbc2de888601755738,-0xfd0e920431b7150f0f4,-0x2bf073bd2255b274332,-0x5638a0ffdb4e891de3,-0x77a433c8d3596713a,-0x7331334ba8f2b9b6,-0x49647808f9cec1e,-0x1be4a2c40a9e53,-0x4ccab599649e]
def m13 : List ℤ := raw_ints% [0x0,-0x18c3c6db001c134d6e764a98c400,0x14a3c0786a21208e9094e52aa3b00,-0x803f60a690ff5a9160cd5c51d0100,0x1ecc87afd610478ab0e571f67469c0,-0x51e4b665163aaf51c61ee420794f40,0x9fc289c9c95b807a315ce1562d7480,-0xec8989182fbafeea770bef6d790780,0x10f30e00b78436aab5bac6dc2871230,-0xf378885e869b3f3c2601eb191c7a10,0xabf28ed56daa52eb64032d6465e120,-0x5f6e4c2038cfa3088fa68c87d813e0,0x295c86b4f02b96424aecb4f35d4a90,-0xdd564eab4a2a5704c3ff2bf559eb0,0x3812a71443220b0124c48ad94ab40,-0xa78dd0eac5529650eb0275670cc0,0x16309482ac2e52ff409e74ffa750,-0x1f86943e39f50e6aea08ac66370,0x1ba5789bb1c45e173f1e326220,-0xd2d18e0fe6d558f1302738e0,0x2c57c07c91e065ff740f430,-0x2d34d197ea7d8f3570e90,0x601dca967f30000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 12 44 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 44 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 27 indices rho q13 m13 13 143988024660480000 15=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 27 indices rho q13 m13 13 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x4ccab599649e,0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r14 : List ℤ := raw_ints% [0xf38c24788505aa856b800,0x15e8f5aac2ea1b8d6c8f00,0xe1d04b1067d12d16b7180,0x5601c532de158d3bca650,0x158abcb2e2dd9845372a0,0x3baad585de18e945bd18,0x74acc9e430898f1a9c0,0xa13c88f1a490ac0b31,0x9a7dc40c1c8fd8938,0x61ddffc96c0cfd7e,0x24f087017a11808,0x64da21a443009]
def m14 : List ℤ := raw_ints% [0x0,0x17378a6d501a5218978ee5ef37c00,-0x131981030f1e2a4c3ee5c027397500,0x75050ee741c1e072e23102ab5c5700,-0x1bad28dde9e61e3fb6487d87629f840,0x48601b5752f56e28baae21f14971ec0,-0x8aa490dba1f118d5e3b5c3661a28100,0xc933cf6d6979bc7d97e32ead788e500,-0xe1a24f32cbb52c196bd4de68d1abb50,0xc5a819710d07eb7c04350a321160670,-0x87d0722d7643158e0957c77da4658c0,0x491619490bb1890b9d9c3f6deefb0c0,-0x1e968e4289f05863587929ceaa70b90,0x9d451bb29ce88fdea2a221f0e4c3b0,-0x260b87217a33e35370c22fc9215d00,0x6bb8cfeba6bff5dfa6422f4ad1a00,-0xd62e22ff31313ba59dca276b7270,0x119f59326f561c81ee02af6b35d0,-0xe164f85cfe72c45063db937040,0x5fd77b50879fc88c6e6d25d40,-0x117cd06b03a4de63bdcd3270,0xee8e7c877158ea8b68150,-0x193b70bb0a640000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 12 46 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 46 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 27 indices rho q14 m14 14 143988024660480000 15=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 27 indices rho q14 m14 14 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x64da21a443009,-0x4ccab599649e,0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r15 : List ℤ := raw_ints% [-0x13fdaeba20971f4fdf30400,-0x1cbbad5934b372189c08280,-0x127a3d417a79059953a1400,-0x70626b2551ff5643df4298,-0x1c15f7b8b4dced2e02b1a4,-0x4d977ab341bd933476b4a,-0x97452ab8a0ab5aa79957,-0xd050ca799bb4c56fb46,-0xc6c96f2beb3290527e,-0x7d52c8e6a82e08f3e,-0x2f08a7ac65774167,-0x7f89bf9abc4bfa]
def m15 : List ℤ := raw_ints% [0x0,-0x15c411c67b18acf70e15f790444400,0x11afe5f2c4577ff53f66484a1dddb00,-0x6aed912807efad75bcc9eb1acf1c100,0x18ec932147e2ee3486852950c3fa99c0,-0x4025dff9282f6fd345541cb3d240ff40,0x78bfe67998e362f5a00dee0886e01e80,-0xabe1600f3f29231276407ca3e0eb9580,0xbca910b55256be25c419036f38005230,-0xa15b800d225fcf6af41177ddd28f0a10,0x6bee32ff84211c5116c739a94f6009a0,-0x38575e75488f3aa41458e4510bfea160,0x16c6d144ab054fa77d50d324fd6c9810,-0x7088399b472ff48997bcd52c163a730,0x19fdf9bc18993a9121fca20a9af5a40,-0x45b53acc90d163c91ab67caf3701c0,0x81f4354e94c88b255de8056804250,-0x9e571951dee064abaed5e9437470,0x73341b8cb5aa9e6bbd8ab9f58a0,-0x2ba1201e004eafbb2b109f5060,0x6e516f315dcc5da9b4f383b0,-0x4e969d318f556198da4d10,0x69dbf779f2300000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 12 48 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 48 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 27 indices rho q15 m15 15 143988024660480000 15=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 27 indices rho q15 m15 15 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x7f89bf9abc4bfa,0x64da21a443009,-0x4ccab599649e,0x37e902c9405,-0x269317c2a2,0x18ebfcce1,-0xed5ad86,0x7f325d,-0x3b42a,0x16a9,-0x66,0x1]
def r16 : List ℤ := raw_ints% [0x1947d9561d531726e038a800,0x244a2a5068e994f64410d500,0x174d79f3277cd9fdcac9bb80,0x8d7e07a87d1dd4feb3a93f0,0x234a8ec82ac439729509d70,0x6147763eb1e34b8c8507c0,0xbd2936afa8f70f488e46c,0x103b6f110d40d2d1c40a5,0xf6f8caa76973e9ba4f0,0x9b1179e59f57a3cfde,0x39eb50b3d97be02d4,0x9c2afa6826293ed]
def m16 : List ℤ := raw_ints% [0x0,0x1467d0aa136722279d3498173fffc00,-0x1063e4f38177d939f750eb6628ffd500,0x61d741a7d571cb6ac81087af7a3ad700,-0x167df9991bdca7402975cc7ff6a50b840,0x3903771cadd35d7cfc47f96d1f17e7ec0,-0x6987d6b8686a88ba3b29e30e5d3925300,0x9370dad54fd19b97d787f6f904f93ab00,-0x9e80acf92fe931b396fc00469bf625f50,0x846fafc17e6d12b4c2df81b4b88e82270,-0x5647e14e2f00fb6e973399d98a8994340,0x2bb5a64b3c69528a7378fa45eedd4f440,-0x1112baa89ae2ec687150e38df397b6310,0x51111e06b1d9a08aa4a192e30cc72a30,-0x11e031aa04a2d6d018dfcf40b8ab6800,0x2d63a07e69dfb539299f2099ad30300,-0x4f46e229f0218abbabeeee16e1c570,0x594ba5ce1d2b3c6e645400a0b8ed0,-0x3b0ac85c5fc4c72958390c4b40c0,0x13e1c0512428c5e535fa810f2c0,-0x2b7a9bf38c62088fad1d32bf0,0x19dc2111b421cbdc8d4bdd0,-0x1bba1a0ff64400000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 12 50 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 50 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 27 indices rho q16 m16 16 143988024660480000 15=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 27 indices rho q16 m16 16 143988024660480000 15 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_16
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<17) : intPolyRF (mz e)=rfPoly (C (143988024660480000:ℚ))*rfX^15*(1-rfX)^11*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U3C15
