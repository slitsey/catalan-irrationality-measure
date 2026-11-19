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
namespace CatalanCore.Li2.NVMod.FamilySource.U4C16
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,4,16,size⟩
def bases : List ℕ := [1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16]
def num : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0xcafa4f9000,0x10757ad2f00,0x9a844fa1e0,0x363d74cfa8,0xcb1003bbc,0x2160cd0ce,0x3f41a3ef,0x571208a,0x566c4f,0x3c582,0x1c25,0x7e,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0x5,0x46,-0xd2,0x14ac,-0xca2,0xaa28,-0x33d83,0x18f65,-0x22f27,0x127c]
def rhoDenominators : List ℤ := raw_ints% [0x3624,0x2a,0x4,0x3,0x1,0x5,0x1,0x7,0x1c,0x12,0x3c,0xb]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 17
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
def r0 : List ℤ := raw_ints% [0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f1000,-0xdadfe28e67cf1b900,0x691601a2412b65d1c0,-0x1f9aa8e3256ab6445c0,0x6ac28852994fb46d0b0,-0x10ce4bdcc3918bdf8b70,0x20b7311f5fb16e483760,-0x32595380a35a7e8639a0,0x3e22989e2fb31bd8715c,-0x3e0012c54c6cd80b230c,0x323429074132329d4f18,-0x20f953984b06842a2638,0x117d4070c5abf4722324,-0x76cf0d5d7e1dfde94f4,0x27d1af5cdaddac31eb0,-0xa515843078b84bf500,0x2013bef462350bcb14,-0x47737af34b56f1124,0x6a2fdfb9fb4cf228,-0x5d49a5e827eba58,0x2636d2870a4c0c,-0x3ee1543bf67c,0x1d3d0c120,-0xe9e86090,0x4df82030,-0xf980670,0x16ae950]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 12 24 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 24 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 28 indices rho q0 m0 0 35997006165120000 16=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 28 indices rho q0 m0 0 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f10000,0xd63814465c656bc300,-0x64928ec9bdb950e7c40,0x1d8c2d6234c76154f9c0,-0x616655c454d9b2524f50,0xef19c49924f9b69253b0,-0x1c50cd99025627a0ece20,0x2a5a5e5c1092b24623b60,-0x32b69f5e7615e233f0824,0x31013ee277870257ca05c,-0x2657dfe550b01129752c8,0x1845ed58cc3ef19558418,-0xc5f2dea364db4c50883c,0x507a0a3c7cd538325ce4,-0x19b73be29028d0614a90,0x651b1b85048200fc5b0,-0x1281145370895e89e9c,0x2679b66f9d2efa1324,-0x34b78dcb5bc3ad7c8,0x29eca239fd3cdb98,-0xf189dd8dd08234,0x14bcc87dc3e6c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 12 25 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 25 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 28 indices rho q1 m1 1 35997006165120000 16=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 28 indices rho q1 m1 1 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f100000,-0xd1dac2e2d1b256f2d00,0x606d7e62c43ace792bc0,-0x1bb30b6ef170eba8deb40,0x592d37cfc4bbee7565730,-0xd58b0b67448dff0318990,0x18a281321c6addf044e440,-0x23d6d3c7708290dcb34340,0x29aad147e9bea172e3b5bc,-0x27045627e52c653dc704f4,0x1d842048778b545d1243f0,-0x12049e40e6c48cf109fff0,0x8d40c602ccbbb7a26880c,-0x37003ab325a28f0305e04,0x10c1cc05a84ccf5011900,-0x3e773504c1a96955adc0,0xac31fdd3a1736a461d4,-0x14de41822fb26b176fc,0x1a51af2a92a7857210,-0x12e733327202c90d0,0x5f717fae8574a34,-0x6d498beac227c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 12 26 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 26 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 28 indices rho q2 m2 2 35997006165120000 16=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 28 indices rho q2 m2 2 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0xcafa4f9000,-0x10757ad2f00,-0x9a844fa1e0,-0x363d74cfa8,-0xcb100397c,-0x2160cc76e,-0x3f41939b,-0x57110fe,-0x56636e,-0x3c262,-0x1b7b,-0x6a]
def m3 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f1000000,0xcdc346957faa736fa300,-0x5c9e24ddbbd91738a8840,0x1a0906698df8b12ea870c0,-0x51ee74f92b3cde9eed4c50,0xbf88fafc803a02dea4c370,-0x158a7edaeea4d2db8811ee0,0x1e80d1a8b7ef4cba7198e20,-0x22750342f830695557248e4,0x1f49333ba8809b1a190a48c,-0x16e53cf24fd728a1c8cef38,0xd7bcd6c5f616cd50edaa88,-0x65a64bd584e647d879c74c,0x25ea46b6081824e5e6c0e4,-0xb0383ee13d1a3670165b0,0x26eaa2cab85bce5d5be50,-0x64ee5171d0e5bf9edf7c,0xb651a4bd169066a9354,-0xd351ad5ecb944a9c78,0x88c17d6d64bcf27c8,-0x25b706452b112b84,0x23f2cdb423114c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 12 28 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 28 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 28 indices rho q3 m3 3 35997006165120000 16=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 28 indices rho q3 m3 3 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x6a,0x1]
def r4 : List ℤ := raw_ints% [0x540ba4f1a000,0x6c3f5365e600,0x3ef3714bd7c0,0x15daee0e59b0,0x50b0ca3ec30,0xd0704e3bd0,0x181b211988,0x20195e589,0x1e57c7b8,0x1396466,0x7e4f0,0x18b1]
def m4 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f10000000,-0xc9ed420d02c30e24a8d00,0x591cba111551c212738bc0,-0x1888b30363e17b036f28d40,0x4b87ac3a92b4ca13d69c530,-0xac835d563fad0aa0a8a7610,0x12edc2212d81c95b9860c340,-0x1a1bc5afc2e973c28f7a7340,0x1cacb9a5d7c0a566203aab3c,-0x1942b557dc14de001754f494,0x11e46c4a5cac5357931104b0,-0xa2b7ebecae13bcc1b4816f0,0x49bfe9b4d91c206c9d44ecc,-0x1a5afbd113255a38af6c5a4,0x74c9117f442cf253449780,-0x18708e4f7a5fdd020c40c0,0x3b98bf183d2b3b83580d4,-0x642e979bef21ab7909dc,0x6a8a116b87177cdefd0,-0x3dfbcf3656ebbb9cd0,0xee687715199b04f4,-0xbcf42c082a63dc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 12 30 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 30 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 28 indices rho q4 m4 4 35997006165120000 16=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 28 indices rho q4 m4 4 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x18b1,-0x6a,0x1]
def r5 : List ℤ := raw_ints% [-0x1393ce86829000,-0x1912403633df00,-0xe7afd9ed605e0,-0x4fc4fffef7b68,-0x1238378b4934c,-0x2e7765cbc23e,-0x5497372846f,-0x6e432355e2,-0x654526516,-0x3ec7f72a,-0x17d892f,-0x4422e]
def m5 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f100000000,0xc6549dcd0daa1f2e5e4300,-0x55e23fed485ca0101f31040,0x172d5959cdb7baba5db15cc0,-0x45dbc21a7875dbdaf28c2450,0x9c034e5db7cc44723a857670,-0x10b698ce11c1d4b9c5ab17f60,0x167851c5b2c9d86b34a8c3da0,-0x180272136a3feeebae07c17e4,0x148878b055e8d912958b9994c,-0xe156e807c447e9849680e0d8,0x7bab26d392cbd29e8ebddee8,-0x35eeab5f0d2f031b8608022c,0x1277c4e2d74c516a9aaaa8c4,-0x4e03f13cc972c8dcdd12270,0xf773778f8dd5e3603d2790,-0x236f8c6854afc0480e6c3c,0x375f33f262ce8ede3dbd4,-0x35f08ee734c1cd61c398,0x1c265d1abbf99e968a8,-0x5e286b7cf1a197ee4,0x3dffae5ce429f2c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 12 32 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 32 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 28 indices rho q5 m5 5 35997006165120000 16=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 28 indices rho q5 m5 5 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x4422e,0x18b1,-0x6a,0x1]
def r6 : List ℤ := raw_ints% [0x360623fbd6be000,0x44dded29cb9e200,0x278f0de9f56f740,0xd8806cc8509a50,0x310f9acc71b860,0x7bebf0ea60db8,0xdee973ff50b4,0x11e3336ce85d,0x101c58c7e50,0x9bb4e9c46,0x3912a17c,0x9b0975]
def m6 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f1000000000,-0xc2f583d117e2bf27785ed00,0x52e86c28457b56453dc033c0,-0x15f2db9f2ea15935f7c51b540,0x40d1ff75e6d0b57d229769d30,-0x8da66be02eef5631952cda010,0xed3823499411f5a76916d82c0,-0x137138380c4aa0fd34d56d29c0,0x14394c1dc70add8beb198d6c3c,-0x10ccbe2d8396ba3cbf63076014,0xb29f71acac61bede69114c310,-0x5eb037f38f1fb7ebcf6c00410,0x27be4e344635bc37f8f0f29ec,-0xd0aa983e17a5e6ead78f2484,0x348436046e1edeb19d0352c0,-0x9dbbee177256b38d85afe80,0x15356fb45921d2235e3d814,-0x1ec57a5a0d94955f8fd71c,0x1b6992378d7e283f060b0,-0xcce248dcb92708d5170,0x252b539dc4134f6794,-0x1451b901a69b843c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 12 34 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 34 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 28 indices rho q6 m6 6 35997006165120000 16=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 28 indices rho q6 m6 6 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r7 : List ℤ := raw_ints% [-0x7aed0dbd626cd000,-0x9c1b6e0be0619b00,-0x5945f2a9aafbf960,-0x1e6045ce4d10d888,-0x6d722bd49b84e9c,-0x1125de2277af3c6,-0x1e90556ad24583,-0x26cc8b667685e,-0x227391b65ebe,-0x146f3d4581a,-0x750228da3,-0x133c061a]
def m7 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f10000000000,0xbfcc5b74e177d52100d8e300,-0x502994848e64166b6e5628840,0x14d5a097308a9ca768384e5cc0,-0x3c555880b2ee892a504acf5850,0x811aff7482593225fe2360f670,-0xd364f8ac8fbdda14e5887a3ae0,0x10e90a37fe8093501f7ffe72420,-0x112264121647e18fdc37afcc3e4,0xdd53b739feddc181836737b84c,-0x8e8f922ab4dd5dddd486da0238,0x4905b1af1a22de226a46a7e408,-0x1d816c96404bd652e94610f94c,0x9476ea2ca2fa5912e33567324,-0x239cd44c503feef54c8546fb0,0x653efeed18bf062041bd3150,-0xcc5c7f1e3d404a96e33867c,0x112fbb36f6f6c84f3609394,-0xdfa64bb9efd84f4280378,0x5d52de6dd070cea5f148,-0xeaa06ef50568702b84,0x6a6e8f45524ae00c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 12 36 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 36 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 28 indices rho q7 m7 7 35997006165120000 16=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 28 indices rho q7 m7 7 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r8 : List ℤ := raw_ints% [0xf402b68d10974a000,0x134e53a0239843f600,0xafff12c6cfe0015c0,0x3ba016b13731f0db0,0xd5bc881ea26ba090,0x2149087d7ac1ba50,0x3ae562cf80b4c80,0x4a1bb9a7c64481,0x41184986d71a8,0x261775c4bc76,0xd6648361a8,0x227687329]
def m8 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f100000000000,-0xbcd5c59e6e7399baf0cb54d00,0x4da09d636ee6c13913547efbc0,-0x13d2814a78a1ab8311d72e7b540,0x3853d464283461657d916854d30,-0x761cecbcea18812673810f23010,0xbd375dc78ffe8ae114f976bc040,-0xec86654b15f469939a287530e40,0xe996669179303e7b98d7bc7ef3c,-0xb75f3bab71045ff1a8c35457f14,0x7289725c6a1bfdc916baca1aaf0,-0x38b54633c7e31b3788438a84ab0,0x161026e2a9d8def95eef191a38c,-0x6a65fd93e4a112939e2c3f4f64,0x18522859328c059863e2c5ab00,-0x416b51181a8be41c7b1ced540,0x7bcae7cea48b89704f7b6e54,-0x9a4bd4e4c52231f2d097fdc,0x72624aa71b281b3e20d510,-0x2a8d6663e98ee8f875590,0x5c8132368e14cfceab4,-0x22ce6b3c9b95b1b9c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 12 38 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 38 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 28 indices rho q8 m8 8 35997006165120000 16=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 28 indices rho q8 m8 8 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r9 : List ℤ := raw_ints% [-0x1b533923e36546e1000,-0x227f8fc6c42e564e700,-0x139837f07ce413496e0,-0x69d4769c45473da428,-0x179c23b321e91ff76c,-0x3a892f2bedd1e5a6e,-0x66f70e79257de3f7,-0x80a5f43f6c0e79a,-0x700aa741d09126,-0x40e2024b6962a,-0x1687a8ec6477,-0x3900e54c86]
def m9 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f1000000000000,0xba0e9925629fa20b41be9f8300,-0x4b48ea5bb204a92e7a8678ec040,0x12e6b96fe7340a1fb3d17dabecc0,-0x34be0f651930ad4a1141ff576c50,0x6c733a7d77eb9424624f13fdfa70,-0xaa185fccf5dcc45a32548dab0e60,0xcfca236b937b885e1088b2decaa0,-0xc8205c2343b545d4a416a44da7e4,0x98d7fa416a9f0440f291e6ccbc4c,-0x5c9e1f9764e49611ae766cc5d198,0x2c569ef437734c4e1b98879e1128,-0x109d0184d0d0b42ad6a6ee79226c,0x4cc936a2a41dbf69ed9b0fb3a84,-0x10b8f8c5127a02f8877f2d350f0,0x2a898649813ca8e9f20c326310,-0x4b664a0632c9b640c06b16cbc,0x56f234fee22be2dbf728ba54,-0x3aa78d3857ce76e8ddc0958,0x136add0d21756afda799e8,-0x2471e646de13c268e224,0xb5f07e5511a568bec]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 12 40 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 40 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 28 indices rho q9 m9 9 35997006165120000 16=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 28 indices rho q9 m9 9 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r10 : List ℤ := raw_ints% [0x2d327185a5ba74656000,0x38ee3ddd5e94052c8a00,0x204007252a01cdb85440,0xada5c1864ba58ddfb10,0x2699ff4d0fcdfc97040,0x5f4e9523d637d87c68,0xa6d43361860b368ac,0xcf3e101364d41c45,0xb340bbbc14e3dc0,0x66f2ab8c1568e6,0x2363610cc2134,0x586c7ef457d]
def m10 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f10000000000000,-0xb773df73e788e9d68da2b58ad00,0x491e5096d77fad7e94386b0143c0,-0x120fda1edf6d7bfcaaa6098915540,0x3186d2abc13b376ae53b717d38d30,-0x63ee1637b5248b30413ed980ba810,0x998c1b3df43d0c4c13365380271c0,-0xb76c4ad5b21505dc658bf94bdfec0,0xac616052a590e235e563ad0be0e3c,-0x802596c8659d83a695bd9bfe3c814,0x4b5d6bccba7060b1caa3696348bd0,-0x22e55d5cb25c9645bea9ccd284850,0xc982f335573abec12c6b91f7e42c,-0x37ca53ffca63e387bff79a547144,0xb92bb7563416991c8c2c6b2f140,-0x1bd333853da5a01bc62a43fee00,0x2e292055703c85d293dacd4e94,-0x312f620d0f73028c0acd8c09c,0x1e2566f84a04fdb34d2e9e70,-0x8dd8d68012dee4aafe44b0,0xe58fbf4921a2ddab00d4,-0x3b61dbb8806bf081fc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 12 42 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 42 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 28 indices rho q10 m10 10 35997006165120000 16=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 28 indices rho q10 m10 10 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r11 : List ℤ := raw_ints% [-0x461c119c001cb1aa95000,-0x582298055e9b4e9d59300,-0x31d013f401af54c76e060,-0x10b81c885b674262158c8,-0x3b4934a56b3c0cdcdbbc,-0x91dcbeb9e146b120a56,-0xfe47617c263184fa4b,-0x13a5d68a866c24acb6,-0x10e5fab3e9751114e,-0x9a3d25eb7233cba,-0x3497ad85194e2b,-0x822056f81252]
def m11 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f100000000000000,0xb502d15d84239d2524c88a322300,-0x471d0abe64601d087423f2c0af840,0x114bbe6fd4670636b318893992fcc0,-0x2ea2bdbafc1a139ccb755054c8f050,0x5c653911499bb5a75245b745d91e70,-0x8b2c7842048b3707391aa1dc618de0,0xa2abc31be1470473bb3e80069fb520,-0x95420a048211df72ccb2d2893e8fe4,0x6c0e30fe523861388c08b2b291004c,-0x3db3ab33523bee6abb24b90d3ecff8,0x1ba40bd416bd714e3f68b7e1097b48,-0x99c4d3ac5395a3bfec680ae27cc8c,0x28ccecb91e36a75c051d1b71d20e4,-0x80f446d8b4096c7f9af6dbe8a430,0x124e1fbfdd360ea9fe897a044ad0,-0x1c6568f8909c4597d3a6d6088fc,0x1bec2a3bc668d350bb759b4f14,-0xf864b062e83c84a73d891238,0x40c95657601adb46ff8bb88,-0x5a4d511fddeebaf1a1dc4,0x135d1356a431d391acc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 12 44 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 44 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 28 indices rho q11 m11 11 35997006165120000 16=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 28 indices rho q11 m11 11 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r12 : List ℤ := raw_ints% [0x672cc0a5d9be11459c2000,0x817a094467d448b01dbe00,0x49088bf8000e9d220e06c0,0x18750e2e01d2a8344d7370,0x567fac599add996450170,0xd42cc46b1b4b657c8240,0x1709870596fb8f034638,0x1c5db21f00362b125e9,0x184814797b39af9298,0xdc665102afb75656,0x4aa85d0fcb86120,0xb743d48ffb631]
def m12 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f1000000000000000,-0xb2b8d42886f4a53ed27c018f00d00,0x4541ae498ef7fda8a4eae036348bc0,-0x109881bf171ca74884c130bc849b540,0x2c07fe66482a17c5883aaf0412bbd30,-0x55b69a42029aeb0fd8e627817e01010,0x7ea4ff8f14b3803d4a7f3bd97614f40,-0x90ec3283320c0532b3ca1c593491340,0x81e521b47258d68c57d6b89d442513c,-0x5b9f21456a8185bf4edb74aa7c9d514,0x32d12613f76c0a6c87f9ec26fb73bb0,-0x1607dc8f9625cf2c9e08d5c06e13af0,0x7615c54f9c825206c4c894869875cc,-0x1e06c1aaea10fd2917acff72b34e24,0x5a581b55ea93cbf026645b0023980,-0xc1b8b3b6221524dd50c99909dcc0,0x118be7fb916227b5b77d38c114d4,-0xfe7164acccffba6922cb137b5c,0x8022416deccf6463bae473ad0,-0x1d988cea771e68ee0515b4d0,0x237e3e57fcb80599bafbf4,-0x64efd9d24e8f324cf5c]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 12 46 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 46 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 28 indices rho q12 m12 12 35997006165120000 16=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 28 indices rho q12 m12 12 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0xb743d48ffb631,-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r13 : List ℤ := raw_ints% [-0x914eb6ec35b7a8ee99a9000,-0xb612a75d46aea6572f3df00,-0x6685e545c1966947e557de0,-0x2243c4dfe9c383fc5472868,-0x78e93249a701703779a38c,-0x127d0fdb3478cdabd369fe,-0x2005e29cfe629e3b0c87f,-0x274b6f28f29c223c1032,-0x2180a074f99398abf36,-0x12eae791cfc1f1a74a,-0x65f82fd4d52b5abf,-0xf8b058f1234afe]
def m13 : List ℤ := raw_ints% [0x0,-0xd6e6afb51f8f10000000000000000,0xb09376c6d9989cd6e554417610c300,-0x438922015a9b294be3a439402f43040,0xff4775222b287a81fc0c762d5e54cc0,-0x29ae14b11ac1e9b1884a5c285e6da450,0x4fc55f7f9356d4cce0c2430cba2e5270,-0x73af89fe88ebd8f0065733754feee960,0x81ae6e8e37b92930c9f8264941d193a0,-0x719a9ed2af2d7eae7d32ad52ffcccbe4,0x4e1bc027246b8036ef839f1e476d904c,-0x2a18611c142c72d7db4b369ae85a5958,0x11aa716f4e933faac19d0ba1bf04be68,-0x5b3e002686740f964929ec10999dbac,0x163b618ba7bc549ec7480956b6ae644,-0x3fa8a064cd3f0ae19e456606ba7170,0x80ca5e93c7efdb7acffe8751e5090,-0xae33818942fd3567c938ebf6333c,0x91555473ab386c160db99bf1dd4,-0x42314f2f83a69e460eb5c1ca18,0xd854daf0a00740fc79952228,-0xdf06b8afb2c6335a9e5264,0x20db59d81eb163dcc4ac]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 12 48 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 48 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 28 indices rho q13 m13 13 35997006165120000 16=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 28 indices rho q13 m13 13 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xf8b058f1234afe,0xb743d48ffb631,-0x822056f81252,0x586c7ef457d,-0x3900e54c86,0x227687329,-0x133c061a,0x9b0975,-0x4422e,0x18b1,-0x6a,0x1]
def r14 : List ℤ := raw_ints% [0xc52e4faf6ffa15300a90e000,0xf6bd6c1c0654d7fe90d01200,0x8ab97354c31b0c6fda797d40,0x2e4887ed54e6bd35cb8f1ad0,0xa2ffa04d50ab36610ec7420,0x18de31a58ea1623d7c314d8,0x2af61a0f2db52f795d5324,0x348f9064268f792d3646d,0x2ca905dc006c5c9f3c30,0x191e501828b4410cbc6,0x86c53a56af45bf76c,0x146e9bf1da338e45]
def m14 : List ℤ := raw_ints% [0x0,0xd6e6afb51f8f100000000000000000,-0xae906f3b471254f576fefd5eafb6d00,0x41f0959652c252205d50fbd7de8ed3c0,-0xf5e2329d86c4e1028c34b192d0175540,0x278da07e5a249367e54b605723584dd30,-0x4a78ff256c9d9beaa7b5ff5ffadc80810,0x6a119b46b9ade7a5f9142f0bdede398c0,-0x748a95abb6da7f07519aa5a90691ccbc0,0x63d5bbe00c8f3b4226860fe70c025783c,-0x42f093904d2c6ea338828a9b7110b6e14,0x23113f8d2514ee9bacb790c7c54b14a90,-0xe3fceaf30c0433d65bbcb72d63178290,0x46ec670b8386c4049e2cc33bf984c86c,-0x108ebdd9648e2dee7fb7722ae2484e04,0x2d1a4c092d0a95861e76b3fa644a3c0,-0x5609ce1dc22a62eecba3fed728e180,0x6c829310881a122c3d7c1b41ca114,-0x533a6f11d51860b34ad3c899081c,0x223c3eba1881a7bedaab424ba30,-0x62d292912feead23111c305f0,0x57844c9492f5346a2bbcc14,-0xaafd1db4deeae308dbbc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 12 50 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 50 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 28 indices rho q14 m14 14 35997006165120000 16=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 28 indices rho q14 m14 14 35997006165120000 16 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_14
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<15) : intPolyRF (mz e)=rfPoly (C (35997006165120000:ℚ))*rfX^16*(1-rfX)^11*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U4C16
