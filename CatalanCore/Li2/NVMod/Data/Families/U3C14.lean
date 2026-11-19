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
namespace CatalanCore.Li2.NVMod.FamilySource.U3C14
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,3,14,size⟩
def bases : List ℕ := [1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14]
def num : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x36209dc00,0x4cc3dad80,0x309ea0a80,0x122a4dba8,0x47392794,0xc07141a,0x16ddc93,0x1e9b0d,0x1c476,0x1130,0x63,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0xf,0xa,-0xf5,0x6e4,-0x93,0x528,-0x3fcf,0x1eb9,-0x4fe1]
def rhoDenominators : List ℤ := raw_ints% [0x6270,0x7e,0x38,0x3,0xc,0x19,0x1,0x7,0x70,0x7e,0x708]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 15
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤14))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤14 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 15 omega4=padCoefficients 15 (omegaCoefficients 14 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 14 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 15 omega5=padCoefficients 15 (omegaCoefficients 14 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 14 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 15 omega6=padCoefficients 15 (omegaCoefficients 14 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 14 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 15 omega7=padCoefficients 15 (omegaCoefficients 14 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 14 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 15 omega8=padCoefficients 15 (omegaCoefficients 14 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 14 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 15 omega9=padCoefficients 15 (omegaCoefficients 14 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 14 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 15 omega10=padCoefficients 15 (omegaCoefficients 14 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 14 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 15 omega11=padCoefficients 15 (omegaCoefficients 14 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 14 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 15 omega12=padCoefficients 15 (omegaCoefficients 14 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 14 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 15 omega13=padCoefficients 15 (omegaCoefficients 14 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 14 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 15 omega14=padCoefficients 15 (omegaCoefficients 14 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 14 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 14 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 4 15 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x21050cdb4d2de00,0x1f75e920f2483c80,-0xe0fd523ec0d0fe00,0x3ea58d64b66bbd0e0,-0xc2b437c2040584340,0x1bff357e4d0862d3f0,-0x315ea62580c0e0ad20,0x44280d1117bb8d4458,-0x4a9534aca08bda5fb0,0x4114a13c4dd24eb92c,-0x2d4fb188674abdc0c8,0x190ed13ffaacca29a4,-0xae592c84df5c28c40,0x3a9ff4468d739afb8,-0xed9d82f08c760370,0x2b933d2847b4d870,-0x56e5a1c0f6b1a90,0x69c09e0bf8e87c,-0x3f8ff160f8b08,0xac58bd1cfc4,0xe7f97f80,-0x56fd8fd0,0x1354caa0,-0x1eee110]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 11 21 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 21 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 25 indices rho q0 m0 0 13089820423680000 14=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 25 indices rho q0 m0 0 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x1ce46b3fe3882400,-0x1ad1bea81f0b30700,0xbaa4eb62680b13800,-0x3282463da824ed1fc0,0x9859f59b2f6db96b00,-0x153a32d1ef7521d5c80,0x2434d3a002d68024100,-0x303fc7211e5af3846b0,0x32d8fee2f430d5025c0,-0x2a9d750d4a8aaf09d20,0x1c682fd456c23117d40,-0xefbf2e2ba05e0e9d10,0x62fd47e02072b7ac80,-0x1f6c9bc40594703340,0x775fe2cb22cfda380,-0x14520d23ec8763cd0,0x251c2a61f287cac0,-0x288693496bbba20,0x151e7a88f93a40,-0x2e5871f5d1b0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 11 22 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 22 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 25 indices rho q1 m1 1 13089820423680000 14=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 25 indices rho q1 m1 1 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x1947ddd7e7171f800,0x16e41dfe482386ba00,-0x9b3731e71c44264200,0x28df46ce0e2e873aa80,-0x77ca13b4d969edc7a80,0x1030ea812eb2c802cc80,-0x1abdb760d99badde1580,0x226f34c2ef29d018dc20,-0x22fb5578ec2c7d43a620,0x1c2eecc7b5c5a46373a0,-0x12002315cbf485594ee0,0x90fd7fc33aef7a44900,-0x38dc9c84caaae067fc0,0x110b08087710f1d7dc0,-0x3ca975104cc02f3340,0x993a9c7b4621e4220,-0xffd50e7414829da0,0xf9f8073b184de20,-0x706d863f5e7060,0xc6ca64281840]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 11 23 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 23 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 25 indices rho q2 m2 2 13089820423680000 14=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 25 indices rho q2 m2 2 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x161ee21cea343b9000,-0x138fd51193a9feea400,0x8163a2bd490fa824e00,-0x2131361c33f21d252f00,0x5ea18379c7419c1b2580,-0xc6bed326db93ff46ca00,0x13e2de8e8291398751580,-0x18c4d5a6e81946c0a0fc0,0x1847502c0332c74b596e0,-0x12d191bfd06bc943c8180,0xb863b87bd9b0577b99e0,-0x58a3b5c3cdf9bd011a80,0x21075ed095448adf3340,-0x958e4d6a92f6e43b200,0x1f292a44eebf47d5440,-0x48edfb730482de9dc0,0x6f1fdd5127b0a3c60,-0x60dcb3ff1cc91c80,0x256f9fe230d3260,-0x352afc5658b00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 11 24 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 24 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 25 indices rho q3 m3 3 13089820423680000 14=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 25 indices rho q3 m3 3 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0x1]
def r4 : List ℤ := raw_ints% [-0x36209dc00,-0x4cc3dad80,-0x309ea0a80,-0x122a4dba8,-0x47392794,-0xc0713f6,-0x16ddc0f,-0x1e9a4c,-0x1c3e6,-0x10f6,-0x57]
def m4 : List ℤ := raw_ints% [0x0,-0x135b05d94cedb41e000,0x10bc8a3ae1e59c631000,-0x6c1cb38c8cb15e212e00,0x1b0c8b17924e7ac050600,-0x4b194ab638c7d69fbad80,0x995634e83f3851985f500,-0xee322e5a2368c10a51f80,0x11f3d78d913b7613efec80,-0x10fe69eb5e5d852ef8dee0,0xcaec039dbaee4c3605940,-0x773a207b83a062e22b460,0x36c198a9e955bce769000,-0x13640daa5a09f45a19140,0x52e65badf6272af36a80,-0x102ba02c712a77777540,0x2307b9c53b7a70f7380,-0x309f7502d564f14a60,0x25b2999ca79b39d40,-0xc77fd6516f400e0,0xe3066f6b26400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 11 26 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 26 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 25 indices rho q4 m4 4 13089820423680000 14=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 25 indices rho q4 m4 4 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x57,0x1]
def r5 : List ℤ := raw_ints% [0x1265159c400,0x19e06ec1a80,0x103924be400,0x5fbc1c9b98,0x1711c797a4,0x3cf2ead42,0x704ee1ff,0x8f8d55c,0x7b29ce,0x4136a,0x10af]
def m5 : List ℤ := raw_ints% [0x0,0x10efa51e234ffd9a4000,-0xe55e7c8de389caca1800,0x5a89f4182f19b97e2e600,-0x161dfa311d75f6f72c9800,0x3bdcfa39410e5386682380,-0x76f39c7d26a7546603b300,0xb3790d2b10ba466950a980,-0xd1bb7ae2c11b7a79e4d700,0xbfe30b13cb65f7d0418e60,-0x89fcb44136b77f79b7cec0,0x4dd55c9fb1c77b91e5ace0,-0x222a419cba92a7ff412700,0xb803ccef1e7f57232d240,-0x2e6b31e1090a577c7f380,0x878e36900d5e44f72040,-0x10f828fd217853d34c00,0x156a5ff5e521ffecbe0,-0xeb992c834f3f3a0c0,0x426ff8a2b339d360,-0x3c76779758b000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 11 28 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 28 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 25 indices rho q5 m5 5 13089820423680000 14=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 25 indices rho q5 m5 5 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x10af,-0x57,0x1]
def r6 : List ℤ := raw_ints% [-0x3870a27d6400,-0x4ee527a7d680,-0x311460b91300,-0x11ed6a20c3d8,-0x444866eb294,-0xb19850c622,-0x1408b44b3b,-0x18e4debe4,-0x1483d74e,-0xa39602,-0x26043]
def m6 : List ℤ := raw_ints% [0x0,-0xed1b07a5ee5fde6f8000,0xc4aecdd1a664b34e32800,-0x4bfd285d122cf93da58e00,0x1224c17b687a5cf2d814400,-0x2fec9b332665f124e27a580,0x5cc48c1bc1337355af5d300,-0x88133c8229363f3829ecb80,0x9a3c8f3f664ecc220d54a00,-0x887ffe7917f2cc2474160e0,0x5ea59cf27d5fa46c1fba2c0,-0x334823025f54889fd368f60,0x1585eedddf45e13c7166500,-0x6e36818cf3cd93d8be8940,0x1a3e194f50afbb0f1fa780,-0x47aa63836787c3fb1bb40,0x848f958dac208ca13700,-0x97ce6543329dbcc7060,0x5c4cb76a5d26b810c0,-0x161d6a7fe34429be0,0x101263e30184000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 11 30 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 30 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 25 indices rho q6 m6 6 13089820423680000 14=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 25 indices rho q6 m6 6 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x26043,0x10af,-0x57,0x1]
def r7 : List ℤ := raw_ints% [0x809ba13149400,0xb2de34db70480,0x6e9724988e900,0x2817f3a1b69f8,0x974cf7d417e4,0x184f6f29503a,0x2b3b34d1457,0x34af8d292c,0x2a4c0befe,0x1452a842,0x47a3e7]
def m7 : List ℤ := raw_ints% [0x0,0xcf77a6b13093e2a190000,-0xa8d5cec4e905f868482800,0x3fe9b3a7803959938ce7600,-0xeee595716acfe18a6011c00,0x2686ce928f7a67ec5a6ff780,-0x48b85e62358761a1b109ff00,0x67cc5e0d294ae84980582580,-0x7236696834a53888874f1400,0x61d9ac56db38c7c4582e8f60,-0x4177013d83c75fa514888dc0,0x2216ffe42dcb02b98d7707e0,-0xdaf60ee0a08f46fb9a16d00,0x42a178f5c5f177884ffc040,-0xef8e44af86bb4b642a2d80,0x2635eddffc3720db328240,-0x4130b49849aace9b74500,0x439b83cc09ace38cd8e0,-0x243ef557055427efbc0,0x75b305507cb337a60,-0x443ae3b8d1b0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 11 32 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 32 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 25 indices rho q7 m7 7 13089820423680000 14=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 25 indices rho q7 m7 7 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r8 : List ℤ := raw_ints% [-0xf25b35c1f98400,-0x14fadc09c8b7a80,-0xce841392a7f500,-0x4a6c5bdcad4398,-0x116cf468b68894,-0x2c65cf7919992,-0x4e12fb2f516b,-0x5dce5a51b64,-0x49eedc3f4e,-0x22a905352,-0x761ba13]
def m8 : List ℤ := raw_ints% [0x0,-0xb588b1db0a81664d5e0000,0x911486993cee7bb661dc800,-0x35ddd2c737bc1d1b95f37e00,0xc532fac2e59ceea911ae9c00,-0x1f18cf45b28e0bd3c3b89b180,0x394a0db322beee691e6376300,-0x4fa4c083aea725ddb01dcd780,0x5524b146a2c22a7a52cf9e000,-0x46ab358a9f60c33c7fa520fe0,0x2da5f6ccafa56df2c23db7ec0,-0x16db5fa41c247b4fb74884660,0x8c7772f578ca6bc8d9587100,-0x28a51dec3236b1211ba39340,0x89dd90a0a95af0b7d323780,-0x1489288880330e0c86eed40,0x2045b759d8c609350f8d00,-0x1e3f693b4654ce3710b60,0xe428f11d8d4da7564c0,-0x271dd5b0d62cb6d6e0,0x12129d076ee40000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 11 34 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 34 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 25 indices rho q8 m8 8 13089820423680000 14=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 25 indices rho q8 m8 8 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r9 : List ℤ := raw_ints% [0x18f8e03bcc935400,0x227834a774295c80,0x151eafa4a5f44d00,0x792f1a699d46878,0x1c35425fe663464,0x475c04f444d95a,0x7c6558e8b9357,0x93d95eaaa28c,0x72f0df0355e,0x34f0d1e742,0xb03aa207]
def m9 : List ℤ := raw_ints% [0x0,0x9ed79b9fa9313983b240000,-0x7ccaa22299283229a1d7a800,0x2d7d40b2249a26caf7c666600,-0xa342b13ebb0a1eecefc858c00,0x1932b3df69e029cbfb3f9c8380,-0x2d59b9f334191ff9bd3c00a700,0x3d7545f496cf5267c511cac180,-0x3fe2d6c230f5de31617b308800,0x33685463ee6dcb0c2f2775ce60,-0x20149c5008ef3acc965d8997c0,0xf73fa3a0ccb936eb83af0c2e0,-0x5ae2f6a4ead3c7fb4ffb10d00,0x1901d4af9567950c2a302da40,-0x4fffab39067aa690ccf3e180,0xb1e7f2bd46a5e09bcc91c40,-0x1012d345186c3c069639100,0xd964ea1c37dd137e033e0,-0x59e32aa85d5132e545c0,0xcfcaaa4532dcb15960,-0x4c7840bac3b00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 11 36 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 36 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 25 indices rho q9 m9 9 13089820423680000 14=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 25 indices rho q9 m9 9 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r10 : List ℤ := raw_ints% [-0x2542d219dc37d0400,-0x3348ad6661fe76a80,-0x1f50addf24ce1ed00,-0xb2f538ace39e0498,-0x2974a9963b4f5494,-0x6844ae33e67cc52,-0xb47f6ba49f34ab,-0xd4b45e15ae404,-0xa39f627068ae,-0x4a5e1d0a2f2,-0xf35dac173]
def m10 : List ℤ := raw_ints% [0x0,-0x8afca82bb40b12533bf80000,0x6b7159e9712248b2978928800,-0x267cf75f44ec81496231b12e00,0x878c47d75b0ed92cc8e829dc00,-0x147ec48bd4c3711d573f795ed80,0x2411323a43f39b9442f2cccbb00,-0x2fafc57390f2f7fe4048ef44380,0x303d0109bff48f7f8ba886a7800,-0x25a8879356a89cf50aeaa94cae0,0x16b785fcc7fc2c56d9a827ea4c0,-0xa881125e323ee1395f9b3f8560,0x3b4b344a2708cc742befb88900,-0xf834211cd02cd956585683540,0x2ec8edce2ec065fdbf5d59380,-0x610001697d2369e2fee8df40,0x80cc5acb8a5e9f7a5c02d00,-0x61fda24386625bb2d9f260,0x23727d5a3987a9bea3ac0,-0x44e995bde4ff6b809e0,0x14311263fa8400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 11 38 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 38 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 25 indices rho q10 m10 10 13089820423680000 14=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 25 indices rho q10 m10 10 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r11 : List ℤ := raw_ints% [0x3374c3f95fd149d400,0x46a5d25a75bb056c80,0x2b03d1f86a3725cd00,0xf4fc27e6361d66778,0x3885fcaae89ed56e4,0x8d7d4237022a4d1a,0xf3899067d6b1cb7,0x11d069836173f2c,0xd96d32f0952fe,0x61ce3d6c7fe2,0x13bf1c82c87]
def m11 : List ℤ := raw_ints% [0x0,0x799d13263d89b008d47900000,-0x5c97387556074703c6a822e800,0x209fcffb54df97fae70f4e35600,-0x70d9275b171f9974273e055ac00,0x10bb0f21f2f4bb60eaff60754f80,-0x1cd03ee45072aac6d857e0497f00,0x2532ce9f8bb3ac8a61496f98bd80,-0x24a542dfb7a4f2eec343060b1800,0x1bc6159a752f6c7b94ae6c8f3d60,-0x10346a677cb317ac2e6a79f57dc0,0x73bb43834d06245788c7c2b55e0,-0x26fdcc6d5c1bb14a97549c19500,0x9b2f17688a6d42278e341d3440,-0x1b90740701e2b995ab48885d80,0x353b50eba525676fa84e4a640,-0x40d3e6ee5303fdcedba9a900,0x2c4cda4a4ec26720b7b9ee0,-0xdfccd5c183e8603f57bc0,0x16d3e8c7a80b8bf25060,-0x552e8e9d2eb000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 11 40 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 40 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 25 indices rho q11 m11 11 13089820423680000 14=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 25 indices rho q11 m11 11 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r12 : List ℤ := raw_ints% [-0x42cd4122a7245030400,-0x5b86326f947890eaa80,-0x3796bde2b136d341d00,-0x13baf88c57026cae898,-0x4896d5b4053fbae794,-0xb4fb202db3392bad2,-0x1360ab1645686486b,-0x168d17de3486e324,-0x11161eeaacba30e,-0x79f787173fd52,-0x186042fcb853]
def m12 : List ℤ := raw_ints% [0x0,-0x6a6970c175d87a07b9e9e00000,0x4fdc995a0abde8276780381c800,-0x1bb3d3014d29bc97c03c60035e00,0x5e32a899c9f90b7f2cf738c5bc00,-0xdb49f38c4532a153cd45385ec980,0x171e67e50b61fac7f6e84558af300,-0x1d2ab4499f98df0b9989f08d48f80,0x1c00dc99366a7ee25dbcfd43e9800,-0x149e543218bd97c72d51495900de0,0xba44e3e16346f2629919fe14e2c0,-0x5015730b0ee7b8cdb44f05eadc60,0x19d66e7bafe9bc1e976f33481100,-0x61c22705173ee7ce2f07c4e8740,0x105abbc1d10d4acbd9d2848ff80,-0x1d63aa63291e860191d1c3a140,0x20c6edf5120aa088ba54db500,-0x1413d8ffb406637d65a48160,0x58578102371a21434408c0,-0x78d87b10f7fd320074e0,0x166dc3f8a464000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 11 42 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 42 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 25 indices rho q12 m12 12 13089820423680000 14=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 25 indices rho q12 m12 12 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x186042fcb853,0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r13 : List ℤ := raw_ints% [0x527692effbfc6f525400,0x70c6ccb74d5a11b03c80,0x445a11273fec3b5ebd00,0x18335299601ad57fda78,0x58c743efdcf22df4c64,0xdc98d9f88a3a9b4cda,0x17868e384f404970d7,0x1b400adabada354cc,0x14881ac6e1689f1e,0x919490acd46f82,0x1cdc176474ac7]
def m13 : List ℤ := raw_ints% [0x0,0x5d1c42a9471d6ac6c2aca400000,-0x44f0c0a486f74b45cf6cd5df2800,0x17901322b293e43b98ba686bbc600,-0x4ed441e7a7bf94da22cd38c678c00,0xb43eae3c3d0a90a9bbdcf260d7b80,-0x12a0a25840f1a06729aaeda173d700,0x16fbbee1dda899a35967aa5afc1980,-0x1585904069d9c328d44dcd389d1800,0xf67752c2295a5d5321f9453b8e460,-0x86be52131262b5420e043688683c0,0x37d1ae91f2c09bb960f5f425de0e0,-0x113f7d25485566c377ee8aca4fd00,0x3e073971ba4d1f344bd32dc59e40,-0x9c49dbd7780a53a8e72d0715980,0x1051251e32e696f8cc73fe18040,-0x10a3a90345eb0505e4e1c63100,0x91e4dfdb2d97fb39908861e0,-0x22dfff3ead11488e1f711c0,0x27ef5b2bd3d082f661f60,-0x5e5dcd6012b0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 11 44 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 44 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 25 indices rho q13 m13 13 13089820423680000 14=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 25 indices rho q13 m13 13 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x1cdc176474ac7,-0x186042fcb853,0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r14 : List ℤ := raw_ints% [-0x61a1a3abc951c13420400,-0x854f4b079cb5c47468a80,-0x50a5f890da12033c6ed00,-0x1c7e472f8cf99b5de9298,-0x68446cab285f3f6ab194,-0x102561d89888d1a6d7d2,-0x1b751d712d79252a76b,-0x1fadc9397baeedd844,-0x17c1dbe56b7407eee,-0xa78525a07ec9d32,-0x20fd4010bd7b73]
def m14 : List ℤ := raw_ints% [0x0,-0x5178ba541e39bd6dea570f800000,0x3b8f700fa01e4bf9ca72810450800,-0x1412f5f9838536169a82b1f3690e00,0x4220d38b5ba148b8d2807f5b5f1c00,-0x94a2341eba109044c2fee14c0d0580,0xf11c8f74854c50079d69c468526b00,-0x1232b9463e69ee31133e8e03bbabb80,0x10a1c66f5b89df681b1ee8cf584d800,-0xb945c89858a2c122d94192b88c88e0,0x621f6bb20dd680f001cc2aeaba70c0,-0x272e0b016d6f9b3652a2bef8654b60,0xb98986d5e13683122ca9655c99900,-0x27a11aeb06bbe6d8b5a620a256940,0x5def0e6f2bc34624c07c79648b80,-0x91b30d79bff1240eb2e6eadf340,0x87a39444a7c5a6780799de1d00,-0x425f36d7c6a50419b6aade860,0xdc4298f1d9b0accfd1ca6c0,-0xd2e5b6a7904ab982ad7e0,0x18c8b1c56c840000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 11 46 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 46 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 25 indices rho q14 m14 14 13089820423680000 14=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 25 indices rho q14 m14 14 13089820423680000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_14
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<15) : intPolyRF (mz e)=rfPoly (C (13089820423680000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.U3C14
