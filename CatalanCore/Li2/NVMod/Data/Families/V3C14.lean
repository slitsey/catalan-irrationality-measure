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
namespace CatalanCore.Li2.NVMod.FamilySource.V3C14
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,3,14,size⟩
def bases : List ℕ := [0,1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10,11,12,13]
def num : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0xb9946600,0x137cc76c0,0xe827f3e0,0x654379d4,0x1cca0f78,0x59bbce3,0xc3c7c8,0x12b4ff,0x13a88,0xd89,0x58,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x5,-0xa,0xf5,-0xc4,0x93,-0x78,0x1545,-0x25d,0x4fe1]
def rhoDenominators : List ℤ := raw_ints% [0x189c0,0x276,0x70,0x15,0x60,0x19,0xa,0x7,0x1c0,0x7e,0x6270]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 14
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤13))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤13 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 14 omega3=padCoefficients 14 (omegaCoefficients 13 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 13 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 14 omega4=padCoefficients 14 (omegaCoefficients 13 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 13 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 14 omega5=padCoefficients 14 (omegaCoefficients 13 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 13 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 14 omega6=padCoefficients 14 (omegaCoefficients 13 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 13 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 14 omega7=padCoefficients 14 (omegaCoefficients 13 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 13 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 14 omega8=padCoefficients 14 (omegaCoefficients 13 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 13 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 14 omega9=padCoefficients 14 (omegaCoefficients 13 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 13 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 14 omega10=padCoefficients 14 (omegaCoefficients 13 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 13 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 14 omega11=padCoefficients 14 (omegaCoefficients 13 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 13 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 14 omega12=padCoefficients 14 (omegaCoefficients 13 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 13 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 14 omega13=padCoefficients 14 (omegaCoefficients 13 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 13 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x8,0x1c,-0x38,0x46,-0x38,0x1c,-0x8,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 10 li0=padCoefficients 10 (liCoefficients 9 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 9 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x7,0x15,-0x23,0x23,-0x15,0x7,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 10 li1=padCoefficients 10 (liCoefficients 9 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 9 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x5,0x9,-0x5,-0x5,0x9,-0x5,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 10 li2=padCoefficients 10 (liCoefficients 9 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 9 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x1,-0x9,0x19,-0x19,0x9,0x1,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 10 li3=padCoefficients 10 (liCoefficients 9 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 9 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x7,-0x1b,0x13,0x13,-0x1b,0x7,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 10 li4=padCoefficients 10 (liCoefficients 9 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 9 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x17,-0x9,-0x5f,0x5f,0x9,-0x17,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 10 li5=padCoefficients 10 (liCoefficients 9 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 9 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x37,0xbd,-0xf5,-0xf5,0xbd,0x37,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 10 li6=padCoefficients 10 (liCoefficients 9 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 9 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x77,0x42f,0x4c9,-0x4c9,-0x42f,-0x77,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 10 li7=padCoefficients 10 (liCoefficients 9 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 9 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf7,0x10c5,0x3d03,0x3d03,0x10c5,0xf7,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 10 li8=padCoefficients 10 (liCoefficients 9 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 9 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x9,0x24,-0x54,0x7e,-0x7e,0x54,-0x24,0x9,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 9 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^9 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
  | 3=>omega3
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
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 13 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 3 14 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
  · exact omega_spec_3
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
theorem cache_li (j : ℕ) (hj : j<9) : coefficientsPoly (cache.li j)=liNumerator 9 j := by
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
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x78f0e07900,-0x6eddc208ac0,0x2f885bd21a00,-0xca6cd96779e0,0x257022555ed60,-0x51a1b4c82030c,0x87b12ccc43dec,-0xaf74717d5aadc,0xb27387b95c6dc,-0x8f5ff175ff413,0x5ad7959a794cb,-0x2d0a989913c44,0x1138aa64cd454,-0x4f5399e44ce6,0x1090d8e61506,-0x25d31d0f2a8,0x3549b07018,-0x25e6a3093,0x802df9b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 11 20 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 20 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 23 indices rho q0 m0 0 640120320000 13=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 23 indices rho q0 m0 0 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x6243b662500,0x57488d32a3c0,-0x2435011637580,0x94f1a32866380,-0x1a8f6b8ac5e080,0x37b94d676c4104,-0x58ea8172ee4f24,0x6e118c742f776c,-0x6ad6d5983b2c8c,0x519ec948e1e731,-0x30f5089a9509b9,0x16db5d5726d35c,-0x82c994a8c304c,0x22eac97c5f842,-0x6af47c2f75e2,0xdc45a45f2b0,-0x111093bc6a0,0xa3a63c3d1,-0x1a87bbc9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 11 21 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 21 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 23 indices rho q1 m1 1 640120320000 13=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 23 indices rho q1 m1 1 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x4fd7042fe100,-0x44d23a61d70c0,0x1ba9e09afbf000,-0x6e16f045fae1e0,0x12f4e0e2351f9e0,-0x2652c234104bf2c,0x3ac8a6a0a7e408c,-0x45c24dda889263c,0x40b4464c335fddc,-0x2f0e61f8408e0db,0x1abf32e71b3d9b3,-0xbc48331f251a24,0x3f02b3744e0a74,-0xf99a836bc1e76,0x2bc6f5276b6d6,-0x512dc23f8728,0x58398ebc638,-0x2c473c025b,0x57757083]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 11 22 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 22 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 23 indices rho q2 m2 2 640120320000 13=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 23 indices rho q2 m2 2 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x40deb366e6d00,0x3658452e0439c0,-0x1532dd001513580,0x51bb26e465e3080,-0xd9be4f3c066d380,0x1a8c37e3920d08e4,-0x2732a437f312cc04,0x2ca653b0b14ea34c,-0x279f1bd805bf7cec,0x1b75a917cc055869,-0xecdd0b02860c731,0x6244ec1d3a95dfc,-0x1ec90cc4ecf906c,0x71134b72428fb2,-0x12273f62f8df52,0x1e407fba22b70,-0x1cb8cb302f60,0xbff01e5909,-0x11f1dbbc1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 11 23 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 23 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 23 indices rho q3 m3 3 640120320000 13=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 23 indices rho q3 m3 3 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x34b4f1c39b8900,-0x2af9d084478eec0,0x104aa4cfcff21400,-0x3cf05dc4d9fd7fe0,0x9d35751c8c50a7e0,-0x12851b508365f23cc,0x1a5b015ae66d4ce2c,-0x1cd9f70493de7109c,0x188570d8b04dd873c,-0x103606625314692c3,0x84bc8d72ce8198db,-0x33f55dfa7e9e4084,0xf3d924ccc4fa654,-0x33e419712931246,0x79e34d16f2f3a6,-0xb6298dd8c1928,0x968691b3abb8,-0x34047416143,0x3aaf98a2b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 11 24 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 24 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 23 indices rho q4 m4 4 640120320000 13=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 23 indices rho q4 m4 4 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x1]
def r5 : List ℤ := raw_ints% [-0xb9946600,-0x137cc76c0,-0xe827f3e0,-0x654379d4,-0x1cca0f78,-0x59bbce3,-0xc3c7c8,-0x12b4fb,-0x13a7c,-0xd7c,-0x52]
def m5 : List ℤ := raw_ints% [0x0,-0x2ad3046eee5f500,0x22088ba6a53c1fc0,-0xc8e3c195e7167d80,0x2da06266841d06580,-0x722178ea59f6ab880,0xd02020d512e7273c4,-0x11dd0e5244cdd181e4,0x12d09a6a2264337a2c,-0xf54efa26f184a78cc,0x9ad69bd0b52e16061,-0x4b454ae118c1bc2e9,0x1bcff8de7480a719c,-0x7a39e0b7640ee48c,0x1819cb7bcd9f74a2,-0x33b57f3c1155742,0x4526b2fab46230,-0x318bc2cd048a0,0xe1750a73d01,-0xbf405ebf9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 11 26 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 26 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 23 indices rho q5 m5 5 640120320000 13=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 23 indices rho q5 m5 5 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x52,0x1]
def r6 : List ℤ := raw_ints% [0x3b7188ac00,0x6325e9a380,0x4924ffa700,0x1f87751208,0x8d3757a9c,0x1af18713e,0x391a412d,0x53a31e6,0x520a95,0x31b66,0xeb4]
def m6 : List ℤ := raw_ints% [0x0,0x22cb739a21ad7100,-0x1afd1f23c692d9cc0,0x9b3ead57e3af49800,-0x224ceda96fd15915e0,0x534d02f19013e645e0,-0x93258e93e21a4d0b6c,0xc33b9c5c0beb549ecc,-0xc60fc62e78335ed9fc,0x9ae4eeaab7a4ce7d9c,-0x5d6cbf3878fe09a36b,0x2b2b54f24aa1ab2ec3,-0xf0ffa7f9a6cc2afe4,0x3dfbfac89e9b4f334,-0xb51b4993d4078b96,0x16278d862d1f59f6,-0x1a72ff0f61f6528,0x105eb4b1457d38,-0x3d0381510eeb,0x26d4068693]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 11 28 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 28 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 23 indices rho q6 m6 6 640120320000 13=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 23 indices rho q6 m6 6 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0xeb4,-0x52,0x1]
def r7 : List ℤ := raw_ints% [-0xaa899ebb800,-0x11acf8b95300,-0xcf245841600,-0x587bf1b9a10,-0x187c3765e58,-0x49a25fbf00,-0x98f7cf762,-0xd9f2f41f,-0xcd665ba,-0x74f7bf,-0x1f27a]
def m7 : List ℤ := raw_ints% [0x0,-0x1c454ded3b5cebd00,0x156e4b8e5994d0f5c0,-0x7849ebdb5e1e362580,0x19e332291cab2995a80,-0x3d1d4924a4a40cbbd80,0x68b2fd9b794850097a4,-0x865ccc1e3dff6db78c4,0x836de15401a1952a40c,-0x62bc4b6aedc29e2f7ac,0x38f35317b9973580899,-0x190718842d9a38298e1,0x83f9a6b95510db5c3c,-0x1fc816b6b059f77bac,0x55f18fb402eef1a12,-0x993ca5eaf2ff27b2,0xa2eaf917b404cf0,-0x56c83a72b459e0,0x107d24488b939,-0x7dbfec6a71]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 11 30 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 30 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 23 indices rho q7 m7 7 640120320000 13=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 23 indices rho q7 m7 7 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x1f27a,0xeb4,-0x52,0x1]
def r8 : List ℤ := raw_ints% [0x1695b1f249c00,0x25477bc865f80,0x1b25f62baa5c0,0xb83b3fa26108,0x32870b473520,0x963de333bd6,0x13395908650,0x1add855824,0x18a7f80b1,0xd848f90,0x366231]
def m8 : List ℤ := raw_ints% [0x0,0x16f84f50c03b7f9900,-0x110a17149ef709c7ac0,0x5d7137b0a8800929c00,-0x139cc29648d5485d43e0,0x2d0fe9f2a849cb52fbe0,-0x4af5031abae14c12860c,0x5d24c20e03287be1fa6c,-0x57efa693fb2f342fba5c,0x3f83df465d4dd2bf92fc,-0x230f5215acd1c5e616d3,0xea93437ca45d2195d6b,-0x4909e74f6b450ca3844,0x10771286a7dbf73ad14,-0x292d631bfec96fc266,0x42c7b7873869d35c6,-0x3f1191b21014a328,0x1ccfa18f82e24b8,-0x472e25c2ddf53,0x1961f3f6fbb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 11 32 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 32 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 23 indices rho q8 m8 8 640120320000 13=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 23 indices rho q8 m8 8 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x366231,-0x1f27a,0xeb4,-0x52,0x1]
def r9 : List ℤ := raw_ints% [-0x276c7bd8738600,-0x40d35de0f39ec0,-0x2efd016fbb0e60,-0x13d0b3868ad3d4,-0x5656ee04684f0,-0xfe797db8d853,-0x20335df09172,-0x2c5c517bc7f,-0x27f3ceebe4,-0x155978888,-0x52d3148]
def m9 : List ℤ := raw_ints% [0x0,-0x12a9c0719c3057ac500,0xd908e0579cb4ff23bc0,-0x48c44b5639ce66ffad80,0xee9b5d48829f6ad4cf80,-0x216327edf8c9a4c550280,0x35fc08edc4dc0c3930c84,-0x4106119f1dc196fbce8a4,0x3b4e805c6df7b3f6558ec,-0x29383897695da8aa4a98c,0x15c9f3c79ae43fa996711,-0x8ac78e83186f0c54f719,0x28d44707bbdb429ce5dc,-0x89d130c040652b48dcc,0x13e792362516fe96c02,-0x1d50594d713cd5eca2,0x1887875be23e1fbb0,-0x993d64381c8ab20,0x132b907a13e3b1,-0x51c37fbe529]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 11 34 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 34 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 23 indices rho q9 m9 9 640120320000 13=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 23 indices rho q9 m9 9 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x52d3148,0x366231,-0x1f27a,0xeb4,-0x52,0x1]
def r10 : List ℤ := raw_ints% [0x3c0a8cd8742b000,0x6269ccc9b88a000,0x470f01c4e56d840,0x1dd34ba83d4c940,0x8136a94f577dec,0x17a2b625950de8,0x2f6fd38bc9fed,0x40a307ca2546,0x396695cc1c1,0x1e1ce11ba4,0x71f16838]
def m10 : List ℤ := raw_ints% [0x0,0xf29ec5c4ee7473c0100,-0xacfb7d7fd6f22f4d08c0,0x38cd04cf3d8f008132000,-0xb613895a2aba9cc5a89e0,0x18da60ff3236cd0babc9e0,-0x271ab56e661aa91144fbac,0x2db39c040075b9d907890c,-0x284e9cebb2bf5c63ce49bc,0x1afa7f05f221738bf73f5c,-0xdaa497903c9e4d2e8d6fb,0x52e33254d7ffe5b137ed3,-0x170aeb7ec7cf9fa93f1a4,0x48c2bd1426df5e34cbf4,-0x9b35c812f360fe28ab6,0xcf36fb5d6ffd591b16,-0x993ccf7a41f78d328,0x32fa33005eee6238,-0x527331520ffc7b,0x106bea197fa3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 11 36 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 36 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 23 indices rho q10 m10 10 640120320000 13=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 23 indices rho q10 m10 10 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x71f16838,-0x52d3148,0x366231,-0x1f27a,0xeb4,-0x52,0x1]
def r11 : List ℤ := raw_ints% [-0x52998146e7e65000,-0x87069e0848754a00,-0x612df1f8de27b900,-0x28a15669867dee20,-0xaf3220a669f5900,-0x1fdd19c34290bbc,-0x3f8117e9afe5d8,-0x55c8b57f18fdb,-0x4b5b9a49e87a,-0x26fd31edc37,-0x90e1ab79c]
def m11 : List ℤ := raw_ints% [0x0,-0xc52100b001be9e0c0d00,0x8a078b625c5c1e6e971c0,-0x2c707e90e1c6e590f91580,0x8b69c668810f554c9d0480,-0x129570a606c4067f97ec780,0x1c7bc60d8797eac162dca64,-0x2054fac5bac4ee212198984,0x1b993ef94d0e4a56c43d0cc,-0x11cd86b548d1b9a88ec866c,0x8a550e43c53f1743c669c9,-0x31f51d831de9a7bec5bb91,0xd1f7f5a18d5ecf427b67c,-0x26bee931adaa152bde2ec,0x4c36c1be232f0650c672,-0x5c12a479587d515c212,0x3c052f5d857ef6de70,-0x10f66ba27dcb2cc60,0x161ee06b2ad6a69,-0x34a69f051a21]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 11 38 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 38 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 23 indices rho q11 m11 11 640120320000 13=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 23 indices rho q11 m11 11 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x90e1ab79c,0x71f16838,-0x52d3148,0x366231,-0x1f27a,0xeb4,-0x52,0x1]
def r12 : List ℤ := raw_ints% [0x6907111c087582800,0xab4c4645cd1154d00,0x7af2b5ebec3f87280,0x333c598a00a951030,0xdc0f42d297e24700,0x27d59c1bf15c0654,0x4eefdc77144aa24,0x69e3b8d4feae8c,0x5c390eb755305,0x2f344d554602,0xad06104169]
def m12 : List ℤ := raw_ints% [0x0,0xa02ad08f016ae069ca900,-0x6e42894fc9545ab9dac6c0,0x22d82e3cf3137b534ab2400,-0x6b18d1ed0a0fb9b622567e0,0xdf4d21c77c99998a78f2fe0,-0x14dbda2076a09d714b2e144c,0x1704b8ca3d84765ddfc732ac,-0x13087ed77bc8f7d2ee95601c,0xbd75665b89daeeb21359abc,-0x584346259cf8e3e40625de3,0x1e5fa419d15bc5be478dcfb,-0x789d880aadf48f5ed6f404,0x14ccae06b9498309f8c7d4,-0x25aed0fcad17804a0d886,0x291e1664be346a743de6,-0x17917f88af4591e3528,0x5a4bfaa5920f5d5b8,-0x5ec5fb0d9022063,0xa873ce0ea04b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 11 40 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 40 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 23 indices rho q12 m12 12 640120320000 13=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 23 indices rho q12 m12 12 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0xad06104169,-0x90e1ab79c,0x71f16838,-0x52d3148,0x366231,-0x1f27a,0xeb4,-0x52,0x1]
def r13 : List ℤ := raw_ints% [-0x7d6dae31152bc3d600,-0xcc2c1dc53a31ab4cc0,-0x9233bb178b0a3999e0,-0x3cc1d3f8777be35974,-0x1041756bd0d9b8c008,-0x2ee51642c6023d51b,-0x5c7d0929412ab2b4,-0x7b5c3f9a04c5173,-0x6ab1a253dedb3c,-0x362562690032c,-0xc45c8413616]
def m13 : List ℤ := raw_ints% [0x0,-0x8222c9743126d655f49500,0x582b5d9cba4bab3701c17c0,-0x1b60e737095821f274e85d80,0x5287e729f8cfd24f2bcc3980,-0xa866690332c03490d8cf4c80,0xf5ab252403bdd98930070944,-0x107cefe9116d03eb04a785364,0xd37ab9784f08e6bd86a403ac,-0x7efad81a162e0890661dc64c,0x38c69f873c8afe128ddd0ec1,-0x129f29f4027122029a01d449,0x45db7b76897f7578c1c361c,-0xb40130022559261ad4030c,0x12bfe26f4ad29c5dee2562,-0x1271639689adfb4486402,0x945dde06e3835966530,-0x1e0794f525bf7ecda0,0x19546621a6788b61,-0x219e129aa5759]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 11 42 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 42 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 23 indices rho q13 m13 13 640120320000 13=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 23 indices rho q13 m13 13 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0xc45c8413616,0xad06104169,-0x90e1ab79c,0x71f16838,-0x52d3148,0x366231,-0x1f27a,0xeb4,-0x52,0x1]
def r14 : List ℤ := raw_ints% [0x8e58af2b3932644c400,0xe7525e5fa3ae79ade80,0xa54fbafcfde1b14e880,0x4489061314d74199658,0x1248fe104594a354adc,0x3492c23aa9c9245d7a,0x67469faaef69b8615,0x891855bcdf5da536,0x75e58b8beaf663d,0x3b6ae126c6348a,0xd5a6afda9464]
def m14 : List ℤ := raw_ints% [0x0,0x69bc43ae67ef8e25d6b9100,-0x469336984466d43cb16d34c0,0x158e33696a5f136d48a2fa800,-0x3fcab7ebdc1de7d30f0405de0,0x7f81ef3cb930a5becb849ade0,-0xb5bd9dc36e06a31517e7e37ec,0xbe14ba1edfa8804207bb99f4c,-0x93d90f0b71bd81c7ec70f957c,0x55bc2269e8a79cfda44da7d1c,-0x24cf1aa5887d072909212558b,0xb8235433df1861f86a2a71e3,-0x28c6acfc1c156e4dc13b9764,0x620d9d241c07d81d10b58b4,-0x961f8ddce9eb32ea9c7fd6,0x84dcd8c17b7c88259b236,-0x3a760e32ec7d0f328928,0x9faf6d6f70b3899f38,-0x6c1d8120974db50b,0x6b24680fbebb3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 11 44 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 44 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 23 indices rho q14 m14 14 640120320000 13=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 23 indices rho q14 m14 14 640120320000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_14
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<15) : intPolyRF (mz e)=rfPoly (C (640120320000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V3C14
