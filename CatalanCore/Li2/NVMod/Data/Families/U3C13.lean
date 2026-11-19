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
namespace CatalanCore.Li2.NVMod.FamilySource.U3C13
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.U,3,13,size⟩
def bases : List ℕ := [1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13]
def num : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x3ddc2200,0x53501c40,0x319d47e0,0x113765fc,0x3db8dd4,0x956505,0xf7641,0x114ea,0xc8a,0x55,0x1]
def rhoNumerators : List ℤ := raw_ints% [-0x1,0x1,-0xf,0x46,-0xf5,0x6e4,-0x24c,0xf78,-0x3fcf,0x1eb9]
def rhoDenominators : List ℤ := raw_ints% [0x9d8,0xe,0x7,0x3,0x2,0x5,0x1,0x7,0x38,0x7e]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.Icc 1 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 14
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤13))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤13 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
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
  change m∈Finset.Ico 4 14 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x122488787ecd400,-0xf387ecc79260a00,0x5f09a70c462f9740,-0x16e22aa68ef530900,0x3cd3d501d61013010,-0x762bf179255d2bbd0,0xad5ae31c4b8d3d000,-0xc399d54c889a2b230,0xab422b72d254d0e24,-0x747efb40bd96e0cd4,0x3d34a3ac30f11ea90,-0x187fc140d3d85aef0,0x74c01e84fa8ca858,-0x18e961205f3265b8,0x394ac44f1255cd0,-0x4fcda558fc9a80,0x368b2a8b37ec4,-0xa7302162474,-0xe355c9c0,0x616de8c0,-0x185b7a30,0x2b4d4b0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 10 20 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 20 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 23 indices rho q0 m0 0 1308982042368000 13=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 23 indices rho q0 m0 0 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0xebdaee1e706c400,0xc091ec379320b700,-0x49092539d22ec7e00,0x111072caafcd343ec0,-0x2befbf759891c16180,0x5283a1a8176e785dc0,-0x74beea8c3f8ba0bc00,0x7eb53d37e6adaf1b70,-0x6a60865fa4e4649b60,0x452026d38d3f5e25b0,-0x22891a31282b8c4880,0xd121ccdc0fd4102a0,-0x3a77d3721eaa5ebc0,0xb98e1f6974520da0,-0x18753fc2cdb6da80,0x1e9ad545093cb30,-0x1225e9bd7f5660,0x2d012f20eff0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 10 21 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 21 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 23 indices rho q1 m1 1 1308982042368000 13=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 23 indices rho q1 m1 1 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,0xbfa1e178bb57f400,-0x987d2ccd38b03c700,0x3848f6026b844da300,-0xcc7204097a641784c0,0x1fe8df9bb8ab3feebc0,-0x3a00ea9d766e35f7d00,0x4f3e55c04119b8f1c00,-0x52d1206db0ea1bd70b0,0x42bb6aaa2c002615770,-0x2974e677e9e4928ee00,0x13b4dcc68574b7028c0,-0x70dcd0c0dd9a4f6b60,0x1d9d00ebd5896cb2e0,-0x574c5bcb184c8d940,0xa88ecf642ab1a6c0,-0xbcee2bc7f50fcb0,0x60bf18c321b770,-0xc13cf87ac740]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 10 22 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 22 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 23 indices rho q2 m2 2 1308982042368000 13=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 23 indices rho q2 m2 2 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0x3ddc2200,-0x53501c40,-0x319d47e0,-0x113765fc,-0x3db8db0,-0x956481,-0xf7580,-0x1145a,-0xc50,-0x49]
def m3 : List ℤ := raw_ints% [0x0,-0x9bb38732183776400,0x78eaaa0ecaeb6eeb00,-0x2b7e8f14fd745c4a300,0x99b57959f780a2e99c0,-0x174c482d2ec9d8a71bc0,0x290a1a213876c7ec4c00,-0x36330984909a0089cc00,0x369962cbe0e3b7c1f0f0,-0x2a435833970d6aa2bb70,0x191e761a93e8d806d6c0,-0xb5dc74e171ecf220cc0,0x3d9412bc3646c5312e0,-0xf28fa290da10268ee0,0x297a7238b8d3c9c1c0,-0x4932af987ec52c2c0,0x49464a1635d6a3f0,-0x20422877fe42770,0x33bb895491f00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 10 24 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 24 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 23 indices rho q3 m3 3 1308982042368000 13=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 23 indices rho q3 m3 3 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x49,0x1]
def r4 : List ℤ := raw_ints% [0x11a3c5b200,0x1783fbec40,0xdd28962a0,0x4b72eccfc,0x108640b78,0x26be40bd,0x3d35408,0x3f813a,0x27f00,0xbed]
def m4 : List ℤ := raw_ints% [0x0,0x7e81ddd8b3ad101400,-0x6002626a0e84787af00,0x21b30099a0902a2e1700,-0x74041cd1a2b0a98e3ec0,0x11190de3007e7a32cecc0,-0x1d385123165089ccbc800,0x25582d0869eaa0c86d400,-0x244c3909c5a113a023c30,0x1b03786ab553be4f245b0,-0xf5eeda919b4066a758c0,0x69fb24a0272f5411b9c0,-0x21f32bfc55b0b531c960,0x7d7048f27a8c7c23360,-0x13e3ca0a8a2d89920c0,0x2005edaf9f08e75fc0,-0x1c8b631504e042730,0xac22b92aa5ef1b0,-0xdd18430a41400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 10 26 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 26 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 23 indices rho q4 m4 4 1308982042368000 13=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 23 indices rho q4 m4 4 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0xbed,-0x49,0x1]
def r5 : List ℤ := raw_ints% [-0x2e1ba417a00,-0x3cfee9b3540,-0x2382cb63e20,-0xbf7f21dbac,-0x294a2b9c48,-0x5ed41b129,-0x91a70470,-0x913169a,-0x560888,-0x176b1]
def m5 : List ℤ := raw_ints% [0x0,-0x66c9844011fc9d10400,0x4c54ba24b30784a8e300,-0x1a2d3f85d618a50d56b00,0x57e5ed2c0429bfd1ecfc0,-0xc9c35b00d8888089a95c0,0x14ee7bef2e58a897601000,-0x19ea4ae8d5e955dccafc00,0x185393d786edbe72d70e70,-0x116ba099637a20242ab5f0,0x97edc42634918a85e2dc0,-0x3e601693cae03c2adfec0,0x12e79f730cef8478619e0,-0x417e4491838fdea843e0,0x99e9bcc4fe7aeb989c0,-0xe1a83b1a8a522af4c0,0xb2921fdfe11721d70,-0x3965f60f8d03c1f0,0x3aeed468acf000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 10 28 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 28 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 23 indices rho q5 m5 5 1308982042368000 13=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 23 indices rho q5 m5 5 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x176b1,0xbed,-0x49,0x1]
def r6 : List ℤ := raw_ints% [0x5a8a5edf8200,0x770ee9678e40,0x44ce2624bca0,0x16faa9956d1c,0x4e5ecdeebe8,0xb15eb48a2d,0x10b43207c8,0x103a64d5a,0x94730d0,0x26603d]
def m6 : List ℤ := raw_ints% [0x0,0x5383bb740e9d3f9d3400,-0x3cc2eee0b6e305dcf8700,0x1462365c0793bc047eef00,-0x42d6b5dc2eb3c5f97a2cc0,0x9585b5f291dc8e275cfac0,-0xf152fa8681cb5902abb800,0x121bbd099fafa75ea909400,-0x106e6048231636cd6c64bb0,0xb54aca8ecca498e9f2bd30,-0x5eb8486e900d7c1d9a8ac0,0x250fb993f85dc799c177c0,-0xaa0a0a8203fae8862e860,0x228158229a39c9c5eca60,-0x4b083622ff8e0d482ec0,0x63fad7c7b8e39d3fdc0,-0x4607cb64b4afef56b0,0x132133e91ff9f4130,-0xfad7511b9f4000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 10 30 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 30 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 23 indices rho q6 m6 6 1308982042368000 13=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 23 indices rho q6 m6 6 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r7 : List ℤ := raw_ints% [-0x945ee56341a00,-0xc22abb74f3940,-0x6f8f08f469220,-0x24fe3ddb5106c,-0x7d0fa462de68,-0x117f3b5a0649,-0x19ffef90350,-0x18cea3b3fa,-0xdd8c6f88,-0x376c371]
def m7 : List ℤ := raw_ints% [0x0,-0x43db084e4bdfc3afba400,0x306cf3d0c0aa245259db00,-0xfe90a5d1a1d4ed477ca300,0x33011b7d98ca9a4645f25c0,-0x6f5294ca03294c8fc761bc0,0xaee2659822ada3b3708d000,-0xcbceb2dc31f64269b801c00,0xb2eb06e0a6214bead5277f0,-0x76e6006fb7927a405705b70,0x3b939feb1357d469b5bdbc0,-0x1638f02d0c2ce281f96e4c0,0x607561785674307e3ecce0,-0x1255b0e2bd9a1e4e4406e0,0x24d8e7c6ffaf936f797c0,-0x2c8894b3fcf7f1543ac0,0x1b87b7139a59ce5a6f0,-0x65eeb0122dd8d2f70,0x429b105d40f0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 10 32 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 32 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 23 indices rho q7 m7 7 1308982042368000 13=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 23 indices rho q7 m7 7 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r8 : List ℤ := raw_ints% [0xd64717a8110200,0x11750ee3b2d1e40,0x9fb98bbe1d20a0,0x34a9ef3304661c,0xb0ceaeef50628,0x1886e08cf87cd,0x240fd782af68,0x21f364b75fa,0x12a08af2f0,0x48e274fd]
def m8 : List ℤ := raw_ints% [0x0,0x3721f6bf9da5cefec75400,-0x26a373653d97812e0501f00,0xc7272a95bf20af85263c700,-0x270db37ee0779cc2e1008ac0,0x5340e70ef420737674e688c0,-0x7f6f58ce0c2a9f287253f800,0x904ab05b4c3c79cea6b83400,-0x7aa7f4face0d1a449a2ee730,0x4e9ace86dee6a3508ea9d4b0,-0x25caf06d8322356374fce0c0,0xd7125e247d987f06e86d5c0,-0x373161c429a1b2a74aaaf60,0x9d2238e52b2fa3f2e9a160,-0x1237ceaa683e95c603f4c0,0x13edffe6cf64a4687dbc0,-0xad7c02f3e260be66230,0x21ea3f4e7bd40d70b0,-0x11a7a22aee140000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 10 34 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 34 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 23 indices rho q8 m8 8 1308982042368000 13=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 23 indices rho q8 m8 8 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r9 : List ℤ := raw_ints% [-0x119ca22ae5f59a00,-0x16e1f3a5eb67e940,-0xd08cece85946a20,-0x44715e94850d96c,-0xe47f8aee62d468,-0x1f7ba5ece013c9,-0x2de81b56fca70,-0x2ac6ed9d03da,-0x172b1437668,-0x592a5e511]
def m9 : List ℤ := raw_ints% [0x0,-0x2ccb987bb016b82f01f4400,0x1edcffbafad50bb5b9119300,-0x9c24ed05e15e57be5e0b9b00,0x1e002d26d1fc0ca15c8a6ebc0,-0x3e87df1a24a730cbb3a1251c0,0x5d5a81248eca6ba8b6a245000,-0x66cb6212ee444581d9b14fc00,0x54ae71894414330dfbe4ddd70,-0x345ea296b7a2e95c9b7994cf0,0x182bf1e6e3622e5e1d83169c0,-0x83313bc8d51d5ae3f5cd9ac0,0x1fd791cc8a11873bfaabf7e0,-0x54ce16c9a998b92587a81e0,0x9103ac9bde3a4afcbaf5c0,-0x8f4a4f7010d299fd6d0c0,0x446c17e999254fb3ac70,-0xb45b3e8d734e5c48f0,0x4ac03d324df00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 10 36 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 36 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 23 indices rho q9 m9 9 1308982042368000 13=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 23 indices rho q9 m9 9 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r10 : List ℤ := raw_ints% [0x158bc4b9ff0084200,0x1bead986000e18640,0xfd9c4d7c24b53ca0,0x52e8ef63a0bfc79c,0x11386613b0c635a8,0x25c0dfab51f59ed,0x36af1532d3eb88,0x328b13129eb1a,0x1b19e68d4350,0x66ffd1983d]
def m10 : List ℤ := raw_ints% [0x0,0x24656be47f1275a631967400,-0x18adb54276648f93e61e47700,0x7aae3e133158b2535b31a5f00,-0x171e64f5ebf19dbaecb77898c0,0x2f294fb4c78151c219573846c0,-0x44bce74055632040327f5b3800,0x49ac8007b2b7896ee58bd25400,-0x3add33d0f74b593ffd8b560eb0,0x232714c0dcdc9054d01f291830,-0xf95328a87d80a6f747a91e6c0,0x50acf94b507f8223d4da9e3c0,-0x1283dc68f576dde29017eae60,0x2e183ac7c2bbb2ad029eb060,-0x488df52e43a08de21c3aac0,0x409e53e2c7721b16b869c0,-0x1b03204dd13c048ec59b0,0x3be036beeaac4296c30,-0x13c00b7c407400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 10 38 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 38 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 23 indices rho q10 m10 10 1308982042368000 13=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 23 indices rho q10 m10 10 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x66ffd1983d,-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r11 : List ℤ := raw_ints% [-0x18e386775f33a41a00,-0x202c6ff7f64b147940,-0x123791546102259a20,-0x5efaa9bf920c7b06c,-0x13a6c6de49cdae3e8,-0x2ae323da9ae2d489,-0x3dc835ec6d76b90,-0x38bade9ae3003a,-0x1e2d288f501c8,-0x7190a0a48f1]
def m11 : List ℤ := raw_ints% [0x0,-0x1d9267a9a73eff97084a3e400,0x13c0bf61e8234d345ac89a0b00,-0x6095093584ec2d0a951efd5300,0x11de7cb7e19706bdd1648d0a1c0,-0x23b639f46b7209dc6bde8a1f7c0,0x32dd063e3e96c116565cc51d000,-0x351c5e02c86503915fcda1ddc00,0x29304db1cbfee6871a87bb5def0,-0x17c461f3b1a1a7ec003959fba70,0xa1f77b26f2763456b93138a7c0,-0x31ff5ba5ebc9b2542cb0e8c0c0,0xad8b9e44a6a9dcc82586b7ae0,-0x19388ef69bd87f210ef7f54e0,0x247d1b4a32b081259bfa03c0,-0x1d3ab4824aa7aee070556c0,0xaabb7fd05e425187dadf0,-0x13da9d49bd93331ffe70,0x535e5ae7d3f000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 10 40 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 40 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 23 indices rho q11 m11 11 1308982042368000 13=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 23 indices rho q11 m11 11 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x7190a0a48f1,0x66ffd1983d,-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r12 : List ℤ := raw_ints% [0x1b711da678d79cc0200,0x236735684d95d387e40,0x13ffad5500034f330a0,0x67fb4e60489b88481c,0x1571cdc4f213147428,0x2e9f36e8b18649dcd,0x42dbcabbf577c6a8,0x3d0f8577d3314ba,0x2045194a139db0,0x787dcc75363d]
def m12 : List ℤ := raw_ints% [0x0,0x1806f439d7e32faab6bc529400,-0xfd350947a91e123ad9efd28f00,0x4c2e7282d1a9d75ff9e3804b700,-0xdd9f0a23881c35626612cb1d6c0,0x1b2550fb7b1a8a3e7cd9ee1eb4c0,-0x25d0f8791e3669a2ce73aebe7800,0x2680b4e442212c7cf71ac1897400,-0x1d0157e0d91852d1fcd9a1142230,0x102e9708fae044e7f64404fba7b0,-0x69ff2b695965e429e3aafdd5cc0,0x1f37954868e9e490f7ced10a1c0,-0x666456f2725fad59d83c632560,0xde2b710b1ecbea15eb3f7b760,-0x126fc169c99d8392651b6d0c0,0xd416e812f9552397f2227c0,-0x4377b547e46cbd1a501d30,0x6933bd53cf63c6dcd3b0,-0x15f6b105b114000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 10 42 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 42 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 23 indices rho q12 m12 12 1308982042368000 13=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 23 indices rho q12 m12 12 1308982042368000 13 9
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_12
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<13) : intPolyRF (mz e)=rfPoly (C (1308982042368000:ℚ))*rfX^13*(1-rfX)^9*momentRF (key size) (X^e) := by
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
#print axioms moment_source_12
end
end CatalanCore.Li2.NVMod.FamilySource.U3C13
