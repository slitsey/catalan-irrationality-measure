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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C14
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,14,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x3ddc2200,0x53501c40,0x319d47e0,0x113765fc,0x3db8dd4,0x956505,0xf7641,0x114ea,0xc8a,0x55,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x5,0x5a,-0x1ea,0x3d4,-0x3e04,0x16f8,-0xaa28,0xbf6d,-0x18f65]
def rhoDenominators : List ℤ := raw_ints% [0x276,0xe,0x7,0x3,0x1,0x5,0x1,0x7,0xe,0x7e]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 14
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
def m0 : List ℤ := raw_ints% [0x0,-0x2f3e17af440,0x298669812db0,-0x110a419277d50,0x455153178f54c,-0xc37f957136a84,0x1954173554aa74,-0x27e99359f7751c,0x30c3ba3294d857,-0x2eb00b55e6cd0d,0x23275b7db12231,-0x14c37f289d9f43,0x98923571392f2,-0x3599e54bb03a6,0xe08c7af1ea56,-0x2a10f99cc6c2,0x5483b6871bb,-0x65b8108939,0x3ab9b1505,-0x903badf]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 10 21 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 21 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 24 indices rho q0 m0 0 4000752000 13=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 24 indices rho q0 m0 0 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x2662733e6740,-0x20f16c87cf1b0,0xd2edd85b06aa0,-0x3439a1f121d1fc,0x8f377ea87be808,-0x1202896d7d7280c,0x1b7db3fbafd5b90,-0x207612303cb1e2b,0x1df4842b301e4c2,-0x15aba925292db37,0xc404cc3d55aeec,-0x55c35b21f48982,0x1c89d28a864e64,-0x70646f6cdd902,0x1398a680ca800,-0x2420bd1c9d17,0x270df4dfb82,-0x1387a2814b,0x26b4caf4]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 10 22 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 22 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 24 indices rho q1 m1 1 4000752000 13=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 24 indices rho q1 m1 1 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% [0x1]
def r2 : List ℤ := raw_ints% [-0x3ddc2200,-0x53501c40,-0x319d47e0,-0x113765fc,-0x3db8db0,-0x956481,-0xf7580,-0x1145a,-0xc50,-0x49]
def m2 : List ℤ := raw_ints% [0x0,-0x1f2ffda2b3e40,0x1a2b51497bc2f0,-0xa39cebe187d4e0,0x27801cee33b1d4c,-0x697475f6b06a658,0xce3120d135135fc,-0x13139ebb77419180,0x15caede5dfc641af,-0x1366dd426e87db86,0xd7f30f299ccd983,-0x74ee13f6ac7b538,0x30c300493e0593a,-0xf5ef760e988d9c,0x38e4dcd77dae4a,-0x9397f51c97148,0xf9440b171fcb,-0xf14ba8e3b76,0x6807f64d47,-0xa5cb8ff0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 10 24 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 24 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 24 indices rho q2 m2 2 4000752000 13=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 24 indices rho q2 m2 2 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [-0x49,0x1]
def r3 : List ℤ := raw_ints% [0x11a3c5b200,0x1783fbec40,0xdd28962a0,0x4b72eccfc,0x108640b78,0x26be40bd,0x3d35408,0x3f813a,0x27f00,0xbed]
def m3 : List ℤ := raw_ints% [0x0,0x1956fe14322940,-0x14d090e00f2c230,0x7f3b6303fca6860,-0x1dfd0b235e5b20dc,0x4e08d59fe9af69b8,-0x94711be7e60c64cc,0xd5543dfcd2b561c0,-0xec032170c0a34d63,0xcae73e43438663de,-0x87d5e989e253c2c7,0x467d5065e7f9d628,-0x1c0752f5d83d6672,0x85ee1acf27ca94c,-0x1d1c1848d05c582,0x46287f5c9aa908,-0x6c58d53c0524f,0x5da2c1a53b4e,-0x22a6fdcb7bb,0x2c4936940]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 10 26 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 26 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 24 indices rho q3 m3 3 4000752000 13=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 24 indices rho q3 m3 3 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [0xbed,-0x49,0x1]
def r4 : List ℤ := raw_ints% [-0x2e1ba417a00,-0x3cfee9b3540,-0x2382cb63e20,-0xbf7f21dbac,-0x294a2b9c48,-0x5ed41b129,-0x91a70470,-0x913169a,-0x560888,-0x176b1]
def m4 : List ℤ := raw_ints% [0x0,-0x1496ae7068c1840,0x10937cd5504a2c70,-0x632e928c675200e0,0x16d97d374aad6a92c,-0x3a0523a060af84158,0x6b7f133b66a1fa5dc,-0x962310499087fc8c0,0xa10460e6b5b042187,-0x85cae66f6c799dd06,0x5642fcb468592519b,-0x2aed012f42339bbc8,0x1047d9d8fc0b37aca,-0x49b49b898900515c,0xf0b9af86a8e001a,-0x21a77dcbad264e8,0x2f6f7435231183,-0x247ca359114b6,0xb8b0d42baff,-0xbcdf0af00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 10 28 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 28 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 24 indices rho q4 m4 4 4000752000 13=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 24 indices rho q4 m4 4 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [-0x176b1,0xbed,-0x49,0x1]
def r5 : List ℤ := raw_ints% [0x5a8a5edf8200,0x770ee9678e40,0x44ce2624bca0,0x16faa9956d1c,0x4e5ecdeebe8,0xb15eb48a2d,0x10b43207c8,0x103a64d5a,0x94730d0,0x26603d]
def m5 : List ℤ := raw_ints% [0x0,0x10ba6dbb551d3b40,-0xd375ac4c435001b0,0x4d7f4bda6e4415360,-0x11788df573917bf93c,0x2b567a4587db1c2178,-0x4e49aca4b6f546e0ac,0x6a5f60c8cd2a435cc0,-0x6eb1a910bf5cee295b,0x58f909ea70da227a4e,-0x37493cfa4d2181305f,0x1a656e1b2c3695e528,-0x98d5f3a85331b6e42,0x28f88da49c3a470ac,-0x7d9d04e7a0ca09d2,0x1047e2fb0d1abbc8,-0x14e72a79a994a27,0xe444d650bb13e,-0x3d810cc8c673,0x323e887400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 10 30 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 30 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 24 indices rho q5 m5 5 4000752000 13=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 24 indices rho q5 m5 5 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r6 : List ℤ := raw_ints% [-0x945ee56341a00,-0xc22abb74f3940,-0x6f8f08f469220,-0x24fe3ddb5106c,-0x7d0fa462de68,-0x117f3b5a0649,-0x19ffef90350,-0x18cea3b3fa,-0xdd8c6f88,-0x376c371]
def m6 : List ℤ := raw_ints% [0x0,-0xd9779283527c0240,0xa8c9dc175a59d15f0,-0x3cb0a32c81bee3e3e0,0xd67392b7e3c191be0c,-0x2083bcb43ea2a6cb718,0x395402a172edec3f63c,-0x4bda69868eab43966c0,0x4ca9405518fe6571d1f,-0x3ba7524cc3afc88cbf6,0x23bfc72f57ba74c8dd3,-0x1062762c37700664d08,0x5a8a5cdf686c22065a,-0x16fe5305962d0e04bc,0x4224058c51d667f2a,-0x7f02a13f46e88228,0x943cd80acc8dd7b,-0x59818e3fad9226,0x147830cd04dd7,-0xd5761ef000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 10 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 24 indices rho q6 m6 6 4000752000 13=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 24 indices rho q6 m6 6 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r7 : List ℤ := raw_ints% [0xd64717a8110200,0x11750ee3b2d1e40,0x9fb98bbe1d20a0,0x34a9ef3304661c,0xb0ceaeef50628,0x1886e08cf87cd,0x240fd782af68,0x21f364b75fa,0x12a08af2f0,0x48e274fd]
def m7 : List ℤ := raw_ints% [0x0,0xb0b1270ab304c1d40,-0x86dfb2e60427961d30,0x2fa16154b691fbe8a60,-0xa50d3c08046d698989c,0x187f9d29441c014bf838,-0x2a339a5e6b0bb1db198c,0x366d7f7675fbf0381ac0,-0x357872f0f5d45fe90413,0x28502c919b0337299b7e,-0x1750956ac6951eb98237,0xa4331b337a4b5b0c868,-0x362286f6072e6beca92,0xd05c017bba9a78568c,-0x231f9dc372d289eda2,0x3e60c133ee625fe08,-0x420b240a0190abbf,0x232c8f72f1c3aee,-0x6ce9e40a7346b,0x3894c094000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 10 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 24 indices rho q7 m7 7 4000752000 13=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 24 indices rho q7 m7 7 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r8 : List ℤ := raw_ints% [-0x119ca22ae5f59a00,-0x16e1f3a5eb67e940,-0xd08cece85946a20,-0x44715e94850d96c,-0xe47f8aee62d468,-0x1f7ba5ece013c9,-0x2de81b56fca70,-0x2ac6ed9d03da,-0x172b1437668,-0x592a5e511]
def m8 : List ℤ := raw_ints% [0x0,-0x8f8fefb8b173dd7c40,0x6be285692b6f1ef7b70,-0x25754ccdef0a1b01aee0,0x7f6c86be6a02815625ec,-0x1288caa8528d6fe45eed8,0x1f395fe1b1becc6ce5d9c,-0x274a0084e61c1b1fd2cc0,0x258d51150f0784a028c77,-0x1b73a73d9a36c7b5e7f66,0xf54db6154b83f577d4cb,-0x67beabeda1883e8c9948,0x20a803d28e3a16ef466a,-0x77092aaa977151b0b1c,0x12cd597cf51e41b0eba,-0x1ed736e90d5d11c968,0x1d8eddf289a987e33,-0xdd8a7c90c066216,0x242f3874ce626f,-0xef90cbf0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 10 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 24 indices rho q8 m8 8 4000752000 13=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 24 indices rho q8 m8 8 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r9 : List ℤ := raw_ints% [0x158bc4b9ff0084200,0x1bead986000e18640,0xfd9c4d7c24b53ca0,0x52e8ef63a0bfc79c,0x11386613b0c635a8,0x25c0dfab51f59ed,0x36af1532d3eb88,0x328b13129eb1a,0x1b19e68d4350,0x66ffd1983d]
def m9 : List ℤ := raw_ints% [0x0,0x74a4f2c6102e23f4f40,-0x56619f70295580e944b0,0x1d843a4e1fd22ea051960,-0x62aa57e5a5e0c9e844efc,0xe13cbcdea14e4cb432cf8,-0x173709eb4424e5193c256c,0x1c8688c9cfd2a9f814f0c0,-0x1a8c3a4eba1be4f218078b,0x12d4f43bce67f700ac982e,-0xa2997f9f8344cd1d239cf,0x4219a3ed1511cbead71a8,-0x13de4411a19fe79169562,0x44922c1c1ced1f40836c,-0xa24266dd2590e6b03f2,0xf5783ff3c85ca28a48,-0xd480d19ce1aa2ff17,0x5751d7c569c8001e,-0xc023f074dd0b23,0x3f4bdef40000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 10 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 24 indices rho q9 m9 9 4000752000 13=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 24 indices rho q9 m9 9 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x66ffd1983d,-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r10 : List ℤ := raw_ints% [-0x18e386775f33a41a00,-0x202c6ff7f64b147940,-0x123791546102259a20,-0x5efaa9bf920c7b06c,-0x13a6c6de49cdae3e8,-0x2ae323da9ae2d489,-0x3dc835ec6d76b90,-0x38bade9ae3003a,-0x1e2d288f501c8,-0x7190a0a48f1]
def m10 : List ℤ := raw_ints% [0x0,-0x5ec60540ed257d370640,0x453a7fd32a1de28d87cf0,-0x174d62e7cfa38e3a19b1e0,0x4c9d0dcc7881370d4438cc,-0xabb8064363d3b0c20f3c98,0x11575eb206fe1170e8ffbfc,-0x14d38c6d053dfc2673552c0,0x12e374144bf1692a7283d8f,-0xd02c767f7d0238b31b0456,0x6c9cced6f5cf642e916683,-0x2a75051af3b19c8ed88788,0xc2ff07c07b3d8ea9782fa,-0x27d04359263f4ae877c7c,0x58235ca4afdc3c624eca,-0x7acbaa59809e974caa8,0x5fd020acffe96175ab,-0x227261738eccd6b86,0x3fb1b8a8e80e8c7,-0x10b2f11f00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 10 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 24 indices rho q10 m10 10 4000752000 13=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 24 indices rho q10 m10 10 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x7190a0a48f1,0x66ffd1983d,-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r11 : List ℤ := raw_ints% [0x1b711da678d79cc0200,0x236735684d95d387e40,0x13ffad5500034f330a0,0x67fb4e60489b88481c,0x1571cdc4f213147428,0x2e9f36e8b18649dcd,0x42dbcabbf577c6a8,0x3d0f8577d3314ba,0x2045194a139db0,0x787dcc75363d]
def m11 : List ℤ := raw_ints% [0x0,0x4d00e444c0ae75bcb5140,-0x3787ea91989e976efe5830,0x126de4cd52021f5344f8060,-0x3ba69cb1303717e6895345c,0x8363bbd16cb4b17a0337fb8,-0xd03197dff7ccabb9e299c4c,0xf497589d24632d3a65356c0,-0xd85a657e1191fff63c121c3,0x90d180e7ccee1b640d8a85e,-0x4917a528344317547f20527,0x1b7c00306cd3ba30b85fce8,-0x788e3fd0edf566c67df2b2,0x174a6fa57dc9a086d8d74c,-0x3031b6f4ad4b6ff6a60c2,0x3dbdd42e93ef3bc72088,-0x2b53aab3a3eeb5fba2f,0xd98a68e626bc388ce,-0x1516e9aeb7eb709b,0x4663e39400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 10 42 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 42 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 24 indices rho q11 m11 11 4000752000 13=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 24 indices rho q11 m11 11 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x787dcc75363d,-0x7190a0a48f1,0x66ffd1983d,-0x592a5e511,0x48e274fd,-0x376c371,0x26603d,-0x176b1,0xbed,-0x49,0x1]
def r12 : List ℤ := raw_ints% [-0x1d1d95d457ceb6a01a00,-0x257f6c0b5f792f803940,-0x1523a7c6a031fbcae220,-0x6da72c5a34800ef446c,-0x168d475f96961973b68,-0x30def63765bb1cac09,-0x45d14208205f145b0,-0x3f79f8af4c25911a,-0x215e10e38870428,-0x7bcab98d76491]
def m12 : List ℤ := raw_ints% [0x0,-0x3e90b977dc8dbfa9532040,0x2c94b89ed0cd968f2ea7a70,-0xe999eb6ecc538103419ace0,0x2e9035c2d1bf00ba8cd12eac,-0x64e109be2c76241ce9969058,0x9ce5093222a8631faf86e95c,-0xb47680290c47c0cd7a3c68c0,0x9bceee9df99f238b4d82b667,-0x656a6bc553804f5b1ea8c6c6,0x318b272ad637c014b72810fb,-0x11ed20c08e4820f2a6783fc8,0x4b19165efe8fda1566bf00a,-0xdb9051ca84fdd5dcaad8dc,0x1a8430143dd1456d9e235a,-0x1f2fd1387ca26a68bfde8,0x13a41b710900470ef1e3,-0x55e2ff27de922e1276,0x6f972b22a42dd6df,-0x12850f0f000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 10 44 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 44 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 24 indices rho q12 m12 12 4000752000 13=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 24 indices rho q12 m12 12 4000752000 13 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_12
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<13) : intPolyRF (mz e)=rfPoly (C (4000752000:ℚ))*rfX^13*(1-rfX)^10*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V4C14
