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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C19
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,19,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x3ca7ccc688000,0x64cbb4aa59800,0x4cc7f7e94c900,0x23971aeee9880,0xb3beda6e39b0,0x28f3acc9aef0,0x6f610a97ee8,0xe646333950,0x16d159545b,0x1bc16a027,0x19b449f7,0x11ce603,0x8ef71,0x3115,0xa5,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x7,0x7,-0x15,0x7,-0x79,0x441,-0x4fe1,0x22f27,-0x49f,0x49f,-0x7e7,0x363]
def rhoDenominators : List ℤ := raw_ints% [0x9056fa0,0x69930,0x1ce0,0x948,0xd8,0x64,0x8,0x31,0xe0,0xbd0,0x5460,0x108,0x252,0xf15,0x36be]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 19
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤18))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤18 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1]
def omegaDens4 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10]
def omega4 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums4 omegaDens4
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_4 : padCoefficients 19 omega4=padCoefficients 19 (omegaCoefficients 18 4) := by decide +kernel
theorem omega_spec_4 : coefficientsPoly omega4=omegaNumerator 18 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_4
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 19 omega5=padCoefficients 19 (omegaCoefficients 18 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 18 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 19 omega6=padCoefficients 19 (omegaCoefficients 18 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 18 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 19 omega7=padCoefficients 19 (omegaCoefficients 18 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 18 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 19 omega8=padCoefficients 19 (omegaCoefficients 18 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 18 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 19 omega9=padCoefficients 19 (omegaCoefficients 18 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 18 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 19 omega10=padCoefficients 19 (omegaCoefficients 18 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 18 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 19 omega11=padCoefficients 19 (omegaCoefficients 18 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 18 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 19 omega12=padCoefficients 19 (omegaCoefficients 18 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 18 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 19 omega13=padCoefficients 19 (omegaCoefficients 18 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 18 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 19 omega14=padCoefficients 19 (omegaCoefficients 18 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 18 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 19 omega15=padCoefficients 19 (omegaCoefficients 18 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 18 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 19 omega16=padCoefficients 19 (omegaCoefficients 18 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 18 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 19 omega17=padCoefficients 19 (omegaCoefficients 18 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 18 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 19 omega18=padCoefficients 19 (omegaCoefficients 18 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 18 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0xc,0x42,-0xdc,0x1ef,-0x318,0x39c,-0x318,0x1ef,-0xdc,0x42,-0xc,0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 14 li0=padCoefficients 14 (liCoefficients 13 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 13 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0xb,0x37,-0xa5,0x14a,-0x1ce,0x1ce,-0x14a,0xa5,-0x37,0xb,-0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 14 li1=padCoefficients 14 (liCoefficients 13 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 13 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x9,0x23,-0x4b,0x5a,-0x2a,-0x2a,0x5a,-0x4b,0x23,-0x9,0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 14 li2=padCoefficients 14 (liCoefficients 13 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 13 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0x5,0x1,0x33,-0xae,0x126,-0x126,0xae,-0x33,-0x1,0x5,-0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 14 li3=padCoefficients 14 (liCoefficients 13 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 13 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,0x3,-0x31,0xa5,-0xf6,0x7e,0x7e,-0xf6,0xa5,-0x31,0x3,0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 14 li4=padCoefficients 14 (liCoefficients 13 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 13 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0x13,-0x5f,0x4b,0x14a,-0x372,0x372,-0x14a,-0x4b,0x5f,-0x13,-0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 14 li5=padCoefficients 14 (liCoefficients 13 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 13 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x33,-0x19,-0x2a3,0x672,-0x3ea,-0x3ea,0x672,-0x2a3,-0x19,0x33,0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 14 li6=padCoefficients 14 (liCoefficients 13 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 13 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x73,0x259,-0x92d,-0xae,0x1b66,-0x1b66,0xae,0x92d,-0x259,-0x73,-0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 14 li7=padCoefficients 14 (liCoefficients 13 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 13 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xf3,0xcef,-0x4b,-0x5646,0x48ae,0x48ae,-0x5646,-0x4b,0xcef,0xf3,0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 14 li8=padCoefficients 14 (liCoefficients 13 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 13 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1f3,0x3331,0xb35b,-0xfea6,-0x1fcc2,0x1fcc2,0xfea6,-0xb35b,-0x3331,-0x1f3,-0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 14 li9=padCoefficients 14 (liCoefficients 13 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 13 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3f3,0xb2f7,0x5804d,0x6d542,-0xd0c7a,-0xd0c7a,0x6d542,0x5804d,0xb2f7,0x3f3,0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 14 li10=padCoefficients 14 (liCoefficients 13 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 13 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7f3,0x24c49,0x1f4b23,0x72f822,0x5b5756,-0x5b5756,-0x72f822,-0x1f4b23,-0x24c49,-0x7f3,-0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 14 li11=padCoefficients 14 (liCoefficients 13 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 13 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xff3,0x74c3f,0x9b73a5,0x3f3f08a,0x9afbd9e,0x9afbd9e,0x3f3f08a,0x9b73a5,0x74c3f,0xff3,0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 14 li12=padCoefficients 14 (liCoefficients 13 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 13 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0xd,0x4e,-0x11e,0x2cb,-0x507,0x6b4,-0x6b4,0x507,-0x2cb,0x11e,-0x4e,0xd,-0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 13 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^13 := by
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
  | 18=>omega18
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
  | 12=>li12
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 18 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 4 19 at hb
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
  · exact omega_spec_18
theorem cache_li (j : ℕ) (hj : j<13) : coefficientsPoly (cache.li j)=liNumerator 13 j := by
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
  · exact li_spec_12
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x10dfecd3c1890400,-0x1661113d5f87a2b00,0xe2ca33534e4542500,-0x5b477a7f2f7a7a33c0,0x1a345b362ce726b74c0,-0x5b596978273b53fce30,0xfb0f78d9effe4c279a0,-0x22dd8d28e61e2a03a5cc,0x3fb8c9bd315a61c17664,-0x60f2e8534757011c4ea4,0x7bcc638aa1108e626a50,-0x856107cda135f60ac55f,0x799647f0c4611d2128ad,-0x5dd7e0b6386212b32ed1,0x3d3d31476900604cee67,-0x21ab6818cbb2abcbea4f,0xf8181a9e052a90bcd25,-0x5ee36133caf6a54c859,0x1dc86d1ce3c47dc84ff,-0x78c136dd7824e97825,0x1827ea5a82a263aecf,-0x3b240dcc800af5c0b,0x69ced69b661486bd,-0x80f31d81487dfa1,0x5f27589b3be4bb,-0x21cd507b6e3f7,0x32cb4d0e46d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 15 26 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 26 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 32 indices rho q0 m0 0 19654365366155520000 18=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 32 indices rho q0 m0 0 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x12fbea6e39ba24800,0x189e495cc163afce00,-0xf3c6e006659cbdf800,0x5fcccfad484ca29fe80,-0x1ad4c8ae6993d8238d40,0x5b2bb0d1836ae659b360,-0xf4014c33ff5b013c0d30,0x20f6a95fe4c0bd5316478,-0x3a8a26b26c1d24f5ae8e0,0x566f206f2b34070199818,-0x6af6d988d27032f5affec,0x6f83775465879e7aaad66,-0x62329955de7396eac9ea8,0x49129ebfcdeb5da541016,-0x2ddfe004a1341fe7525c0,0x183437eaf8b36dd4a3ebe,-0xaaa7737bdc400f29eee8,0x3e3e4149dda2698ff8ae,-0x128e3c0046e659cac798,0x471ba2e5350fad28312,-0xd5d008c5a7a303eeb8,0x1e7ffe9cf1fc896fc2,-0x325a22590eed6c7b0,0x37d3b6aca589ea52,-0x24b1c191eea8598,0xb369e360fb182,-0xd931dfb85dc]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 15 27 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 27 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 32 indices rho q1 m1 1 19654365366155520000 18=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 32 indices rho q1 m1 1 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x155b67bc00f1691000,-0x1b1a39df8ad9f01c400,0x106713fd144d680d4600,-0x64c7578a313c4f838400,0x1b8edccde260ea88c28c0,-0x5b584f430318ae50ccf00,0xee3fb7d3c09d96c1bfcf0,-0x1f557053acb9c9529d52a0,0x361c1e2f428f875060fa28,-0x4d9732b0059daff90a0638,0x5d1f4b876d4321ac439574,-0x5e01a1a034fcdf75430110,0x5004aeb0362e2c5981a6da,-0x3971cebd7dfca83bf5525e,0x22b6b20cb3d21469cf4428,-0x1195b53927a51006acbb24,0x76af689be4c53544768f6,-0x294b1fb3c32930208fdca,0xbb1a4bc7fa9bd9916b84,-0x2a5a997202c262e73228,0x779b63ebddd79f8caa6,-0xfe5263e90ad8e4eff2,0x182fbc6d8abc320f60,-0x1859eee4f685981c4,0xe376d712737b4e2,-0x3b8e9f1b083fee,0x39ebdf060650]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 15 28 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 28 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 32 indices rho q2 m2 2 19654365366155520000 18=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 32 indices rho q2 m2 2 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m3 : List ℤ := raw_ints% [0x0,-0x1806d4b3810f9632000,0x1ddc2ae8209395199000,-0x11af7eaeefb3e4947a200,0x6a423694525d181501500,-0x1c640f4524dea010b46440,0x5bde0f27b90e62779d2e40,-0xe9afb76ff2f20866c09990,0x1df123db1f59363e3c2bf70,-0x3250d832e7157ef425b88b8,0x461eafbaa18c27f099fd678,-0x51abfd0af5ab62025b566cc,0x4fe30c78a589f6bf247d904,-0x41c56d36c8240236596031e,0x2d93df7b8dfdbb93dd6de6e,-0x1a868fd638f77e87b12dd18,0xce82a2af0db0d598319a50,-0x536b76c7dc861366fca132,0x1bb174de84913600a7bac2,-0x7735c9a8d468dcf48fc4c,0x198090889df4c964961b4,-0x439d316f419c938b0622,0x85d8110c1d24dbb2a52,-0xbb7d9501ba4701dfc0,0xab1811c35e133f5c8,-0x5878b7e5b2dbbf56,0x13c6366c6462886,-0xf6a609584dc0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 15 29 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 29 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 32 indices rho q3 m3 3 19654365366155520000 18=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 32 indices rho q3 m3 3 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m4 : List ℤ := raw_ints% [0x0,0x1b07af49f13188f84000,-0x20ec44ae934a552626800,0x1318edabf7b6e44d857a00,-0x7049da61e9d209b104d900,0x1d5616eb243481859fb74c0,-0x5cbcb1478e38153efe67f40,0xe63b52f800bec9c35755f30,-0x1cc284386467fc4c8a91d530,0x2f0ff5934385717725842638,-0x3fc8948ca5ac28ea31f86598,0x48255195e529a691ede4c514,-0x446b9ca0eba96c4b3256b5f4,0x368445a649f063f8d5d2bdde,-0x247caa7656dd0ba4e584d916,0x14760112aecfce5615a14450,-0x9912e94dd80a0dc99b48b10,0x3b3b6c97902f2ac74558702,-0x12c415c5903d30922fd261a,0x4cbfed5a4e25d208ea10c4,-0xf83a7e221599e5e4acce4,0x269a25ed961f4f2f59642,-0x4715caf44e68f240462a,0x5b8e8221c6570f2a5e8,-0x4b952f4678026e5e28,0x2285a31c2f97063a6,-0x690808585e8f38e,0x418561de3ed00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 15 30 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 30 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 32 indices rho q4 m4 4 19654365366155520000 18=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 32 indices rho q4 m4 4 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m5 : List ℤ := raw_ints% [0x0,-0x1e68a5332f57ba1748000,0x2453aaf46b42320ae61800,-0x14a700ece0fcf2d8b200a00,0x76ec1f422f1da685d98ef00,-0x1e66ee91f6043cea411b7840,0x5df4e421544071109b979dc0,-0xe3d0fa1637d1a6663bb73010,0x1bc38ef60fdc510d4f9b8d150,-0x2c457c9f408d9fb3629f7cfd8,0x3a63eb744ec09e760cd42f878,-0x402d9f94205bd72c4dacf950c,0x3b0bdbba169209ec9b2600b7c,-0x2d8ed4492d6277ade8a0be466,0x1d76b4761fb2a61b2885a916e,-0xfed6c3d4bbb0659fdcb326c8,0x728c1785e334b05855e6ecd8,-0x2a78999a35c9a9d13eb8b5ca,0xcd7f8b4a241e9fba1670672,-0x31e84b250e1a08eaab389ec,0x987dfd02add6f184ac63bc,-0x163eafd281c521f4510e9a,0x26136caf3f7e6c08c30f2,-0x2d0875ada25a9bb50270,0x219104fddf25c6d99e0,-0xd8185e079ca1090de,0x22da1b2d215172b6,-0x115fdf67a21c00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 15 31 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 31 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 32 indices rho q5 m5 5 19654365366155520000 18=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 32 indices rho q5 m5 5 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m6 : List ℤ := raw_ints% [0x0,0x2235b9d99542b15a310000,-0x281c9bddfe91f3b03d4f800,0x165dc4606bb29cfdf3d58a00,-0x7e387a7722e4f1178c1acd00,0x1f98dab0b4ab87f17e6ab4cc0,-0x5f883f3db85c5ef0c291a5c40,0xe262ff74063a2847471a4f130,-0x1aef4a84adeaa19f12cc574c70,0x29e100c555c6d1495e31d4fa38,-0x35c937c3bb618804ec0ccc38d8,0x397b1a55ec1b3a61b355fa0694,-0x335596a8d1b91c068e6bcb2684,0x265fbed7b8160acc7712769a9e,-0x17fe35ed614307dde39f686726,0xc821d522ef7576a32747ceed0,-0x5681abf6261aad921a3b385e0,0x1ebdb1a2c31cd7a7e50c3c7c2,-0x8dfe4aacaafca69db0e6026a,0x20c34858fac656e09489dc44,-0x5e8d2ee322c5cf9fabdcf94,0xcee7ff8902cbe8e94a7482,-0x148e7fb25dacac1552745a,0x164bc1899ff322b963968,-0xef9ee46aab0081e10d8,0x54b7b8fe9a9a07abe6,-0xb8ea3bfbd6168ebe,0x4997d596f05000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 15 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 32 indices rho q6 m6 6 19654365366155520000 18=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 32 indices rho q6 m6 6 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x1]
def r7 : List ℤ := raw_ints% [-0x3ca7ccc688000,-0x64cbb4aa59800,-0x4cc7f7e94c900,-0x23971aeee9880,-0xb3beda6e39b0,-0x28f3acc9aef0,-0x6f610a97ee8,-0xe646333950,-0x16d159545b,-0x1bc16a003,-0x19b44973,-0x11ce542,-0x8eee1,-0x30db,-0x99]
def m7 : List ℤ := raw_ints% [0x0,-0x267c7114c7eb07857720000,0x2c52929d74aa25407f153800,-0x1841bce9944a43cd189e5ea00,0x864029979edc7447b00b6f700,-0x20ee6ff4cfd33e6d9e51b5c040,0x61794245f9e49b48fdf074a7c0,-0xe1e72e893411e7052994127b10,0x1a419c059171f574979bce545d0,-0x27d4f7da6412a7c984b3d06cd18,0x31d879c64aa7a5e046a4c703238,-0x33d34299c1825184d056a554b0c,0x2cf3910a84693161600a3c4ea5c,-0x20928f25be7c8a7e05ae4744d76,0x13b2ac3fb3aca49a44e6e61f79e,-0x9e846b67d553476b95b7b4a6a8,0x41e931ac2b54e8764c4fd71e18,-0x1674069ccfd94c83e1c9ab84fa,0x6303e1d6c98bdb53dff219b42,-0x15b436c7f90c3fb11c278492c,0x3b24c13be829934c6b220b9c,-0x7946a4d5100ead9297c060a,0xb2e0c391568b2140ddadc2,-0xb1ad1b66f6dd9e3e81050,0x6b581ab345384463ff60,-0x2143fc60375ee04c9ee,0x3d44f5bf9e4f1fd26,-0x13739a71dd9c000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 15 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 32 indices rho q7 m7 7 19654365366155520000 18=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 32 indices rho q7 m7 7 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x99,0x1]
def r8 : List ℤ := raw_ints% [0x24404962a748000,0x3c01172d08f5800,0x2d7eb775c468900,0x14f88720e045b80,0x69339edcf1e1b0,0x17c5e36a1b53c0,0x4001c488329b8,0x82a9e3f3c1e8,0xcbcd8303113,0xf2982c62f4,0xda0a9949c,0x90912e58,0x43a3547,0x1466ac,0x31c2]
def m8 : List ℤ := raw_ints% [0x0,0x2b4bff3760e8687626040000,-0x31026e6914e9bc346cb563800,0x1a57f6f58148db51b065300a00,-0x8f1667bb10951e8e2da4c9fd00,0x226a9ad0415b398540f987ad4c0,-0x63cb57af4e08bcbd38c373f1c40,0xe25677cc9be9afa6252479a9a30,-0x19b7253f48b33e1e28d577051e70,0x261632d4035b51a9e845f5aab3f8,-0x2e77a5b9e471a611585a5d917898,0x2f0776178227c9bf01478b079694,-0x27a36c9ee75d352850f8fc1b74c4,0x1bdb04c67aa83330df62dccec8ce,-0x104cd37357b6a6dc9f8c16d8f6d6,0x7e992760b54b70d4c5d12876f70,-0x32a66823d4b201ab703a51e74c0,0x108b2c9046e025b8d0984bfb952,-0x45a7874fd3651f760c1841f17a,0xe80c83af5de5de252121f8e04,-0x254e158300523f17426851814,0x47a2fcbc659be7cb4d0f6dd2,-0x61f23eed7bb50892416f42a,0x58f8e322e404724d4a4408,-0x304176e5a300820e31f38,0xd13dc0719ebe28aab16,-0x144831f93338f8ba6e,0x52233a301ad0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 15 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 32 indices rho q8 m8 8 19654365366155520000 18=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 32 indices rho q8 m8 8 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x31c2,-0x99,0x1]
def r9 : List ℤ := raw_ints% [-0xbca155b2e7b10000,-0x13731faa21920b000,-0xeb074e6596a9fa00,-0x6bd65f2adfb98800,-0x21a035fe928e0be0,-0x78c791cae60a030,-0x14299c5a7a14010,-0x28c1d4b84694e8,-0x3ecb2dae3960e,-0x4994059ca37b,-0x40c649bf13a,-0x29bf434caa,-0x12c08e64a,-0x55001a3,-0xbab5e]
def m9 : List ℤ := raw_ints% [0x0,-0x30b57f1e4d057584eac480000,0x363a9e45a84beb2b95e56cb800,-0x1ca616dba530816022700bfaa00,0x98d0a924583bb381366e60f3700,-0x2410a81d91ed54bf8dd6698bd840,0x6682dadf974e1b1a6f879b1e1bc0,-0xe3acaff6ba6c774a78cdc0965010,0x194d292739734b71eaa49cd8604d0,-0x249b7231be8aebcc842ff133508d8,0x2b917228b7253e485e9054de334f8,-0x2af25356c203f5ce3dd3e2e17280c,0x233126c50f7d137bee5f14c4704dc,-0x17fed3fa8f2342d19f3add6263126,0xd97a007ed843e52e50466704e70e,-0x65eb75b5993fb8dc6248162e7948,0x273ee301728dec9ed65172f65b38,-0xc4adbf18adc9963f6c4fe945f0a,0x316a21437efa47ba804927cca12,-0x9c59123df6e1961ae95e675fec,0x17b787ce8233c35ca23c1602dc,-0x2a9f928373f52b5aeb4c8adda,0x35f7eaaae5673f50520e7ad2,-0x2cc51df43b580c1e1088af0,0x15c203427ec458addee780,-0x5253606b54bdb432fa9e,0x6b5099af316c60e516,-0x15a591b4375c0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 15 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 32 indices rho q9 m9 9 19654365366155520000 18=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 32 indices rho q9 m9 9 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xbab5e,0x31c2,-0x99,0x1]
def r10 : List ℤ := raw_ints% [0x2c3d027eda5bdf0000,0x48c6fc270ca5a4d000,0x36c8a4b62066c41e00,0x190a0b3d72924f8500,0x7c5af7f8d6fd836a0,0x1bc4204901baa8040,0x49af29a71b98f100,0x93c8fdfcce63b50,0xe1833971c82d82,0x10518c34124544,0xe260059b8237,0x8f033c584e0,0x3e85d019d4,0x110b9266c,0x23571f3]
def m10 : List ℤ := raw_ints% [0x0,0x36cc2f0216a62435881d100000,-0x3c0b523ec526af78adf50ce3800,0x1f326b40d272eb833e7c26c84a00,-0xa386de37d0e8d1607275d3cd1d00,0x25e44ef66263d2a4c8aba4bea1cc0,-0x69a521c21df1b397d9ae3ef094840,0xe5e85fb7890a528370adc77a91730,-0x190175c245deab5031796581664370,0x235d102067d415b74f332216a8bab8,-0x291469030980a201084ca1f41fc858,0x2775bb8d7a2a25f0e00d289db9b494,-0x1f73bc7b4042952f4511fac5f061c4,0x14d11b53743f528a4b0b1ff8c5d03e,-0xb6b4858ce51309f308f9baf2f1a86,0x52b10e086d56cc55e38466e8b3990,-0x1ea72fc60e02d117013af048fdce0,0x9353eb17e8137a8a197714a7f8a2,-0x235731fdca615c4cac0c001ec80a,0x6a2d812c846394cb4570a402ec4,-0xf3102e0c5fd5073b59793a35d4,0x19889731d740028a3db1c93be2,-0x1de8a224778c5114ce905e0fa,0x16a040852f3dc3bc621fec28,-0x9d5ccc6bab32dd20fe1558,0x206859935c3ad52295986,-0x23736bebd55e032a99e,0x5b278fa9be500000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 15 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 32 indices rho q10 m10 10 19654365366155520000 18=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 32 indices rho q10 m10 10 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r11 : List ℤ := raw_ints% [-0x85f95696d52a7b18000,-0xdbdea32c2590f684800,-0xa50b1389b37cb4efb00,-0x4b2fcba139689872380,-0x173fa2eb466bd37ed10,-0x52ae574823b180c730,-0xda3e9fa719c455df8,-0x1b2f044f7a0e2c5f0,-0x2929a25885f80211,-0x2f360618a760e83,-0x2874cc04d8f731,-0x192e66ef925a2,-0xacc3acba463,-0x2de361c21b,-0x5bb94b33]
def m11 : List ℤ := raw_ints% [0x0,-0x3da5b4e2597ae8bc3920b200000,0x4286b2ba0c19e0bde35bd03db800,-0x220401bd0e894f32c785a6848ea00,0xaf53bea1e27fe108e285f30425700,-0x27e9bbdd5b6441691b6052b1463040,0x6d3889d3c2f77ae8b615ad5199d7c0,-0xe90aa1d21cd1b1d8c4b59c0d112510,0x18d25261cb3969c80c7719168f305d0,-0x2254bbc134b84add5d6f3bfc9a40c98,0x26f22bfecb64e4ff575b663d7b291b8,-0x24794addfd00565befdd57ddc54f50c,0x1c4aa57751c22f70759b106e346b9dc,-0x122f118b4534202e7793852c813b0d6,0x9a9bb6aa010ebba892b6d8c49376fe,-0x43991bf53715b56cbf89eb79809fe8,0x1820a74e8154a87dfa558c53a090d8,-0x6f39e634408a6229f04fc52ed711a,0x1978db70b0719f7281f14bd07ef62,-0x48a6e17b7b428ffa82877a3e4eac,0x9ccbe6ba2b5282711917178499c,-0xf64ba24b4d5aa1481ee19301aa,0x10a9c79976905b7a7163c3e162,-0xb7aab3a0bc40b9edda95e990,0x47485a7ac429db98b8c6b20,-0xcc2b6814b33dc1dff634e,0xbb2bcb59e140a56da86,-0x17f5c52eaf5c00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 15 42 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 42 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 32 indices rho q11 m11 11 19654365366155520000 18=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 32 indices rho q11 m11 11 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r12 : List ℤ := raw_ints% [0x15bb8cdecc3c3d6518000,0x239764b34898e92d3c800,0x1aa6c98ccb21b001ec300,0xc1b6e2635f4fa966e680,0x3bb3f4a3ad968584ea90,0xd38485c66b280a63cc0,0x22bd3727c5c76197908,0x44ddb69a633c897cf8,0x679fe79738e62b131,0x75f3d7622ca452b4,0x64250bfa69f0ab2,0x3d9f2cf476bc68,0x1a0ae649da8e1,0x6c9c2cc49cc,0xd3b0bb5c4]
def m12 : List ℤ := raw_ints% [0x0,0x455a6b7ea4aa45d3c044c8400000,-0x49c11ea7f2d05de12169ee1f13800,0x2522be0be1e0e664cbc3f5e68f8a00,-0xbc551daffee8ca2975550dcaeffd00,0x2a259d610215f81952f3a2a7e9764c0,-0x714488be285d479262cc7c943a6c440,0xed170e084a37e3a2f1847e2232edc30,-0x18be71772f983d83865bd82cbcfc4c70,0x217d42088da6ac985b978926f2bdcb78,-0x251ee08fc4a0719ad07cf90b4f941618,0x21e929c879a96f5c09d71d1707b56e94,-0x199bed6948c76f306253c90b02689dc4,0xffd9338b348aa05d515efba72be182e,-0x83c16f124875b463a8d0b7840e313b6,0x37aa1f85716727baa1228a1b4538eb0,-0x13223ddc7c0734df5b5ca32ad48f700,0x549b37e19ee5d2f04b02ac147b4972,-0x127f2196e18a43d0387d91e734591a,0x3212091b1ba4bb24a2affded4ed84,-0x65d3af994ca67c623e81604b5a94,0x955e69170229294fd82b08d8d72,-0x9542f3b85d703ad481cd15c04a,0x5d80c2d64b633877c4e869748,-0x20589aa6e1a959a663932f78,0x50655e130cfd8ca8599876,-0x3db1e69347b75402f84e,0x64a4d603dad000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 15 44 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 44 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 32 indices rho q12 m12 12 19654365366155520000 18=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 32 indices rho q12 m12 12 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r13 : List ℤ := raw_ints% [-0x32282d88d8a20fe2820000,-0x51fdc2ebcf7e8deceee000,-0x3d445cb6431c452c331c00,-0x1bc3b088d5e983ade07f00,-0x8886f6a5fe7378c56b440,-0x1e21dd9f8c05031e4b530,-0x4ee1979a20ca03d0f4e0,-0x9bad9ddbf0c6713f838,-0xe9071d76ffcd686fb4,-0x1079952fb950d87fab,-0xde21a434144cf168,-0x877137235422e9a,-0x389927b8867b1c,-0xe8b4b122c433,-0x1bd4bbfdd88]
def m13 : List ℤ := raw_ints% [0x0,-0x4e05b8ee793f8e8e384d614800000,0x51d1716d00b0deb97f53f9fa34b800,-0x28977417d05dbdfa633ee8dde782a00,0xcaac48fdfa7245b504bcc4f8324f700,-0x2c9d326210381019776529cac8be8840,0x75d1c0a8df28f8b5138e3b195bb2d3c0,-0xf213afa4896792bf99a9438aed051210,0x18c4e561e45782da6db2be6e3a5f486d0,-0x20d26173aad63c0c6c3a546f7c3114e58,0x2390ba9dc647c976b73afaca44fb27c78,-0x1fb5223a22d833d4d00a1491abe5af60c,0x1752c24ff348f8cec08b71270e64c8cdc,-0xe275233c79373c22f720a09f58c75606,0x710d10473cd478973b681282fd90b06e,-0x2e29e336233af6ea5e419a5f442c6788,0xf48a496c64718560287fc7527c61178,-0x40d3b4f837b40ad84eb585eb6eadbaa,0xd871bb6b1b7e37f22d4412f97d1132,-0x22beba1db95f905cbeedad5ce7976c,0x428c5fac9da82c0f7595d9f07485c,-0x5b16d51b3961901254a996bacbfa,0x53ef593e9122986ab250a8b1a72,-0x2fbee798bf762ef4550b2db130,0xeb2cf2f465fc84317ba6fdc0,-0x1fa7452d646dd42331de97e,0x14502e6b21c4252e75976,-0x1a6434e1459c000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 15 46 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 46 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 32 indices rho q13 m13 13 19654365366155520000 18=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 32 indices rho q13 m13 13 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r14 : List ℤ := raw_ints% [0x6981a193c76ee3a4e040000,0xac31696cb323df521aec000,0x806e75e311da258baa0e800,0x3a13ebf75530d5503b46800,0x11ce440c9b2e0851ecb1680,0x3eb34205124e502fe36b40,0xa39ac6b270eb6a1ccfe10,0x141aa92972637b28f8da0,0x1df5ced8ff5887186720,0x21b6f9e62e390f75004,0x1c3c6a780e8712068d,0x1116e7bebf2dad730,0x713c8d34680926e,0x1cc6df379db90c,0x364d21870475]
def m14 : List ℤ := raw_ints% [0x0,0x57c6700c4867805fff570d71000000,-0x5ad15179b145d6feac9714322e03800,0x2c6c053bb17022d7d5896177d2daca00,-0xda7e72bdbabd82b448e6aa7521a5dd00,0x2f565a2da157e7fe1420f3bda2293acc0,-0x7aea1877307e9e407968e93a62e5b2040,0xf80906c4dddabfbd8a1fcf8c3ca9d7930,-0x18e517bccd258e065b7dd12a7fbe07fd70,0x2050a66fe3ebcd4f1feef7643eb90f0a38,-0x223f9f398eebc12a8bbcf42ff7821c49d8,0x1dcfe828c54e7e521354f43696823d9c94,-0x155e5a02f7ab0c36761a6c7bfcbd7eb9c4,0xc9b7a985366275920260ed5f3acc4b99e,-0x61a61537ac39226ef34825f51a7016466,0x268c69db0486ec0e957b04060d4579cd0,-0xc4b5554d528802fc3300f23ff27cbe20,0x32056c760cf6f1995c14643cf79b0ec2,-0x9f63e9e60aefb080b31c2a9584844aa,0x1844b496f39c0029f5fc823b1401644,-0x2bc0b8040096f591270c985c72ad54,0x37d5df134383895d872739fae0182,-0x2f63ee9a21f5eac55c90ca4b0c1a,0x1871fa90b3c9e194df76d730368,-0x6afc68703f0ab9798e8ff1698,0xc7587e7939d7d6688ee88e6,-0x6ae4a3a92ac200a58327e,0x6e9b0d3e7050000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 15 48 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 48 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 32 indices rho q14 m14 14 19654365366155520000 18=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 32 indices rho q14 m14 14 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x364d21870475,-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r15 : List ℤ := raw_ints% [-0xcddab9c1757d41d68dc28000,-0x14f7d4f31dcdf7e748e0a7800,-0xf9d1f15a05e499a90a751d00,-0x70c2a54dbd3b4552de4cca80,-0x227f2b45e4edf3cea562b570,-0x792d8d9bc5a01a430ad9d30,-0x13b4d2e22b576ede7e734c8,-0x269e83a8d7b016c9b17380,-0x3955e3a17bad597926bf7,-0x403cc3e688b1455066b3,-0x3585693c275d7d759df,-0x2031f0a8c11d5024d2,-0xd3c48aa50a8f5b75,-0x3556eeb516d302b,-0x638d76468265d]
def m15 : List ℤ := raw_ints% [0x0,-0x62bf3e0dd174706bff41ef1f2000000,0x64dd88a5e8f55c135f581b60b1a3b800,-0x30ab811feab725cb707b52dcde8476a00,0xebf52907c03b698657ebc121278519700,-0x3257a6a1e2d5fb09711635b6c63d9be040,0x8098d838dbcf213f407c223cec56abefc0,-0xff0213d216b0bbbb0aa3165a6e41a63710,0x191ec2ca541c3b29fef99a4c1d312d2bfd0,-0x1ff54ec6a2b5be3f7b5a962a08e6d9ad618,0x2124da25bb30af7ddc3353920b12bcfb538,-0x1c2e89b39a6754315606e72baf70621db0c,0x13b1191b45b2489bf85f7347feb8d51cbdc,-0xb4caded464628c30a4d660e46383b882b6,0x54e45795b49d0c511da0e202ce15a0635e,-0x2067b730522a48ab0d3c822d91c448ec28,0x9f4f2e65bad7b8d63aac073c9dbec6f18,-0x26dbdbfb1a39f4e4c527d0dabe7f3b4ba,0x7626c242b516f5abebda44b2ac558b82,-0x110e7aa6a390ebaa5d84f9508d9a122c,0x1ced98c5be82243b19d4993b87e511c,-0x2263c698ee1c8e224737f085375aca,0x1adae4073291010c9dc7982f4fe02,-0xc8b658a861d3381857181925dd0,0x30b635903f92fb5a23e5bd7560,-0x4e6f0f77160000381fe07f2e,0x231e37285d475c65d6fde6,-0x1cf0e0cbfa1c0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 15 50 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 50 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 32 indices rho q15 m15 15 19654365366155520000 18=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 32 indices rho q15 m15 15 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x638d76468265d,0x364d21870475,-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r16 : List ℤ := raw_ints% [0x179668a29d1bbe7221c4f68000,0x26649ee8494bc215ede4f5b800,0x1c8c452ce44d64129c2bd88d00,0xcdd482453bcb37c9ae0db4980,0x3ed9f74d8d9e1198f07ce4a70,0xdc4ea3f648f87e31e15977c0,0x23bd3a2742b65b7f33fbed18,0x45d791fafd43487bbb67d48,0x675a92a0d36cf1573fb38f,0x735c41f08d03864438c34,0x5fb208907fbc5c812208,0x3944f83cfd07704a738,0x17669aa850a3619d3b,0x5d9f593e2153972c,0xad33e865b389c6]
def m16 : List ℤ := raw_ints% [0x0,0x6f1725cf8ba2fe797f2a2d0304000000,-0x7016678777b33e6df64425bf8995f3800,0x35624aa644fa7fafa0cf8ec1ecb83e0a00,-0xff3edbd0a37050282ceb016f04a74bbd00,0x35a8709b0f61093d9eaf8c6c0ac5ea2f4c0,-0x86eaca24779e7bc536e7a31d0f65c399c40,0x1070c6cce30d405058ad93040ae00365ee30,-0x1971ecb39c13db595a43d573095cf1752670,0x1fbe32bddcdacd2bd300dbb5e5957643f6f8,-0x203ae23a53b198090c967a67f8b146de3398,0x1ac7fdbb63a653e061441d25b4ad0b11be94,-0x123feb26f3284ac2acd64e2c06190e62d9c4,0xa303dcfb698300b3cbb9fafbfba48d3448e,-0x4a446f28331bfc7f61af676ee1c035b9096,0x1b6b00ed2415447cc4996a5259cdd3323f0,-0x81defc5bf7353300a67ff80bec2541a640,0x1e628e53ffd6cd28c713109914265db892,-0x582335ada2f11c235f2e42ced43a07eba,0xc0f20dbe263f8235bf893fd3b868e904,-0x133a657ce5c4c4dd6be319e067f81a14,0x15466bc0f2adf886685d4c569a6c812,-0xf44bcfbc037e1b654ddd8a539d06a,0x673437e73db0f9d16388ec97b088,-0x163165c0aba4f853f42ff3b76b8,0x1ed86b01ac063266f00567ad6,-0xb867425dd1079b9eb8c42e,0x790a35597ed00000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 15 52 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 52 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 32 indices rho q16 m16 16 19654365366155520000 18=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 32 indices rho q16 m16 16 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [0xad33e865b389c6,-0x638d76468265d,0x364d21870475,-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r17 : List ℤ := raw_ints% [-0x2909b1e01fc6c678d7b85530000,-0x42b8b2a29962ef3686ddd751000,-0x318c6a24410c35bacc12caebe00,-0x164b904a17208af58edf1cde600,-0x6cbf23aa0b83fb3b3bd35484a0,-0x17c75a07f7fe86b6ea8c9d7330,-0x3d963f5a94e1252defae0d7b0,-0x780ee77dc661be1a243e36c8,-0xb12a0a9e706465ce026741a,-0xc51ac3405cdb679c3a099b,-0xa2e481d3794b32377d7d6,-0x610f2beaba88fa095f4a,-0x2774fa93e53590b032e,-0x9ce8a153711b79603,-0x12031b8b6b643572]
def m17 : List ℤ := raw_ints% [0x0,-0x7cfa0a897d175e48af0f72a3648000000,0x7ca035220562d08162bdc1d968a252b800,-0x3a9e41655df6f2cb9b529f3c33d8b1eaa00,0x1148f7352e23e4098954998d451567d23700,-0x3950eeee71d4c13c613a1656bdd691da3840,0x8dee60835057c6c958a71b83ce1ffbbdabc0,-0x110385c5d4a58772f8163ba2f866760fcd410,0x19dee460651b5d2c5a2c5a8eb01d1756b50d0,-0x1fa9b2e55101f08c3d01880d63bab6875f3d8,0x1f7d2990ed9ebd86828afe1f4b738685fabf8,-0x1994ca17855c07149b449eb71da352e6e040c,0x1101c0416c4ddc45a0c175e90350efb64cedc,-0x93d95bfcf7cfe174e52d7cc9069f64dfbae6,0x415f0a803ac450903073d358477e2d599bce,-0x17584919b70c81ea638ab3b94495607205c8,0x6a8c5f143b0de141903fe61d3e5c44299b8,-0x17e8b5cf030ebf2659a9eb17c989e10a84a,0x4225d8c65fad205fcabd9ba0a167423252,-0x892f407f3e032169a1e1efa7d3052eeec,0xcd832446ca0ccd751d20d680203efbdc,-0xd37392d6504bf8839e54c6be40c4a1a,0x8b4f05e5ab8749b54a58a482b14012,-0x35280f4ba4ccb281ed36ad084c770,0xa1d8f9b75c98a67c4576779d200,-0xc1fac02d21723db019122885e,0x3c74a383eb74758f3e7c3d6,-0x1f9bc8eeccdc00000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 15 54 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 54 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 32 indices rho q17 m17 17 19654365366155520000 18=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 32 indices rho q17 m17 17 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [-0x12031b8b6b643572,0xad33e865b389c6,-0x638d76468265d,0x364d21870475,-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r18 : List ℤ := raw_ints% [0x44488e4170a98f090836a9090000,0x6ee823d991beec974b9760e2b000,0x524455694737c437d2aed2697200,0x24f82144ac82972ecd873123ab00,0xb40e0eab2f85faf7d033df93a60,0x274e2458b5460be8b4385731240,0x659b73d3394d250e5480c31820,0xc5a573dc81c34239bb60c3df0,0x122f048fe468488f6908c30be,0x142c5aa4f4e7164d6d50f044,0x109e250ff01c56a4adb0963,0x9dd59723c239671313480,0x3fe28a86f265a6a7a608,0xfcc2ddb3aaa468312c,0x1cd76aba525dedc77]
def m18 : List ℤ := raw_ints% [0x0,0x8c994bdaacba4a11c4f160f7d110000000,-0x8aa3ac7a7eb3e77b97a1a2eca26dd7e3800,0x406ef044ccbaad260d8ca3afe475cb094a00,-0x12c20f8f5ffe08d592d9d73fc253c7f159d00,0x3d5a50421330e587dba515d40b2fb9ff53cc0,-0x95b3e108f4d1eb560a634ce46446c05003840,0x11a990aa05b4b95bcfdb78620d9fa9f938fb30,-0x1a663fbb3b62b80a069ac7a9dd09b74442c770,0x1fb6a9c162067bb2e7a986ed38575de76001b8,-0x1ee7f717a54878116ad81953ed6876a294c358,0x188ebc3187317404e16ed94d3795bb5d6ef494,-0xfef27323a46ab00339805c35a2b2a2120adc4,0x86dc81fb709153a884e0a9ce5aef8756f44fe,-0x39e273940a270e008a446bb67a68d2d440446,0x13ffb051064c64f35e404826accc03640ec10,-0x57f453f2ea102b74dd8d0ca2b9c3ae2a0760,0x12ed87e9e8ef2427273329227ac88b144ae2,-0x31ef0ca00ac5d0ce2fbd29a7a7464d06b4a,0x620ff12224b6e8b090f6541d1b2a6ff5c4,-0x89ed73032fdc128155c3514e457a2e0d4,0x83d8b0785c2f766bebba03f9d3153522,-0x4fa6df599c107359e274fd314c3813a,0x1b6b12f9778b1b6e6e06bb1746e6a8,-0x49ca0fabca9a6f4a302388d787d8,0x4c325f6821f1644fd05ede9a46,-0x13ccce0245964fafc46cf95e,0x83f24e55065000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 15 56 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 56 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 32 indices rho q18 m18 18 19654365366155520000 18=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 32 indices rho q18 m18 18 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [0x1cd76aba525dedc77,-0x12031b8b6b643572,0xad33e865b389c6,-0x638d76468265d,0x364d21870475,-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r19 : List ℤ := raw_ints% [-0x6d5649c51d53572653ccbd2938000,-0xb16d04ed0a889434d39912890a800,-0x83792ed8e624097652787a102bf00,-0x3b0355acf4dbd4fb28cf1488d7180,-0x11f09e090f0af6963dc43884c65d0,-0x3e90e903518c6756029dca3d5730,-0xa1773d237157afedd4b77964b98,-0x1397bb52c09b4a3e94e69ad4c10,-0x1cc73a6adb9ec91f37ace22c5d,-0x1fd9251975fb69c62d46bc563,-0x1a2938e2f05c02114c3fb58d,-0xf7abf372cea0c7f4d87602,-0x63df9668dfda139b93507,-0x1897070fbe661cd336bb,-0x2caa9eedc6c43be787]
def m19 : List ℤ := raw_ints% [0x0,-0x9e2c755602519353fd8f8d16cb320000000,0x9a4e89c94ab96d23b3aac2afc43e4161b800,-0x46e5c1dd2329133475fae3bacdc8a779dea00,0x1463454fcd03925a8c067fc9608ac45eced700,-0x41ced819b33e90f36c29fee852df1a85499040,0x9e4d9624678dece979bc6bfc7652681cf707c0,-0x12644b02968fa7cb1ee125aee69b5a7ce8fa910,0x1b08db4123c3a54c17f6b46752fd2aa383d79d0,-0x1fe460b0fd1b4addaf019be56207366f2d29798,0x1e7847b043afbb24c1f9c69c7ca883db82810b8,-0x17b0b00a953861c063f4faaaeee541c1577910c,0xf01fd6def76549e0e780e4f2077c365aec95dc,-0x7bb35a3721741c7415c390555653846400ea96,0x338dace80b876dc5ed6890b7e02cf3797735be,-0x113c03c754042c6e7e3177cd6efa207cbbbc68,0x490a47e694f05a31f9f77b8e0a697cae7b958,-0xf128c9a2f7b4fd5c1a7b341b301e260f5a5a,0x25e795d5711a6bf5a37d5a789e1a5d2659a2,-0x46744c92a18f3756e29a539a7473e9f3dac,0x5cf9bcf77c5294133926ddfbe31684f89c,-0x527ef1e6bd5a46788b1d4aa79b8f68dea,0x2da67cedf2daa4ffab64b846fd2324a2,-0xe28ce94f0ee5cad44ebc65b56c7610,0x21a563dd303d45d28e1e32aa27ba0,-0x1de947abcf7a6c358d7ce6e110e,0x67a78cd25bb8e7c88db40746,-0x2264ed49bddc000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 15 58 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 58 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 32 indices rho q19 m19 19 19654365366155520000 18=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 32 indices rho q19 m19 19 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [-0x2caa9eedc6c43be787,0x1cd76aba525dedc77,-0x12031b8b6b643572,0xad33e865b389c6,-0x638d76468265d,0x364d21870475,-0x1bd4bbfdd88,0xd3b0bb5c4,-0x5bb94b33,0x23571f3,-0xbab5e,0x31c2,-0x99,0x1]
def r20 : List ℤ := raw_ints% [0xa9544480209b2c7c4c8257969b8000,0x1128da9cd3be51e2e46c6ddfee7a800,0xcb41e0c88cb141853635112c445700,0x5b237e26b09da7017729040feb2c80,0x1bac6483edde76565ebd7f6930ca50,0x606230f4516086f2a5731a4396ac0,0xf85dad848a49cf323dd7d01fed28,0x1e16168edc1f3fb02f0b3b941d98,0x2c1b4d50c47e554db2fb4854ced,0x30b4a3d4a2df761769b28c7934,0x27e8c13202a5a501490521cde,0x178c313da1a30e05ac3b4b08,0x977005ab8b0707d2f7c595,0x2525903fe8f3c5681a00c,0x432f15f82b65dc90348]
def m20 : List ℤ := raw_ints% [0x0,0xb1f20400c29bc5be7d417eb9a49840000000,-0xabd4293de802940c5dc65521a320e2f7d3800,0x4e163b534dd49db3dde2b680631221a97c8a00,-0x16312238db23d314c339db2f84ae0c578537d00,0x46b9ff7cded88343fe2a6d25a045aabd7ea84c0,-0xa7d006ee764442e3f3c25aaa4efe62ccbcff440,0x13354d37f876f8aa9c805906107e609ff5346030,-0x1bc7dac5b89e7f315e310352858975be57b6a070,0x2032878f49c5c7b0518dd5ac7ef905e47dfbda78,-0x1e2bb568d4a0ad03726fcb48e1158f144452e918,0x16f6629b19324ce0a07815df7e6ac008a3edde94,-0xe352ff82f9d7befd87c4d5b03e48b3c49f815c4,0x72148bc3e4bd36e79c738e1d320f8e16ced16ee,-0x2e2cbcea4200037f2d6c0487d2348aad0ab2b76,0xef02f8ae2a268eaf80e2c3f2363f78ad611d30,-0x3d01bdc92686860f9ddc17b7023c676e340980,0xc12015e37b2622b526b84c5fc12b3bebab9b2,-0x1ced5fb4d21748fbe12bcc4fc6acc71af4e5a,0x32dd1eb5a1742658ab0c9dec7a2225118c84,-0x3eee78e35f5820795eafcdc8d5333b91194,0x33c821288ddf8e84de427ddeae0ed74cb2,-0x1a37e981119a2f93e13f570913c11d28a,0x751c8a0f31da12ae7f0a35bebc34dc8,-0xf577d2080f3a9c96fe68e95cef1f8,0xbbbd797bb3a48f011391e3a6336,-0x21e1f4d3e2446d5a4d9c9fe0e,0x8f53583106d0000000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 15 60 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 60 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 32 indices rho q20 m20 20 19654365366155520000 18=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 32 indices rho q20 m20 20 19654365366155520000 18 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_20
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<21) : intPolyRF (mz e)=rfPoly (C (19654365366155520000:ℚ))*rfX^18*(1-rfX)^13*momentRF (key size) (X^e) := by
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
  · exact moment_source_19 size
  · exact moment_source_20 size
#print axioms moment_source_20
end
end CatalanCore.Li2.NVMod.FamilySource.V4C19
