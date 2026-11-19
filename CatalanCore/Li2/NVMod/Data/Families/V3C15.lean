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
namespace CatalanCore.Li2.NVMod.FamilySource.V3C15
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,3,15,size⟩
def bases : List ℕ := [0,1,2]
def indices : List ℕ := [3,4,5,6,7,8,9,10,11,12,13,14]
def num : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def den : List ℤ := raw_ints% [0xa261d9400,0x11c6c2e480,0xde9fbcd00,0x671d89d78,0x1f8505264,0x6b4e63e2,0x1050a9d3,0x1c9adba,0x23e86f,0x1f806,0x1259,0x66,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x5,-0x5,0x23,-0x62,0x93,-0x1e,0x717,-0x25d,0x4fe1,-0x49f]
def rhoDenominators : List ℤ := raw_ints% [0x10eb40,0x189c,0x3f0,0x54,0x60,0x4b,0x32,0x7,0x1c0,0xfc,0x6270,0x26ac]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-3) 0:ℚ)/(rhoDenominators.getD (m-3) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 3
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 3 15
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤14))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤14 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1]
def omegaDens3 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9]
def omega3 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums3 omegaDens3
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_3 : padCoefficients 15 omega3=padCoefficients 15 (omegaCoefficients 14 3) := by decide +kernel
theorem omega_spec_3 : coefficientsPoly omega3=omegaNumerator 14 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_3
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
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
  change m∈Finset.Ico 3 15 at hb
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x5c986bdca400,0x5fb9a7abc5a00,-0x2ea0b9f8e3e140,0xe37e652afc6380,-0x30a964641fbe1c0,0x7c0e56a5c213b80,-0xf42554f5ba1da8c,0x17b489cc88c34b28,-0x1d794822eced5920,0x1d8eb47d21f92fc8,-0x17fa2d17899e3b37,0xfb6075a9273ca4e,-0x844579f68c2b86f,0x374a0438ef61bb8,-0x120c42d8d2a9e2a,0x47bdc938052d3c,-0xd0c59f20b5486,0x1a27b283bd4d0,-0x20929351dfd3,0x149ab25d9fe,-0x3e532d52b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 12 21 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 21 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 25 indices rho q0 m0 0 852000145920000 14=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 25 indices rho q0 m0 0 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m1 : List ℤ := raw_ints% [0x0,0x51055e610f800,-0x514da65737d100,0x2664eafc02fd240,-0xb55c0e3773edec0,0x2580a1f3e16a82e0,-0x5c45b7ba97116f40,0xaeef8e401d22f224,-0x10540ea82126a52c8,0x13786688968c597e8,-0x12acd4d8c64005d48,0xe71a8f58730c5465,-0x8fd87bc05828760a,0x4794fb545a3f2515,-0x1c25485cf1e53dc8,0x895b0f5f8e4e5be,-0x1f9d0403e0d5b44,0x5441498701b1aa,-0x9832411913720,0xa6a50c08e479,-0x58cd306ccba,0xce1d71579]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 12 22 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 22 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 25 indices rho q1 m1 1 852000145920000 14=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 25 indices rho q1 m1 1 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x46e4b294ed9000,0x45250b7f0fb0f00,-0x1fb291059041c140,0x9126c4efff0ae6c0,-0x1d0de9cd73affed40,0x451521add0f6e8980,-0x7e549adee5d44fcac,0xb598926a3bcf506f8,-0xcfec93b3b1afef000,0xbef7a07e6e9929788,-0x8cf9c4dc9e07efddf,0x536f038432ecfe3ee,-0x274c53c951bb592f7,0xe8b38dca84cd5e78,-0x4257211beb5bb61a,0xe24a3089faf588c,-0x227e9025da90836,0x380c849a7a88d0,-0x35c4611ffb51b,0x17fc05f6c47e,-0x2a6a0dd693]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 12 23 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 23 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 25 indices rho q2 m2 2 852000145920000 14=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 25 indices rho q2 m2 2 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x3e081c424fde000,-0x3ae14f2468cbff00,0x1a3c7c30a73988840,-0x749ed7a017ba69840,0x169ff715c396b9c9e0,-0x340d2961595d70fdc0,0x5bed10343c6ae1b804,-0x7f5767fc54bb4ed7e8,0x8c29d9eb73aa75be28,-0x7b67042a4a933ba0a8,0x57097b334bdb11f0bd,-0x3105a54357eb2086ba,0x15dedc93e36bf242ad,-0x79f4b5442a393e848,0x2080cdeec99313cce,-0x66ab4e1a684bdd84,0xe4ef66e6fba235a,-0x14df32370903140,0x117a6a8d241331,-0x67cb3ee686aa,0x8b1529c2f1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 12 24 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 24 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 25 indices rho q3 m3 3 852000145920000 14=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 25 indices rho q3 m3 3 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x364718ba05e24000,0x3233df611bb073b00,-0x15c54b5cf8123e7b40,0x5e0cf88befa9eae9c0,-0x11b4d0b4ce38939b840,0x27767bb4039e9da1480,-0x4362e54e7cc27f5344c,0x5a0f45d698d19cfdc78,-0x5f658d9f1c4abdaa940,0x5097d376c444ed14608,-0x365bfc0e346589a0167,0x1d2923784332cd1107e,-0xc5493698ce7e805c7f,0x40c6644ba7b7572d38,-0x1023d8096f8f74574a,0x2f314e59f1023eb6c,-0x601ad5f93c150046,0x7d961a670348a10,-0x5b771ddea9d2c3,0x1c15b3b3b470e,-0x1c660b17cbb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 12 25 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 25 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 25 indices rho q4 m4 4 852000145920000 14=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 25 indices rho q4 m4 4 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4,0xc,0xd,0x6,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x2f7e35a2c525f8000,-0x2adb5aaffc38bbef00,0x121c108de98fd002240,-0x4c20a7350a922797c40,0xdecaccfc981f88a3de0,-0x1e1979961943e19473c0,0x31c08ae49009f768ece4,-0x403849cad244144b0228,0x41885575b233e92df7a8,-0x352ce877b5252b505c68,0x225411bdf0af5ab8ead5,-0x118d5082bb8595b4206a,0x709bbf15202ee6de605,-0x22d77a4e08173dd4408,0x81dc01da5a0396fd5e,-0x15f4bcc06efe2615e4,0x28c8d490b189670ca,-0x2fa318aaba52f440,0x1e0fec82b3709a9,-0x798b8d4e7d5da,0x5c75a4b74a9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 12 26 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 26 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 25 indices rho q5 m5 5 852000145920000 14=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 25 indices rho q5 m5 5 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [0x1]
def r6 : List ℤ := raw_ints% [-0xa261d9400,-0x11c6c2e480,-0xde9fbcd00,-0x671d89d78,-0x1f8505264,-0x6b4e63e2,-0x1050a9d3,-0x1c9adba,-0x23e86b,-0x1f7fa,-0x124c,-0x60]
def m6 : List ℤ := raw_ints% [0x0,-0x298e6eee6c81390000,0x24a14839eff04ae4300,-0xf19b19c1824a8cffd40,0x3dd727b8d772511d37c0,-0xb0096d3bd6acef212940,0x1717ad7c10a8c4fc15a80,-0x24fcfe759fc5b32cfceec,0x2e29246f686ea86c3e5b8,-0x2d6c1c824324db0990400,0x236eb89cc8f9e1b8ece48,-0x15e91c1b7c01bc122b2af,0xaaf4361f5a32d1bb4c0e,-0x41090e3ead72075f84c7,0x12f76b6a241b8e5ec678,-0x4213f11a2c0e4c830fa,0xa546ab490ef015200c,-0x117aa781b8fe6aff56,0x123498a6bb9c54410,-0x9eb115d0896c32b,0x20d8bd9461a61e,-0x12c1355681a3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 12 28 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 28 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 25 indices rho q6 m6 6 852000145920000 14=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 25 indices rho q6 m6 6 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [-0x60,0x1]
def r7 : List ℤ := raw_ints% [0x3ce4b178000,0x6a062f81c00,0x525f7a9fb80,0x25cc73f4000,0xb6ac464808,0x264515225c,0x5b2f14b3e,0x9b507bed,0xbad7be6,0x9919d5,0x4e966,0x13f4]
def m7 : List ℤ := raw_ints% [0x0,0x245ca1109ef111e0000,-0x1f583768a79528c52700,0xc9edae30d78d4a775c40,-0x3268c9d9958dd11c0ca40,0x8bbbb93a9cdcb1bf13de0,-0x11d1486e98b3377428ebc0,0x1baf38fc52fc56928da2c4,-0x216fe4af3dee4c172e8ee8,0x1fc1c600a4935409414028,-0x17d5c940eaa6e48e10dca8,0xe20e7ecf84ba5e6320e2d,-0x6932c44dc97b01f1d639a,0x25fbc6960525261fca49d,-0xa7137ada78943929e4c8,0x21ff848949eb07eb796e,-0x4e910d9a29d23ec49c4,0x78ed4605b1aa9e4dba,-0x700aaea9ed744bfc0,0x3481546773841261,-0x8dd74466f8d78a,0x3cb08ccd68a1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 12 30 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 30 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 25 indices rho q7 m7 7 852000145920000 14=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 25 indices rho q7 m7 7 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [0x13f4,-0x60,0x1]
def r8 : List ℤ := raw_ints% [-0xca80862d1000,-0x15ee39d9fca00,-0x10f00513e4800,-0x7b719e7c02e0,-0x24f1db6cb350,-0x7a66bdab160,-0x11f446763c0,-0x1df92d180a,-0x231294adf,-0x1b9b5bd2,-0xd4fdff,-0x309d2]
def m8 : List ℤ := raw_ints% [0x0,-0x1fd10cee8b12efa40000,0x1ada34276a36df8e77b00,-0xa92634e94273f1638af40,0x293adbd64835ff2a9861c0,-0x6f6955e147b5e5e05ae240,0xdd2c7dfb058c1ae3a11c80,-0x14db37fcefc137d9e603c8c,0x1866f903859c9894b6283f8,-0x1663a47cc70017661d1b4c0,0x102e62d2289b62055337388,-0x93358da37f61921cfa5fb7,0x4168dbec571b41e0e5e51e,-0x166c247dfb59ad974f9acf,0x5cfa86c052bf0ba11f7b8,-0x11ace8287e542a804192a,0x25b4c6b1f1568d2c1aac,-0x34b52c6d9c620bcd9e6,0x2b556afb6996c33110,-0x11683eb8b9eaeb653,0x2638db674935cae,-0xc3dad90e4f4b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 12 32 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 32 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 25 indices rho q8 m8 8 852000145920000 14=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 25 indices rho q8 m8 8 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [-0x309d2,0x13f4,-0x60,0x1]
def r9 : List ℤ := raw_ints% [0x1ed6030a776800,0x35385a0d3ae100,0x28e7b394236000,0x1285d388641c70,0x580d7dd791728,0x12117180a2e14,0x29ebc9c208b6,0x44f5352a8d4,0x4f20c07a04,0x3ca3e600d,0x1c23d230,0x60ebad]
def m9 : List ℤ := raw_ints% [0x0,0x1bd6eb50b9b091af80000,-0x1707809e1c188e44403f00,0x8e0089e7b5e617611ee640,-0x21d51540f37caf2dc821040,0x5936d7055d784900dcf65e0,-0xac82d1eae5004e515741bc0,0xfcfcf60d52e77d40480d1a4,-0x11f01be70214f8a7832b47a8,0xfe9b6d12be2b290ed68f6a8,-0xb1528d6f54de3b99aa130e8,0x60c6a754f6eb3b6f05f5cc5,-0x29139a4a8014def0769294a,0xd5f45c8b8f92fae1173a75,-0x34459cb9080fdfbb2c2388,0x94782d402502979bcc8fe,-0x124189d7d646584fb28a4,0x1723589427674ba90d2a,-0x10d66c8ef2a4b777d40,0x5c75d42eb1324f359,-0xa483190a6bd0bba,0x2767367f66cd9]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 12 34 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 34 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 25 indices rho q9 m9 9 852000145920000 14=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 25 indices rho q9 m9 9 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r10 : List ℤ := raw_ints% [-0x3d7a2f068d90400,-0x69c108adefe8280,-0x50f5544171da800,-0x247b86440cc3218,-0xac6891e7055d24,-0x231f5710f0de92,-0x50c2da97d4683,-0x835ab3c21bfc,-0x948e4ef4f2f,-0x6fb181a40a,-0x32805b918,-0xa7a14be]
def m10 : List ℤ := raw_ints% [0x0,-0x185c0de6a27a7f79900000,0x13c587f6c9e66d23e353300,-0x777706f0c8f684129f5b140,0x1bd99772bd465115e35d2bc0,-0x47bd15cb007b90e6cd91ab40,0x87407d5de4191b73ddeaae80,-0xc0f9189b40da46248b85652c,0xd47587a17541ffb063a64c38,-0xb661444078ee7de26ca29d80,0x7a7db487adb9671d02c5d6c8,-0x40344d9f37dba9526386b27f,0x1a0b0b8fcfd52e455e6cadae,-0x80d89d8610c4b5fdbc56497,0x1dabe3ac9c23c60e5ed9ef8,-0x4ea8adbdaf47fbccf933da,0x8e9200995ac651ee25c4c,-0xa38d8d8058524711d5f6,0x691490de7bfca478e10,-0x1eb7cb27b4904ac63b,0x2c2ca40756455ebe,-0x7e8989cd17fb3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 12 36 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 36 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 25 indices rho q10 m10 10 852000145920000 14=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 25 indices rho q10 m10 10 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0xa7a14be,0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r11 : List ℤ := raw_ints% [0x6a5424632183d800,0xb66623963aa69300,0x8b2a681227e7a380,0x3e75e7cb0f249710,0x125be9f77ce8c420,0x3b7d3624aaa6c98,0x87cf0e84bfa808,0xdaedd7a683189,0xf4d94ff31266,0xb57b2c33d45,0x508864ee04,0x1049e8a9c]
def m11 : List ℤ := raw_ints% [0x0,0x15508c29ce2b2f8a5e00000,-0x10fe00000cbb630809ef9700,0x64b5ef8d4c3ee9ed00f20040,-0x16fedc9b8c25cfa0c86248640,0x39eb798e7f22e80d3c7cd25e0,-0x6a924fba1aa8a1070f9f01bc0,0x9411814e1bd004ce729787184,-0x9e580b95e9e5b495d47422268,0x83a242d805c4ddfc3a52db728,-0x5550ac32223e6ca7a86c9f728,0x2af8b8048f56ca60c2a499c9d,-0x10a9f11f23d055fa312ff617a,0x4e5179841a2de018af3dc58d,-0x10ff3e53b64b6a43f74cf448,0x2a07d795c275e59d249400e,-0x461adbb5a02a30e3420884,0x48a976d727cee0b80071a,-0x291d813ff73fdd4f42c0,0xa355981784a9907a91,-0xbd6eade6ec1ade6a,0x19574670e25f51]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 12 38 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 38 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 25 indices rho q11 m11 11 852000145920000 14=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 25 indices rho q11 m11 11 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x1049e8a9c,-0xa7a14be,0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r12 : List ℤ := raw_ints% [-0xa54ff0f4c83ce3000,-0x11ae8c17f2136c6600,-0xd73db8aa29d4c5900,-0x6047358d90d0b01a0,-0x1c2f3fe83f7ef85e0,-0x5ae227f5562fed98,-0xce433b63e42cdfc,-0x14a20d36a987950,-0x16df702747481b,-0x10c44eca74d42,-0x7560e19eaf7,-0x174ec64c24]
def m12 : List ℤ := raw_ints% [0x0,-0x12a67aa49465c99912400000,0xe9e3156a1f265860d272ab00,-0x55117db8891f489c2c4da0340,0x130b19d27454d561fb073a25c0,-0x2ef2268812a1ab3786d9cee440,0x54613f4552a9b7511a289be080,-0x7243e92ddf8383bf56c65bb0cc,0x76c9f47a86887248fe7ac4a278,-0x5fb4811941b14f533d09237640,0x3be5c14f32a2e3c62b94b60c08,-0x1d016f94ca77c38a3f09afad07,0xac1bd59a4473e61d0cb5121be,-0x3007c79a74adc2f3b4cd8d41f,0x9d237c0bb460dbfcea78c438,-0x16a3728ae5f786aa78c6ed0a,0x22b4c03cd02eff5b784b0ec,-0x2070ea34d126b8a359df86,0x1020b09226b2a87328f10,-0x3646b0edf2dd4a9dce3,0x32ad337812651104e,-0x51078d64da5cdb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 12 40 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 40 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 25 indices rho q12 m12 12 852000145920000 14=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 25 indices rho q12 m12 12 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0x174ec64c24,0x1049e8a9c,-0xa7a14be,0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r13 : List ℤ := raw_ints% [0xec8c21ceb69c18d000,0x193fed7de11066ff200,0x1329f2527b022d86e00,0x88c248935e0eb96be0,0x27e5f32b5be80e4470,0x8021bfbc481899de8,0x1216250fb8ac49814,0x1cc73d72eb88d82c,0x1facdc7db4f2a4c,0x170432174560bd,0x9f5f67a3b342,0x1f354e86b61]
def m13 : List ℤ := raw_ints% [0x0,0x1051ab5001d91065eff800000,-0xc965f42283bd2ea7f21c2af00,0x47fdfe27e8af580a2616f22a40,-0xfd0b860c04930524e542ea8c40,0x2631e5b335fe57c3d5fcb093de0,-0x431f474a94bc5e0b1dfc2954bc0,0x58ab3d1016d9ef84e05cafa3a64,-0x59aeac2d914d979ffce5d80e728,0x4613c5723c144c2a59594a151a8,-0x2a60ad0a78d76bfe836059e7768,0x13bd52794dabebc914c1e79d3b5,-0x700b4a687f3b4679fd7e9cc82a,0x1db4ff79b2d999be0f3bdffbe5,-0x5b8b1918761844e1de28d1708,0xc48d584282b11605b224429e,-0x1149a23dace121ea7e9e1964,0xe8bcc8d46cbf281c7e078a,-0x656ab4e24ba81ae8f4840,0x12077e5802a2fd158609,-0xd882bb27f7c551b9a,0x10297a32de5ae09]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 12 42 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 42 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 25 indices rho q13 m13 13 852000145920000 14=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 25 indices rho q13 m13 13 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x1f354e86b61,-0x174ec64c24,0x1049e8a9c,-0xa7a14be,0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r14 : List ℤ := raw_ints% [-0x13cba95ffd24ee111400,-0x21bfc71d1f323d414480,-0x198fb4613a76a8a7bb00,-0xb5f6d4abd389ecc6478,-0x34ee98c3cea14c59804,-0xa96770aafd31350a32,-0x17d088522f8739ec0b,-0x25b531d18e6d2f966,-0x2942bbc834d09ee3,-0x1dc4d15b58a51fa,-0xcc55ec514c5fc,-0x27946cf71564]
def m14 : List ℤ := raw_ints% [0x0,-0xe4775e6019dee5931f9000000,0xad949ac0cc29fbe692f202e300,-0x3d098b3d5f4b1cceec4788c2540,0xd2ba1eb09bcab98d203f2a60fc0,-0x1f303793cce057106a068f944d40,0x35a2b956674b5475fb84af907280,-0x452d0027fe1e6030f2f5274f476c,0x441ff4a0388ad3e40a7138dde6b8,-0x33aa2c7c1bb53aa77437ea79cf00,0x1e34de254d9841e080ce5b1d7348,-0xd8a45492835565270ef2987e14f,0x4989bdb2b2cc4ffdddea0bc854e,-0x128612f598a66199521180fbb67,0x35be919a375ef2c85770be1778,-0x6b65d00bf5b7bb035e48370ba,0x8a8d008a576d9ec03b19108c,-0x68be42e8d382cdc9d945a96,0x27eafc44ae91964e9ec410,-0x5fc3cb8a90b2b229944b,0x39b5a83458a746b55e,-0x337bd40e1eb60c3]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 12 44 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 44 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 25 indices rho q14 m14 14 852000145920000 14=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 25 indices rho q14 m14 14 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x27946cf71564,0x1f354e86b61,-0x174ec64c24,0x1049e8a9c,-0xa7a14be,0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r15 : List ℤ := raw_ints% [0x191b0dc85aa111cb1d000,0x2abca811e178b2a4eae00,0x204f6c6d48add9bebcf80,0xe584db16db3323a89fe0,0x4299345ac2fca5d1fe98,0xd483ea9937afb18f644,0x1dc58026ed4aad09b3a,0x2ef24a425fcd44329d,0x331e774ca305decf6,0x24aa6838cb16c175,0xf9e52d8bdd25ca,0x2ffc4a55dbfdc]
def m15 : List ℤ := raw_ints% [0x0,0xc7e8729416a308e0bb9e000000,-0x95bc4994cede59e9b1d85e58700,0x33d70e939b79b06b9644669de440,-0xaff2c620dd64fa99f19e54852240,0x198e7351c6e6d0600d3e045adade0,-0x2b0bc6a28261a27d2ec0e542b2bc0,0x363f86b8e68eafbb2eef155062444,-0x340ec76d43df93d2cb2992bcea5e8,0x2657ef9fb1395df5ebf06968be628,-0x15afcfb07ec03de573850099da1a8,0x95bdab18be56a06adb98d423180d,-0x30a519d4e877b9751df55a4e695a,0xba3eff2b91aa6344afbad5a037d,-0x1fc8e348c15520dec92a392fbc8,0x3b0fc37bb790c53f46d58554ae,-0x45c03754dd47c4d4bb758b344,0x2f4a031086fe5e5ce2044a7a,-0xfba7c2d8ce010cd468cdc0,0x1fc45ee33265da0bb03c1,-0xf5aefb9bd5df0f2f4a,0xa3b74fbbd14d701]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 12 46 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 46 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 25 indices rho q15 m15 15 852000145920000 14=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 25 indices rho q15 m15 15 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0x2ffc4a55dbfdc,-0x27946cf71564,0x1f354e86b61,-0x174ec64c24,0x1049e8a9c,-0xa7a14be,0x60ebad,-0x309d2,0x13f4,-0x60,0x1]
def r16 : List ℤ := raw_ints% [-0x1e6ffe5b59d44b96d73000,-0x33be78b6eaec949dc60e00,-0x270eef0bc5959741087e00,-0x114f148c8b5aac64500ba0,-0x502f72f06499a912aca10,-0xff39163ca652012b75a0,-0x23a5f671960de9946810,-0x380470e7e2755b0769e,-0x3cbeaf759217555dc7,-0x2b5b5af62418db232,-0x125c56c549fe6a07,-0x38032c577d4bde]
def m16 : List ℤ := raw_ints% [0x0,-0xaeeb644193cea7c4a42a4000000,0x814616260bf15ea46fa51127db00,-0x2c1a4454c42fa586a89091f049740,0x9347f6dccab23ec023b9ad54869c0,-0x1503232ae963984d829452cf912640,0x22b14e2692506b26a215cf6047e480,-0x2ac14e03fc48fa810295b2da19110c,0x28026a1adee6fac758043b8ca4e8f8,-0x1ca3eac0fae162fc9d7731e82697c0,0xfadd275211fab62129cb9068a1c88,-0x6843d01768a2852a0a777d41a5157,0x206bf8a77535edeec2808245a9c5e,-0x75e89788e5a46557e7ab743d1c6f,0x12ed92a1b4c0a719f44fd80c68b8,-0x20ac8f46f7b270fe2dfdaef8aea,0x234621856ec0770fa1557be32c,-0x15683f1e3de5f216a5122eb26,0x633a372afc7886c2a502d10,-0xa873b34c3688ae196b673,0x4142a34d75a100d71ee,-0x207c2537a921b56b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 12 48 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 48 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 25 indices rho q16 m16 16 852000145920000 14=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 25 indices rho q16 m16 16 852000145920000 14 10
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_16
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<17) : intPolyRF (mz e)=rfPoly (C (852000145920000:ℚ))*rfX^14*(1-rfX)^10*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V3C15
