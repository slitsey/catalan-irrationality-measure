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
namespace CatalanCore.Li2.NVMod.FamilySource.V4C15
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,4,15,size⟩
def bases : List ℕ := [0,1,2,3]
def indices : List ℕ := [4,5,6,7,8,9,10,11,12,13,14]
def num : List ℤ := raw_ints% [0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def den : List ℤ := raw_ints% [0x36209dc00,0x4cc3dad80,0x309ea0a80,0x122a4dba8,0x47392794,0xc07141a,0x16ddc93,0x1e9b0d,0x1c476,0x1130,0x63,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x5,0x2d,-0x46,0x1ea,-0x3e04,0x5be,-0x38b8,0xbf6d,-0x18f65,0x22f27]
def rhoDenominators : List ℤ := raw_ints% [0x189c,0x7e,0x1c,0x3,0x3,0x19,0x1,0x7,0x1c,0x7e,0x384]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-4) 0:ℚ)/(rhoDenominators.getD (m-4) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 4
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 4 15
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
def m0 : List ℤ := raw_ints% [0x0,0x5c986bdca40,-0x5bbd3745c8b0,0x2ac1e6beb81f0,-0xc74246543c4fc,0x28a231380a6e2c,-0x628c0399d35b78,0xb811019d4114d8,-0x10eaad167f5b3db,0x13d972437ddcba7,-0x12b88b7fb46e9ee,0xe39d763ca20e66,-0x8b0feba853ba45,0x43d99585e40bb9,-0x1a1f4cdb696d7c,0x7c9f03d3c7aec,-0x1bfb3af0402a5,0x488eb6a08399,-0x7f0cad31a0e,0x861be77006,-0x44437d49f,0x9487c7b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 11 22 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 22 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 26 indices rho q0 m0 0 40007520000 14=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 26 indices rho q0 m0 0 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x51055e610f80,0x4e6d237036f20,-0x23ace2f907c7c0,0xa214546f1e17c8,-0x202e574264d8c50,0x4be25a114134270,-0x89975711d7e5220,0xc40eeca16769a5a,-0xde77ef390a61ca4,0xca6f458690c551c,-0x94032730ced7128,0x56bb258b580a13e,-0x286e7d4558cae0c,0xecdaa349b21ad8,-0x42c5773c8d6d10,0xe11ad04a53a16,-0x21e51ea92fd7c,0x365f94d19f3c,-0x337a1f3f1e8,0x16acd981ca,-0x27d18204]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 11 23 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 23 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 26 indices rho q1 m1 1 40007520000 14=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 26 indices rho q1 m1 1 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x24,0x84,0xc1,0x90,0x3a,0xc,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x46e4b294ed900,-0x431fa681c00b40,0x1dd5dad491b7320,-0x844b11305dfb1d0,0x199a775f74074e48,-0x3ac3a38918e45df8,0x678aab5899a9dcf8,-0x8f1ce8ab7e2f4cd4,0x9d3095767540cfaa,-0x8a1ebedc9aaa8a46,0x613ea5f87d2cb076,-0x36b047284df36c06,0x185edc12f4cb505c,-0x87cf1254af108d4,0x2432b8642726ce4,-0x7279488c802320,0xfffcb606d29e2,-0x1778a074cbf4e,0x13ded5f25aae,-0x78a47c1e96,0xaa652eb0]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 11 24 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 24 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 26 indices rho q2 m2 2 40007520000 14=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 26 indices rho q2 m2 2 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0x36209dc00,-0x4cc3dad80,-0x309ea0a80,-0x122a4dba8,-0x47392794,-0xc0713f6,-0x16ddc0f,-0x1e9a4c,-0x1c3e6,-0x10f6,-0x57]
def m3 : List ℤ := raw_ints% [0x0,-0x3e081c424fde00,0x3983d1c92d02f00,-0x1901f04e9afa3fe0,0x6c57dca6a417cb40,-0x1475e53eca8c8d238,0x2dc1a15b04deb7f28,-0x4e6cde09b77db7a48,0x693f1d18b7cda68c0,-0x6fff6ae2d033d1b76,0x5f1bc807d66466bc2,-0x4087085848522941a,0x22d972e4015825506,-0xeda15c61708dd494,0x4ebff53fc075773c,-0x13d8161aa5639d7c,0x3ad725e123ab00c,-0x7a017da5329f9e,0xa3614adbce5ba,-0x7b501a139e22,0x2823537080e,-0x2d794ee40]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 11 26 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 26 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 26 indices rho q3 m3 3 40007520000 14=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 26 indices rho q3 m3 3 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x57,0x1]
def r4 : List ℤ := raw_ints% [0x1265159c400,0x19e06ec1a80,0x103924be400,0x5fbc1c9b98,0x1711c797a4,0x3cf2ead42,0x704ee1ff,0x8f8d55c,0x7b29ce,0x4136a,0x10af]
def m4 : List ℤ := raw_ints% [0x0,0x364718ba05e2400,-0x3155f1a33d6cf580,0x1501b63d3a63e4be0,-0x5904698ae71e973e0,0x106bc109ad0d8422b8,-0x23d132680372778a68,0x3bc67ed93270aa9ec8,-0x4df583f2b19c5ff908,0x507213cc2e6be0a916,-0x42132749d36e38f812,0x2b3ac3bf3bcd5e96fa,-0x166f0444234618acfe,0x925a4abbea5994214,-0x2e2815b209b27e7dc,0xafead586105a48bc,-0x1e8d1cfddef14f44,0x3aac8602536e93e,-0x479540aa5d080a,0x3005d7dff2782,-0xd5adca126f6,0xc1c62eb00]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 11 28 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 28 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 26 indices rho q4 m4 4 40007520000 14=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 26 indices rho q4 m4 4 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x10af,-0x57,0x1]
def r5 : List ℤ := raw_ints% [-0x3870a27d6400,-0x4ee527a7d680,-0x311460b91300,-0x11ed6a20c3d8,-0x444866eb294,-0xb19850c622,-0x1408b44b3b,-0x18e4debe4,-0x1483d74e,-0xa39602,-0x26043]
def m5 : List ℤ := raw_ints% [0x0,-0x2f7e35a2c525f800,0x2a5d509e71a7c7a80,-0x11aede6837b3097760,0x495e47bfb90eaa9120,-0xd3bcce8b6c07a34198,0x1c2e59d296528746888,-0x2dd684d97659665a6e8,0x3a267e1129c13054c58,-0x3a3c46e6c5e0322186e,0x2e4ca9973baacf19f7a,-0x1d3ae067ee037726f62,0xe9543d0ba33d60f006,-0x5b0df87f46271d7b64,0x1b551cc0cb9b28b48c,-0x627558c416160cbac,0x1003ad98ebb6e63a4,-0x1c73ec18a96a2136,0x1f90119260cf252,-0x12c3c847ae0c0a,0x471380cdfd7e,-0x3382020400]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 11 30 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 30 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 26 indices rho q5 m5 5 40007520000 14=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 26 indices rho q5 m5 5 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x26043,0x10af,-0x57,0x1]
def r6 : List ℤ := raw_ints% [0x809ba13149400,0xb2de34db70480,0x6e9724988e900,0x2817f3a1b69f8,0x974cf7d417e4,0x184f6f29503a,0x2b3b34d1457,0x34af8d292c,0x2a4c0befe,0x1452a842,0x47a3e7]
def m6 : List ℤ := raw_ints% [0x0,0x298e6eee6c8139000,-0x246a5e41521faa6280,0xeea648aebfd64025e0,-0x3ca75c4589f41a69d20,0xab52e30a0dfd1889838,-0x16487845f5b5f86cac68,0x235b72b9211a15b10b48,-0x2bab13c8bd5fcee3c698,0x2a7a13a76da6e3ee18f6,-0x20b6696684534e905412,0x13f0ed9600d733dd6c9a,-0x991c8a7cc2fea66490e,0x39347919ce802af7d54,-0x1058681bb0cd8bb2a5c,0x37a332f3a566fa5a7c,-0x87846d6f37519baf4,0xde7790feb6c5959e,-0xdfee9ce18436e8a,0x75a2e37937fba2,-0x17a101a179466,0xdaaac7b000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 11 32 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 32 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 26 indices rho q6 m6 6 40007520000 14=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 26 indices rho q6 m6 6 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r7 : List ℤ := raw_ints% [-0xf25b35c1f98400,-0x14fadc09c8b7a80,-0xce841392a7f500,-0x4a6c5bdcad4398,-0x116cf468b68894,-0x2c65cf7919992,-0x4e12fb2f516b,-0x5dce5a51b64,-0x49eedc3f4e,-0x22a905352,-0x761ba13]
def m7 : List ℤ := raw_ints% [0x0,-0x245ca1109ef111e000,0x1f5527bd95c82794c80,-0xc9b1b2446c406872060,0x324a0c338d0baa12d5a0,-0x8b291c8de04670dfffd8,0x11b43ba2799e85e00da48,-0x1b6d96e8a4072d3c7d8a8,0x2101e11615a3d928f3a78,-0x1f35ac8feb6566d6036be,0x174c767f612a16f257e2a,-0xdb8c8e467aa26fc66e92,0x656392d3f124449b7236,-0x2446f87a37f5e84598c4,0x9de043948c1de5be22c,-0x1fba707a37ab923cbcc,0x484741fd247c522c24,-0x6d7c99a6e79e07246,0x63cbb2b0170faf42,-0x2e30dc3a42502fa,0x7d96c4ff1b32e,-0x39eb9b64000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 11 34 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 34 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 26 indices rho q7 m7 7 40007520000 14=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 26 indices rho q7 m7 7 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r8 : List ℤ := raw_ints% [0x18f8e03bcc935400,0x227834a774295c80,0x151eafa4a5f44d00,0x792f1a699d46878,0x1c35425fe663464,0x475c04f444d95a,0x7c6558e8b9357,0x93d95eaaa28c,0x72f0df0355e,0x34f0d1e742,0xb03aa207]
def m8 : List ℤ := raw_ints% [0x0,0x1fd10cee8b12efa4000,-0x1afc140d7c5f3fa90a80,0xaac850467bdeec8d7ce0,-0x29d0310ffc85e83b92320,0x717526d684efa8cd89ff8,-0xe218fc508bed8b51e47a8,0x1564e3e042aeba95672788,-0x191b59f1022511af152798,0x1717fb85e3c296d9f7ca26,-0x10b911745b5c682d52aaa2,0x9856833fee4eec1fae2ea,-0x43bac406b41b9745954be,0x1736c11551e8697729cf4,-0x602b0eb960d31cdf133c,0x12404e3278efddde7b5c,-0x26dacf9750d959f3554,0x363c1e49319d239e0e,-0x2cab883955c1a92da,0x122ad4dc9c63d032,-0x29ae60e0534056,0xf512f9b0000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 11 36 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 36 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 26 indices rho q8 m8 8 40007520000 14=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 26 indices rho q8 m8 8 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r9 : List ℤ := raw_ints% [-0x2542d219dc37d0400,-0x3348ad6661fe76a80,-0x1f50addf24ce1ed00,-0xb2f538ace39e0498,-0x2974a9963b4f5494,-0x6844ae33e67cc52,-0xb47f6ba49f34ab,-0xd4b45e15ae404,-0xa39f627068ae,-0x4a5e1d0a2f2,-0xf35dac173]
def m9 : List ℤ := raw_ints% [0x0,-0x1bd6eb50b9b091af8000,0x1742d795f9646f497b880,-0x90deb311bd41cf5bb2760,0x22dc285a8fe3a0b2b444a0,-0x5cd5afb838d735986a6f98,0xb54620d9d6b35aeb8f1b88,-0x10c6b1bad62de8e78d92ce8,0x1336cceedff1e26db34c2b8,-0x113492e523b6dfc138fd1ee,0xc17e59295546c2c4bade3a,-0x6a8e61349b2faa33591ee2,0x2da0efb1c055aa54b655a6,-0xefbe61525cdc4f16dd864,0x3b164ed3f1e9fdbcbde0c,-0xa95e3429e544660dbcac,0x150ab5913305a2f47944,-0x1b068382e9aeb4bd8b6,0x141255ecba873f4512,-0x72773e018525b58a,0xdd1b5d3507ac5e,-0x40b61b040000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 11 38 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 38 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 26 indices rho q9 m9 9 40007520000 14=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 26 indices rho q9 m9 9 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r10 : List ℤ := raw_ints% [0x3374c3f95fd149d400,0x46a5d25a75bb056c80,0x2b03d1f86a3725cd00,0xf4fc27e6361d66778,0x3885fcaae89ed56e4,0x8d7d4237022a4d1a,0xf3899067d6b1cb7,0x11d069836173f2c,0xd96d32f0952fe,0x61ce3d6c7fe2,0x13bf1c82c87]
def m10 : List ℤ := raw_ints% [0x0,0x185c0de6a27a7f7990000,-0x1411958b7e6dc489d2fe80,0x7b1a255d68322190a65fe0,-0x1d237c048a8f215988c1420,0x4c39280b2c03513007406b8,-0x91f655eef11518ac008a9e8,0xd38ef2a3f99e9e7aee73cc8,-0xeca8b95f12bfa894fb7c858,0xce744e989dcb233ec1bc816,-0x8cf1d0ed954b80f4689e9f2,0x4b1d7d6c6ba80a895eb7c7a,-0x1efdd2580a57930fcfbfc6e,0x9c0ba428df11b506598f14,-0x249ae4b555878a11bf2c9c,0x63007a0e730ffcc0d07bc,-0xb795bb270d00bad71374,0xd8a30100498356e7c3e,-0x90c6fd82703947ceea,0x2d1d18efa959d7d02,-0x4939ebda040fdc6,0x110fec4b00000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 11 40 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 40 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 26 indices rho q10 m10 10 40007520000 14=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 26 indices rho q10 m10 10 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r11 : List ℤ := raw_ints% [-0x42cd4122a7245030400,-0x5b86326f947890eaa80,-0x3796bde2b136d341d00,-0x13baf88c57026cae898,-0x4896d5b4053fbae794,-0xb4fb202db3392bad2,-0x1360ab1645686486b,-0x168d17de3486e324,-0x11161eeaacba30e,-0x79f787173fd52,-0x186042fcb853]
def m11 : List ℤ := raw_ints% [0x0,-0x15508c29ce2b2f8a5e0000,0x11542716c60bd48a563ac80,-0x68c75bf032f27b16c7e1e60,0x186ac217072686f27a3345a0,-0x3ecadaa2bbb177553cad3358,0x76043868745724886736b4c8,-0xa79148e19425badd6a6d1d28,0xb738cf3fc8c22b03c257e178,-0x9bd36474b7541f8459dd4e1e,0x6763b1a2384918e454ea384a,-0x3559f1097db6d9176224a232,0x153765c595ed96a66fa48196,-0x66631625661014f9a856a04,0x16db6f2faa87b84fd3e75ec,-0x3a4cdf167de7d3fb947b8c,0x64c0f533be70cbd5c11e4,-0x6d1135218df0afac4826,0x417391977eac41884e2,-0x11ca29d6115d8d8b1a,0x18392b1e7f24c90e,-0x47e180e400000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 11 42 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 42 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 26 indices rho q11 m11 11 40007520000 14=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 26 indices rho q11 m11 11 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x186042fcb853,0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r12 : List ℤ := raw_ints% [0x527692effbfc6f525400,0x70c6ccb74d5a11b03c80,0x445a11273fec3b5ebd00,0x18335299601ad57fda78,0x58c743efdcf22df4c64,0xdc98d9f88a3a9b4cda,0x17868e384f404970d7,0x1b400adabada354cc,0x14881ac6e1689f1e,0x919490acd46f82,0x1cdc176474ac7]
def m12 : List ℤ := raw_ints% [0x0,0x12a67aa49465c9991240000,-0xef981a54251ecef75824280,0x595300b9d1a58cc003050ae0,-0x148269f1860e3dbc44dc35920,0x33e4b23f73250c4253089bf78,-0x5fcd49e64bab0a1994d26da28,0x855b4a8073b3f5ddb62548008,-0x8ea1dbf2ec900729bf3ecd618,0x76578679104e07cfe854d9086,-0x4c5b846df68ef4b6436cd2ec2,0x262b976badf411f940616178a,-0xea2b4976ce4ffa26d84f019e,0x43b3a4c44bfe27f83f247034,-0xe618a6f15014afcd4068efc,0x2292cc46b0c7e2c837e911c,-0x37a059ea888c340b19ed94,0x372725353b55c13e766ee,-0x1da8de32b88951f6a67a,0x7044e30447b8e7dd52,-0x800f3c69885098b6,0x12e6e28b000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 11 44 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 44 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 26 indices rho q12 m12 12 40007520000 14=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 26 indices rho q12 m12 12 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x1cdc176474ac7,-0x186042fcb853,0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r13 : List ℤ := raw_ints% [-0x61a1a3abc951c13420400,-0x854f4b079cb5c47468a80,-0x50a5f890da12033c6ed00,-0x1c7e472f8cf99b5de9298,-0x68446cab285f3f6ab194,-0x102561d89888d1a6d7d2,-0x1b751d712d79252a76b,-0x1fadc9397baeedd844,-0x17c1dbe56b7407eee,-0xa78525a07ec9d32,-0x20fd4010bd7b73]
def m13 : List ℤ := raw_ints% [0x0,-0x1051ab5001d91065eff80000,0xcf336fcaf1dd6b9bcfe06080,-0x4c43b6f8785efaaea0fde8d60,0x11443f8cccca415600ba8556a0,-0x2b0479aac34f40821d1e5be518,0x4e11342e78479565f798127808,-0x6a9e2473022645d9a165783f68,0x6fa00d16ff28a4dd43b5528038,-0x5a69df56280941ea737cc6afce,0x38c3d65856b9dba27ac585aada,-0x1b808cc0d6945f1fb9fb0cdc02,0xa2bab354d5b60e3d62c0eef06,-0x2d1a00d3b39fafdcb931444a4,0x91d240e5ddc6472b9977f8cc,-0x14a3a5ab2712cf5e4a12156c,0x1ee1d2745bf989fd1c5b184,-0x1bfff4b8dbab83ce9a4316,0xd77836642ecdff1aef32,-0x2c48a8afddffd16fd2a,0x2a4346bd4749df53e,-0x4f6dcd04000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 11 46 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 46 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 26 indices rho q13 m13 13 40007520000 14=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 26 indices rho q13 m13 13 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x20fd4010bd7b73,0x1cdc176474ac7,-0x186042fcb853,0x13bf1c82c87,-0xf35dac173,0xb03aa207,-0x761ba13,0x47a3e7,-0x26043,0x10af,-0x57,0x1]
def r14 : List ℤ := raw_ints% [0x6f99f7f984a0a73321d400,0x982ca7c9773f8e664f6c80,0x5be9db9947be366067ad00,0x2069c1953fbe783cd97778,0x765b5ce96a36a371650e4,0x124841800e869059dd41a,0x1f001f13bfcca434df37,0x23a56ad89c078853e6c,0x1aa0909f9a96601abe,0xbae2fec9017949a2,0x2499d6c715a2047]
def m14 : List ℤ := raw_ints% [0x0,0xe4775e6019dee5931f900000,-0xb350a9eea5c1be731620ee680,0x41354b13f0309577c806e32de0,-0xe917aa4e756a6658283c3d9620,0x23c3b3928290ec28825f8a24638,-0x3fd999b8485f57272431c4c0468,0x559e068f0049b8c8335027d1548,-0x57ceaf6a1d6c8f95ede52daa5d8,0x457a05b55ae4f36f7615d5a5676,-0x2a780fbca2eea2919b3a9eae012,0x13f38a70cc9ead4795d3fe2911a,-0x71e46c7e6bcff8d99f5f97c64e,0x1e43273a4ca46435cb7b841a54,-0x5d0e11fc7566f42c9211fd45c,0xc65fc6900efead95cfc5957c,-0x113ba01a71bf06398e9e1cb4,0xe43cd5176b5084a631251e,-0x61fd7ea5a8f04779fec8a,0x1176fb47fc0e0d5f3222,-0xdee6ff8fdefdacd26,0x14d6125b0000000]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 11 48 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 48 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 26 indices rho q14 m14 14 40007520000 14=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 26 indices rho q14 m14 14 40007520000 14 11
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_14
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<15) : intPolyRF (mz e)=rfPoly (C (40007520000:ℚ))*rfX^14*(1-rfX)^11*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V4C15
