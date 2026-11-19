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
namespace CatalanCore.Li2.NVMod.FamilySource.V5C18
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,5,18,size⟩
def bases : List ℕ := [0,1,2,3,4]
def indices : List ℕ := [5,6,7,8,9,10,11,12,13,14,15,16,17]
def num : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def den : List ℤ := raw_ints% [0xd7a9f489000,0x1247cccfaf00,0xb4a20f6eee0,0x43499116c08,0x10dfe78c724,0x3027da196a,0x64968b3ad,0x9bc4cd19,0xb2e51c9,0x9689f1,0x5a3f7,0x2483,0x8f,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x7,-0x230,0x3b1,-0x5e8,0x1729,-0x19860,0x2a1fa7,-0xaebc3,0x22f27,-0x127c0,0x5377f]
def rhoDenominators : List ℤ := raw_ints% [0x81f0,0x4d,0x8,0x1b,0x4,0x1,0x1,0x7,0x70,0x1b,0x8,0xb,0x129]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-5) 0:ℚ)/(rhoDenominators.getD (m-5) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 5
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 5 18
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤17))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤17 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1]
def omegaDens5 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19]
def omega5 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums5 omegaDens5
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_5 : padCoefficients 18 omega5=padCoefficients 18 (omegaCoefficients 17 5) := by decide +kernel
theorem omega_spec_5 : coefficientsPoly omega5=omegaNumerator 17 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_5
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens6 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24]
def omega6 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums6 omegaDens6
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_6 : padCoefficients 18 omega6=padCoefficients 18 (omegaCoefficients 17 6) := by decide +kernel
theorem omega_spec_6 : coefficientsPoly omega6=omegaNumerator 17 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_6
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 18 omega7=padCoefficients 18 (omegaCoefficients 17 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 17 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 18 omega8=padCoefficients 18 (omegaCoefficients 17 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 17 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 18 omega9=padCoefficients 18 (omegaCoefficients 17 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 17 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 18 omega10=padCoefficients 18 (omegaCoefficients 17 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 17 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 18 omega11=padCoefficients 18 (omegaCoefficients 17 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 17 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 18 omega12=padCoefficients 18 (omegaCoefficients 17 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 17 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 18 omega13=padCoefficients 18 (omegaCoefficients 17 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 17 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 18 omega14=padCoefficients 18 (omegaCoefficients 17 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 17 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 18 omega15=padCoefficients 18 (omegaCoefficients 17 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 17 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 18 omega16=padCoefficients 18 (omegaCoefficients 17 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 17 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 18 omega17=padCoefficients 18 (omegaCoefficients 17 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 17 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
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
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 17 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 5 18 at hb
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
  · exact omega_spec_17
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
def r0 : List ℤ := raw_ints% [0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m0 : List ℤ := raw_ints% [0x0,0x688811c4152400,-0x7a5cbba95608b00,0x440b2461ddc4cb80,-0x17e7b19de8502a120,0x5f3c63b7dc0f34e60,-0x11def9cb27fb9370c8,0x29f995346c7bc3e068,-0x4f05843ad7778f83e4,0x793066e69f7bcbc854,-0x990ba77e37040a7a2e,0xa03a873e73e20b7006,-0x8b8d46d72b4ec13f71,0x652dc62b690428fddd,-0x3cf100954c05666ba0,0x1e589a8376c95c5928,-0xc64ca28044f5a530f,0x41a6486893a030cab,-0x1153fe0c16a2979e6,0x3900eb86c59a8bae,-0x8d54408cf492c9f,0xfb9c469e64c8c3,-0x12a75251266864,0xcfe1dabc4f1c,-0x426e6f307fd,0x523f25221]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 13 26 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 26 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 31 indices rho q0 m0 0 25560004377600 17=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 31 indices rho q0 m0 0 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m1 : List ℤ := raw_ints% [0x0,-0x6f1092e05676400,0x7f91828bda163b00,-0x458ead08d7b1cba80,0x17f15938eec7e70c60,-0x5d613bf348d02af4a0,0x11237ae66de7e4fd818,-0x27554a1123232773ab8,0x4846212b3ffe4e8abb4,-0x6c0dd936cdc9d35c3a4,0x84d910e2d8e975c7c02,-0x87331021b399d0b725a,0x7245141cadebb039995,-0x503e1e950cc4f0343a1,0x2eb4fe4a338f15c0a04,-0x166b1db87ec5000054c,0x8cc7724b0c403b7c43,-0x2ca057e9bbb4a3fe3f,0xb3aa485190c64cca2,-0x230600cec292c566a,0x51c1ff2bdb1f628b,-0x87cadebbace2c0f,0x946035282ebd20,-0x5d7066aa3c798,0x1a34d9d05ca9,-0x1b13039aed]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 13 27 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 27 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 31 indices rho q1 m1 1 25560004377600 17=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 31 indices rho q1 m1 1 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x240,0x960,0x1054,0xf8c,0x8e1,0x320,0xaa,0x14,0x1]
def m2 : List ℤ := raw_ints% [0x0,0x76019c0e5bdda400,-0x851995dc86649eb00,0x47371fd6709fae5b80,-0x18093f817de812de120,0x5bd749c2b24c8578f60,-0x107faf99267816427548,0x250644384b08051044a8,-0x4272a5845c1947bd5344,0x60e9284ca97aa92935f4,-0x7411cb13b38bdf21d4ae,0x72e4f15f191476ba3ef6,-0x5e49a7add0e58c734629,0x4028e11c8f10be3bbd65,-0x241b0cd5bfb7f0fc50b0,0x10b5beda88b6dae861e8,-0x64dc21c4cb3354a8737,0x1e9db268439f6a98ee3,-0x757e0c5c481c3151c6,0x15b54142147fe659de,-0x2fae62c71a5c64fa7,0x49cda79de6e34b3b,-0x4a29ae97d358b74,0x2a20ab1ea0b7fc,-0xa57050d57bb5,0x8e6946dc49]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 13 28 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 28 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 31 indices rho q2 m2 2 25560004377600 17=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 31 indices rho q2 m2 2 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% [0x1]
def r3 : List ℤ := raw_ints% [-0xd7a9f489000,-0x1247cccfaf00,-0xb4a20f6eee0,-0x43499116c08,-0x10dfe78c724,-0x3027da172a,-0x64968aa4d,-0x9bc4bcc5,-0xb2e423d,-0x968110,-0x5a0d7,-0x23d9,-0x7b]
def m3 : List ℤ := raw_ints% [0x0,-0x7d61b5cf419b7e400,0x8afa2a623d77e89b00,-0x490600534f88609aa80,0x182f35b47a8f387fe860,-0x5a9910d7b6111d9b78a0,0xff119594988824b7bf98,-0x23014bf3cf0fd041b60b8,0x3d67007ac3a85942cc954,-0x576a6c47f716a56b4df44,0x660e2af26fa3dd10f5982,-0x62510c174f35d19174efa,0x4e61a49e7b793ca1ab31d,-0x33b541080d50eb6991129,0x1c24c589d4382e86956f4,-0xc901ab934fc4a62b585c,0x48e6722ce514bb90d45b,-0x1530f8f8f6a3e8c13b57,0x4d822c97d113f431ac2,-0xd91631d8da88d2efea,0x1c059841dd1bab8c43,-0x286056d93c01274c7,0x254056184bc48e10,-0x130b10ef576f168,0x414588c6cb6b1,-0x2ec266a9ef5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 13 30 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 30 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 31 indices rho q3 m3 3 25560004377600 17=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 31 indices rho q3 m3 3 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% [-0x7b,0x1]
def r4 : List ℤ := raw_ints% [0x679ea87dd3000,0x8bb04c8808500,0x55a5609d516a0,0x1f9fb6a67f8f8,0x7d84aaf64244,0x161527516eca,0x2d51d743cf5,0x448e25e0b6,0x4c37c8ece,0x3d26048e,0x21f469d,0xbea1a,0x20dc]
def m4 : List ℤ := raw_ints% [0x0,0x8537d12c35b5362400,-0x9138c8304ffc6724b00,0x4afcf6f24204d0482b80,-0x1863225acde988f211d20,0x59a1e75bba19b2b350d60,-0xf7596a0eb533f131e9ec8,0x213cf13b54da897b014b28,-0x3905744910b3c81ef8d8e4,0x4f4ab75a5a3114b3723c14,-0x5a49f74e5b960baf45acae,0x54b2f595b232196b10b5b6,-0x41a1cdb32420fe17ef77b1,0x29fea174c49ffe478bfb0d,-0x161d77bab5d48aa95c8c20,0x9863880b0ee2055e8f198,-0x35246c49e48a06511e34f,0xecb337362dac7538269b,-0x338fdcbab9cd55dc7766,0x88c5091f82eca7d2fbe,-0x10968aafa7b04968d5f,0x1639763902d446e053,-0x12cb5ab71da5a39e4,0x8a093af0b6e862c,-0x19bf00263afdbd,0xf55b13f6cb1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 13 32 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 32 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 31 indices rho q4 m4 4 25560004377600 17=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 31 indices rho q4 m4 4 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% [0x20dc,-0x7b,0x1]
def r5 : List ℤ := raw_ints% [-0x1bae949f45bc000,-0x2523563707d3400,-0x16a3cce6990c380,-0x84d5ffaea4c040,-0x20adda5e47a9f8,-0x5b0d8d7a4d4d4,-0xb87f051e99e2,-0x1129594f2487,-0x12ad7e18806,-0xe8f201c4e,-0x7c31c3b6,-0x29079f7,-0x670ca]
def m5 : List ℤ := raw_ints% [0x0,-0x8d8b4e3ef9108986400,0x97db4fdb43a92d96fb00,-0x4d1dd293c4f3e61649a80,0x18a50038f77d1a14018c60,-0x58edddd5d5be092f2102a0,0xf0b5531103c308a55ed918,-0x1fb13dd72b3a415312d6238,0x353561246cec63c0e348d74,-0x4850861628d3aca9caf1ce4,0x505c515e54b6f3dee3fc602,-0x49727a41b9512131e66cafa,0x3758468ad724cdee1382ec5,-0x225c9d94eff5f2286e69431,0x1183b8062bf9bbdb95169a4,-0x747818713cbad97ede2d0c,0x270f4edbc26ffac8a1abd3,-0xa69bab4a7eebb160edeaf,0x229403db2dc43cce04662,-0x56d358e9e2d4bdf4a20a,0x9e313816042ff3d26db,-0xc4d7ae336b33e3447f,0x9853307fcfa4e8ec0,-0x3ea66644f1da8218,0xa26d0600f8bbd9,-0x505f89145c3d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 13 34 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 34 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 31 indices rho q5 m5 5 25560004377600 17=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 31 indices rho q5 m5 5 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% [-0x670ca,0x20dc,-0x7b,0x1]
def r6 : List ℤ := raw_ints% [0x56d00424ce41a000,0x7401b9d69e145600,0x4663e750341d48c0,0x19abae1285a1fad0,0x64615349ea02228,0x11578b1176ac3ac,0x22ccaf19a2a1ae,0x332becc7c2bd8,0x36d9a7bb5413,0x29eb6e6c024,0x15c4d95498,0x6ef65ba8,0x10886df]
def m6 : List ℤ := raw_ints% [0x0,0x96640322e8a1921ea400,-0x9ee80000e690c0706ab00,0x4f6a8a2e77481e74affb80,-0x18f4dd7020958718c0ec920,0x5879aaacf3e3edbe5bbaf60,-0xeb0c69f2327589c76a7e048,0x1e57760c5917512480e25ea8,-0x31e24fe81dc9cfdcfc065c84,0x424cfceb2ad7ff5011797534,-0x47f195bd847012f8ce7a58ae,0x4018ebe3156f8bbc6c2e05b6,-0x2efda5380f492a903f1e3ab9,0x1c523adb31306854d7d63e75,-0xdfa12207d722100b2cc0e90,0x59b79315d328444b5f66a88,-0x1cf0517db2b0989a0dd65e7,0x7634d30877ad170e4cf613,-0x175e4024465d092121b306,0x37851eb67861e6b71975e,-0x5ee5b95ce4f14f609997,0x6d89cd599ea1ba7f0ab,-0x4d6ff1267adc44af54,0x1c7a3441c30abb31c,-0x40033ef67d27b45,0x1a4ccdcac2d59]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 13 36 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 36 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 31 indices rho q6 m6 6 25560004377600 17=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 31 indices rho q6 m6 6 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% [0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r7 : List ℤ := raw_ints% [-0xded8e30053b957000,-0x128cdcb3c7c841d100,-0xb3662e7a3b10eff20,-0x412112497a8dc0238,-0xfd50fcdebaf0558c,-0x2b7c628476f97d2e,-0x5698b2ef33e4e07,-0x7e28551bef1d19,-0x85ae986f4483f,-0x64b3e822fadc,-0x335588e5e05,-0xff57b0b85,-0x24ccfae9]
def m7 : List ℤ := raw_ints% [0x0,-0x9fca4355172bab408e400,0xa6657b28e3a6cc77715b00,-0x51e53e9dfa8468792c98a80,0x1952dacc19f59c57b62fd060,-0x584298beba9c47c1770614a0,0xe6496c60bc0747d7f0f82e98,-0x1d29e4ee74999dc9554fef5b8,0x2efb2e7e08164a9861a80bc94,-0x3d19c1d4cbc6f52c835068f84,0x40c6b40ef73c56a8eb1085482,-0x38492f784b23abf07c1be427a,0x282a1f00afab16aa8607c102d,-0x178208e3acca7bee91e422979,0xb3c817d6ce1b90841abecad4,-0x45a327a2e9e6e5d362ac9bbc,0x159b2606eeec36657f1d7c8b,-0x548285e38c26007be4549c7,0xfe8da0c4b1836769084b02,-0x23bf4bb2d81e95f46ba1aa,0x394610bc2fce982be09b3,-0x3d4055fd179aec9249f7,0x277e04d7e3d555f01f0,-0xcf5b394b9a63c35c8,0x193688c1fb8216c1,-0x898db5117b4c5]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 13 38 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 38 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 31 indices rho q7 m7 7 25560004377600 17=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 31 indices rho q7 m7 7 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% [-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r8 : List ℤ := raw_ints% [0x1f00953263a95ab1000,0x292ce60fb727256d700,0x18ce9e8f53f384458e0,0x8f8d2cb6c9d9ac2428,0x22bde73fe6a63a658c,0x5eed8a33fafda4fee,0xbbdeff981aa4fd47,0x10fadb27f716c7ba,0x11d4f09bd439cd8,0xd4905d4d09e1a,0x6adf03f276f3,0x20a4f9ecb36,0x499051ca2]
def m8 : List ℤ := raw_ints% [0x0,0xa9c6e78a689e65f4972400,-0xae5ace03608e393ee870b00,0x54903c99e95b185c1de5cb80,-0x19bf2b3a4f0c83eb61d94b520,0x58467899720e9cd31bd911160,-0xe25a3c71fa6c46e094b9e25c8,0x1c23b20f6f0f3bf4d1022d5a28,-0x2c71b346d29401220e208f9524,0x38974d8d7e3f0d7b6646e28354,-0x3aa59e819867faca4c1b3472ae,0x31b9cc17aa1a152577836818b6,-0x228da0f1e3006e44d62c548801,0x13a5ac6e0e765d86e02774981d,-0x91923c52d77c74a788309d680,0x3673a2bc255443d4d4b3eb5f8,-0x1040849622016f68969983b3f,0x3cddb440f54fc5a32bc92c4b,-0xae89c70e411d20c03af2da6,0x172ae18f9f016b7c5448cfe,-0x22c385b52f45d8d9f5c58f,0x22672f6181b10957ffcc3,-0x14328858541ea209f644,0x5e740eda2053e15c8c,-0x9eca2c4dc6683f0d,0x2ceb7b08e35841]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 13 40 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 40 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 31 indices rho q8 m8 8 25560004377600 17=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 31 indices rho q8 m8 8 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% [0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r9 : List ℤ := raw_ints% [-0x3df90b3bab7f8bab2000,-0x521c70c6214127e5ae00,-0x31553ce43a27f66cd2c0,-0x11c8ff578bcf70bae430,-0x449cf30bfd6cc3dd0a0,-0xbaaa48a90945a34788,-0x16f8c9e1e41f6f4f8c,-0x2104fefa3f0d0888b,-0x226d5404e717f578,-0x196d42cd3cb09aa,-0xca5f19f832834,-0x3d0001b1f7f3,-0x872a3c3348]
def m9 : List ℤ := raw_ints% [0x0,-0xb46356030f284c53e096400,0xb6cf760b85441cd2d6f7bb00,-0x576dfed6b34f6a67885f87a80,0x1a3a13664990ed60cf299c1460,-0x588393f94181192780d6abb6a0,0xdf2f756a3f53fd69548b668818,-0x1b40bebeb3f71627928d4337538,0x2a39df37c8b06ae63c5e473f0b4,-0x34ab98ae2a2070f72d5e2bfcb24,0x35628b9e81ff57328787b0fc102,-0x2c30725aa608aabd8415a51edfa,0x1dea004d8f7baef9c8b48960fd5,-0x1087cdf933b33faef4b9be77e01,0x76b1da0fc87e76edcf34083984,-0x2ae218935107c528a8eb55e9ec,0xc502cac1c5ed5c1a831b78c03,-0x2c264dcba8e18cdddf44d209f,0x787d6b097f3bc6014f486ea2,-0xf1bba1e65f60b758eaa024a,0x1536a7ca797d58eda4bb84b,-0x1366ef1459186b46dc362f,0xa5ae012ad5f456c12ea0,-0x2b0deb195b340f6d0f8,0x3e75901a5a7437be9,-0xea7bfc83725a8d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 13 42 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 42 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 31 indices rho q9 m9 9 25560004377600 17=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 31 indices rho q9 m9 9 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r10 : List ℤ := raw_ints% [0x71de348d664da01188000,0x968e80a6122e2729b1800,0x5a3d7c27d055a0ba42100,0x207191994232830df2780,0x7cc4bd9702c8c55949f0,0x152326af6bd435017330,0x2971573bb9aba26b820,0x3b45b1314510a25a7c,0x3d6f56bde939d82fd,0x2d0e401a1f35d950,0x163914e415948ce,0x6a129748135a4,0xe8095eead45]
def m10 : List ℤ := raw_ints% [0x0,0xbfa98b63401ad1191e9fa400,-0xbfcb68942c455ea0046736b00,0x5a8130525450354b4ef7299b80,-0x1ac3e978dfbd9528648e5762120,0x58f8a33841959888784dcf42360,-0xdcbc11c105a96dcd30178b2bf48,0x1a7d8967c01851b9e1e4306f09a8,-0x28499841d3fd335c022cf668a6c4,0x31410fd9929c31a1430b7f535674,-0x30d9d6fd64068c4603172cbcd2ae,0x277e99e45f86d9847589a45155b6,-0x1a0ead9a4492f6abe67b5b0a9c89,0xdffb71ca8013bab680fbbf9ac05,-0x6170195e76bffb24dd1917df9f0,0x2201f308f30ddcf577aa05d24e8,-0x964ed868124c72ed1cbd0fd257,0x203e7f404faad55ad6e054cb43,-0x53b88b26f826ab55f42118346,0x9e930de4bd6104925043a99e,-0xd026e7ff4f3155117628c47,0xafb99ebe5e999b9b6d549b,-0x551fdd4e2100c0d7254b4,0x13a28477c73e33d2c57c,-0x188cce63557c6b9e15,0x4c6e9d6b1abb769]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 13 44 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 44 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 31 indices rho q10 m10 10 25560004377600 17=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 31 indices rho q10 m10 10 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r11 : List ℤ := raw_ints% [-0xc379ea8bfcd0f6d7ded000,-0x101fdeb4fe7d7d83e24ab00,-0x9a50929de50ef9c3a0aa60,-0x37594a42f78e57137f6528,-0xd446ede8904c61bb9d934,-0x23d9950f113aeae2831a2,-0x4608f61451e41178e371,-0x63beb64f4a97abc749d,-0x66e07d137645fc85b1,-0x4b032e544d33b87f8,-0x24be8b16e4bf4343,-0xadef9408271581,-0x178aa4bd193e7]
def m11 : List ℤ := raw_ints% [0x0,-0xcba42419741c7e2ab0899e400,0xc9571a455db6b48a04adaa1b00,-0x5dccaecf09276d597d172b16a80,0x1b5d14f79891f0834fde7b63d860,-0x59a4c46d974e830a3b20341988a0,0xdaf51f85cbb28f1501c8029b2598,-0x19d715eab44e0d35d0a3862ba68b8,0x26985701633a65a17b8ee6b3c79d4,-0x2e45bf15438a6956b6107b71ee7c4,0x2cee5ab32b82837fad2fe77752b82,-0x237eed93174322958950030efbf7a,0x16d5808ef17c5e9df60532b65b1bd,-0xbee217697ad53773fb0772bb1fc9,0x50841ff7c5cb7cb38f5d6c523db4,-0x1b26b6d6582e34f08eecfce6799c,0x7373eb75bc98c1aafffcd8e663b,-0x17b46f673119fd7a4cda94c4137,0x3a890971cc9394c5253a85e142,-0x689b1ad9163e0c20f7af249ea,0x803f196a8c662cd4387ceea3,-0x63ced97414599aacd5fe327,0x2bd122ef9680845e1d7cd0,-0x8f50792b9361d31bf1a8,0x9a469cb5a22759cf51,-0x18e45bad3d914f95]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 13 46 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 46 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 31 indices rho q11 m11 11 25560004377600 17=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 31 indices rho q11 m11 11 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r12 : List ℤ := raw_ints% [0x13d5115e4f3f7f89f529f000,0x1a2223fe7f242c4118051900,0xf9a6511389ecb4df0b78120,0x595bc6b788f7f90e6a868d8,0x155e812144faf430639f854,0x39962230b8cc74e434f372,0x70267132392250dbb4679,0x9f27b5fac676434a891e,0xa378ccc4c0cdd1ec2c2,0x769e41143aebd055c6,0x39c607068a8a940e9,0x10fa26b7604be7f2,0x24778c51ea8888]
def m12 : List ℤ := raw_ints% [0x0,0xd85e665b0b5e460d5b92382400,-0xd37b8711a23f1fd2a4f884bcb00,0x61538d7e4d76135cf68623bb6b80,-0x1c060ec236487ed61a0be4f200d20,0x5a877402766d44a37adedfa942560,-0xd9d180cd0996d17fb9cc902108cc8,0x194ada03f63645cfd1d7d515e9bd28,-0x251ee3ceadd170580279bffbce6964,0x2baaa830c978223672dc0c06e7d694,-0x298824f86695df447b7c25d42348ae,0x2013523130a5a5aa576a85cca288b6,-0x1420515b3fa932fdd77c1933b08651,0xa3adfef3a7b7aac57ba3f45035c2d,-0x42f5d4a1420176416deba0796ece0,0x15d1bd9f605192a8a74a019cbf758,-0x5942dd29027490d48a05199f052f,0x1189b91213de04b9fbfef32810fb,-0x292b9d40a48b4bab75bec435be6,0x455ecaff9b27539669383cc93e,-0x4f5b6f9b16ef7f9094553cfbf,0x38dcb58538f339e905ad1633,-0x1697040d549d0de1a64bea4,0x4163513af1872dc7875ec,-0x3c8be0a878e7910365d,0x8199678cbd0b24d1]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 13 48 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 48 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 31 indices rho q12 m12 12 25560004377600 17=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 31 indices rho q12 m12 12 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r13 : List ℤ := raw_ints% [-0x1eb89c99e3c4a9ba6cb0c8000,-0x286cd21284fdbfb9e24230800,-0x181902434b4a63a6ed2d0ce00,-0x89c1e2a546009b6fe93e2320,-0x20e021d83bfdf426de348248,-0x5862f8514689adbc807d7fc,-0xabac28e75f760bb4006876,-0xf2e03a12f3062a1a0f6cf,-0xf894733648a3a37db1aa,-0xb3a25ba564ec36c8d46,-0x5712ca35e51d0ffd72,-0x1971877ea3d8dbcaf,-0x364a0aa61b65c06]
def m13 : List ℤ := raw_ints% [0x0,-0xe5e44cc0bc142a6e314b5ba6400,0xde423aaaab1011cfcf480d087b00,-0x651917de9df0fe8dc972338b45a80,0x1cbf612cb149dce14732cd49ed1c60,-0x5ba0868ce31b9f3e14df17a8bf8aa0,0xd949b63714736124e9d1a773502718,-0x18d6ad0633c5bf33bed4170d8af9038,0x23d7201d1f0460eeae4131144e43ff4,-0x29633aed65654abcc369fae2d6c4d64,0x2693749e993bf0d2b99adb9eb3bc402,-0x1d236151a883971e718901afd852efa,0x11d7290e2900f415b9a763df19397e5,-0x8d325103fa40c8744bff4c403df0d1,0x3808d001501f17e3ab20c565502364,-0x11a5625f304fba816e99b593a91ecc,0x4572e3f94e5ded5c68fba418b4133,-0xd0e13ee9d2c974fee6a3b020218f,0x1d1f342b7ff5deace10d28973ae2,-0x2e3bcfb905faaca71e0b3ef688a,0x314d63671d17e4bf745775dabb,-0x207c0304d1e0c8b8cf49c7edf,0xba969983f1010b2616ff880,-0x1dd58e908c65c6cc7ddbd8,0x17be45fba43cea7be2f9,-0x2a2366352caed65dd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 13 50 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 50 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 31 indices rho q13 m13 13 25560004377600 17=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 31 indices rho q13 m13 13 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [-0x364a0aa61b65c06,0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r14 : List ℤ := raw_ints% [0x2dbc39ae28708fbe442f736000,0x3c1b61b139293822980eb59a00,0x23c7a07c3cfa2a8cc812bf1140,0xcc36a87110c77ef70dc1a9a30,0x30a5a619b7679dd91acbf77b8,0x8285369b1788745fad662e34,0xfcea98cb849f511dafc8a12,0x164dce12db8e42cf5176220,0x16c20e1079430794bf2fe7,0x10635bc5566e6dbf225fc,0x7e955fd12dc6c3c0e84,0x24d04bf7088831f1a0,0x4e1d4742574faaab]
def m14 : List ℤ := raw_ints% [0x0,0xf442918cc7d56d1514601160a400,-0xe9b5597d446e12eccc3c8dd902b00,0x6920d4cea9dc7d91f954c97edb3b80,-0x1d89a8343ead908bae282dcb5f67920,0x5cf023c79b3d0c9bb99a9236d499760,-0xd957b1f963d4292e73c128630a5ae48,0x1878ba4ec9fb29ed7a89e75d0a3dd4a8,-0x22bbd9bf448b8d44554ed26ff29ec504,0x2764e7b9a2e7534f60e6e8b1ba380bb4,-0x23ffec2af09e85dfa301d39356a704ae,0x1a9b3c04963d9ed4c476af9a45b351b6,-0xfe6e1e0eef3c02f1ac8843fa2c96759,0x7a83b20fc8353237601706eb156d295,-0x2f2d1659c0f609ce381825118777b50,0xe5befa40f9cd1131fcfdea6c844948,-0x365d840b680f6cb9102f9e8d6049c7,0x9c6776bd14b0e8b73495ec9b31b73,-0x14b621ba3532fb8625ba0fbd64f86,0x1ef57eb88b8149e2ecb243d7d3de,-0x1ebe6cc7c33b7f0da690664bdf7,0x129a84f783798c06be759ac78b,-0x606e3c44c291a7493ba2c014,0xd9c6d975d03ec6c200a9dc,-0x94dbc484a869685819e5,0xdb0bf3f3591990a79]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 13 52 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 52 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 31 indices rho q14 m14 14 25560004377600 17=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 31 indices rho q14 m14 14 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [0x4e1d4742574faaab,-0x364a0aa61b65c06,0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r15 : List ℤ := raw_ints% [-0x41ce72ca77b5e9a5f0305183000,-0x5663b66733ce0770c438a7c8500,-0x335c533c3a2d6ac6ef1c7fcb5a0,-0x124ba23d7192d3f6a26cc196818,-0x459eff40d5aa7af61f02ec52dc,-0xba74bfd5fe6569b54a485e616,-0x16890c0fd14cb468c203db85b,-0x1fb91d98144a35a7ab620fa1,-0x2048766127c292fd12fb923,-0x172d30e5187bd43fc7fe14,-0xb264aa954c4170ed6601,-0x33ac103b85d758852fd,-0x6d20ed7063d4e63e5]
def m15 : List ℤ := raw_ints% [0x0,-0x10386baa59452c3e665a61276ae400,0xf5dfaa3d0761f41b990056b692db00,-0x6d6e89d8d1890b54b700d1a5fc14a80,0x1e6591ce461930a0cda29fd61d1fe060,-0x5e76c284f36ad6419fc303215a333ca0,0xd9f6b219740242b0832d1ffb3d082c98,-0x182f75f9b832130ac59ce0643eb2a8bb8,0x21c8a625f40086bdd46c41d2096c3cb14,-0x25a6c77231b638f191fd410c532f2e404,0x21bfef52afe946cf592b53ab66f967a82,-0x186aa055f8dc54d7a1ce3837cdff9cc7a,0xe401adb0f34f810a3143a50fe0eb2c4d,-0x6ae8f32ef7027f061c54f5977250b319,0x27f3f05110142d44d6820a6fdbd02694,-0xbc12a2b91f3a0500535b9c6c5c0d57c,0x2acf6cbd51eab5f5665a78479d7eaeb,-0x75c6bd3ee17a68d31a6a289b2cc7a7,0xece6f504d7910be1e6396cfe27382,-0x14d2a2433b717f4e025a4e31f362a,0x133ca3ffbe744f2d7713dab8a293,-0xaad745b62a5d85d30bc8d77757,0x31e1a3ea99ff6dd16dc571db0,-0x63561d5d7bc9aac081ccb88,0x3a48baac3b5dbf50990e1,-0x471d2d2a9a62dbbf65]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 13 54 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 54 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 31 indices rho q15 m15 15 25560004377600 17=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 31 indices rho q15 m15 15 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [-0x6d20ed7063d4e63e5,0x4e1d4742574faaab,-0x364a0aa61b65c06,0x24778c51ea8888,-0x178aa4bd193e7,0xe8095eead45,-0x872a3c3348,0x499051ca2,-0x24ccfae9,0x10886df,-0x670ca,0x20dc,-0x7b,0x1]
def r16 : List ℤ := raw_ints% [0x5bef1a63ebf7e536acb56b98d000,0x7891dafbc280210cbd65d35c5b00,0x479a00f70b98370953339907c960,0x1979352db4eaac0ab589b3d00588,0x60cc71699014d1c27decbeba71c,0x102d398e11150038f5bfb4c66f6,0x1f39bd6799ffe4aa737b54baab,0x2bddc8570b8bd1ea7c4bc6a02,0x2c8972217326fa050eebd42c,0x1fe3a219c36866d613fde72,0xf4b6d6d4126c1c3ee32df,0x46a2e93f9c8ef43bec2e,0x949546641ec94179ee]
def m16 : List ℤ := raw_ints% [0x0,0x113bf264fed97f024cc00739e192400,-0x102cca008c685135d52905c21fc08b00,0x72063eba0502935506a62e969bc90b80,-0x1f53de506c9f639415215cf3278796520,0x6035257fdc5f4ac2fbe1ef03ca28df960,-0xdb2320c27240fe74f9f70ad6134b643c8,0x17f993718dbcfd52732f8490ee683cf028,-0x20f9c4163035c4eee3ba5060212e8121a4,0x242153d52be46ec60c150a9861d058bdd4,-0x1fc8217ef63efbc8284756f396c27236ae,0x168431da6a05148c6bf24932f1c75720b6,-0xcd669e924832d7ccea33ae9edb28141a1,0x5dcf9072a5c666dfab87a8f3623baa93d,-0x2207b8844475962b1c13faabcbad33140,0x9adaf5007c9e28c9f64adb25cc6c06b8,-0x21e7979bc03226c7c776757b8b46361f,0x592c332cd2c3f3b5cdaa8422e15f8ab,-0xaa322c9e957dd2895feea84cdc7626,0xe104e742d8da7fb8590335242a17e,-0xc1320b23ba93ed4e48741cd3a4ef,0x623ece683f38f48030b65a6bea3,-0x19d23eaba6b590b054dfe3a504,0x2d4c9d05d9ced8636975cd4c,-0x16cd96586929a5c10bbaad,0x171222c79c738f4e261]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 13 56 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 56 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 31 indices rho q16 m16 16 25560004377600 17=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 31 indices rho q16 m16 16 25560004377600 17 13
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_16
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<17) : intPolyRF (mz e)=rfPoly (C (25560004377600:ℚ))*rfX^17*(1-rfX)^13*momentRF (key size) (X^e) := by
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
end CatalanCore.Li2.NVMod.FamilySource.V5C18
