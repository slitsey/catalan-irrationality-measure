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
namespace CatalanCore.Li2.NVMod.FamilySource.V7C31
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
noncomputable section
def key (size : ℕ) : TypeKey := ⟨.V,7,31,size⟩
def bases : List ℕ := [0,1,2,3,4,5,6]
def indices : List ℕ := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
def num : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def den : List ℤ := raw_ints% [0x4a662ebc146962cc932400000,0x72f21b60b38b9cb8dea740000,0x544d7543e1eaf976e558c0000,0x27112154ff57984f45671b000,0xcd84b9790e64a0811a031400,0x33084c595baf01939ee29d00,0x9f215054833341febb249c0,0x18f88b2b882cf6eb5021ec0,0x3361e9ac8f4a793d9dc5f0,0x57bc983695ed862f7d330,0x7d6660d4eed48d597054,0x96e3e244f136778cbe4,0x995cfccf6932938d09,0x83d2bbc283fb6c0c0,0x5fbd0ce1af7ff756,0x3a923bd8d9349d4,0x1e0531859b23ef,0xcc88335c53d0,0x477bd1a9338,0x1426de9bcc,0x477cc1b7,0xbff940,0x16ebe,0x1bc,0x1]
def rhoNumerators : List ℤ := raw_ints% [0x1,-0x1,0x1,-0x1,0x37,-0xb,0x8f,-0x8f,0x8f,-0x2cb,0xa16f,-0xbec9,0x10d0971,-0x19789,0x7f5ad,-0x1182e3,0x242f7713,-0x200db3,0x321567b,-0x904903,0x3767d,-0x1277f,0x584005,-0xc8307]
def rhoDenominators : List ℤ := raw_ints% [0x39d9f27efa800,0xa0fa49ba60,0xb901c480,0x260efe0,0x375ba00,0x817e0,0x77880,0xc4e0,0x1c00,0x1a94,0x17bb0,0x8dcc,0x4fc2c0,0x3c54,0xbbb0,0x13fec,0x27fd800,0x2b2a0,0x68e380,0x265320,0x28600,0x34fe0,0x6430380,0xc007160]
def rho (m : ℕ) : ℚ := (rhoNumerators.getD (m-7) 0:ℚ)/(rhoDenominators.getD (m-7) 1:ℚ)
theorem bases_nodup : bases.Nodup := by decide +kernel
theorem indices_nodup : indices.Nodup := by decide +kernel
theorem base_set (size : ℕ) : bases.toFinset=baseIndices (key size) := by
  change bases.toFinset=Finset.range 7
  decide +kernel
theorem indices_set (size : ℕ) : indices.toFinset=poles (key size) := by
  change indices.toFinset=Finset.Ico 7 31
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
theorem cutoff_check : indices.all (fun (m : ℕ)=>decide (m≤30))=true := by decide +kernel
theorem cutoff_bound (m : ℕ) (hm : m∈indices.toFinset) : m≤30 :=
  of_decide_eq_true ((List.all_eq_true.mp cutoff_check) m (List.mem_toFinset.mp hm))
def omegaNums7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens7 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31]
def omega7 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums7 omegaDens7
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_7 : padCoefficients 31 omega7=padCoefficients 31 (omegaCoefficients 30 7) := by decide +kernel
theorem omega_spec_7 : coefficientsPoly omega7=omegaNumerator 30 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_7
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens8 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40]
def omega8 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums8 omegaDens8
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_8 : padCoefficients 31 omega8=padCoefficients 31 (omegaCoefficients 30 8) := by decide +kernel
theorem omega_spec_8 : coefficientsPoly omega8=omegaNumerator 30 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_8
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens9 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51]
def omega9 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums9 omegaDens9
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_9 : padCoefficients 31 omega9=padCoefficients 31 (omegaCoefficients 30 9) := by decide +kernel
theorem omega_spec_9 : coefficientsPoly omega9=omegaNumerator 30 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_9
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums10 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens10 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64]
def omega10 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums10 omegaDens10
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_10 : padCoefficients 31 omega10=padCoefficients 31 (omegaCoefficients 30 10) := by decide +kernel
theorem omega_spec_10 : coefficientsPoly omega10=omegaNumerator 30 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_10
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums11 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens11 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79]
def omega11 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums11 omegaDens11
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_11 : padCoefficients 31 omega11=padCoefficients 31 (omegaCoefficients 30 11) := by decide +kernel
theorem omega_spec_11 : coefficientsPoly omega11=omegaNumerator 30 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_11
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums12 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens12 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90]
def omega12 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums12 omegaDens12
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_12 : padCoefficients 31 omega12=padCoefficients 31 (omegaCoefficients 30 12) := by decide +kernel
theorem omega_spec_12 : coefficientsPoly omega12=omegaNumerator 30 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_12
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums13 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens13 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9]
def omega13 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums13 omegaDens13
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_13 : padCoefficients 31 omega13=padCoefficients 31 (omegaCoefficients 30 13) := by decide +kernel
theorem omega_spec_13 : coefficientsPoly omega13=omegaNumerator 30 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_13
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums14 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens14 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4]
def omega14 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums14 omegaDens14
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_14 : padCoefficients 31 omega14=padCoefficients 31 (omegaCoefficients 30 14) := by decide +kernel
theorem omega_spec_14 : coefficientsPoly omega14=omegaNumerator 30 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_14
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums15 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens15 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1]
def omega15 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums15 omegaDens15
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_15 : padCoefficients 31 omega15=padCoefficients 31 (omegaCoefficients 30 15) := by decide +kernel
theorem omega_spec_15 : coefficientsPoly omega15=omegaNumerator 30 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_15
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums16 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens16 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100]
def omega16 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums16 omegaDens16
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_16 : padCoefficients 31 omega16=padCoefficients 31 (omegaCoefficients 30 16) := by decide +kernel
theorem omega_spec_16 : coefficientsPoly omega16=omegaNumerator 30 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_16
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums17 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens17 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121]
def omega17 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums17 omegaDens17
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_17 : padCoefficients 31 omega17=padCoefficients 31 (omegaCoefficients 30 17) := by decide +kernel
theorem omega_spec_17 : coefficientsPoly omega17=omegaNumerator 30 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_17
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums18 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens18 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144]
def omega18 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums18 omegaDens18
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_18 : padCoefficients 31 omega18=padCoefficients 31 (omegaCoefficients 30 18) := by decide +kernel
theorem omega_spec_18 : coefficientsPoly omega18=omegaNumerator 30 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_18
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums19 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens19 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169]
def omega19 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums19 omegaDens19
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_19 : padCoefficients 31 omega19=padCoefficients 31 (omegaCoefficients 30 19) := by decide +kernel
theorem omega_spec_19 : coefficientsPoly omega19=omegaNumerator 30 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_19
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums20 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens20 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190]
def omega20 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums20 omegaDens20
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_20 : padCoefficients 31 omega20=padCoefficients 31 (omegaCoefficients 30 20) := by decide +kernel
theorem omega_spec_20 : coefficientsPoly omega20=omegaNumerator 30 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_20
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums21 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens21 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9]
def omega21 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums21 omegaDens21
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_21 : padCoefficients 31 omega21=padCoefficients 31 (omegaCoefficients 30 21) := by decide +kernel
theorem omega_spec_21 : coefficientsPoly omega21=omegaNumerator 30 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_21
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums22 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens22 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4]
def omega22 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums22 omegaDens22
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_22 : padCoefficients 31 omega22=padCoefficients 31 (omegaCoefficients 30 22) := by decide +kernel
theorem omega_spec_22 : coefficientsPoly omega22=omegaNumerator 30 22 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_22
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums23 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens23 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211]
def omega23 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums23 omegaDens23
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_23 : padCoefficients 31 omega23=padCoefficients 31 (omegaCoefficients 30 23) := by decide +kernel
theorem omega_spec_23 : coefficientsPoly omega23=omegaNumerator 30 23 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_23
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums24 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens24 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240]
def omega24 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums24 omegaDens24
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_24 : padCoefficients 31 omega24=padCoefficients 31 (omegaCoefficients 30 24) := by decide +kernel
theorem omega_spec_24 : coefficientsPoly omega24=omegaNumerator 30 24 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_24
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums25 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens25 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271]
def omega25 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums25 omegaDens25
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_25 : padCoefficients 31 omega25=padCoefficients 31 (omegaCoefficients 30 25) := by decide +kernel
theorem omega_spec_25 : coefficientsPoly omega25=omegaNumerator 30 25 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_25
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums26 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens26 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4]
def omega26 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums26 omegaDens26
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_26 : padCoefficients 31 omega26=padCoefficients 31 (omegaCoefficients 30 26) := by decide +kernel
theorem omega_spec_26 : coefficientsPoly omega26=omegaNumerator 30 26 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_26
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums27 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens27 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9]
def omega27 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums27 omegaDens27
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_27 : padCoefficients 31 omega27=padCoefficients 31 (omegaCoefficients 30 27) := by decide +kernel
theorem omega_spec_27 : coefficientsPoly omega27=omegaNumerator 30 27 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_27
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums28 : List ℤ := raw_ints% [0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens28 : List ℤ := raw_ints% [0x1,0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310]
def omega28 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums28 omegaDens28
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_28 : padCoefficients 31 omega28=padCoefficients 31 (omegaCoefficients 30 28) := by decide +kernel
theorem omega_spec_28 : coefficientsPoly omega28=omegaNumerator 30 28 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_28
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums29 : List ℤ := raw_ints% [0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens29 : List ℤ := raw_ints% [0x1,0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349]
def omega29 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums29 omegaDens29
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_29 : padCoefficients 31 omega29=padCoefficients 31 (omegaCoefficients 30 29) := by decide +kernel
theorem omega_spec_29 : coefficientsPoly omega29=omegaNumerator 30 29 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_29
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def omegaNums30 : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1]
def omegaDens30 : List ℤ := raw_ints% [0x1,0x1,0x4,0x9,0x10,0x19,0x24,0x31,0x40,0x51,0x64,0x79,0x90,0xa9,0xc4,0xe1,0x100,0x121,0x144,0x169,0x190,0x1b9,0x1e4,0x211,0x240,0x271,0x2a4,0x2d9,0x310,0x349,0x384]
def omega30 : List ℚ := List.zipWith (fun (n d : ℤ)=>(n:ℚ)/(d:ℚ)) omegaNums30 omegaDens30
-- kcost: 1 s estimated; one shared pole numerator list
set_option trace.profiler true in
theorem omega_ok_30 : padCoefficients 31 omega30=padCoefficients 31 (omegaCoefficients 30 30) := by decide +kernel
theorem omega_spec_30 : coefficientsPoly omega30=omegaNumerator 30 30 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) omega_ok_30
  simpa only [padCoefficients_spec,omegaCoefficients_spec] using h
def liRaw0 : List ℤ := raw_ints% [0x0,0x1,-0x15,0xd2,-0x532,0x1761,-0x4f7d,0xd3f8,-0x1c638,0x31ae2,-0x47c2a,0x561cc,-0x561cc,0x47c2a,-0x31ae2,0x1c638,-0xd3f8,0x4f7d,-0x1761,0x532,-0xd2,0x15,-0x1]
def li0 : List ℚ := liRaw0.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_0 : padCoefficients 23 li0=padCoefficients 23 (liCoefficients 22 0) := by decide +kernel
theorem li_spec_0 : coefficientsPoly li0=liNumerator 22 0 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_0
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw1 : List ℤ := raw_ints% [0x0,0x1,-0x14,0xbe,-0x474,0x12ed,-0x3c90,0x9768,-0x12ed0,0x1ec12,-0x29018,0x2d1b4,-0x29018,0x1ec12,-0x12ed0,0x9768,-0x3c90,0x12ed,-0x474,0xbe,-0x14,0x1]
def li1 : List ℚ := liRaw1.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_1 : padCoefficients 23 li1=padCoefficients 23 (liCoefficients 22 1) := by decide +kernel
theorem li_spec_1 : coefficientsPoly li1=liNumerator 22 1 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_1
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw2 : List ℤ := raw_ints% [0x0,0x1,-0x12,0x98,-0x31e,0xb5b,-0x1e48,0x3c90,-0x5ad8,0x626a,-0x419c,0x0,0x419c,-0x626a,0x5ad8,-0x3c90,0x1e48,-0xb5b,0x31e,-0x98,0x12,-0x1]
def li2 : List ℚ := liRaw2.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_2 : padCoefficients 23 li2=padCoefficients 23 (liCoefficients 22 2) := by decide +kernel
theorem li_spec_2 : coefficientsPoly li2=liNumerator 22 2 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_2
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw3 : List ℤ := raw_ints% [0x0,0x1,-0xe,0x52,-0xde,-0x33,0xb28,-0x3168,0x8448,-0xfdce,0x1717c,-0x1a1d4,0x1717c,-0xfdce,0x8448,-0x3168,0xb28,-0x33,-0xde,0x52,-0xe,0x1]
def li3 : List ℚ := liRaw3.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_3 : padCoefficients 23 li3=padCoefficients 23 (liCoefficients 22 3) := by decide +kernel
theorem li_spec_3 : coefficientsPoly li3=liNumerator 22 3 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_3
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw4 : List ℤ := raw_ints% [0x0,0x1,-0x6,-0x28,0x276,-0xe25,0x3168,-0x75f0,0xc738,-0xe916,0xa24c,0x0,-0xa24c,0xe916,-0xc738,0x75f0,-0x3168,0xe25,-0x276,0x28,0x6,-0x1]
def li4 : List ℚ := liRaw4.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_4 : padCoefficients 23 li4=padCoefficients 23 (liCoefficients 22 4) := by decide +kernel
theorem li_spec_4 : coefficientsPoly li4=liNumerator 22 4 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_4
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw5 : List ℤ := raw_ints% [0x0,0x1,0xa,-0xe6,0x5fa,-0x1473,0x2388,0x78,-0xaed8,0x20472,-0x37ab4,0x420dc,-0x37ab4,0x20472,-0xaed8,0x78,0x2388,-0x1473,0x5fa,-0xe6,0xa,0x1]
def li5 : List ℚ := liRaw5.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_5 : padCoefficients 23 li5=padCoefficients 23 (liCoefficients 22 5) := by decide +kernel
theorem li_spec_5 : coefficientsPoly li5=liNumerator 22 5 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_5
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw6 : List ℤ := raw_ints% [0x0,0x1,0x2a,-0x1c0,0x516,0xa6b,-0x7c08,0x1bfc0,-0x3aff8,0x4e83a,-0x3a904,0x0,0x3a904,-0x4e83a,0x3aff8,-0x1bfc0,0x7c08,-0xa6b,-0x516,0x1c0,-0x2a,-0x1]
def li6 : List ℚ := liRaw6.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_6 : padCoefficients 23 li6=padCoefficients 23 (liCoefficients 22 6) := by decide +kernel
theorem li_spec_6 : coefficientsPoly li6=liNumerator 22 6 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_6
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw7 : List ℤ := raw_ints% [0x0,0x1,0x6a,-0x18e,-0xe76,0x812d,-0x1b5e8,0x2c7d8,-0x7ba8,-0x7f12e,0x133f9c,-0x18ac94,0x133f9c,-0x7f12e,-0x7ba8,0x2c7d8,-0x1b5e8,0x812d,-0xe76,-0x18e,0x6a,0x1]
def li7 : List ℚ := liRaw7.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_7 : padCoefficients 23 li7=padCoefficients 23 (liCoefficients 22 7) := by decide +kernel
theorem li_spec_7 : coefficientsPoly li7=liNumerator 22 7 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_7
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw8 : List ℤ := raw_ints% [0x0,0x1,0xea,0x488,-0x52da,0x12ebb,-0x80b8,-0x86850,0x1d7018,-0x30cdb6,0x286f0c,0x0,-0x286f0c,0x30cdb6,-0x1d7018,0x86850,0x80b8,-0x12ebb,0x52da,-0x488,-0xea,-0x1]
def li8 : List ℚ := liRaw8.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_8 : padCoefficients 23 li8=padCoefficients 23 (liCoefficients 22 8) := by decide +kernel
theorem li_spec_8 : coefficientsPoly li8=liNumerator 22 8 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_8
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw9 : List ℤ := raw_ints% [0x0,0x1,0x1ea,0x21ca,-0xd386,-0xbd33,0x1058e8,-0x328cc8,0x3ad748,0x1fbd32,-0xc65e94,0x11ed5fc,-0xc65e94,0x1fbd32,0x3ad748,-0x328cc8,0x1058e8,-0xbd33,-0xd386,0x21ca,0x1ea,0x1]
def li9 : List ℚ := liRaw9.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_9 : padCoefficients 23 li9=padCoefficients 23 (liCoefficients 22 9) := by decide +kernel
theorem li_spec_9 : coefficientsPoly li9=liNumerator 22 9 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_9
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw10 : List ℤ := raw_ints% [0x0,0x1,0x3ea,0x8f90,-0x3c8a,-0x12cdf5,0x42b718,-0x1993e0,-0x1391958,0x31c535a,-0x306c2e4,0x0,0x306c2e4,-0x31c535a,0x1391958,0x1993e0,-0x42b718,0x12cdf5,0x3c8a,-0x8f90,-0x3ea,-0x1]
def li10 : List ℚ := liRaw10.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_10 : padCoefficients 23 li10=padCoefficients 23 (liCoefficients 22 10) := by decide +kernel
theorem li_spec_10 : coefficientsPoly li10=liNumerator 22 10 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_10
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw11 : List ℤ := raw_ints% [0x0,0x1,0x7ea,0x204e2,0xbba6a,-0x568d13,-0x5efc8,0x3727698,-0x7d5fe48,0x3098d12,0xd362bbc,-0x171af6f4,0xd362bbc,0x3098d12,-0x7d5fe48,0x3727698,-0x5efc8,-0x568d13,0xbba6a,0x204e2,0x7ea,0x1]
def li11 : List ℚ := liRaw11.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_11 : padCoefficients 23 li11=padCoefficients 23 (liCoefficients 22 11) := by decide +kernel
theorem li_spec_11 : coefficientsPoly li11=liNumerator 22 11 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_11
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw12 : List ℤ := raw_ints% [0x0,0x1,0xfea,0x6bcd8,0x5c0346,-0x81a2a5,-0x6649f98,0x115da210,0x662a2b8,-0x4bfb4f96,0x5f9e8fac,0x0,-0x5f9e8fac,0x4bfb4f96,-0x662a2b8,-0x115da210,0x6649f98,0x81a2a5,-0x5c0346,-0x6bcd8,-0xfea,-0x1]
def li12 : List ℚ := liRaw12.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_12 : padCoefficients 23 li12=padCoefficients 23 (liCoefficients 22 12) := by decide +kernel
theorem li_spec_12 : coefficientsPoly li12=liNumerator 22 12 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_12
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw13 : List ℤ := raw_ints% [0x0,0x1,0x1fea,0x1594ba,0x205a5da,0x5f5b38d,-0x2901d6f8,-0x15bc6208,0x121d532a8,-0x1309bb38e,-0x1502d2174,0x32b419a9c,-0x1502d2174,-0x1309bb38e,0x121d532a8,-0x15bc6208,-0x2901d6f8,0x5f5b38d,0x205a5da,0x1594ba,0x1fea,0x1]
def li13 : List ℚ := liRaw13.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_13 : padCoefficients 23 li13=padCoefficients 23 (liCoefficients 22 13) := by decide +kernel
theorem li_spec_13 : coefficientsPoly li13=liNumerator 22 13 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_13
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw14 : List ℤ := raw_ints% [0x0,0x1,0x3fea,0x437c60,0x9f41d96,0x4c2648ab,-0x4493d4c8,-0x36cd7f280,0x45bc7e448,0x97ff7597a,-0x1319b41344,0x0,0x1319b41344,-0x97ff7597a,-0x45bc7e448,0x36cd7f280,0x4493d4c8,-0x4c2648ab,-0x9f41d96,-0x437c60,-0x3fea,-0x1]
def li14 : List ℚ := liRaw14.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_14 : padCoefficients 23 li14=padCoefficients 23 (liCoefficients 22 14) := by decide +kernel
theorem li_spec_14 : coefficientsPoly li14=liNumerator 22 14 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_14
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw15 : List ℤ := raw_ints% [0x0,0x1,0x7fea,0xcff352,0x2da2a4ca,0x25d8c24ad,0x5d09ffb58,-0x167284f2a8,-0x26f4ed05e8,0x6b8fb39b52,0x280e3a65dc,-0xbd26368154,0x280e3a65dc,0x6b8fb39b52,-0x26f4ed05e8,-0x167284f2a8,0x5d09ffb58,0x25d8c24ad,0x2da2a4ca,0xcff352,0x7fea,0x1]
def li15 : List ℚ := liRaw15.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_15 : padCoefficients 23 li15=padCoefficients 23 (liCoefficients 22 15) := by decide +kernel
theorem li_spec_15 : coefficientsPoly li15=liNumerator 22 15 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_15
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw16 : List ℤ := raw_ints% [0x0,0x1,0xffea,0x27ad828,0xc8747a66,0xfd1a0c7fb,0x5aebaf1b88,0x1ad40c2e70,-0x26d892638a8,-0xc6e0cc1576,0x63ff99ac84c,0x0,-0x63ff99ac84c,0xc6e0cc1576,0x26d892638a8,-0x1ad40c2e70,-0x5aebaf1b88,-0xfd1a0c7fb,-0xc8747a66,-0x27ad828,-0xffea,-0x1]
def li16 : List ℚ := liRaw16.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_16 : padCoefficients 23 li16=padCoefficients 23 (liCoefficients 22 16) := by decide +kernel
theorem li_spec_16 : coefficientsPoly li16=liNumerator 22 16 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_16
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw17 : List ℤ := raw_ints% [0x0,0x1,0x1ffea,0x78686aa,0x358767b3a,0x6088cafe4d,0x38efa92eb28,0x9f981d9e8b8,-0x7e05aa123f8,-0x30dbc1e4fe4e,0x38a93c9bdac,0x4e8a470b213c,0x38a93c9bdac,-0x30dbc1e4fe4e,-0x7e05aa123f8,0x9f981d9e8b8,0x38efa92eb28,0x6088cafe4d,0x358767b3a,0x78686aa,0x1ffea,0x1]
def li17 : List ℚ := liRaw17.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_17 : padCoefficients 23 li17=padCoefficients 23 (liCoefficients 22 17) := by decide +kernel
theorem li_spec_17 : coefficientsPoly li17=liNumerator 22 17 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_17
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw18 : List ℤ := raw_ints% [0x0,0x1,0x3ffea,0x16bf9230,0xe07957db6,0x22cebe11f4b,0x1defe0cd8558,0x9cb216f194e0,0xf34dddad17e8,-0x132b0e82fd066,-0x38a6ffaef51a4,0x0,0x38a6ffaef51a4,0x132b0e82fd066,-0xf34dddad17e8,-0x9cb216f194e0,-0x1defe0cd8558,-0x22cebe11f4b,-0xe07957db6,-0x16bf9230,-0x3ffea,-0x1]
def li18 : List ℚ := liRaw18.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_18 : padCoefficients 23 li18=padCoefficients 23 (liCoefficients 22 18) := by decide +kernel
theorem li_spec_18 : coefficientsPoly li18=liNumerator 22 18 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_18
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw19 : List ℤ := raw_ints% [0x0,0x1,0x7ffea,0x4496b4c2,0x3a1324852a,0xc17370cf86d,0xe4b225d12c78,0x70c8ed3449418,0x17d56d18d50c78,0x1a5b770e9e0792,-0x189fe48928be04,-0x431d244c6091b4,-0x189fe48928be04,0x1a5b770e9e0792,0x17d56d18d50c78,0x70c8ed3449418,0xe4b225d12c78,0xc17370cf86d,0x3a1324852a,0x4496b4c2,0x7ffea,0x1]
def li19 : List ℚ := liRaw19.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_19 : padCoefficients 23 li19=padCoefficients 23 (liCoefficients 22 19) := by decide +kernel
theorem li_spec_19 : coefficientsPoly li19=liNumerator 22 19 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_19
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw20 : List ℤ := raw_ints% [0x0,0x1,0xfffea,0xce741c78,0xee32359b86,0x41779e07d29b,0x66b2f28cb5ca8,0x460e394cbe30d0,0x16e7600746b41f8,0x3a9592753a034aa,0x409bf45b60f2aec,0x0,-0x409bf45b60f2aec,-0x3a9592753a034aa,-0x16e7600746b41f8,-0x460e394cbe30d0,-0x66b2f28cb5ca8,-0x41779e07d29b,-0xee32359b86,-0xce741c78,-0xfffea,-0x1]
def li20 : List ℚ := liRaw20.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_20 : padCoefficients 23 li20=padCoefficients 23 (liCoefficients 22 20) := by decide +kernel
theorem li_spec_20 : coefficientsPoly li20=liNumerator 22 20 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_20
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def liRaw21 : List ℤ := raw_ints% [0x0,0x1,0x1fffea,0x26cbc539a,0x3ca8830de9a,0x15be0261ceb0d,0x2c37ec99661348,0x27d4e703f4f3378,0x120bd3cf61ce1f68,0x470a6a37b04d94f2,0x9f0569f00c07eecc,0xcf7a613494bdf1dc,0x9f0569f00c07eecc,0x470a6a37b04d94f2,0x120bd3cf61ce1f68,0x27d4e703f4f3378,0x2c37ec99661348,0x15be0261ceb0d,0x3ca8830de9a,0x26cbc539a,0x1fffea,0x1]
def li21 : List ℚ := liRaw21.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 3 s estimated; one shared polylog numerator list
set_option trace.profiler true in
theorem li_ok_21 : padCoefficients 23 li21=padCoefficients 23 (liCoefficients 22 21) := by decide +kernel
theorem li_spec_21 : coefficientsPoly li21=liNumerator 22 21 := by
  have h:=congrArg (coefficientsPoly (R:=ℚ)) li_ok_21
  simpa only [padCoefficients_spec,liCoefficients_spec] using h
def powerRaw : List ℤ := raw_ints% [0x1,-0x16,0xe7,-0x604,0x1c93,-0x66de,0x12375,-0x29a30,0x4e11a,-0x7970c,0x9ddf6,-0xac398,0x9ddf6,-0x7970c,0x4e11a,-0x29a30,0x12375,-0x66de,0x1c93,-0x604,0xe7,-0x16,0x1]
def power : List ℚ := powerRaw.map (fun (z : ℤ)=>(z:ℚ))
-- kcost: 1 s estimated; shared clearing power
theorem power_ok : power=powerCoefficients 22 [1,-1] := by decide +kernel
theorem power_spec : coefficientsPoly power=(1-X:ℚ[X])^22 := by
  rw [power_ok,powerCoefficients_spec]
  congr 1
  simp [coefficientsPoly]
  ring
def omegaCache : ℕ→List ℚ
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
  | 19=>omega19
  | 20=>omega20
  | 21=>omega21
  | 22=>omega22
  | 23=>omega23
  | 24=>omega24
  | 25=>omega25
  | 26=>omega26
  | 27=>omega27
  | 28=>omega28
  | 29=>omega29
  | 30=>omega30
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
  | 13=>li13
  | 14=>li14
  | 15=>li15
  | 16=>li16
  | 17=>li17
  | 18=>li18
  | 19=>li19
  | 20=>li20
  | 21=>li21
  | _=>[]
def cache : MomentCache := ⟨power,omegaCache,liCache⟩
theorem cache_omega (m : ℕ) (hm : m∈indices.toFinset) : coefficientsPoly (cache.omega m)=omegaNumerator 30 m := by
  have hb:=hm
  rw [indices_set 0] at hb
  change m∈Finset.Ico 7 31 at hb
  obtain ⟨hlo,hhi⟩:=Finset.mem_Ico.mp hb
  interval_cases m
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
  · exact omega_spec_19
  · exact omega_spec_20
  · exact omega_spec_21
  · exact omega_spec_22
  · exact omega_spec_23
  · exact omega_spec_24
  · exact omega_spec_25
  · exact omega_spec_26
  · exact omega_spec_27
  · exact omega_spec_28
  · exact omega_spec_29
  · exact omega_spec_30
theorem cache_li (j : ℕ) (hj : j<22) : coefficientsPoly (cache.li j)=liNumerator 22 j := by
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
  · exact li_spec_13
  · exact li_spec_14
  · exact li_spec_15
  · exact li_spec_16
  · exact li_spec_17
  · exact li_spec_18
  · exact li_spec_19
  · exact li_spec_20
  · exact li_spec_21
def q0 : List ℤ := raw_ints% []
def r0 : List ℤ := raw_ints% [0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m0 : List ℤ := raw_ints% [0x0,-0x5dba19de433bb79144308f24000,0xce9a548a9c3cfc5ab349e6c2e000,-0xdd96475f6eb859d734d690efc0400,0x9a11acff41488f17cd39deaa06e000,-0x4e11704e7a7655fb04d9da7c2b1f200,0x1eb9c89b37d8d5c3b54a13a56a32c400,-0x9c6abfcf5793c0425808472f7517d740,0x295871192f461454ea220985334b03f80,-0x94280e7161c1ca7e8a0787e8a8cb647c0,0x1c88205bf620985593166131b7dfeb1b00,-0x4c7566ef462c02239f3160e9f82562da40,0xb3cac6405dddea669fea511328056b4c80,-0x175a1c8b31d91395931986030205572b840,0x2b21b89ca928b1cd0776416416ebb7b2b00,-0x472134510607644739c15ef24c79df9830c,0x691dc059df924f72aaf672ee785994064c8,-0x8b9ae79cf2583d57ffa7f6aabd8cf02eca4,0xa6fef850e55b92744446907b632777ad110,-0xb436f82d62a04fb0ca310fb48bced8d93b8,0xafa496f773f6ab69aa72589207125ab2780,-0x9ab339a936810bb530a2c6bbca97a394198,0x7b261ad6707d2f5bef1bb3f09c35a23b050,-0x58933aeae9088e6128b56a9aca789b3c42f,0x39846422b34fcced9b2f2e6074da9e9ae7a,-0x21ad8ab5da9359ced9bbb29876e788369b9,0x11bffa1117ad3ce6f86182f089c663693ec,-0x866cbd072e6715e3b6e16cba6fe551f1f1,0x38fa4ec4c7e73a17dc9492f29745e4a04a,-0x158ce75d800abc8714478a76e6e5355af7,0x73df19bb776ec650c3bc40b76d31f16b0,-0x226a94f944e7608e5de289b95d3c7c432,0x8fa839a57eca41800f160fbdbf95ecdc,-0x20aaf99d27714a28cc80374cda75168e,0x66a72243510f722a76823174a653f18,-0x1137283d7a0bfd1d3e9406997c3526a,0x26e55b1cfa97e48ec15d4678b6e6c4,-0x48b2e6c4de451ad0a3a93605cd036,0x6de17d816ee8c527537adc607520,-0x82572437b21e5e872c5dec23203,0x747b91ca6583463fb38414b662,-0x49fda20c86d20f12e67d9caa5,0x1e9545eb26f7fefe6da8a1cc,-0x71b3263934087d9a5734fd,0xb3d238532fdd5863c2f2,-0x3cb8dd728eb34a29ab]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 0
theorem quotient_ok_0 : quotientCheck 24 41 0 num den q0 r0=true := by decide +kernel
theorem quotient_source_0 (size : ℕ) : (coefficientsPoly q0).map (Int.castRingHom ℚ)=polyPart (key size) (X^0) :=
  quotient_from_check (key size) 41 0 num den q0 r0 (num_source size) (den_source size) quotient_ok_0
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_0 : cachedMomentCheck cache 53 indices rho q0 m0 0 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_0 (size : ℕ) : intPolyRF (coefficientsPoly m0)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^0) :=
  moment_from_cached_check cache (key size) 53 indices rho q0 m0 0 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_0 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_0
def q1 : List ℤ := raw_ints% []
def r1 : List ℤ := raw_ints% [0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m1 : List ℤ := raw_ints% [0x0,0xafbcf080be0ff8305fdb0c638000,-0x17e6e48eddd64dc3cfc81126a85000,0x194d4a9387907e8eca22162441ed400,-0x115bf570af69e7d99afbe9c771d3c400,0x8ad606cbc6075d375bdaf868fe7b5800,-0x35e3d3bb43a6761ac259b00ba61747000,0x10e7c7364ce29b9d7550d4e2aafa1ca1c0,-0x4678d78f01515f1335462310890f262780,0xf8d49913136d2e09f1a17632d7208454c0,-0x2f33d77f239f637bda409d29fab64a46800,0x7c8eb3185f0fbc00c57de88411780015480,-0x1205051c994e74616d58d55f4a0644a3d600,0x24d8f07f291e73b40a591afe99d01416b380,-0x42f10a335f5e4e54c31c20eac53f42ddc800,0x6c89ddd4bcd64565772a54b142450c8f68d4,-0x9da1bf456412535996ad8984d3cc692e44b8,0xcda4673c98f8cb96b718b8fd9ed1f6fddf5c,-0xf182c2325519202601392b18789ab845f930,0xffbefda5d6314b952cbb69d6f0e4f90384f8,-0xf4734642dea43697c4112d30d4ca7f9916a0,0xd30598b79e30083986a09269bd8564b6e658,-0xa489319f35a8aa2aa573793c8d89a15f67f0,0x73d522352d2351f3b7ef9585d11d28894ce9,-0x4990d5a162366af1f39ac6156cb87d056b96,0x2a1838573b845c4e57105a9a392e94be31cf,-0x15a968f5773d6ecc3a14683ef9699c513e74,0xa004c5450fd7c6a5b0114437442e82fbd67,-0x4216bab37513efed1dac0423d2f6a388526,0x1853dec4e7833570ba7eca41af9e53f6f11,-0x7f23972d6ad6421abf3cad99200d3c3150,0x24a6e991d423dc677310e4f54e2583569e,-0x943f6aa3a0ddfa24bb72ba088d1d386c4,0x209b7d281e16511e0ef5e08c43108fec2,-0x62e6705ab2756fcf861b38d522efe168,0xff89f1e60671b6a1bd17eda9c819376,-0x22a6802a3b29778b4c9b681349e4dbc,0x3dfc8570c057ae419af87e553f224a,-0x5952620a13687c348f34dbea600a0,0x6488c29f26f5c5bc054d0f8368b5,-0x54bf35a966aad647b89eeeb8b6e,0x3264fe121fcbafc76170ab6083,-0x134e6db86f16e740b8a8e5114,0x41a006625183549460eeadb,-0x5d14b815e63f015a99e7e,0x1b6ead6296f4760379d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 1
theorem quotient_ok_1 : quotientCheck 24 42 1 num den q1 r1=true := by decide +kernel
theorem quotient_source_1 (size : ℕ) : (coefficientsPoly q1).map (Int.castRingHom ℚ)=polyPart (key size) (X^1) :=
  quotient_from_check (key size) 42 1 num den q1 r1 (num_source size) (den_source size) quotient_ok_1
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_1 : cachedMomentCheck cache 53 indices rho q1 m1 1 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_1 (size : ℕ) : intPolyRF (coefficientsPoly m1)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^1) :=
  moment_from_cached_check cache (key size) 53 indices rho q1 m1 1 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_1 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_1
def q2 : List ℤ := raw_ints% []
def r2 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m2 : List ℤ := raw_ints% [0x0,-0x1498242f1645df15ab3bab73a90000,0x2c416319e116caa84a5cecdae853000,-0x2e4022426144b803281ed522a127c400,0x1f51cf320de043f079213fc2dde2cd400,-0xf72bf1ef52e6af376f8c1e699a9586a00,0x5ea525e8dc336b626a4c86198f70f4c400,-0x1d47f55a125256d81b399b4d470479e0d40,0x7857f354b36a9ddd58920b0614d9207bc80,-0x1a2cfe64f8d41d179efc41e8e7259979adc0,0x4e479fbdf3dbfadbbc2b47f922e9822f7f00,-0xcb75454a725f1c8869d29e014f2a825036c0,0x1cfb2d106e2ad0febd8c6053bb6975ec27c80,-0x3a5400ffa0c1ade06a92ba6af93038fb749c0,0x68411c690aed35319ce57357755700789c100,-0xa63c83bcae639b22efa5556a8e4fba185a74c,0xed52139bf374409746a818647e5780d264688,-0x13031005242344dced610d9a13818980b8ce64,0x15ed41d37c2afdfef773584f09f6fc7d037d10,-0x16ca253941c6437a879cfb8c1afd51866736d8,0x155e255b324ae8a330231c75453d1ac73f0f80,-0x121539b18aa34256791713329315a9f5f26ef8,0xdd01e6c609caca5abb94e775237638992bed0,-0x98518bd5e1b2b477453d3f8953b572fd260ff,0x5ea1e3eefd17e7fa872c2ec7d4d6676633d1a,-0x34ed196c72806e5ef00869e07d85b11b73669,0x1a98b1c335ff46c1965c1e15f24a5bca70cac,-0xbfabd9692bcf6a12ec5ba5ec70c6e08524c1,0x4d24ba366d69311d8b4292a1a6e9cfba41aa,-0x1ba3d00bd43e06195e68a68916f27a929827,0x8c69963df049310448438eca4a63507ecb0,-0x274a090e8517f6285151f67a86159c39492,0x99fd7e62cfa63e84f82115c3e2eb8fb9dc,-0x20c271e34f79f5698c93aa71deeb2e6f2e,0x5fe5ea430fb821896aa6d16b0b2b00998,-0xee8f1c272d38d209093814ffd80e4e2a,0x1f0e203c069658264624c3068cefa484,-0x3527dca89dfce09e49f03fd084bccf6,0x48febcf421a64ece4c009cc157d0a0,-0x4de9b01ddf6f6915167de5309e393,0x3de82de9ef6d7270df17a18bdc02,-0x226e7d255ff42eb7921124f7495,0xc3686776ff61d37f2965d688c,-0x25e91cca79666f2bf029cdcd,0x302c10309da9c79dfd37d2,-0xc63032bb4e0e60ee1db]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 2
theorem quotient_ok_2 : quotientCheck 24 43 2 num den q2 r2=true := by decide +kernel
theorem quotient_source_2 (size : ℕ) : (coefficientsPoly q2).map (Int.castRingHom ℚ)=polyPart (key size) (X^2) :=
  quotient_from_check (key size) 43 2 num den q2 r2 (num_source size) (den_source size) quotient_ok_2
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_2 : cachedMomentCheck cache 53 indices rho q2 m2 2 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_2 (size : ℕ) : intPolyRF (coefficientsPoly m2)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^2) :=
  moment_from_cached_check cache (key size) 53 indices rho q2 m2 2 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_2 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_2
def q3 : List ℤ := raw_ints% []
def r3 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m3 : List ℤ := raw_ints% [0x0,0x269d43d849c30248a10fe178dce0000,-0x51f670b1e81dbf051e14bf1dd8b23000,0x5496ad8f1c5fdfeb5d0fba1ab89abb400,-0x388d5a59c57480f3920a3aa4951a109c00,0x1b88340fd5ce5834bcde07f49a78f2c9800,-0xa6719243a1f354c4c9c48bc7c76533a0800,0x32cc2d83fd7fe1d41aef0e52552877b04bc0,-0xcde4097b49b560559ed0d38d9e4850127980,0x2c268f783012ee72615bd0849c9ca54f754c0,-0x8220a84cb58f2757a88aa6c91f7fccae46a00,0x14d37b37e332c0b51341b52e0ce7423f448000,-0x2ebefe844687b39b6c00475da8f8e6d999cb00,0x5c9f7983ab10a22bfbd556cc4d55ac21c31000,-0xa2eb2fc28b24b89fc09289b28c5b44d08f0600,0xff898a7dc278cdf1d805cf7499afc9ad536494,-0x166b09108d38afedbce5cbae1db5d8ea8fe14b8,0x1c3d51c77bb93251e2edaccd5b2f3c09dec0f1c,-0x1ffdc09666a0485bb3a56992ed2e2a39f4748b0,0x20a473f24e3ff68347dd94afc35fcacd512f3d8,-0x1e07679158db2d80dfb6cde202873861a4ca6e0,0x18eb0681b1df66f46ef5cda514aff2fe0aa7678,-0x12a6b58a481ac87925c42ac35bd8dbb0721be70,0xc9634747593e13b45a8111a5bdb70913a8c819,-0x7a6aba360f916ec1edce65fb98c8acbe1acab6,0x42ee4348912ec7bbb0603937d9a27e2d4b089f,-0x20d988445970c8233a9db4ff4f3c09f8fc9834,0xe6fbb64ceae1b405250d9448011bfa25bcc97,-0x5a9b2d150ce2e1d414fa08002014c1a224606,0x1f99d8b3d51204e9c6c4a55253f82b0eb5161,-0x9c0efe1c6b1e7fcd1d02834118bd6b8d2d50,0x2a62b582c6e843b5fa2ec10206e97b42863e,-0xa0fa47df627f50a150f6173a788ab0ff104,0x211f07d43528013bf64a62e475a7d03caa2,-0x5d91502daec8176d022e00d06ca8e9a768,0xe00fae080e8b147a6589782a119c16db6,-0x1bfeddec4321c91166e66ff0ec7d7aebc,0x2dd59e10ee5cb2c92f2bbfc526b1160a,-0x3bf4b00acea85956b534b5d99cbb220,0x3ca796388ed461ee2fedbad172df25,-0x2d651dc399b9659b4a9c8c21b400e,0x1798186843e1691a82fc6892d713,-0x7bd89e283e7620d3f5c51ee5d4,0x15eaa7fafd600369e6dfdc00b,-0x18ecb4a32f6e54d7731bf5e,0x59721a5088bf1b566bed]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 3
theorem quotient_ok_3 : quotientCheck 24 44 3 num den q3 r3=true := by decide +kernel
theorem quotient_source_3 (size : ℕ) : (coefficientsPoly q3).map (Int.castRingHom ℚ)=polyPart (key size) (X^3) :=
  quotient_from_check (key size) 44 3 num den q3 r3 (num_source size) (den_source size) quotient_ok_3
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_3 : cachedMomentCheck cache 53 indices rho q3 m3 3 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_3 (size : ℕ) : intPolyRF (coefficientsPoly m3)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^3) :=
  moment_from_cached_check cache (key size) 53 indices rho q3 m3 3 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_3 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_3
def q4 : List ℤ := raw_ints% []
def r4 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m4 : List ℤ := raw_ints% [0x0,-0x4866df358a4da4482dfdc6c29e240000,0x97d688c614fa3baaf234b3ce1d86ff000,-0x9ac9aa3e9dc72d6ce5e97ce8c63d166400,0x6631c134e45e8df9eaea348cfd189e1c400,-0x311eac839a922988d51cc91e155a78f4ea00,0x125185c990a4248950305db63be3d7cecf400,-0x5843a1e6fdd796587d137b7de163fb0592b40,0x160e5fcf044316125c00cf4d2bf911a1373480,-0x4aa00d18c3998bd51399e3774aa21a4bc84dc0,0xd8d37997976adac4ff8876a611aa4afbe11700,-0x22328d2e64439072ff81356cb94e7ae97651540,0x4b9dd928bedea13db79d3c2b5071a7cedcb4780,-0x938a42502f79daf04a145304ad3c26bdfdb5b40,0xff732739db6123dbf5acb2f1868d6bf0fbfe700,-0x18a39f2af3f8e209a33cd29cb76493835c58ff8c,0x220369d91595956291e4eebbeaf9c39ec1547f08,-0x2a1dec0c7759203733401ce8e6e1017902d4e4a4,0x2ee05a4cfaf300d676482f441a7385754efc6610,-0x2ef77d7ac64593ee99f99fd917f3d8f56d808478,0x2a66b318853435490862b19f4ecee918c64b8340,-0x2281cc6e5b5c7f0c3e49f1d66875dbe38c8f9058,0x19505fc46ab016de8f9ab47db347af76c40cc950,-0x10bafff42923ec1a264441d0ba522d7b976152cf,0x9f3bb5e6164c9c90f969cb2b2f2108b88716f7a,-0x551f37c04cea3d424d240d49272095f38bb5c99,0x28cf4f614b9f6dcb060774340a22d844f1a3e6c,-0x1180457c2003370bf22087706a957ce3fade911,0x6b1063104ea89c179449a10cd9b00eb5b74fca,-0x245a1ade3977e7fab4d69014095c9458d0b057,0xae8669e6f9397a307ef8da0c9f541a57472b0,-0x2e02d1a2ef4c091278f01b00f2838d2c72ef2,0xa9542efcd318e944a925b7b34a117ffac31c,-0x21b1761f7e02413120739743d0ac293d374e,0x5bd8a419aff0d6c9b19f979f5f327309318,-0xd3ae8961a7bdd4f8b499a0d1623e7eb76a,0x19612b8ccf5fcac00ab56e5cc9e96d6184,-0x27bb217cd2b5699480de6efc0e205efb6,0x317c310a89d8cc08dc98f8f5c6e8c020,-0x2f6c10dd4ce076953a9831c10b60a23,0x21681769d9925eb80595ff21d23fe2,-0x103638b49c51cac6851e2bc4a1705,0x4ea02080c8307ec9a9332fdd64c,-0xcad9c2f783e543395eef6ab1d,0xce48ac2c67d12c533cbadf2,-0x28595fb73dea1c575ad0b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 4
theorem quotient_ok_4 : quotientCheck 24 45 4 num den q4 r4=true := by decide +kernel
theorem quotient_source_4 (size : ℕ) : (coefficientsPoly q4).map (Int.castRingHom ℚ)=polyPart (key size) (X^4) :=
  quotient_from_check (key size) 45 4 num den q4 r4 (num_source size) (den_source size) quotient_ok_4
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_4 : cachedMomentCheck cache 53 indices rho q4 m4 4 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_4 (size : ℕ) : intPolyRF (coefficientsPoly m4)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^4) :=
  moment_from_cached_check cache (key size) 53 indices rho q4 m4 4 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_4 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_4
def q5 : List ℤ := raw_ints% []
def r5 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m5 : List ℤ := raw_ints% [0x0,0x87c0e28463519407563bd4ace88380000,-0x1195b955dd285a4daf8e7d5889e743d3000,0x11b648fa063ddb36a35740658eab6d035400,-0xb8d18576ae16bcabc63e0e117e81a5e59c00,0x57b9dfe989c5f783fd2b5f6ef616ef3da8800,-0x204cae13ed56c37d48df0fed3b013ace598800,0x999ac653bd02a3f63061ff72dc51c76d0a25c0,-0x25df8950a616214d974c13d7946746de9597d80,0x7e656f52f76b55b8e1921df27f52848a4f280c0,-0x16a210d072b716973ba34a6a1038bf02dfb25e00,0x384c785ac2d0a90be2736f3eb0ad374ebc5d7780,-0x7aa9d9e0d5e5f6c4dafbb9c29ab2c816b1a3d400,0xebbd881f6c34dfafbc8186590e2337fbc0746880,-0x191dcdb1ec0da325449892f61e1000f3f7d858800,0x262592ce7c8642f1fe9c4d3324d156ca61aa06854,-0x33cd28b21a5fa8cb49ee95473acee695423f55338,0x3f10ee80cd5e35db86b00e9434945153b7a8219dc,-0x44fa8f23feb60ee70c81a16e19956538518b68eb0,0x43e0da5ba1e47df8aff41cdabd71e9df56b6981b8,-0x3c2682af7c4c243efd0aeca585f715731d9ea4420,0x3004cc5766c0f779da3946554985662dbd2a5e998,-0x2287e23207e74125d14c2bf05871618af79cffdf0,0x165ae208c1a4064e8177f86057b9e7cbfd30bc549,-0xd03e522bcc5abb2044b48d7708d04c644f7a2356,0x6cdc4739847ba1d848cea84578a50a36b79eaa6f,-0x32fcfe78e6f450a347df7a99b333ce67ea4c1374,0x155708409f7c1a7bb0896e890cf5cd024b8110c7,-0x7f430bef8f9c5ebbf0e8b655f55653afe6fece6,0x2a118e0923be9cffb3586f77841dfbcb9fb6eb1,-0xc45bedf65b160eb98e031e89a9a4613f314b50,0x323ffaa2559601a42f5726dc7c0f7be2b029de,-0xb330f259c6b1378ab21e98b05240601c5fcc4,0x227af02e619a398b3e65a03da0036d1f1ff82,-0x5aaf775fb5792a486a67c41ca2fde37e66e8,0xc91f8ae65a917e371e2c8a9a5e9a325d0f6,-0x172209b4f2b83f927cce17181576145f4bc,0x229d937eb2d52bbdc2f537d0d9a7bb8aca,-0x29085f4344c431ee2520f39bcd7d15ca0,0x253a4644c1f564abe1a83e9a95400795,-0x18aacb3b6198c66365b47044088092e,0xb2ada1a4c8cba7f734f31552f12a3,-0x31fe3e3268945c85dd2230b52714,0x75674630fd3f9ad29c48784c3b,-0x6aac3be0a717cde35387fc3e,0x123171c3d216dcbdf7d53d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 5
theorem quotient_ok_5 : quotientCheck 24 46 5 num den q5 r5=true := by decide +kernel
theorem quotient_source_5 (size : ℕ) : (coefficientsPoly q5).map (Int.castRingHom ℚ)=polyPart (key size) (X^5) :=
  quotient_from_check (key size) 46 5 num den q5 r5 (num_source size) (den_source size) quotient_ok_5
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_5 : cachedMomentCheck cache 53 indices rho q5 m5 5 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_5 (size : ℕ) : intPolyRF (coefficientsPoly m5)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^5) :=
  moment_from_cached_check cache (key size) 53 indices rho q5 m5 5 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_5 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_5
def q6 : List ℤ := raw_ints% []
def r6 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m6 : List ℤ := raw_ints% [0x0,-0xfe89a8b83a38f58dc1b02ec433f6900000,0x2097ea1f8cd02692082b7c8594ff3db07000,-0x2071e34fedee97b43f69eb2463630782c8400,0x14e80e7d59f35e02c650451a2355102eb7e400,-0x9cd6553a08ce1d30a0dc793010a4fd670d8a00,0x390656247ff3fc86e5125303b191a3b0ed3b400,-0x10bba645376b2c2040ad32642f80366e2442d940,0x4126619e91e73f825d90620a08314dc7d5362880,-0xd68599e65b57f9699e978dac4fba4174182ed5c0,0x25e31e58d49237dc93a3ef02e3e05078a07508300,-0x5ceb653a3c21f2954fb9218105533b94c70e727c0,0xc78972d43be81c65939c0b1f3d852597b84eeb280,-0x179cf11fe05f46aac6edf45e3bc54ac284d600e8c0,0x27a427563da8599e26422145cb3cb8395a5933f500,-0x3b4430b23dfc586ddc946a0a9410272a69bdb69fcc,0x4f2fc27a7c85d2d5abf0416a194acba69ca6a61a88,-0x5ecf2e222bc5e391d1066e86463a5ddd8576fdc8e4,0x65ed1962eeb455637f4d95facf7bfea95ee7770810,-0x6287ea138294200a436a49da567f752abd92b8b318,0x55b8a8531a8c46cef192734b5300b0ad56a45cb700,-0x43241a6d06bd509703412430a97480c6b2e88aacb8,0x2f5676a39f42d50b6578ebc2fe18da4078e25dfdd0,-0x1e0635229d5535d2bd7b00b7ba65d5a3fd978b269f,0x111c8fff0259ab0fe90416470fd3c7e046f7e31ada,-0x8bfabbe4d9fa768e55639e77a26b46da14a1282c9,0x400fcde48922d21cd399d93a7c34235d26dfe972c,-0x1a2b64f729db2409df36a541cd12ea56bd421e461,0x9825dc620fd617db0345b28fd40b8cdd8ce9cfea,-0x30f850ec48c615d92c96be314d1be605ad47b187,0xde3b132f5cad428f607c05b1e49ca76ab08acb0,-0x373446c3ca37d2fdaed8e1f380c637fbd04cd52,0xbebea373ca39d36ca6b79a4ec3dd32f106515c,-0x237da2e87d8b43d72cef37faa1cc71bc74156e,0x5a0c608d79d2ee716d5eae47cdcb143426398,-0xc0243c049b082eb4a6b631f5cd92582d6faa,0x153210801b87d951af7bd526cbbc61066a84,-0x1e4e565b12dd896cdf84cba1cbf9b05ef76,0x222cc3ae5adc089785c2028daaded0b9a0,-0x1d566f3d920f5eda032e88c697b3352b3,0x12458b9d895acf69262e915f2c40e6c2,-0x7b5e19babe0b6a150466775ef94d75,0x1fd4ced2c817413bbb5e651d4290c,-0x43fa2bd9a1825016e667ad78d6d,0x37250ecf98768f4192699b612,-0x833116ee9a4144d38cbb3b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 6
theorem quotient_ok_6 : quotientCheck 24 47 6 num den q6 r6=true := by decide +kernel
theorem quotient_source_6 (size : ℕ) : (coefficientsPoly q6).map (Int.castRingHom ℚ)=polyPart (key size) (X^6) :=
  quotient_from_check (key size) 47 6 num den q6 r6 (num_source size) (den_source size) quotient_ok_6
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_6 : cachedMomentCheck cache 53 indices rho q6 m6 6 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_6 (size : ℕ) : intPolyRF (coefficientsPoly m6)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^6) :=
  moment_from_cached_check cache (key size) 53 indices rho q6 m6 6 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_6 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_6
def q7 : List ℤ := raw_ints% []
def r7 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m7 : List ℤ := raw_ints% [0x0,0x1dd421c596d2acc69cb2a57afe16e4e00000,-0x3c6d5b7a89a86b567b821d31b0c542fb8b000,0x3b767ec35299884655fbf00342d54dbef2f400,-0x25de240267fffadb362b99d244addb4add13c00,0x118ae59403dabaff9f349e2083de79a345c13800,-0x64ce2c3c32a58ef854d7725185a1134120116800,0x1d35a8f77dfc2a959fbeb008b85d7535e31bfefc0,-0x704549d43c5b2f8f40b1519e77f7c8e0aa4d4a980,0x16cd3a90209efeab5e05ddb51e7d2d75f64c723cc0,-0x3f90e8c60aa8968fd631b2a214925c89df7df56a00,0x99bf105946370f9bb1dafe1cea2e206f0fe5adbb00,-0x1457af24e5b436fec1f6278156ef0ddbc1aa7594500,0x25f4df0922964911099c2efd1fd81ac0719700a7500,-0x3ec46ed7bf88f763974fd506c4c03d684d9a59eda00,0x5c657d22534e198f242705886c640376dac44f7c414,-0x797e7af0492435376ed84f79da0f21565ffc0a9dbb8,0x8f15c2f540c5c0f435203f74b45103bae36435aac9c,-0x973ac9dfcf2c6858b7ae342f65a67071a59e40a32b0,0x8fa4936f8cb8efbb7c810eae6ab534b98f69da1ce98,-0x7ab6dd61f54b8fce9f65b9acd7f86596f1ab1481360,0x5e51ebf77afd988469803225336f30c0f8db7a8cdb8,-0x41363040aae0b378cfc4874e297176ad1d910a8b170,0x288745203f43c3ad9167c3185eb5adc326b157e2879,-0x169d4dd75b6d041495633875a8ed4be4e0eb5a015f6,0xb4f540e4c93d712ba3f0efc4039ad86a3ebd2d1e3f,-0x50edb0c92f0b395dffecaf3288e79af7808c6628b4,0x20457b68181532b45c86bba8aadb41561f131f75f7,-0xb6eec4ad4739bfa5a652063d85e92ff8d2e31e5c6,0x3954a241fe59cb5e554b643d025a851cb133a6301,-0xfcf65a46a98b142c58a76780b55f8296c3277150,0x3cff30ec1cf9b0b7d0f525df9db4c41cef4e397e,-0xcc34e52a5e00becf826286cbb55702e2362d684,0x24bcb95b3f3cfcdb6a514f547bb3ac2cc515862,-0x59e8911b79ddc28411cbceb28a5af62b64b868,0xb8893ac5e1cf6a095e6dc7a7cc6016958b536,-0x1384b107ac36ef60e6c4f59b95156cb7bc0bc,0x1aa84508337746a078d2d2cc38ae0efcde8a,-0x1c95634f4c58d0b7bc39a9c4d932e601b20,0x1734558acee76c86170834058b1684b605,-0xd930e57c1c1e9331790f516289b5f84e,0x555c69f0583937f2a8a125f1a122033,-0x144acfb3af02f557aa3601bd848654,0x275f30971146246775d9e30c8b6b,-0x1c7f6750cf8248d4dc1a60271e,0x3b19e82094384a3d5e6c38d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 7
theorem quotient_ok_7 : quotientCheck 24 48 7 num den q7 r7=true := by decide +kernel
theorem quotient_source_7 (size : ℕ) : (coefficientsPoly q7).map (Int.castRingHom ℚ)=polyPart (key size) (X^7) :=
  quotient_from_check (key size) 48 7 num den q7 r7 (num_source size) (den_source size) quotient_ok_7
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_7 : cachedMomentCheck cache 53 indices rho q7 m7 7 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_7 (size : ℕ) : intPolyRF (coefficientsPoly m7)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^7) :=
  moment_from_cached_check cache (key size) 53 indices rho q7 m7 7 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_7 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_7
def q8 : List ℤ := raw_ints% []
def r8 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m8 : List ℤ := raw_ints% [0x0,-0x37edbf527acb03f465cef6469c6aed2400000,0x700efbaca311a8ba9fac0279437bfb59f3f000,-0x6d08f0e7994132b12d3edb093d48c2942b5a400,0x44a43ec054e173ca525109692fa1973b2203c400,-0x1f6d2afa9551246de460e8edbb1f6a12e74792a00,0xb26c38be16ea70d5a9aac858cc644c284fcc2b400,-0x3310e1edd2c9df42a41462e36f18fa0b8ec436d740,0xc1cfb3cdbc32e9286b41ec668d00deca0e21986c80,-0x26dae954be5b419007c50c827c586bd69ec3af73dc0,0x6ae35ad3a5cf0494c0429dfbd37c5d5adc236679f00,-0xff059caacaba8c3c77e4067d62a4a9fe84101fa3e40,0x2145b7c12fd95eacd454ca6f5ff6cba170652e913580,-0x3d314de5715b6c67d060cc9f37e39a2a42ae0429f240,0x63b3540b75eb900b107cec52c2a9fd2644a6489c9300,-0x9089485cf7adee6fd0b8db53c2ce30b5ee9a150c780c,0xbb149bf2a193501444dd5f2f73819c5f661ddb2de208,-0xd8c53d81ce14f341055d20678500218b9dc43b3ff124,0xe14a248e70a980c1cc1c9e88c279f81e73b3fd21c610,-0xd24c6283f51b12753d0acc2c402364c74b49e272e6b8,0xb0739fb1985556365566987fb6f54a76bd24db8b28c0,-0x851d30c9b165676de68733ccc989dedba4d77c93d418,0x5a44080c6193b70f875459002e2ad40eaf501a6ce650,-0x36faa4eb265e5268c5220ef3a283978b8afea5f9486f,0x1e0a38b3d85ffe242b803a8a656a763be8b01bede23a,-0xeb296049429c77d855dd9d764aeb0b9aa5e0cef7ef9,0x66c9070002bfdc181040ec49d4fcab91975794c27ec,-0x28038e8025ff876a904d894e342f264e4f687c27eb1,0xdd2adfe7980f5b5f53a8438d319a93efc3e64d5e0a,-0x437eb1e96648df95392592283d7cc01a6062219bb7,0x12190afe9028d996a87f8d67e038a0734b781f5eb0,-0x43c6bbb0a503268d84646aea3d10bd71ef5ebb7b2,0xdbd6775240706a17ad4ba6605304a98020d2739c,-0x263c687fc36a673fdeb4aed0f7d96af32c6aab8e,0x5a3f8499cb19ddb62120ed19797e0d26490c018,-0xb2242df68d3a87d50bfc9812dfe07dc3bbeaea,0x120fa1721f2bb21bb22f8faffd9b3cb20e6d84,-0x178d9dfbe59b6059759fdcbaaf528015bac36,0x1800dd46ac9f6ede74e873c1b20e09b47720,-0x126aba31d19cbb9d74db2fc49ebd9109943,0xa1cd9b20514752cc0205a84b43dcf61a2,-0x3b2df114889ff6763db52dc423fd31e5,0xcf341cf32e7d4648fc5359a4e12bcc,-0x16cf2fd478dd8b296a79002d5e4bd,0xeb8cc8de8aa7ab278b2db2a032,-0x1a9d0fed1e7308ad992d3c6b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 8
theorem quotient_ok_8 : quotientCheck 24 49 8 num den q8 r8=true := by decide +kernel
theorem quotient_source_8 (size : ℕ) : (coefficientsPoly q8).map (Int.castRingHom ℚ)=polyPart (key size) (X^8) :=
  quotient_from_check (key size) 49 8 num den q8 r8 (num_source size) (den_source size) quotient_ok_8
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_8 : cachedMomentCheck cache 53 indices rho q8 m8 8 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_8 (size : ℕ) : intPolyRF (coefficientsPoly m8)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^8) :=
  moment_from_cached_check cache (key size) 53 indices rho q8 m8 8 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_8 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_8
def q9 : List ℤ := raw_ints% []
def r9 : List ℤ := raw_ints% [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7e900,0x26c280,0x532a10,0x679320,0x53a7d8,0x2e4f28,0x121199,0x5051a,0xfce7,0x2274,0x317,0x2a,0x1]
def m9 : List ℤ := raw_ints% [0x0,0x68ddc6baa63ca76a3ee40dc465487ca3800000,-0xcfdb9b2a297ec168450e19e84a1acd38d923000,0xc808937df2217457f615397605e6b645d2339400,-0x7c847ddca877d1f956f45b736bb509b9ca89a5c00,0x385acbd2a535f908f8a81e88096d7ab9ef5bcae800,-0x13c3229d80377602003ca7e46929d7d9bc8b570c800,0x5968c6c78584a45233e261fd6c2bb4b0964b932a9c0,-0x14f271f9c49417a77c396b9233009e81fe471ff29580,0x425768b11f2a70e08226d386a526a1eacf17771f18c0,-0xb421e457a7f4ec41dbed1b85970cce11a76ccb5ef600,0x1a80b2c0c04c47d6ac270be3763e4d96e6dd063d54a80,-0x3690ebb8e5f8e2bb5c87d99fa401cc4126c4191809e00,0x62f09c80107b6caed4e388ad80153d71e4e12399fb580,-0x9edc8d15091f5597f7e45774d84aeedaa3dcd014bbc00,0xe2db4e38969023cfeecfd66123cc89a900539c289f7d4,-0x12119ad5df4afc876f37dc997565f237f698437b778c38,0x149a48f7aaaf511f3817e5fd42d4a485ca584ec970fb5c,-0x150f4563821a056b1e1c68dc05bb0a9bd6da838a1276b0,0x1352bc3768418ceced56f37daf6c6f89146a27b0229a78,-0xfed43b17ddd46cdfad665db8f162329c359f48a3d04a0,0xbcb7ea7fcd91e7c7d559257dee689e83bc8a8644a62d8,-0x7d88f06048d521fbb7645039d9d145b2e71d807b578f0,0x4af22649b7574594f48b976e6740352abea384194d1a9,-0x281a9901259b3d04bde32d50b20c6104e2a9f6f186096,0x1332cf308bb5d6fa92dfbfab6f4a8b919067fecd8980f,-0x833b7ea2c68ef6cee337fbc470be2625bc242cb089f4,0x31e13e0b2e66352f6d098a525f1472f1c789081e2c27,-0x10cd8a5e92b4a83ccc4961507c6a76a891021ecce0a6,0x4fe58b27ad0b7acf38892e6676d5c415dd3c9ee9e51,-0x14d49586f76be415f59c25182d49cb531f114afaf50,0x4bb8d911d0ab39133c25d472346bdbc4e89ed0b51e,-0xedf31d1185c120b7edc5eabd4f620e04b73af9844,0x2802021c7c2aa127b97740d15c9bf9c7618893142,-0x5b0ec481e31bc88d28303a45a0aa9625feba01e8,0xacd2260fcb0834fc3b710488cd692c1df2c7a76,-0x10ca697153ac122998144a02a6895103cbd32bc,0x14e66b49a031f6bacc616a85a78e8dde3bd14a,-0x143c06eb3e6fc3d03ed15f6be185b0d90dda0,0xeaa364ba0ffd60727e7d1f05a38633c0a75,-0x78da1126734272c9e58de8681678ef3f6e,0x291a21e01fa9eb3e56ef4ab2125bc2bc3,-0x845c74cbbbc665af3048b1732184194,0xd3764dc11100b7e6d07ce2afbad9b,-0x79a423eeb51c0bf4f655f639ffe,0xbfab0f81de57ff612ec286dd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 9
theorem quotient_ok_9 : quotientCheck 24 50 9 num den q9 r9=true := by decide +kernel
theorem quotient_source_9 (size : ℕ) : (coefficientsPoly q9).map (Int.castRingHom ℚ)=polyPart (key size) (X^9) :=
  quotient_from_check (key size) 50 9 num den q9 r9 (num_source size) (den_source size) quotient_ok_9
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_9 : cachedMomentCheck cache 53 indices rho q9 m9 9 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_9 (size : ℕ) : intPolyRF (coefficientsPoly m9)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^9) :=
  moment_from_cached_check cache (key size) 53 indices rho q9 m9 9 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_9 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<0 at hj;omega) moment_ok_9
def q10 : List ℤ := raw_ints% [0x1]
def r10 : List ℤ := raw_ints% [-0x4a662ebc146962cc932400000,-0x72f21b60b38b9cb8dea740000,-0x544d7543e1eaf976e558c0000,-0x27112154ff57984f45671b000,-0xcd84b9790e64a0811a031400,-0x33084c595baf01939ee29d00,-0x9f215054833341febb249c0,-0x18f88b2b882cf6eb5021ec0,-0x3361e9ac8f4a793d9dc5f0,-0x57bc983695ed862f7d330,-0x7d6660d4eed48d597054,-0x96e3e244f136778cbe4,-0x995cfccf69328ba409,-0x83d2bbc283f8ffe40,-0x5fbd0ce1af2ccd46,-0x3a923bd8d2bb6b4,-0x1e053185477c17,-0xcc88332e04a8,-0x477bd08819f,-0x1426d996b2,-0x477bc4d0,-0xbfd6cc,-0x16ba7,-0x192]
def m10 : List ℤ := raw_ints% [0x0,-0xc49fd49df7b1b9e735eb99d03de7e9b29000000,0x181a6e0dec6d565c644016f2075eb7c8dedaf7000,-0x16f28c597db87b42f20b505841f51451413c97c400,0xe20b8aa75a679a213d6aa0a90ccba7772f2283a400,-0x6527f4b9a822aef725d38efaf967bca2b6503434a00,0x2310aa24bc0ea4229e6bb3effd5fe80c1d8f57b3b400,-0x9cc5dddf12ebcfa6e4ae7c7c6fdda33485a5792fa540,0x2448f814095b3e56ff9951587642e7d0ac70d6a735080,-0x717df33edd6c17ae2d4fdf2a576c0190cd613a66c65c0,0x1303a727fb9eb09f7a57f1cb32de8d5e89c2fb506f9b00,-0x2c2c9d460c678bfdc4470eebc9015acab971fca43178c0,0x59b94709372f0198223602477cb48e4c37add6270eb080,-0xa06e26960493a362d6c0eddbf43984aee75b40ddab17c0,0xfde8ba4e309684379a8e4ea59c55e23d0c4d6c11b2a100,-0x1653d0a29d0eb2680b73535fce1d9e49f5e512577ada84c,0x1c052f6c7e9c1b144ea08147d5f141ba2aef4aafd987988,-0x1f72711851fea95f031e73e525901bcb734cfc80da17564,0x1f9f0f9f79a3ca7e9c780248bf512cdd953be1569855c10,-0x1c865dae90b1f3f9465cd410bee8a26c19a840b3e4c4758,0x1719a06722ade5cb6a85351f95688127d394e91b282d080,-0x10cbf081708485ed6239064ee2e1230fdb2d0d174f74e78,0xaf64e2812f93c574b272957a978a0c0ba73311d546fad0,-0x66a7444dc6799c197bdc04a16359b216531f6a4895203f,0x35cdabcd3a0be94e8fef49208e5d42988460717bd8d19a,-0x1934538cec6226598139736ab2cf7d8614ce0bdee97129,0xa86ae224f13bf99affc694f436130a92374b5b18234ac,-0x3e813c6d8ae1b9011393ec82c22e5488c8f3ff9497801,0x1488a70651673f3c027d6a70fefd5e12faffe88e94a2a,-0x5f156d1d34e22329a7efd6cda8a1b463ad393d7e0ee7,0x181ab003541ba87678f40525edb9fe8ea6acc364f8b0,-0x550d277a9eec75fbded0e24ec53e169ae616bfdde12,0x102e9ef4f4cbd9b0aaa679c4af96f933abc6e2065dc,-0x2a140f05a5b76b8d78b3d97efba8896cfc96d751ae,0x5c55bd0c2640227492aee173caf99bd942f7b6c98,-0xa87652ebe895411861511ffea15eb446c60b512a,0xfae07987fb0d701e7d8449f9650ce99b8936284,-0x129f48e0cbeb49b5616d77506904a677bb26df6,0x111ea038d51fca0472f8ef3594b642ab48f0a0,-0xbb696fcb116003cf603722d157b9fa0f65d3,0x5a7b795cd6d35f5007206203ccaecdff482,-0x1c97fae4f0466083f8b369c8debd9fd455,0x549f7a352d15bc4a5bcdebdf9e7d6a8c,-0x7a8a4aeada4e0435f4aea71ec6010d,0x3ecb4999d10cc0c8bf65e46e8c52,-0x563d380b92aa0aecd792b609b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 10
theorem quotient_ok_10 : quotientCheck 24 52 10 num den q10 r10=true := by decide +kernel
theorem quotient_source_10 (size : ℕ) : (coefficientsPoly q10).map (Int.castRingHom ℚ)=polyPart (key size) (X^10) :=
  quotient_from_check (key size) 52 10 num den q10 r10 (num_source size) (den_source size) quotient_ok_10
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_10 : cachedMomentCheck cache 53 indices rho q10 m10 10 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_10 (size : ℕ) : intPolyRF (coefficientsPoly m10)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^10) :=
  moment_from_cached_check cache (key size) 53 indices rho q10 m10 10 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_10 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<1 at hj;omega) moment_ok_10
def q11 : List ℤ := raw_ints% [-0x192,0x1]
def r11 : List ℤ := raw_ints% [0x74d47563580d7d253f0e8800000,0xb435c8cf1ddcd2b7810f7e80000,0x83eeb009380f701ffb46b640000,0x3d0498e23515a23304168fa6000,0x14049592ac8a48a85c68263b800,0x4f55832ad8ea6bd94e65d77600,0xf6b1cb5f204b8d88c7f153280,0x2697293a0753687b851a1ffc0,0x4f20383e408022f40cbeb420,0x8690086aee7a5522b8bdb70,0xbf6efa8af5aaed937a90b8,0xe51b7342f3da3ee56bbb4,0xe765c6d9641e043aac3e,0xc56b1b0a7cada6f0977,0x8e19b27e3d576266cc,0x55fdd12c6a21d21a2,0x2b7b04064072b69a,0x12328af21b42089,0x6377ec08d2948,0x1b2d4c8824b9,0x5c1b0e9aac,0xe5f9a1b0,0x1800f90,0x14d91]
def m11 : List ℤ := raw_ints% [0x0,0x170abaea8306d3c918519c0667412d62ece000000,-0x2cbb30be4342e2202c0175dbc46fd45dc2a89fb000,0x2a23ee21c57468f906b21879427204127869bb13400,-0x19aa7930b585c1d84bf4cc1463814ad66320f0a47c00,0xb5c023ea8691f5f0a154a8cd4f3da0e6b052342c9800,-0x3e4b031b7ecfd48660cfc3e8dfc48902bf645e9c02800,0x11349e14cbb5b0f5d4adfe3f98f46527d5892f7f62d3c0,-0x3ef5b446ac0ae5a9d0864055148d937155a7ef1bcca180,0xc286ad14e72fb6f09df104c249e7104001e6f7d79154c0,-0x202eb8e6e61d2585d187cc95b45f7442a6a41643ed2a200,0x49cdcfe3a6a7ab036f056c8f62adbc865b2205e7fe44600,-0x93eafa27001575fb0534f06792f81128dc7c697e3d79f00,0x104df004e91cbbf9222b4bc9f7b28aa002cc044c8fbc0a00,-0x1970eec0f2a47b4d95f0947068ec206a37ed31fe079aae00,0x23462a8ef73cf92ada1417ade9a56ece963dcc04df04a394,-0x2b9a5e7327de8839cdd9c06aebbca600028b2e0a953d1cb8,0x302cdd78003c9115e3b88c24d41c88ef9e7ca302b0d8d61c,-0x2fa9bd5078b9de5ebc8784a2757443512870d8ac002c62b0,0x2a475ebf2162de75b3c25a7e2f73f9c79218bce4fdf44d58,-0x21a5523ede994b9297747d5b8a5db3b37c11e3359e2287e0,0x18064b23d2a1bfeecea356cb1e5f6e9baa55e72a93ecc0f8,-0xf62c36dc41fe052d4c96fd148e00d4e0294afd07b4eb470,0x8d4410d28f06c1c405ad3ff175c211da775080acfbb48d9,-0x4888314dbf91a4515ee5a9e8657e4f7f357d9f412c84b36,0x2140d62a2da74df51b56122e3a891ef17998a2e4230ffdf,-0xd93ba55b9b9527e0b837a0c095c2aba0628de2760f7f34,0x4eba651487410459c4ae7749c4180fd87ac1e09fd9d357,-0x19394196d3fd64c8bca8ae6ee9a7eab8c0898b20779d86,0x71c001719345e6e4849f7197fb2c3bc85241e98d380a1,-0x1c09ecf75269ae0b9bdfc95adc04f1f7e76ddc2b30550,0x600718eb1b748c67dc77fde7707e82519f5bf1e84cbe,-0x11b2c30c8cdcaaaf98f28bdb5d28a3a0171e00db0a04,0x2c7a714284c6ce7295e8578e3e2d5a8a4963f532a22,-0x5e15a052b7e3c9e6056abc3a6ddb4154d4e8fe5b68,0xa4f8fbf3b2ab76a60f56da7fd049c910cd56848b6,-0xeb4a9d3aed5c4ff72d61fb20c479eb4c153ffabc,0x10a871e4ac732df35120298b0042fffde1a03b0a,-0xe88d726df9c9f005ff90b478775d657d944420,0x962010bfbc8c549d4db1c25fbcb3dd9c22ce5,-0x43e569aae822ef05b2ca11df020763c1b68e,0x13ebf1a0ca3c55d8716ed47b4eca6211d53,-0x36244cec3614c8da5ad3e01e3480c50d4,0x4703aaf0c7a95bcb2d639db5236e2cb,-0x20675bf6a5fe74fab5c33713146de,0x26c98ffe519ec752a552776f2d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 11
theorem quotient_ok_11 : quotientCheck 24 54 11 num den q11 r11=true := by decide +kernel
theorem quotient_source_11 (size : ℕ) : (coefficientsPoly q11).map (Int.castRingHom ℚ)=polyPart (key size) (X^11) :=
  quotient_from_check (key size) 54 11 num den q11 r11 (num_source size) (den_source size) quotient_ok_11
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_11 : cachedMomentCheck cache 53 indices rho q11 m11 11 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_11 (size : ℕ) : intPolyRF (coefficientsPoly m11)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^11) :=
  moment_from_cached_check cache (key size) 53 indices rho q11 m11 11 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_11 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<2 at hj;omega) moment_ok_11
def q12 : List ℤ := raw_ints% [0x14d91,-0x192,0x1]
def r12 : List ℤ := raw_ints% [-0x60f10eab1f14a53511452b6400000,-0x95513448e7fa3f7319169c7340000,-0x6d244b9fe933bfc43d2b498640000,-0x32637a5f6811824c423226cf0b000,-0x107f9c3e161f8b1a3a7b453c7f400,-0x413e69aa5016eea2648342303500,-0xca631f29c0f9562325d04130fc0,-0x1f92c00314aa531a69bc91df840,-0x408a04d730abd25c19cf344d30,-0x6d60004d53e8e0e585f555a10,-0x9afc326b245e1cef3b3a0824,-0xb8a4f4be2775ca829287f6c,-0xb9831b50ce13bba5b0db65,-0x9d4d6c2ac898ecb024082,-0x70687225355301c6ec3f,-0x436fc98514870132e48,-0x21bde54910d8801bbd,-0xdf05ffedefde5236,-0x4af201e8bd91a2f,-0x140a7ad4317144,-0x41f8791c9eee,-0x9e08e5d294,-0xf7e33dee,-0xc277ec]
def m12 : List ℤ := raw_ints% [0x0,-0x2b341e77b5accd190d99048c019a35197c24000000,0x530871ba468b0e58a593949fdf507a851871a96f000,-0x4d6c5440c9a5cbdf61f54331a62515ac55f9f612e400,0x2ea92314243a996751d31a4ae7f61cb78e88cea688400,-0x146deceac07865e4bd211dd33f978d0da0b1a230d1ea00,0x6ecba7618591797b0080dd72805b62028ede15ca9db400,-0x1e416e6a330ce87231ed3a2341ef34f153a612b398cc340,0x6d6d04534af225b6d631f36eda0cd33ee8260e8693d1480,-0x14e0cc309ca652b63535d1059fb72df4f8d229f68408cdc0,0x3695f6dc26a315e2d06ed0e3479fbb7785098e23fe1a3700,-0x7b98be883ad6a4332102889ca8d09fd90396fd5e17e1b740,0xf47b6242dc10f044c7861835283b68a17b43207280efe380,-0x1a96035d6c90e4894c62fd7905b6c04cf3811de5757ba7940,0x28e89a818add48f5de4b9e0281f3bd34d44a4d61c52781f00,-0x37e81b3048beec20004120ea5753dc95b4583dd75c08e908c,0x4415446dc871fdf40cffad0fe23d60416092df1ac47893108,-0x4a117becfe3d0c455e96c5ae1a7fdcf2158eee557e33ef5a4,0x481da31bca7037719a82a5a5445189329b0107fb6e1247a10,-0x3eea00e592a1e14aa1ea64e9030d4cbb2a8c28e69838dacf8,0x3135a7243d7389fc2d0f0d447d2dd071830a7aacd9f1a1e40,-0x2282ef5815b6742c9731730079996ef1c30c9aa71775a03d8,0x15b0fa97733a2acb871c5d835b03eb8e43434e4b067a0bb50,-0xc34d0abaf5285ecb9976129600ca3d9278040f523fd0a60f,0x623e9d23abd091ce9d1832ade0c5fbcf034e0b56eb0c08fa,-0x2c16036917b566e487a0ba7685e2e3cfa98acb5dd0d3a159,0x119968afd612ebe8314d8a901d40ebedd6a1216a12460d6c,-0x63a96de81174d3ffa7346ce1d9588fb71c9a0a6c3e73051,0x1f24770649def5bd48d7ee7ddb7c5749e8e48194e47544a,-0x88c705030edcae44b524d118c1e181e8d982f55debab17,0x20c84a146ca116a52b2aa3ea45b9126e7d0de0018d7ab0,-0x6cf89ea4d2f0bf10e7897ce8fad80ef249cd689b09072,0x13740be8b09b5323205507f4ad081f1d5ab384a91381c,-0x2f3e8ee0f0a0f24650454a4614ab3431e01399ac37ce,0x605155c1ae55ebac7df9ede970368fa7d0aa5803918,-0xa246acb27c5ea1009b4e7915f9c3ac6b668434ba6a,0xdd974aec9b2375cd2b7288281b089262e8d973984,-0xef50404f0899ea943f0e9a580c9f74fd77badcb6,0xc616490b89f96435ef909d49efab289a157a620,-0x7895d25b574c3756c13316a411ff8368841063,0x330dbff9b0b957ee3731706443cd2c955df62,-0xde608c484a7982ee02cc5033ded87d51cc5,0x22a967e8b98a7c6a95fe1c875a3412554c,-0x2927735b9d724501e1c0d1d35ff1325d,0x10b70fa698c691f0ef3ab6ec0b9a72,-0x117048eb95f73fc92c8d68657cb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 12
theorem quotient_ok_12 : quotientCheck 24 56 12 num den q12 r12=true := by decide +kernel
theorem quotient_source_12 (size : ℕ) : (coefficientsPoly q12).map (Int.castRingHom ℚ)=polyPart (key size) (X^12) :=
  quotient_from_check (key size) 56 12 num den q12 r12 (num_source size) (den_source size) quotient_ok_12
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_12 : cachedMomentCheck cache 53 indices rho q12 m12 12 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_12 (size : ℕ) : intPolyRF (coefficientsPoly m12)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^12) :=
  moment_from_cached_check cache (key size) 53 indices rho q12 m12 12 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_12 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<3 at hj;omega) moment_ok_12
def q13 : List ℤ := raw_ints% [-0xc277ec,0x14d91,-0x192,0x1]
def r13 : List ℤ := raw_ints% [0x3884498073fabcad1bae45613000000,0x56f0603288215389721366558b00000,0x3f74df6212f4af4b3af262929dc0000,0x1d4023f112d43ac8db9d4e1513a4000,0x98f8a31058a87388718d4e2431c000,0x25bc37fefa04a55f4bd2f8761bc800,0x74cde37473c24edfd1c95c9f40800,0x122da8e5a4f988386a97123ac8940,0x250f18f675ed7a660e5d5b371100,0x3e9d64988845462a930aacdb310,0x586c538debfdd60915a1fd3f60,0x68ef9d59cf2913797d1b0ea0c,0x68f5ffe488ba12a5ee3eb3e0,0x588b410fe7a5f7b1be2159b,0x3ee546239f3e0cea1abcc6,0x2577ba30a23d8ebfaaf31,0x12970305bd0b13c40b0c,0x79a1218055ef32d803,0x285cf157f4f806d6a,0xa9fc538d46259e1,0x22438cdd8b3470,0x4fdc5739e812,0x788ee29694,0x5964bf62]
def m13 : List ℤ := raw_ints% [0x0,0x5101b92074a4008ef97ee8868301238fc8c38000000,-0x9a2afbb84b8b786d8d033d84a9e4b814269a12193000,0x8e5091d9cf6a5b7afd2f6198431677105bb869a23d400,-0x54e3b93dd9a3091a08c96bad2b39d625536d6e73a59c00,0x24c6ae43220c7f3457cdd7425c8315933eac3795dc64800,-0xc54b8f86b5216ea10f2fabe218089cf40f135cebef98800,0x3547616be2242e9a7528eca511d8b701f1157aa57bc2edc0,-0xbe7f2c9c85200be9ea67807476e86f0acb8f7b287df34d80,0x23eb7921c15de122046b4a764acc6d0fd932fcead41b7f0c0,-0x5cc73913351a4b353a1ecef798cb5a052fce4211218afee00,0xcf75ffce5bc08dcada411799dd98f6ba273503bfd1cd84d80,-0x1951b71fbd816f7f20728aaba65bbe9eb1a7bff41a27110800,0x2b7850c875f96ecc7428c29c0146d27c89259ffc88bd43d280,-0x41f95fc59694e0afa3ec0d0ddce0cde4484ac698e67ced3000,0x58e3394456abe0f12b6945e584c4ee4d5ed864bfade0f4e754,-0x6aaa02d8edc22293ad3104fe0abbed10a11c9b794541b3ad38,0x724869728d45e434d781c53361c6bdc72859aa6e9fc3587cdc,-0x6d858e56d7ac9e049465d456f4fb63c0f14bddca86fadbd6b0,0x5dfced39fdcbb9112bbd07325683160267926e0dff28942f38,-0x4844700dfd35259177fc219d9e28ec4ebb35f2c07661c60d20,0x31c96b999f826e8c22e611216f060752b23c2fb61b7fd02018,-0x1eb7395d2d8bfc381f42acfb608c28521909d0fad7da48c3f0,0x10f3b3611ae1fc2564cf657b1ef940d8483df3d645c7ed7609,-0x85b180063d11721937762b83df486606a8996a410f95545d6,0x3aba0dec70d296981334788e0d66c119d81e3101613714daf,-0x16ec8e5026ef1b0be96de7706c3e042c6bad338c96c416874,0x7ec8e4c264506a5f51e40f713e3a2bc3a08c4d34dd334b87,-0x26a449211853a407b30db116935c110ec34df1f2b8391c66,0xa54a260fdb7ef223fdba33e5d6341e735de030594a3a9f1,-0x26851d185d540228cc291696b614c104a254852eff63350,0x7c457a95bc6b70b9809276d4a5476c73d59b8a87aaf05e,-0x157c83de0ed230c201b0b6f12a6c1a1f1666ee2111abc4,0x326b8687cefee9d95b8b60aa9ec2e8cc529b40b9e7302,-0x630d746511b08a1a9f17996a81be715420ed56e3e4e8,0xa04f8af3b800f3c79920fbcfc1a1999adaede75a7f6,-0xd185622f9e7d66fd9136331d4b1b538c69b3e608bc,0xd7a6c12ac5a88ddc72dc9625dc6c1637c23a413ca,-0xa941bb9921868aa7aaee17cc5379f59836c0aea0,0x611b28047787ca46bf6ff634672d0e90e7c2555,-0x26768a30d7f89af9719b5e70b9608a3515cdae,0x9b559d72e21e6747ec3fbc5011d622ff0ce3,-0x1633d5760a4f1d0eb1cf88d8ef95869d414,0x17d937d06c01c6fc7d3a00915a3ca5afb,-0x89e783d8a571d55b47b0cc6dc5fbbe,0x7d66267a40e748dcad8978ecc7d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 13
theorem quotient_ok_13 : quotientCheck 24 58 13 num den q13 r13=true := by decide +kernel
theorem quotient_source_13 (size : ℕ) : (coefficientsPoly q13).map (Int.castRingHom ℚ)=polyPart (key size) (X^13) :=
  quotient_from_check (key size) 58 13 num den q13 r13 (num_source size) (den_source size) quotient_ok_13
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_13 : cachedMomentCheck cache 53 indices rho q13 m13 13 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_13 (size : ℕ) : intPolyRF (coefficientsPoly m13)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^13) :=
  moment_from_cached_check cache (key size) 53 indices rho q13 m13 13 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_13 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<4 at hj;omega) moment_ok_13
def q14 : List ℤ := raw_ints% [0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r14 : List ℤ := raw_ints% [-0x19facdc85c8cd3be281f72282fc800000,-0x27eae3bc72d95242b5e35d33a39680000,-0x1d192aac45ab58bb0ace92a5adae80000,-0xd64df9cec536a87dd08756777ff96000,-0x45f003b92b4da9839d052a1abfdf6800,-0x1138ff4c8d92e51212a109da15b15a00,-0x3535716798af95ded9aff62582ab380,-0x8436e4009dfd25d106565cd8ccfd80,-0x10ce6857a3bc77b1ac3962eb274ca0,-0x1c52269e53d64b8a283899cf89760,-0x27e01b1db520cb7ca8a0410df918,-0x2f29d643451859d209d036fe9e8,-0x2efeb50855dca2b914d988ca66,-0x2778c4266014568b1da8655a0,-0x1be5b2d532acfbd4103bc351,-0x10858f5510e5f57b72cb262,-0x824230d1eebe31994634d,-0x34d4d4f1569e855c3a94,-0x115c1b9a72742b04b6d,-0x483a28e566fa46aae,-0xe56bc4ce863572d,-0x20c5a743e8f610,-0x30340b2a3eaa,-0x227bd95764]
def m14 : List ℤ := raw_ints% [0x0,-0x97e33b1cdab3810c13cdf3fc35a222ad986e90000000,0x11e4fcdb88ad5b952b54867c1e18fe669fd45dceda7000,-0x105b792c5ee17c9431bf99941f7abe51d04db0b420f0400,0x9a8c1c5048ae504317a180820c7b8cf6b8800806ace6400,-0x4243af67c31aae63026c3517fb979be3be80c05d68d50a00,0x15fbbfe76c89dcb30feeb95f860ff4b10afc4ee02bffcb400,-0x5df3bfd768b69059858c9e3d750950a48eed36c2ecda5b140,0x14c2ab5c0ac2c77048e9d2ef4835e48fc201e654ed27e7b880,-0x3de97890bc27274fdc2bdc7bfa0cf727f0a27d8fb67be575c0,0x9e048ec3d376eb60131ebc1a6dcb7bda380035e7a2a9c77300,-0x15d05e599182b95cc1c2730e1f7e8ffa63e362e53d5fa9fd9c0,0x2a0efd3b8c9911abefa25b8285c915b6a636f582eab02950e80,-0x4744c7e1ad0cdf0158fd4db5549c29a74f684daaeec066f36c0,0x6ab518d62163b07cf3520484e6ff550aad4ef3c9b29e0318d00,-0x8dc3c652152af4b3c34e8fa7d0342d0d2de9baaa355fd5f90cc,0xa7a9378e763f1580e4b20fd473c8e3377bd8276d16074c80888,-0xb0f2d1d95b72a82d92246857b880205291eafde84f0790931e4,0xa6f142899214c69c809cf7a7f23d70b04d54c9066666398a010,-0x8cf394c8a80626b4477d0db48362b3cdb9876c750d9ec23ef98,0x6a8e6fcece3b8cc95c8bcf9172925df7cc8c2a1544cf75a6200,-0x481fad9d86764e9c5d531c10157cd8472ffd54b92d36daf1c38,0x2baed59d73ff87d5ad69e07d871421833714e486a2bb36847d0,-0x17a5d2f3653b43fc55b79a3679ff66a13f3fbf89535f8a4d1df,0xb6c450d152147d994b65dc4de015808c1266c0c313d4adf85a,-0x4e98b1c7192f2f4655e4e74a08bde2f1037ad85e103e293789,0x1e00a01d0e213d9d7a3ef2a09f0313af69c4cec5a11807b22c,-0xa211cf193b04cbc09d231898f45eca7f00f665ac2100d07a1,0x302e4fa39c51e84cf464e6d6b022a0a570b22c690027efc6a,-0xc8b91aeba7e480e79f70677e9a657e766837ed09764c9047,0x2d7b88331147fe6600c51bb7cea4240350647a912f4c24b0,-0x8e67608033b45f16ac4761c5eaa462cab750e0ac5231ed2,0x17d823083491e02059187946b9de02287f012209bcf4a5c,-0x360e6f26d0bc49657e18bad2dce1cbcea424e50d876dee,0x665047190c2784dc8b7aad4f2ec977857df81a2452598,-0x9f06cdfcfe5d878e506431f725875575c64c3a673eaa,0xc6de167521ce0cfccfabd4e4a927cd31f685658c284,-0xc2ff23c181c17fe351e5172f6d85bf6ea604b9e076,0x910cfcd3e5e85c0e51b8bd78ba3f7387b1d3fb7a0,-0x4e62f523d44c651712968ed230eaa17f9eadf0f3,0x1d076735785d28d55fc2acdb003562f281a5242,-0x6c9fb9b4cd30cc5f45f9a2b964a42347e9335,0xe3a69fb12918b7e80b2bb7e4eab203f6c0c,-0xdd1a3c4044db517cbcf6926c8b3edc8ad,0x4715289c8c7b9a12e4092281f99ea92,-0x38568479c2bbb2a915f2bd9851fb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 14
theorem quotient_ok_14 : quotientCheck 24 60 14 num den q14 r14=true := by decide +kernel
theorem quotient_source_14 (size : ℕ) : (coefficientsPoly q14).map (Int.castRingHom ℚ)=polyPart (key size) (X^14) :=
  quotient_from_check (key size) 60 14 num den q14 r14 (num_source size) (den_source size) quotient_ok_14
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_14 : cachedMomentCheck cache 53 indices rho q14 m14 14 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_14 (size : ℕ) : intPolyRF (coefficientsPoly m14)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^14) :=
  moment_from_cached_check cache (key size) 53 indices rho q14 m14 14 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_14 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<5 at hj;omega) moment_ok_14
def q15 : List ℤ := raw_ints% [-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r15 : List ℤ := raw_ints% [0xa059077727b073b605ea1236eb61000000,0xf61c8bead551ad13eaa92313ee04d00000,0xb3327790ed38e15dc707109a9dc5480000,0x52613a87cd0b75134e167d1465bc50c000,0x1ad8bfe90be88ecc3f8aaa6b05a9067000,0x699da704869ec8a420a7208146900ec00,0x145bd8d198c19d6375b116ac756c3b500,0x327e1a87297ff666aa14307265dc8f80,0x667a5cfb9beae1ed99647a6ef88e440,0xac497cbb84b788f49b5fb00a1c8220,0xf1f21197fa4facfabb8779257d570,0x11d541f3b1066e9c6a6c197b027f8,0x11b5ee10fc1ccab223b2c2c23c9c,0xed1d7ca27e3064de50c81bc09a,0xa6de090b24d936ad62a6a81f8,0x62566c22e2ccf9cebc181f7f,0x302dd99df360ceb7d3a8ffa,0x1368e6db1749ed524809f3,0x653b9b77b71e13854f4c,0x1a1279fd292a722e443,0x51d84ce32040b71ce,0xb853df0a78ec5d3,0x10a1016256de28,0xb9ac1c952c6]
def m15 : List ℤ := raw_ints% [0x0,0x11cca0ed61a1091f6a5222978e49001057dcf4e0000000,-0x213d833242f38201caf41fb8a166358125ac2052abeb000,0x1e185344bc884161f49ed8dff7466ea3c102362863b37400,-0x1198ef1c99eca0e812d2f58e5ebfc66e5985f05f6051dbc00,0x7781cd7db7381e189da7d71093c83074166fc82254e23f800,-0x273c89c8f5ee3109031d14b8cbad234e12cb760789e89ce800,0xa5e70c3590ef618ab13453f198c4d7f0b87e1fe4372f9977c0,-0x2441e00a85340649b7cb7774e72d8e1e8c2ba71f01861db9980,0x6ae7ec12a7c49a27ee5e62fe9cfc03f26f45687aca3a8a4ecc0,-0x10dadc52ebf96b4b7744ebd13797929e29a682570da5baddda00,0x24c7fbca8c09282f5d0ffac6879ffe08b960bada184339580100,-0x460954c8655e9d123a7ca1a9da4d8280c73db53227b217e19900,0x7527dae986826af4063c8129aff9646cc0b5c2d916156a726f00,-0xad15badb2d0615de28f96598c90b299b539bdee0198eb6a0c200,0xe2ca5fd9459891a2e02166da4f95f4db164c6ebcae40ba9ae314,-0x1086605aa5266c7548ab6d9a55416bba26e0b9c703973f78ffdb8,0x112eb9cbec9d7cbf39ed8e356f2e7d35d6a7dab80dd36cb8fef9c,-0xff640f08fa3538e67421af9ae3a3fdac76261a67c12e4ffa12b0,0xd42f3a9d13fa83a06223d36277b929e8482b2bb6ab9f71b4c818,-0x9dbcc006f23a5a477ca46ccb2491e590cf82cd133f309f7e8460,0x68e989077284676196f122a813a52e734b35d1def729aa297838,-0x3e639b30e99994a509b2b8c4a0e51bed04bd32ae1b19d2780770,0x21220f6a883d087a294f3ae2ef92b3e2cdfe9341f36a5f130139,-0xfafa7d17b7f97258999b6b4d038948ed1cd3a94de540aace076,0x69ac4a82fe7e31fde118604bd1d7efc466ea837502e81d9797f,-0x27734b16a93a1aeeafbf25ab752e571b7683571b7edb74e05b4,0xd02828501dee0aaa85d753b54156faac47509afeee17a7f4b7,-0x3c5ca96c4513593fcacfa428cd7e09654f10ae8dcdabe85d46,0xf4eb4966dcc1440362aab5d23e7e2a0d6af1f64904b6f3a41,-0x35f59d02fa0c6547f00d46cd746c87e6c4b6e17476000f950,0xa3f31c02e1ff037528693143926d7ec4ba74188ca7e90ffe,-0x1a953215dbe7ade3de95f0059a0085993e1a2779f373dd84,0x3a36a478e00b453dd7f9370058080fcbc9f0b895ab5fbe2,-0x6a21da0004deed71687e09bc92158dd0fd2d6588bcde68,0x9e625053d940a566e79320de32394d7b9e4911da46036,-0xbd731d68e35f8509ced2db435246ed1c59d507d5ccbc,0xb0e5eb337f2e9b8307dd1562a6430b038b226fb138a,-0x7ca7a3a974dede57576781b9aaca62c399edd77d20,0x3f6b0ac3fb93cc198fa3963b15f7e5ad9d0c5bbc5,-0x15f1d50657c3ceff86a2eaa5e1f58b1d1befd4ce,0x4c08fdff9bdbfbc875483f34a4bde9f6629273,-0x91f13704a34d793d7e38b3369cfe5e3b8b54,0x801a1eeefc95cc024a7dd74ea252cd462b,-0x24a02dd0bee16b646b8196fdd27c9e9e,0x194d577b423fd21dbfda1f47eeecd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 15
theorem quotient_ok_15 : quotientCheck 24 62 15 num den q15 r15=true := by decide +kernel
theorem quotient_source_15 (size : ℕ) : (coefficientsPoly q15).map (Int.castRingHom ℚ)=polyPart (key size) (X^15) :=
  quotient_from_check (key size) 62 15 num den q15 r15 (num_source size) (den_source size) quotient_ok_15
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_15 : cachedMomentCheck cache 53 indices rho q15 m15 15 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_15 (size : ℕ) : intPolyRF (coefficientsPoly m15)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^15) :=
  moment_from_cached_check cache (key size) 53 indices rho q15 m15 15 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_15 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<6 at hj;omega) moment_ok_15
def q16 : List ℤ := raw_ints% [0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r16 : List ℤ := raw_ints% [-0x35f5dcbbd8991b4179f685d9c9f55d800000,-0x52bde44145661005d79c4ecb37051cb80000,-0x3c2e8aa6858ee0e54909df8519bafd780000,-0x1ba2727de417ed978f0a3d79f300b1062000,-0x8fe9027ee214bef6aba687030481278b800,-0x2355c273f3934f1177545f420561588fe00,-0x6cd034c321f0aa6dc8a4079830a6439e80,-0x10d6a8cc9951bb2a948f87f22c3b799380,-0x221c6bbae759123d66ba9f48a25016820,-0x393aa0b1bde6947d53f50914fe79d2e0,-0x502eb2f77c46dd7c7aa056c74ff46d8,-0x5e50ff5f32876f08696a662068e4e8,-0x5d660c5796b51e8bda4664eaccefe,-0x4de5fbec98fec9414925251457e4,-0x369e243a0e9bf112320fa9d17ea,-0x200d2d79582b07a9f44e9a8000,-0xfa088deb458fa6f6b10f395b,-0x642a15d85b90ead6d56e2e6,-0x206fa2d43effcc4265c35d,-0x849e984aa1e069ba887c,-0x19c6bdcd89fa9168d47,-0x3963e34300185d5b2,-0x51a9ff90033bd21,-0x37f66b6d4b140]
def m16 : List ℤ := raw_ints% [0x0,-0x215fadbd170df11ae75a00dc2ac8e01ea4be4b240000000,0x3dc2a0774464ca29ab22f3ef04dff4bb77bf0063df99f000,-0x37653fbd406c5ec99f3250e3531f945a17f66bb0c7b542400,0x2014ca65799ce547d6cab78071e4b9afbe29212071a23d4400,-0xd7b9795dc33b1cb22fa7039c98168588d8ca3773471244aa00,0x461bf190317e920303185521ae88a73a824c15a170806a0b400,-0x1255962a6c47c2bfd558f02992992300fc2cd72ec1838fd5ef40,0x3f6be1cee56e40a7aa083e6561d791a3f4ad36cd3f33a12c3c80,-0xb8edb01749b3d4304b33c53871f474f29a188a909dfaab155dc0,0x1cd29ff26e6c881f86fe3d4840e2e9118bed6a14e46aca4b84f00,-0x3e27b671ba4a0dc806e937d7e215a8df4c9e20efcf42ab259c040,0x74e86b80af14358126d55feeffd7f261be14580ad174a2ce27180,-0xc117cf2ccb5f9c4772bef06a4adb5f01cfa293881572e95eb7040,0x1198bb423cc6febd36cb5e4c2c08464d98f172b2dd9473d4816b00,-0x16be8687d776c55f6f2b7bf747775f14bf624120147457b260090c,0x1a24a61d414676dc971ed7a8afd1bf6c56fe920537acfdfabdc008,-0x1ac9624967bd91c5230c0fa84d59b0760724424fd90957ea536a24,0x188187e30c161a31359acf7936cc630dde5a4651dd5f7a5e648e10,-0x1409c796ff320eb425306f6ae72f79353df52b61c24377c6012738,0xea6971a0cdf94bd8b34b71028dff387f7f84812d150a8ae6febc0,-0x993990dfe5ed480faaf36356d840596e61918c667c3546db57f98,0x597a9522b5dbcd447238798b8c49a61de3439d80ceb23bfaf4050,-0x2e9f8b3ea436c3a0184627c5e4d51b5fb9f6c616a475f82b55baf,0x15a2c34066e9518f1c3e104d2c000bdb772b7c4048f80b501cfba,-0x8eb8303654e02f043ce565a3aba0b3ea4e92bb71958f15b31bb9,0x341c9ffc65b45d99dfbf24c42ca133c3953baece2dfa69efe2ec,-0x10c97bd19ae73bfcc925fc89da84ee1e0071f8f22510eb7eddf1,0x4bf9f7d4b6e0356bf64a5c6344b7372c6b3d362c354ecfdc28a,-0x12c3ec9106b7c49e484eb8f34f317b562a1e5d7a816fcc25e77,0x405060f064d6c57b3122be441075178ddfb422a6581b0336b0,-0xbd9efed5ad50a6148ead7299da587ddb4620d72e037bd5932,0x1dc4c27fab18f56b0c088212ca1af54c0b4dad2b68c233c9c,-0x3ef622726f7af4157968e4cda2cc0987dabfd3a3fac1040e,0x6e8c10f2c9658cea7184da54249739e66421f9259fef218,-0x9e5a36ec5f6d8d9a849156ff0e68bad576d859ad9835ea,0xb51d36c4e65c3e790f256a4c9729d4b76210874c3cd84,-0xa0fb1428d4ec9b5691f28086f04910bb2e6c7f672136,0x6b69235d1fd7aba76a37eb3c846768d8f08913bc520,-0x336a8288cbc42b7fb5a5d0854cf5d4a0f723521f83,0x109d3f373667b2e9b4fb1a89dba7611c316ebbd22,-0x35454bb2bb068289be34ba52bcb54e0b37d7fa5,0x5d96df97e95783c24b943e6fd9c86cf426ecc,-0x4a357a63f8d4003031124033590aaef13fd,0x12dd51801ee5188650ab637af331b9cb2,-0xb5c1298b8f15a59eefc1940467f2b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 16
theorem quotient_ok_16 : quotientCheck 24 64 16 num den q16 r16=true := by decide +kernel
theorem quotient_source_16 (size : ℕ) : (coefficientsPoly q16).map (Int.castRingHom ℚ)=polyPart (key size) (X^16) :=
  quotient_from_check (key size) 64 16 num den q16 r16 (num_source size) (den_source size) quotient_ok_16
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_16 : cachedMomentCheck cache 53 indices rho q16 m16 16 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_16 (size : ℕ) : intPolyRF (coefficientsPoly m16)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^16) :=
  moment_from_cached_check cache (key size) 53 indices rho q16 m16 16 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_16 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<7 at hj;omega) moment_ok_16
def q17 : List ℤ := raw_ints% [-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r17 : List ℤ := raw_ints% [0x10439173c9fa83c862092b60596b0ad0000000,0x18eab2e79de3e9e0551cda8ac2d8af73800000,0x121b0c1c6136c210b17d3f26c64da612480000,0x84e1a797ab26b095534663b319c64f9a40000,0x2b33307995787698a44fec23523068092e000,0xa97fec85317e5259855855c982c258bb8800,0x2093f8e4f69a99735ffa42c28c2eaf073200,0x5089f01de45cb3bcd32f2ceb6c10886d180,0xa2e144db172e76307aa8dc9ebdcc92d880,0x110c320398db442b4e84e2787af5b793e0,0x17d609c303e5c630b0042b32dec1c5620,0x1bf948ba7128c572aeab13ccdefc5628,0x1ba18a10e2fd0bf90219ce9ba719658,0x16fac96319b7ce5c99f69719482102,0x100f65dcf7f7e48467fb22c23f39c,0x963e9b19895d05966131bd0f116,0x48f3062b1ebe80b20d07f2bac0,0x1d159adfbbd29678444388aa5,0x95dc7a8923fc7fcf377a31a,0x260c574f81ae816be93ba3,0x756b3fb76c913cf16c44,0x103099051932b3d02b9,0x16c7f336fc5bf37ce,0xf6562c18afaddf]
def m17 : List ℤ := raw_ints% [0x0,0x3e9365c28b3a241271c8c19cd038a43974e4cce380000000,-0x72c6a3dafcac1da78f573fb3ed787c9e63895b97544703000,0x6602ea68473ef6b0a79ab2251727559238322b6e9d98881400,-0x3a867c2754f845ee9e82aa01f04838db21a7831d9799574dc00,0x185c1682d91e07fb7abcce65e2a27b4c257e2a7567a74301a800,-0x7d69a7e1f505eab757611efdd6237cdcbdc627bd429d75c24800,0x20763cca7c5e51639d04414ca04691b7bdb73368c14c8e1a8f1c0,-0x6f1bbba720022c6fd06b1e7a0aab0a4c8e71cff56da5609948580,0x14074da8fc1da6ba5c6ec01e6e6e24e4f62f26311a6d5eb8be48c0,-0x3162add5c119cb30c14d9bb568172b1b5c1b617ea7433ebb496600,0x69433282e6e29129a02a3707a34c6c932fd6b03e99635ca2490080,-0xc39cf34cbc535c080b819cc9971e9aefb80285eb2d608863001200,0x13f12f0768fbd29901a10c0dd4cd549a2b9d82c3c78a9c464843f80,-0x1cb3f1692cc94adf0ec0ce1e2e15bab4340cb27eeacd68743b6e400,0x249a9e6dcbe5fbe24e602fe22d2454781322e04a63ea3dd549fb6d4,-0x297d8f604bd2a571e5cbf6b71e7614012c24da8df7d7275bb4f4e38,0x29e60a5c2498d8531080f383f0e5143d78c20ee7b5c34c791a62e5c,-0x25c179a817c3c4d1a1693bd37396aaf5c4595697cc06cd6aedbd6b0,0x1e63a5916e18d435cb4c0343c344913ed1beadee4ae61f04a515ff8,-0x15db1c0b3d75d07fa1fcbe9714a9884ca6588fa41dad88268e95da0,0xe0ad67d02a28c5371b87419a0b9445fbfe053d2500414b1b1d0158,-0x80dc18b54943597a09047a54f13b9515f35e6b78161db6843ddef0,0x41e25783b3d876a0258e4c3143839b88a33728a736df9c98ded269,-0x1df8c8fece69664f5c975e3868ce2f9a7c9a306f12c7f3b705ab16,0xc19be07a8ccf39b2d14ec45666be4261b81acc2e2155e6cba3b4f,-0x4525b1a9f57a74a0fe87f66fd5adcf82bf869d54cec23778296f4,0x15c27a56de7cbf44ba9c9d437f2d09d3010a42d993f92d82eaee7,-0x601177c929312617dc7ee566b294d5f75d5a80684be0c44d6026,0x171c12397a9b48476a3a0958e19bfc243bed5f28e05bf1f4d191,-0x4d00f50f5da9dda128aec434ea1229639a35abbcbd3b4911750,0xdc4aecae6cbf29f96b56416b3ddd7b081ffad0d1f1a61e9b9e,-0x217b40f2d180524a676f9cf6f82ae593c350cc33a792287f44,0x4461f228adbd464b5bbb4950f10bf4682be0a0611bf4134c2,-0x739ac6e4dff4f833d04c6e43f53c53a17dd72c5d59ae07e8,0x9ee8a9b7d20ef8eaf39b67ab9f064f36fb0f84785d3f976,-0xadbafb1af2dd6e53ecbd38607abbe66d70c6159bd636bc,0x92ee7a0aee8ada4e4506213a4ad05861fb63aeaa1324a,-0x5cc89ac585b3fac00e901be11c5aa86e8284e5530fa0,0x29c470e9a5ea8404b314e8e6d3d16ccfca68fd2f835,-0xc989382894e88d45d0caa1624410251b05ba21bee,0x2559eb4893f588eb4bd647eb022d55d0ca3c0603,-0x3c080870f1182225a08373d53d4874021ab694,0x2afb4b8aa51f52025da403aeb11fff91d45b,-0x9b67a9457b0c7818d90b9b161aaee0f7e,0x5192de49df0b8b4fd4724ee7fb261d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 17
theorem quotient_ok_17 : quotientCheck 24 66 17 num den q17 r17=true := by decide +kernel
theorem quotient_source_17 (size : ℕ) : (coefficientsPoly q17).map (Int.castRingHom ℚ)=polyPart (key size) (X^17) :=
  quotient_from_check (key size) 66 17 num den q17 r17 (num_source size) (den_source size) quotient_ok_17
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_17 : cachedMomentCheck cache 53 indices rho q17 m17 17 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_17 (size : ℕ) : intPolyRF (coefficientsPoly m17)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^17) :=
  moment_from_cached_check cache (key size) 53 indices rho q17 m17 17 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_17 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<8 at hj;omega) moment_ok_17
def q18 : List ℤ := raw_ints% [0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r18 : List ℤ := raw_ints% [-0x47973c0d2b77374af6be1e1965453f805c00000,-0x6d971e5994ad93a51ae46a74ffbf250cf0c0000,-0x4f90240b974c502cb95fc7572093af0ad740000,-0x2475ebc1cffd81e7d7a4f1bc4b9a1d35eb05000,-0xbd749dbdc9289f54ff647fdaddf49f6f8e6c00,-0x2e67f3ea43b34a486d3f1797cdd6915dece300,-0x8e879502f18158018afed0ee07a1ddda97640,-0x15fdfdf9666caf1faa7226a35ade871d95740,-0x2c68c3483bfe4dc2890c463ba62811bbca90,-0x4a3eae6ec502df2a05e57e28a17c0d58e50,-0x679e65073c790bb039325fbf4d4586094c,-0x795bbc36f6daec063d51efd8698c2597c,-0x7799b1dc91053f1b98c25ba6270199af,-0x633755dc09ac83d3d44ce34094210e8,-0x45251afdd2615f953d240c651f70e8,-0x284cd6dc4bca42ae63a2407f9a010,-0x137f2ecf36fa6116eeda15fcdf1b,-0x7bdcb42bfcc43b8f05e54dd770,-0x27b370817734a482c4eb28b23,-0xa065ac88bdaa7acf82eef9a,-0x1ebd9b0fc1d7f1bcc52dc6,-0x434ee2956d8a8878f27c,-0x5ddc76ae7251badac9,-0x3ebe410b0af256f6]
def m18 : List ℤ := raw_ints% [0x0,-0x75545eccc50d03a295586b06066a33ebbb2d002a900000000,0xd5590ee2314c265044f8f1e9311b31d2f617666a9ce0b57000,-0xbbf00fe0e1fb186b56562c9a291d26cc64ded2551e7076a4400,0x6ad65e48279a518363ef3d457218174183043b9c89d1bc2d2400,-0x2c0ccbf930743bfe6340c3a57d9a6b5afa25309974b2f4058ca00,0xe0961385380885bffa5b78f9c7cb921537ff206a5b028cde9b400,-0x398cf588ea2006ed9ac584d8e50fcec88089b70f0ddf74f50cfd40,0xc2f2907630e895c1e61673932d6c0970689946bb22cd254a37a080,-0x22c454853aa545a160911cb11e6ca698f3293f1bec15cdfd15385c0,0x54c842f780bf5bf6a31e38a067ce9a26004662b91e537849a19cb00,-0xb2a6410c7a2cf3927cfea51b6d82cc1ec571edba2d461451f124ac0,0x14812c82e43ffd6dd9dd1d2ac7038621d6e66b43cb72971113ba4c80,-0x21097c11dcb085be52508870c0f0774aca318dfcdff467832ffc45c0,0x2ef28aaaf1e4e1a8633ce9455d2cfe222a75ac853808632e00be3900,-0x3b1507e1ace0a8fd3295d7ca824b45ad96e0d12becfdca95f792594c,0x420d711e0d302d158e78ed7039210a0d7abcf34317ebb98d2f541788,-0x41c079174e805ec5dc71eda5a593cba19b50b8dde2b50e0ae3acde64,0x3a5eed16bdcfdeec28b98682ee3ec6fec541cdc70bc0297c657e0410,-0x2e411ced5280978d772178e5805ba1a18490b8ba4a157e489dbfabd8,0x20ba49c9920180a4c9367ad15a2257c6d37d66ce76a13c0a62348b80,-0x14abddc0ee28f1cef62712df97e114512031582b620e4403bd13d5f8,0xba531e951ee9197b3b570825684655574781b502f78f307ff4444d0,-0x5d7d860cd7cea47ab273c7206222342403eb552f1e4a23ab6a1bb7f,0x29b26e8585fb90963f30fce81bee6a3db5156bd5072fee114bf3f1a,-0x107c9d7fece9b05e7ff1b3a8ec5b08bbaf96fd21d39637eb82175e9,0x5c285046a559009eb34880474625c0c3e86198833b310193ce5fac,-0x1c54d184d998a7efc5d255d871157cecaa8adb4b0f9b072d6d1341,0x7a04b1647a544ab42f18366ff96745e471f4dfa6d6566363426aa,-0x1c965049c730e1716eccfe3e16be6e8b5b9737f9a8298650235a7,0x5c9b37deca3160684a644315e5df97718a6f28b657f715def0b0,-0x1010a7166e247b6fe8cacaaed3c395db914a6465d6c12c158f92,0x25d127d889696e367203b877bab758bce8a04a4f964bef3aedc,-0x4a92ab467ed7a6d94c9981b8f9e3bc9d13c72b5fce41078a2e,0x795bf6761a6cb2a8ae4fea938ad22d1b3ffcf54b994775e98,-0xa0099a652746fe505702be22fa6aadc3f05ba2e0838a382a,0xa72fe326448a468d079faea51f1fb9d6b681eb064d3aa84,-0x867cf4e1a5fa51155e157c175f8eb9fa6490b672d506f6,0x50566e13595474ba1209c35bc6a6c0ea7e2fbb3236ea0,-0x21fdd1dae6e28793eaddc93abea918f7a737db107413,0x98fca690b195002736b0d77a750be7460cfd411002,-0x1a351dba21c063bba1adc736876cabea3d4156a15,0x26836fcc1a2f728e1f13fa6f2ac02e434961d8c,-0x18e3e01026f122b38bd698c4377f94115644d,0x4ffbf62d4c7f131185e032e17db1a4d0d2,-0x2499791bf7593b445f371f7b5310f5b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 18
theorem quotient_ok_18 : quotientCheck 24 68 18 num den q18 r18=true := by decide +kernel
theorem quotient_source_18 (size : ℕ) : (coefficientsPoly q18).map (Int.castRingHom ℚ)=polyPart (key size) (X^18) :=
  quotient_from_check (key size) 68 18 num den q18 r18 (num_source size) (den_source size) quotient_ok_18
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_18 : cachedMomentCheck cache 53 indices rho q18 m18 18 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_18 (size : ℕ) : intPolyRF (coefficientsPoly m18)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^18) :=
  moment_from_cached_check cache (key size) 53 indices rho q18 m18 18 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_18 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<9 at hj;omega) moment_ok_18
def q19 : List ℤ := raw_ints% [-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r19 : List ℤ := raw_ints% [0x123c0a0f63f8db19da909df0de242a0b7c9800000,0x1be4784a1e5a9a15683ba9543d4e31cd23db80000,0x143bd2306d3901f433f0f549ed846f8ca6d7c0000,0x9439e92503417d667562985bb253553cf4eb2000,0x301782e86ceaa6d1348fd9ba61288aa990fce800,0xbc47affdfa9dfed74a3da902f2ff1f5c8f27200,0x2419d55dc4e66f032486f14242da9f43bac7b80,0x59038ef016dd5254331e4b3da14e875a349640,0xb380671b61be9a0e594a26aae777c41217d60,0x12ba54ec5893ba5e5f18f0e32ae9bccbb4590,0x1a181264eae97cfcebc3ce1ea22f96409a68,0x1e816df48c809e5f223e2a4f10e62947bcc,0x1e00c371a7bafb04561ebd93ee3eea332a,0x18d56640dea1ff047034e5ef82cdc1ed1,0x11437a6398e355a1b10cc0f2c4187fbc,0xa08a038ba61a71906f77e3339eb8d0,0x4d6c40bf513e08ee5fca8c71b319a,0x1ea1ceaeab7bc9c4efc5a3838ac5,0x9c751935bdd6f24dd81aa07060,0x2752cd998a3d57e891265b2e5,0x77efce34e91adf8e7c4b040,0x104f6e344f534597efd5ba,0x1693af9ca24e0fb74c18,0xef58220b4aa93f7df]
def m19 : List ℤ := raw_ints% [0x0,0xdbfe31bff17866d0d805c8ab4c072159fef4604fce00000000,-0x18ca95607df17e0808d33798e6c0cd037a5317c64da1348db000,0x15a6444a286878c396b935194cf5051beb6605f45f4aa5709b400,-0xc32832699e670d722f31312258cd586ab382c79444e790172fc00,0x4fb993a4dfbcaa0a95aaab25f46617434061cf5cae3e07315b5800,-0x1929de9b62b9f627bce35e2c8b5c014aa8d6cdda08365c37161a800,0x66293fd3f5546f275f7ac413595b299c113fecbcbd10e5d90efdbc0,-0x1568fd4fb51b1851907b2cd63e276212ace3537acf5d4a65e75d1180,0x3c742c4d94e4c39c506f81ff9474391678e7fe07b9c496061a0204c0,-0x91d3ec2c3aae1bcd507c9da30139241ebf50aea337e13bcbf01f9200,0x12fd76444cc38deae369c25833d6b096b4ed54abe7d3ba27226afec00,-0x22780b83acd6281e2dbfd6d1b05073f3d3d4cfb4d29ff93d3edc53300,0x36de38be809921cafcc821b506d12f3e404eefc49c5ccb40dcf76a400,-0x4cff055c0e1b12d6fbed86fafc59366f7bb2f8114a2786ea9c1a51600,0x5fa3a96d221f8c0998f30f7e98ae81aac73f48815338aec4d6d458294,-0x697a4b8a3753f2c4c21b814ae0ade28012cb6c7070ae24c10a73adeb8,0x678502b9ba43702b8168b2c1fe24d7b198eb657184b6a005d800e391c,-0x5a8cb326e5d869ec77c5297454bdb5bf83137ec3d34efea43d0b9e2b0,0x46a73fcc1c3620d27f0ac4aa9969403f11be1519d3fed83ebc695fed8,-0x313090c9c6dcd5f7e810a1c4979348b6426e397dedf4ee2375c8688e0,0x1e8c13559d459caf99708999cd27674df37df880b96990e87a6963378,-0x10e7d6ffbbc5e019b5b9e71963d4a57afbf6f0c6b9fa718994778aa70,0x85352dcc63d76032b5449f5291884a9d67c1d9edeea3944fcb7b1199,-0x3a40b250bb02a4bccf308907b3ef1cb1e4e6998e5cd763ea4962b5b6,0x168f1f01a1e7a817a24c8961f17ab2c6aeb0a8caa59c8a7795f60b1f,-0x7b5bae608171abae5f32b86fccf81bd5472d34e484b7baa251e5c34,0x250c9d0d53d7bdaf9e2e933fe3af7e98bd4754d260c953c9ec7da17,-0x9ba8c262a495dc6880c8ef5d7737b4d1ee3d601904064200552506,0x23849200982e483e5f613e006c095fbb63ac44e133890764198fe1,-0x6fda51c8631631e8b4c146d7f20df13bd10c2f1138b14010e4d50,0x12d316b9e6a0a5ea097e506c13b9f7e5b5e6df2c5c13d260b033e,-0x2ae3d94818c7b45704da6f3f9e3a33ef21c06e5b9504fad77104,0x51a50dc4926372259c8bf2b5fe0b54bc420fec11cb1515b0da2,-0x7fdfec25538790262c0fcbf07b91a20cb2f9c035ff75202168,0xa1ba96cfd8fab8de82523214ee632c8fd631678888b0bbbb6,-0xa1637c58b9f1f0fcb77b975ea39384a791486189d726b6bc,0x7b6e08578e1fba507196f78a5fd0849b704ec3dd0caa80a,-0x45b7412ffb20bb61ae54a5f0487668315331fdd38ac620,0x1bb5deea6ad84e777c8d66ac002f747e9d2cfc91c22a5,-0x74447291b7141352d4c756cbb00d83faabeb095730e,0x1266581177ee7d3ddc2820599fdefd10d36ade7f93,-0x18b63dc092455f7d81ddc47a13420e51aa6e95d4,0xe691c5b9723af26fecbdd16caa8745fd5358b,-0x2926cd6de352a1fb2e58ef03ff7e5d12e5e,0x106a763ae95cdcd9652e7bd7c643c26d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 19
theorem quotient_ok_19 : quotientCheck 24 70 19 num den q19 r19=true := by decide +kernel
theorem quotient_source_19 (size : ℕ) : (coefficientsPoly q19).map (Int.castRingHom ℚ)=polyPart (key size) (X^19) :=
  quotient_from_check (key size) 70 19 num den q19 r19 (num_source size) (den_source size) quotient_ok_19
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_19 : cachedMomentCheck cache 53 indices rho q19 m19 19 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_19 (size : ℕ) : intPolyRF (coefficientsPoly m19)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^19) :=
  moment_from_cached_check cache (key size) 53 indices rho q19 m19 19 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_19 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<10 at hj;omega) moment_ok_19
def q20 : List ℤ := raw_ints% [0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r20 : List ℤ := raw_ints% [-0x458f02a682011dacca8c7182b009ed7d7e85c00000,-0x6a53d970f42d80dd4305f46c4f44ba45b95d8c0000,-0x4d130ecc0ed78be6e6881ea73530c758385b3c0000,-0x2342b410c8557d61b6e74462b83380799ca05c5000,-0xb6e20b8a271f15ea7b2b11913a843165e280f4c00,-0x2cb4d8bc7ee2856cd8b3071190b0c5f9ca2e4db00,-0x8902679c1562970a6e8b013d73a1d99b65c40c40,-0x15170559bb3c807f194336f65383cfc3a5178dc0,-0x2a79e0b6b0e42f04806801cda21df52950565d0,-0x46cf40287d88afd063d4499f9dd2cb3612c970,-0x62836b58dc6bbf349168d07387aefe7ca9f9c,-0x72faa04025d4c99cc81a3edc769f949dfd34,-0x70e12e6d1b4e7126ac23ba28c16ff320e0b,-0x5d3e5bd149ca1540f56869a18ac380f416,-0x40ad0e7d968c4528c5a8103264da24f19,-0x257f358a6dbfd0ca6d13c86ed82c5bf0,-0x12088eca0af071eaed3b827366e2d61,-0x71cd5138a5110627953764b9f8096,-0x2433661ff6c5f26a3b6273d5bb03,-0x90fe84aaa4181a65ef77bf1a54,-0x1b8347a49e9a9c0a154439c84,-0x3b8bfbc0a917d8198b22e80,-0x51eac0d073eb08e42f3c8,-0x35e1e141709c8ea9aac]
def m20 : List ℤ := raw_ints% [0x0,-0x19c7c9d47e4c1c0c7950ad8412e8d5e88be0a3495a2400000000,0x2e1a3c4a8531f41a53e47ca1eb18cd47a40d2f4a59303740cf000,-0x27eb68fdb74f55208652d9cac046efaad8127413f30c1edc196400,0x164b7343f52065f206aaeb18fc1bdac62b125597627ea08d3160400,-0x906a1f6f0b6cee7f7171d58260abbdcf592b7575270237edc696a00,0x2d289a86b1737a21e242907491bccac3f22936b43d5a9651ceb7b400,-0xb594de294111928d22af6cd2db4a1c9a00db4b0f0746ebebe76e5b40,0x25ad66967f5683bc5ba2630e55cdf56200970f04cb12acb10809ee480,-0x694ba8406cb3e872a83c3c8d245b7f9daac2bbbe0eae8fcc17f7aedc0,0xfb4ccad04e4bb106602f497757cf6a25a647bf468862d0da53670e700,-0x205d70236a07d7ff582bcf7813aa01e78cfef822e0d4e61e4d67e95940,0x3a1354528b3f166b4379a35936d73dca6ce7a6b52e2e92fc358f94df80,-0x5b59ac6204e46bb2b87ce9743a1614c2e8428b2d8d5fa4f91b27c1d740,0x7e9d132121903931ed88656e35a58c83e0f591d2c6295d8af18a8a7700,-0x9b41ab4a44938199f589cfcee66087be6ee3cab75d21d187093953e18c,0xa8f1a5558e77e8ca2e277a51209e251b99d1c6655cb3a9568b9006cf08,-0xa38064153ac17acaf047ceb330a374b75e789af4ac357b31582406cea4,0x8cf093c0e06a8fa0368a9cc3e5d38f1c33b941c2697e4a31386064c210,-0x6c4d4ba1808a3a4817d183f22a569b6bc67004c9882b2b3db95e9c1578,0x4a33ebe187f56d42b3b45113ce45e47100204b94f4479a8339ba759140,-0x2d50084128722b60b1a03a5ab8360c493621810449d9c3ce96896a8758,0x18a36bdec4d039bbbe2a4be8ce1d5b7d4230792f7bc32a2cece6c8f550,-0xbe9044178cabeb736b7486f36c7d3465bd3a4a9b25df7d0065683294f,0x51b7bd35fc8c54780c18c7c3b241d8ba8058517cac092a64afa4d767a,-0x1eff64e0a8b4f5ca4913055086c4e134ef7a25627762c6a1bc64fae19,0xa5d35fd1452166136b22c806fffae65154dee372257305afdf6ae86c,-0x30a872784193d1274b691f588ac8443bbdad15991b7e3e7b72708791,0xc76e08997682d3a577c55c56d3e111126ca1934e407f27859d1a8ca,-0x2c5160d65360c78f4668fdfe9dc729a3724801bb2cdf90efeb0b5d7,0x87abc0414ea42c1b233ffc7e35ea764847f8b25207cdb15d0192b0,-0x16263fc0a3324f81f08b3e9d8cb4e14377d5611d97a2a2ff6491f2,0x30d6a96b88f4f61ebf16cfadc7c4d741e3ce35827446517ec411c,-0x59bab8585d00f2010949c45682dba1f3fcbd29a81a5b4cae104e,0x873982d132f4976093a87ab98da14c16863c1760b4378a62b18,-0xa3faa51ebe80c693131360ceb1ea59ee931c4eb9d03d1f1d6a,0x9c40c1c00c58d601269b7800a24913aed56dd671c2aa92984,-0x7192055ba198bd3404222a3361d6a7fac4ed1543d66ab9b6,0x3ca002785ac57849fe421714f0af3d0e95595f69b015420,-0x16a034bdf79e8d9e287fc4899e655675294307841986a3,0x587448a4bc6495ed32291099dcf5cb8a016d2382bae2,-0xcecd293a6fbd6a703a3ac9a58b35531fa48a9c1a85,0xfdb905768330deca0f08b1aa8bcd910e96e5384c,-0x85766bf586ad4228afc546baf9d662fcbe099d,0x152a2d1775da29ad54b7934a6e04dd7ba6f2,-0x75c571f92df2c4f917aadf2f09e3328b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 20
theorem quotient_ok_20 : quotientCheck 24 72 20 num den q20 r20=true := by decide +kernel
theorem quotient_source_20 (size : ℕ) : (coefficientsPoly q20).map (Int.castRingHom ℚ)=polyPart (key size) (X^20) :=
  quotient_from_check (key size) 72 20 num den q20 r20 (num_source size) (den_source size) quotient_ok_20
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_20 : cachedMomentCheck cache 53 indices rho q20 m20 20 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_20 (size : ℕ) : intPolyRF (coefficientsPoly m20)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^20) :=
  moment_from_cached_check cache (key size) 53 indices rho q20 m20 20 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_20 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<11 at hj;omega) moment_ok_20
def q21 : List ℤ := raw_ints% [-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r21 : List ℤ := raw_ints% [0xfa8ccf2d74721f2bf670a81962a67410de843000000,0x17ebfc969ac0dcf61a243b445ef2705192ecc8300000,0x115417af4e4be8f1e23ff6fb1a322df369d654840000,0x7ebf146235744c5169be7f568fe4287fd5cfd064000,0x290da5a236f961c699aeed5cd1b53e4e936fbbd2000,0xa06dcf5670674392b68b9d6ae1336791306ca43000,0x1eb30062469255452bb14431c76aeb6bf462c23200,0x4b87ad38cc7370c0e71df5ee1c27b8e5f99a81cc0,0x97f2b4faf77d4cf7713d1f728899430d175bcf80,0xfcfd76cd93879a5b62ffcfa7143d5cd88675e70,0x15f7e35bb20295b23e01f2283a21381dc5f3700,0x199a1a3172dc91207f08e524b1ed10c66d8594,0x1917e7ff0efa96414429a30ff71da1b962ed8,0x14b0de2d631898af4b0dd33f1fa9ef0af2f5,0xe52b7539883ff17103cd3199e365def5b2,0x849238c24a49c5f936ee126228784d357,0x3f99ce2c5bc6fd9c99378f7ed0238ea4,0x19041b8534412372f65586ff225425f,0x7eee00ddc36885af287050ffb190a,0x1fa9d993920b502e30e75bebaa0d,0x5fbff5d66f6d16d510a5e122a0,0xce4b597c56116d467d285a7c,0x11a4f1f01479900ee8e8528,0xb8901dd0b647e8a14e88]
def m21 : List ℤ := raw_ints% [0x0,0x30569a6e6cceb49763774557a3749114064532298903800000000,-0x55c046acdf2581d1c75cbca372b83c3e5b3a3b963d0ff325773000,0x49a38187f1a9a675a555632762b420cfd337b3617a65038eee05400,-0x28c6d88159010667e8e1ef9397b39727ad38a059485d9f969e201c00,0x105d0000c0572691be3da3240485389a2182fad941748e42480ad0800,-0x51205203be99bc205758c586679bcd2683a9092994758138a59730800,0x143256afa77a1b4099ea47af9670173a82d1f38c96e171b0e2d0c8b5c0,-0x4266886b80e0d9e7e5bc650219bb9b8a34bbce38d7349085c6e0bc3d80,0xb7b3b28cb146a8a842c3289bf17d653e5e2b708e278891f8965e9620c0,-0x1b1dbe01d457584e349daf37ec09e1d64375ddbe3bb262323d532f55e00,0x3745e7274dcbb2b026110f3b4c1431c165d07cf1e076cf93f0763786380,-0x6211a8b3f05a9fbb27bb1b8497cacf7412943bd572e123e7405735bbc00,0x9875c692f6c94856f3f824dce5424d4c89638019a4bffb37d92fbbffc80,-0xd0c02795796c4dfc9186368d99f1434147f942ca10ff887b2fc51b4d800,0xfcbe0ccefbbf9ac1660c4330a8bb7b8715d01165e9fa74966aff9ff6654,-0x10f67438102857bd286a8a98ea3ca6dbca49d35d0a86101c462553a5ef38,0x1030d08dbdeb975d98307a88de6cc1e9c0831efb52823e0394038eab0fdc,-0xdc18dfc205eeadcad4821f7a505e3e2a6de8e470dc19f607bff9b82f6b0,0xa6963111e2a43f345c4f3a7cad641814b75a24a0a78a2c04ddbb5c96cb8,-0x7056b291ceb45bd4fcc4b4c3b76dfe92a9163759b92c252ac0471c47620,0x437768b865a091ec26c57eae75e592a4bf7ffd5914f0ff8c1e78d1dc698,-0x240bf2b685d7126b5a5c5f9d596c51e48df0aff8ce4edef609b4e0bc9f0,0x111b2481f393956821615785f702c7c5de44b11c7a17792fe01f24726c9,-0x73198f67ee59c0474075852c05902862c3d5fb6763321b673f16ad9056,0x2ac4c8fe71b097441823ee66dd5e2c990322b9e0183d7e77486dff20ef,-0xdfd87e6f32fc1a36b34baf11b537b92bde093614ae258600ffb349574,0x402c5f84c9f4319cdd3f251a8950ee04dc05eb8aac2e3ae45ad395647,-0x10095fccd9eb133f3894e343c007b74e90bc57a4d205882ecece9abe6,0x3787ad28ee7c8a6e920c22d1f878b698d12c62f7dba68fb0c48d1531,-0xa53da197f77983f5112ddc2f5f3fc9c4876c01ccb357e6eabaa5b50,0x1a2aa9a60a0a000b0002803440c25588d00d0ea02fec1c74a6536de,-0x37d42485550c23bc9d82d7a2fb3e04e29dc7a30a690ac9a9fb92c4,0x62fb00f07ae5e031d2419dcd31dc28705f9979a7080e6d391f682,-0x8f7e6b6ce008e4b66004cbd124024174b4f42510202e88b5eae8,0xa6ca27fdb7d3fa4eba4b09a71f6c3cf183bde6978d27f7caef6,-0x97b5923d608e2d39915d4493919035c23942b21859882b3cbc,0x68c086a6c3bbedb2df3d2bcfe164bfe48bb5def7b3981ecca,-0x34d2c8c8c3ae4a59c564c1fde49b6f5f8529df94d84b00a0,0x128055d8845c23ac48bafd04459ebcd4d2a5322af93c315,-0x435bdd3a007917be6bfbc5187193eda76a36bb8072a2e,0x915657b70f857c442de93ce28eaf4621ac233edd723,-0xa2d2a39727da1bb6182427f503f0fe88a295a6914,0x4d3c3630be1c5b4a6644bed143d5e59e9ef99bb,-0xae1a6b6e820a7de4e3af35526a7637dadb3e,0x34caa89e44b203e239080e4d8bb7613bd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 21
theorem quotient_ok_21 : quotientCheck 24 74 21 num den q21 r21=true := by decide +kernel
theorem quotient_source_21 (size : ℕ) : (coefficientsPoly q21).map (Int.castRingHom ℚ)=polyPart (key size) (X^21) :=
  quotient_from_check (key size) 74 21 num den q21 r21 (num_source size) (den_source size) quotient_ok_21
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_21 : cachedMomentCheck cache 53 indices rho q21 m21 21 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_21 (size : ℕ) : intPolyRF (coefficientsPoly m21)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^21) :=
  moment_from_cached_check cache (key size) 53 indices rho q21 m21 21 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_21 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<12 at hj;omega) moment_ok_21
def q22 : List ℤ := raw_ints% [0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r22 : List ℤ := raw_ints% [-0x35a353bbb3c20c974ac32be8f28be313fb27232000000,-0x51e42c70dda58106bc0c077b193b0765de5dfa2a00000,-0x3b4861e2d822a0deac8d0da1d8b3cd8d92acd52300000,-0x1b150ca9acf4b51ebbd3efedbc98519c6df4deb818000,-0x8c3f26a0ca48a69c5d0e7a344882a3ab4f3558b46000,-0x2239d722947429684607ce08b59935dabd6b357c4800,-0x68b2aa0d0949698644c9f5680ff423b9bcb7e4b7e00,-0x101582b7f1707dcbf5b65bf4f3bafe34b75c27ca400,-0x2052d22fe6e35d65e2b1c9d97c8ce633fa30682ac0,-0x35c1c6650ff1cdd3170161885cbed959e4fd50200,-0x4a98565d7fa771c23e06945a464fa0869429e630,-0x56d0d907f75e4b63aef824cf16e084ec4509220,-0x54f711ae66cf0cb28c85ed994d5a55e7972534,-0x45f1c4d8b5a6cc8b4103765566ccea4fab728,-0x3054e8928a396ce8689c9e4c902ec762a6bb,-0x1be75cc43ee09aa7060eaa6da483f32daee,-0xd5b7e76ce38faad538aa3334ce92815a1,-0x53db3b2d1283200c40ebb037d04257dc,-0x1a852125a63074371302a73f30c0361,-0x69868282b3207b13a144c450bd356,-0x13e01028571a95c9bdcb4d78012b,-0x2aa742b95008093e87ff4cc760,-0x3a1bac1a2f70aaaec8d65e74,-0x25cad4b4b48bb68935aeb8]
def m22 : List ℤ := raw_ints% [0x0,-0x5aa2618f0c03929bda7fa204527a90058bc1be0de0e69000000000,0x9f87dbb836328b24160b780c7211148478e1ed035610f4d3e807000,-0x87e53d22bb783eb47f988fd9b6a7d0338353563f59d94c3f0f698400,0x4aa046058dc56aca2c4170a6b96a0a0953820a9036dbf6ce936afe400,-0x1db092583e84530000455da4b1dc69f66030913848ee03fdef7f6e8a00,0x91e3f886fdb132f925fbc748b34b72ac71c42f19842a156a74df2ab400,-0x23fc87bac302999ed99edf3e2e35fe5be9266f3db9e9412995da6318940,0x75301294dbb0e94a333595aee58d0aa14ac58af3ecb3b82af004a6f0880,-0x1410381e03e4b797e74541615c7e8b7fd061a7f6d29679af918f972695c0,0x2ee67c7b4b0040856abe532a1f8572e50fe52e2b4f4cfabcb3a1198aa300,-0x5e960719b8b330fd4890a3e653fa61623d8cde785876710067b89f93cbc0,0xa5f83d0e1cf02c9fb667890e30f566c209548cc4052c882f98059ab06a80,-0xff0f4d81359baf497ac37af3457051019c6b4303ff84efe7983e36f744c0,0x1590f4edf1218c83b61e86b68f7cf7d3c1a4b9b91b122b5d8e9d439d4a500,-0x19c932aa5c92d79a4938dd6bbcc43306ea197d5ccd75ef6a1480485c501cc,0x1b54795b0e9825b4fe4ac0f95dd2c875cd4a8c0f64b3845f5f5ab15b7a688,-0x19bb5e04b3df27f3714dcdadaefcdedd8f914d912b51cb7a345cae10c7ae4,0x158d5063c375c4159e91623130d1994158f1b82e2695b454cce9ed16e8810,-0x1011c9c6ad5c55db33e8ca3f0f7a4b84fdbc1fd6a8d7a747ad0aa079b3c18,0xaaad7d5c430e739e7f87fbab2a19273bdfbf41abdf4fb739d4e2ddcfcd00,-0x64d233228d61ad5e46b1c46b54534cc15080998e05042f69f3928b9dbbb8,0x34f0084613c3b9239093c2055295bb2cf4cd7ca459e124b196917471f1d0,-0x18aa114530d46115b64e17b19fa011ab0539294ff02a9b2c6a52c6ae9d1f,0xa2c3ecb0c47b96b8f02d87a39903a8da3a9fe6147900e3f96cff46325da,-0x3b3fc871c7d9bacec1a6faba8b0b31664fce2a4fcc8d267897c60326c49,0x12f682a4242b67ce3ebc0e658b0bbe1617e423bd2e3966400afbca93d2c,-0x54fc54c7959321bfc0a24dbf3e756137f4af130b531394358a49ee9ae1,0x14b7c810fcd27c78ccc5e47e5eaf7fe6f4008bd654081db716496cc8ea,-0x45dd28965dcc70fa6183fe03aa898b57b9cd7dcfb9219a262949dff07,0xca1140874e02c6e1a9bd7659863e9271566f4011ab5e41fe58035cb0,-0x1f08b6f6888dc8efcb9d25bdea1f6e7e5efb90398be10a5f3d11b052,0x400f9e717f80f4a6752b7a78b7593dc5085946c8f9b05488ef1935c,-0x6d93f5a3a23aacf501735ec496560771e8c2132de026183c40266e,0x98c78109698f495b62e829db21e5471628393dc5d5585f0a51798,-0xaa2ac9affc68ba3cfe60f938fb0dc38b1727df59da3684e5fdaa,0x93b23e7cffe39badf28aff6978b437e89a594cee3ef89f69a84,-0x60d735a1d1289eb77513cb343aa7aed37cb44702f456862176,0x2e1c5631b2457a937996e3b7bd3d22f6640930e9a1f5315a0,-0xf2635c28f20133339be2c8712bfeaa7f20f8a0f0bb8af33,0x3356c294668ca31d62e069893281aced8d0fcbf412adc2,-0x662e9e93305d20ab71f29289f3271e456fb244df98f5,0x687d9bbbe481c25b16de17f0999248a30049767f0c,-0x2caf6e8c44fabcfd4702cddb359fc2fc31d353ed,0x597b132254066555190c7cfeb440c52383f12,-0x17a841469372a9e528d4bc8bdf580318bb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 22
theorem quotient_ok_22 : quotientCheck 24 76 22 num den q22 r22=true := by decide +kernel
theorem quotient_source_22 (size : ℕ) : (coefficientsPoly q22).map (Int.castRingHom ℚ)=polyPart (key size) (X^22) :=
  quotient_from_check (key size) 76 22 num den q22 r22 (num_source size) (den_source size) quotient_ok_22
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_22 : cachedMomentCheck cache 53 indices rho q22 m22 22 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_22 (size : ℕ) : intPolyRF (coefficientsPoly m22)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^22) :=
  moment_from_cached_check cache (key size) 53 indices rho q22 m22 22 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_22 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<13 at hj;omega) moment_ok_22
def q23 : List ℤ := raw_ints% [-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r23 : List ℤ := raw_ints% [0xafbb733326066f94a97068dc023646396c98039e000000,0x10c26d2c7a85631c3d9803a8b64ab089df6aeed29600000,0xc2018f08d60b766173d15b9356ab892beb918f02000000,0x589256976543250d35f8fb6c79a1b86718544b85268000,0x1ca5b38139a6c0552c651f7972db222f567d82024ce000,0x6fc62d56d05b8ffe5d830a88d4f0ded21f1d261e27800,0x155a47ab5a8b698115cead07162a695ea4f9a65893a00,0x3470250819cf3be8fa84e8fdbc0eeac4733329e11c00,0x694848e2e5fe3859b9436dda0096e2fdcc72e22c080,0xaee98931cd82380a020549354f1eab5c44cc323fc0,0xf270a922a26e6de815840660fd1bc23934830d260,0x119cf77de34f81cb757819f0aa5d236f71f719db0,0x1136e5c6394e0612d7a47c1586e72219e375ea58,0xe2675d7eec3c1b6074358da4088462c285e4cc,0x9c311476034adeda7f0fffbae94afb3e982a8,0x5a03c2ad98cd9066bbb2696eb101d38c81a5,0x2b013669cc011b199b7af0f8a6292366ada,0x10d63e5f3b4a2dad1d1008f2586c3b87df,0x54fd4b311e58d3b9855259799d7f8864,0x15143843aebcf36d8214af1b8149f3f,0x3f543ade8c274e5a2c216f22cca32,0x8771046148a706e1a59922ca4d5,0xb7cc5eae835b56b1c9655f530,0x7701ccf39b1a5e73044a8ac]
def m23 : List ℤ := raw_ints% [0x0,0xa9f076ec3686b2e439af4fc81aa5ce0a660b445a05b04e000000000,-0x128d98a07c980e9e625c5219a6cc0deec93b9337bb9da527c148cb000,0xfae33e40834dd2d865de17a21f53d136414c2722cdbdff10cbef3f400,-0x88a82c166ad2144c93a68be76a5a1f1a22d5e45cf3c65ca9f5d2443c00,0x35e9b255ac7b4b593f02ce8af5ba98deed7440addcd272ef56f4ef2b800,-0x1069f0d4452f4bd7d2fbd2997a6c2cfd3606fe39ddb9e5b35cca396e6800,0x4032baec4b0c192cb4addf3af839c6818dd502cb318ae0e8388b8d89ffc0,-0xcf1c5e107ff66d190058671ba1cc7bf0c57d5367bcc6efef412401a10980,0x231dc21f96331b2aa6795e430379f8be48648e5cd89dc107baf5b24889cc0,-0x5143c6c6e164515e7e06861fd4cd337c1f8f86d85f9aeaed0ebcc7da7ca00,0xa22e93b5ffbe4bbe57255795adbad51dd9c02d1843b5d0512d0ca2d9d0700,-0x1197e834cdf86242647c8fe819feafa32135aa6bf5b2cb6d67be930af06d00,0x1abb650cc468b74f2bf6a2e5316db870253d7b7ca51b24e225bb1762a7a900,-0x23bd32f6729462807ffb424cdbfb58b6ee23c915f4d95db8aba895f763aa00,0x2a3506a6ba6b813dc5ed80a4660ea383e9ac4af952e1be31e9298e35e98214,-0x2c29205b7d6ccacd0455f795f1352ce259343ee3fb899cb7c7ebc4ee15bfb8,0x29054550ad305d4f94ff275066202670113328ddc4ca1b3585c51bc26fb29c,-0x21dfdae09a4030de5ffeb90a65032fa7f049ce97f4c36316122a67de53d2b0,0x18e293a0bff609b494d04c38e050610089345833d345988ad4292dea2f3198,-0x104381f3ae614b8c1f48b071c01135e6c58712600d831cdd97bc2ff2bc1560,0x97362e21a98cf2364bb3a3256c1fee4045075728b6fe1fe3a65d7e097b2b8,-0x4e08b1b5f453f31b53bccbae5af5788633dc6523316de83f738eb6cb79d70,0x23b2dfe1ef1988d31e001009fcd641d21612d10efbdd7d873677725edb9f9,-0xe712a3743bc767c69bde76e1ddfbe1b9673998a1106437b143c8e4fa4af6,0x52684e85b3d7a2fc33c678ac5c122d7710e9e872241d015b7600811974bf,-0x19ce78d9987dbc6ec9ef088e4f585a49be501ab1204713b3a9fff5b482b4,0x7100fc63ff2cf78c8aa857fd8e2fe06e12e3848411fe4efb75c719a8377,-0x1adfbe9a8ff38d424a0f1ea4014ccb6e21571824c8d706e8eb65379f4c6,0x58401341a9ed867f1723a190481ddcf4ba3734b6d452e4bd84663d8181,-0xf8132f7d4d3f5f33cdc7240381f84a839a7132e19c7c2f4dbf5510150,0x24f2a644292fc9bee8e6b2405396bb3c61d592eaf31de7ecb1b5fa67e,-0x49c71cd06089453cecd0f970e817e1b8d89d89f8cba586059532c484,0x79bb8dbad73da883e09c9ce7f3deefa2093f2942f4f04487d2bdf62,-0xa3312a92f4227efafe5f366fa4db67d91f08628d01204294f42468,0xae1f6cfae66c06b4656935cd4a8bd42dae238732af4599e5b9b36,-0x90292a3e20fc369586bdead53fe832100e84e2b6dce18e9838bc,0x59b8c92a50111376f6137609863b1c219180a1cdbe7d42db88a,-0x28521b84b8e404e061767dc52dcc42be29864dbb8b266d1f20,0xc6b8d2706d2ed2a8adbe2097f2d10e889a846cd7d654a185,-0x2728d98a5009fbbc31ab29cc7e4e62dca68ee1cd92d114e,0x47dd97aa5669179253fd7a700f828234f7dc6e818a4b3,-0x430e1c59f8bb3d39210e3af30c92006b63ecb757054,0x19d8bb1a2d3083b36f7252d7308b5a2a9b30430eb,-0x2df920fa5888bbb40cf0b2c8b2dba56c9df61e,0xa992f950ddd4b207ac2f6518e4d2dc6a0d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 23
theorem quotient_ok_23 : quotientCheck 24 78 23 num den q23 r23=true := by decide +kernel
theorem quotient_source_23 (size : ℕ) : (coefficientsPoly q23).map (Int.castRingHom ℚ)=polyPart (key size) (X^23) :=
  quotient_from_check (key size) 78 23 num den q23 r23 (num_source size) (den_source size) quotient_ok_23
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_23 : cachedMomentCheck cache 53 indices rho q23 m23 23 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_23 (size : ℕ) : intPolyRF (coefficientsPoly m23)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^23) :=
  moment_from_cached_check cache (key size) 53 indices rho q23 m23 23 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_23 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<14 at hj;omega) moment_ok_23
def q24 : List ℤ := raw_ints% [0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r24 : List ℤ := raw_ints% [-0x229605afd588d64167bb4ead732c39a730e77927c3000000,-0x34bf9e3f2af60c66853d150cedb17161d151540207f00000,-0x2624727b2dabc21e7f01c441a866d95e9210708830b00000,-0x11673b476eae702bee75ebd966c4f578991c32886de24000,-0x5a00fedbde22afaaddd2469683fffb96daec4154a0af000,-0x15eedc28ef003f2c9f3d246b9f1141a56f4ce9328fc9c00,-0x42fd38092557c6613589865c68f5e8594f5bbc914d1500,-0xa46112ce3c391ea584ac56b6d4c46caedaf24c7116f00,-0x149bddd389f31e452a28f8e477a8b2704654759c56140,-0x2234c42d900050c0c29926911f9783d01f4b0bb6a3c0,-0x2f5ce03b285318c345b658c0a08874567ea73ec58b0,-0x36fdf34cf2489862f1a3ceb2bc5d29ca6a6b55cad0,-0x35ae562b8d0ac3cb23c885548ced756a9d6a30c5c,-0x2c10fcdd4c53c3aa3ca4b766197c90b00cd196a8,-0x1e5b1787c76acf28dc13c017ba37762f49cb8fc,-0x11775200ec97cefe31be0770604ed76fcf37c8,-0x85463e827ab2c3fba5a5a4bf578d1bc07aef,-0x341389bd7c72c487b88d2a6e7c1ca1264e6,-0x1064d0ccee39b35d179bc1c865ad1c21c1,-0x40e61105f094f614f8b40efe387f04ac,-0xc2746809513a79ce4e04bef3799fb5,-0x19e9fb8c00c0218a198e1bf60acce,-0x230be1f91be5c9b8e3e69ee72d3,-0x169ac0c7fda6651db20be9520]
def m24 : List ℤ := raw_ints% [0x0,-0x13ea2defae63c8f6bec28b59731f6e2537f552028caaa924000000000,0x2287a7848aedb99a4085bf1ef25612a4e2deb225ee6d77021653eff000,-0x1cf5e30119dd4053524aaf98c756acd9f84f5d9745dfc236fa1a1a2a400,0xfa65eabe7a2c428c67499dc669b3191275394384a557f95bb28baf2c400,-0x61fa0abb85d3f4332be56106bdb78f2e45dd7b15d953b62ecd7082002a00,0x1d9382d830c8a5191b4a486d77c6574c99c67a58fde2dcaefbc7561a2b400,-0x72a99503248bf5a0dd7f0a545b57cfb1c81e6e9dc79c859f844383b820740,0x16e8a836cb77be58598b76f1afb66b610c1d3da79c599af400244510ad0c80,-0x3d8f423af47f96c142389887d036fa9dbffa5eaa7ecb4eddae4166eef17dc0,0x8d0e99d5c6c706cc321d6eebea79e6818df67f6b07aaa29f5f9ca9987bff00,-0x116a0fdbaf97e0e8c49b4fffc7f33e422a79a16fffb3dd87716958f7ad38240,0x1de73defda0c9f20f194185a39ab878c5500cbd7659e8cf9793bcc812a12d80,-0x2cee6b15d7c171d97824e38b7958516d09933b84b4c8f573b90b7bd907aae40,0x3b5fc5881a05fd992b0613678aa5e8ce84fe35d9f1a417062cca22ac4f74300,-0x45454aba8b839b422cbc177be0502251b70341d71cee1cea9b33c5356311a0c,0x478f21ffdb4b8a1baca3b18d962dc05626c03b47cf03ac3c9e8383def0e5e08,-0x4196f1e2a41ef4bf6a0b04e525e030f7572fcb97096f57e788b30413fc32324,0x356914c039b49ddb8e30d91fa393d9d76cff649987b80016dc739f863671610,-0x26aa0761e9b572b670f0d7b55c97bea4ec27d697081112f88e8aaaba03037b8,0x18e1a052e584388461ad004793ee9e5063bf24919fb0e59b9379cadbd638ec0,-0xe398a03e98efc143f5de5c2b9f0faed02b43a67a1491efe323e86032ef5b18,0x73736c7215c5ba8fb31a44da51c01a347bed155a4cea31e56a1aef8f0eda50,-0x33dd63d70938496a7ccfaece9f0fa04ca819592a04c83f820f58e11c76ceef,0x1494fceaae1ac36ea7074000e55261df8adf0a7ed09f8526f9cb4560fa7d3a,-0x73110886de30241df43322656481bcee2d04a43c16035ad69036958fd9879,0x23424be0d304077828983482e42e32cdd62152497b5c790b522848b191dec,-0x96db3c70147a62bc171a29bc4e7fc80480f6830dc91ebd4b54b2097d2d31,0x22ff5d6b669be4ff91c79a4e2f85f985f6a2129aad18b1fd1601a6db070a,-0x6fe9ace86255008c45276ca26263d908da8d036bec9228d9f00e1a1b137,0x131baaeb8442d6d7a95759aa8c652f243028c19978f9a87433820828eb0,-0x2c271bec78792368ac7cc2d91b9e73b8b89b6687fa98152312e23ebab2,0x5545b12f1a0ed058967a0f8848a54ad3d2eb751414c95a0f7ef49459c,-0x87b11402dda1e15d049a6623847345f3ba3931c92b7b04fdfacddc8e,0xaedbcbe3fe91dd63b2bad2f8c97ff011c289bb835ed24e22fcfe418,-0xb2ac231ddbe9e22ce382ad67fd0b7d3c036f97ae006595bb2930ea,0x8d0e7d5e24585671684429cab5cadf116afac3eb2102af643cd84,-0x534c32cb2985df84d675f5336fc5cf4ab47e470defede3ede636,0x2350a11c5e6faee698504ffaf53f10bbf526ff0c1c623115320,-0xa31c74b3b3c0feef8d7841ccb0ba5ac4930fe8e866fde05c3,0x1de3fce2842118041ac68201481f2c982615d2e87d5058a2,-0x328ee77abe491ad6ae3058889cca3b11487b1274b42d65,0x2b078c7e0919f90d70935eaf6fab01c57661a91cb1cc,-0xef237225dfdebaaba6912f561a5bcb073ba1c933d,0x179cae218c5debe1f3c7e8e840095e388e4b932,-0x4bf2976dc68433f4c5457b957e8ed81f1eb]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 24
theorem quotient_ok_24 : quotientCheck 24 80 24 num den q24 r24=true := by decide +kernel
theorem quotient_source_24 (size : ℕ) : (coefficientsPoly q24).map (Int.castRingHom ℚ)=polyPart (key size) (X^24) :=
  quotient_from_check (key size) 80 24 num den q24 r24 (num_source size) (den_source size) quotient_ok_24
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_24 : cachedMomentCheck cache 53 indices rho q24 m24 24 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_24 (size : ℕ) : intPolyRF (coefficientsPoly m24)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^24) :=
  moment_from_cached_check cache (key size) 53 indices rho q24 m24 24 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_24 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<15 at hj;omega) moment_ok_24
def q25 : List ℤ := raw_ints% [-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r25 : List ℤ := raw_ints% [0x691c1830918113b0b9e3c112083329dd0db31fee588000000,0xa03b488786442e55c5366e8ac97819ee91faa14230f800000,0x73cde8a14c58c5d326d01aa986595b9bae11dcf7b25900000,0x34cf2243deb71156834a2767dc3ee58db1b9a52b368f60000,0x110f30d79c0d1fc0ab7688efbda5701b739eace8775244000,0x4278efcd70acbf180eba0bdfb51db36fb111e8a8fda9b000,0xcae210453fd7f7f724ffea32e209f12174a5863ceb95c00,0x1f1770f571122082d9caa39a2151a18e99bab1f1d5c8300,0x3e5189a2b299a6d79743e4a7b459b87a3ce906a8fbff00,0x67580bd05cb14c765f903cf2e14032447afc400bff4c0,0x8ef4e1473129338e6a719c6c54f8dac133d38c304ac0,0xa5cfe25220879fa6dc79521adf39e523aeb9d10d7d0,0xa1ad3f2a583c06dcae31ba29774cfdd80294e01350,0x848e6c9f9c91dc2e9a82faa1f99cd616e8ce4cba4,0x5b30f1fe48dad3305ca23f2914137321aff66218,0x34647bf953e41ca72c494ce4d840c9cc31ce584,0x18f22dc8fd745991e09596512b14341ae16118,0x9baf4769c1fd65e6efa05147ab4e40f20f11,0x30ea1b987c18498dd09ff15ad4e947f9a1a,0xc138a36380840fc06731d74f3e0cd13bf,0x2418e774d254873ab65f6001f9aab534,0x4cc3180d3e334163620313de17c84b,0x6780aed00520485670910745c0f2,0x4288461c006cda69ce609c30ad]
def m25 : List ℤ := raw_ints% [0x0,0x2557162166fb18cea5acc547b7daee85c8ebf9c4c7bffd238000000000,-0x4047050758dfdaba8ba771bef0c3ed6684b4ba9c7799e792977822e3000,0x358224a2f4c92ce1594ac8b9ce2a20abd4037b54ba40411d88ef4f6c9400,-0x1cb135408d56846b85275eea63641c3fd3eb572985939638d1ac8c6675c00,0xb2317cee83e42fa63dd086b13a14c33703d5870762628c7ac786df7a86800,-0x3558702cec3f0fa6dc1b17ae17db8d7c216e335e314160ccd904f3924bc800,0xcd08af157373af2baba88754e4180290a0bcece62343940bdcb721d62639c0,-0x289942ef162f51500b9db1dd7b687047992851d44bd86061f3b38db41a27580,0x6c15224182baf1837ffa96265c930b0b9d56bf46645947a2f674c7ece4f78c0,-0xf544a41ab451d6ecfae8c82b9c842a70ad71157d4aae083b8816e39981bd600,0x1df9b1177cb74aab5e48d8380ec13cad4288befd2369573acafbd52f268f7680,-0x32eef321396d3b32ab4773963a871f3723511c7ea33e95a891e45e92a1620600,0x4bb18e28b76edd3a6955db700ce6b3f55265ba890404e90586bf6be11a5e0980,-0x62e1eec7883053c3fff3fdd63a346c1d073ddca787c5251af2e8bbff62c30c00,0x71fcb3a0196e582a760d4048d93874bca3ea877c1e1cc2e71b1ed3d2b000f5d4,-0x7447f55fa49437206ff4b06bf8cca3a1077382eeec1c0a26f50acfeb86919038,0x692f4175100c04cb8a9dfa4134f7642dbeb8f8323cadb48e20c80e3b65ef215c,-0x5479b3ff54daedcc42dfe2c787cd4058e79c5f410085bfa8731d21cb140736b0,0x3c44bb18357aeb7456d468bf683a828a3ca48ab69b5934ba9c570b5ac4399578,-0x2631b99fa0419f7f0bae07e1437c7c6ddf5aa2240e0b777e55422b30600cd6a0,0x157c4e73686d2d9c7e3909dc0a8049b8fab2a1678baae54aab3c398e56b12fd8,-0xab6d682e90f9da090d5d25d2b102cfaf3a2fd4494cd209f6f602810483184f0,0x4ba1acb0486c2ca00f280f17f559f61474a9a8a8553a1760ae74ab9152ab329,-0x1d7188f3529ba5251928f0fa9b63aecf3bb94f8e240b1f8f3019354bad37596,0xa1499784d29ea2b97c80b2cdef21ec34acae615e630dad28dac720b91cbe8f,-0x305c64cbf4c4f3f98d25125856f00da4d1851855945c9582f05262fd4963f4,0xca2c6d02feaac61227df30a11ada710ed9945d7ae267efbc92ac5f14041a7,-0x2dc0ee1145bb1da8be689dbdc640a02fe11cd0743bf25d9b5d0a19f81ffa6,0x8e76e754b737722358f21a38f21d2a85f07893f40bac085973022aeb74d1,-0x17a32a6c809ee84acafcc0fa91c91671c8711ee3c23d957b03c8e7d7ff50,0x34f45a8aca11a7e552909c31ab770a3a25f5fabdc4459c5da9b044c421e,-0x62e65dadb3dacb98c7417e7c0beaf4138ba91b9b1093759c3ae9c5e644,0x97bed560e8a8e9dff3df2980d2048cab354433ee4baef9d81c25a3842,-0xbbec481ac1f7bc1794ccc79f165a0e454662503a21423c1255b18de8,0xb7d626366943c93705320990392350b9449f76a1eb2a21cdccb0876,-0x8a57e1cdc68f292b57250221bcf2403998a5a9acddb5a1fa7e9abc,0x4d7bf164362111c9479e26b615b574a6b9f11ffaf53b06787034a,-0x1efa3f7df30c4da7f0b34caedf69c83b04203fe0b0f3616f81a0,0x8606503992df927bd67826dec766bc792136db187aabbfc5f5,-0x16d4742eeaa9e38e81decb1a0f0fa857d31058bca8bd1786e,0x2393a125299d052bd56c1b175707b696381f4cac5b24043,-0x1b9c3419ab94945299feeb7e45001d960df285feaeb94,0x8a3f962b32a8feced3572b985a3062fdacb0312b1b,-0xc1f8dc33a74f9bdfdd273bf2990582f056b5efe,0x2201710c34bb0398e4c103c652f5533e155d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 25
theorem quotient_ok_25 : quotientCheck 24 82 25 num den q25 r25=true := by decide +kernel
theorem quotient_source_25 (size : ℕ) : (coefficientsPoly q25).map (Int.castRingHom ℚ)=polyPart (key size) (X^25) :=
  quotient_from_check (key size) 82 25 num den q25 r25 (num_source size) (den_source size) quotient_ok_25
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_25 : cachedMomentCheck cache 53 indices rho q25 m25 25 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_25 (size : ℕ) : intPolyRF (coefficientsPoly m25)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^25) :=
  moment_from_cached_check cache (key size) 53 indices rho q25 m25 25 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_25 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<16 at hj;omega) moment_ok_25
def q26 : List ℤ := raw_ints% [0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r26 : List ℤ := raw_ints% [-0x1355f2b565423031c23070090478b0b3d2a48d49c62f5400000,-0x1d767f100f402f604516ba1b21f8c955818d0458aa7a8640000,-0x15489d2fab7590c414a9a921a39759e85b3735c92c7001c0000,-0x9b3687bf2bd62b433d8469dce79b839a5f80e9c91fd643f000,-0x321cac7845acec44721c6d550c3a9bc0c5ee9972cbeede8400,-0xc325b03f9397d471a7ffc235c1dcc8f435bee12fd136fd900,-0x2533bd00238dad3d9f503a315d07aa7b7065be1e7a8a626c0,-0x5b27cb19443d5bbbfe8b0cff38711de7c1292eafa6796bc0,-0xb692145ae3cc7fd5976b6008177b41b83b1d1dbb99f4030,-0x12e83adbeee229bc7a741d3c238d4b966a4a0996156b870,-0x1a21a4f506c8bb5adac5bc848d5e35fb8014983cf0b404,-0x1e47c4a458c95ee80cb09fe52cbe50838cf39c59c3e54,-0x1d7e9e6ed8d40674e0e74c9e4c8093b9fdb28c932745,-0x1827ac834a74f5bb082fa575a3e5ae1114832c42e70,-0x1098cd2f37b6f018d58f256a04a35cdfec035d797a,-0x985d208331a0611249b2ce2d9cdc1c8b179a422c,-0x48709ffdfe423c109619a60b620483d231b32ff,-0x1c35cfd3b67ba1e8599a3eddc65a88fcfa4278,-0x8d904f212081d71a25b65ee76f883bbdedc7,-0x22e1dd5bac25fd0ca70ec895bd4dd75eec2,-0x680ad95cdeb5ea77b838ae1907e5824ec,-0xdcb8c0854c019b5e21ee41669ccbb0c,-0x128d1d52d330afa9fd9237236bae1b,-0xbe3aac88b9c8279115e879eab1a]
def m26 : List ℤ := raw_ints% [0x0,-0x4603497ea116ce8376a3f1e678ba7f3ad8ba7450f687faa290000000000,0x77acdf3ea79591cdabb2ebecec41f80dae599eb410bf837b76a9bf3b7000,-0x62e6d078e5069dbbbc703304102e2e86cb4a85047628aa1612fdbff4cc400,0x34a24c1961c5f4ebd912489add372183bf156a8c8a8891da76809b9a16a400,-0x1445560bb959c007532c1cf2f4211e005b64833e59634759a48a2688e564a00,0x604f1de87158f885ecc3b2d0a52638006d21ccc11850f8c1dbea28530bfb400,-0x16f0d4cb3a6b17db0c5aadf18c05833394a08a19c02ab510e089f77d135f5540,0x480b5fd9809718bf63af1f0256e781c862f7d32ed65b384b10f806a4f995f080,-0xbe0db9c3a87eb5cee22d9fa56aa8258d2d88663574fa3af8330a4a964136a5c0,0x1ab329dfca5044dd98f8f1cb9e138e36962a6de5111296610e93d9dc309e1fb00,-0x33b1c6787dfbebdc4c73bf972c0611cc4680cd0a0a2d90274e4c2594a192f5cc0,0x56eeea9a20f6384dbaf8303fe041fcb3814aefc8bae9a80fa27f8c6078ce16880,-0x7fcde8d3f30876aa1e999ce8c3455047c654b77caf7f5556e71940774059533c0,0xa51476963c9c17cb66ed57875f3f8c77f7efd5605e785a00fc2d34f78ba58d100,-0xbc0e5ea533225e00dba0aa398dcaf09119fed9bfaf546f207e78796fc41368a4c,0xbd79541b5ee7a0a0cbdb23ee07b4aa913a9bde9d74473c2567d96ef3d0e88b588,-0xa92c86ae314d66cceae2a305ef085089b877afe35d6c388b65e8041bf93ca0764,0x86049f3d149f4975e184aa54598782087eb877c61e6a74ed7fb9b4b5940002c10,-0x5e3eeca07f259a1c5cbe06ff9225a671b24c50f0d4c2342e14778913f9f326058,0x3ad36fb3b788a71b1a693afcb69c6c4eb494b48791d130d6216ba1c59efc8a680,-0x209092e086b80bf1c58bb804f9bc9d151f37eb85dd07e25306a7984d6f5090d78,0xff7383b87f2ebf80bf9df5f8662d003afae2b0a51b1cee72420701d581724ed0,-0x6eb13e37c844e452dcd6a34fb38b21b7ea9b250e8e1da5531b91b539cbde36bf,0x2a4702fa5ed7e67f8fbfffc298ac71fdff25a1c49a31cd133efa85f545f52c9a,-0xe2ee2c9cbda76f61ac413384011e4e375af9bb5edcdb1eb3621d0bbf87a5aa9,0x4295aa319c65abca997ef4ec3af01ec5c496245676a744353282d41f1b64aac,-0x10ffbd709cc0e0f871aecebaed180fb3c6eb29829b4790c344832f1cfa69e81,0x3c0b09b4004a568f91560ca536d819408a589410584d6ad35b832ec288e32a,-0xb6098c2d6ac9066673ceff40f90e3806c9485fb9d3115e4f1e2cdf296ec67,0x1d58f3e776a0c67419bcd3c15f5fc602fcc8d1f28001b3bf07f0aee7368b0,-0x3fbc5abf2078226b0855d66b569d9787d52901ccdc6c9ea217537af40112,0x7317a517af78a3c684dd0beed375195607b35581e06f54a2dca9ed1f7dc,-0xaa3c20d2ea4bb6ab7279967f47453068f296107aae02e9f868e037c2ae,0xca8c976e711b33303face65bd483c2003a2f5fbfa3175c2a63f145098,-0xbda3d791f93b2ae71c602cd435991944a605fa1ef195bbda2a0c4f2a,0x87fc4c2462a1bcac43283fd082b1aaa6ea661bc99200ce351f21284,-0x48358218d39d3204a5dc61c82e876a2006143f524c01b924736ff6,0x1b361736b11d74169f6868a8670410d9d46e570422f395017aca0,-0x6e3ba020dfc3473a369bb45206bf33ec641f97bb8d645586253,0x1172657c8d4f3bbc61e3f7bbf9e47fe809fd1d9598dc6cab82,-0x190a0f4b858c2b28003e8fa43bd3d82207dcb9d3bb325fd5,0x11b6eedbe2140611eb7bf0aa4c2e2d0274523fcdb6908c,-0x4fe6ba6fe18e23079a859af19e3a8b5d49a728e178d,0x638f5ac8897cc15b94364a63842574d85e1d3552,-0xf38d62cb1cb0a8ba371a704badf5f7cbee1b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 26
theorem quotient_ok_26 : quotientCheck 24 84 26 num den q26 r26=true := by decide +kernel
theorem quotient_source_26 (size : ℕ) : (coefficientsPoly q26).map (Int.castRingHom ℚ)=polyPart (key size) (X^26) :=
  quotient_from_check (key size) 84 26 num den q26 r26 (num_source size) (den_source size) quotient_ok_26
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_26 : cachedMomentCheck cache 53 indices rho q26 m26 26 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_26 (size : ℕ) : intPolyRF (coefficientsPoly m26)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^26) :=
  moment_from_cached_check cache (key size) 53 indices rho q26 m26 26 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_26 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<17 at hj;omega) moment_ok_26
def q27 : List ℤ := raw_ints% [-0xbe3aac88b9c8279115e879eab1a,0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r27 : List ℤ := raw_ints% [0x3748e3fa91700bf006f929ef484200c3dc8bec57b47fda800000,0x5434a978b14481a316e6a90c263755619f62d7d3bb3a56880000,0x3ccd677503375c8fe285cbe99584b483b34df2542a198bd40000,0x1bb3212007e6410fce1950fa801673ed8612099c11c257ffe000,0x8f0433c0dba406b05000e3b8f22c4bb9906865fc5cf34681800,0x22ca1028eead58ab570868bca6341e4cafab1c287fb79046e00,0x6a0cd76652733a09233df32820a9e40eaeec31dc1eb86ee480,0x103af49e285fafd87e25ff92be830d9b1822d602455e9b38c0,0x207bf58ca97be95ee7fcdea24a6ab8cbfeaf936aab8e3fea0,0x35c8f38ee388e60b5a1127608627b8d7dacfdb2c853d42b0,0x4a467eb7cd113c40ce7b9c6b43f70a7bf3dd5af579ecc18,0x55fe124d1a738646413521424d582bc9357b49083d4d24,0x53ae656b40d5c3f96650fbc4c39085e64eefcb7231796,0x4475ff820cf745679d90f1b369ae567e39e3353cac3b,0x2efc9467477eb97142d63e7bf3b20d351db1b85624c,0x1aed27d6d1064836f7e13991f70c869b941cc0a20e,0xcc8ea21b42118279c9c0e4707bfed53051aa091a,0x4f8b56d4ea28c98e33923591c8071752aa14021,0x18e87802bc9877e074fe1744d6958a5c9f1938,0x62072a8df82e2bc956f497972aef24d728f1,0x123d1cdc099eecac7433f81054bca8cfad4,0x269c23fda0054d2e0d225975c6624eb94,0x33cc51b23b146fc0a9125f716956e40,0x211bee0fef2c29ffc8dbc13c512fd]
def m27 : List ℤ := raw_ints% [0x0,0x834629cd6e0ac3367e736590225dae8e565d9a17ce3ef5f0ce0000000000,-0xdedc1c2011eec8507288b96ac0f969e80bec47083f4d2bdb16cfaa9bbb000,0xb6df4b320a206c984fe08541bc75121e7dfee863b8af5be706aa6bebb23400,-0x609b9ca9a039f325e82920d597361ddbb6ec157135610ade239d1eaded17c00,0x24ec4fd81ed0c57f83376035a389ba197ab279a08ef0a68dad7afd96a6ca1800,-0xae09b7bd031b0a5222f1621fd1f86e5210788220a5185b8089ee5d5898832800,0x291d6163c5bf6226691d490a7aa5162d232248d58fa4c559fc98b4dc844cbe3c0,-0x8003a438be786653d6ea1d8922ab301f115fe188fb85cf9b701ec808b53bf8180,0x14eb154b14c10491a95597c26a6179a33dc774443e0d6874d94e9ee1c4e048b4c0,-0x2e9534733e0d0211d464c303055e6f4d69b6cb4f552e06c2d0e4559fcf137e8200,0x5950fc42e1aa9c7cfed781b3b902b31d9429ccce32623cc38a6ca23b20dc605200,-0x94ae42dd345e5cbac4f4d7b583ea7878c9be8d0d18c7667edf4ff5f4e017714700,0xd844c3b985d3aae32710e6dab0fc9649fff86d4d98ae9a1a6a40546ddce6547e00,-0x1144063150876f592bd008d0c1d79b7e51d995cf9f0d9541a51f49fa6a877d87e00,0x1370c46db05d7bbf7eb3fe6098850d2d32f4f52c6899a27a4a8e8de5138969be194,-0x1359395fe3ed583bc902e3d40e08bedfbae59120bec1472c5bd6a408d03e612a0b8,0x110df67e595cf7e6bdda56a6a65bd0fce3ba1e37ecab54389f1ddbdccb5e0ac5c1c,-0xd54214977f3132609530781931ba4299935a744e8c2aa7f665a87ad9567fa5e2b0,0x93d803fda463dabeab8af8dad2e4523bcaddbe263bdfe873034d2c44ca2ceba058,-0x5ae6733e8ae03b1e0bda298dea5cc6ed7355e8c398f4f51e7c862a58667b58a9e0,0x318664c27c996dc1d4715df9173e7b2131320ad52dd68df31c1fdcfee2d41eb5f8,-0x17dfe81c5172254a69c721b57cb8e4b555ed871eea624bb86c90ff0264b27be070,0xa296d35239f3ca84250cc16c2c755cc39828ffaaf18c04ea91c1eb3e9d6213a59,-0x3ced92dcc0b8c97259231d3bd4bda217837f139b3d032d42980df2c3701462036,0x1407a24e5e06492e474d9e9dd0b93024af0d902aa8145a67d10c4cacbdda6765f,-0x5c04eaac5a41836537733f24a90631ea792a00ab6736b4c8eb287e486d9a7934,0x16f45b994699a039472c135f5610e2719f88019d2cfac3db2b18a4dca548f0d7,-0x4f16d1ae723f3f4fb4aab52f394692f8e541f2a24f0f24aacf96312dad2cc86,0xe974d35a7100b056eaad37bb99a6d84491f2ba34ec5bbe27d23c4ac81e0f21,-0x249140f93d40f6fd599b56fcea9db06c355fea01fe12e80d490b8ffbaf1550,0x4cfa00e8db85fd94d372b9fa655b8fb7da821994863344b526072c0a079be,-0x865fef749c2bdc66bb8a9e726fbf96e5a29025d41ae06fdad439acd0d804,0xbf8fa89f5e2e0aa1ab1b2113465ab2afb64b34c35933f7962726f0df122,-0xdaec731d86950f476e996b8713213c8d1ca297a40422be7706e026e768,0xc41cc18a93887bd1e398c3a8acc1ded006619c5ff95ba473202353eb6,-0x85f3ccf5bd264fa205c613891f69a88531a94baa69ee6a3fc177d2bc,0x4368e9d2d44d2f781c10e0e9832e57d46f0ee07bd6939444e1f050a,-0x17ef3afb6d2870910d6bd0d52341330c93ae42316abb4ec64d8820,0x5abefe1389f66b5be8232bd0a82649f68d80e1098616896a7865,-0xd56f82bb47b8c0cae817d13dd171a69bc0d6d8f64026ef2f8e,0x11a0277b7f51570ee30d6d1928f3a3b71449f2b99457cc1d3,-0xb5d437df82c5c9084fbecbe74f24ed4a59d36c7b3a1ad4,0x2e2ab04bd090580f6887bfd9ca9a2eb6c30a8abfb84b,-0x3315bbb6e3c262c2d15ac7457d5f8c69c0631f5de,0x6cfe5bee862cce04a6f5794a86b64c02f65ad]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 27
theorem quotient_ok_27 : quotientCheck 24 86 27 num den q27 r27=true := by decide +kernel
theorem quotient_source_27 (size : ℕ) : (coefficientsPoly q27).map (Int.castRingHom ℚ)=polyPart (key size) (X^27) :=
  quotient_from_check (key size) 86 27 num den q27 r27 (num_source size) (den_source size) quotient_ok_27
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_27 : cachedMomentCheck cache 53 indices rho q27 m27 27 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_27 (size : ℕ) : intPolyRF (coefficientsPoly m27)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^27) :=
  moment_from_cached_check cache (key size) 53 indices rho q27 m27 27 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_27 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<18 at hj;omega) moment_ok_27
def q28 : List ℤ := raw_ints% [0x211bee0fef2c29ffc8dbc13c512fd,-0xbe3aac88b9c8279115e879eab1a,0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r28 : List ℤ := raw_ints% [-0x99f49fccd69903f499867a0c10ed85605f74ade1ed39f29400000,-0xea677109ccddc7f5907e636a9a8aeb3f9c4277162788102240000,-0xa92fa04e7e8b010db5ea43b4dfa984a9ec97b7b6be7900cd40000,-0x4d0ab075f5bb659fa341bb8745b2415d032a0fdfb9f0050e6f000,-0x18d955f45958e065799ba7312219b57497b83d7ad9082f872e400,-0x60a9ef8b587b02f71f2181fac55afdef460699f98c4a91971100,-0x126806d6af36712077d33353128bd8b3b5a7e01dbecf001df4c0,-0x2d0b6888319ae3d704568f443939cafe8a814c9b4ee3a92ff40,-0x5a18af13b22203c1dbc530f10479e700dcd704ca3bbfec4570,-0x95122c118058f42f0be859b1a14707eae4941d0c696d117d0,-0xcdb51abb733e1587497b4cd4ba5c68232fb649ad22b0a854,-0xedf6e99843b84d8fc76bcfca9fbd40a5842944b3b8cbc3c,-0xe75d6de938c4e14c0670743d976ca522d34bdb866cb6c1,-0xbd1a5ad4b8a4a6f2a1ccf69bad8cb6021be35adc6e62a,-0x81a70a90a1d22a6cbcadfce50d037bcded7af2cccfc3,-0x4a374546854817c131aa48c788764bc30f0b65f7c38,-0x2331f5bb76abe325744b16dfa33a855c533a03af25,-0xdaaf50df83ad806df1076e3b56835e0bdd896b76,-0x4460d222dcee6716270401e6cbbd7ad09142e37,-0x10cae08c800a31aff1989c81a91dc9bc513764,-0x31e6ef294fb6701f766cfd622d23ede626ea,-0x696f63362d6a46946f24d118fd00f2d96c,-0x8d25d17d7bf59a4cfdee7e7e0744e232,-0x5a01f3167bc2916f74ac3b3337808c]
def m28 : List ℤ := raw_ints% [0x0,-0xf6238e612e542e062d185e6e406fa74ae1ef80eca2b60d238240000000000,0x19f162907549a3527b0d61df27caf85892d72b4967881b8e24ed8e53a42f000,-0x15242c5fc3b9b91fae976c0c471f32777c6c4a22baddc0b5ce40a139b32fe400,0xb16b1430c363f856da0b2bfa938a8ad2682073450691ca183ec0d68472938400,-0x434df320f02b13da60528c4156073625d2df3306cb64aca41026bdd092248ea00,0x13aca315798aeb971260cc945671e8e315dafe3677b5026b4f7ec7c7550f61b400,-0x49c499ac435e77e090284ff5cefa47272385ee00066503ed617baa1cbb777cf340,0xe3c247034dcc0b665931f7d6dfdebbfe45a259c22b32f76f7d90c2d41717deb480,-0x24e4687b6dd9dedb3a28e3c99aca6fa24577f21f5a6539f1965b086cb1fccd10dc0,0x51681801beefb3420e0b2d36e8e4430749abac5369b7355b507e452b181a5219700,-0x9a99e26fa0c165152def1743cc6b96c3b023fb9f7bdd0b51b7225b6161056eb3b40,0xfecc04501b9fc2404041dabf842252ab979fa9c95c1a5676e13e7a5fc59dae15b80,-0x16ec3c25c2bf44fad0053195daadfe1c9bc72a1ae807563c73a95803d08c7202f540,0x1cf608de138e458a059ae29de0ac0a0723de65bf770b6f2b1cf033a95fb0ef0bcf00,-0x203c5ca95b4b027d15775fe4948c845177a0402f2f3319072ee1f1e4a81832aeb28c,0x1fb297963eb809e3d6bd82cb44a111532592935c5a8225be5c26df58aa15dcca6d08,-0x1b9616d21bc0888bb7c1e91921afe56158e99a78c9756ff8725460a4142bb69a67a4,0x1545bf3c969056ca378bf8ddcf4fb6e944145f3dccc92475114c0b263e49dd018a10,-0xe8a50b6e8934be02ac8261d861d97e372769acb780362a2801e8db771f65ee34df8,0x8ceada935c678c160ef5312fb961602dd67559d3ea133b33a6540a126211b626440,-0x4b92242d409832c61aac92840846ca13a8a5eef8ca80b32e7bf43ee43d260f63ad8,0x23d321520a96c66fbfb4d5d4753b6b7378eaa405ee461e3650ade0ecaa37f19ef50,-0xefa99cd43890fc61538506a32b7562ce760078011d80228210caeb66a574790c8f,0x581f89025fc01fe7a178edbfb3a740dffae9055836792a228101afcfd2b46063fa,-0x1c63dbd6a48512fb40b0c6027a07ddc6098fabccfb51de8749020ef07885ed1ad9,0x7fa341406bd4d989e4494167dfe707dfeb65eb7f53e22c9c7921274e82d68836c,-0x1f1c555507aec23645a34293e155fcf57f4cab2a62bc507aef25820a06c8dced1,0x688ea135329f82319a0a71cde5abf3b296b88cb8559723aac2e8b2ab5211dd4a,-0x12c797ddab13ecb5df87dca991e0fc0435e7fba14dd8e78f7b3c561d70785097,0x2db904ee4351fc0bca04edad010f6750c6cf0942214b06d082e895ad6f02ab0,-0x5d47c18738cf6d02a40594974f935072cb35b62b84451a92f2f5eaf26c5372,0x9d62f62b6ea2dc4ad0a0ad38b011d0fcfc8d77335958b09c941abc3bb4a1c,-0xd83257999b04000d9f38b6fecab09b2590fb03012381802b422e1d9ae8ce,0xed421a75325d9d59d71c057b4f027729ea6b8a365000bca93f65e821d18,-0xcb499ca3061214559bea32c3c8eb9536ee5195e5e693e33452cd7a306a,0x8437696853ecb4ee0287c7c7dca16a2e07669a00513bb1e4f88203984,-0x3f0852cbd7cc0f2176bf83a3e8b9ef91d48df9ec444a615c61c4e6b6,0x151401e0eb3b56e4358c7317945f8f0884af0cf5221a6d05eccc220,-0x4ac3f34dc584b6b154fc27bfc5aa54daac06d2b2c7d7babff5ce3,0xa3434513b356ed207af3faa0f632e0f7477baf84b7575de1662,-0xc688ac93fb9fc2c924a489597b64fbf0b112034bc4144f845,0x74a1d2d7996b75d79bdd65888bef1d535fc289683eedb4c,-0x1aaaf0846d1c730b87a07f683fc5fc8bbd847cd9930dd,0x1a342f656d69632aba491fe9305c4c598eba2fd372,-0x30c39765c947ef5507fc9cc51511b901f83d4b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 28
theorem quotient_ok_28 : quotientCheck 24 88 28 num den q28 r28=true := by decide +kernel
theorem quotient_source_28 (size : ℕ) : (coefficientsPoly q28).map (Int.castRingHom ℚ)=polyPart (key size) (X^28) :=
  quotient_from_check (key size) 88 28 num den q28 r28 (num_source size) (den_source size) quotient_ok_28
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_28 : cachedMomentCheck cache 53 indices rho q28 m28 28 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_28 (size : ℕ) : intPolyRF (coefficientsPoly m28)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^28) :=
  moment_from_cached_check cache (key size) 53 indices rho q28 m28 28 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_28 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<19 at hj;omega) moment_ok_28
def q29 : List ℤ := raw_ints% [-0x5a01f3167bc2916f74ac3b3337808c,0x211bee0fef2c29ffc8dbc13c512fd,-0xbe3aac88b9c8279115e879eab1a,0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r29 : List ℤ := raw_ints% [0x1a287d79d50550d7256328de9458f2e4477ab4ef981a2e77b000000,0x27d009183606044afc93ea499e39b18046532780731ee230e300000,0x1cb97823369c6d0d53ef1c5ec57626922f56f656d5ec7afc66c0000,0xd132241659ab7c14f4f2b02bea88202e4ec0cbd1adc1c4e1584000,0x43718ed8f1fd89fc295e10ddda5e50f11714a9855d8440bec80000,0x1063b8f5ccda7be2453d3229363f9483653ca38fe5929ff4faf800,0x31e84d80e9f7eb42ed70e17bdf54f1a166993d18b124291094400,0x7a1112e8ba09d51133cd7b903e778f3726f061217211e7aadc40,0xf4019ca8503092e85c31078f313535708a10b3c2dd2b13d4000,0x19376d9e46e527c50b9fd8182c85ae835ff04fdd3f7388338d0,0x22c5cfc3561c099c9c08f4488c4b1874d0c79395174c4e5620,0x2831f20bf82d44ea48e14de56f2123f0d0f9b21ca134cd85c,0x270c6d451faa83f6e5c947e8e6c89a4b083842654b97e4b0,0x1fe3402326acd0ae626e3a74a92c28bb0223eec5b24b23f,0x15d78b7ff4cc4fd88b3f0c0b3e725405c9208c8d595cde,0xc7d6a9161c8f77ecbeeb615784eb7e1a9b2e3735902d,0x5ea999b52b31f35089e6d30487199bae18441c8aa7c,0x24b77b12717d823ea92e3f562b4884164f7812269b,0xb771e0424bfce137cec015e7e98a6bee9fa3172a,0x2cfc46a20e7e7727cc447a02dcbf1a8a3630559,0x85786ec4ad56f44917aa8f877d5add01538b0,0x1198279a6443b992cb63db79ace2c4762816,0x178233c66235bfc0da62035e2c5c06b67c,0xef5901d82afd9f0506c382eccfe109e]
def m29 : List ℤ := raw_ints% [0x0,0x1cd82aaf636ddd64b948db10eb8d159ac67a111bbb11558a294380000000000,-0x30541afb60b072740f6d8e84d5ff79e7f3f120084d53e16b7f33a0f799953000,0x271e900978a6e5504d6bd1eca3b3b79cf8b92a47e20a5c5f3683dfd894c6cd400,-0x146004e44e24c225b9c3be310f76054b4fcff2704050c62867380233798d8a9c00,0x7ac5f1e8413969f388b3358e552a0897b8f1f0feb58c109a0c1d8f3e775bd3c800,-0x239e367322bdab141ff5d4ed60add8a4b41d42fc1befd6f4418ee1c747fea0c8800,0x847f7301c288faf84d95c87d06017d487c41ffdc48b6089c191d9fa6d3276857dc0,-0x195bc029ed01954c5728a27c6d465fa18d2fecedf5eaae9a568e85879acf921f2d80,0x41288f44f38bdaef822006a5c20633798e256048f95664f9f53df74f9274dc3a50c0,-0x8e7e9a7f47ea67ea8112a4e8cfc7c2bedbe0e43bfbf4952bd8f69f8c372fd584ce00,0x10c163cf17d257a266d45a1dfe7a838763f1776139aaafd7955a340852c8b1da73980,-0x1b5833c0cb49942b60cba4e5b7143928cb0253829131e4d42b496723e06e5b070f000,0x26f52768c26d34677fa02e466d194952a3a4e2b52d062f98772cd0ff8a5547bd56680,-0x30b0e1da34d25013bcec89a0b1d9e60800493180ab313fe0c2366aa3d7baba2fd8000,0x3595c4877a01616e6c855affe84d49e886aaf910e6e383e1270451a2da48bbc216554,-0x3410b469d32545cb1badcd1acd90278b7dfd71247906b4ec1f213fe32e5fe6df43138,0x2cbefb53014b46b87108a3bb9af22d67b5ce42ab8b8d708d5d88bd90e1fcea86a62dc,-0x220cd9f391bddbe68503c5b1de05119e4e26eca2555ae4d0796492ee8fae655d696b0,0x16f3532adb06f19b3f659ee7acfaeceea098168b72db709cc47f93a1df449656b1a38,-0xdb271fc55f2abf008fad1c32af47be024ae8f6dc637e950e5ba6ec39efbc445fff20,0x73b2043c9bca7baec2964eb296cb605d7a1135b1717f567714521147758088a9fd18,-0x35f0668da3970b2d69234908944f4531f52c064de969c0b7088457354a19677e0ff0,0x162809f68385551831ec2df4ca88ff233abec8770e9e6f7f70be4076f3446741b789,-0x7fe8c697fed3ccabfd029aaab8cf3cb1474da936f68209af7cfc73eeee49b8ddad6,0x28626b7fd6a5d0cc28e0f5dde8252c48d263919f627c7465e06fee7caf052fbd42f,-0xb1aefd1f9cd9c4cc83aaf06c7106dd01ba8fbbdc161f3abe56a55a9bd7e70b0274,0x2a513107bbac974b58ab3719ce117424ad89f1b1990f767d671e75b5ffe8c87107,-0x8ab88c770b99fc4c1a66a5ac8323750fc4664328aaf0792793321f26dd39a5b66,0x1841707a7e10718eb14a7bf6722613b573c06023a427f3c0b2f63b6dc4876f071,-0x395d7fdc43336f2c659bd7633e02d6fc4cb85d174e7f5799ceadfac604100350,0x71681c5cd61761b343a00b67aa7709cdd895afe1543380482580a7da6593d5e,-0xb8e87770a48825e2e2d8fbe23eb58a71a93469b25ba645b3e8ab75ceaa79c4,0xf4b2b121c0305fb445073f1e7eefd3d1272987dcc4ac8745ec2a6442b7a02,-0x101cb346641246cd824fb2c4f06cd030ba4f1594707005dcba8a667fef0e8,0xd33457a9e57c8247a2087fbd7397f68e3c2b263d06062f9e2a2921645f6,-0x82c0f9d1bea618d562b258d747189ff85c33add5e209ecf88408f1d0bc,0x3b07ba75b051b4b32828c938ec8968f3c94caa141d0d283af457535ca,-0x129579ae6cbeaf8268de4991b460e5c108b814424e58cb11c79792a0,0x3da52982d94f76d88ccdff7d561ae64c656dd4b4e953aaafdc40d5,-0x7ceeaba2e1e87ff24fd74c34fce998b40d41da2647fdf96d86ae,0x8bc736c660ebec2b8520d30f8ef4b593964e93aaa747630163,-0x4acd27a965b7d50ea99bda5e601f3efeb8e8d8ed2c763e14,0xf666d598ba48b14b8846c3ff50df3fe0a95673754087b,-0xd6fe4ed9c5d308d03f5624fdddc298db03d05e9abe,0x15cfcee18359baf40699dfe436adde1d061aafd]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 29
theorem quotient_ok_29 : quotientCheck 24 90 29 num den q29 r29=true := by decide +kernel
theorem quotient_source_29 (size : ℕ) : (coefficientsPoly q29).map (Int.castRingHom ℚ)=polyPart (key size) (X^29) :=
  quotient_from_check (key size) 90 29 num den q29 r29 (num_source size) (den_source size) quotient_ok_29
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_29 : cachedMomentCheck cache 53 indices rho q29 m29 29 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_29 (size : ℕ) : intPolyRF (coefficientsPoly m29)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^29) :=
  moment_from_cached_check cache (key size) 53 indices rho q29 m29 29 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_29 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<20 at hj;omega) moment_ok_29
def q30 : List ℤ := raw_ints% [0xef5901d82afd9f0506c382eccfe109e,-0x5a01f3167bc2916f74ac3b3337808c,0x211bee0fef2c29ffc8dbc13c512fd,-0xbe3aac88b9c8279115e879eab1a,0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r30 : List ℤ := raw_ints% [-0x458f43b10f561f83f10254641133f2c5772a8c88bea712d103800000,-0x69d576b7309d81413801b621afb1ff35adda8170345dec6e78980000,-0x4c549f721e1bf8a25e9fc454a3d13d2b2d103c480d70de367e380000,-0x22bafbd8cbaabe363492aa0d90f7bf6680437196f22e89914ebea000,-0xb3133b86292494882f9b4a666180a8dc56784ff44353a8735ce1800,-0x2b7f649a886819deeb054f979899c37f4c6a90f8ee31ebd40e4e600,-0x8463b4c38729355175562a21c4dc6ef7bce507d19fc5f8d42a8c80,-0x143a33ac0616efaff5ff569d9bf3a7c4da87563a58ae7ccab1b680,-0x28693562904b88f0dc3d71f4970757a2c7c43ac410601a0344de0,-0x42c779832e64582b22a6ebd9e5e7527f9029464402b7aa8a17a0,-0x5c06c04777ebe0a49e4e7524b749bced786fef6ef65ff0d5b08,-0x6a4d66cafe8dbb1c839d7f1f4701b21cb20bf9dea61935c098,-0x673130686c57d57947ee32e81b73f01416d3a86b37782c332,-0x5433253be2da72e8280cb5871e038872f53dddd9b1bf11d0,-0x399f884d9b45483e867634d4758645a96812ad9e49f54d5,-0x20eb57a253d3aeca0b872fa3b187325fc8425a388373fa,-0xf93deaff01e6a5e02772913568e0dcea9f3e0beb8d55,-0x6090ab111f9e0c4e818edff4f2fb448f5861ed00fe4,-0x1e1df83a41b597639003543e01f7dfa927991835f5,-0x7602d77ddeae4a0bc12048216193769c6be5d0be,-0x15da0d1afd26fcbb8f3a7cb177142034f49f999,-0x2e040304a67420cabc0625026acf6f37a9cd0,-0x3d606b0c27aae8687f28d2aeeec9bdc112e,-0x26fb22ccc733e3bf119ae12ff2c9e1b8c]
def m30 : List ℤ := raw_ints% [0x0,-0x36155008da6dff1cdb689abfb9a888823424e013fec080630d5e900000000000,0x5a0bce8805f26501aab482ed73e2498a5081e903274cc197538f0fe0c65e67000,-0x486941d7636b7280046b538dfcacc33c8e314b9e0949a847be16a5848da8540400,0x25755ff9adcda681891977ff33c6ac2f1daf9e247cc41bfcf410cdcf7bc85216400,-0xe01d6e256c969f60fc1695d4477387e3c173e8bf71aad11b1385be652ac39500a00,0x408a0b13eddf238f9e42be0e820f0e63b65aa3583c3bebed242b609bed38b8a8b400,-0xee3d15a1f3b701a3319273d6c03d6d2d4ab24d91b1548297d888507abd6418226140,0x2d3ae9fbb3940122d2a181ccf4c92f723cc1bcf65bd36e7412d82c01db0e513f45880,-0x733ec5906943ec783b5be54414bfc413412b8724a8a840c333f312b2a2c0475dbb5c0,0xf9d23e64edd55b30fe6baf6052227728820454d453ed6c61cb4fd96f01cf967a7d300,-0x1d1b350250504b917d570be14ec56d7d73ae638daf2946766a62964006e5384a3ffdc0,0x2f0b6aba112c50dd2fa60bdaca1e13e465d30090d27d52f97e6fe2c7bf62b09b974680,-0x425950a42a6c6845615c47462db02e27ff0a9d389dbdeec8dfaa712a847652c8bb12c0,0x520c5d354cc414319f661efec161c437cee7ebe326aa21d9118d5d46c85603606ebd00,-0x594a6bb263a9c3bafe304ddf1013444824f57b116e7576c5afbb5a9e6b39aa9f55f2cc,0x55bdfd06308f24416c8e552398b2cd31eba428ea5290cabac1620442306ef1d56d4488,-0x48c765b6ae462d954d39046690f32579bd27f9d89baf14113537d1b79da420ec4783e4,0x36a9129d49da414a0a2d3428b174c7f89e049e7daba7794693063c24ba19d0d3f8f010,-0x2455a3a50cbbd4c04da7ec6a2e976e5f2cd17912890450a608ff876a342a099484d898,0x155e4e0634e01dd22db45cb424749154fdd7fd174db622c8d5acb69ed96ea637939800,-0xb1b335ed7ed1a8b6039a36ec80c2adba5f5cb4690bb542c86b09d3f64e2b6858e0b38,0x517c1141dab82e1c3ba415070ceed6a51b95e1958cbc7ea55d5329856244d71965bd0,-0x20e2b3453963c814a8ec3b1fbbb9940e04a4a9d5478654003172aae18057d90ff485f,0xba4e717f1f8a7ef722ac50d051cb210d6ffdda0b62c8df31ebbe35afcaafa918d35a,-0x39a6371ab5cda140a63689caf01042b1032088e640b0b7a5af05bcc459ad218b8109,0xf83b0839143ce9c6d2f97375174b143e058d5f876cb29703ee56186270f6e83882c,-0x39c3ab383f110e158dc7eb1cc3131d0003d2fbb5982df4474bb4a7868053b721e21,0xb8b159c2fa43278d726bbedc401166ce48fb9b222417445a55aacb02980a18756a,-0x1f6f991eba76ddf74076845ad3f9e0303c5fa2d01536fc63d1458dbe82d59bfdc7,0x48363963af6db5eeb7e50e4e916ca4a12d1d95918d716b67dd9cd9e5a848914b0,-0x8a5074d3c61f03458a9777d1477b49c56f1f960dfde1c13470eff7539b8101d2,0xd9e4808205843bdfce42a3ef8f12481139261c4459495c3276664455c7ddc5c,-0x115b8d70af29ce8a9bcde52c418d94afbd68b163adb7ce1d5a5a72e0d5cdeee,0x118cdd19fb3ebe6f93c196481ac415ebbf3b371d2430bef4a0dd0c585b0998,-0xdbe822babd211ecb82b8d29799afef2560a010579935420e6ed3a362ecaa,0x818b0d5819955f3fa013aee6d69a0f68fa6f753606635cc57f524ee9284,-0x375cacd0c4c41d520a25456ed7ca50fe064a753f3e3c9aeebf68ef3276,0x1066f2faf913900bb8a4c019fd935998b2e1c4d56e9978db7f28a33a0,-0x32dca7c91a3ac0e1bad99e5a2a02579545012f1110128d9824d4d73,0x5fa20dc8af958f75630572b9660e5acefd8d17046a3a7d1b48942,-0x626a71fc3e8491dc7eb65aa5557ebe0d1efcf65d2f3d586feb5,0x2ff73fe6c0be98fb0d2cc8c038dc9a3ec39c5798e0bfc520c,-0x8e40d48556b49bfd3553b02693df99c1cc0302ca7c2f2d,0x6e36afb15fbdc018b0edd45ce1ba704a5677b3cb392,-0x9c0fc6b532dd772f8cf162e8a52ea4775f90f7b]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 30
theorem quotient_ok_30 : quotientCheck 24 92 30 num den q30 r30=true := by decide +kernel
theorem quotient_source_30 (size : ℕ) : (coefficientsPoly q30).map (Int.castRingHom ℚ)=polyPart (key size) (X^30) :=
  quotient_from_check (key size) 92 30 num den q30 r30 (num_source size) (den_source size) quotient_ok_30
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_30 : cachedMomentCheck cache 53 indices rho q30 m30 30 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_30 (size : ℕ) : intPolyRF (coefficientsPoly m30)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^30) :=
  moment_from_cached_check cache (key size) 53 indices rho q30 m30 30 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_30 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<21 at hj;omega) moment_ok_30
def q31 : List ℤ := raw_ints% [-0x26fb22ccc733e3bf119ae12ff2c9e1b8c,0xef5901d82afd9f0506c382eccfe109e,-0x5a01f3167bc2916f74ac3b3337808c,0x211bee0fef2c29ffc8dbc13c512fd,-0xbe3aac88b9c8279115e879eab1a,0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r31 : List ℤ := raw_ints% [0xb54273cd2f6637425a6f018c3f2d6b6152a06d9f83769b9d43b000000,0x113b23cd9b6995b44d15a69be45ed4c14761158dee96dada1d6ff00000,0xc6c5d590ecc8797f47c1c409e18eff2f8c319a63e93e2635613f80000,0x5a6896e6099553ea32199485ad6d936f0f51c671bc950d0f165844000,0x1d1fa0dc4b6b156e1c95ce86f4759566f5262b24b82665c1d960c5000,0x712382c85863b0759469af29bcee89bd6fe6326595d999ce7aaec400,0x158316ee5cda20daf34f5a2cfd86e4c90c3835812c19d389f6e2af00,0x34900092256fa37c8dd6921ef21c63e7c94e9c009008d815cbc8480,0x68f4d71141ec46ff5754ad72e4132ee41d707e7f7d04c5f596d8c0,0xad57d186987779a0c9ccc62c297b50bceb6e3454414d53a394060,0xeebbf344158e37fe74b36ff41685da6bee01b5ee6c9bd5103250,0x11396d8394f7099b9fe5dacc8a6b4ee048935d9f1ad55b3b31a8,0x10b56a1f00142a87e17b0f11e2b3070dc8a0dc8587cb6e95354,0xd9f8661dffa38f39019dacf8793b24364c26ad9339d42e5ce,0x950c8f5140203ffb3145dbdea4b93bfb6644b53c36664338,0x55131b44a347ad2b766ac4567f6d73d27158282118e671b,0x283830bf1dc8b17d6b8c508d843ae9543786d076a067ba,0xf90fe47d25b284ad50e32d2acdcccc37463c41c9386b,0x4d9768c3cb3e6a492d9c2b23051667bf96395cf5abc,0x12faa6107260c7f4d6470c1860ba9a4a565afb819b,0x3827852fb473f3c172750d2a2f27f4a8d7b46c56,0x76145df6d59ad757caff55d0effa242e7c1567,0x9d3f71ff253e75376f459e343e36353ffd18,0x63b254f01d31696e35fcbe03a4c65bb5a2]
def m31 : List ℤ := raw_ints% [0x0,0x6567f610998e3e561b6422277c1bfff421c524257da8f0b9b9114e00000000000,-0xa7cdb5e34b562f7fb90b50742c1036e3c1d9985f6a1ff9cab1d61583678b1ab000,0x8614e0ed67841af9e926f055ce2df05c7855e78ab5fe439d59af579ec0c11847400,-0x44e6b889e660c8ed2c272597cb66be0f818b5dbe77a0046b1dd48f719ff5345abc00,0x1996469a699f8fba6277a19569c0758fe7fa19732a41c91b44074b09f379aacc17800,-0x750bb286c8be9962eac7e9dfea6bb4a3fa5e84d23d2ee51227104caac3408c45fe800,0x1acd07036cd05a907d89defa3124cc4c95f7a38b5f7d7d9793f847a68434f899d987c0,-0x50c5c2c213853755189de7be72f01f9c09a93568c8e72d09334d066f06a8a17bd07980,0xcc1e1a9d1ebce15eaf71b5a70a560ae89967f58b32f78a42f4030934bc4a3c9ed24cc0,-0x1b6ac5c9a096f399d785f3140e3fbf474fd7305c16c44c75271af4481537d544dabba00,0x32a634cb4658487a36f987b9637ef0d246eb650b4d9d2ff6a86226382277aa3732acd00,-0x51178996b9961b39f4b52de5ad5b5f0a5d0571e58edf98611d67c549a91ee462d75c100,0x713bd846f9ccc218dbaecb8baf92fbf59614eb602f2434549aae40708f9adbe48dc2300,-0x8a916b02c0c026e5bc2d4f9918f53ac3d02ac22dd3af3d704a98a2a272e902d423f9200,0x9525404f89a35eedfb3cd17890b8340b4b5b29bb4ac034f5b4a7ff31e69b8976b01a114,-0x8d900727890d900073bfd14a03519e90880926fd81a92b73461036680be9228abe381b8,0x76b1a261854c7e94504fd33734b46c7cfedc22aa5ee1ca623cf49ec33270c345d7c359c,-0x57fec74d56edaa34fdd640b4ce558e59554d274f9d13f3371542e0ee3f1e05d2bce12b0,0x39b1dd0714643b19d9450c93e658ff4186ff02fd325d35efc06eef5024468b106428b18,-0x217078a65d016e5f1c81fb0f35543e5dce23f18a3929f72b1da9e5ba7fcd1807fbdc660,0x111cf1d65d0697cb46da01ea00dbb5affe0e9e8f62aa5fb74c2d613dff79117898ffd38,-0x7b80c93b00c3a9b6cf4ee59d2f4a373433876abd4d14358f08fede8091c99fb6dc7370,0x30f99a5b6fc54017542eec53af80d7fb6af0a064f7b70f5c9720257a64819ccb3fd2b9,-0x1104c125864a5fa4f275ec9a041dd0eba9ffb7aec4bf02e27647be895a71392ae0b576,0x5294b876ad0558a8aa81d41b532d2b550c9d0551d06b1ade6b26f1bed7fe71b1bcfff,-0x15bff588f31e2225cdc6b5ecc718088fb4760725726268facf2ac856c75132c7a3fb4,0x4f1fd8d31829442343dfa280130c2e1e874984a5943715df61b633c219b16b942237,-0xf6be87af7e4ab9ff1dee581de3d666c78f742896caa03516102715eafcac22bac46,0x28e0efca5c895cec84565f21e945cbb3744cfa6f245e2f7d292f409cf299e6638c1,-0x5b322c9a085b35903ab1585ffc5d76a2f93ae0e3a8f72001662d136ab231ae8950,0xa936f59133639392e25c2b885d346b74356e649cefe9e9ed19b8c4cfbb2befcfe,-0x10181b1fb6f5d81cd8664061863553b43f9db249a1beecc49087e3ccf220cab84,0x13c0b55ff2c24eb8e26b1d12971b015a17d5b37a284ec1c8002be777971ec2e2,-0x1329993bd186bb4d8cdc0595d6a5aa8bfad39d4aaabad5a67763cac3ce66a68,0xe5717d023cc95da6edfa60c343762b3285fc18e327c4317c54bfa7fb5e636,-0x8090d1c5b0034f76dd2f6edf9926279f277caf7c22ddea1c1f27049b04bc,0x33fe0ad0086b98a0f5677ba57aafe4f72ece841eee4a848d098b71d4d8a,-0xe7da215797a9852957aeae38e9bd54779e95729bc167f6e951ecb0120,0x29fda99678907934d468eca2df3e2ca371c4c55d60a61b25179ce745,-0x4939e8782ea08feca697dc8102ce5f92e437bfd977be9e047c4dce,0x454b6679b247ae9558ec352679b9719903ea95fd5022bca296f3,-0x1ec0a1ce0c050ae64c920a1ff4cc7660222f4dc762f0869554,0x521a809fc80539432224de569a6da9ea274c56b801d4bab,-0x387ba8d291b77fd82d4d1d3d91b99fe7cc87ebbc2d9e,0x45c587ef4ca9a8775a0a8edcb1aa8e13a8f3354d]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 31
theorem quotient_ok_31 : quotientCheck 24 94 31 num den q31 r31=true := by decide +kernel
theorem quotient_source_31 (size : ℕ) : (coefficientsPoly q31).map (Int.castRingHom ℚ)=polyPart (key size) (X^31) :=
  quotient_from_check (key size) 94 31 num den q31 r31 (num_source size) (den_source size) quotient_ok_31
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_31 : cachedMomentCheck cache 53 indices rho q31 m31 31 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_31 (size : ℕ) : intPolyRF (coefficientsPoly m31)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^31) :=
  moment_from_cached_check cache (key size) 53 indices rho q31 m31 31 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_31 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<22 at hj;omega) moment_ok_31
def q32 : List ℤ := raw_ints% [0x63b254f01d31696e35fcbe03a4c65bb5a2,-0x26fb22ccc733e3bf119ae12ff2c9e1b8c,0xef5901d82afd9f0506c382eccfe109e,-0x5a01f3167bc2916f74ac3b3337808c,0x211bee0fef2c29ffc8dbc13c512fd,-0xbe3aac88b9c8279115e879eab1a,0x4288461c006cda69ce609c30ad,-0x169ac0c7fda6651db20be9520,0x7701ccf39b1a5e73044a8ac,-0x25cad4b4b48bb68935aeb8,0xb8901dd0b647e8a14e88,-0x35e1e141709c8ea9aac,0xef58220b4aa93f7df,-0x3ebe410b0af256f6,0xf6562c18afaddf,-0x37f66b6d4b140,0xb9ac1c952c6,-0x227bd95764,0x5964bf62,-0xc277ec,0x14d91,-0x192,0x1]
def r32 : List ℤ := raw_ints% [-0x1cf957ce8a4868ffb770a822ad84c250cc5b25a6d375214f4990c800000,-0x2c0e709ce28d70d151f3dc6336ee73d72648f6c6879b82c7bfa26680000,-0x1fc0fbf06c8f9c18436ead6dbbbfb73f5fe00e700349666acf4aea80000,-0xe7010edbe5f40f20a3d457d1666e2307a4ceb3291c419fe8f091696000,-0x4a62f4c4b6dce50f87f1651dd1f97043e7042d5090eb0f78b559926800,-0x120dc82c76866c10ca04986ec856b3b95d05fefbabf1d6569efd5c0a00,-0x36e683da33b6586cfcc83b00c48a3700bf058136457a120747188a780,-0x861517cada62bd0ae797f423d6d7b334a879e59e3de8a50882728680,-0x10b9a8756562279dab9ac3a640c208a20625b3af3299d7b52a5d6d60,-0x1b9bbfaa0a923e73a516ed1e315a88e7685a14a8893b451159dbba0,-0x2600752478f03e0d19a062c74523c0ebc9ecf0812db3185aa738c8,-0x2bd77dd008f694c7347f1191340cd6918ecf6dddfd586df9507f8,-0x2a805dcac48cde2ec7153cbf0f3afd1311b1fa6014cb110e6b0a,-0x22a0e8c09069ffa14691266a5d6b00b27a79b58e812d544662c,-0x17a946d0303150e9fa9b171b87350c8795c6fdaf945b296c9e,-0xd7e914c502d7cda7f3059388451a745ab87af415ba5d58f0,-0x65fba04ac3aefb75dbaf25e6e4756d1a3b71857cafb5123,-0x276ef5add4b05f509c575ad37abe83398aff94fbfeb1e6,-0xc45af9c113c0d1f4e6fdada486d24216f46cd8068905,-0x2ff9b40734c0d4f8d55c839fcec2aa3832990ba785c,-0x8dc65500089cddeeae2a782cea8cd0dca7cfa7733,-0x129b9990a41c5643ae6094ee89d437e476c18e2a,-0x18be95d37e57781005fc136d4c4dbe274254d5,-0xfa9d9514d633da3b65cbb5a1391d1cf07e0]
def m32 : List ℤ := raw_ints% [0x0,-0xbe22ed5f1feab4e1735bc00a08b47fe9bf51a3c64b9cc35c3b0072400000000000,0x138c26ed3e1980be3503843b96aa8c47bcd38e3ff1fc70f3329cd3f5eabac205f000,-0xf85bd8074d7a5f77ccac21a7a17023134abab203d7e98a3112b59c98ed5dfc012400,0x7ecd3a48f48d80df8d8b58cae557caa34b7a870bb9b37e684d42ea82f750842b84400,-0x2ec5939c11520a851fe5c0da7009ded20d8f7496f4ad00af95732466e4eb127e83aa00,0xd473478aa2f3ea14e3792b0736b762f3e4bbe86e5102f11a449ffed4cb6f88fff4b400,-0x304a12a22b3287676c91af5c90ed56741a930f5ac8cf44fba1e3119adf139c39a0b1f40,0x906ad2574dbdd8d1515fac66bcd08fd3629e8d4917f86adfb68d84e28d99525f33bdc80,-0x16a051d1d0f1c41b7742f771deab9f4619ee91359bb5408a98f6ab7b33bb9ea24e719dc0,0x30379853117aa4eba2387fe3f813571cc6522e573fd0b745c572777814db1cbd5c29af00,-0x5849b879735554e4f21adf4dc0587a4f1762308b7286f88d5a2b7f5c55a6817dc9d38440,0x8c0af24c4120dda9721567c7924c03989920b65806cb2150c986d0b4a53a9e96068f6980,-0xc1a4f4be4c903ce7adf8ac1f89b2e036326185303a570d17b082fffb5c49a3411377ac40,0xea89baba2e7e1305ca6842d1b815217ea76aff3ccb67e01195391e984d684848a8cc1b00,-0xf9b63740c5def01c2751c4d8661eee749747dc10506ef4854330c443ff2354095e33ab0c,0xea4fc11ab5db1f8d0c7ca0c7314e49a21f07fb574f2f81b35d36a413662e7e93eb50fc08,-0xc2174aae468a2d47e364725173c24a60818ae0c2c62bb19a8b43d4819c084428dbbe9c24,0x8e0e4e9e2fcd1c8eb8bfbb696e7b0c5361384b54efc5b3285fb0f1a49781a7966f6a1e10,-0x5be16d7058cb4f310e82cf0d8547c4ea7faf6a40fed36532f3f555b042fb7444a4ff1838,0x347d19c52e7861a12c13c64872592eb396c8150f683f7822c8359d03e30b4c6233d291c0,-0x1a73ac4cf312b2208e9c885b186b141c69449e1b4582535ebc99beed4d79da615dcd6698,0xbbcbeee802226b5ef470ca30e9b9ebd4a40e9039c9fe0b2910b21a836449f8f86b33450,-0x492dc1becd45d2f8ab86c04d55ff4bc3f246799d127aa8f40e166097e8da88e7e0ea22f,0x18f529ea99691d1281377070a9acbafd8a5c48cf48917c41ea556f56007492e7aceaaba,-0x76b2edf638a8afb1a2f798c497354d599862d4aafab3987238746964a2c62454027539,0x1e988af9c1cbb49bb733b339f0f40534aa573ff8d1db3ea70481397554ecdc6e4718ec,-0x6cc0b36016e41a462eb23f4c1e7bafbc04c3ec2f217172d64b5268e0c0c2a02136c71,0x14ac0a4257cec48afbd2d87f6b5e749f00f332707eefd3235c1bb3765143e2d5e2b8a,-0x3555190f72e7667df5dbf3e67fe58bf05c8aea0d0645a94022b9b166ced3a10f93f7,0x73893251d455102def246967a63ba6f3b3093c76147c35e61913d2e5c04b91466b0,-0xcfa4606c2b392a4d254a7b596555f1d33ab9e5b7607473f19ef7dc69c79c35dc32,0x1312dfa5cdafc042df72bffcef5f37786273992c4eefeff7a1c3e4e9e61f134e9c,-0x16894df7ccfe2f3fb62ba240f69f9f8d49732ee25bdbe501d2a43ac1423d7b50e,0x14f88fec14408458da131d0ce35a017474c5d55405285844fb2861d21aa2d618,-0xefde4535b975968c01ca877cf62a1d3530cd855b61ceb76d91cdb0dfc9dbea,0x7fcdfee1777b2a2d901d63d8ae44964615371c9279067c316ca2f8f22ed84,-0x30e3d9dd5516e66fc6f0f46bc94f4107fc4bce091f913a5c68a33b0ffb36,0xcd050be0f5468618080ecaaf43bd7387af7062501892c132d242c4a120,-0x22afb7a5fd2960dc4f9da88b5a2ef9fcfe7205ffab793bd481ee94c03,0x381547db570e72583d05c74d9eb5ff41a91194320f916a515cd7422,-0x30ca3e705deb88516dd59dae648ecde545208f0a79582b4f1bb25,0x13b67ec342fbcbc0958d47d4841a1c023cea73f39bac861b4cc,-0x2f5fd45154a35a2ce2ab73e1a7febe7b08d9076da192627d,0x1cf0424068cfebc1dcc11a287be78f1263ed6c155f5b2,-0x1f2fa1802f66bb294d176ab0d79906a2250cb94ab]
-- kcost: 2 s estimated; integer quotient/remainder binding for moment 32
theorem quotient_ok_32 : quotientCheck 24 96 32 num den q32 r32=true := by decide +kernel
theorem quotient_source_32 (size : ℕ) : (coefficientsPoly q32).map (Int.castRingHom ℚ)=polyPart (key size) (X^32) :=
  quotient_from_check (key size) 96 32 num den q32 r32 (num_source size) (den_source size) quotient_ok_32
-- kcost: 3 s estimated; actual cleared moment list equality, all source terms included
set_option trace.profiler true in
theorem moment_ok_32 : cachedMomentCheck cache 53 indices rho q32 m32 32 29176098739859498022528338165760000 30=true := by decide +kernel
theorem moment_source_32 (size : ℕ) : intPolyRF (coefficientsPoly m32)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^32) :=
  moment_from_cached_check cache (key size) 53 indices rho q32 m32 32 29176098739859498022528338165760000 30 22
    indices_nodup ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size)
    (quotient_source_32 size) cutoff_bound (by decide) power_spec cache_omega
    (by intro j hj;apply cache_li (j-1);change j<23 at hj;omega) moment_ok_32
def moments : List (List ℤ) := [m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32]
def mz (e : ℕ) : ℤ[X] := coefficientsPoly (moments.getD e [])
theorem moment_source (size e : ℕ) (he : e<33) : intPolyRF (mz e)=rfPoly (C (29176098739859498022528338165760000:ℚ))*rfX^30*(1-rfX)^22*momentRF (key size) (X^e) := by
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
  · exact moment_source_21 size
  · exact moment_source_22 size
  · exact moment_source_23 size
  · exact moment_source_24 size
  · exact moment_source_25 size
  · exact moment_source_26 size
  · exact moment_source_27 size
  · exact moment_source_28 size
  · exact moment_source_29 size
  · exact moment_source_30 size
  · exact moment_source_31 size
  · exact moment_source_32 size
#print axioms moment_source_32
end
end CatalanCore.Li2.NVMod.FamilySource.V7C31
